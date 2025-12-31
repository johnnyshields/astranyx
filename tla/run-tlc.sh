#!/bin/bash
# Run TLC model checker on lockstep specifications
#
# Models:
#   LeaderElection  - Raft election, term safety, majority voting (~21K states)
#   LockstepSimple  - Frame sync, basic events, leader authority (~1M states)
#   LockstepState   - Event ownership, syncTerm validation, desync recovery (~50M states)
#   LockstepNetwork - Message loss, peer lifecycle, checksum detection (~TBD states)
#
# Usage:
#   ./run-tlc.sh              # Run all models (default)
#   ./run-tlc.sh --quick      # Run LeaderElection + LockstepSimple (skip State)
#   ./run-tlc.sh --state      # Run only LockstepState
#   ./run-tlc.sh --network    # Run only LockstepNetwork
#   ./run-tlc.sh --force      # Force re-run ignoring cache
#
# Environment:
#   TLC_JAR - Path to tla2tools.jar (default: ~/tla2tools.jar)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLC_JAR="${TLC_JAR:-$HOME/tla2tools.jar}"
PASSED_FILE="$SCRIPT_DIR/.tlc-passed"
TMP_DIR="$SCRIPT_DIR/tmp"

mkdir -p "$TMP_DIR"

# Parse arguments
FORCE=false
MODE="all"  # all, quick, full
ARGS=()

for arg in "$@"; do
    case "$arg" in
        --force) FORCE=true ;;
        --quick) MODE="quick" ;;
        --state) MODE="state" ;;
        --network) MODE="network" ;;
        --all) MODE="all" ;;
        *) ARGS+=("$arg") ;;
    esac
done

if [[ ! -f "$TLC_JAR" ]]; then
    echo "Error: TLA+ tools not found at $TLC_JAR"
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    echo "Set TLC_JAR environment variable to the path of tla2tools.jar"
    exit 1
fi

run_model() {
    local SPEC_NAME=$1
    local SPEC_FILE="$SCRIPT_DIR/${SPEC_NAME}.tla"
    local CONFIG_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.cfg"

    if [[ ! -f "$SPEC_FILE" ]]; then
        echo "Error: $SPEC_FILE not found"
        exit 1
    fi

    # Compute hash of spec + config
    local HASH=$(cat "$SPEC_FILE" "$CONFIG_FILE" | sha256sum | cut -d' ' -f1)
    echo "[$SPEC_NAME] Hash: ${HASH:0:16}..."

    # Check if already passed
    if [[ "$FORCE" == "false" ]] && [[ -f "$PASSED_FILE" ]] && grep -q "$HASH" "$PASSED_FILE"; then
        echo "[$SPEC_NAME] Already passed (use --force to re-run)"
        return 0
    fi

    cd "$SCRIPT_DIR"

    echo "[$SPEC_NAME] Running TLC model checker..."
    echo ""

    java -XX:+UseParallelGC \
         -Xmx4g \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         -workers auto \
         "${ARGS[@]}" \
         "${SPEC_NAME}.tla"

    echo ""
    echo "[$SPEC_NAME] Model checking complete."

    # Record successful run
    echo "$HASH  $SPEC_NAME  $(date -Iseconds)" >> "$PASSED_FILE"
}

case "$MODE" in
    all)
        run_model "LeaderElection"
        run_model "LockstepSimple"
        run_model "LockstepState"
        run_model "LockstepNetwork"
        ;;
    quick)
        run_model "LeaderElection"
        run_model "LockstepSimple"
        ;;
    state)
        run_model "LockstepState"
        ;;
    network)
        run_model "LockstepNetwork"
        ;;
esac

echo ""
echo "All model checks passed."
