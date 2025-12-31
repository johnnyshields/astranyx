#!/bin/bash
# Run TLC model checker on lockstep specifications
#
# Models:
#   LeaderElection - Election only (~21K states, ~2s)
#   LockstepCore   - Fast (~1M states, ~1 min)
#   LockstepFull   - Complete (~50M+ states, ~10+ min)
#
# Usage:
#   ./run-tlc.sh              # Run all models (default)
#   ./run-tlc.sh --quick      # Run LeaderElection + LockstepCore (skip Full)
#   ./run-tlc.sh --full       # Run only LockstepFull
#   ./run-tlc.sh --force      # Force re-run ignoring cache
#
# Environment:
#   TLC_JAR - Path to tla2tools.jar (default: ~/tla2tools.jar)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLC_JAR="${TLC_JAR:-$HOME/tla2tools.jar}"
PASSED_FILE="$SCRIPT_DIR/.tlc-passed"

# Parse arguments
FORCE=false
MODE="all"  # all, quick, full
ARGS=()

for arg in "$@"; do
    case "$arg" in
        --force) FORCE=true ;;
        --quick) MODE="quick" ;;
        --full) MODE="full" ;;
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
        run_model "LockstepCore"
        run_model "LockstepFull"
        ;;
    quick)
        run_model "LeaderElection"
        run_model "LockstepCore"
        ;;
    full)
        run_model "LockstepFull"
        ;;
esac

echo ""
echo "All model checks passed."
