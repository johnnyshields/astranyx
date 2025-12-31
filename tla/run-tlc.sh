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
#   ./run-tlc.sh                              # Run all models (default)
#   ./run-tlc.sh -f LeaderElection            # Run single model
#   ./run-tlc.sh -f LeaderElection,LockstepSimple  # Run specific models
#   ./run-tlc.sh --force                      # Force re-run ignoring cache
#   ./run-tlc.sh --max                        # Use maximum resources (48GB heap, 28 workers)
#
# Environment:
#   TLC_JAR - Path to tla2tools.jar (default: ~/tla2tools.jar)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLC_JAR="${TLC_JAR:-$HOME/tla2tools.jar}"
PASSED_FILE="$SCRIPT_DIR/.tlc-passed"
TMP_DIR="$SCRIPT_DIR/tmp"

mkdir -p "$TMP_DIR"

# All available models
ALL_MODELS="LeaderElection,LockstepSimple,LockstepState,LockstepNetwork"

# Parse arguments
FORCE=false
MAX_RESOURCES=false
FILE_LIST=""
ARGS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --force) FORCE=true; shift ;;
        --max) MAX_RESOURCES=true; shift ;;
        -f|--file)
            FILE_LIST="$2"
            shift 2
            ;;
        -f=*|--file=*)
            FILE_LIST="${1#*=}"
            shift
            ;;
        *) ARGS+=("$1"); shift ;;
    esac
done

# Default to all models if none specified
if [[ -z "$FILE_LIST" ]]; then
    FILE_LIST="$ALL_MODELS"
fi

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

    # Resource configuration
    if [[ "$MAX_RESOURCES" == "true" ]]; then
        # --max: Use most cores and lots of RAM (32 cores, 63GB RAM machine)
        HEAP="-Xmx48g"
        WORKERS="-workers 28"
        echo "[$SPEC_NAME] Using MAX resources: 48GB heap, 28 workers"
    else
        # Default: Conservative settings
        HEAP="-Xmx4g"
        WORKERS="-workers auto"
    fi

    java -XX:+UseParallelGC \
         $HEAP \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         $WORKERS \
         "${ARGS[@]}" \
         "${SPEC_NAME}.tla"

    echo ""
    echo "[$SPEC_NAME] Model checking complete."

    # Record successful run
    echo "$HASH  $SPEC_NAME  $(date -Iseconds)" >> "$PASSED_FILE"
}

# Parse comma-separated file list and run each model
IFS=',' read -ra MODELS <<< "$FILE_LIST"
for model in "${MODELS[@]}"; do
    # Trim whitespace
    model=$(echo "$model" | xargs)
    run_model "$model"
done

echo ""
echo "All model checks passed."
