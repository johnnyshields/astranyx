#!/bin/bash
# Run TLC model checker on LockstepNetcode specification
#
# Features:
#   - Caches successful runs based on SHA-256 hash of spec + config
#   - Skips re-running if already passed with same hash
#
# Requirements:
#   - Java 11+ installed
#   - TLA+ tools (download from https://github.com/tlaplus/tlaplus/releases)
#
# Usage:
#   ./run-tlc.sh                    # Run with caching
#   ./run-tlc.sh --force            # Force re-run ignoring cache
#   ./run-tlc.sh -workers 4         # Pass args to TLC
#
# Environment:
#   TLC_JAR - Path to tla2tools.jar (default: ~/tla2tools.jar)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLC_JAR="${TLC_JAR:-$HOME/tla2tools.jar}"
PASSED_FILE="$SCRIPT_DIR/.tlc-passed"
SPEC_FILE="$SCRIPT_DIR/LockstepNetcode.tla"
CONFIG_FILE="$SCRIPT_DIR/MCLockstepNetcode.cfg"

# Check for --force flag
FORCE=false
ARGS=()
for arg in "$@"; do
    if [[ "$arg" == "--force" ]]; then
        FORCE=true
    else
        ARGS+=("$arg")
    fi
done

if [[ ! -f "$TLC_JAR" ]]; then
    echo "Error: TLA+ tools not found at $TLC_JAR"
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    echo "Set TLC_JAR environment variable to the path of tla2tools.jar"
    exit 1
fi

# Compute hash of spec + config
HASH=$(cat "$SPEC_FILE" "$CONFIG_FILE" | sha256sum | cut -d' ' -f1)
echo "Spec hash: $HASH"

# Check if already passed
if [[ "$FORCE" == "false" ]] && [[ -f "$PASSED_FILE" ]] && grep -q "$HASH" "$PASSED_FILE"; then
    echo "TLC already passed for this spec (hash found in $PASSED_FILE)"
    echo "Use --force to re-run anyway"
    exit 0
fi

cd "$SCRIPT_DIR"

echo "Running TLC model checker on LockstepNetcode.tla..."
echo "Config: MCLockstepNetcode.cfg"
echo ""

java -XX:+UseParallelGC \
     -Xmx4g \
     -jar "$TLC_JAR" \
     -config MCLockstepNetcode.cfg \
     -workers auto \
     "${ARGS[@]}" \
     LockstepNetcode.tla

echo ""
echo "Model checking complete."

# Record successful run
echo "$HASH  $(date -Iseconds)" >> "$PASSED_FILE"
echo "Hash recorded in $PASSED_FILE"
