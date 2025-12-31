#!/bin/bash
# Run TLC model checker on LockstepNetcode specification
#
# Requirements:
#   - Java 11+ installed
#   - TLA+ tools (download from https://github.com/tlaplus/tlaplus/releases)
#
# Usage:
#   ./run-tlc.sh                    # Run with default config
#   ./run-tlc.sh -workers 4         # Run with 4 worker threads
#   ./run-tlc.sh -deadlock          # Check for deadlocks
#
# Environment:
#   TLC_JAR - Path to tla2tools.jar (default: ~/tla2tools.jar)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLC_JAR="${TLC_JAR:-$HOME/tla2tools.jar}"

if [[ ! -f "$TLC_JAR" ]]; then
    echo "Error: TLA+ tools not found at $TLC_JAR"
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    echo "Set TLC_JAR environment variable to the path of tla2tools.jar"
    exit 1
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
     "$@" \
     LockstepNetcode.tla

echo ""
echo "Model checking complete."
