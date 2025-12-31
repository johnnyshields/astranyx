#!/bin/bash
# Run TLC model checker on lockstep specifications
#
# Models:
#   LeaderElection  - Raft election, term safety, majority voting (~114M states)
#   LockstepSimple  - Frame sync, basic events, leader authority (~159M states)
#   LockstepState   - Event ownership, syncTerm validation, desync recovery (~50M states)
#   LockstepNetwork - Message loss, peer lifecycle, checksum detection (~TBD states)
#
# Usage:
#   ./run_tlc.sh                              # Run all models (default)
#   ./run_tlc.sh -m LeaderElection            # Run single model
#   ./run_tlc.sh -m LeaderElection,LockstepSimple  # Run specific models
#   ./run_tlc.sh --force                      # Force re-run ignoring cache
#   ./run_tlc.sh --max                        # Use maximum resources (75% mem, 90% cpu)
#   ./run_tlc.sh --ci                         # CI mode: fail if any hashes missing (no TLC run)
#   ./run_tlc.sh -s, --sanity                 # Sanity check: run each model for 30s, report failures
#   ./run_tlc.sh -f, --fail-fast              # Stop on first failure (default: continue and report all)
#   ./run_tlc.sh -d, --download-jar           # Auto-download TLC jar to tla/tmp if missing
#   ./run_tlc.sh --jar ~/tla2tools.jar        # Specify path to tla2tools.jar

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PASSED_FILE="$SCRIPT_DIR/.tlc_passed"
TMP_DIR="$SCRIPT_DIR/tmp"

mkdir -p "$TMP_DIR"

# All available models
ALL_MODELS="LeaderElection,LockstepSimple,LockstepState,LockstepNetwork"

# Parse arguments
FORCE=false
MAX_RESOURCES=false
CI_MODE=false
SANITY_MODE=false
FAIL_FAST=false
DOWNLOAD_JAR=false
TLC_JAR=""
MODEL_LIST=""
ARGS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --force) FORCE=true; shift ;;
        --max) MAX_RESOURCES=true; shift ;;
        --ci) CI_MODE=true; shift ;;
        -s|--sanity) SANITY_MODE=true; shift ;;
        -f|--fail-fast) FAIL_FAST=true; shift ;;
        -d|--download-jar) DOWNLOAD_JAR=true; shift ;;
        --jar)
            TLC_JAR="$2"
            shift 2
            ;;
        --jar=*)
            TLC_JAR="${1#*=}"
            shift
            ;;
        -m|--model)
            MODEL_LIST="$2"
            shift 2
            ;;
        -m=*|--model=*)
            MODEL_LIST="${1#*=}"
            shift
            ;;
        *) ARGS+=("$1"); shift ;;
    esac
done

# Default to all models if none specified
if [[ -z "$MODEL_LIST" ]]; then
    MODEL_LIST="$ALL_MODELS"
fi

# CI mode: check hashes only, don't run TLC
if [[ "$CI_MODE" == "true" ]]; then
    MISSING=()
    IFS=',' read -ra MODELS <<< "$MODEL_LIST"
    for model in "${MODELS[@]}"; do
        model=$(echo "$model" | xargs)
        SPEC_FILE="$SCRIPT_DIR/${model}.tla"
        CONFIG_FILE="$SCRIPT_DIR/MC${model}.cfg"

        if [[ ! -f "$SPEC_FILE" ]]; then
            echo "Error: $SPEC_FILE not found"
            exit 1
        fi

        HASH=$(cat "$SPEC_FILE" "$CONFIG_FILE" | sha256sum | cut -d' ' -f1)

        if [[ ! -f "$PASSED_FILE" ]] || ! grep -q "$HASH" "$PASSED_FILE"; then
            MISSING+=("$model")
            echo "[$model] MISSING - hash not found: ${HASH:0:16}..."
        else
            echo "[$model] OK - hash found: ${HASH:0:16}..."
        fi
    done

    if [[ ${#MISSING[@]} -gt 0 ]]; then
        echo ""
        echo "ERROR: ${#MISSING[@]} model(s) have not been verified: ${MISSING[*]}"
        echo ""
        echo "Run tla/run_tlc.sh locally and commit tla/.tlc_passed file after it succeeds"
        exit 1
    fi

    echo ""
    echo "All model hashes verified."
    exit 0
fi

# Resolve TLC JAR location
TLC_VERSION="1.8.0"
TLC_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLC_VERSION}/tla2tools.jar"
LOCAL_JAR="$TMP_DIR/tla2tools.jar"

# Try to find tla2tools.jar: --jar flag, local download, or PATH
if [[ -n "$TLC_JAR" ]]; then
    # Explicit --jar provided
    :
elif [[ -f "$LOCAL_JAR" ]]; then
    TLC_JAR="$LOCAL_JAR"
elif command -v tla2tools.jar &> /dev/null; then
    TLC_JAR="$(command -v tla2tools.jar)"
fi

# Download if requested and still not found
if [[ "$DOWNLOAD_JAR" == "true" ]] && [[ ! -f "$TLC_JAR" ]]; then
    echo "Downloading TLC tools v${TLC_VERSION}..."
    curl -L -o "$LOCAL_JAR" "$TLC_URL"
    echo "Downloaded to $LOCAL_JAR"
    TLC_JAR="$LOCAL_JAR"
fi

if [[ -z "$TLC_JAR" ]] || [[ ! -f "$TLC_JAR" ]]; then
    echo "Error: tla2tools.jar not found"
    echo ""
    echo "Options:"
    echo "  1. Download from https://github.com/tlaplus/tlaplus/releases and add to PATH"
    echo "  2. Use --jar /path/to/tla2tools.jar"
    echo "  3. Use --download-jar to auto-download"
    exit 1
fi

# Track failures for reporting at end
FAILED_MODELS=()

# Sanity check mode: run each model for limited time
run_model_sanity() {
    local SPEC_NAME=$1
    local TIMEOUT=${2:-30}
    local SPEC_FILE="$SCRIPT_DIR/${SPEC_NAME}.tla"
    local CONFIG_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.cfg"

    if [[ ! -f "$SPEC_FILE" ]]; then
        echo "Error: $SPEC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        return 1
    fi

    cd "$SCRIPT_DIR"

    echo "[$SPEC_NAME] Sanity check (${TIMEOUT}s timeout)..."

    # Use conservative resources for sanity check
    local OUTPUT
    OUTPUT=$(timeout "${TIMEOUT}s" java -XX:+UseParallelGC \
         -Xmx4g \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         -workers auto \
         "${SPEC_NAME}.tla" 2>&1) || true

    # Check for errors in output
    if echo "$OUTPUT" | grep -q "Error:"; then
        echo "[$SPEC_NAME] FAILED - error found:"
        echo "$OUTPUT" | grep -A5 "Error:"
        FAILED_MODELS+=("$SPEC_NAME")
        return 1
    elif echo "$OUTPUT" | grep -q "Invariant.*violated"; then
        echo "[$SPEC_NAME] FAILED - invariant violated:"
        echo "$OUTPUT" | grep -B2 -A10 "Invariant.*violated"
        FAILED_MODELS+=("$SPEC_NAME")
        return 1
    else
        echo "[$SPEC_NAME] OK - no errors in ${TIMEOUT}s"
        return 0
    fi
}

run_model() {
    local SPEC_NAME=$1
    local SPEC_FILE="$SCRIPT_DIR/${SPEC_NAME}.tla"
    local CONFIG_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.cfg"

    if [[ ! -f "$SPEC_FILE" ]]; then
        echo "Error: $SPEC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        if [[ "$FAIL_FAST" == "true" ]]; then
            exit 1
        fi
        return 1
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
        # --max: Use most available resources (75% mem, 90% cpu)
        if [[ -f /proc/meminfo ]]; then
            TOTAL_MEM_KB=$(grep MemTotal /proc/meminfo | awk '{print $2}')
            TOTAL_MEM_GB=$((TOTAL_MEM_KB / 1024 / 1024))
        elif command -v sysctl &> /dev/null; then
            # macOS
            TOTAL_MEM_BYTES=$(sysctl -n hw.memsize 2>/dev/null || echo 0)
            TOTAL_MEM_GB=$((TOTAL_MEM_BYTES / 1024 / 1024 / 1024))
        else
            TOTAL_MEM_GB=8
        fi
        HEAP_GB=$((TOTAL_MEM_GB * 75 / 100))
        [[ $HEAP_GB -lt 4 ]] && HEAP_GB=4
        HEAP="-Xmx${HEAP_GB}g"

        if command -v nproc &> /dev/null; then
            NUM_CPUS=$(nproc)
        elif command -v sysctl &> /dev/null; then
            NUM_CPUS=$(sysctl -n hw.ncpu 2>/dev/null || echo 4)
        else
            NUM_CPUS=4
        fi
        NUM_WORKERS=$((NUM_CPUS * 90 / 100))
        [[ $NUM_WORKERS -lt 2 ]] && NUM_WORKERS=2
        WORKERS="-workers $NUM_WORKERS"

        echo "[$SPEC_NAME] Using MAX resources: ${HEAP_GB}GB heap, $NUM_WORKERS workers"
    else
        # Default: Conservative settings
        HEAP="-Xmx4g"
        WORKERS="-workers auto"
    fi

    if java -XX:+UseParallelGC \
         $HEAP \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         $WORKERS \
         "${ARGS[@]}" \
         "${SPEC_NAME}.tla"; then
        # Record successful run immediately after TLC passes
        echo "$HASH  $SPEC_NAME  $(date -Iseconds)" >> "$PASSED_FILE"
        echo "[$SPEC_NAME] PASSED - hash recorded: ${HASH:0:16}..."
        echo ""
        return 0
    else
        echo "[$SPEC_NAME] FAILED"
        FAILED_MODELS+=("$SPEC_NAME")
        if [[ "$FAIL_FAST" == "true" ]]; then
            exit 1
        fi
        return 1
    fi
}

# Parse comma-separated model list and run each model
IFS=',' read -ra MODELS <<< "$MODEL_LIST"

if [[ "$SANITY_MODE" == "true" ]]; then
    echo "Running sanity checks (30s per model)..."
    echo ""
    for model in "${MODELS[@]}"; do
        model=$(echo "$model" | xargs)
        run_model_sanity "$model" 30
        if [[ "$FAIL_FAST" == "true" ]] && [[ ${#FAILED_MODELS[@]} -gt 0 ]]; then
            break
        fi
    done
else
    for model in "${MODELS[@]}"; do
        model=$(echo "$model" | xargs)
        run_model "$model"
    done
fi

echo ""

# Report failures
if [[ ${#FAILED_MODELS[@]} -gt 0 ]]; then
    echo "========================================="
    echo "FAILED MODELS (${#FAILED_MODELS[@]}):"
    for failed in "${FAILED_MODELS[@]}"; do
        echo "  - $failed"
    done
    echo "========================================="
    exit 1
fi

if [[ "$SANITY_MODE" == "true" ]]; then
    echo "All sanity checks passed."
else
    echo "All model checks passed."
fi
