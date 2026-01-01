#!/bin/bash
# Run TLC model checker on lockstep specifications
#
# Models are auto-detected by finding MC*.tla files in the tla/ directory.
#
# Usage:
#   ./run_tlc.sh                        # Run all models (default)
#   ./run_tlc.sh Model1 Model2          # Run specific model(s)
#   ./run_tlc.sh -f, --force            # Force re-run ignoring .tlc_passed hashes
#   ./run_tlc.sh -k, --hash-check       # Hash check: fail if any hashes missing
#   ./run_tlc.sh -s, --sanity           # Sanity check: run each model for 30s
#   ./run_tlc.sh -x, --fail-fast        # Stop on first failure
#   ./run_tlc.sh --ci                   # CI mode: hash check + sanity checks (30s each)
#   ./run_tlc.sh -d, --download-jar     # Auto-download TLC jar to tla/tmp if missing
#   ./run_tlc.sh --jar ~/tla2tools.jar  # Specify path to tla2tools.jar

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PASSED_FILE="$SCRIPT_DIR/.tlc_passed"
TMP_DIR="$SCRIPT_DIR/tmp"

mkdir -p "$TMP_DIR"

# Auto-detect all models by finding MC*.tla files (strips MC prefix and .tla suffix)
# Searches current dir and subdirs
detect_models() {
    local models=""
    while IFS= read -r -d '' mc_file; do
        local basename=$(basename "$mc_file" .tla)
        local model_name=${basename#MC}  # Remove MC prefix
        if [[ -z "$models" ]]; then
            models="$model_name"
        else
            models="$models,$model_name"
        fi
    done < <(find "$SCRIPT_DIR" -name "MC*.tla" -print0 2>/dev/null | sort -z)
    echo "$models"
}

ALL_MODELS=$(detect_models)

# Parse arguments
FORCE=false
CI_MODE=false
HASH_CHECK_ONLY=false
SANITY_MODE=false
FAIL_FAST=false
DOWNLOAD_JAR=false
TLC_JAR=""
MODEL_ARGS=()

show_help() {
    head -15 "$0" | tail -10
    exit 0
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        -h|--help) show_help ;;
        -f|--force) FORCE=true; shift ;;
        --ci) CI_MODE=true; shift ;;
        -k|--hash-check) HASH_CHECK_ONLY=true; shift ;;
        -s|--sanity) SANITY_MODE=true; shift ;;
        -x|--fail-fast) FAIL_FAST=true; shift ;;
        -d|--download-jar) DOWNLOAD_JAR=true; shift ;;
        --jar)
            TLC_JAR="$2"
            shift 2
            ;;
        --jar=*)
            TLC_JAR="${1#*=}"
            shift
            ;;
        -*) echo "Unknown option: $1"; exit 1 ;;
        *) MODEL_ARGS+=("$1"); shift ;;
    esac
done

# Build MODEL_LIST from positional arguments (supports space-sep and comma-sep)
MODEL_LIST=""
for arg in "${MODEL_ARGS[@]}"; do
    if [[ -z "$MODEL_LIST" ]]; then
        MODEL_LIST="$arg"
    else
        # Convert spaces to commas for unified handling
        MODEL_LIST="$MODEL_LIST,$arg"
    fi
done

# Default to all models if none specified
if [[ -z "$MODEL_LIST" ]]; then
    MODEL_LIST="$ALL_MODELS"
fi

# TLC JAR configuration (needed for CI mode sanity checks)
TLC_VERSION="1.8.0"
TLC_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLC_VERSION}/tla2tools.jar"
LOCAL_JAR="$TMP_DIR/tla2tools.jar"

# Hash check mode: verify hashes without running TLC
if [[ "$HASH_CHECK_ONLY" == "true" ]]; then
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

        MC_FILE="$SCRIPT_DIR/MC${model}.tla"
        HASH=$(cat "$SPEC_FILE" "$MC_FILE" "$CONFIG_FILE" 2>/dev/null | sha256sum | cut -d' ' -f1)

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

# CI mode: check hashes THEN run sanity checks
if [[ "$CI_MODE" == "true" ]]; then
    echo "=== Phase 1: Verify model hashes ==="
    echo ""
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

        MC_FILE="$SCRIPT_DIR/MC${model}.tla"
        HASH=$(cat "$SPEC_FILE" "$MC_FILE" "$CONFIG_FILE" 2>/dev/null | sha256sum | cut -d' ' -f1)

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
    echo ""

    # Now run sanity checks (requires Java/TLC JAR)
    # Skip if TLC JAR not available (hash check is the primary gate)
    if [[ -z "$TLC_JAR" ]] || [[ ! -f "$TLC_JAR" ]]; then
        # Try to find or download JAR for sanity checks
        if [[ -f "$LOCAL_JAR" ]]; then
            TLC_JAR="$LOCAL_JAR"
        elif [[ "$DOWNLOAD_JAR" == "true" ]]; then
            echo "Downloading TLC tools v${TLC_VERSION} for sanity checks..."
            curl -L -o "$LOCAL_JAR" "$TLC_URL"
            TLC_JAR="$LOCAL_JAR"
        fi
    fi

    if [[ -n "$TLC_JAR" ]] && [[ -f "$TLC_JAR" ]]; then
        echo "=== Phase 2: Sanity checks (30s per model) ==="
        echo ""
        SANITY_MODE=true
        # Continue to sanity check logic below
    else
        echo "Skipping sanity checks (TLC JAR not available)"
        echo "Use --download-jar to enable sanity checks in CI"
        exit 0
    fi
fi

# Resolve TLC JAR (skip if already set by CI mode)
if [[ -z "$TLC_JAR" ]] || [[ ! -f "$TLC_JAR" ]]; then
    # Try to find tla2tools.jar: --jar flag, local download, or PATH
    if [[ -f "$LOCAL_JAR" ]]; then
        TLC_JAR="$LOCAL_JAR"
    elif command -v tla2tools.jar &> /dev/null; then
        TLC_JAR="$(command -v tla2tools.jar)"
    fi

    # Download if requested and still not found
    if [[ "$DOWNLOAD_JAR" == "true" ]] && { [[ -z "$TLC_JAR" ]] || [[ ! -f "$TLC_JAR" ]]; }; then
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
fi

# Track failures for reporting at end
FAILED_MODELS=()

# Sanity check mode: run each model for limited time
run_model_sanity() {
    local SPEC_NAME=$1
    local TIMEOUT=${2:-30}
    local SPEC_FILE="$SCRIPT_DIR/${SPEC_NAME}.tla"
    local MC_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.tla"
    local CONFIG_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.cfg"

    if [[ ! -f "$SPEC_FILE" ]]; then
        echo "Error: $SPEC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        return 1
    fi

    if [[ ! -f "$MC_FILE" ]]; then
        echo "Error: $MC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        return 1
    fi

    cd "$SCRIPT_DIR"

    echo "[$SPEC_NAME] Sanity check (${TIMEOUT}s timeout)..."

    local OUTPUT
    OUTPUT=$(timeout "${TIMEOUT}s" java -XX:+UseParallelGC \
         -Xmx4g \
         -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         -workers auto \
         -lncheck final \
         "MC${SPEC_NAME}.tla" 2>&1) || true

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
    local MC_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.tla"
    local CONFIG_FILE="$SCRIPT_DIR/MC${SPEC_NAME}.cfg"

    if [[ ! -f "$SPEC_FILE" ]]; then
        echo "Error: $SPEC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        if [[ "$FAIL_FAST" == "true" ]]; then
            exit 1
        fi
        return 1
    fi

    if [[ ! -f "$MC_FILE" ]]; then
        echo "Error: $MC_FILE not found"
        FAILED_MODELS+=("$SPEC_NAME")
        if [[ "$FAIL_FAST" == "true" ]]; then
            exit 1
        fi
        return 1
    fi

    local HASH=$(cat "$SPEC_FILE" "$MC_FILE" "$CONFIG_FILE" | sha256sum | cut -d' ' -f1)
    echo "[$SPEC_NAME] Hash: ${HASH:0:16}..."

    # Check if already passed
    if [[ "$FORCE" == "false" ]] && [[ -f "$PASSED_FILE" ]] && grep -q "$HASH" "$PASSED_FILE"; then
        echo "[$SPEC_NAME] Already passed (use --force to re-run)"
        return 0
    fi

    cd "$SCRIPT_DIR"

    echo "[$SPEC_NAME] Running TLC model checker..."
    echo ""

    # Resource configuration: use 75% of available memory, auto workers
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
    WORKERS="-workers auto"

    local TLC_OUTPUT
    TLC_OUTPUT=$(java -XX:+UseParallelGC \
         -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet \
         $HEAP \
         -jar "$TLC_JAR" \
         -config "MC${SPEC_NAME}.cfg" \
         -metadir "$TMP_DIR" \
         -lncheck final \
         -cleanup \
         $WORKERS \
         "MC${SPEC_NAME}.tla" 2>&1 | tee /dev/stderr)
    local TLC_EXIT=${PIPESTATUS[0]}

    if [[ $TLC_EXIT -eq 0 ]]; then
        # Parse state counts from TLC output
        # Format: "46895806 states generated, 5602527 distinct states found, 0 states left on queue."
        local STATES_LINE=$(echo "$TLC_OUTPUT" | grep -E "^[0-9]+ states generated")
        local STATES_GENERATED=""
        local STATES_DISTINCT=""
        if [[ -n "$STATES_LINE" ]]; then
            STATES_GENERATED=$(echo "$STATES_LINE" | sed -E 's/^([0-9]+) states generated.*/\1/')
            STATES_DISTINCT=$(echo "$STATES_LINE" | sed -E 's/.*[^0-9]([0-9]+) distinct states found.*/\1/')
        fi

        # Parse graph depth from TLC output
        # Format: "The depth of the complete state graph search is 32."
        local DEPTH_LINE=$(echo "$TLC_OUTPUT" | grep -E "^The depth of the complete state graph search is")
        local GRAPH_DEPTH=""
        if [[ -n "$DEPTH_LINE" ]]; then
            GRAPH_DEPTH=$(echo "$DEPTH_LINE" | sed -E 's/.*is ([0-9]+)\..*/\1/')
        fi

        # Record successful run with state counts and depth
        local RECORD="$HASH  $SPEC_NAME  $(date -Iseconds)"
        if [[ -n "$STATES_GENERATED" ]] && [[ -n "$STATES_DISTINCT" ]]; then
            RECORD="$RECORD  states_generated=$STATES_GENERATED  states_distinct=$STATES_DISTINCT"
        fi
        if [[ -n "$GRAPH_DEPTH" ]]; then
            RECORD="$RECORD  graph_depth=$GRAPH_DEPTH"
        fi
        echo "$RECORD" >> "$PASSED_FILE"
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
    if [[ "$CI_MODE" != "true" ]]; then
        echo "Running sanity checks (30s per model)..."
        echo ""
    fi
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
