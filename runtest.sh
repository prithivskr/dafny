#!/usr/bin/env bash

# Exit on error
set -e

if [ -z "$1" ]; then
    echo "Usage: $0 <test_name_pattern>"
    echo "Example: $0 avl-tree/insert"
    exit 1
fi

PARAM="$1"

# Replace :: with / in the parameter
PARAM_CLEAN=$(echo "$PARAM" | sed 's/::/\//g')

# Find all *.dfy files in predictableverif/dafny
ALL_FILES=$(find predictableverif/dafny -name "*.dfy")

# Filter files that match the clean parameter
MATCHES=()
while IFS= read -r file; do
    if [ -n "$file" ]; then
        MATCHES+=("$file")
    fi
done < <(echo "$ALL_FILES" | grep -i "$PARAM_CLEAN" || true)

NUM_MATCHES=${#MATCHES[@]}

if [ "$NUM_MATCHES" -eq 0 ]; then
    echo "Error: No matching .dfy file found for pattern '$PARAM' in predictableverif/dafny"
    exit 1
elif [ "$NUM_MATCHES" -eq 1 ]; then
    DFY_FILE="${MATCHES[0]}"
else
    # Check if there is a unique exact suffix match (e.g. matches ending with /PARAM_CLEAN.dfy or PARAM_CLEAN)
    EXACT_MATCHES=()
    for match in "${MATCHES[@]}"; do
        if [[ "$match" == *"/$PARAM_CLEAN.dfy" ]] || [[ "$match" == *"/$PARAM_CLEAN" ]]; then
            EXACT_MATCHES+=("$match")
        fi
    done
    
    if [ "${#EXACT_MATCHES[@]}" -eq 1 ]; then
        DFY_FILE="${EXACT_MATCHES[0]}"
    else
        echo "Error: Multiple matches found for pattern '$PARAM':"
        for match in "${MATCHES[@]}"; do
            echo "  - $match"
        done
        echo "Please be more specific."
        exit 1
    fi
fi

# Determine the corresponding .bpl filename
BPL_FILE="${DFY_FILE%.dfy}.bpl"

echo "Matching file found: $DFY_FILE"
echo "BPL file output: $BPL_FILE"
echo "Running: make exe SkipJavaRuntime=true && ./Binaries/Dafny verify --qf-heap --p3 $DFY_FILE --bprint $BPL_FILE"
echo ""

make exe SkipJavaRuntime=true && ./Binaries/Dafny verify --qf-heap --p3 "$DFY_FILE" --bprint "$BPL_FILE"
