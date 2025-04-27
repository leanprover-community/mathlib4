#!/usr/bin/env bash

set -euo pipefail

# Replace every '/' with '.'
modified_args="${@//\//.}"

# Remove every '.lean' suffix
modified_args="${modified_args//.lean/}"

# Call 'lake' with the modified arguments
lake $modified_args

