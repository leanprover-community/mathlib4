#!/usr/bin/env bash
# Validates GitHub Apps configuration against actual GitHub state.
#
# This script checks that:
# - Apps exist with expected IDs and descriptions
# - Apps are installed and not suspended
# - Required secrets exist in each repository
# - Workflow files reference the correct secrets
# - No undocumented MATHLIB_* secrets exist (warning only)
#
# Usage: ./scripts/validate-github-apps.sh
#
# Requirements:
# - gh (GitHub CLI) installed and authenticated
# - yq (YAML processor) installed
# - jq (JSON processor) installed
#
# Exit codes:
# - 0: All validations passed (warnings are OK)
# - 1: One or more validations failed

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
ERRORS=0
WARNINGS=0
APPS_VALIDATED=0

# Config file location (relative to repo root)
CONFIG_FILE=".github/github-apps.yml"

# Find repo root
REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || echo ".")"
CONFIG_PATH="${REPO_ROOT}/${CONFIG_FILE}"

# Check dependencies
check_dependencies() {
    local missing=()
    command -v gh &>/dev/null || missing+=("gh")
    command -v yq &>/dev/null || missing+=("yq")
    command -v jq &>/dev/null || missing+=("jq")

    if [[ ${#missing[@]} -gt 0 ]]; then
        echo -e "${RED}Missing required dependencies: ${missing[*]}${NC}"
        echo "Install with:"
        echo "  brew install gh yq jq  # macOS"
        echo "  apt install gh yq jq   # Debian/Ubuntu"
        exit 1
    fi

    # Check gh is authenticated
    if ! gh auth status &>/dev/null; then
        echo -e "${RED}GitHub CLI not authenticated. Run 'gh auth login' first.${NC}"
        exit 1
    fi
}

# Print status messages
ok() { echo -e "  ${GREEN}✓${NC} $1"; }
fail() { echo -e "  ${RED}✗${NC} $1"; ((ERRORS++)) || true; }
warn() { echo -e "  ${YELLOW}⚠${NC} $1"; ((WARNINGS++)) || true; }
info() { echo -e "  ${BLUE}ℹ${NC} $1"; }

# Get list of app slugs from config
get_app_slugs() {
    yq -r '.apps | keys | .[]' "$CONFIG_PATH"
}

# Get app property
get_app_prop() {
    local slug="$1" prop="$2"
    yq -r ".apps[\"$slug\"].$prop // \"\"" "$CONFIG_PATH"
}

# Get array property as newline-separated values
get_app_array() {
    local slug="$1" prop="$2"
    yq -r ".apps[\"$slug\"].$prop[]? // \"\"" "$CONFIG_PATH"
}

# Validate a single app
validate_app() {
    local slug="$1"
    local expected_id expected_org expected_desc

    expected_id=$(get_app_prop "$slug" "id")
    expected_org=$(get_app_prop "$slug" "org")
    expected_desc=$(get_app_prop "$slug" "description")

    echo -e "\n${BLUE}[$slug]${NC}"

    # Check app exists and get metadata
    local app_data
    if ! app_data=$(gh api "/apps/$slug" 2>/dev/null); then
        fail "App does not exist at /apps/$slug"
        return
    fi

    # Verify app ID
    local actual_id
    actual_id=$(echo "$app_data" | jq -r '.id')
    if [[ "$actual_id" == "$expected_id" ]]; then
        ok "App exists (id: $actual_id)"
    else
        fail "App ID mismatch: expected $expected_id, got $actual_id"
    fi

    # Verify description contains expected text (substring match)
    local actual_desc
    actual_desc=$(echo "$app_data" | jq -r '.description // ""')
    if [[ "$actual_desc" == *"$expected_desc"* ]] || [[ "$expected_desc" == *"$actual_desc"* ]]; then
        ok "Description matches"
    else
        warn "Description mismatch: expected '$expected_desc', got '$actual_desc'"
    fi

    # Check app is installed on org
    local installations
    if installations=$(gh api "/orgs/$expected_org/installations" 2>/dev/null); then
        local installed suspended
        installed=$(echo "$installations" | jq -r ".installations[] | select(.app_slug == \"$slug\") | .id" | head -1)
        if [[ -n "$installed" ]]; then
            ok "App installed on $expected_org"

            # Check if suspended
            suspended=$(echo "$installations" | jq -r ".installations[] | select(.app_slug == \"$slug\") | .suspended_at // empty" | head -1)
            if [[ -z "$suspended" ]]; then
                ok "App not suspended"
            else
                fail "App is suspended!"
            fi
        else
            fail "App not installed on $expected_org"
        fi
    else
        warn "Could not check installations on $expected_org (may lack permissions)"
    fi

    # Validate secrets for each repo
    validate_app_secrets "$slug"

    # Validate workflow references
    validate_app_workflows "$slug"

    ((APPS_VALIDATED++)) || true
}

# Validate secrets exist for an app
validate_app_secrets() {
    local slug="$1"
    local secrets_json

    # Get secrets configuration as JSON for easier parsing
    secrets_json=$(yq -o=json ".apps[\"$slug\"].secrets // []" "$CONFIG_PATH")
    local num_secrets
    num_secrets=$(echo "$secrets_json" | jq 'length')

    for ((i=0; i<num_secrets; i++)); do
        local repo app_id_secret private_key_secret
        repo=$(echo "$secrets_json" | jq -r ".[$i].repo")
        app_id_secret=$(echo "$secrets_json" | jq -r ".[$i].app_id")
        private_key_secret=$(echo "$secrets_json" | jq -r ".[$i].private_key")

        # Get secrets list for repo
        local repo_secrets
        if ! repo_secrets=$(gh secret list --repo "$repo" 2>/dev/null); then
            warn "Could not list secrets for $repo (may lack permissions)"
            continue
        fi

        # Check APP_ID secret exists
        if echo "$repo_secrets" | grep -q "^${app_id_secret}"; then
            ok "Secret $app_id_secret exists in $repo"
        else
            fail "Secret $app_id_secret missing in $repo"
        fi

        # Check PRIVATE_KEY secret exists
        if echo "$repo_secrets" | grep -q "^${private_key_secret}"; then
            ok "Secret $private_key_secret exists in $repo"
        else
            fail "Secret $private_key_secret missing in $repo"
        fi
    done
}

# Validate workflow files reference correct secrets
validate_app_workflows() {
    local slug="$1"
    local workflows_json

    workflows_json=$(yq -o=json ".apps[\"$slug\"].workflows // []" "$CONFIG_PATH")
    local num_workflows
    num_workflows=$(echo "$workflows_json" | jq 'length')

    for ((i=0; i<num_workflows; i++)); do
        local repo files_json
        repo=$(echo "$workflows_json" | jq -r ".[$i].repo")
        files_json=$(echo "$workflows_json" | jq -r ".[$i].files")

        # Get expected secret name pattern for this app
        local secret_pattern
        secret_pattern=$(yq -r ".apps[\"$slug\"].secrets[0].app_id // \"\"" "$CONFIG_PATH")

        local num_files
        num_files=$(echo "$files_json" | jq 'length')

        for ((j=0; j<num_files; j++)); do
            local file
            file=$(echo "$files_json" | jq -r ".[$j]")

            # For mathlib4, check local files; for others, use API
            if [[ "$repo" == "leanprover-community/mathlib4" ]]; then
                local workflow_path="${REPO_ROOT}/.github/workflows/${file}"
                if [[ -f "$workflow_path" ]]; then
                    ok "Workflow $file exists"

                    # Check it references the expected secrets
                    if grep -q "$secret_pattern" "$workflow_path" 2>/dev/null; then
                        ok "Workflow $file references $secret_pattern"
                    else
                        fail "Workflow $file does not reference $secret_pattern"
                    fi
                else
                    fail "Workflow $file does not exist"
                fi
            else
                # For other repos, just check file exists via API
                if gh api "repos/$repo/contents/.github/workflows/$file" &>/dev/null; then
                    ok "Workflow $file exists in $repo"
                else
                    fail "Workflow $file does not exist in $repo"
                fi
            fi
        done
    done
}

# Check for undocumented MATHLIB_* secrets (exhaustivity)
check_exhaustivity() {
    echo -e "\n${BLUE}[Exhaustivity Check]${NC}"

    # Get all documented secret names
    local documented_secrets
    documented_secrets=$(yq -r '.apps[].secrets[].app_id, .apps[].secrets[].private_key' "$CONFIG_PATH" | sort -u)

    # Get all MATHLIB_* secrets from mathlib4
    local actual_secrets
    if ! actual_secrets=$(gh secret list --repo leanprover-community/mathlib4 2>/dev/null | awk '{print $1}' | grep "^MATHLIB_"); then
        warn "Could not list secrets for exhaustivity check"
        return
    fi

    # Find undocumented secrets
    local undocumented=()
    while IFS= read -r secret; do
        if ! echo "$documented_secrets" | grep -q "^${secret}$"; then
            undocumented+=("$secret")
        fi
    done <<< "$actual_secrets"

    if [[ ${#undocumented[@]} -eq 0 ]]; then
        ok "All MATHLIB_* secrets are documented"
    else
        for secret in "${undocumented[@]}"; do
            warn "Secret $secret in mathlib4 not documented in config"
        done
    fi
}

# Main
main() {
    echo "Validating GitHub Apps configuration..."
    echo "Config file: $CONFIG_PATH"

    check_dependencies

    if [[ ! -f "$CONFIG_PATH" ]]; then
        echo -e "${RED}Config file not found: $CONFIG_PATH${NC}"
        exit 1
    fi

    # Validate each app
    for slug in $(get_app_slugs); do
        validate_app "$slug"
    done

    # Exhaustivity check
    check_exhaustivity

    # Summary
    echo -e "\n${BLUE}────────────────────────────────────────${NC}"
    echo -e "Summary: ${GREEN}$APPS_VALIDATED apps validated${NC}"
    if [[ $ERRORS -gt 0 ]]; then
        echo -e "         ${RED}$ERRORS errors${NC}"
    fi
    if [[ $WARNINGS -gt 0 ]]; then
        echo -e "         ${YELLOW}$WARNINGS warnings${NC}"
    fi

    if [[ $ERRORS -gt 0 ]]; then
        echo -e "\n${RED}Validation failed!${NC}"
        exit 1
    else
        echo -e "\n${GREEN}Validation passed!${NC}"
        exit 0
    fi
}

main "$@"
