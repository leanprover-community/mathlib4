#!/usr/bin/env bash
# Commit Verification Script
# Verifies transient and automated commits in a PR
#
# Usage: ./scripts/verify_commits.sh <base_ref> [--json] [--json-file <path>]
#
# Exit codes:
#   0 - All verifications passed
#   1 - Verification failed
#   2 - Usage error

set -euo pipefail

# --- Configuration ---
TIMEOUT_SECONDS=600  # 10 minutes per command
TRANSIENT_PREFIX="${TRANSIENT_PREFIX:-transient: }"
AUTO_PREFIX="${AUTO_PREFIX:-x: }"

# --- Colors (disabled if not a terminal) ---
if [[ -t 1 ]]; then
  RED='\033[0;31m'
  GREEN='\033[0;32m'
  YELLOW='\033[0;33m'
  BLUE='\033[0;34m'
  NC='\033[0m'
else
  RED='' GREEN='' YELLOW='' BLUE='' NC=''
fi

# --- Helpers ---
log_info()  { echo -e "${BLUE}[INFO]${NC} $*" >&2; }
log_ok()    { echo -e "${GREEN}[OK]${NC} $*" >&2; }
log_warn()  { echo -e "${YELLOW}[WARN]${NC} $*" >&2; }
log_error() { echo -e "${RED}[ERROR]${NC} $*" >&2; }

# Show a truncated diff stat between two trees
show_diff_stat() {
  local tree1="$1"
  local tree2="$2"
  local max_lines="${3:-20}"
  local diff_output
  diff_output=$(git diff-tree --stat "$tree1" "$tree2")
  local line_count
  line_count=$(echo "$diff_output" | wc -l)
  if [[ $line_count -gt $max_lines ]]; then
    echo "$diff_output" | head -"$max_lines" >&2
    echo "  ... and $((line_count - max_lines)) more lines" >&2
  else
    echo "$diff_output" >&2
  fi
}

usage() {
  echo "Usage: $0 <base_ref> [--json | --json-file <path>]"
  echo ""
  echo "Arguments:"
  echo "  base_ref          The base commit/branch to compare against (e.g., origin/master)"
  echo "  --json            Output results in JSON format (instead of human-readable)"
  echo "  --json-file PATH  Write JSON to PATH while outputting human-readable to stdout"
  exit 2
}

# --- Argument parsing ---
JSON_OUTPUT=false
JSON_FILE=""
BASE_REF=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --json) JSON_OUTPUT=true; shift ;;
    --json-file) JSON_FILE="$2"; shift 2 ;;
    --help|-h) usage ;;
    -*) log_error "Unknown option: $1"; usage ;;
    *) BASE_REF="$1"; shift ;;
  esac
done

if [[ -z "$BASE_REF" ]]; then
  log_error "Missing required argument: base_ref"
  usage
fi

# --- State management ---
# Save original HEAD/branch to restore on exit
ORIGINAL_REF=""
STASH_CREATED=false

save_state() {
  # Try to get current branch name; if in detached HEAD, fall back to SHA
  ORIGINAL_REF=$(git symbolic-ref --short HEAD 2>/dev/null || git rev-parse HEAD)
  # Stash any uncommitted changes
  if ! git diff --quiet || ! git diff --cached --quiet; then
    git stash push -q -m "verify_commits temporary stash"
    STASH_CREATED=true
  fi
}

restore_state() {
  if [[ -n "$ORIGINAL_REF" ]]; then
    git checkout -q "$ORIGINAL_REF" 2>/dev/null || true
    git reset -q HEAD 2>/dev/null || true
  fi
  if [[ "$STASH_CREATED" == "true" ]]; then
    git stash pop -q 2>/dev/null || true
  fi
}

# Ensure we restore state on exit (success or failure)
trap restore_state EXIT

# --- Main logic ---

# Find merge base
MERGE_BASE=$(git merge-base "$BASE_REF" HEAD)
log_info "Merge base: $MERGE_BASE"
log_info "HEAD: $(git rev-parse HEAD)"

# Collect all commits in the PR
mapfile -t ALL_COMMITS < <(git rev-list --reverse "$MERGE_BASE..HEAD")
TOTAL_COMMITS=${#ALL_COMMITS[@]}

if [[ $TOTAL_COMMITS -eq 0 ]]; then
  log_info "No commits to verify"
  exit 0
fi

log_info "Found $TOTAL_COMMITS commits to analyze"

# Categorize commits (also build NON_TRANSIENT list for later use)
declare -a TRANSIENT_COMMITS=()
declare -a NON_TRANSIENT_COMMITS=()
declare -a AUTO_COMMITS=()
declare -a SUBSTANTIVE_COMMITS=()

for commit in "${ALL_COMMITS[@]}"; do
  subject=$(git log -1 --format="%s" "$commit")

  if [[ "$subject" == "$TRANSIENT_PREFIX"* ]]; then
    TRANSIENT_COMMITS+=("$commit")
  else
    NON_TRANSIENT_COMMITS+=("$commit")
    if [[ "$subject" == "$AUTO_PREFIX"* ]]; then
      AUTO_COMMITS+=("$commit")
    else
      SUBSTANTIVE_COMMITS+=("$commit")
    fi
  fi
done

log_info "Categorized: ${#SUBSTANTIVE_COMMITS[@]} substantive, ${#AUTO_COMMITS[@]} automated, ${#TRANSIENT_COMMITS[@]} transient"

# Save state before any checkouts
save_state

# --- Verification results ---
TRANSIENT_VERIFIED=false
TRANSIENT_ERROR=""
declare -A AUTO_RESULTS=()  # commit -> "ok" or error message
OVERALL_SUCCESS=true

# --- 1. Verify transient commits ---
verify_transient() {
  log_info "Verifying transient commits..."

  if [[ ${#TRANSIENT_COMMITS[@]} -eq 0 ]]; then
    log_info "No transient commits to verify"
    TRANSIENT_VERIFIED=true
    return 0
  fi

  # Get the final tree (^{tree} dereferences commit to its tree object)
  FINAL_TREE=$(git rev-parse HEAD^{tree})

  if [[ ${#NON_TRANSIENT_COMMITS[@]} -eq 0 ]]; then
    # All commits are transient - final tree should match base
    EXPECTED_TREE=$(git rev-parse "$MERGE_BASE^{tree}")
  else
    # Cherry-pick non-transient commits onto base and get resulting tree
    log_info 'Work in detached HEAD to avoid creating/deleting branches'
    git checkout -q --detach "$MERGE_BASE"

    CHERRY_PICK_FAILED=false
    for commit in "${NON_TRANSIENT_COMMITS[@]}"; do
      local cp_output
      # Check if this is a merge commit (has more than one parent)
      local parent_count
      parent_count=$(git rev-list --parents -n 1 "$commit" | awk '{print NF-1}')

      local cp_args=(--no-commit)
      if [[ "$parent_count" -gt 1 ]]; then
        # For merge commits, use -m 1 to cherry-pick relative to first parent
        cp_args+=(-m 1)
      fi

      if ! cp_output=$(git cherry-pick "${cp_args[@]}" "$commit" 2>&1); then
        # Cherry-pick failed - transient commits don't cleanly separate
        echo "$cp_output" >&2
        git cherry-pick --abort 2>/dev/null || git reset --hard HEAD >/dev/null 2>&1
        CHERRY_PICK_FAILED=true
        TRANSIENT_ERROR="Cherry-pick of $(git log -1 --format='%h: %s' "$commit") failed - transient commits may have side effects"
        break
      fi
    done

    if [[ "$CHERRY_PICK_FAILED" == "false" ]]; then
      # Get the tree of the cherry-picked result
      # cherry-pick --no-commit stages changes, so write-tree works directly
      EXPECTED_TREE=$(git write-tree)
    fi

    # Note: restore_state (via trap) will return us to ORIGINAL_HEAD

    if [[ "$CHERRY_PICK_FAILED" == "true" ]]; then
      return 1
    fi
  fi

  if [[ "$FINAL_TREE" == "$EXPECTED_TREE" ]]; then
    log_ok "Transient commits verified: final tree matches (${FINAL_TREE:0:12})"
    TRANSIENT_VERIFIED=true
    return 0
  else
    TRANSIENT_ERROR="Tree mismatch: transient commits have net effect"
    log_error "Transient verification failed: $TRANSIENT_ERROR"
    log_error "Diff between HEAD and tree-without-transient-commits:"
    show_diff_stat "$EXPECTED_TREE" "$FINAL_TREE"
    return 1
  fi
}

# --- 2. Verify automated commits ---
verify_auto_commit() {
  local commit="$1"
  local subject
  subject=$(git log -1 --format="%s" "$commit")
  local command="${subject#$AUTO_PREFIX}"
  local short_sha="${commit:0:7}"

  log_info "Verifying auto commit $short_sha: $command"

  # Check single parent
  local parent_count
  parent_count=$(git rev-list --parents -n 1 "$commit" | awk '{print NF-1}')
  if [[ "$parent_count" -ne 1 ]]; then
    AUTO_RESULTS["$commit"]="Expected 1 parent, found $parent_count"
    log_error "Auto commit $short_sha: expected 1 parent, found $parent_count"
    return 1
  fi

  local parent
  parent=$(git rev-parse "$commit^")
  local expected_tree
  expected_tree=$(git rev-parse "$commit^{tree}")

  # Checkout parent in detached HEAD
  git checkout -q --detach "$parent"

  # Record untracked files before running command (to exclude pre-existing ones)
  local untracked_before
  untracked_before=$(git ls-files --others --exclude-standard | sort)

  # Run command with timeout
  local cmd_exit=0
  timeout "$TIMEOUT_SECONDS" bash -c "$command" || cmd_exit=$?

  if [[ $cmd_exit -eq 124 ]]; then
    AUTO_RESULTS["$commit"]="Command timed out after ${TIMEOUT_SECONDS}s"
    log_error "Auto commit $short_sha: command timed out"
    return 1
  elif [[ $cmd_exit -ne 0 ]]; then
    AUTO_RESULTS["$commit"]="Command failed with exit code $cmd_exit"
    log_error "Auto commit $short_sha: command failed (exit $cmd_exit)"
    return 1
  fi

  # Stage changes: update tracked files and add only NEW untracked files
  git add -u  # Stage modifications to tracked files
  local untracked_after
  untracked_after=$(git ls-files --others --exclude-standard | sort)
  # Add only files that are new (not in untracked_before)
  local new_files
  new_files=$(comm -13 <(echo "$untracked_before") <(echo "$untracked_after"))
  if [[ -n "$new_files" ]]; then
    echo "$new_files" | xargs -r git add
  fi
  local actual_tree
  actual_tree=$(git write-tree)

  # Note: restore_state (via trap) handles returning to ORIGINAL_HEAD

  if [[ "$expected_tree" == "$actual_tree" ]]; then
    AUTO_RESULTS["$commit"]="ok"
    log_ok "Auto commit $short_sha verified"
    return 0
  else
    AUTO_RESULTS["$commit"]="Tree mismatch: command output differs from commit"
    log_error "Auto commit $short_sha: tree mismatch"
    log_error "Diff between expected and actual:"
    show_diff_stat "$expected_tree" "$actual_tree"
    return 1
  fi
}

verify_auto_commits() {
  log_info "Verifying automated commits..."

  if [[ ${#AUTO_COMMITS[@]} -eq 0 ]]; then
    log_info "No automated commits to verify"
    return 0
  fi

  local all_ok=true
  for commit in "${AUTO_COMMITS[@]}"; do
    if ! verify_auto_commit "$commit"; then
      all_ok=false
    fi
  done

  if [[ "$all_ok" == "true" ]]; then
    return 0
  else
    return 1
  fi
}

# --- Run verifications ---
if ! verify_transient; then
  OVERALL_SUCCESS=false
fi

# Restore to original state before auto verification
# (transient verification may have left us in detached HEAD)
restore_state
save_state

if ! verify_auto_commits; then
  OVERALL_SUCCESS=false
fi

# --- Output results ---
output_json() {
  echo "{"
  echo "  \"success\": $([[ "$OVERALL_SUCCESS" == "true" ]] && echo "true" || echo "false"),"

  # Substantive commits
  echo "  \"substantive_commits\": ["
  local first=true
  for commit in "${SUBSTANTIVE_COMMITS[@]}"; do
    [[ "$first" == "true" ]] || echo ","
    first=false
    local subject
    subject=$(git log -1 --format="%s" "$commit" | sed 's/"/\\"/g')
    echo -n "    {\"sha\": \"$commit\", \"short\": \"${commit:0:7}\", \"subject\": \"$subject\"}"
  done
  echo ""
  echo "  ],"

  # Auto commits
  echo "  \"auto_commits\": ["
  first=true
  for commit in "${AUTO_COMMITS[@]}"; do
    [[ "$first" == "true" ]] || echo ","
    first=false
    local subject
    subject=$(git log -1 --format="%s" "$commit" | sed 's/"/\\"/g')
    local result="${AUTO_RESULTS[$commit]:-not_run}"
    local verified=$([[ "$result" == "ok" ]] && echo "true" || echo "false")
    local error_msg=""
    [[ "$result" != "ok" && "$result" != "not_run" ]] && error_msg="$result"
    echo -n "    {\"sha\": \"$commit\", \"short\": \"${commit:0:7}\", \"subject\": \"$subject\", \"verified\": $verified"
    [[ -n "$error_msg" ]] && echo -n ", \"error\": \"$(echo "$error_msg" | sed 's/"/\\"/g')\""
    echo -n "}"
  done
  echo ""
  echo "  ],"

  # Transient commits
  echo "  \"transient_commits\": ["
  first=true
  for commit in "${TRANSIENT_COMMITS[@]}"; do
    [[ "$first" == "true" ]] || echo ","
    first=false
    local subject
    subject=$(git log -1 --format="%s" "$commit" | sed 's/"/\\"/g')
    echo -n "    {\"sha\": \"$commit\", \"short\": \"${commit:0:7}\", \"subject\": \"$subject\"}"
  done
  echo ""
  echo "  ],"

  echo "  \"transient_verified\": $([[ "$TRANSIENT_VERIFIED" == "true" ]] && echo "true" || echo "false")"
  [[ -n "$TRANSIENT_ERROR" ]] && echo "  ,\"transient_error\": \"$(echo "$TRANSIENT_ERROR" | sed 's/"/\\"/g')\""

  echo "}"
}

output_summary() {
  echo ""
  echo "========================================="
  echo "         COMMIT VERIFICATION SUMMARY"
  echo "========================================="
  echo ""

  echo "Substantive commits (${#SUBSTANTIVE_COMMITS[@]}):"
  if [[ ${#SUBSTANTIVE_COMMITS[@]} -eq 0 ]]; then
    echo "  (none)"
  else
    for commit in "${SUBSTANTIVE_COMMITS[@]}"; do
      echo "  - ${commit:0:7}: $(git log -1 --format='%s' "$commit")"
    done
  fi
  echo ""

  echo "Automated commits (${#AUTO_COMMITS[@]}):"
  if [[ ${#AUTO_COMMITS[@]} -eq 0 ]]; then
    echo "  (none)"
  else
    for commit in "${AUTO_COMMITS[@]}"; do
      local result="${AUTO_RESULTS[$commit]:-not_run}"
      if [[ "$result" == "ok" ]]; then
        log_ok "${commit:0:7}: $(git log -1 --format='%s' "$commit")"
      else
        log_error "${commit:0:7}: $(git log -1 --format='%s' "$commit")"
        [[ "$result" != "not_run" ]] && echo "        Error: $result"
      fi
    done
  fi
  echo ""

  echo "Transient commits (${#TRANSIENT_COMMITS[@]}):"
  if [[ ${#TRANSIENT_COMMITS[@]} -eq 0 ]]; then
    echo "  (none)"
  else
    for commit in "${TRANSIENT_COMMITS[@]}"; do
      echo "  - ${commit:0:7}: $(git log -1 --format='%s' "$commit")"
    done
    if [[ "$TRANSIENT_VERIFIED" == "true" ]]; then
      log_ok "Net effect: none (verified)"
    else
      log_error "Verification failed: $TRANSIENT_ERROR"
    fi
  fi
  echo ""

  echo "========================================="
  if [[ "$OVERALL_SUCCESS" == "true" ]]; then
    log_ok "ALL VERIFICATIONS PASSED"
  else
    log_error "VERIFICATION FAILED"
  fi
  echo "========================================="
}

# --- Output ---
if [[ "$JSON_OUTPUT" == "true" ]]; then
  output_json
elif [[ -n "$JSON_FILE" ]]; then
  output_json > "$JSON_FILE"
  output_summary
else
  output_summary
fi

# Exit with appropriate code
if [[ "$OVERALL_SUCCESS" == "true" ]]; then
  exit 0
else
  exit 1
fi
