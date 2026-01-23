#!/usr/bin/env bash
# Commit Verification Script
# Verifies transient commits in a PR have zero net effect
#
# Usage: ./scripts/verify_commits.sh <base_ref>
#
# Exit codes:
#   0 - All verifications passed
#   1 - Verification failed
#   2 - Usage error

set -euo pipefail

# --- Configuration ---
# TRANSIENT_PREFIX can be set via environment variable, defaults to "transient"
TRANSIENT_PREFIX="${TRANSIENT_PREFIX:-transient: }"

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
  echo "Usage: $0 <base_ref>"
  echo ""
  echo "Arguments:"
  echo "  base_ref          The base commit/branch to compare against (e.g., origin/master)"
  exit 2
}

# --- Argument parsing ---
BASE_REF=""

while [[ $# -gt 0 ]]; do
  case "$1" in
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

# Categorize commits
declare -a TRANSIENT_COMMITS=()
declare -a NON_TRANSIENT_COMMITS=()

for commit in "${ALL_COMMITS[@]}"; do
  subject=$(git log -1 --format="%s" "$commit")

  if [[ "$subject" == "$TRANSIENT_PREFIX"* ]]; then
    TRANSIENT_COMMITS+=("$commit")
  else
    NON_TRANSIENT_COMMITS+=("$commit")
  fi
done

log_info "Categorized: ${#NON_TRANSIENT_COMMITS[@]} substantive, ${#TRANSIENT_COMMITS[@]} transient"

# Save state before any checkouts
save_state

# --- Verification results ---
TRANSIENT_VERIFIED=false
TRANSIENT_ERROR=""
OVERALL_SUCCESS=true

# --- Verify transient commits ---
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

# --- Run verifications ---
if ! verify_transient; then
  OVERALL_SUCCESS=false
fi

output_summary() {
  echo ""
  echo "========================================="
  echo "         COMMIT VERIFICATION SUMMARY"
  echo "========================================="
  echo ""

  echo "Substantive commits (${#NON_TRANSIENT_COMMITS[@]}):"
  if [[ ${#NON_TRANSIENT_COMMITS[@]} -eq 0 ]]; then
    echo "  (none)"
  else
    for commit in "${NON_TRANSIENT_COMMITS[@]}"; do
      echo "  - ${commit:0:7}: $(git log -1 --format='%s' "$commit")"
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
output_summary

# Exit with appropriate code
if [[ "$OVERALL_SUCCESS" == "true" ]]; then
  exit 0
else
  exit 1
fi
