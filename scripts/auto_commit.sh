#!/usr/bin/env bash
# Auto-Commit Script
# Runs a command and creates a commit with the result
#
# Usage: scripts/auto_commit.sh <command>...
#
# The commit message will be: x scripts/auto_commit.sh <command>
#
# This format enables a rebase workflow: during interactive rebase, you can
# convert "pick abc123 x scripts/auto_commit.sh <cmd>" to "x scripts/auto_commit.sh <cmd>"
# (by deleting the "pick abc123 " prefix), and git will re-run the command via exec.
#
# Examples:
#   scripts/auto_commit.sh lake exe mk_all
#   scripts/auto_commit.sh ./scripts/fix_unused.py
#
# Exit codes:
#   0 - Success (commit created or no changes to commit)
#   1 - Command failed
#   2 - Usage error

set -euo pipefail

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

log_info()  { echo -e "${BLUE}[INFO]${NC} $*" >&2; }
log_ok()    { echo -e "${GREEN}[OK]${NC} $*" >&2; }
log_warn()  { echo -e "${YELLOW}[WARN]${NC} $*" >&2; }
log_error() { echo -e "${RED}[ERROR]${NC} $*" >&2; }

usage() {
  echo "Usage: $0 <command>..."
  echo ""
  echo "Runs a command and creates a commit with message:"
  echo "  x scripts/auto_commit.sh <command>"
  echo ""
  echo "Examples:"
  echo "  $0 lake exe mk_all"
  echo "  $0 ./scripts/fix_unused.py"
  exit 2
}

if [[ $# -eq 0 ]]; then
  log_error "No command specified"
  usage
fi

COMMAND="$*"
COMMIT_MSG="x scripts/auto_commit.sh $COMMAND"

log_info "Running: $COMMAND"

# Run the command
cmd_exit=0
bash -c "$COMMAND" || cmd_exit=$?

if [[ $cmd_exit -ne 0 ]]; then
  log_error "Command failed with exit code $cmd_exit"
  exit 1
fi

log_ok "Command completed successfully"

# Stage all changes (modifications to tracked files + new untracked files)
# Note: We use -A to add everything, matching what verify_commits.sh expects
git add -A

# Check if there are any staged changes
if git diff --cached --quiet; then
  log_warn "No changes to commit"
  exit 0
fi

# Show what we're about to commit
log_info "Changes to commit:"
git diff --cached --stat >&2

# Create the commit
log_info "Creating commit: $COMMIT_MSG"
git commit -m "$COMMIT_MSG"

log_ok "Commit created successfully"
