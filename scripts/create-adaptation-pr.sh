#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# We need to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches.
# We do that by making sure the entire script is parsed before execution starts
# using the following pattern
# {
# # script content
# exit
# }
# (see https://stackoverflow.com/a/2358432).
# So please do not delete the following line, or the final two lines of this script.
{

# Default values
AUTO="no"

# Set MATHLIB_REPO to current repository if not provided
if [ -z "${MATHLIB_REPO:-}" ]; then
  MATHLIB_REPO="leanprover-community/mathlib4"
fi

# Function to validate and setup remotes
setup_remotes() {
  echo "### Validating remote configuration..."

  # Check if we have a remote for the main mathlib4 repository
  MAIN_REMOTE=$(find_remote "leanprover-community/mathlib4")
  if [ -z "$MAIN_REMOTE" ]; then
    echo "Adding remote 'upstream' for leanprover-community/mathlib4"
    git remote add upstream https://github.com/leanprover-community/mathlib4.git
    MAIN_REMOTE="upstream"
  fi

  # Check if we have a remote for the nightly-testing fork
  NIGHTLY_REMOTE=$(find_remote "leanprover-community/mathlib4-nightly-testing")
  if [ -z "$NIGHTLY_REMOTE" ]; then
    echo "Adding remote 'nightly-testing' for leanprover-community/mathlib4-nightly-testing"
    git remote add nightly-testing https://github.com/leanprover-community/mathlib4-nightly-testing.git
    NIGHTLY_REMOTE="nightly-testing"
  fi

  echo "Remote configuration:"
  echo "  Main repository ($MAIN_REMOTE): leanprover-community/mathlib4"
  echo "  Nightly testing ($NIGHTLY_REMOTE): leanprover-community/mathlib4-nightly-testing"
}

# Function to display usage
usage() {
  echo "Usage: $0 <BUMPVERSION> <NIGHTLYDATE>"
  echo "       or"
  echo "       $0 --bumpversion=<BUMPVERSION> --nightlydate=<NIGHTLYDATE> --nightlysha=<SHA> [--auto=<yes|no>]"
  echo "BUMPVERSION: The upcoming release that we are targeting, e.g., 'v4.10.0'"
  echo "NIGHTLYDATE: The date of the nightly toolchain currently used on 'nightly-testing'"
  echo "NIGHTLYSHA: The SHA of the nightly toolchain that we want to adapt to"
  echo "AUTO: Optional flag to specify automatic mode, default is 'no'"
  exit 1
}

# Function to find remote for a given repository
find_remote() {
  local repo_pattern="$1"
  # Use || true to prevent script exit if any command in the pipeline fails
  # This handles cases where git remote fails or grep doesn't find matches
  git remote -v | grep -E "$repo_pattern(\.git)? \(fetch\)" | head -n1 | cut -f1 || true
}

# Parse arguments
if [ $# -eq 2 ] && [[ $1 != --* ]] && [[ $2 != --* ]]; then
  BUMPVERSION=$1
  NIGHTLYDATE=$2
elif [ $# -ge 2 ]; then
  for arg in "$@"; do
    case $arg in
      --bumpversion=*)
        BUMPVERSION="${arg#*=}"
        shift
        ;;
      --nightlydate=*)
        NIGHTLYDATE="${arg#*=}"
        shift
        ;;
      --nightlysha=*)
        NIGHTLYSHA="${arg#*=}"
        shift
        ;;
      --auto=*)
        AUTO="${arg#*=}"
        shift
        ;;
      *)
        usage
        ;;
    esac
  done
else
  usage
fi

# Validate required arguments
if [ -z "$BUMPVERSION" ] || [ -z "$NIGHTLYDATE" ]; then
  usage
fi

# Check if 'gh' command is available
if ! command -v gh &> /dev/null; then
    echo "'gh' (GitHub CLI) is not installed. Please install it and try again."
    exit 1
fi

# Setup and validate remotes
setup_remotes

echo "### Creating a PR for the nightly adaptation for $NIGHTLYDATE"

echo
echo "### [auto] save the current branch name"

usr_branch=$(git branch --show-current)

echo
echo "### [auto] checkout master and pull the latest changes"

git fetch $MAIN_REMOTE master

# Ensure local master branch exists and tracks $MAIN_REMOTE/master
if git show-ref --verify --quiet refs/heads/master; then
  git checkout master
  git pull $MAIN_REMOTE master
else
  git checkout -b master $MAIN_REMOTE/master
fi

echo
echo "### [auto] checkout 'bump/$BUMPVERSION' and merge the latest changes from '$MAIN_REMOTE/master'"

git checkout "bump/$BUMPVERSION"
git pull $MAIN_REMOTE "bump/$BUMPVERSION"
git merge --no-edit $MAIN_REMOTE/master || true # ignore error if there are conflicts

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo
  echo "### [auto] Conflict resolution"
  echo "### Automatically choosing 'lean-toolchain' and 'lake-manifest.json' from the newer branch"
  echo "### In this case, the newer branch is 'bump/$BUMPVERSION'"
  git checkout bump/$BUMPVERSION -- lean-toolchain lake-manifest.json
  git add lean-toolchain lake-manifest.json

  # Check if there are more merge conflicts after auto-resolution
  if ! git diff --name-only --diff-filter=U | grep -q .; then
    # Auto-commit the resolved conflicts if no other conflicts remain
    git commit -m "Auto-resolved conflicts in lean-toolchain and lake-manifest.json"
  fi
fi

if git diff --name-only --diff-filter=U | grep -q . || ! git diff-index --quiet HEAD --; then
  if [ "$AUTO" = "yes" ]; then
    echo "Auto mode enabled. Bailing out due to unresolved conflicts or uncommitted changes."
    exit 1
  fi
fi

# Loop until all conflicts are resolved and committed
while git diff --name-only --diff-filter=U | grep -q . || ! git diff-index --quiet HEAD --; do
  echo
  echo "### [user] Conflict resolution"
  echo "We are merging the latest changes from '$MAIN_REMOTE/master' into 'bump/$BUMPVERSION'"
  echo "There seem to be conflicts or uncommitted files"
  echo ""
  echo "  1) Open `pwd` in a new terminal and run 'git status'"
  echo "  2) Make sure to commit the resolved conflicts, but do not push them"
  read -p "  3) Press enter to continue, when you are done"
done

echo "All conflicts resolved and committed."
echo "Proceeding with git push..."
git push

echo
echo "### [auto] create a new branch 'bump/nightly-$NIGHTLYDATE' and merge the latest changes from nightly-testing"

git checkout -b "bump/nightly-$NIGHTLYDATE" || git checkout "bump/nightly-$NIGHTLYDATE"
git merge --no-edit $NIGHTLYSHA || true # ignore error if there are conflicts

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo
  echo "### [auto] Conflict resolution"
  echo "### Automatically choosing 'lean-toolchain' and 'lake-manifest.json' from 'nightly-testing'"
  git checkout $NIGHTLYSHA -- lean-toolchain lake-manifest.json
  git add lean-toolchain lake-manifest.json
fi

if git diff --name-only --diff-filter=U | grep -q .; then
  if [ "$AUTO" = "yes" ]; then
    echo "Auto mode enabled. Bailing out due to unresolved conflicts or uncommitted changes."
    exit 1
  fi
fi

# Check if there are more merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo
  echo "### [user] Conflict resolution"
  echo "We are merging the latest changes from nightly-testing into 'bump/nightly-$NIGHTLYDATE'"
  echo "Specifically, we are merging the following version of nightly-testing:"
  echo "$NIGHTLYSHA"
  echo "There seem to be conflicts: please resolve them"
  echo ""
  echo "  1) Open `pwd` in a new terminal and run 'git status'"
  echo "  2) Run 'git add' on the resolved files, but do not commit"
  read -p "  3) Press enter to continue, when you are done"
fi

echo
echo "### [auto] commit the changes and push the branch"

pr_title="chore: adaptations for nightly-$NIGHTLYDATE"
# Create a commit with the PR title
# We allow an empty commit,
# as the user might have inadvertently already committed changes
# In general, we do not want this command to fail.
git commit --allow-empty -m "$pr_title"
git push --set-upstream $NIGHTLY_REMOTE "bump/nightly-$NIGHTLYDATE"

# Check if there is a diff between bump/nightly-$NIGHTLYDATE and bump/$BUMPVERSION
if git diff --name-only bump/$BUMPVERSION bump/nightly-$NIGHTLYDATE | grep -q .; then

  echo
  echo "### [auto] create a PR for the new branch"
  echo "Creating a pull request. Setting the base of the PR to 'bump/$BUMPVERSION'"
  echo "Running the following 'gh' command to do this:"
  gh_command="gh pr create -t \"$pr_title\" -b '' -B bump/$BUMPVERSION --repo leanprover-community/mathlib4-nightly-testing"
  echo "> $gh_command"
  gh_output=$(eval $gh_command)
  # Extract the PR number from the output
  pr_number=$(echo $gh_output | sed 's/.*\/pull\/\([0-9]*\).*/\1/')

  echo
  echo "### [auto] post a link to the PR on Zulip"

  zulip_title="nightly#$pr_number adaptations for nightly-$NIGHTLYDATE"
  zulip_body=$(printf "> %s\n\nPlease review this PR. At the end of the month this diff will land in 'master'." "$pr_title nightly#$pr_number")

  echo "Posting the link to the PR in a new thread on the #nightly-testing channel on Zulip"
  echo "Here is the message:"
  echo "Title: $zulip_title"
  echo " Body: $zulip_body"

  if command -v zulip-send >/dev/null 2>&1; then
    zulip_command="zulip-send --stream nightly-testing --subject \"$zulip_title\" --message \"$zulip_body\""
    echo "Running the following 'zulip-send' command to do this:"
    echo "> $zulip_command"
    eval $zulip_command
  else
    echo "Zulip CLI is not installed. Install it to send messages automatically."
    if [ "$AUTO" = "yes" ]; then
      exit 1
    else
      echo "Please send the message manually."
      read -p "Press enter to continue"
    fi
  fi

# else, let the user know that no PR is needed
else
  echo
  echo "### [auto] No PR needed"
  echo "The changes in 'bump/nightly-$NIGHTLYDATE' are the same as in 'bump/$BUMPVERSION'"
  echo "No PR is needed"

fi

echo
echo "### [auto] checkout the 'nightly-testing' branch and merge the new branch into it"

git checkout nightly-testing
git pull $NIGHTLY_REMOTE nightly-testing
git merge --no-edit "bump/nightly-$NIGHTLYDATE" || true # ignore error if there are conflicts

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo
  echo "### [auto] Conflict resolution"
  echo "### Automatically choosing lean-toolchain and lake-manifest.json from the newer branch"
  echo "### In this case, the newer branch is 'bump/nightly-$NIGHTLYDATE'"
  git checkout bump/nightly-$NIGHTLYDATE -- lean-toolchain lake-manifest.json
  git add lean-toolchain lake-manifest.json

  # Check if there are more merge conflicts after auto-resolution
  if ! git diff --name-only --diff-filter=U | grep -q .; then
    # Auto-commit the resolved conflicts if no other conflicts remain
    git commit -m "Auto-resolved conflicts in lean-toolchain and lake-manifest.json"
  fi
fi

if git diff --name-only --diff-filter=U | grep -q . || ! git diff-index --quiet HEAD --; then
  if [ "$AUTO" = "yes" ]; then
    echo "Auto mode enabled. Bailing out due to unresolved conflicts or uncommitted changes."
    echo "PR has been created, and message posted to Zulip."
    echo "Error occurred while merging the new branch into 'nightly-testing'."
    exit 2
  fi
fi

# Loop until all conflicts are resolved and committed
while git diff --name-only --diff-filter=U | grep -q . || ! git diff-index --quiet HEAD --; do
  echo
  echo "### [user] Conflict resolution"
  echo "We are merging the new PR "bump/nightly-$NIGHTLYDATE" into 'nightly-testing'"
  echo "There seem to be conflicts or uncommitted files"
  echo ""
  echo "  1) Open `pwd` in a new terminal and run 'git status'"
  echo "  2) Make sure to commit the resolved conflicts, but do not push them"
  read -p "  3) Press enter to continue, when you are done"
done

echo "All conflicts resolved and committed."
echo "Proceeding with git push..."
git push $NIGHTLY_REMOTE nightly-testing

echo
echo "### [auto] finished: checkout the original branch"

git checkout $usr_branch

# These last two lines are needed to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches
# See the top of the file for more details.
exit
}
