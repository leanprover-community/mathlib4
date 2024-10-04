#!/usr/bin/env bash

set -e # abort whenever a command in the script fails

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

# Check the CI status of the latest commit on the 'nightly-testing' branch
status=$(gh run list --branch nightly-testing | grep -m1 . | awk '{print $1}')
if [ "$status" != "completed" ]; then
  if [ "$status" != "in_progress" ]; then
    echo "The latest commit on the 'nightly-testing' branch did not pass CI. Please fix the issues and try again."
    gh run list --branch nightly-testing
    exit 1
  else
    if [ "$AUTO" = "yes" ]; then
      echo "Auto mode enabled. Bailing out because the latest commit on 'nightly-testing' is still running CI."
      exit 1
    else
      echo "The latest commit on 'nightly-testing' is still running CI."
      read -p "Press enter to continue, or ctrl-C if you'd prefer to wait for CI."
    fi
  fi
fi

echo "### Creating a PR for the nightly adaptation for $NIGHTLYDATE"

echo
echo "### [auto] save the current branch name"

usr_branch=$(git branch --show-current)

echo
echo "### [auto] checkout master and pull the latest changes"

git checkout master
git pull

echo
echo "### [auto] checkout 'bump/$BUMPVERSION' and merge the latest changes from 'origin/master'"

git checkout "bump/$BUMPVERSION"
git pull
git merge origin/master || true # ignore error if there are conflicts

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
  echo "We are merging the latest changes from 'origin/master' into 'bump/$BUMPVERSION'"
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
echo "### [auto] create a new branch 'bump/nightly-$NIGHTLYDATE' and merge the latest changes from 'origin/nightly-testing'"

git checkout -b "bump/nightly-$NIGHTLYDATE"
git merge $NIGHTLYSHA || true # ignore error if there are conflicts

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
  echo "We are merging the latest changes from 'origin/nightly-testing' into 'bump/nightly-$NIGHTLYDATE'"
  echo "Specifically, we are merging the following version of 'origin/nightly-testing':"
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
git push --set-upstream origin "bump/nightly-$NIGHTLYDATE"

# Check if there is a diff between bump/nightly-$NIGHTLYDATE and bump/$BUMPVERSION
if git diff --name-only bump/$BUMPVERSION bump/nightly-$NIGHTLYDATE | grep -q .; then

  echo
  echo "### [auto/user] create a PR for the new branch"
  echo "Create a pull request. Set the base of the PR to 'bump/$BUMPVERSION'"
  echo "Here is a suggested 'gh' command to do this:"
  gh_command="gh pr create -t \"$pr_title\" -b '' -B bump/$BUMPVERSION"
  echo "> $gh_command"
  if [ "$AUTO" = "yes" ]; then
    echo "Auto mode enabled. Running the command..."
    answer="y"
  else
    echo "Shall I run this command for you? (y/n)"
    read answer
  fi
  if [ "$answer" != "${answer#[Yy]}" ]; then
  	gh_output=$(eval $gh_command)
  	# Extract the PR number from the output
  	pr_number=$(echo $gh_output | sed 's/.*\/pull\/\([0-9]*\).*/\1/')
  fi
  
  echo
  echo "### [auto/user] post a link to the PR on Zulip"
  
  zulip_title="#$pr_number adaptations for nightly-$NIGHTLYDATE"
  zulip_body="> $pr_title #$pr_number"
  
  echo "Post the link to the PR in a new thread on the #nightly-testing channel on Zulip"
  echo "Here is a suggested message:"
  echo "Title: $zulip_title"
  echo " Body: $zulip_body"

  if command -v zulip-send >/dev/null 2>&1; then
    zulip_command="zulip-send --stream nightly-testing --subject \"$zulip_title\" --message \"$zulip_body\""
    echo "Here is a suggested 'zulip-send' command to do this:"
    echo "> $zulip_command"
  
    if [ "$AUTO" = "yes" ]; then
      echo "Auto mode enabled. Running the command..."
      answer="y"
    else
      echo "Shall I run this command for you? (y/n)"
      read answer
    fi
  
    if [ "$answer" != "${answer#[Yy]}" ]; then
      eval $zulip_command
    fi
  else
    echo "Zulip CLI is not installed. Please install it to send messages automatically."
    if [ "$AUTO" = "yes" ]; then
      exit 1
    fi
  fi
  
  if [ "$AUTO" != "yes" ]; then
    read -p "Press enter to continue"
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
git pull
git merge "bump/nightly-$NIGHTLYDATE" || true # ignore error if there are conflicts

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
    echo "Error occured while merging the new branch into 'nightly-testing'."
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
git push

echo
echo "### [auto] finished: checkout the original branch"

git checkout $usr_branch

# These last two lines are needed to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches
# See the top of the file for more details.
exit
}
