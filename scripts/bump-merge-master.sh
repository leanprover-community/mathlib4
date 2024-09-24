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
  echo "Usage: $0 --bumpversion=<BUMPVERSION> [--auto=<yes|no>]"
  echo "BUMPVERSION: The upcoming release that we are targeting, e.g., 'v4.10.0'"
  echo "AUTO: Optional flag to specify automatic mode, default is 'no'"
  exit 1
}

# Parse arguments
for arg in "$@"; do
  case $arg in
    --bumpversion=*)
      BUMPVERSION="${arg#*=}"
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

# Validate required arguments
if [ -z "$BUMPVERSION" ]; then
  usage
fi

if [ "$AUTO" != "yes" ] && [ "$AUTO" != "no" ]; then
  usage
fi

# If in auto mode, check that `gh` and `zulip-send` are installed.
if [ "$AUTO" = "yes" ]; then
  if ! command -v gh &> /dev/null; then
    echo "The 'gh' command is not installed. Please install it to run in auto mode."
    exit 1
  fi
  if ! command -v zulip-send &> /dev/null; then
    echo "The 'zulip-send' command is not installed. Please install it to run in auto mode."
    exit 1
  fi
fi

echo "### Creating a PR that merges 'master' into 'bump/$BUMPVERSION' while resolving conflicts"

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
timestamp=$(date +'%Y%m%d%H%M')
new_branch="merge-master-into-bump-$BUMPVERSION-$timestamp"
git checkout -b "$new_branch"

# Merge master into the new branch
git merge origin/master || true # ignore error if there are conflicts

# Check if there are merge conflicts
if git diff --name-only --diff-filter=U | grep -q .; then
  echo
  echo "### [auto] Conflict resolution"
  echo "### Automatically choosing 'lean-toolchain' from 'bump/$BUMPVERSION'"
  git checkout bump/$BUMPVERSION -- lean-toolchain lake-manifest.json
  git add lean-toolchain lake-manifest.json
  
  # Check if there are more merge conflicts after auto-resolution
  if ! git diff --name-only --diff-filter=U | grep -q .; then
    # Auto-commit the resolved conflicts if no other conflicts remain
    git commit -m "Auto-resolved conflicts in 'lean-toolchain'"
  fi
fi

# Loop until all conflicts are resolved and committed
while git diff --name-only --diff-filter=U | grep -q . || ! git diff-index --quiet HEAD --; do
  echo
  echo "### [user] Conflict resolution"
  echo "We are merging the latest changes from 'origin/master' into 'bump/$BUMPVERSION'"
  echo "There seem to be conflicts or uncommitted files"
  echo ""
  echo "  1) Open `pwd` in a new terminal and run the following command to list files with conflicts"
  echo "     > git diff --name-only --diff-filter=U"
  echo "  2) Make sure to commit the resolved conflicts, but do not push them"
  read -p "  3) Press enter to continue, when you are done"
done

echo "### [auto/user] Create a PR for the resolved conflicts"
echo "Create a pull request. Set the base of the PR to 'bump/$BUMPVERSION'"

pr_title="chore: merge master into bump/$BUMPVERSION and resolve conflicts"
gh_command="gh pr create -t \"$pr_title\" -b '' -B bump/$BUMPVERSION"

# Function to create PR using gh
create_pr_with_gh() {
  gh_output=$(eval $gh_command 2>&1)
  if [ $? -ne 0 ]; then
    echo "Error: Failed to create PR using gh. Output:"
    echo "$gh_output"
    exit 1
  fi
  # Extract the PR number from the output
  pr_number=$(echo $gh_output | sed 's/.*\/pull\/\([0-9]*\).*/\1/')
}

# Function to create PR manually
create_pr_manually() {
  cat <<EOF
1. Push your changes to the remote repository.
   git push origin $new_branch
2. Go to the GitHub repository in your web browser.
3. Navigate to the 'Pull requests' tab.
4. Click on 'New pull request'.
5. Set the base branch to 'bump/$BUMPVERSION'.
6. Add a title and description for your PR.
   Suggested title: $pr_title
7. Click 'Create pull request'.
EOF
}

# Check if `gh` is installed
if command -v gh &> /dev/null; then
  if [ "$AUTO" = "yes" ]; then
    echo "Auto mode enabled. Creating PR..."
    create_pr_with_gh
  else
    echo "Here is a suggested 'gh' command to do this:"
    echo "> $gh_command"
    echo "Shall I run this command for you? (y/n)"
    read answer
    if [ "$answer" != "${answer#[Yy]}" ]; then
      create_pr_with_gh
    else
      create_pr_manually
      echo "Please enter the PR number below."
      read -p "PR number: " pr_number
    fi
  fi
else
  cat <<EOF
GitHub CLI (gh) is not installed.
Please install GitHub CLI (gh) to create a PR more easily.
Alternatively, you can create a PR manually by following these steps:
EOF
  create_pr_manually
  echo "Please enter the PR number below."
  read -p "PR number: " pr_number
fi

# Output the PR number
echo "PR number: $pr_number"

echo
echo "### [auto/user] post a link to the PR on Zulip"

zulip_title="merge master into bump/$BUMPVERSION"
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
    zulip_output=$(eval $zulip_command 2>&1)
    if [ $? -ne 0 ]; then
      echo "Error: Failed to post PR to zulip. Output:"
      echo "$zulip_output"
      exit 1
    fi
  fi
else
  echo "Zulip CLI is not installed. Please install it to send messages automatically."
  if [ "$AUTO" = "yes" ]; then
    exit 1
  fi
fi

}
