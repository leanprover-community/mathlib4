#!/usr/bin/env bash

# Create one GitHub pull request per .diff/.patch file, using the current git
# repository. This script does not clone the repository again; it creates a
# temporary git worktree from the current repository and removes it afterwards.
#
# Usage:
#   scripts/create-prs-from-diffs.sh DIFF_DIR [options]
#
# Required arguments:
#   DIFF_DIR      Directory containing .diff or .patch files.
#
# Common examples:
#   # Dry-run only. This is the default and does not push or create PRs.
#   scripts/create-prs-from-diffs.sh pr_diff
#
#   # Actually push branches and create PRs.
#   scripts/create-prs-from-diffs.sh pr_diff --no-dry-run
#
#   # Explicitly target upstream and push branches to origin.
#   scripts/create-prs-from-diffs.sh pr_diff \
#     --target-repo leanprover-community/mathlib4 \
#     --push-remote origin \
#     --no-dry-run
#
# Options:
#   --base BRANCH          Base branch for PRs. Defaults to the target repo's
#                          default branch.
#   --target-repo REPO     Target GitHub repo for PRs. Accepted forms:
#                          owner/repo, https://github.com/owner/repo,
#                          git@github.com:owner/repo.git.
#                          If omitted, the script uses the only GitHub remote.
#                          If multiple GitHub remotes exist, it asks you to
#                          type the exact target repo.
#   --push-remote REMOTE   Local git remote to push PR branches to. Defaults to
#                          origin when targeting a different remote, otherwise
#                          the target remote.
#   --title-prefix TEXT    PR title prefix. Default: Apply
#   --commit-prefix TEXT   Commit subject prefix. Default: Apply
#   --dry-run              Validate patches only. No push, no PR. This is the
#                          default.
#   --no-dry-run           Push branches and create PRs.
#   --keep-worktree        Keep the temporary worktree for inspection.
#   -h, --help             Show this help.
#
# Remote selection:
#   - If the repository has only one GitHub remote, that remote is used.
#   - If both origin and upstream, or any other multiple GitHub remotes, exist,
#     the script prints all candidates and asks you to type the target repo.
#
# Safety constraints:
#   - Dry-run is enabled by default.
#   - The current working directory is never modified by patch application.
#   - All diffs are validated in a temporary worktree before any push or PR.
#   - Branch names use the diff directory name plus a number, for example
#     pr_diff-001, pr_diff-002.
#   - Existing open PRs for the same head branch are detected and reused.

set -euo pipefail

usage() {
  sed -n '2,66p' "$0" | sed 's/^# \{0,1\}//'
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

need_command() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

try_normalize_github_repo() {
  local input="$1"
  local repo="${input%/}"

  repo="${repo%.git}"
  case "$repo" in
    https://github.com/*)
      repo="${repo#https://github.com/}"
      ;;
    http://github.com/*)
      repo="${repo#http://github.com/}"
      ;;
    git@github.com:*)
      repo="${repo#git@github.com:}"
      ;;
    ssh://git@github.com/*)
      repo="${repo#ssh://git@github.com/}"
      ;;
  esac

  repo="${repo%/}"
  repo="${repo%.git}"

  [[ "$repo" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] || return 1
  printf '%s\n' "$repo"
}

normalize_github_repo() {
  local input="$1"
  try_normalize_github_repo "$input" || die "not a supported GitHub repo address: $input"
}

slugify() {
  local value="$1"
  value="$(printf '%s' "$value" |
    tr '[:upper:]' '[:lower:]' |
    sed -E 's/[^a-z0-9._-]+/-/g; s/-+/-/g; s/^-//; s/-$//')"

  if [[ -z "$value" ]]; then
    value="patch"
  fi

  printf '%s\n' "${value:0:80}"
}

read_from_tty_or_stdin() {
  local __var="$1"
  local answer

  if [[ -r /dev/tty ]]; then
    IFS= read -r answer </dev/tty
  else
    IFS= read -r answer
  fi

  printf -v "$__var" '%s' "$answer"
}

resolve_remote_slug() {
  local remote="$1"
  local url
  url="$(git remote get-url "$remote")" || return 1
  try_normalize_github_repo "$url"
}

find_remote_for_slug() {
  local slug="$1"
  local remote
  local remote_slug

  for remote in "${remote_names[@]}"; do
    remote_slug="${remote_slugs_by_name[$remote]}"
    if [[ "$remote_slug" == "$slug" ]]; then
      printf '%s\n' "$remote"
      return 0
    fi
  done

  return 1
}

choose_target_repo() {
  local input
  local slug
  local remote

  if [[ -n "$target_repo_input" ]]; then
    slug="$(normalize_github_repo "$target_repo_input")"
    remote="$(find_remote_for_slug "$slug")" ||
      die "--target-repo must match one of this repository's GitHub remotes: $target_repo_input"
    target_slug="$slug"
    target_remote="$remote"
    return
  fi

  if [[ "${#remote_names[@]}" -eq 1 ]]; then
    target_remote="${remote_names[0]}"
    target_slug="${remote_slugs_by_name[$target_remote]}"
    return
  fi

  printf 'Multiple GitHub remotes found. Choose the target repository for PRs:\n'
  for remote in "${remote_names[@]}"; do
    printf '  %s -> https://github.com/%s\n' "$remote" "${remote_slugs_by_name[$remote]}"
  done
  printf 'Type the target repository exactly, for example owner/repo or https://github.com/owner/repo:\n> '
  read_from_tty_or_stdin input

  slug="$(normalize_github_repo "$input")"
  remote="$(find_remote_for_slug "$slug")" ||
    die "typed target repo does not match any configured GitHub remote: $input"

  target_slug="$slug"
  target_remote="$remote"
}

dry_run=1
base_branch=""
target_repo_input=""
push_remote_input=""
title_prefix="Apply"
commit_prefix="Apply"
keep_worktree=0
declare -a positional=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --base)
      [[ $# -ge 2 ]] || die "--base requires a value"
      base_branch="$2"
      shift 2
      ;;
    --target-repo)
      [[ $# -ge 2 ]] || die "--target-repo requires a value"
      target_repo_input="$2"
      shift 2
      ;;
    --push-remote)
      [[ $# -ge 2 ]] || die "--push-remote requires a value"
      push_remote_input="$2"
      shift 2
      ;;
    --title-prefix)
      [[ $# -ge 2 ]] || die "--title-prefix requires a value"
      title_prefix="$2"
      shift 2
      ;;
    --commit-prefix)
      [[ $# -ge 2 ]] || die "--commit-prefix requires a value"
      commit_prefix="$2"
      shift 2
      ;;
    --dry-run)
      dry_run=1
      shift
      ;;
    --no-dry-run)
      dry_run=0
      shift
      ;;
    --keep-worktree)
      keep_worktree=1
      shift
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    --)
      shift
      positional+=("$@")
      break
      ;;
    -*)
      die "unknown option: $1"
      ;;
    *)
      positional+=("$1")
      shift
      ;;
  esac
done

[[ ${#positional[@]} -eq 1 ]] || {
  usage >&2
  exit 2
}

need_command git
need_command gh
need_command find
need_command sort
need_command sed
need_command tr

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

diff_dir="${positional[0]}"
[[ -d "$diff_dir" ]] || die "diff directory does not exist: $diff_dir"
diff_dir="$(cd "$diff_dir" && pwd -P)"

mapfile -d '' diff_files < <(
  find "$diff_dir" -maxdepth 1 -type f \( -name '*.diff' -o -name '*.patch' \) -print0 | sort -z
)
[[ ${#diff_files[@]} -gt 0 ]] || die "no .diff or .patch files found in $diff_dir"

declare -a remote_names=()
declare -A remote_slugs_by_name=()

while IFS= read -r remote; do
  [[ -n "$remote" ]] || continue
  if slug="$(resolve_remote_slug "$remote")"; then
    remote_names+=("$remote")
    remote_slugs_by_name["$remote"]="$slug"
  fi
done < <(git remote)

[[ ${#remote_names[@]} -gt 0 ]] || die "no GitHub remotes found in the current repository"

target_slug=""
target_remote=""
choose_target_repo

if [[ -n "$push_remote_input" ]]; then
  git remote get-url "$push_remote_input" >/dev/null ||
    die "--push-remote is not a configured remote: $push_remote_input"
  push_remote="$push_remote_input"
else
  if [[ "$target_remote" != "origin" ]] && git remote get-url origin >/dev/null 2>&1; then
    push_remote="origin"
  else
    push_remote="$target_remote"
  fi
fi

push_slug="$(resolve_remote_slug "$push_remote")" ||
  die "push remote is not a supported GitHub remote: $push_remote"
push_owner="${push_slug%%/*}"

if [[ -z "$base_branch" ]]; then
  base_branch="$(gh repo view "$target_slug" --json defaultBranchRef --jq '.defaultBranchRef.name')"
fi

target_url="https://github.com/${target_slug}"
push_url="https://github.com/${push_slug}"
branch_base="$(slugify "$(basename "$diff_dir")")"
base_ref="refs/remotes/${target_remote}/${base_branch}"

if [[ "$dry_run" -eq 0 ]]; then
  gh auth status >/dev/null 2>&1 || die "gh is not authenticated; run 'gh auth login' first"
fi

printf 'Plan:\n'
printf '  mode: %s\n' "$([[ "$dry_run" -eq 1 ]] && printf 'dry-run' || printf 'create PRs')"
printf '  current repository: %s\n' "$repo_root"
printf '  diff directory: %s\n' "$diff_dir"
printf '  target remote: %s\n' "$target_remote"
printf '  target repo: %s\n' "$target_url"
printf '  push remote: %s\n' "$push_remote"
printf '  push repo: %s\n' "$push_url"
printf '  base branch: %s\n' "$base_branch"
printf '  branch name base: %s\n' "$branch_base"
printf '  diff files: %d\n' "${#diff_files[@]}"

if [[ "$dry_run" -eq 1 ]]; then
  printf '\nDry-run is ON: no git push or gh pr create command will be run.\n'
fi

printf '\nFetching base branch from target remote...\n'
git fetch --no-tags "$target_remote" "+refs/heads/${base_branch}:${base_ref}"

work_parent=""
cleanup() {
  if [[ -n "${work_parent:-}" && -d "$work_parent" ]]; then
    if [[ "$keep_worktree" -eq 1 ]]; then
      printf 'kept temporary worktree: %s\n' "$work_parent"
    else
      git worktree remove --force "${work_parent}/repo" >/dev/null 2>&1 || true
      rm -rf "$work_parent"
    fi
  fi
}
trap cleanup EXIT

work_parent="$(mktemp -d "${TMPDIR:-/tmp}/create-prs-from-diffs.XXXXXX")"
worktree="${work_parent}/repo"

printf '\nCreating temporary worktree from current repository...\n'
git worktree add --quiet --detach "$worktree" "$base_ref"

cd "$worktree"

if ! git config user.name >/dev/null; then
  git config user.name "create-prs-from-diffs"
fi
if ! git config user.email >/dev/null; then
  git config user.email "create-prs-from-diffs@example.invalid"
fi

declare -a branches=()
declare -a titles=()
declare -a diff_names=()
declare -a body_files=()

validate_diff() {
  local diff_file="$1"
  local diff_name="$2"

  git reset --hard --quiet "$base_ref"
  git clean -fdx --quiet
  git apply --check "$diff_file"
  git apply "$diff_file"

  if git diff --quiet --exit-code; then
    die "diff produced no changes after applying: $diff_file"
  fi

  git add -A
  git commit --quiet -m "Validate ${diff_name}" -m "Dry validation commit; not pushed."
}

prepare_branch() {
  local diff_file="$1"
  local diff_name="$2"
  local branch="$3"
  local commit_subject="$4"

  git checkout --quiet -B "$branch" "$base_ref"
  git reset --hard --quiet "$base_ref"
  git clean -fdx --quiet
  git apply "$diff_file"
  git add -A
  git commit --quiet -m "$commit_subject" -m "Created from diff file: ${diff_name}"
}

printf '\nValidating diffs in temporary worktree...\n'
diff_index=0
for diff_file in "${diff_files[@]}"; do
  diff_index=$((diff_index + 1))
  diff_name="$(basename "$diff_file")"
  stem="${diff_name%.*}"
  hash="$(git hash-object "$diff_file" | cut -c1-10)"
  branch="$(printf '%s-%03d' "$branch_base" "$diff_index")"
  title="${title_prefix} ${stem}"
  body_file="${work_parent}/body-${hash}.md"

  printf '  checking %s -> %s\n' "$diff_name" "$branch"
  validate_diff "$diff_file" "$diff_name"

  {
    printf 'Created from diff file `%s`.\n\n' "$diff_name"
    printf 'Target repository: `%s`\n' "$target_slug"
    printf 'Base branch: `%s`\n' "$base_branch"
  } >"$body_file"

  branches+=("$branch")
  titles+=("$title")
  diff_names+=("$diff_name")
  body_files+=("$body_file")
done

printf '\nValidated %d diff file(s).\n' "${#branches[@]}"

if [[ "$dry_run" -eq 1 ]]; then
  printf '\nDry-run result:\n'
  for index in "${!branches[@]}"; do
    printf '  would create PR: %-70s from %s\n' "${titles[$index]}" "${branches[$index]}"
  done
  printf '\nNo branches were pushed and no PRs were created.\n'
  exit 0
fi

printf '\nCreating branches, pushing, and opening PRs...\n'
for index in "${!branches[@]}"; do
  diff_file="${diff_files[$index]}"
  diff_name="${diff_names[$index]}"
  branch="${branches[$index]}"
  title="${titles[$index]}"
  body_file="${body_files[$index]}"
  commit_subject="${commit_prefix} ${diff_name%.*}"

  printf '  preparing %s\n' "$branch"
  prepare_branch "$diff_file" "$diff_name" "$branch" "$commit_subject"

  printf '  pushing %s to %s\n' "$branch" "$push_remote"
  git push --force-with-lease "$push_remote" "${branch}:refs/heads/${branch}"

  existing_pr="$(
    gh pr list \
      --repo "$target_slug" \
      --head "${push_owner}:${branch}" \
      --state open \
      --json url \
      --jq '.[0].url // ""'
  )"

  if [[ -n "$existing_pr" ]]; then
    printf '  existing PR: %s\n' "$existing_pr"
    continue
  fi

  gh pr create \
    --repo "$target_slug" \
    --base "$base_branch" \
    --head "${push_owner}:${branch}" \
    --title "$title" \
    --body-file "$body_file"
done

printf '\nDone.\n'
