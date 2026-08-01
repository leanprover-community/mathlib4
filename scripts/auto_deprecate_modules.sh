#!/usr/bin/env bash

# auto_deprecate_modules.sh: maintain a stacked `deprecated_module` stub PR
# for a parent PR that deletes or renames Lean modules.
#
# For parent PR #N, this script:
#   * finds every `Mathlib/`, `Archive/` or `Counterexamples/` module that
#     #N deletes or renames (vs the merge base with the target branch);
#   * generates one `deprecated_module` stub per moved module, plus the
#     matching `public import` lines in the root import files
#     (`Mathlib.lean`, `Mathlib/Tactic.lean`, `Archive.lean`,
#     `Counterexamples.lean`);
#   * commits them on branch `deprecation-stubs/pr-N`, based on the head
#     commit of #N. The branch lives in the repository given by --push-repo
#     (a fork in the same fork network, e.g. mathlib4_copy), so the token
#     never needs push access to the main repository;
#   * opens (or refreshes) a PR for that branch against the target branch,
#     and chains it to #N with a `bors stack #N` comment. Bors then merges
#     both PRs atomically, parent first, so the old module names always
#     resolve on the target branch. Bors compares bundle members by commit
#     SHA, so a fork-hosted stub branch works.
#
# SECURITY: this script is meant to run in a privileged workflow
# (pull_request_target) with a token that can push branches to the stub
# fork and open PRs.
# It must never execute anything that comes from the parent PR. The stub
# commit is assembled with git plumbing (read-tree/update-index/commit-tree);
# file content is only read via `git cat-file` / `git show`. Do not add
# steps that check out or build the parent PR's tree (lake, lean, ...).
#
# Stub generation mirrors scripts/create_deprecated_modules.lean:
#   * a rename becomes a redirect stub (`public import <new module>`);
#   * a deletion copies the deleted file's import block verbatim;
#   * the `since` date is the date of the commit that removed the file.
# The stub PR's own CI (`lake exe mk_all --check`, the header linter and a
# full build) validates the generated files, so any drift between the two
# generators is caught before the stubs can merge.
#
# Usage:
#   auto_deprecate_modules.sh --pr N --repo OWNER/NAME [options]
#
# Options:
#   --pr N              parent PR number (required)
#   --repo OWNER/NAME   GitHub repository of the parent PR (required unless
#                       offline)
#   --remote NAME       git remote to fetch the parent from (default: origin)
#   --push-repo O/N     repository that hosts the stub branches (default:
#                       --repo). Must be in the same fork network. PRs still
#                       open on --repo.
#   --push-remote R     git remote or URL to push the stub branch to
#                       (default: --remote when --push-repo equals --repo,
#                       otherwise https://github.com/<push-repo>.git)
#   --base BRANCH       target branch of the parent PR (default: master)
#   --bors-login NAME   GitHub login of the bors bot (default: mathlib-bors).
#                       Used to tell a bors merge apart from an abandoned
#                       parent: in squash mode bors closes pull requests
#                       instead of merging them through GitHub, so `.merged`
#                       stays false and only the closing actor differs.
#   --dry-run           log everything, push nothing, call no mutating API
#   --close             close the stub PR (parent was closed without merge)
#   --only-if-exists    exit quietly unless an open stub PR already exists;
#                       used by the repo-wide `synchronize` trigger
#   --run-url URL       workflow-run URL to link in the stub PR body
#   --head-ref REF      TESTING: use a local ref as the parent head; skips
#                       all gh calls and fetches, and requires --dry-run
#   --base-ref REF      TESTING: use a local ref as the target branch
#
# Environment:
#   GH_TOKEN            token for gh (pushes use the remote's configured auth)
#   ADM_GIT_NAME/EMAIL  git identity for the stub commit
#                       (default: mathlib-nolints[bot])

set -euo pipefail
export LC_ALL=C

PR=""
REPO=""
REMOTE="origin"
PUSH_REPO=""
PUSH_REMOTE=""
BASE="master"
BORS_LOGIN="mathlib-bors"
DRY_RUN=""
CLOSE=""
ONLY_IF_EXISTS=""
RUN_URL=""
HEAD_REF_OVERRIDE=""
BASE_REF_OVERRIDE=""

while [ $# -gt 0 ]; do
  case "$1" in
    --pr) PR="$2"; shift 2 ;;
    --repo) REPO="$2"; shift 2 ;;
    --remote) REMOTE="$2"; shift 2 ;;
    --push-repo) PUSH_REPO="$2"; shift 2 ;;
    --push-remote) PUSH_REMOTE="$2"; shift 2 ;;
    --base) BASE="$2"; shift 2 ;;
    --bors-login) BORS_LOGIN="$2"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    --close) CLOSE=1; shift ;;
    --only-if-exists) ONLY_IF_EXISTS=1; shift ;;
    --run-url) RUN_URL="$2"; shift 2 ;;
    --head-ref) HEAD_REF_OVERRIDE="$2"; shift 2 ;;
    --base-ref) BASE_REF_OVERRIDE="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

[ -n "$PR" ] || { echo "--pr is required" >&2; exit 2; }
case "$PR" in *[!0-9]*|'') echo "--pr must be a number" >&2; exit 2 ;; esac

OFFLINE=""
if [ -n "$HEAD_REF_OVERRIDE" ]; then
  OFFLINE=1
  [ -n "$DRY_RUN" ] || { echo "--head-ref requires --dry-run" >&2; exit 2; }
else
  [ -n "$REPO" ] || { echo "--repo is required" >&2; exit 2; }
fi

PUSH_REPO="${PUSH_REPO:-$REPO}"
PUSH_OWNER="${PUSH_REPO%%/*}"
PUSH_REPO_NAME="${PUSH_REPO##*/}"
if [ -z "$PUSH_REMOTE" ]; then
  if [ "$PUSH_REPO" = "$REPO" ]; then
    PUSH_REMOTE="$REMOTE"
  else
    PUSH_REMOTE="https://github.com/${PUSH_REPO}.git"
  fi
fi

STUB_BRANCH="deprecation-stubs/pr-${PR}"
GIT_NAME="${ADM_GIT_NAME:-mathlib-nolints[bot]}"
GIT_EMAIL="${ADM_GIT_EMAIL:-258989889+mathlib-nolints[bot]@users.noreply.github.com}"

cd "$(git rev-parse --show-toplevel)"

TMP="$(mktemp -d)"
cleanup() {
  rm -rf "$TMP"
  git update-ref -d "refs/auto-deprecate/head-${PR}" 2>/dev/null || true
  git update-ref -d "refs/auto-deprecate/base-${PR}" 2>/dev/null || true
  git update-ref -d "refs/auto-deprecate/existing-${PR}" 2>/dev/null || true
}
trap cleanup EXIT

log() { printf '%s\n' "$*" >&2; }

# find_stub_pr: print the number of the open stub PR, if any. The head
# filter takes the branch label (`owner:branch`); for a same-org fork the
# label matches either hosting repository, which is fine because only the
# automation creates this branch name.
find_stub_pr() {
  gh api "repos/${REPO}/pulls?state=open&head=${PUSH_OWNER}:${STUB_BRANCH}" \
    --jq '.[0].number // empty'
}

close_stub_pr() {
  local reason="$1" num
  num="$(find_stub_pr)"
  if [ -z "$num" ]; then
    log "no open stub PR for ${STUB_BRANCH}; nothing to close"
    return 0
  fi
  if [ -n "$DRY_RUN" ]; then
    log "dry-run: would close stub PR #${num} (${reason}) and delete ${PUSH_REPO}:${STUB_BRANCH}"
    return 0
  fi
  gh pr close "$num" --repo "$REPO" --comment "$reason"
  gh api -X DELETE "repos/${PUSH_REPO}/git/refs/heads/${STUB_BRANCH}" 2>/dev/null ||
    log "note: branch ${STUB_BRANCH} was already gone from ${PUSH_REPO}"
  log "closed stub PR #${num} and deleted ${PUSH_REPO}:${STUB_BRANCH}"
}

# gc_stub_branch: delete the stub branch once its PR is no longer open.
# Needed because bors's delete_merged_branches cannot delete a branch that
# lives in the stub fork.
gc_stub_branch() {
  if [ -n "$(find_stub_pr)" ]; then
    log "parent #${PR} was merged but the stub PR is still open; leaving it untouched"
  elif [ -n "$DRY_RUN" ]; then
    log "dry-run: would delete ${PUSH_REPO}:${STUB_BRANCH} if it still exists"
  elif gh api -X DELETE "repos/${PUSH_REPO}/git/refs/heads/${STUB_BRANCH}" 2>/dev/null; then
    log "deleted merged stub branch ${PUSH_REPO}:${STUB_BRANCH}"
  else
    log "no stub branch to clean up"
  fi
}

# --close: the parent PR was closed.
# Merged by bors or through GitHub: never touch an open stub PR; only
# garbage-collect the stub branch once its PR is no longer open. In squash
# mode bors closes pull requests instead of merging them through GitHub, so
# `.merged` stays false there and the closing actor is the signal.
# Closed by a person without a merge: the stubs are no longer needed, so
# close the stub PR.
if [ -n "$CLOSE" ]; then
  merged="$(gh api "repos/${REPO}/pulls/${PR}" --jq .merged)"
  closer="$(gh api "repos/${REPO}/issues/${PR}" --jq '.closed_by.login // empty')"
  # closed_by reports the app-suffixed login (`name[bot]`) while comments
  # use the plain login; compare with the suffix stripped.
  if [ "$merged" = "true" ] || [ "${closer%\[bot\]}" = "${BORS_LOGIN%\[bot\]}" ]; then
    gc_stub_branch
    exit 0
  fi
  close_stub_pr "Parent PR #${PR} was closed without merging, so these stubs are no longer needed."
  exit 0
fi

if [ -n "$ONLY_IF_EXISTS" ] && [ -z "$OFFLINE" ]; then
  if [ -z "$(find_stub_pr)" ]; then
    log "no open stub PR for #${PR}; nothing to refresh"
    exit 0
  fi
fi

# Opt-out: the `no-auto-stub` label on the parent disables this automation.
if [ -z "$OFFLINE" ]; then
  IFS=$'\t' read -r state base_ref has_optout < <(gh api "repos/${REPO}/pulls/${PR}" \
    --jq '[.state, .base.ref, (([.labels[].name] | contains(["no-auto-stub"])) | tostring)] | @tsv')
  if [ "$state" != "open" ]; then
    log "parent #${PR} is ${state}; nothing to do"
    exit 0
  fi
  if [ "$base_ref" != "$BASE" ]; then
    log "parent #${PR} targets '${base_ref}', not '${BASE}'; skipping"
    exit 0
  fi
  if [ "$has_optout" = "true" ]; then
    log "parent #${PR} carries the no-auto-stub label"
    close_stub_pr "Parent PR #${PR} opted out of automatic deprecation stubs (label \`no-auto-stub\`)."
    exit 0
  fi
  git fetch -q --no-tags "$REMOTE" \
    "+refs/heads/${BASE}:refs/auto-deprecate/base-${PR}" \
    "+refs/pull/${PR}/head:refs/auto-deprecate/head-${PR}"
  BASE_SHA="$(git rev-parse "refs/auto-deprecate/base-${PR}")"
  HEAD_SHA="$(git rev-parse "refs/auto-deprecate/head-${PR}")"
else
  BASE_SHA="$(git rev-parse "${BASE_REF_OVERRIDE:-$BASE}")"
  HEAD_SHA="$(git rev-parse "$HEAD_REF_OVERRIDE")"
fi

MB="$(git merge-base "$BASE_SHA" "$HEAD_SHA")"
log "parent #${PR}: head ${HEAD_SHA}, merge base ${MB}"

# mod_name Mathlib/Data/Nat/Basic.lean -> Mathlib.Data.Nat.Basic
mod_name() {
  local p="${1%.lean}"
  printf '%s' "${p//\//.}"
}

# stub_date PATH: date (YYYY-MM-DD) of the commit that removed PATH,
# searched from the parent head. Matches create_deprecated_modules.lean,
# which uses the deletion commit's date for `since :=`.
stub_date() {
  local d
  d="$(git log -1 --format=%cs "$HEAD_SHA" -- "$1" || true)"
  if [ -z "$d" ]; then
    log "warning: no history for $1 (shallow clone?); using today's date"
    d="$(date -u +%Y-%m-%d)"
  fi
  printf '%s' "$d"
}

# Collect deletions and renames of library modules, excluding files that
# were already deprecation stubs (removing an expired stub must not create
# a fresh one; PR_summary flags those separately).
STUBS_FILE="$TMP/stubs.tsv"    # kind<TAB>old<TAB>new
: > "$STUBS_FILE"
mkdir -p "$TMP/stubs"

while IFS=$'\t' read -r status old new; do
  case "$old" in
    Mathlib/*.lean|Archive/*.lean|Counterexamples/*.lean) ;;
    *) continue ;;
  esac
  if git show "${MB}:${old}" 2>/dev/null | grep -q '^deprecated_module'; then
    log "skip ${old}: it is already a deprecation stub"
    continue
  fi
  case "$status" in
    D) printf 'D\t%s\t\n' "$old" >> "$STUBS_FILE" ;;
    R*) printf 'R\t%s\t%s\n' "$old" "$new" >> "$STUBS_FILE" ;;
  esac
done < <(git diff -M --name-status --diff-filter=DR "$MB" "$HEAD_SHA")

if [ ! -s "$STUBS_FILE" ]; then
  log "parent #${PR} deletes or renames no library modules"
  if [ -z "$OFFLINE" ]; then
    close_stub_pr "Parent PR #${PR} no longer deletes or renames modules, so these stubs are no longer needed."
  fi
  exit 0
fi

# Generate one stub file per moved module.
SUMMARY="$TMP/summary.md"
: > "$SUMMARY"

while IFS=$'\t' read -r kind old new; do
  date="$(stub_date "$old")"
  out="$TMP/stubs/${old}"
  mkdir -p "$(dirname "$out")"
  if [ "$kind" = "R" ]; then
    {
      printf 'module -- shake: keep-all\n\n'
      printf 'public import %s\n\n' "$(mod_name "$new")"
      printf 'deprecated_module "`%s` has been renamed to `%s`" (since := "%s")\n' \
        "$(mod_name "$old")" "$(mod_name "$new")" "$date"
    } > "$out"
    printf -- '- `%s` → `%s` (renamed)\n' "$old" "$new" >> "$SUMMARY"
  else
    old_src="$(git show "${MB}:${old}")"
    imports="$(grep -E '^((public|meta)[[:space:]]+)*import[[:space:]]' <<<"$old_src" || true)"
    {
      if grep -qE '^module([[:space:]]|$)' <<<"$old_src"; then
        printf 'module -- shake: keep-all\n\n'
      fi
      if [ -n "$imports" ]; then
        printf '%s\n\n' "$imports"
      fi
      printf 'deprecated_module (since := "%s")\n' "$date"
    } > "$out"
    printf -- '- `%s` (deleted)\n' "$old" >> "$SUMMARY"
  fi
  log "generated stub for ${old} (${kind}, since ${date})"
done < "$STUBS_FILE"

# roots_for PATH: the root import files that must list PATH's module.
# Modules under Mathlib/Tactic/ are listed both in Mathlib.lean and in
# Mathlib/Tactic.lean (mirroring `lake exe mk_all`).
roots_for() {
  case "$1" in
    Mathlib/Tactic/*) printf 'Mathlib.lean\nMathlib/Tactic.lean\n' ;;
    Mathlib/*)        printf 'Mathlib.lean\n' ;;
    Archive/*)        printf 'Archive.lean\n' ;;
    Counterexamples/*) printf 'Counterexamples.lean\n' ;;
  esac
}

# prefix_for ROOT: the module-name prefix of the sorted import region that
# ROOT owns. Insertion sorts only against lines with this prefix, because
# root files also carry unrelated entries (e.g. `public import Std`).
prefix_for() {
  case "$1" in
    Mathlib.lean)          printf 'Mathlib.' ;;
    Mathlib/Tactic.lean)   printf 'Mathlib.Tactic.' ;;
    Archive.lean)          printf 'Archive.' ;;
    Counterexamples.lean)  printf 'Counterexamples.' ;;
  esac
}

# insert_import FILE MOD PREFIX: insert `public import MOD` into FILE at
# its sorted position among the `public import PREFIX*` lines. No-op when
# the line is already present.
insert_import() {
  local file="$1" mod="$2" prefix="$3"
  awk -v mod="$mod" -v prefix="$prefix" '
    BEGIN { newline = "public import " mod; done = 0; inregion = 0 }
    {
      matches = (index($0, "public import " prefix) == 1)
      if (!done && $0 == newline) { done = 1 }
      else if (!done && matches) {
        inregion = 1
        cur = substr($0, 15)
        if (cur > mod) { print newline; done = 1 }
      }
      else if (!done && inregion && !matches) { print newline; done = 1 }
      print
    }
    END { if (!done) print newline }
  ' "$file" > "${file}.new"
  mv "${file}.new" "$file"
}

# Prepare updated root import files.
mkdir -p "$TMP/roots"
ROOTS_TOUCHED="$TMP/roots_touched"
: > "$ROOTS_TOUCHED"

while IFS=$'\t' read -r kind old new; do
  while IFS= read -r root; do
    [ -n "$root" ] || continue
    if ! git cat-file -e "${HEAD_SHA}:${root}" 2>/dev/null; then
      log "warning: ${root} does not exist at the parent head; skipping"
      continue
    fi
    rootcopy="$TMP/roots/${root//\//__}"
    if [ ! -f "$rootcopy" ]; then
      git cat-file blob "${HEAD_SHA}:${root}" > "$rootcopy"
      printf '%s\n' "$root" >> "$ROOTS_TOUCHED"
    fi
    insert_import "$rootcopy" "$(mod_name "$old")" "$(prefix_for "$root")"
  done < <(roots_for "$old")
done < "$STUBS_FILE"

# Assemble the stub commit with git plumbing; the parent PR's tree is never
# checked out.
export GIT_INDEX_FILE="$TMP/index"
git read-tree "$HEAD_SHA"
while IFS=$'\t' read -r kind old new; do
  blob="$(git hash-object -w -- "$TMP/stubs/${old}")"
  git update-index --add --cacheinfo "100644,${blob},${old}"
done < "$STUBS_FILE"
sort -u "$ROOTS_TOUCHED" | while IFS= read -r root; do
  blob="$(git hash-object -w -- "$TMP/roots/${root//\//__}")"
  git update-index --add --cacheinfo "100644,${blob},${root}"
done
TREE="$(git write-tree)"
unset GIT_INDEX_FILE

COMMIT_MSG="chore: module deprecation stubs for #${PR}"
COMMIT="$(GIT_AUTHOR_NAME="$GIT_NAME" GIT_AUTHOR_EMAIL="$GIT_EMAIL" \
  GIT_COMMITTER_NAME="$GIT_NAME" GIT_COMMITTER_EMAIL="$GIT_EMAIL" \
  git commit-tree "$TREE" -p "$HEAD_SHA" -m "$COMMIT_MSG")"

log "built stub commit ${COMMIT}"
git --no-pager show --stat --format='%h %s' "$COMMIT" >&2

if [ -n "$DRY_RUN" ]; then
  log ""
  log "dry-run: generated stubs:"
  while IFS=$'\t' read -r kind old new; do
    log ""
    log "----- ${old} -----"
    cat "$TMP/stubs/${old}" >&2
  done < "$STUBS_FILE"
  log ""
  log "dry-run: would push ${COMMIT} to ${PUSH_REPO}:${STUB_BRANCH}"
  log "dry-run: would open or refresh the stub PR and comment 'bors stack #${PR}'"
  exit 0
fi

# Idempotency: skip the push when the branch already holds this exact tree
# on this exact parent.
NEED_PUSH=1
if git fetch -q --no-tags "$PUSH_REMOTE" "+refs/heads/${STUB_BRANCH}:refs/auto-deprecate/existing-${PR}" 2>/dev/null; then
  existing="$(git rev-parse "refs/auto-deprecate/existing-${PR}")"
  if [ "$(git rev-parse "${existing}^{tree}")" = "$TREE" ] &&
     [ "$(git rev-parse "${existing}^1" 2>/dev/null)" = "$HEAD_SHA" ]; then
    log "branch ${STUB_BRANCH} is already up to date"
    NEED_PUSH=""
  fi
  git update-ref -d "refs/auto-deprecate/existing-${PR}" || true
fi
if [ -n "$NEED_PUSH" ]; then
  git push -q --force "$PUSH_REMOTE" "${COMMIT}:refs/heads/${STUB_BRANCH}"
  log "pushed ${PUSH_REPO}:${STUB_BRANCH}"
fi

COMPARE_URL="https://github.com/${REPO}/compare/${HEAD_SHA}...${COMMIT}"
BODY="$TMP/body.md"
cat > "$BODY" <<EOF
This PR adds \`deprecated_module\` stubs for the modules that #${PR} deletes or renames:

$(cat "$SUMMARY")

It is stacked on #${PR} with \`bors stack\`. Bors merges the two PRs in one batch, parent first. The old module names keep working on \`${BASE}\` at all times.

Notes for the reviewer:

- The diff on this page includes the changes of #${PR}, because this branch starts from its head commit. See the stubs alone here: ${COMPARE_URL}
- Give each of the two PRs its own \`bors r+\`. Bors holds the first approval until the other PR is also approved.
- Automation refreshes this branch each time #${PR} changes. Do not push commits to it.
- If a stub needs a custom deprecation message, edit it after the merge, or replace this PR with a manual one and add the \`no-auto-stub\` label to #${PR}.

---
Auto-generated by \`scripts/auto_deprecate_modules.sh\`${RUN_URL:+ ([workflow run](${RUN_URL}))}
EOF

EXISTING_PR="$(find_stub_pr)"
if [ -z "$EXISTING_PR" ]; then
  if [ "$PUSH_REPO" = "$REPO" ]; then
    url="$(gh pr create --repo "$REPO" --base "$BASE" --head "$STUB_BRANCH" \
      --title "chore: module deprecation stubs for #${PR}" \
      --body-file "$BODY")"
    EXISTING_PR="${url##*/}"
  else
    # Cross-repo head. `head_repo` disambiguates when the fork and the main
    # repository share an owner (`owner:branch` alone is ambiguous then).
    EXISTING_PR="$(gh api "repos/${REPO}/pulls" \
      -f title="chore: module deprecation stubs for #${PR}" \
      -f head="${PUSH_OWNER}:${STUB_BRANCH}" \
      -f head_repo="${PUSH_REPO_NAME}" \
      -f base="$BASE" \
      -F body=@"$BODY" \
      --jq '.number')"
  fi
  log "opened stub PR #${EXISTING_PR}"
  gh pr comment "$EXISTING_PR" --repo "$REPO" --body "bors stack #${PR}"
  log "posted 'bors stack #${PR}' on #${EXISTING_PR}"
else
  gh pr edit "$EXISTING_PR" --repo "$REPO" --body-file "$BODY"
  log "refreshed stub PR #${EXISTING_PR}"
fi
