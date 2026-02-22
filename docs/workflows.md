# GitHub Workflows Summary

### Note

- The grouping below is done mainly by primary trigger (the main event that causes runs).
- _Importance_ is a rough evaluation of the importance of the workflow in our operations:
  - High: core CI logic, merge-flow, branch-health, or high-impact automation.
  - Medium: quality checks, reports, notifications, and operational helpers.
  - Low: cosmetic/status/bookkeeping helpers with limited blast radius.

### Trigger type glossary

This is an overview of the most important triggers used by Mathlib CI. For a complete listing, please [see the GitHub actions documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows).

- `pull_request`: runs on PR activity using the PR branch workflow file.
- `pull_request_target`: runs on PR activity using the base branch workflow file (safer access to repository secrets/write operations when guarded correctly).
- `issue_comment`: runs when issue or PR comments are created/edited.
- `pull_request_review`: runs on PR review submissions.
- `pull_request_review_comment`: runs on inline PR review comments.
- `push`: runs when commits are pushed to matching branches/tags.
- `schedule`: runs at a regular scheduled time.
- `workflow_dispatch`: manual run from the Actions UI or API.
- `workflow_run`: runs after another workflow run is requested, is in progress, or is completed.
- `issues`: runs on issue lifecycle events (for example `closed`, `reopened`).
- `workflow_call`: reusable workflow entrypoint, triggered only when called by another workflow.

# Summary
## Main CI

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`build_fork.yml`](../.github/workflows/build_fork.yml) | continuous integration (mathlib forks)<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/build_fork.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/build_fork.yml) | High | `pull_request_target` | On PRs from forks, this workflow builds, lints and tests Mathlib using the reusable build template (`build_template.yml`). |
| [`bors.yml`](../.github/workflows/bors.yml) | continuous integration (staging)<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/bors.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/bors.yml) | High | `push` | On the `staging` and `trying` branches used by Bors, this workflow builds, lints and tests Mathlib using the reusable build template (`build_template.yml`). |
| [`build.yml`](../.github/workflows/build.yml) | continuous integration<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/build.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/build.yml) | High | `push` | On non-fork PRs, this workflow builds, lints and tests Mathlib using the reusable build template (`build_template.yml`). |

### The main CI pipelines above all use this reusable workflow for the base logic:
| File  | Description |
|---|---|
| [`build_template.yml`](../.github/workflows/build_template.yml) | Reusable CI workflow (`workflow_call`) that performs Lean setup, build/test/lint steps, cache/artifact handling, and reporting. |

## Pull requests

Primary trigger for this section: PR/merge-queue events (`pull_request`, `pull_request_target`).

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`actionlint.yml`](../.github/workflows/actionlint.yml) | Check workflows<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/actionlint.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/actionlint.yml) | Medium | `pull_request` | Runs `actionlint` for workflow changes on PRs and merge queues and posts suggestions using `reviewdog`. |
| [`commit_verification.yml`](../.github/workflows/commit_verification.yml) | Commit Verification<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/commit_verification.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/commit_verification.yml) | Medium | `pull_request` | Verifies `transient:` and `x:` commits in PRs and posts a verification summary comment. |
| [`pre-commit.yml`](../.github/workflows/pre-commit.yml) | Run pre-commit and in-place update PR on push<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/pre-commit.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/pre-commit.yml) | Medium | `pull_request, push` | Runs pre-commit hooks on pushes/PRs and uses pre-commit-ci lite for automatic fixes. |
| [`check_pr_titles.yaml`](../.github/workflows/check_pr_titles.yaml) | Check PR titles<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/check_pr_titles.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/check_pr_titles.yaml) | Low | `pull_request_target` | Validates PR titles against project conventions and maintains a sticky guidance comment. |
| [`lint_and_suggest_pr.yml`](../.github/workflows/lint_and_suggest_pr.yml) | lint and suggest<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/lint_and_suggest_pr.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/lint_and_suggest_pr.yml) | Low | `pull_request` | Runs style linting and suggests changes on pull requests. The suggested changes can be applied by calling `bot_fix_style.yaml`. |
| [`PR_summary.yml`](../.github/workflows/PR_summary.yml) | Post PR summary comment<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/PR_summary.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/PR_summary.yml) | Low | `pull_request_target` | On `pull_request_target`, computes PR summary data (imports/declarations/tech debt), manages related labels, and updates PR comments. |
| [`add_label_from_diff.yaml`](../.github/workflows/add_label_from_diff.yaml) | Autolabel PRs<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/add_label_from_diff.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/add_label_from_diff.yaml) | Low | `pull_request_target, push` | Applies an inferred topic label to newly opened PRs using `lake exe autolabel`. |
| [`label_new_contributor.yml`](../.github/workflows/label_new_contributor.yml) | Label New Contributors<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/label_new_contributor.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/label_new_contributor.yml) | Low | `pull_request_target` | Labels PRs from new contributors (based on the number of their PRs merged). |
| [`zulip_emoji_closed_pr.yaml`](../.github/workflows/zulip_emoji_closed_pr.yaml) | Add "closed-pr" emoji in Zulip<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/zulip_emoji_closed_pr.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/zulip_emoji_closed_pr.yaml) | Low | `pull_request_target` | Updates Zulip emoji reactions for PR close/reopen events. |
| [`zulip_emoji_labelling.yaml`](../.github/workflows/zulip_emoji_labelling.yaml) | zulip_emoji_labelling.yaml<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/zulip_emoji_labelling.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/zulip_emoji_labelling.yaml) | Low | `pull_request_target` | Updates Zulip emoji reactions in response to PR label changes. |

## Maintainer commands

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`maintainer_bors.yml`](../.github/workflows/maintainer_bors.yml) | Add "ready-to-merge" and "delegated" label<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/maintainer_bors.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/maintainer_bors.yml) | High | `issue_comment, pull_request_review, pull_request_review_comment` | Processes bors merge/delegate commands, updates labels, and emits artifact/context for follow-up workflows. |
| [`maintainer_merge.yml`](../.github/workflows/maintainer_merge.yml) | Maintainer merge<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/maintainer_merge.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/maintainer_merge.yml) | High | `issue_comment, pull_request_review, pull_request_review_comment` | Handles maintainer merge/delegate commands, performs permission checks, and posts Zulip/PR notifications. |
| [`labels_from_comment.yml`](../.github/workflows/labels_from_comment.yml) | Label PR based on Comment<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/labels_from_comment.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/labels_from_comment.yml) | Medium | `issue_comment, pull_request_review, pull_request_review_comment` | Adds/removes an allowlisted set of labels based on comment/review text commands. |
| [`bot_fix_style.yaml`](../.github/workflows/bot_fix_style.yaml) | bot fix style<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/bot_fix_style.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/bot_fix_style.yaml) | Low | `issue_comment, pull_request_review, pull_request_review_comment` | Responds to review/comment events and runs `lint-style-action` in `fix` mode. |
| [`zulip_emoji_merge_delegate.yaml`](../.github/workflows/zulip_emoji_merge_delegate.yaml) | Zulip emoji merge update<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/zulip_emoji_merge_delegate.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/zulip_emoji_merge_delegate.yaml) | Low | `push` | On push to `master`, detects merged PR context and updates Zulip emoji state. |
| [`sync_closed_tasks.yaml`](../.github/workflows/sync_closed_tasks.yaml) | Cross off linked issues<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/sync_closed_tasks.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/sync_closed_tasks.yaml) | Low | `issues, pull_request` | Updates the dependent PR checkboxes when issues/PRs are closed or reopened. |

## Scheduled CI maintenance

Primary trigger for this section: scheduled automation (`schedule`, often with `workflow_dispatch`).

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`daily.yml`](../.github/workflows/daily.yml) | Daily CI Workflow<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/daily.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/daily.yml) | High | `schedule (daily at 00:00 UTC)` | Runs scheduled expensive checks (master + nightly variants) and posts status updates to Zulip. |
| [`nightly_bump_and_merge.yml`](../.github/workflows/nightly_bump_and_merge.yml) | Bump toolchain and merge pr-testing branches<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nightly_bump_and_merge.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nightly_bump_and_merge.yml) | High | `schedule (daily at 10:00, 13:00, 16:00, 19:00, 22:00 UTC)` | Automates nightly-testing toolchain bump and merges `lean-pr-testing-*` branches with status messaging. |
| [`nightly_merge_master.yml`](../.github/workflows/nightly_merge_master.yml) | Merge master to nightly<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nightly_merge_master.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nightly_merge_master.yml) | High | `schedule (daily at 00:30 UTC)` | Daily automation that merges `mathlib4/master` into `mathlib4-nightly-testing` and pushes updates. |
| [`update_dependencies.yml`](../.github/workflows/update_dependencies.yml) | Update Mathlib Dependencies<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/update_dependencies.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/update_dependencies.yml) | High | `schedule (hourly at minute 00 UTC)` | Hourly dependency update workflow that runs `lake update`, manages a bot PR, and alerts on failures. |
| [`docker_build.yml`](../.github/workflows/docker_build.yml) | docker<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/docker_build.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/docker_build.yml) | Medium | `schedule (daily at 00:00 UTC)` | Scheduled build-and-push of Docker images to GHCR with metadata and provenance attestations. |
| [`merge_conflicts.yml`](../.github/workflows/merge_conflicts.yml) | Merge conflicts<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/merge_conflicts.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/merge_conflicts.yml) | Medium | `schedule (every 15 minutes)` | Periodically detects conflicted PRs and labels/comments on them. |
| [`nightly-docgen.yml`](../.github/workflows/nightly-docgen.yml) | Docgen test on nightly-testing<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nightly-docgen.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nightly-docgen.yml) | Medium | `schedule (daily at 01:37 UTC)` | Runs nightly-testing docgen checks and sends Zulip success/failure messages. |
| [`nightly-regression-report.yml`](../.github/workflows/nightly-regression-report.yml) | nightly-testing regression report<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nightly-regression-report.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nightly-regression-report.yml) | Medium | `schedule (daily at 04:37 UTC)` | Produces nightly-testing regression/lint report output and posts summary to Zulip. |
| [`nolints.yml`](../.github/workflows/nolints.yml) | update nolints<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nolints.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nolints.yml) | Medium | `schedule (weekly on Sunday at 00:00 UTC)` | Regenerates `nolints.json` on a schedule and opens/updates a PR with the result. |
| [`remove_deprecated_decls.yml`](../.github/workflows/remove_deprecated_decls.yml) | Remove outdated deprecated declarations<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/remove_deprecated_decls.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/remove_deprecated_decls.yml) | Medium | `schedule (monthly on day 15 at 04:05 UTC)` | Monthly/manual cleanup of old deprecations with optional PR creation and Zulip notifications. |
| [`dependent-issues.yml`](../.github/workflows/dependent-issues.yml) | Dependent Issues<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/dependent-issues.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/dependent-issues.yml) | Low | `schedule (every 15 minutes)` | Periodically updates dependency-tracking labels from issue/PR dependency checkboxes. |
| [`latest_import.yml`](../.github/workflows/latest_import.yml) | Late importers report<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/latest_import.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/latest_import.yml) | Low | `schedule (weekly on Monday at 04:00 UTC)` | Runs weekly min-imports analysis/build and posts a late-importers report to Zulip. |
| [`long_file_report.yml`](../.github/workflows/long_file_report.yml) | Weekly Long File Report<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/long_file_report.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/long_file_report.yml) | Low | `schedule (weekly on Monday at 04:00 UTC)` | Runs a weekly long-file report script and posts the result to Zulip. |
| [`technical_debt_metrics.yml`](../.github/workflows/technical_debt_metrics.yml) | Weekly Technical Debt Counters<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/technical_debt_metrics.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/technical_debt_metrics.yml) | Low | `schedule (weekly on Monday at 04:00 UTC)` | Runs weekly technical-debt counter script and posts results to Zulip. |
| [`weekly-lints.yml`](../.github/workflows/weekly-lints.yml) | Weekly linting report<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/weekly-lints.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/weekly-lints.yml) | Low | `schedule (weekly on Monday at 05:00 UTC)` | Runs a set of low-priority lints and posts the results to Zulip |

## Workflow chaining (`workflow_run`)

Primary trigger for this section: completion of other workflows (`workflow_run`).

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`nightly_detect_failure.yml`](../.github/workflows/nightly_detect_failure.yml) | Post to zulip if the nightly-testing branch is failing.<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/nightly_detect_failure.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/nightly_detect_failure.yml) | High | `workflow_run` | Reacts to nightly-testing CI outcomes; posts status updates and performs branch/tag maintenance on success. |
| [`update_dependencies_zulip.yml`](../.github/workflows/update_dependencies_zulip.yml) | Monitor Dependency Update Failures<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/update_dependencies_zulip.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/update_dependencies_zulip.yml) | High | `workflow_run` | Watches dependency-update CI runs and sends Zulip success/failure messages with PR/label handling. |
| [`maintainer_bors_wf_run.yml`](../.github/workflows/maintainer_bors_wf_run.yml) | Add "ready-to-merge" and "delegated" label (workflow_run)<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/maintainer_bors_wf_run.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/maintainer_bors_wf_run.yml) | Medium | `workflow_run` | Manages labels plus Zulip emoji updates for Bors commands. |
| [`maintainer_merge_wf_run.yml`](../.github/workflows/maintainer_merge_wf_run.yml) | Maintainer merge (workflow_run)<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/maintainer_merge_wf_run.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/maintainer_merge_wf_run.yml) | Medium | `workflow_run` | Manages labels and posts on Zulip for maintainer merge/delegate commands. |
| [`export_telemetry.yaml`](../.github/workflows/export_telemetry.yaml) | Export workflow telemetry<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/export_telemetry.yaml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/export_telemetry.yaml) | Low | `workflow_run` | Exports CI run telemetry to OTLP when selected CI workflows complete. |

## Manual-only workflows

Primary trigger for this section: explicit manual invocation (`workflow_dispatch`).

| File | Name | Importance | Triggers | Description |
|---|---|---|---|---|
| [`stale.yml`](../.github/workflows/stale.yml) | Close stale issues and PRs<br>[![passed/failed](https://img.shields.io/github/actions/workflow/status/leanprover-community/mathlib4/stale.yml?label=status)](https://github.com/leanprover-community/mathlib4/actions/workflows/stale.yml) | Low | `workflow_dispatch` | Manual stale-bot workflow for inactive PRs/issues (currently configured in debug-only mode). |
