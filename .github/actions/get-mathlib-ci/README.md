# get-mathlib-ci

This action is the source of truth for how workflows in this repository check out
`leanprover-community/mathlib-ci`.

## Policy

Any workflow that needs `mathlib-ci` should use this action instead of writing its
own `actions/checkout` block for `leanprover-community/mathlib-ci`.

The default `ref` in [`action.yml`](./action.yml) is the single canonical pinned
`mathlib-ci` commit for this repository. This is auto-updated regularly by the
[`update_dependencies.yml` workflow](../../workflows/update_dependencies.yml).

## Why

- Keep the pinned `mathlib-ci` ref in one place.
- Avoid drift and copy/paste mistakes across many workflows.
- Make ref bumps a one-file update.

## Usage

In workflows, check out this repository's actions from the running workflow commit,
then use the local action:

```yaml
- name: Checkout local actions
  uses: actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd # v6.0.2
  with:
    ref: ${{ github.workflow_sha }}
    fetch-depth: 1
    sparse-checkout: .github/actions
    path: workflow-actions

- name: Get mathlib-ci
  uses: ./workflow-actions/.github/actions/get-mathlib-ci
```

Override the ref only when needed:

```yaml
- name: Get mathlib-ci
  uses: ./workflow-actions/.github/actions/get-mathlib-ci
  with:
    ref: master
```

## Outputs

This action also exposes values that later workflow steps can reuse:

- `ref`: the effective `mathlib-ci` ref that was checked out. If the workflow did
  not pass `with.ref`, this is the action's default pinned commit.
- `path`: the checkout path used for `mathlib-ci`.
- `scripts_dir`: the absolute path to the checked out `scripts` directory.

The action also exports these environment variables for subsequent steps:

- `CI_CHECKOUT_PATH`: the absolute path to the checked out `mathlib-ci` repository.
- `CI_SCRIPTS_DIR`: the absolute path to the checked out `mathlib-ci/scripts` directory.

If a workflow needs to refer to the exact resolved `mathlib-ci` ref later, use the
action output instead of duplicating the pinned SHA in the workflow:

```yaml
- name: Get mathlib-ci
  id: get_mathlib_ci
  uses: ./workflow-actions/.github/actions/get-mathlib-ci

- name: Use resolved ref
  run: |
    echo "Resolved ref: ${{ steps.get_mathlib_ci.outputs.ref }}"
    echo "Scripts dir: ${{ steps.get_mathlib_ci.outputs.scripts_dir }}"
    echo "Raw URL: https://raw.githubusercontent.com/leanprover-community/mathlib-ci/${{ steps.get_mathlib_ci.outputs.ref }}/scripts/nightly/create-adaptation-pr.sh"
```
