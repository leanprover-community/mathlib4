# get-mathlib-ci

This action is the source of truth for how workflows in this repository check out
`leanprover-community/mathlib-ci`.

## Policy

Any workflow that needs `mathlib-ci` should use this action instead of writing its
own `actions/checkout` block for `leanprover-community/mathlib-ci`.

The default `ref` in [`action.yml`](./action.yml) is the single canonical pinned
`mathlib-ci` commit for this repository.

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
