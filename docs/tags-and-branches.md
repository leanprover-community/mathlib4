# The Lean Github ecosystem

Documentation of the branches, tags, and CI workflows relevant for making PRs to Lean, Std, and
Mathlib.

* [Things you need to know](#things-you-need-to-know) is relevant for everyone
* [Tags and branches](#tags-and-branches) is for "experts only" who are making or fixing
  breaking changes in Lean, or who want to understand the inner workings of Mathlib CI.

## Things you need to know

* If you are making a PR to `leanprover/lean4` which may involve breaking changes,
  please rebase your PR onto the `nightly` branch. This will enable combined CI with Mathlib.

* If you are making a PR to `leanprover-community/mathlib4`,
  please ask for "write" access to the repository via the [zulip chat](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/github.20permission), and push your branch to that repo.
  This will enable Mathlib's `.olean` cache to include your PR.

## Tags and branches

### `leanprover/lean4`

* Development occurs on the `master` branch.
* Stable releases and release candidates have tags, e.g. `v4.2.0` or `v4.3.0-rc1`.
  * To use these, your `lean-toolchain` should contain e.g. `leanprover/lean4:v4.2.0`.
* Stable releases arrive at the end of each month, and are identical to the last release candidate.
* The first release candidate of the next version is released immediately after the stable release.
* Each version has a `releases/v4.X.0` feature branch, which may contain
  * additional commits for release notes
  * cherry picked commits from `master` for critical fixes released via release candidates.
* We make a regular nightly release from `master`, which has a tag e.g. `nightly-2023-11-01` on the
  `leanprover/lean4-nightly` repository.
  * To use these, your `lean-toolchain` should contain e.g. `leanprover/lean4:nightly-2023-11-01`.
* There is a `nightly` branch on `leanprover/lean4` which follows the most recent commit which was
  used to construct a nightly release.
* Every PR automatically receives a toolchain. For PR #NNNN, your `lean-toolchain` should contain
  `leanprover/lean4-pr-releases:pr-release-NNNN`.

### `leanprover/std4` (aka 'Std')

* Development occurs on `main`.
* Std uses the latest stable release or release candidate in its `lean-toolchain`.
  * Because we release `v4.3.0-rc1` immediately after releasing `v4.2.0`, Std is only very briefly
    on stable releases.
* The first commit on `main` which uses a new toolchain is tagged with the version number of that
  toolchain (e.g. `v4.2.0`).
* There is a branch `stable` which follows the `v4.X.0` tags.
* Std has a branch `bump/v4.X.0` for the upcoming stable version,
  * which contains adaptations for breaking changes that have been approved by the maintainers
  * and which will be using a `leanprover-lean4:nightly-YYYY-MM-DD` toolchain.
* Std has a branch `nightly-testing` which
  * uses a recently nightly release (this is updated automatically)
  * has all commits from `main` merged into it automatically
  * may have any changes from `bump/v4.X.0` merged into it manually
  * may have any other commits, including unreviewed ones, required to keep the `nightly-testing`
    branch working again recent nightly releases.
* When changes are required to Std to adapt to a breaking change in Lean,
  please open a PR.
  * Typically, if the change was made in `leanprover/lean4#NNNN`,
    this PR should be from a branch named `lean-pr-testing-NNNN`,
    and `lean-toolchain` will contain `leanprover/lean4-pr-releases:pr-release-NNNN`.
  * This PR should be made against the `bump/v4.X.0` branch, not against `main`.
  * This PR should be labelled `v4.X.0`, where `v4.X.0` is the upcoming stable version,
    and also labelled 'depends on core changes'.
  * Once the Lean PR has been merged and published in a nightly release, the Std adaptation PR
    * should have its `lean-toolchain` updated to `leanprover/lean4:nightly-YYYY-MM-DD`
    * may be merged into `nightly-testing` as needed.
  * Once the Std adaptation PR has been approved, it can be merged to `bump/v4.X.0`.
* It is always allowed to merged `bump/v4.X.0` into `nightly-testing`, but not conversely.
  (Changes to `bump/v4.X.0` have been reviewed, but changes to `nightly-testing` may not be.)
* When it is time to update Std to a new Lean release,
  *hopefully* all that is required is to make a new PR
  consisting of squash merging `bump/v4.X.0` to `main`.

### `leanprover-community/mathilb4` (aka 'Mathlib')

* Everything said above about Std applies to Mathlib, except:
  * Development occurs on `master`.
  * PRs to Mathlib should be made from branches of the Mathlib repository itself.
    * This is required for Mathlib's `.olean` caching mechanism.
    * Please ask on the [zulip chat](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/github.20permission) for "write" permission to Mathlib.
      Please write a sentence about your background and plans.
* Note that the `nightly-testing` branch of Mathlib may use the `nightly-testing` branch of Std.
* Mathlib adaptation PRs on `lean-pr-testing-NNNN` branches may need to change the Std dependency
  to use a `lean-pr-testing-NNNN` branch of Std, if Std also experiences breakages.
* Failures in CI on the `nightly-testing` are reported by a bot to zulip in the private
  "Mathlib reviewers" stream.
* Success in CI on the `nightly-testing` branch results in the creation or updating of a branch
  `nightly-testing-YYYY-MM-DD` to match that commit.
  * Thus if `nightly-testing-YYYY-MM-DD` exists, we know that:
    * the `lean-toolchain` is `leanprover/lean4:nightly-YYYY-MM-DD`, and
    * CI succeeds.

### Combined CI between Lean and Mathlib

* For every PR to Lean, we attempt to run Mathlib CI against the resulting toolchain.
* For this to work, you will need to rebase your PR onto the `nightly` branch.
  * If you have not done this, a bot will comment saying that it can not run Mathlib CI,
    and advising that if you need this you will need to rebase your PR onto `nightly`.
* Further, the latest nightly release may or may not have a corresponding
  `nightly-testing-YYYY-MM-DD` branch on Mathlib (see above).
  * If this branch does not yet exist, a bot will comment on your PR notifying you
    that it can not run Mathlib CI, and advising that it will try again when you either
    * push more commits, or
    * rebase your PR onto a future update of the `nightly` branch
      (note that this may be necessary if Mathlib is having persistent problems adapting
      to the most recent nightly release).
  * If this branch does exist, then the bot will automatically create a
    `lean-pr-testing-NNNN` branch at Mathlib from the `nightly-testing-YYYY-MM-DD` branch,
    and set the toolchain to `leanprover/lean4-pr-releases:pr-release-NNNN`.
    * Subsequent CI results from that Mathlib branch will be reported back to the Lean PR
      in the form of comments.
