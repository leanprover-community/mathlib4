# `awaiting-zulip` discussion check

This action keeps an open mathlib PR from being hidden from the review queue by
`awaiting-zulip` without a linked discussion that references that PR.

It scans the PR description, issue comments, review bodies, and inline review
comments (including pagination). Generic Zulip homepage/channel links do not
qualify. Message links using either `/near/` or `/with/` resolve the message's
current channel/topic, so renamed topics and old `/stream/` links work. Topic-only
links are also supported. The entire linked topic is checked, not just messages
near the anchor.

Both full GitHub URLs and Zulip linkifiers (`#12345`, `mathlib4#12345`, etc.)
qualify: the validator reads rendered link destinations and `topic_links` (or
legacy `subject_links`), rather than matching bare numbers. Destinations must
identify the same PR in `leanprover-community/mathlib4`; `/pull/N` and `/issues/N`
URLs, including comment fragments, are accepted. References to Lean's repository,
a different PR, and unlinked numbers/code examples do not qualify.

The comment-labeling workflow runs `mode: directive` to validate before applying
the label. The separate workflow runs `mode: enforce` after manual labeling and
PR/comment changes. A daily sweep retries missed events and outages and checks
existing labels, including changes made on Zulip itself. These two workflows
serialize PR events with the same concurrency group. A sweep also checks the
label event again before removing it. Removal of the label is always allowed.
Closed PRs and ordinary issues are ignored.

When a discussion is missing, the action removes (or declines to apply) the
label and leaves one updatable bot comment mentioning the labeler. For historical
labels applied by the comment bot, it identifies the human from the preceding
label directive. Read errors and inaccessible discussions leave the label
unchanged and fail the workflow for retry; a second, verifiable qualifying link
is sufficient even if another link cannot be read. The action never posts to or
edits Zulip. It uses the existing `ZULIP_API_KEY` and mathlib bot account; that
account must have access to any linked private reviewers topic.

Privileged jobs check out only the default branch's action, never PR code, and
API clients refuse redirects to avoid forwarding credentials. Unit tests run on
PR code in a separate job with read-only permissions and no Zulip secret.

Use **Check awaiting-zulip discussions → Run workflow** to check one PR or all
open labelled PRs. Manual runs default to dry-run. Event and scheduled runs apply
the policy; the first sweep will also enforce it on existing labels.

Run the dependency-free tests locally:

```sh
python3 -m unittest discover -s .github/actions/awaiting-zulip -v
```
