# IMO problems

We have a collection of solutions to IMO problems in mathlib, stored under `/archive/imo/`.

These are part of mathlib for three purposes:
* The [IMO Grand Challenge](https://imo-grand-challenge.github.io/) will need training data, and exemplars,
  and this is a reasonable place to collect Lean samples of IMO problems.
* As with the rest of `/archive/`, we want to have high quality examples
  covering elementary mathematics, available as learning materials.
* They are popular as a first contribution to mathlib,
  and an opportunity to teach new contributors how to write Lean code.

That said, IMO problems also come at a cost:
* reviewing pull requests by first time contributors can be very time-consuming
* less significantly, there is a certain amount of maintenance work
  ensuring they keep up with mathlib.

Thus we'd like authors of IMO pull requests to keep in mind the following points.
* Reviewing may take some time
  (because reviewers are motivated more by wanting to teach you how to write good code,
  rather than personal enthusiasm for the material).
* It is essential to read the
  [style guide](https://leanprover-community.github.io/contribute/style.html)
  carefully, and try to follow it very closely.
* Please document your solution thoroughly.
  Remember everything in `/archive/` should be an exemplar of good mathlib style.
  There must be a clear human readable account of the solution at the top of the file
  (ideally something that would score 7!) but don't stop there.
  Please write doc-strings on most of your lemmas, explaining what they are doing and why,
  and in any non-trivial proof include single line comments explaining the significant steps.
* Be nice to your reviewers, and responsive to their suggestions!
  You should expect that your first pull request will involve at least as much work
  after you open the pull request as before.
  Reviewers may ask you to factor out useful lemmas into mathlib,
  or to completely restructure your proof.
* Pay forward what you learn from reviewing:
  there are often several [open pull requests about IMO problems](https://github.com/leanprover-community/mathlib/pulls?q=is%3Aopen+is%3Apr+label%3Aimo),
  and you should go look at the others and see if you can make helpful suggestions!
* If there is a lemma that can be stated more generally than you need for the actual problem,
  but that could be useful for others, be sure to write the more general lemma,
  and include it in the appropriate part of mathlib (i.e. not under `/archive/`).
  (We're much more interested if you find ways that mathlib could be improved to
  make solving your IMO problem easier, than we are in having another solution.)
* Although this may be hard for first time contributors,
  if you can identify a new tactic that would make your proof work more naturally,
  either ask for help on Zulip getting it implemented,
  or start reading about [metaprogramming](https://leanprover-community.github.io/learn.html#metaprogramming-and-tactic-writing)
  and do it yourself. (A new and useful tactic is worth a hundred lemmas!)
