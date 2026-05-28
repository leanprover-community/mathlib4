# Mathlib's values

## Our values

To maximise its utility and to cope with the scale of the Mathlib library, we aspire to a number of values as described below.

### Trust
Mathematical notions on paper are not always immediately transcribable to Lean code in a straightforward way. Indeed, subtleties about generality and questions about actual implementations in code can result in difficult questions that need to be answered if we demand the Lean code faithfully reflect the important ideas of modern research mathematics.

Code in Mathlib is reviewed with a careful eye by both experts in that domain of mathematics and by experts in Lean development so that users of the code can trust that definitions and theorem statements are what a mathematician would expect.

### Open source

Mathlib is open source free software.

### Maintainability

When new code is added to Mathlib, the Mathlib Maintainers agree to "maintain" this code indefinitely. This means that if the code needs to be adjusted for any reason (e.g., to make it compatible with a new version of the Lean language or because of changes elsewhere in the library) the Maintainers accept responsibility for ensuring that this adjustment takes place. As a result the Maintainers require that new code is written in such a way as to reduce the chance that such adjustments will be necessary.

### General definitions

Traditional mathematics literature tends to have a much more focussed scope than Mathlib and to have definitions that are tailored to this scope. For example a text on calculus might develop the theory using definitions that are not valid over the p-adic numbers or an algebraic geometry paper might assume the coefficients are complex numbers or a treatise on manifolds might assume they are all finite-dimensional. However in Mathlib we wish to support users in as many situations as reasonably possible and so we tend to take great care to ensure that definitions are very broadly applicable. (And indeed Mathlib's theory of calculus does support the p-adics, its algebraic geometry allows coefficients be any commutative ring, and its manifolds can be infinite-dimensional.)

### Weak hypotheses

When proving theorems in Mathlib we try hard to make assumptions as weak as possible.

As well as having the obvious benefit of making a theorem more widely-applicable, this has the benefit of reducing the work for anyone invoking it. For example, if a theorem remains true when a compactness assumption is dropped, then even for users who are applying the theorem in a situation where compactness holds, it may save them significant work not to have to prove compactness when invoking the theorem. Given that a single theorem may be invoked a great many times, it is often worth the extra effort to weaken its hypotheses as much as possible.

### Strong conclusions

Similar to the "weak hypotheses" value, we try to make theorem conclusions as strong as possible. For example if an existence argument can be upgraded to prove that a set of points has positive measure, then this is the form in which we will state the theorem. Even when this might require substantially more effort, we sometimes strive to provide the stronger conclusion.

### Classical not constructive

Mathlib makes no effort to avoid using the law of excluded middle and almost no effort to have computable definitions. Here we will refer to both these practices as being "constructive".

There are three main reasons why Mathlib does not aim to be constructive:
1. Most contemporary research is not constructive
1. Many results are not true constructively
1. Constructive proofs are often longer and harder

We do not claim this is a superior way to practice mathematics, merely that we have committed to this value for reasons of pragmatism.

Notwithstanding the above, certain corners of Mathlib are actually constructive. This is partly because some important early additions to the library were. However we do not require new material to be constructive and we even prefer non-constructive mathematics if it allows much shorter proofs or a more ergonomic experience for users (in technical terms, one might e.g. wish to avoid "decidability diamonds").

## Accessibility for non-formalists

We desire for Mathlib to be accessible to people who do not have experience with computer code beyond LaTeX. Moreover we wish to achieve such accessibility without compromising on the values above. This is a difficult task and much work remains to be done.

Partly for the sake of accessibility, we require human-readable comments (aka "doc strings") on all definitions and we encourage thoughtful code comments in general, especially in longer proofs. Such code comments are often most useful when they use natural language or LaTeX rather than Lean code. We also believe that key to accessibility is the creation of independent artifacts (tutorials, phrasebooks, teaching courses, ...) which build on top of Mathlib and give side-by-side demonstrations of important concepts.

## Implications for PR review

Mathlib changes by merging PRs (pull requests) from contributors. It is largely during review of such PRs that mission alignment is assessed and values are enacted. We provide some comments on this code review process below. In many cases, more detail is available in the [style guide](https://leanprover-community.github.io/contribute/style.html) and the [PR Review Guide](https://leanprover-community.github.io/contribute/pr-review.html).

### Please be courteous

Mathlib has a [Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md). Please bear this in mind when contributing and reviewing.

### Is the subject matter appropriate?

The first question asked of every contribution is whether the subject matter is within the scope of Mathlib. This is usually easy to answer. See [here](https://leanprover-community.github.io/contribute/index.html#what-to-contribute-to-mathlib) for further remarks.

### Is the author a human?

In addition to its other functions, code review is an educational tool. Mathlib has hundreds of contributors and most probably learned their art during the review process. For newcomers, it is not uncommon for the educational aspect of review to be significantly more valuable than the actual contribution to the library. Because review bandwidth is constantly saturated, many reviewers are unwilling to perform their service unless the author is a human.

### Is the code maintainable?

Making a careful assessment of maintainability is a key part of review.

### Is the code performant?

We try hard to avoid adding code which is slow to elaborate or to typecheck. If code uses `set_option` to change the default values of values like `maxHeartbeats` or `synthInstance.maxHeartbeats` then usually something is wrong. Moreover we wish for code to be sufficiently robust that we can expect future code, developed on top of it, will not encounter performance issues.

Lean includes a suite of tools for profiling code. In addition, commenting with `!bench` on a PR provides valuable performance information.

### Are the definitions "correct"?

This is perhaps the most important function of review as Lean can only tell you that you have defined *something*, but not that you have defined what you intended. Non-trivial definitions get the most attention during review.

In addition there are non-mathematical reasons for giving definitions special attention. There often exist many mathematically-correct implementations of the same concept in Lean, and some of these may have distinct advantages over others.

### Is there API for new definitions?

New definitions should come with lemmas that use them. In ideal situations a definition can be completely characterised by a collection of lemmas but even when this is not possible, a partial characterisation is still very desirable. We call such a collection of lemmas the API and during review we encourage contributors to add such lemmas. Adding API also helps increase confidence that the definition means what is intended, and that it is ergonomic.

### Are the theorems appropriate?

After definitions, we study new theorems, checking that hypotheses are as weak as reasonably possible and that conclusions are strong. In addition, during review we often request contributors "modularise" theorems far more than in the informal literature by breaking a theorem down into many small lemmas.

### Data-bearing typeclass instances creating diamonds?

Any new data-bearing typeclass `instance`s are studied during review to increase confidence that diamonds are not being created. These can be difficult to spot and careful thought is needed.

### Is the naming correct?

Mathlib follows a naming scheme described [here](https://leanprover-community.github.io/contribute/naming.html). We try to enforce this during review.

### Are things in the right files?

Placing definitions, lemmas, and theorems in the right files is important. By keeping Mathlib's import tree wide, we reduce the memory footprint for people importing just a fragment of the library and we decrease wall-clock compile time by enabling easier compile parallelisation. Another reason for correct placement is discoverability: we want to make it easy to guess where a definition or lemma might be.

### Are the proofs human-readable?

Longer proof scripts (50+ lines) should make an effort to sketch the shape of the argument, using code comments if necessary. This is of less importance than other items but is still desirable.

### Are automation annotations in place?

Ensuring that annotations for automation like `simp`, `gcongr`, `fun_prop`, `grind` are added is an important part of review. Similarly, use of code generators like `to_additive`, `to_dual` should also be checked during review.

### Is the code style good?

During review we also check for minor points of style such as:
 * Use of `variable` where appropriate.
 * Use of `section` and `namespace` where appropriate.
 * Are the right `public` and `private` modifiers in place? (New files should avoid using `@[expose] public section` for everything.)
 * Proof golfing, but not overgolfing. Note that reducing character / line count is sometimes a side effect of a better proof but it is not a goal, and often a better proof can increase these values.
 * Whitespace.
 * Formatting of doc strings.
