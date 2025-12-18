/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Tactic.Basic

/-!
# Documentation for `ext` tactic

This file contains a library note on the use of the `ext` tactic and `@[ext]` attribute.
-/

public section

library_note «partially-applied ext lemmas»
/--
When possible, `ext` lemmas are stated without a full set of arguments. As an example, for bundled
homs `f`, `g`, and `of`, `f.comp of = g.comp of → f = g` is a better `ext` lemma than
`(∀ x, f (of x) = g (of x)) → f = g`, as the former allows a second type-specific extensionality
lemmas to be applied to `f.comp of = g.comp of`.
If the domain of `of` is `ℕ` or `ℤ` and `of` is a `RingHom`, such a lemma could then make the goal
`f (of 1) = g (of 1)`.

For bundled morphisms, there is a `ext` lemma that always applies of the form
`(∀ x, ⇑f x = ⇑g x) → f = g`. When adding type-specific `ext` lemmas like the one above, we want
these to be tried first. This happens automatically since the type-specific lemmas are inevitably
defined later.
-/
