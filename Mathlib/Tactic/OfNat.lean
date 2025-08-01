/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Init

/-! # The `ofNat()` macro -/

/--
This macro is a shorthand for `OfNat.ofNat` combined with `no_index`.

When writing lemmas about `OfNat.ofNat`, the term needs to be wrapped
in `no_index` so as not to confuse `simp`, as `no_index (OfNat.ofNat n)`.

Some discussion is [on Zulip here](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20Polynomial.2Ecoeff.20example/near/395438147).
-/
macro "ofNat(" n:term ")" : term => `(no_index (OfNat.ofNat $n))
