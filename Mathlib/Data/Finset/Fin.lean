/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison, Johan Commelin
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range

/-!
# Finsets in `Fin n`
A few constructions for Finsets in `Fin n`.
## Main declarations
* `Finset.finRange`: `{0, 1, ..., n - 1}` as a `Finset (Fin n)`.
* `Finset.attach_Fin`: Turns a Finset of naturals strictly less than `n` into a `Finset (Fin n)`.
-/

variable {n : ℕ}

namespace Finset

/-- `Finset.finRange n` is the Finset `{0, 1, ..., n - 1}`, as a `Finset (Fin n)`. -/
def finRange (n : ℕ) : Finset (Fin n) := ⟨List.finRange n, List.Nodup_finRange n⟩

@[simp]
lemma mem_finRange (m : Fin n) : m ∈ finRange n := List.mem_finRange m

end Finset
