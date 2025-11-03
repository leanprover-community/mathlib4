/-
Copyright (c) 2025 Jan Förster, Leon Müller, Luis Sand, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Förster, Leon Müller, Luis Sand, Junyan Xu
-/
import Mathlib.Data.Set.Card
import Mathlib.Topology.Closure

/-!
# The Kuratowski closure-complement theorem

This file proves Kuratowski's closure-complement theorem, which says that if one repeatedly
applies the closure and complement operators to a set in a topological space, at most 14
distinct sets can be obtained.

In another file it will be shown that the maximum can be realized in the real numbers.
(A set realizing the maximum is called a 14-set.)

## Main definitions

* `Topology.ClosureCompl.IsObtainable` is the binary inductive predicate saying that a set can be
  obtained from another using the closure and complement operations.

* `Topology.ClosureCompl.theFourteen` is an explicit multiset of fourteen sets obtained from a
  given set using the closure and complement operations.

## Main results

* `Topology.ClosureCompl.mem_theFourteen_iff_isObtainable`:
  a set `t` is obtainable by from `s` if and only if they are in the Multiset `theFourteen s`.

* `Topology.ClosureCompl.ncard_isObtainable_le_fourteen`:
  for an arbitrary set `s`, there are at most 14 distinct sets that can be obtained from `s` using
  the closure and complement operations (the **Kuratowski closure-complement theorem**).

## Notation

* `k`: the closure of a set.
* `i`: the interior of a set.
* `c`: the complement of a set in docstrings; `ᶜ` is used in the code.

## References

* https://en.wikipedia.org/wiki/Kuratowski%27s_closure-complement_problem
* https://web.archive.org/web/20220212062843/http://nzjm.math.auckland.ac.nz/images/6/63/The_Kuratowski_Closure-Complement_Theorem.pdf
-/

namespace Topology.ClosureCompl

variable {X : Type*} [TopologicalSpace X]

/-- `IsObtainable s t` means that `t` can be obtained from `s` by taking closures and complements.
-/
inductive IsObtainable (s : Set X) : Set X → Prop
  | base : IsObtainable s s
  | protected closure ⦃t : Set X⦄ : IsObtainable s t → IsObtainable s (closure t)
  | complement ⦃t : Set X⦄ : IsObtainable s t → IsObtainable s tᶜ

scoped notation "k" => closure
scoped notation "i" => interior

/-- The function `kckc` is idempotent: `kckckckc s = kckc s` for any set `s`.
This is because `ckc = i` and `ki` is idempotent. -/
theorem kckc_idem (s : Set X) : k (k (k (k sᶜ)ᶜ)ᶜ)ᶜ = k (k sᶜ)ᶜ := by simp

/-- Cancelling the first applied complement we obtain `kckckck s = kck s` for any set `s`. -/
theorem kckckck_eq_kck (s : Set X) : k (k (k (k s)ᶜ)ᶜ)ᶜ = k (k s)ᶜ := by simp

/-- The at most fourteen sets that are obtainable from `s` are given by applying
`id, c, k, ck, kc, ckc, kck, ckck, kckc, ckckc, kckck, ckckck, kckckc, ckckckc` to `s`. -/
def theFourteen (s : Set X) : Multiset (Set X) :=
  {s, sᶜ, k s, (k s)ᶜ, k sᶜ, (k sᶜ)ᶜ, k (k s)ᶜ, (k (k s)ᶜ)ᶜ,
    k (k sᶜ)ᶜ, (k (k sᶜ)ᶜ)ᶜ, k (k (k s)ᶜ)ᶜ, (k (k (k s)ᶜ)ᶜ)ᶜ,
    k (k (k sᶜ)ᶜ)ᶜ, (k (k (k sᶜ)ᶜ)ᶜ)ᶜ}

/-- `theFourteen` has exactly 14 sets (possibly with repetition) in it. -/
theorem card_theFourteen (s : Set X) : (theFourteen s).card = 14 := rfl

/-- If `t` is obtainable from `s` by the closure and complement operations,
then it is in the multiset `theFourteen s`. -/
theorem IsObtainable.mem_theFourteen {s t : Set X} (h : IsObtainable s t) : t ∈ theFourteen s := by
  induction h with | base => exact .head _ | closure _ mem => ?_ | complement _ mem => ?_
  all_goals repeat obtain _ | ⟨_, mem⟩ := mem; rotate_left
  all_goals simp [theFourteen]

/-- A set `t` is obtainable by from `s` if and only if they are in the Multiset `theFourteen s`. -/
theorem mem_theFourteen_iff_isObtainable {s t : Set X} :
    t ∈ theFourteen s ↔ IsObtainable s t where
  mp h := by
    repeat
      obtain _ | ⟨_, h⟩ := h
      rotate_left
    all_goals
      repeat
        first
        | apply IsObtainable.complement
        | apply IsObtainable.closure
      exact IsObtainable.base
  mpr := (·.mem_theFourteen)

/-- **Kuratowski's closure-complement theorem**: the number of obtainable sets via closure and
complement operations from a single set `s` is at most 14. -/
theorem ncard_isObtainable_le_fourteen (s : Set X) : {t | IsObtainable s t}.ncard ≤ 14 := by
  classical
  convert Set.ncard_coe_finset _ ▸ (theFourteen s).toFinset_card_le
  simp [Set.ext_iff, mem_theFourteen_iff_isObtainable]

end Topology.ClosureCompl
