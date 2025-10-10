/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic

/-!
# Induction principles for `∀ i, Finset (α i)`

In this file we prove a few induction principles for functions `Π i : ι, Finset (α i)` defined on a
finite type.

* `Finset.induction_on_pi` is a generic lemma that requires only `[Finite ι]`, `[DecidableEq ι]`,
  and `[∀ i, DecidableEq (α i)]`; this version can be seen as a direct generalization of
  `Finset.induction_on`.

* `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min`: generalizations of
  `Finset.induction_on_max`; these versions require `∀ i, LinearOrder (α i)` but assume
  `∀ y ∈ g i, y < x` and `∀ y ∈ g i, x < y` respectively in the induction step.

## Tags
finite set, finite type, induction, function
-/


open Function

variable {ι : Type*} {α : ι → Type*} [Finite ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Finset

/-- General theorem for `Finset.induction_on_pi`-style induction principles. -/
theorem induction_on_pi_of_choice (r : ∀ i, α i → Finset (α i) → Prop)
    (H_ex : ∀ (i) (s : Finset (α i)), s.Nonempty → ∃ x ∈ s, r i x (s.erase x))
    {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        r i x (g i) → p g → p (update g i (insert x (g i)))) :
    p f := by
  cases nonempty_fintype ι
  induction hs : univ.sigma f using Finset.strongInductionOn generalizing f with | _ s ihs
  subst s
  rcases eq_empty_or_nonempty (univ.sigma f) with he | hne
  · convert h0 using 1
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩
    set g := update f i ((f i).erase x) with hg
    clear_value g
    have hx' : x ∉ g i := by
      rw [hg, update_self]
      apply notMem_erase
    rw [show f = update g i (insert x (g i)) by
      rw [hg, update_idem, update_self, insert_erase x_mem, update_eq_self]] at hr ihs ⊢
    clear hg
    rw [update_self, erase_insert hx'] at hr
    refine step _ _ _ hr (ihs (univ.sigma g) ?_ _ rfl)
    rw [ssubset_iff_of_subset (sigma_mono (Subset.refl _) _)]
    exacts [⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, fun _ _ ↦ le_rfl⟩]

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and `x ∉ g i`, `p g` implies `p (update g i (insert x (g i)))`.

See also `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min` for specialized versions
that require `∀ i, LinearOrder (α i)`. -/
theorem induction_on_pi {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step : ∀ (g : ∀ i, Finset (α i)) (i : ι), ∀ x ∉ g i, p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ x ∉ s) (fun _ s ⟨x, hx⟩ ↦ ⟨x, hx, notMem_erase x s⟩) f
    h0 step

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly greater than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`. -/
theorem induction_on_pi_max [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, y < x) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ ∀ y ∈ s, y < x)
    (fun _ s hs ↦ ⟨s.max' hs, s.max'_mem hs, fun _ ↦ s.lt_max'_of_mem_erase_max' _⟩) f h0 step

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly less than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that needs `x ∉ g i` and does not need `∀ i, LinearOrder (α i)`. -/
theorem induction_on_pi_min [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, x < y) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_max (α := fun i ↦ (α i)ᵒᵈ) _ h0 step

end Finset
