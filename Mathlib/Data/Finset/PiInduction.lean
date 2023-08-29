/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Sigma

#align_import data.finset.pi_induction from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

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
    (H_ex : ∀ (i) (s : Finset (α i)) (_ : s.Nonempty), ∃ x ∈ s, r i x (s.erase x))
    {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        r i x (g i) → p g → p (update g i (insert x (g i)))) :
    p f := by
  cases nonempty_fintype ι
  -- ⊢ p f
  induction' hs : univ.sigma f using Finset.strongInductionOn with s ihs generalizing f; subst s
  -- ⊢ p f
                                                                                         -- ⊢ p f
  cases' eq_empty_or_nonempty (univ.sigma f) with he hne
  -- ⊢ p f
  · convert h0 using 1
    -- ⊢ f = fun x => ∅
    simpa [funext_iff] using he
    -- 🎉 no goals
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    -- ⊢ p f
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩
    -- ⊢ p f
    set g := update f i ((f i).erase x) with hg
    -- ⊢ p f
-- Porting note: this tactic does not exist yet
--  clear_value g
    have hx' : x ∉ g i := by
      rw [hg, update_same]
      apply not_mem_erase
    rw [show f = update g i (insert x (g i)) by
      rw [hg, update_idem, update_same, insert_erase x_mem, update_eq_self]] at hr ihs ⊢
    clear hg
    -- ⊢ p (update g i (insert x (g i)))
    rw [update_same, erase_insert hx'] at hr
    -- ⊢ p (update g i (insert x (g i)))
    refine step _ _ _ hr (ihs (univ.sigma g) ?_ _ rfl)
    -- ⊢ Finset.sigma univ g ⊂ Finset.sigma univ (update g i (insert x (g i)))
    rw [ssubset_iff_of_subset (sigma_mono (Subset.refl _) _)]
    -- ⊢ ∃ x_1, x_1 ∈ Finset.sigma univ (update g i (insert x (g i))) ∧ ¬x_1 ∈ Finset …
    exacts [⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, fun _ _ ↦ le_rfl⟩]
#align finset.induction_on_pi_of_choice Finset.induction_on_pi_of_choice

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and `x ∉ g i`, `p g` implies `p (update g i (insert x (g i)))`.

See also `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min` for specialized versions
that require `∀ i, LinearOrder (α i)`.  -/
theorem induction_on_pi {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i) (_ : x ∉ g i),
        p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ x ∉ s) (fun _ s ⟨x, hx⟩ ↦ ⟨x, hx, not_mem_erase x s⟩) f
    h0 step
#align finset.induction_on_pi Finset.induction_on_pi

-- Porting note: this docstring is the exact translation of the one from mathlib3 but
-- the last sentence (here and in the next lemma) does make much sense to me...
/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly greater than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that `x ∉ g i` instead of ` does not need `∀ i, LinearOrder (α i)`. -/
theorem induction_on_pi_max [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, y < x) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s ↦ ∀ y ∈ s, y < x)
    (fun _ s hs ↦ ⟨s.max' hs, s.max'_mem hs, fun _ ↦ s.lt_max'_of_mem_erase_max' _⟩) f h0 step
#align finset.induction_on_pi_max Finset.induction_on_pi_max

/-- Given a predicate on functions `∀ i, Finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `fun _ ↦ ∅` and for any function `g : ∀ i, Finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly less than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `LinearOrder` instances on all `α i`. See also `Finset.induction_on_pi` for a
version that `x ∉ g i` instead of ` does not need `∀ i, LinearOrder (α i)`. -/
theorem induction_on_pi_min [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ ↦ ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, x < y) → p g → p (update g i (insert x (g i)))) :
    p f :=
  @induction_on_pi_max ι (fun i ↦ (α i)ᵒᵈ) _ _ _ _ _ _ h0 step
#align finset.induction_on_pi_min Finset.induction_on_pi_min

end Finset
