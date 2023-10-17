/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Data.Fintype.BigOperators_aux
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
A supplement to the file
# Measurable spaces and measurable functions
-/


open scoped Classical BigOperators
open Filter
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}


open Set Function MeasurableSpace Equiv

-- move this, maybe next to `measurable_update` in `MeasureTheory.MeasurableSpace`
section Measurable

open Set

variable {α : ι → Type _}

theorem measurable_uniqueElim [Unique ι] [∀ i, MeasurableSpace (α i)] :
    Measurable (uniqueElim : α (default : ι) → ∀ i, α i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The measurable equivalence `(∀ i, α i) ≃ᵐ α ⋆` when the domain of `α` only contains `⋆` -/
@[simps (config := .asFn)]
def MeasurableEquiv.piUnique (α : ι → Type _) [Unique ι] [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ α (default : ι) where
      toFun := fun f => f default
      invFun := uniqueElim
      left_inv := fun f => funext fun i => by
        cases Unique.eq_default i
        rfl
      right_inv := fun x => rfl
      measurable_toFun := measurable_pi_apply _
      measurable_invFun := measurable_uniqueElim

theorem MeasurableSet.univ_pi_fintype {δ} {π : δ → Type _} [∀ i, MeasurableSpace (π i)] [Fintype δ]
    {t : ∀ i, Set (π i)} (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi finite_univ.countable fun i _ => ht i

variable {δ : Type _} [DecidableEq δ] {π : δ → Type _} [∀ a : δ, MeasurableSpace (π a)]

-- not yet moved in mathlib
theorem measurable_updateFinset {s : Finset δ} {x : ∀ i, π i}  : Measurable (updateFinset x s) := by
  simp_rw [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

end Measurable

section MeasurableOnFamily

variable {α : ι → Type _}

variable [∀ i, MeasurableSpace (α i)]

-- we really need a linter that warns me if I don't have a `[DecidableEq ι]` argument here.
-- not yet moved in mathlib
variable (α) in
def MeasurableEquiv.piFinsetUnion [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ᵐ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := (Finset.union s t h).symm
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e

end MeasurableOnFamily
