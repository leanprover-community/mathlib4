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


open scoped BigOperators
open Filter
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}


open Set Function MeasurableSpace Equiv

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

end Measurable

section MeasurableOnFamily

variable {α : ι → Type _}

variable [∀ i, MeasurableSpace (α i)]

variable (α)

theorem measurable_eq_mp {i i' : ι} (h : i = i') : Measurable (congr_arg α h).mp := by
  cases h
  exact measurable_id

theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : ι} (h : i = i') {f : β → α i}
    (hf : Measurable f) : Measurable fun x => (congr_arg α h).mp (f x) :=
  (measurable_eq_mp α h).comp hf

variable {α}

theorem measurable_piCongrLeft (f : ι' ≃ ι) : Measurable (piCongrLeft α f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [piCongrLeft_apply_eq_cast]
  apply Measurable.eq_mp α (f.apply_symm_apply i)
  exact measurable_pi_apply (f.symm i)

variable (α)
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def MeasurableEquiv.piCongrLeft (f : ι' ≃ ι) : (∀ b, α (f b)) ≃ᵐ ∀ a, α a := by
  refine' { Equiv.piCongrLeft α f with .. }
  · exact measurable_piCongrLeft f
  simp only [invFun_as_coe, coe_fn_symm_mk]
  rw [measurable_pi_iff]
  exact fun i => measurable_pi_apply (f i)
variable {α}

theorem MeasurableEquiv.piCongrLeft_eq (f : ι' ≃ ι) :
  (MeasurableEquiv.piCongrLeft α f : _ → _) = f.piCongrLeft α := by rfl

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
def MeasurableEquiv.sumPiEquivProdPi (α : ι ⊕ ι' → Type _) [∀ i, MeasurableSpace (α i)] :
   (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') := by
  refine' { Equiv.sumPiEquivProdPi α with .. }
  · refine Measurable.prod ?_ ?_ <;>
      rw [measurable_pi_iff] <;> rintro i <;> apply measurable_pi_apply
  · rw [measurable_pi_iff]; rintro (i|i)
    exact measurable_pi_iff.1 measurable_fst _
    exact measurable_pi_iff.1 measurable_snd _

theorem MeasurableEquiv.coe_sumPiEquivProdPi (α : ι ⊕ ι' → Type _) [∀ i, MeasurableSpace (α i)] :
    (MeasurableEquiv.sumPiEquivProdPi α : _ → _) = Equiv.sumPiEquivProdPi α := by rfl

theorem MeasurableEquiv.coe_sumPiEquivProdPi_symm (α : ι ⊕ ι' → Type _)
    [∀ i, MeasurableSpace (α i)] :
    (MeasurableEquiv.sumPiEquivProdPi α |>.symm : _ → _) = (Equiv.sumPiEquivProdPi α).symm := by rfl

-- we really need a linter that warns me if I don't have a `[DecidableEq ι]` argument here.
variable (α) in
def MeasurableEquiv.piFinsetUnion [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ᵐ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := (Finset.union s t h).symm
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e

variable (α) in
def MeasurableEquiv.piSetUnion {s t : Set ι} [DecidablePred (· ∈ s)] (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ᵐ ∀ i : (s ∪ t : Set ι), α i :=
  let e := (Equiv.Set.union <| Set.disjoint_iff.mp h).symm
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e

end MeasurableOnFamily

open Finset

namespace MeasureTheory


theorem Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine' ⟨fun i => _⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall]
