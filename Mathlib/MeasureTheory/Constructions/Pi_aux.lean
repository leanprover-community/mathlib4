/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Basic_aux

/-!
A supplement to the file
# Product measures
-/


open scoped Classical ENNReal
open Function MeasureTheory.OuterMeasure Equiv Finset Sum MeasureTheory.Measure
set_option autoImplicit true

noncomputable section

variable {ι ι' ι'' : Type _}

namespace MeasureTheory

variable {α : ι → Type _}
variable [∀ i, MeasurableSpace (α i)]
variable [Fintype ι] [Fintype ι']
variable {m : ∀ i, OuterMeasure (α i)}
variable (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]

/-- Some properties of `Measure.pi` -/

-- oops, previous PR was wrong. Don't move these, fix statement
theorem MeasurableEquiv.piCongrLeft_eq' (f : ι' ≃ ι) :
    ⇑MeasurableEquiv.piCongrLeft α f = f.piCongrLeft α := by rfl

theorem MeasurableEquiv.coe_sumPiEquivProdPi_symm' (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine' (pi_eq fun s _ => _).symm
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.piCongrLeft_eq' f,
      piCongrLeft_preimage_univ_pi, pi_pi _ _, f.prod_comp (fun i => μ i (s i))]

theorem measurePreserving_sumPiEquivProdPi_symm {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi π).symm
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) where
  measurable := (MeasurableEquiv.sumPiEquivProdPi π).symm.measurable
  map_eq := by
    refine' (pi_eq fun s _ => _).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm',
      sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_type]

theorem measurePreserving_sumPiEquivProdPi {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi π)
      (Measure.pi μ) ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) :=
  measurePreserving_sumPiEquivProdPi_symm μ |>.symm

-- not yet moved
theorem measurePreserving_piFinsetUnion [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h)
      ((Measure.pi fun i : s ↦ μ i).prod (Measure.pi fun i : t ↦ μ i))
      (Measure.pi fun i : ↥(s ∪ t) ↦ μ i) :=
  let e := (Finset.union s t h).symm
  measurePreserving_piCongrLeft (fun i : ↥(s ∪ t) ↦ μ i) e |>.comp <|
    measurePreserving_sumPiEquivProdPi_symm fun b ↦ μ (e b)

-- not yet moved
-- generalizes `measurePreserving_funUnique`
theorem measurePreserving_piUnique {π : ι → Type _} [Unique ι] [∀ i, MeasurableSpace (π i)]
    (μ : ∀ i, Measure (π i)) :
    MeasurePreserving (MeasurableEquiv.piUnique π) (Measure.pi μ) (μ default) where
  measurable := (MeasurableEquiv.piUnique π).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique π
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure, Fintype.prod_unique, e.symm.map_apply]
      congr 1; exact e.toEquiv.image_eq_preimage s
    simp_rw [Measure.pi, OuterMeasure.pi, this, boundedBy_eq_self, toOuterMeasure_toMeasure,
      MeasurableEquiv.map_map_symm]

-- namespace Measure

-- theorem pi_map_left (f : ι' ≃ ι) :
--     map (MeasurableEquiv.piCongrLeft α f) (Measure.pi fun i' => μ (f i')) = Measure.pi μ :=
--   measurePreserving_piCongrLeft μ f |>.map_eq

-- theorem pi_sum {π : ι ⊕ ι' → Type _} [∀ i, MeasurableSpace (π i)] (μ : ∀ i, Measure (π i))
--     [∀ i, SigmaFinite (μ i)] :
--     map (MeasurableEquiv.sumPiEquivProdPi π).symm
--       ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) = Measure.pi μ :=
--   measurePreserving_sumPiEquivProdPi_symm μ |>.map_eq

-- theorem map_piUnique_symm [Unique ι] :
--     map (MeasurableEquiv.piUnique α).symm (μ (default : ι)) = Measure.pi μ :=
--   (measurePreserving_piUnique μ).symm _ |>.map_eq

-- theorem pi_unique {π : ι → Type _} [Unique ι] [∀ i, MeasurableSpace (π i)]
--     (μ : ∀ i, Measure (π i)) :
--     map (MeasurableEquiv.piUnique π) (Measure.pi μ) = μ default :=
--   measurePreserving_piUnique μ |>.map_eq

-- end Measure
