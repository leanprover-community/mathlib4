/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# K-projective cochain complexes

We define the notion of K-projective cochain complex in an abelian category,
and show that bounded above complexes of projective objects are K-projective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using a projective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive Opposite

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `L`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `L`.)
/-- A cochain complex `K` is K-projective if any morphism `K ⟶ L`
with `L` acyclic is homotopic to zero. -/
class IsKProjective (K : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C ℤ} (f : K ⟶ L) :
    L.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from a
K-projective cochain complex to an acyclic cochain complex. -/
noncomputable irreducible_def IsKProjective.homotopyZero
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hL : L.Acyclic) [K.IsKProjective] :
    Homotopy f 0 :=
  (IsKProjective.nonempty_homotopy_zero f hL).some

lemma _root_.HomotopyEquiv.isKProjective {K₁ K₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv K₁ K₂)
    [K₁.IsKProjective] : K₂.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩

lemma isKProjective_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂)
    [K₁.IsKProjective] :
    K₂.IsKProjective :=
  (HomotopyEquiv.ofIso e).isKProjective

lemma isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂) :
    K₁.IsKProjective ↔ K₂.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso e, fun _ ↦ isKProjective_of_iso e.symm⟩

lemma isKProjective_iff_leftOrthogonal (K : CochainComplex C ℤ) :
    K.IsKProjective ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL ↦ ?_,
      fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]

lemma IsKProjective.leftOrthogonal (K : CochainComplex C ℤ) [K.IsKProjective] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← isKProjective_iff_leftOrthogonal]

instance (K : CochainComplex C ℤ) [hK : K.IsKProjective] (n : ℤ) :
    (K⟦n⟧).IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at hK ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).leftOrthogonal.le_shift n _ hK)

lemma isKProjective_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (K⟦n⟧).IsKProjective ↔ K.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ ↦ inferInstance⟩

lemma isKProjective_of_op {K : CochainComplex C ℤ}
    (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence in
open Cochain.InductionUp in
lemma isKProjective_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ (n : ℤ), Projective (K.X n)] :
    K.IsKProjective := by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : ℤ) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInjective_of_injective L (-d))

end CochainComplex
