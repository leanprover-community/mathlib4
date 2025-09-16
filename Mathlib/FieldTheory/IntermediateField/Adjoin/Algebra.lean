/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Adjoining Elements to Fields

This file relates `IntermediateField.adjoin` to `Algebra.adjoin`.
-/

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

namespace algebraAdjoinAdjoin

/-- `IntermediateField.adjoin` as an algebra over `Algebra.adjoin`. -/
scoped instance : Algebra (Algebra.adjoin F S) (adjoin F S) :=
  (Subalgebra.inclusion <| algebra_adjoin_le_adjoin F S).toAlgebra

scoped instance (X) [SMul X F] [SMul X E] [IsScalarTower X F E] :
    IsScalarTower X (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.isScalarTower_left (algebra_adjoin_le_adjoin F S) _

scoped instance (X) [MulAction E X] : IsScalarTower (Algebra.adjoin F S) (adjoin F S) X :=
  Subalgebra.inclusion.isScalarTower_right (algebra_adjoin_le_adjoin F S) _

scoped instance : FaithfulSMul (Algebra.adjoin F S) (adjoin F S) :=
  Subalgebra.inclusion.faithfulSMul (algebra_adjoin_le_adjoin F S)

scoped instance : IsFractionRing (Algebra.adjoin F S) (adjoin F S) :=
  .of_field _ _ fun ⟨_, h⟩ ↦ have ⟨x, hx, y, hy, eq⟩ := mem_adjoin_iff_div.mp h
    ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩

scoped instance : Algebra.IsAlgebraic (Algebra.adjoin F S) (adjoin F S) :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (Algebra.adjoin F S))

end algebraAdjoinAdjoin

theorem adjoin_eq_algebra_adjoin (inv_mem : ∀ x ∈ Algebra.adjoin F S, x⁻¹ ∈ Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymm
    (show adjoin F S ≤
        { Algebra.adjoin F S with
          inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E)
    (h : K.toSubalgebra = Algebra.adjoin F S) : K = adjoin F S := by
  apply toSubalgebra_injective
  rw [h]
  refine (adjoin_eq_algebra_adjoin F _ fun x ↦ ?_).symm
  rw [← h]
  exact K.inv_mem

theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤ :=
  top_le_iff.mp (hS.symm.trans_le <| algebra_adjoin_le_adjoin F S)

section AdjoinSimple

variable (α : E)

@[simp]
theorem AdjoinSimple.isIntegral_gen : IsIntegral F (AdjoinSimple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← AdjoinSimple.algebraMap_gen F α]
  rw [isIntegral_algebraMap_iff (algebraMap F⟮α⟯ E).injective]

variable {F} {α}

theorem adjoin_algebraic_toSubalgebra {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x) :
    (IntermediateField.adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  adjoin_eq_algebra_adjoin _ _ fun _ ↦
    (Algebra.IsIntegral.adjoin fun x hx ↦ (hS x hx).isIntegral).inv_mem

theorem adjoin_simple_toSubalgebra_of_integral (hα : IsIntegral F α) :
    F⟮α⟯.toSubalgebra = Algebra.adjoin F {α} :=
  adjoin_algebraic_toSubalgebra <| by simpa [isAlgebraic_iff_isIntegral]

lemma _root_.Algebra.adjoin_eq_top_of_intermediateField {S : Set E} (hS : ∀ x ∈ S, IsAlgebraic F x)
    (hS₂ : IntermediateField.adjoin F S = ⊤) : Algebra.adjoin F S = ⊤ := by
  simp [*, ← IntermediateField.adjoin_algebraic_toSubalgebra hS]

lemma _root_.Algebra.adjoin_eq_top_of_primitive_element {α : E} (hα : IsIntegral F α)
    (hα₂ : F⟮α⟯ = ⊤) : Algebra.adjoin F {α} = ⊤ :=
  Algebra.adjoin_eq_top_of_intermediateField (by simpa [isAlgebraic_iff_isIntegral]) hα₂

lemma finite_of_fg_of_isAlgebraic
    (h : IntermediateField.FG (⊤ : IntermediateField F E)) [Algebra.IsAlgebraic F E] :
    Module.Finite F E := by
  obtain ⟨s, hs⟩ := h
  have : Algebra.FiniteType F E := by
    use s
    rw [← IntermediateField.adjoin_algebraic_toSubalgebra
      (fun x hx ↦ Algebra.IsAlgebraic.isAlgebraic x)]
    simpa [← IntermediateField.toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

theorem le_sup_toSubalgebra : E1.toSubalgebra ⊔ E2.toSubalgebra ≤ (E1 ⊔ E2).toSubalgebra :=
  sup_le (show E1 ≤ E1 ⊔ E2 from le_sup_left) (show E2 ≤ E1 ⊔ E2 from le_sup_right)

theorem sup_toSubalgebra_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have : (adjoin E1 (E2 : Set L)).toSubalgebra = _ := adjoin_algebraic_toSubalgebra fun x h ↦
    IsAlgebraic.tower_top E1 (isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨x, h⟩ : E2)))
  apply_fun Subalgebra.restrictScalars K at this
  rw [← restrictScalars_toSubalgebra, restrictScalars_adjoin] at this
  -- TODO: rather than using `← coe_type_toSubalgera` here, perhaps we should restate another
  -- version of `Algebra.restrictScalars_adjoin` for intermediate fields?
  simp only [← coe_type_toSubalgebra] at this
  rw [Algebra.restrictScalars_adjoin] at this
  exact this

theorem sup_toSubalgebra_of_isAlgebraic_left [Algebra.IsAlgebraic K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra := by
  have := sup_toSubalgebra_of_isAlgebraic_right E2 E1
  rwa [sup_comm (a := E1), sup_comm (a := E1.toSubalgebra)]

/-- The compositum of two intermediate fields is equal to the compositum of them
as subalgebras, if one of them is algebraic over the base field. -/
theorem sup_toSubalgebra_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  halg.elim (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_left E1 E2)
    (fun _ ↦ sup_toSubalgebra_of_isAlgebraic_right E1 E2)

theorem sup_toSubalgebra_of_left [FiniteDimensional K E1] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_left E1 E2

theorem sup_toSubalgebra_of_right [FiniteDimensional K E2] :
    (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgebra :=
  sup_toSubalgebra_of_isAlgebraic_right E1 E2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `E(L) = E[L]`. -/
theorem adjoin_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) := by
  let i := IsScalarTower.toAlgHom F E K
  let E' := i.fieldRange
  let i' : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField i
  have hi : algebraMap E K = (algebraMap E' K) ∘ i' := by ext x; rfl
  apply_fun _ using Subalgebra.restrictScalars_injective F
  rw [← restrictScalars_toSubalgebra, restrictScalars_adjoin_of_algEquiv i' hi,
    Algebra.restrictScalars_adjoin_of_algEquiv i' hi, restrictScalars_adjoin]
  dsimp only [← E'.coe_type_toSubalgebra]
  rw [Algebra.restrictScalars_adjoin F E'.toSubalgebra]
  exact E'.sup_toSubalgebra_of_isAlgebraic L (halg.imp
    (fun (_ : Algebra.IsAlgebraic F E) ↦ i'.isAlgebraic) id)

theorem adjoin_toSubalgebra_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_toSubalgebra_of_isAlgebraic E L (Or.inl halg)

theorem adjoin_toSubalgebra_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    (adjoin E (L : Set K)).toSubalgebra = Algebra.adjoin E (L : Set K) :=
  adjoin_toSubalgebra_of_isAlgebraic E L (Or.inr halg)

end Tower

end AdjoinSimple

end AdjoinDef

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

theorem fg_of_fg_toSubalgebra (S : IntermediateField F E) (h : S.toSubalgebra.FG) : S.FG := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.FG :=
  S.fg_of_fg_toSubalgebra S.toSubalgebra.fg_of_noetherian

theorem induction_on_adjoin [FiniteDimensional F E] (P : IntermediateField F E → Prop)
    (base : P ⊥) (ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) : P K :=
  letI : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

end IntermediateField

namespace IsFractionRing

variable {F A K L : Type*} [Field F] [CommRing A] [Algebra F A]
  [Field K] [Algebra F K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra F L]
  {g : A →ₐ[F] L} {f : K →ₐ[F] L}

/-- If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
then the image of `f` is the field generated by the image of `g`.
Note: this does not require `IsScalarTower F A K`. -/
theorem algHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = (g : A →+* L)) :
    f.fieldRange = IntermediateField.adjoin F g.range := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  convert ringHom_fieldRange_eq_of_comp_eq h using 2
  exact Set.union_eq_self_of_subset_left fun _ ⟨x, hx⟩ ↦ ⟨algebraMap F A x, by simp [← hx]⟩

/-- If `F` is a field, `A` is an `F`-algebra with fraction field `K`, `L` is a field,
`g : A →ₐ[F] L` lifts to `f : K →ₐ[F] L`,
`s` is a set such that the image of `g` is the subalgebra generated by `s`,
then the image of `f` is the intermediate field generated by `s`.
Note: this does not require `IsScalarTower F A K`. -/
theorem algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (h : RingHom.comp f (algebraMap A K) = (g : A →+* L))
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    f.fieldRange = IntermediateField.adjoin F s := by
  apply IntermediateField.toSubfield_injective
  simp_rw [AlgHom.fieldRange_toSubfield, IntermediateField.adjoin_toSubfield]
  refine ringHom_fieldRange_eq_of_comp_eq_of_range_eq h ?_
  rw [← Algebra.adjoin_eq_ring_closure, ← hs]; rfl

variable [IsScalarTower F A K]

/-- The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by the image
of the algebra hom. -/
theorem liftAlgHom_fieldRange (hg : Function.Injective g) :
    (liftAlgHom hg : K →ₐ[F] L).fieldRange = IntermediateField.adjoin F g.range :=
  algHom_fieldRange_eq_of_comp_eq (by ext; simp)

/-- The image of `IsFractionRing.liftAlgHom` is the intermediate field generated by `s`,
if the image of the algebra hom is the subalgebra generated by `s`. -/
theorem liftAlgHom_fieldRange_eq_of_range_eq (hg : Function.Injective g)
    {s : Set L} (hs : g.range = Algebra.adjoin F s) :
    (liftAlgHom hg : K →ₐ[F] L).fieldRange = IntermediateField.adjoin F s :=
  algHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

end IsFractionRing
