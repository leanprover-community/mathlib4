/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.

- `sepDegree F E`: the separable degree of an algebraic extension `E / F` of fields, defined to be
  the cardinal of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  (Mathematically, it should be the algebraic closure of `F`, but in order to make the type
  compatible with `Module.rank F E`, we use the algebraic closure of `E`.)
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

- `finSepDegree F E`: the separable degree of `E / F` as a natural number, which is zero if
  `sepDegree F E` is not finite.

## Main results

- `emb_equiv_of_equiv`: a random isomorphism between `Emb F E` and `Emb F E'` when `E` and `E'` are
  isomorphic as `F`-algebras.

- `sepDegree_eq_of_equiv`, `finSepDegree_eq_of_equiv`: if `E` and `E'` are isomorphic as
  `F`-algebras, then they have the same separable degree over `F`.

## Tags

separable degree, degree, polynomial

## TODO

- ...

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

noncomputable section

universe u v v' w

variable (F : Type u) (E : Type v) [Field F] [Field E]

variable [Algebra F E]

namespace Field

/-- `Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
-/
def Emb := E →ₐ[F] (AlgebraicClosure E)

/-- If `E / F` is an algebraic extension, then the separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.
-/
def sepDegree := Cardinal.mk (Emb F E)

/-- The separable degree of `E / F` as a natural number. -/
def finSepDegree : ℕ := Cardinal.toNat (sepDegree F E)

lemma emb_nonempty : Nonempty (Emb F E) :=
  Nonempty.intro <| IsScalarTower.toAlgHom F E (AlgebraicClosure E)

lemma sepDegree_nezero : NeZero (sepDegree F E) :=
  NeZero.mk <| haveI := emb_nonempty F E; Cardinal.mk_ne_zero _

lemma finSepDegree_nezero_of_finiteDimensional [FiniteDimensional F E] :
    NeZero (finSepDegree F E) := NeZero.mk <| by
  haveI : Fintype (Emb F E) := minpoly.AlgHom.fintype _ _ _
  haveI := emb_nonempty F E
  simp only [finSepDegree, sepDegree, Cardinal.mk_toNat_eq_card]
  exact Fintype.card_ne_zero

/-- A random isomorphism between `Emb F E` and `Emb F E'` when `E` and `E'` are isomorphic
as `F`-algebras. -/
def emb_equiv_of_equiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    Emb F E ≃ Emb F E' := by
  let i' : (AlgebraicClosure E) ≃ₐ[F] (AlgebraicClosure E') := AlgEquiv.symm <| by
    letI : Algebra E E' := i.toAlgHom.toRingHom.toAlgebra
    apply AlgEquiv.restrictScalars (R := F) (S := E)
    apply IsAlgClosure.equivOfAlgebraic E E' (AlgebraicClosure E') (AlgebraicClosure E)
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := E') (i.symm.toAlgHom x)
    rw [show ∀ y : E, (algebraMap E E') y = i.toAlgHom y from fun y ↦ rfl] at h
    simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply] using h
  refine ⟨fun f ↦ (i'.toAlgHom.comp f).comp i.symm.toAlgHom,
    fun f ↦ (i'.symm.toAlgHom.comp f).comp i.toAlgHom, fun f ↦ ?_, fun f ↦ ?_⟩
  · simp only [AlgHom.comp_assoc]
    rw [← AlgHom.comp_assoc]
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.symm_comp, AlgHom.comp_id, AlgHom.id_comp]
  · simp only [AlgHom.comp_assoc]
    rw [← AlgHom.comp_assoc]
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.comp_symm, AlgHom.comp_id, AlgHom.id_comp]

/-- If `E` and `E'` are isomorphic as `F`-algebras, then they have the same separable degree
over `F`. -/
theorem sepDegree_eq_of_equiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    Cardinal.lift.{v'} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F E') := by
  have := ((Equiv.ulift.{v'} (α := E →ₐ[F] (AlgebraicClosure E))).trans
    (emb_equiv_of_equiv F E E' i)).trans
      (Equiv.ulift.{v} (α := E' →ₐ[F] (AlgebraicClosure E'))).symm
  simpa only [Cardinal.mk_uLift] using this.cardinal_eq

/-- If `E` and `E'` are isomorphic as `F`-algebras, then they have the same `finSepDegree`
over `F`. -/
theorem finSepDegree_eq_of_equiv (E' : Type v') [Field E'] [Algebra F E'] (i : E ≃ₐ[F] E') :
    finSepDegree F E = finSepDegree F E' := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_equiv F E E' i)

@[simp]
theorem sepDegree_self : sepDegree F F = 1 :=
  le_antisymm
    (show sepDegree F F ≤ 1 from Cardinal.le_one_iff_subsingleton.2 AlgHom.subsingleton)
      (Cardinal.one_le_iff_ne_zero.2 (sepDegree_nezero F F).out)

@[simp]
theorem finSepDegree_self : finSepDegree F F = 1 := by
  simp only [finSepDegree, sepDegree_self, Cardinal.one_toNat]

@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := sepDegree_eq_of_equiv _ _ _ (IntermediateField.botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{u, v}, Cardinal.lift_inj] at this

@[simp]
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  simp only [finSepDegree, sepDegree_bot, Cardinal.one_toNat]

@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField F E) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv F _ E IntermediateField.topEquiv

@[simp]
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField F E) = finSepDegree F E := by
  simp only [finSepDegree, sepDegree_top]

theorem sepDegree_bot' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
      Cardinal.lift.{w} (sepDegree F E) := by
  exact sepDegree_eq_of_equiv _ _ _ ((IntermediateField.botEquiv E K).restrictScalars F)

@[simp]
theorem sepDegree_bot'' (K : Type v) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : sepDegree F (⊥ : IntermediateField E K) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_bot' F E K

@[simp]
theorem finSepDegree_bot' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (sepDegree_bot' F E K)

@[simp]
theorem sepDegree_top' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv _ _ _
    ((IntermediateField.topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem finSepDegree_top' (K : Type w) [Field K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K := by
  simp only [finSepDegree, sepDegree_top']

end Field
