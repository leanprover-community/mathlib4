/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # Calculus of fractions in the derived category

We obtain various consequences of the calculus of left and right fractions
for `HomotopyCategory.quasiIso C (ComplexShape.up ℤ)` as lemmas about
factorizations of morphisms `f : Q.obj X ⟶ Q.obj Y` (where `X` and `Y`
are cochain complexes). These `f` can be factored as
a right fraction `inv (Q.map s) ≫ Q.map g` or as a left fraction
`Q.map g ≫ inv (Q.map s)`, with `s` a quasi-isomorphism (to `X` or from `Y`).
When strict bounds are known on `X` or `Y`, certain bounds may also be ensured
on the auxiliary object appearing in the fraction.

-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomorphism and `g : X' ⟶ Y`. -/
lemma right_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category can be written
as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y'` a quasi-isomorphism. -/
lemma left_fac {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `X` strictly `≤ n`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X` a quasi-isomorphism with
`X'` strictly `≤ n` and `g : X' ⟶ Y`. -/
lemma right_fac_of_isStrictlyLE {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [X.IsStrictlyLE n] :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (_ : IsIso (Q.map s))
      (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac f
  have : IsIso (Q.map (CochainComplex.truncLEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨X'.truncLE n, inferInstance, CochainComplex.truncLEMap s n ≫ X.ιTruncLE n, ?_,
      CochainComplex.truncLEMap g n ≫ Y.ιTruncLE n, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category with `Y` strictly `≥ n`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and `s : Y ⟶ Y'`
a quasi-isomorphism with `Y'` strictly `≥ n`. -/
lemma left_fac_of_isStrictlyGE {X Y : CochainComplex C ℤ} (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [Y.IsStrictlyGE n] :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')
      (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac f
  have : IsIso (Q.map (CochainComplex.truncGEMap s n)) := by
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    rw [isIso_Q_map_iff_quasiIso] at hs
    infer_instance
  refine ⟨Y'.truncGE n, inferInstance, X.πTruncGE n ≫ CochainComplex.truncGEMap g n,
    Y.πTruncGE n ≫ CochainComplex.truncGEMap s n, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · have eq := Q.congr_map (CochainComplex.πTruncGE_naturality s n)
    have eq' := Q.congr_map (CochainComplex.πTruncGE_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_mono (Q.map (CochainComplex.πTruncGE Y n)
      ≫ Q.map (CochainComplex.truncGEMap s n)), assoc, IsIso.inv_hom_id, comp_id]
    simp only [eq, IsIso.inv_hom_id_assoc, eq']

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≥ a` and `≤ b`, and `Y` strictly `≥ a`
can be written as `f = inv (Q.map s) ≫ Q.map g` with `s : X' ⟶ X`
a quasi-isomorphism with `X'` strictly `≥ a` and `≤ b`, and `g : X' ⟶ Y`. -/
lemma right_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C ℤ} (a b : ℤ) [X.IsStrictlyGE a] [X.IsStrictlyLE b]
    [Y.IsStrictlyGE a] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyGE a) (_ : X'.IsStrictlyLE b)
    (s : X' ⟶ X) (_ : IsIso (Q.map s)) (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', hX', s, hs, g, fac⟩ := right_fac_of_isStrictlyLE f b
  have : IsIso (Q.map (CochainComplex.truncGEMap s a)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
    infer_instance
  refine ⟨X'.truncGE a, inferInstance, inferInstance,
    CochainComplex.truncGEMap s a ≫ inv (X.πTruncGE a), ?_,
      CochainComplex.truncGEMap g a ≫ inv (Y.πTruncGE a), ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_epi (Q.map s), IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← CochainComplex.πTruncGE_naturality s a,
      Functor.map_comp, assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, CochainComplex.πTruncGE_naturality g a,
      Functor.map_comp, assoc, IsIso.hom_inv_id, comp_id]

/-- Any morphism `f : Q.obj X ⟶ Q.obj Y` in the derived category
with `X` strictly `≤ b`, and `Y` strictly `≥ a` and `≤ b`
can be written as `f = Q.map g ≫ inv (Q.map s)` with `g : X ⟶ Y'` and
`s : Y ⟶ Y'` a quasi-isomorphism with `Y'` strictly `≥ a` and `≤ b`. -/
lemma left_fac_of_isStrictlyLE_of_isStrictlyGE
    {X Y : CochainComplex C ℤ} (a b : ℤ)
    [X.IsStrictlyLE b] [Y.IsStrictlyGE a] [Y.IsStrictlyLE b] (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE a) (_ : Y'.IsStrictlyLE b)
    (g : X ⟶ Y') (s : Y ⟶ Y') (_ : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', hY', g, s, hs, fac⟩ := left_fac_of_isStrictlyGE f a
  have : IsIso (Q.map (CochainComplex.truncLEMap s b)) := by
    rw [isIso_Q_map_iff_quasiIso] at hs
    rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
    infer_instance
  refine ⟨Y'.truncLE b, inferInstance, inferInstance,
    inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap g b,
    inv (Y.ιTruncLE b) ≫ CochainComplex.truncLEMap s b, ?_, ?_⟩
  · rw [Q.map_comp]
    infer_instance
  · simp only [Functor.map_comp, Functor.map_inv, IsIso.inv_comp, IsIso.inv_inv, assoc, fac,
      ← cancel_mono (Q.map s), IsIso.inv_hom_id, comp_id]
    rw [← Functor.map_comp, ← CochainComplex.ιTruncLE_naturality s b,
      Functor.map_comp, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, CochainComplex.ιTruncLE_naturality g b,
      Functor.map_comp, IsIso.inv_hom_id_assoc]

lemma subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE (X Y : CochainComplex C ℤ)
    (a b : ℤ) (h : a < b) [X.IsStrictlyLE a] [Y.IsStrictlyGE b] :
    Subsingleton (Q.obj X ⟶ Q.obj Y) := by
  suffices ∀ (f : Q.obj X ⟶ Q.obj Y), f = 0 from ⟨by simp [this]⟩
  intro f
  obtain ⟨X', _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE f a
  have : g = 0 := by
    ext i
    by_cases hi : a < i
    · apply (X'.isZero_of_isStrictlyLE a i hi).eq_of_src
    · apply (Y.isZero_of_isStrictlyGE b i (by lia)).eq_of_tgt
  rw [this, Q.map_zero, comp_zero]

end DerivedCategory
