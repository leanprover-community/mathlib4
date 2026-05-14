/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Smallness of Ext-groups from the existence of enough injectives

Let `C : Type u` be an abelian category (`Category.{v} C`) that has enough injectives.
If `C` is locally `w`-small, i.e. the type of morphisms in `C` are `Small.{w}`,
then we show that the condition `HasExt.{w}` holds, which means that for `X` and `Y` in `C`,
and `n : ℕ`, we may define `Ext X Y n : Type w`. In particular, this holds for `w = v`.

However, the main lemma `hasExt_of_enoughInjectives` is not made an instance:
for a given category `C`, there may be different reasonable choices for the universe `w`,
and if we have two `HasExt.{w₁}` and `HasExt.{w₂}` instances, we would have
to specify the universe explicitly almost everywhere, which would be an inconvenience.
Then, we must be very selective regarding `HasExt` instances.

Note: this file dualizes the results in `HasEnoughProjectives.lean`.

-/

public section

universe w v u

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
lemma isSplitMono_from_singleFunctor_obj_of_injective
    {I : C} [Injective I] {L : CochainComplex C ℤ} {i : ℤ}
    (ι : (CochainComplex.singleFunctor C i).obj I ⟶ L) [L.IsStrictlyGE i] [QuasiIsoAt ι i] :
    IsSplitMono ι := by
  let e := L.pOpcyclesIso (i - 1) i (by simp)
    ((L.isZero_of_isStrictlyGE i (i - 1) (by simp)).eq_of_src _ _)
  let α := (singleObjHomologySelfIso _ _ _).inv ≫ homologyMap ι i ≫ L.homologyι i ≫ e.inv
  have : ι.f i = (singleObjXSelf (ComplexShape.up ℤ) i I).hom ≫ α := by
    rw [← cancel_mono e.hom]
    dsimp [α, e]
    rw [assoc, assoc, assoc, assoc, pOpcyclesIso_inv_hom_id, comp_id, homologyι_naturality]
    dsimp [singleFunctor, singleFunctors]
    rw [singleObjHomologySelfIso_inv_homologyι_assoc,
      ← pOpcycles_singleObjOpcyclesSelfIso_inv_assoc, Iso.inv_hom_id_assoc, p_opcyclesMap]
  exact ⟨⟨{
    retraction := mkHomToSingle (Injective.factorThru (𝟙 I) α) (by
      rintro j rfl
      apply (L.isZero_of_isStrictlyGE (j + 1) j (by simp)).eq_of_src)
    id := by
      apply HomologicalComplex.to_single_hom_ext
      rw [comp_f, mkHomToSingle_f, id_f, this, assoc, Injective.comp_factorThru_assoc,
        id_comp, Iso.hom_inv_id] }⟩⟩

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

lemma to_singleFunctor_obj_eq_zero_of_injective {I : C} [Injective I]
    {K : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj K ⟶ Q.obj ((CochainComplex.singleFunctor C i).obj I))
    (n : ℤ) (hn : i < n) [K.IsStrictlyGE n] :
    φ = 0 := by
  obtain ⟨L, _, g, ι, h, rfl⟩ := left_fac_of_isStrictlyGE φ i
  have hπ : IsSplitMono ι := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective ι
  have h₁ : inv (Q.map ι) = Q.map (retraction ι) := by
    rw [← cancel_epi (Q.map ι), IsIso.hom_inv_id, ← Q.map_comp, IsSplitMono.id, Q.map_id]
  have h₂ : g ≫ retraction ι = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (K.isZero_of_isStrictlyGE n i hn).eq_of_src
  rw [h₁, ← Q.map_comp, h₂, Q.map_zero]

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian.Ext

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
lemma eq_zero_of_injective [HasExt.{w} C] {X I : C} {n : ℕ} [Injective I]
    (e : Ext X I (n + 1)) : e = 0 := by
  let K := (CochainComplex.singleFunctor C 0).obj X
  have := K.isStrictlyGE_of_ge (-n) 0 (by lia)
  letI := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  exact to_singleFunctor_obj_eq_zero_of_injective (K := K) (n := -n) _ (by lia)

lemma subsingleton_of_injective [HasExt.{w} C]
    (X I : C) [Injective I] (n : ℕ) : Subsingleton (Ext.{w} X I (n + 1)) :=
  subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective

end Abelian.Ext

variable (C)

open Abelian

/-- If `C` is a locally `w`-small abelian category with enough injectives,
then `HasExt.{w} C` holds. We do not make this an instance though:
for a given category `C`, there may be different reasonable choices for
the universe `w`, and if we have two `HasExt.{w₁} C` and `HasExt.{w₂} C`
instances, we would have to specify the universe explicitly almost
everywhere, which would be an inconvenience. Then, we must be
very selective regarding `HasExt` instances. -/
lemma hasExt_of_enoughInjectives [LocallySmall.{w} C] [EnoughInjectives C] : HasExt.{w} C := by
    letI := HasDerivedCategory.standard C
    have := hasExt_of_hasDerivedCategory C
    rw [hasExt_iff_small_ext.{w}]
    intro X Y n
    induction n generalizing X Y with
    | zero =>
      rw [small_congr Ext.homEquiv₀]
      infer_instance
    | succ n hn =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have : Function.Surjective (Ext.postcomp hS.extClass X (rfl : n + 1 = _)) :=
        fun y₁ ↦ Ext.covariant_sequence_exact₁ X hS y₁ (Ext.eq_zero_of_injective _) rfl
      exact small_of_surjective.{w} this

end CategoryTheory
