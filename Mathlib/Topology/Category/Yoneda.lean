/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

universe w w' v u

open CategoryTheory Opposite Limits

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

def coyoneda : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)

def coyoneda' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  obj X := C((unop X).1, Y)
  map f g := ContinuousMap.comp g f.unop

lemma coyoneda_eq_comp : coyoneda F Y = F.op ⋙ coyoneda' Y := rfl

lemma piComparison_fac {α : Type} (X : α → TopCat) :
    piComparison (coyoneda'.{w, w'} Y) (fun x ↦ op (X x)) =
    (coyoneda' Y).map ((opCoproductIsoProduct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫
    (equivEquivIso (sigmaEquiv Y (fun x ↦ (X x).1))).inv ≫ (Types.productIso _).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  ext
  simp only [coyoneda', unop_op, piComparison, types_comp_apply,
    Types.productIso_hom_comp_eval_apply, Types.pi_lift_π_apply, comp_apply, TopCat.coe_of,
    unop_comp, Quiver.Hom.unop_op, sigmaEquiv, equivEquivIso_hom, Equiv.toIso_inv,
    Equiv.coe_fn_symm_mk, comp_assoc, sigmaMk_apply, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

noncomputable
instance {α : Type} (X : α → TopCat) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) (coyoneda'.{w, w'} Y) := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ (coyoneda' Y) _ (fun x ↦ op (X x)) _ _ ?_
  rw [piComparison_fac]
  infer_instance

noncomputable
instance : PreservesFiniteProducts (coyoneda'.{w, w'} Y) where
  preserves J _ := {
    preservesLimit := by
      intro K
      let i : K ≅ Discrete.functor (fun i ↦ op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      exact preservesLimitOfIsoDiagram _ i.symm }

end ContinuousMap

open ContinuousMap

variable (X : (Type (max u v))) [TopologicalSpace X] (G : C ⥤ TopCat.{v})

theorem factorsThrough_of_pullbackCondition {Z B : C} {π : Z ⟶ B} [HasPullback π π]
    [PreservesLimit (cospan π π) G]
    {a : C(G.obj Z, X)}
    (ha : a ∘ (G.map pullback.fst) = a ∘ (G.map (pullback.snd (f := π) (g := π)))) :
    Function.FactorsThrough a (G.map π) := by
  intro x y hxy
  let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv <|
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : ∀ y, G.map pullback.fst ((PreservesPullback.iso G π π).inv y) =
      pullback.fst (f := G.map π) (g := G.map π) y := by
    simp only [← PreservesPullback.iso_inv_fst]; intro y; rfl
  have h₂ : ∀ y, G.map pullback.snd ((PreservesPullback.iso G π π).inv y) =
      pullback.snd (f := G.map π) (g := G.map π) y := by
    simp only [← PreservesPullback.iso_inv_snd]; intro y; rfl
  erw [h₁, h₂] at ha'
  simpa using ha'

variable [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], HasPullback π π]
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) G]
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], EffectiveEpi (pullback.fst (f := π) (g := π))]
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], QuotientMap (G.map π))

theorem EqualizerConditionCoyoneda : EqualizerCondition.{v, u} (coyoneda G X) := by
  intro Z B π _ _
  refine ⟨fun a b h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · simp only [ContinuousMap.coyoneda, unop_op, Quiver.Hom.unop_op, Set.coe_setOf, MapToEqualizer,
      Set.mem_setOf_eq, Subtype.mk.injEq, comp, ContinuousMap.mk.injEq] at h
    simp only [ContinuousMap.coyoneda, unop_op]
    ext x
    obtain ⟨y, hy⟩ := (hq Z B π).surjective x
    rw [← hy]
    exact congr_fun h y
  · simp only [ContinuousMap.coyoneda, comp, unop_op, Quiver.Hom.unop_op, Set.mem_setOf_eq,
      ContinuousMap.mk.injEq] at ha
    simp only [ContinuousMap.coyoneda, comp, unop_op, Quiver.Hom.unop_op, Set.coe_setOf,
      MapToEqualizer, Set.mem_setOf_eq, Subtype.mk.injEq]
    simp only [ContinuousMap.coyoneda, unop_op] at a
    refine ⟨(hq Z B π).lift a (factorsThrough_of_pullbackCondition X G ha), ?_⟩
    congr
    exact FunLike.ext'_iff.mp ((hq Z B π).lift_comp a (factorsThrough_of_pullbackCondition X G ha))

noncomputable
instance [h : PreservesFiniteProducts G.op] : PreservesFiniteProducts (coyoneda G X) := by
  rw [coyoneda_eq_comp]
  constructor
  intro J _
  have h' : PreservesFiniteProducts (coyoneda' X) := inferInstance
  have _ := h.1 J
  have _ := h'.1 J
  exact compPreservesLimitsOfShape _ _
