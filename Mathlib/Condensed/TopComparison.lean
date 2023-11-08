/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Condensed.Explicit

/-!

# The functor from topological spaces to condensed sets

This file develops some API for "topologically concrete" categories, defining universe polymorphic
"Yoneda presheaves" on such categories. If the forgetful functor to `TopCat` has nice properties,
like preserving pullbacks and finite coproducts, then this Yoneda presheaf satisfies the sheaf
condition for the regular and extensive topologies respectively.

We then apply this API to `CompHaus` and define the functor
`topCatToCondensed : TopCat.{u+1} ⥤ CondensedSet.{u}`.
-/

universe w w' v u

open CategoryTheory Opposite Limits

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) (Y : Type w') [TopologicalSpace Y]
-- `C` is meant to be `CompHaus`, `Profinite` or `Stonean`.

namespace ContinuousMap

/--
A universe polymorphic "Yoneda presheaf" on `C` given by continuous maps into a topoological space
`Y`.
-/
def yonedaPresheaf : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f g := ContinuousMap.comp g (F.map f.unop)

/--
A universe polymorphic Yoneda presheaf on `TopCat` given by continuous maps into a topoological
space `Y`.
-/
def yonedaPresheaf' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  obj X := C((unop X).1, Y)
  map f g := ContinuousMap.comp g f.unop

theorem piComparison_fac {α : Type} (X : α → TopCat) :
    piComparison (yonedaPresheaf'.{w, w'} Y) (fun x ↦ op (X x)) =
    (yonedaPresheaf' Y).map ((opCoproductIsoProduct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫
    (equivEquivIso (sigmaEquiv Y (fun x ↦ (X x).1))).inv ≫ (Types.productIso _).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  ext
  simp only [yonedaPresheaf', unop_op, piComparison, types_comp_apply,
    Types.productIso_hom_comp_eval_apply, Types.pi_lift_π_apply, comp_apply, TopCat.coe_of,
    unop_comp, Quiver.Hom.unop_op, sigmaEquiv, equivEquivIso_hom, Equiv.toIso_inv,
    Equiv.coe_fn_symm_mk, comp_assoc, sigmaMk_apply, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

/-- The universe polymorphic Yoneda presheaf on `TopCat` preserves finite products. -/
noncomputable instance : PreservesFiniteProducts (yonedaPresheaf'.{w, w'} Y) where
  preserves J _ := {
    preservesLimit := fun {K} =>
      have : ∀ {α : Type} (X : α → TopCat), PreservesLimit (Discrete.functor (fun x ↦ op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.ofIsoComparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x ↦ op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i ↦ op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimitOfIsoDiagram _ i.symm }

end ContinuousMap

open ContinuousMap

variable (G : C ⥤ TopCat.{v}) (X : (Type (max u v))) [TopologicalSpace X]

/--
An auxiliary lemma to that allows us to use `QuotientMap.lift` in the proof of
`equalizerCondition_yonedaPresheaf`.
-/
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

/--
If `G` preserves the relevant pullbacks and every effective epi in `C` is a quotient map (which is
the case when `C` is `CompHaus` or `Profinite`), then `yonedaPresheaf` satisfies the equalizer
condition which is required to be a sheaf for the regular topology.
-/
theorem equalizerCondition_yonedaPresheaf
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) G]
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], QuotientMap (G.map π)) :
      EqualizerCondition.{v, u} (yonedaPresheaf G X) := by
  intro Z B π _ _
  refine ⟨fun a b h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · simp only [yonedaPresheaf, unop_op, Quiver.Hom.unop_op, Set.coe_setOf, MapToEqualizer,
      Set.mem_setOf_eq, Subtype.mk.injEq, comp, ContinuousMap.mk.injEq] at h
    simp only [yonedaPresheaf, unop_op]
    ext x
    obtain ⟨y, hy⟩ := (hq Z B π).surjective x
    rw [← hy]
    exact congr_fun h y
  · simp only [yonedaPresheaf, comp, unop_op, Quiver.Hom.unop_op, Set.mem_setOf_eq,
      ContinuousMap.mk.injEq] at ha
    simp only [yonedaPresheaf, comp, unop_op, Quiver.Hom.unop_op, Set.coe_setOf,
      MapToEqualizer, Set.mem_setOf_eq, Subtype.mk.injEq]
    simp only [yonedaPresheaf, unop_op] at a
    refine ⟨(hq Z B π).lift a (factorsThrough_of_pullbackCondition G X ha), ?_⟩
    congr
    exact FunLike.ext'_iff.mp ((hq Z B π).lift_comp a (factorsThrough_of_pullbackCondition G X ha))

/--
If `G` preserves finite coproducts (which is the case when `C` is `CompHaus`, `Profinite` or
`Stonean`), then `yonedaPresheaf` preserves finite products, which is required to be a sheaf for
the extensive topology.
-/
noncomputable instance [PreservesFiniteCoproducts G] :
    PreservesFiniteProducts (yonedaPresheaf G X) := by
  change PreservesFiniteProducts (G.op ⋙ yonedaPresheaf' X)
  have h' : PreservesFiniteProducts (yonedaPresheaf' X) := inferInstance
  have h : PreservesFiniteProducts G.op := {
    preserves := fun J _ => by
      apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeOp
      exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _ }
  constructor
  intro J _
  have _ := h.1 J
  have _ := h'.1 J
  exact compPreservesLimitsOfShape _ _

/--
Associate to a `(u+1)`-small topological space the corresponding condensed set, given by
`yonedaPresheaf`.
-/
noncomputable def TopCat.toCondensed (X : TopCat.{u+1}) : CondensedSet.{u} :=
  @Condensed.ofSheafCompHaus (yonedaPresheaf.{u, u+1, u, u+1} compHausToTop.{u} X) _ (by
    apply (config := { allowSynthFailures := true }) equalizerCondition_yonedaPresheaf compHausToTop.{u} X
    intro Z B π he
    rw [CompHaus.effectiveEpi_iff_surjective] at he
    apply QuotientMap.of_surjective_continuous he π.continuous )

/--
`TopCat.toCondensed` yields a functor from `TopCat.{u+1}` to `CondensedSet.{u}`.
-/
noncomputable def topCatToCondensed : TopCat.{u+1} ⥤ CondensedSet.{u} where
  obj X := X.toCondensed
  map f := ⟨⟨fun _ g ↦ f.comp g, by aesop⟩⟩

theorem topCatToCondensed_obj (X : TopCat.{u+1}) (S : CompHaus.{u}) :
    (topCatToCondensed.obj X).val.obj (op S) = C(S, X) := rfl

theorem topCatToCondensed_map {X Y : TopCat.{u+1}} {S : CompHaus.{u}} (g : C(S, X)) (f : X ⟶ Y) :
    (topCatToCondensed.map f).val.app (op S) g = f.comp g := rfl
