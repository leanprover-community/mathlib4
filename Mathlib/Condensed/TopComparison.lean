/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Topology.Category.TopCat.Yoneda
import Mathlib.Condensed.Explicit

/-!

# The functor from topological spaces to condensed sets

This file builds on the API from the file `TopCat.Yoneda`. If the forgetful functor to `TopCat` has
nice properties, like preserving pullbacks and finite coproducts, then this Yoneda presheaf
satisfies the sheaf condition for the regular and extensive topologies respectively.

We apply this API to `CompHaus` and define the functor
`topCatToCondensedSet : TopCat.{u+1} ⥤ CondensedSet.{u}`.

-/

universe w w' v u

open CategoryTheory Opposite Limits regularTopology ContinuousMap

variable {C : Type u} [Category.{v} C] (G : C ⥤ TopCat.{w})
  (X : Type w') [TopologicalSpace X]

/--
An auxiliary lemma to that allows us to use `QuotientMap.lift` in the proof of
`equalizerCondition_yonedaPresheaf`.
-/
theorem factorsThrough_of_pullbackCondition {Z B : C} {π : Z ⟶ B} [HasPullback π π]
    [PreservesLimit (cospan π π) G]
    {a : C(G.obj Z, X)}
    (ha : a ∘ (G.map (pullback.fst _ _)) = a ∘ (G.map (pullback.snd π π))) :
    Function.FactorsThrough a (G.map π) := by
  intro x y hxy
  let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv <|
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : ∀ y, G.map (pullback.fst _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.fst (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_fst]; intro y; rfl
  have h₂ : ∀ y, G.map (pullback.snd _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.snd (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_snd]; intro y; rfl
  erw [h₁, h₂, TopCat.pullbackIsoProdSubtype_inv_fst_apply,
    TopCat.pullbackIsoProdSubtype_inv_snd_apply] at ha'
  simpa using ha'

/--
If `G` preserves the relevant pullbacks and every effective epi in `C` is a quotient map (which is
the case when `C` is `CompHaus` or `Profinite`), then `yonedaPresheaf` satisfies the equalizer
condition which is required to be a sheaf for the regular topology.
-/
theorem equalizerCondition_yonedaPresheaf
    [∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) G]
    (hq : ∀ (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], QuotientMap (G.map π)) :
      EqualizerCondition (yonedaPresheaf G X) := by
  apply EqualizerCondition.mk
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
    exact DFunLike.ext'_iff.mp ((hq Z B π).lift_comp a (factorsThrough_of_pullbackCondition G X ha))

/--
If `G` preserves finite coproducts (which is the case when `C` is `CompHaus`, `Profinite` or
`Stonean`), then `yonedaPresheaf` preserves finite products, which is required to be a sheaf for
the extensive topology.
-/
noncomputable instance [PreservesFiniteCoproducts G] :
    PreservesFiniteProducts (yonedaPresheaf G X) := by
  change PreservesFiniteProducts (G.op ⋙ yonedaPresheaf' X)
  have h' : PreservesFiniteProducts (yonedaPresheaf' X) := inferInstance
  have h : PreservesFiniteProducts G.op :=
    { preserves := fun J _ => by
        apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeOp
        exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _ }
  constructor
  intro J _
  have := h.1 J
  have := h'.1 J
  exact compPreservesLimitsOfShape _ _

/--
Associate to a `(u+1)`-small topological space the corresponding condensed set, given by
`yonedaPresheaf`.
-/
@[simps! val_obj val_map]
noncomputable def TopCat.toCondensedSet (X : TopCat.{u+1}) : CondensedSet.{u} :=
  @CondensedSet.ofSheafCompHaus (yonedaPresheaf.{u, u+1, u, u+1} compHausToTop.{u} X) _ (by
    apply (config := { allowSynthFailures := true }) equalizerCondition_yonedaPresheaf
      compHausToTop.{u} X
    intro Z B π he
    rw [((CompHaus.effectiveEpi_tfae π).out 0 2 :)] at he
    apply QuotientMap.of_surjective_continuous he π.continuous )


/--
`TopCat.toCondensedSet` yields a functor from `TopCat.{u+1}` to `CondensedSet.{u}`.
-/
@[simps]
noncomputable def topCatToCondensedSet : TopCat.{u+1} ⥤ CondensedSet.{u} where
  obj X := X.toCondensedSet
  map f := ⟨⟨fun _ g ↦ f.comp g, by aesop⟩⟩
