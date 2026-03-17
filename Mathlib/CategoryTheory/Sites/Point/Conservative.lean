/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Types.Epimorphisms

/-!
# Conservative families of points

Let `J` be a Grothendieck topology on a category `C`.
Let `P : ObjectProperty J.Point` be a family of points. We say that
`P` is a conservative family of points if the corresponding
fiber functors `Sheaf J (Type w) ⥤ Type w` jointly reflect
isomorphisms. Under suitable assumptions on the coefficient
category `A`, this implies that the fiber functors
`Sheaf J A ⥤ A` corresponding to the points in `P`
jointly reflect isomorphisms, epimorphisms and monomorphisms,
and they are also jointly faithful.

We provide a constructor `ObjectProperty.IsConservativeFamilyOfPoints.mk'`
which allows to verify that a family of points is conservative
using a condition involving covering sieves (SGA 4 IV 6.5 (a)).

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

namespace ObjectProperty

/-- Let `P : ObjectProperty J.Point` a family of points of a
site `(C, J)`). We say that it is a conservative family of points
if the corresponding fiber functors `Sheaf J (Type w) ⥤ Type w`
jointly reflect isomorphisms. -/
@[stacks 00YK "(1)"]
structure IsConservativeFamilyOfPoints : Prop where
  jointlyReflectIsomorphisms_type :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := Type w))

namespace IsConservativeFamilyOfPoints

variable {P} (hP : P.IsConservativeFamilyOfPoints)
  (A : Type u') [Category.{v'} A] [LocallySmall.{w} C]

section

variable
  [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [hJ : J.HasSheafCompose (forget A)]

include hP hJ in
@[stacks 00YK "(1)"]
lemma jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) where
  isIso {K L} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose J (forget A)),
      hP.jointlyReflectIsomorphisms_type.isIso_iff]
    exact fun Φ ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.sheafFiberCompIso (forget A))).app (Arrow.mk f))).2
          (inferInstanceAs (IsIso ((forget A).map (Φ.obj.sheafFiber.map f))))

include hP hJ in
@[stacks 00YL "(1)"]
lemma jointlyReflectMonomorphisms [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyReflectMonomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectMonomorphisms

include hP hJ in
@[stacks 00YL "(2)"]
lemma jointlyReflectEpimorphisms
    [HasWeakSheafify J A] [HasProducts.{w} A] :
    JointlyReflectEpimorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectEpimorphisms

include hP hJ in
@[stacks 00YL "(3)"]
lemma jointlyFaithful [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyFaithful

variable {A} in
include hP hJ in
lemma W_iff {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [HasWeakSheafify J A]
    [HasProducts.{w} A] :
    J.W f ↔ ∀ (Φ : P.FullSubcategory), IsIso (Φ.obj.presheafFiber.map f) := by
  rw [GrothendieckTopology.W_iff, (hP.jointlyReflectIsomorphisms A).isIso_iff]
  exact forall_congr'
    (fun Φ ↦ (MorphismProperty.isomorphisms A).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.presheafToSheafCompSheafFiberIso A)).app (Arrow.mk f)))

omit [(forget A).ReflectsIsomorphisms] hJ in
include hP in
variable {A} in
lemma jointly_reflect_isLocallySurjective
    [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
    {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)
    (hf : ∀ (Φ : P.FullSubcategory),
      Function.Surjective (Φ.obj.presheafFiber.map f)) :
    Presheaf.IsLocallySurjective J f := by
  simp only [← epi_iff_surjective] at hf
  rw [Presheaf.isLocallySurjective_iff_whisker_forget,
    ← Presheaf.isLocallySurjective_presheafToSheaf_map_iff,
    Sheaf.isLocallySurjective_iff_epi,
    (hP.jointlyReflectEpimorphisms (Type w)).epi_iff]
  exact fun Φ ↦ ((MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso
      ((Φ.obj.presheafFiberCompIso (forget A)).symm ≪≫
        Functor.isoWhiskerLeft _ (Φ.obj.presheafToSheafCompSheafFiberIso (Type w)).symm)).app
          (Arrow.mk f))).1 (hf Φ)

end

set_option backward.isDefEq.respectTransparency false in
lemma jointly_reflect_ofArrows_mem
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints)
    {X : C} {ι : Type*} [Small.{w} ι] {U : ι → C} (f : ∀ i, U i ⟶ X) :
    Sieve.ofArrows _ f ∈ J X ↔
      ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x := by
  refine ⟨fun hf Φ x ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨Z, _, ⟨_, p, _, ⟨i⟩, rfl⟩, z, rfl⟩ := Φ.obj.jointly_surjective _ hf x
    exact ⟨i, Φ.obj.fiber.map p z, by simp⟩
  · rw [J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map]
    refine hP.jointly_reflect_isLocallySurjective _ (fun Φ x ↦ ?_)
    obtain ⟨x, rfl⟩ := (Φ.obj.shrinkYonedaCompPresheafFiberIso.app X).toEquiv.symm.surjective x
    obtain ⟨i, y, rfl⟩ := hf Φ x
    refine ⟨Φ.obj.presheafFiber.map (Sigma.ι (fun i ↦ shrinkYoneda.{w}.obj (U i)) i)
      (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.app _ y), ?_⟩
    have := congr_fun (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.naturality (f i)) y
    dsimp at this ⊢
    rw [this, ← Sigma.ι_desc (fun i ↦ shrinkYoneda.{w}.map (f i)) i, Functor.map_comp]
    rfl

lemma jointly_reflect_ofArrows_mem_of_small
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints) [ObjectProperty.Small.{w} P]
    {X : C} {ι : Type*} {U : ι → C} (f : ∀ i, U i ⟶ X) :
    Sieve.ofArrows _ f ∈ J X ↔
      ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x := by
  refine ⟨fun hf Φ x ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨Z, _, ⟨_, p, _, ⟨i⟩, rfl⟩, z, rfl⟩ := Φ.obj.jointly_surjective _ hf x
    exact ⟨i, Φ.obj.fiber.map p z, by simp⟩
  · let ι' : Type _ := Σ (Φ : P.FullSubcategory), Φ.obj.fiber.obj X
    choose i y hy using fun (j : ι') ↦ hf j.1 j.2
    refine J.superset_covering (S := Sieve.ofArrows _ (fun i' ↦ f (i i'))) ?_ ?_
    · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      exact fun _ ↦ Sieve.ofArrows_mk _ _ _
    · rw [hP.jointly_reflect_ofArrows_mem]
      exact fun Φ x ↦ ⟨_, _, hy ⟨Φ, x⟩⟩

set_option backward.isDefEq.respectTransparency false in
private lemma mk'.isLocallySurjective
    (hP : ∀ ⦃X : C⦄ (S : Sieve X) (_ : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x),
        S ∈ J X)
    {F₁ F₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) [Mono f]
    (hf : ∀ (Φ : P.FullSubcategory), Function.Surjective (Φ.obj.presheafFiber.map f)) :
    Presheaf.IsLocallySurjective J f := by
  wlog hF₂ : ∃ (U : C), F₂ = shrinkYoneda.obj U generalizing F₁ F₂
  · refine ⟨fun {U} s ↦ ?_⟩
    let f' := pullback.snd f (shrinkYonedaEquiv.{w}.symm s)
    have hf' (Φ : P.FullSubcategory) :
        Function.Surjective (Φ.obj.presheafFiber.map f') := by
      replace hf := hf Φ
      rw [← CategoryTheory.epi_iff_surjective] at hf ⊢
      exact (MorphismProperty.epimorphisms _).of_isPullback
        ((IsPullback.of_hasPullback f (shrinkYonedaEquiv.{w}.symm s)).map
          Φ.obj.presheafFiber) (.infer_property _)
    have := this f' hf' ⟨_, rfl⟩
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J f' (shrinkYonedaObjObjEquiv.symm (𝟙 U)))
    rintro V g ⟨v, hv⟩
    refine ⟨(pullback.fst f (shrinkYonedaEquiv.{w}.symm s)).app _ v, ?_⟩
    refine (congr_fun (NatTrans.congr_app (pullback.condition (f := f)) (op V)) _).trans ?_
    dsimp at hv ⊢
    refine (congr_arg _ hv).trans ?_
    refine (congr_arg _ (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 _))).trans ?_
    simpa using shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm s g
  obtain ⟨U, rfl⟩ := hF₂
  suffices Presheaf.imageSieve f (shrinkYonedaObjObjEquiv.symm (𝟙 U)) ∈ J U from ⟨by
    intro V g
    obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
    replace this := J.pullback_stable g this
    rw [Presheaf.pullback_imageSieve] at this
    have hg := shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 _)
    simp only [Quiver.Hom.unop_op, Category.comp_id] at hg
    simpa [← hg]⟩
  refine hP _ (fun Φ u ↦ ?_)
  obtain ⟨x₁, hx₁⟩ := hf Φ (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.app _ u)
  obtain ⟨V, v, y, rfl⟩ := Φ.obj.toPresheafFiber_jointly_surjective (A := Type w) x₁
  obtain ⟨t, ht⟩ := shrinkYonedaObjObjEquiv.symm.surjective (f.app _ y)
  refine ⟨V, t, ⟨y, ht.symm.trans ?_⟩, v, ?_⟩
  · simpa using (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm t.op (𝟙 _)).symm
  · refine (Φ.obj.shrinkYonedaCompPresheafFiberIso.symm.app U).toEquiv.injective ?_
    dsimp
    trans (Φ.obj.toPresheafFiber V v (shrinkYoneda.{w}.obj U)) (shrinkYonedaObjObjEquiv.symm t)
    · rw [← Φ.obj.presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app]
      exact Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.naturality_apply t v
    · rw [← hx₁]
      refine Eq.trans (congr_arg _ ht)
        (Φ.obj.toPresheafFiber_naturality_apply f _ v y).symm

/- Let `P` be family of points of a site `(C, J)`, we show that `P` is a conservative
family of points if the following condition is satisfied (SGA 4 IV 6.5 (a)):
for any sieve `S : Sieve X`, if the family of maps `Φ.map.fiber.map f`
for all morphisms `f` in the sieve `S` is jointly surjective for any `Φ` in `P`,
then `S` is a covering sieve for `J`. -/
lemma mk' [HasSheafify J (Type w)]
    (hP : ∀ ⦃X : C⦄ (S : Sieve X) (_ : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x),
        S ∈ J X) :
    P.IsConservativeFamilyOfPoints where
  jointlyReflectIsomorphisms_type :=
    JointlyFaithful.jointlyReflectsIsomorphisms
      (JointlyFaithful.of_jointly_reflects_isIso_of_mono (fun _ _ f _ hf ↦ by
        have : Epi f := by
          rw [← Sheaf.isLocallySurjective_iff_epi]
          exact mk'.isLocallySurjective hP _
            (fun Φ ↦ ((isIso_iff_bijective _).1 (hf Φ)).2)
        exact Balanced.isIso_of_mono_of_epi f))

end IsConservativeFamilyOfPoints

end ObjectProperty

namespace GrothendieckTopology

/-- A site has enough points (relatively to a universe `w`)
if it has a `w`-small conservative family of points. -/
class HasEnoughPoints (J : GrothendieckTopology C) : Prop where
  exists_objectProperty (J) :
    ∃ (P : ObjectProperty (Point.{w} J)),
      ObjectProperty.Small.{w} P ∧ P.IsConservativeFamilyOfPoints

end GrothendieckTopology

end CategoryTheory
