/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Points of a site

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
(This definition is essentially the definition of a fiber functor on a site
from SGA 4 IV 6.3.)

The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

Under certain assumptions, we show that if `A` is concrete and
`P ⟶ Q` is a locally bijective morphism between presheaves,
then the induced morphism on fibers is a bijection. It follows
that not only `Φ.sheafFiber : Sheaf J A ⥤ A` is the restriction of
`Φ.presheafFiber` but it may also be thought as a localization
of this functor with respect to the class of morphisms `J.W`.
In particular, the fiber of a presheaf identifies to the fiber of
its associated sheaf.

Under suitable assumptions on the target category `A`, we show that
both `Φ.presheafFiber` and `Φ.sheafFiber` commute with finite limits
and with arbitrary colimits.

-/

@[expose] public section

universe w' w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)`
consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements`
is initially small (which allows defining the fiber functor on presheaves by
taking colimits) and cofiltered (so that the fiber functor on presheaves is exact),
and such that covering sieves induce jointly surjective maps on fibers (which
allows to show that the fibers of a presheaf and its associated sheaf are isomorphic). -/
structure Point where
  /-- the fiber functor on the underlying category of the site -/
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

instance [LocallySmall.{w} C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

/-- The fiber functor on categories of presheaves that is given by a point of a site. -/
noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

/-- Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`, this
is the canonical map `P.obj (op X) ⟶ Φ.presheafFiber.obj P`. -/
noncomputable def toPresheafFiber (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.obj (op X) ⟶ Φ.presheafFiber.obj P :=
  colimit.ι ((CategoryOfElements.π Φ.fiber).op ⋙ P) (op ⟨X, x⟩)

@[ext]
lemma presheafFiber_hom_ext
    {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x P ≫ f =
      Φ.toPresheafFiber X x P ≫ g) : f = g :=
  colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

/-- Given a point `Φ` of a site `(C, J)`, `X : C` and `x : Φ.fiber.obj X`,
this is the map `P.obj (op X) ⟶ Φ.presheafFiber.obj P` for any `P : Cᵒᵖ ⥤ A`
as a natural transformation. -/
@[simps]
noncomputable def toPresheafFiberNatTrans (X : C) (x : Φ.fiber.obj X) :
    (evaluation Cᵒᵖ A).obj (op X) ⟶ Φ.presheafFiber where
  app := Φ.toPresheafFiber X x
  naturality _ _ f := by simp [presheafFiber, toPresheafFiber]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiber_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    P.map f.op ≫ Φ.toPresheafFiber X x P =
      Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  colimit.w ((CategoryOfElements.π Φ.fiber).op ⋙ P)
      (CategoryOfElements.homMk ⟨X, x⟩ ⟨Y, Φ.fiber.map f x⟩ f rfl).op

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiber_naturality {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (op X) ≫ Φ.toPresheafFiber X x Q :=
  ((Φ.toPresheafFiberNatTrans X x).naturality g).symm

section

variable {P : Cᵒᵖ ⥤ A} {T : A}
  (φ : ∀ (X : C) (_ : Φ.fiber.obj X), P.obj (op X) ⟶ T)
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : Φ.fiber.obj X),
    P.map f.op ≫ φ X x = φ Y (Φ.fiber.map f x) := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for morphisms from the fiber of a presheaf. -/
noncomputable def presheafFiberDesc :
    Φ.presheafFiber.obj P ⟶ T :=
  colimit.desc _ (Cocone.mk _ { app x := φ x.unop.1 x.unop.2 })

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x :=
  colimit.ι_desc _ _

end

variable {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC]

section

variable {P Q : Cᵒᵖ ⥤ A}

variable [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]

instance : PreservesColimitsOfShape Φ.fiber.Elementsᵒᵖ (forget A) :=
  Functor.Final.preservesColimitsOfShape_of_final (FinallySmall.fromFilteredFinalModel.{w} _) _

lemma toPresheafFiber_jointly_surjective (p : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z = p := by
  obtain ⟨⟨X, x⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p
  exact ⟨X, x, z, rfl⟩

lemma toPresheafFiber_jointly_surjective₂ (p₁ p₂ : ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))),
      Φ.toPresheafFiber X x P z₁ = p₁ ∧ Φ.toPresheafFiber X x P z₂ = p₂ := by
  obtain ⟨⟨X, x⟩, z₁, z₂, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) p₁ p₂
  exact ⟨X, x, z₁, z₂, rfl, rfl⟩

lemma toPresheafFiber_eq_iff' (X : C) (x : Φ.fiber.obj X) (z₁ z₂ : ToType (P.obj (op X))) :
    Φ.toPresheafFiber X x P z₁ = Φ.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  refine (Types.FilteredColimit.isColimit_eq_iff'
    (ht := isColimitOfPreserves (forget A)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ P))) ..).trans ?_
  constructor
  · rintro ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩
    exact ⟨Y, f, y, hf, hf'⟩
  · rintro ⟨Y, f, y, hf, hf'⟩
    exact ⟨⟨Y, y⟩, ⟨f, hf⟩, hf'⟩

variable (f : P ⟶ Q)

lemma toPresheafFiber_map_surjective [Presheaf.IsLocallySurjective J f] :
    Function.Surjective (Φ.presheafFiber.map f) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨Y, g, ⟨t, ht⟩, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.imageSieve_mem J f z) x
  exact ⟨Φ.toPresheafFiber Y y P t, by simp [← toPresheafFiber_w, ← ht]⟩

lemma toPresheafFiber_map_injective [Presheaf.IsLocallyInjective J f] :
    Function.Injective (Φ.presheafFiber.map f) := by
  suffices ∀ (X : C) (x : Φ.fiber.obj X) (p₁ p₂ : ToType (P.obj (op X)))
      (hp : f.app _ p₁ = f.app _ p₂), Φ.toPresheafFiber X x P p₁ = Φ.toPresheafFiber X x P p₂ by
    rintro q₁ q₂ h
    obtain ⟨X, x, p₁, p₂, rfl, rfl⟩ := Φ.toPresheafFiber_jointly_surjective₂ q₁ q₂
    simp only [toPresheafFiber_naturality_apply, toPresheafFiber_eq_iff'] at h
    obtain ⟨Y, g, y, rfl, h⟩ := h
    simp only [← NatTrans.naturality_apply] at h
    simpa using this _ y _ _ h
  intro X x p₁ p₂ h
  obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ (Presheaf.equalizerSieve_mem J f _ _ h) x
  simp_all [← toPresheafFiber_w_apply]

lemma toPresheafFiber_map_bijective
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f] :
    Function.Bijective (Φ.presheafFiber.map f) :=
  ⟨Φ.toPresheafFiber_map_injective f, Φ.toPresheafFiber_map_surjective f⟩

lemma W_isInvertedBy_presheafFiber
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P Q f hf
  obtain ⟨_, _⟩ := (J.W_iff_isLocallyBijective f).1 hf
  rw [← isIso_iff_of_reflects_iso _ (forget A), isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective f

end

/-- The fiber functor on the category of sheaves that is given a by a point of a site. -/
noncomputable abbrev sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

instance (P : Cᵒᵖ ⥤ A) [HasWeakSheafify J A]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J P)) :=
  W_isInvertedBy_presheafFiber _ _ (W_toSheafify J P)

variable (A) in
/-- The fiber functor on sheaves is obtained from the fiber functor on presheaves
by localization with respect to the class of morphisms `J.W`. -/
noncomputable def presheafToSheafCompSheafFiber [HasWeakSheafify J A]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C]
    [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms] :
    presheafToSheaf J A ⋙ Φ.sheafFiber ≅ Φ.presheafFiber :=
  (NatIso.ofComponents
    (fun P ↦ asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
      (by simp [← Functor.map_comp])).symm

instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.presheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _

instance [LocallySmall.{w} C] [HasFiniteLimits A] [AB5OfSize.{w, w} A] :
    PreservesFiniteLimits (Φ.sheafFiber (A := A)) :=
  comp_preservesFiniteLimits _ _

instance : PreservesColimitsOfSize.{w, w} (Φ.presheafFiber (A := A)) where
  preservesColimitsOfShape := by
    dsimp [presheafFiber]
    infer_instance

instance [HasSheafify J A] [J.WEqualsLocallyBijective A] [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)] [LocallySmall.{w} C] :
    PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) where
  preservesColimitsOfShape {K _} := ⟨fun {F} ↦
    preservesColimit_of_preserves_colimit_cocone
      (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _))
        (IsColimit.ofIsoColimit (isColimitOfPreserves Φ.presheafFiber
          (colimit.isColimit (F ⋙ sheafToPresheaf J A))) (by
            let G := colimit (F ⋙ sheafToPresheaf J A)
            let φ := CategoryTheory.toSheafify J G
            have : IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J G)) :=
              W_isInvertedBy_presheafFiber _ _ (W_toSheafify J _)
            refine Cocones.ext (asIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J G)))
              (fun k ↦ ?_)
            dsimp
            rw [← Functor.map_comp, Sheaf.sheafifyCocone_ι_app_val]
            dsimp))⟩

end Point

end GrothendieckTopology

end CategoryTheory
