/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.Basic
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.CompHausLike.SigmaComparison
public import Mathlib.Topology.FiberPartition
/-!

# The sheaf of locally constant maps on `CompHausLike P`

This file proves that under suitable conditions, the functor from the category of sets to the
category of sheaves for the coherent topology on `CompHausLike P`, given by mapping a set to the
sheaf of locally constant maps to it, is left adjoint to the "underlying set" functor (evaluation
at the point).

We apply this to prove that the constant sheaf functor into (light) condensed sets is isomorphic to
the functor of sheaves of locally constant maps described above.

## Proof sketch

The hard part of this adjunction is to define the counit. Its components are defined as follows:

Let `S : CompHausLike P` and let `Y` be a finite-product-preserving presheaf on `CompHausLike P`
(e.g. a sheaf for the coherent topology). We need to define a map `LocallyConstant S Y(*) ⟶ Y(S)`.
Given a locally constant map `f : S → Y(*)`, let `S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding
decomposition of `S` into the fibers. Let `yᵢ ∈ Y(*)` denote the value of `f` on `Sᵢ` and denote
by `gᵢ` the canonical map `Y(*) → Y(Sᵢ)`. Our map then takes `f` to the image of
`(g₁(y₁), ⋯, gₙ(yₙ))` under the isomorphism `Y(S₁) × ⋯ × Y(Sₙ) ≅ Y(S₁ ⊔ ⋯ ⊔ Sₙ) = Y(S)`.

Now we need to prove that the counit is natural in `S : CompHausLike P` and
`Y : Sheaf  (coherentTopology (CompHausLike P)) (Type _)`. There are two key lemmas in all
naturality proofs in this file (both lemmas are in the `CompHausLike.LocallyConstant` namespace):

* `presheaf_ext`: given `S`, `Y` and `f : LocallyConstant S Y(*)` like above, another presheaf
  `X`, and two elements `x y : X(S)`, to prove that `x = y` it suffices to prove that for every
  inclusion map `ιᵢ : Sᵢ ⟶ S`, `X(ιᵢ)(x) = X(ιᵢ)(y)`.
  Here it is important that we set everything up in such a way that the `Sᵢ` are literally subtypes
  of `S`.

* `incl_of_counitAppApp`: given  `S`, `Y` and `f : LocallyConstant S Y(*)` like above, we have
  `Y(ιᵢ)(ε_{S, Y}(f)) = gᵢ(yᵢ)` where `ε` denotes the counit and the other notation is like above.

## Main definitions

* `CompHausLike.LocallyConstant.functor`: the functor from the category of sets to the category of
  sheaves for the coherent topology on `CompHausLike P`, which takes a set `X` to
  `LocallyConstant - X`
  - `CondensedSet.LocallyConstant.functor` is the above functor in the case of condensed sets.
  - `LightCondSet.LocallyConstant.functor` is the above functor in the case of light condensed sets.

* `CompHausLike.LocallyConstant.adjunction`: the functor described above is left adjoint to the
  "underlying set" functor `(sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩`, which takes
  a sheaf `X` to the set `X(*)`.

* `CondensedSet.LocallyConstant.iso`: the functor `CondensedSet.LocallyConstant.functor` is
  isomorphic to the functor `Condensed.discrete (Type _)` (the constant sheaf functor from sets to
  condensed sets).

* `LightCondSet.LocallyConstant.iso`: the functor `LightCondSet.LocallyConstant.functor` is
  isomorphic to the functor `LightCondensed.discrete (Type _)` (the constant sheaf functor from sets
  to light condensed sets).

-/

@[expose] public section

universe u w

open CategoryTheory Limits LocallyConstant TopologicalSpace.Fiber Opposite Function Fiber

variable {P : TopCat.{u} → Prop}

namespace CompHausLike.LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHausLike P` given by locally constant
maps.
-/
@[simps obj_obj obj_map map_app]
def functorToPresheaves : Type (max u w) ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) where
  obj X := {
    obj := fun ⟨S⟩ ↦ (LocallyConstant S X)
    map f := TypeCat.ofHom (fun g ↦ g.comap f.unop.hom.hom) }
  map f := { app _ := TypeCat.ofHom (fun t ↦ t.map f) }

/--
Locally constant maps are the same as continuous maps when the target is equipped with the discrete
topology
-/
@[simps]
def locallyConstantIsoContinuousMap (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := TypeCat.ofHom fun f ↦ (f : C(Y, X))
    inv := TypeCat.ofHom fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

section Adjunction

variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]

section

variable {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : Fiber r)

/-- A fiber of a locally constant map as a `CompHausLike P`. -/
abbrev fiber : CompHausLike.{u} P := CompHausLike.of P a.val

/-- The inclusion map from a component of the coproduct induced by `f` into `S`. -/
def sigmaIncl : fiber r a ⟶ Q := ofHom _ (TopologicalSpace.Fiber.sigmaIncl _ a)

/-- The canonical map from the coproduct induced by `f` to `S` as an isomorphism in
`CompHausLike P`. -/
noncomputable def sigmaIso [HasExplicitFiniteCoproducts.{u} P] : (finiteCoproduct (fiber r)) ≅ Q :=
  isoOfBijective (ofHom _ (sigmaIsoHom r)) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩

lemma sigmaComparison_comp_sigmaIso [HasExplicitFiniteCoproducts.{u} P]
    (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) :
    (X.mapIso (sigmaIso r).op).hom ≫ sigmaComparison X (fun a ↦ (fiber r a).1) ≫
      TypeCat.ofHom (fun g ↦ g a) = X.map (sigmaIncl r a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, sigmaComparison, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
    ← X.map_comp_apply]
  rfl

end

variable {S : CompHausLike.{u} P} {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)}
  [HasProp P PUnit.{u + 1}] (f : LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))))

/-- The projection of the counit. -/
noncomputable def counitAppAppImage : (a : Fiber f) → Y.obj ⟨fiber f a⟩ :=
  fun a ↦ Y.map (CompHausLike.isTerminalPUnit.from _).op a.image

/--
The counit is defined as follows: given a locally constant map `f : S → Y(*)`, let
`S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding decomposition of `S` into the fibers. We need to provide an
element of `Y(S)`. It suffices to provide an element of `Y(Sᵢ)` for all `i`. Let `yᵢ ∈ Y(*)` denote
the value of `f` on `Sᵢ`. Our desired element is the image of `yᵢ` under the canonical map
`Y(*) → Y(Sᵢ)`.
-/
noncomputable def counitAppApp (S : CompHausLike.{u} P)
    (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w))
    [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P] :
    LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))) ⟶ Y.obj ⟨S⟩ :=
  TypeCat.ofHom fun r ↦ (inv (sigmaComparison Y (fun a ↦ (fiber r a).1)) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)

-- This is the key lemma to prove naturality of the counit:
/--
To check equality of two elements of `X(S)`, it suffices to check equality after composing with
each `X(S) → X(Sᵢ)`.
-/
lemma presheaf_ext (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w))
    [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩)
    [HasExplicitFiniteCoproducts.{u} P]
    (h : ∀ (a : Fiber f), X.map (sigmaIncl f a).op x = X.map (sigmaIncl f a).op y) : x = y := by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a ↦ (fiber f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

lemma incl_of_counitAppApp [PreservesFiniteProducts Y] [HasExplicitFiniteCoproducts.{u} P]
    (a : Fiber f) : Y.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  rw [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, Iso.inv_hom_id,
    Functor.map_id_apply]
  exact congrFun (Iso.inv_hom_id_apply (asIso (sigmaComparison Y (fun a ↦ (fiber f a).1)))
    (counitAppAppImage f)) _

variable {T : CompHausLike.{u} P} (g : T ⟶ S)

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `incl_comap` works.
-/
noncomputable def componentHom (a : Fiber (f.comap g.hom.hom)) :
    fiber _ a ⟶ fiber _ (Fiber.mk f (g a.preimage)) :=
  ConcreteCategory.ofHom
  { toFun x := ⟨g x.val, by
      simp only [Fiber.mk, Set.mem_preimage, Set.mem_singleton_iff]
      convert map_eq_image _ _ x
      exact map_preimage_eq_image_map _ _ a⟩
    continuous_toFun := by
      -- term mode gives "unknown free variable" error.
      exact Continuous.subtype_mk (by fun_prop) _ }

lemma incl_comap {S T : (CompHausLike P)ᵒᵖ}
    (f : LocallyConstant S.unop (Y.obj (op (CompHausLike.of P PUnit.{u + 1}))))
      (g : S ⟶ T) (a : Fiber (f.comap g.unop.hom.hom)) :
        g ≫ (sigmaIncl (f.comap g.unop.hom.hom) a).op =
          (sigmaIncl f _).op ≫ (componentHom f g.unop a).op :=
  rfl

/-- The counit is natural in `S : CompHausLike P` -/
@[simps! app]
noncomputable def counitApp [HasExplicitFiniteCoproducts.{u} P]
    (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts Y] :
    (functorToPresheaves.obj (Y.obj (op (CompHausLike.of P PUnit.{u + 1})))) ⟶ Y where
  app := fun ⟨S⟩ ↦ counitAppApp S Y
  naturality := by
    intro S T g
    ext f
    apply presheaf_ext (f.comap g.unop.hom.hom)
    intro a
    simp only [op_unop, functorToPresheaves_obj_obj, functorToPresheaves_obj_map,
      TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rw [incl_of_counitAppApp, ← Functor.map_comp_apply, incl_comap,
      Functor.map_comp_apply, incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    apply congrArg
    exact image_eq_image_mk (g := g.unop) (a := a)

variable (P) (X : TopCat.{max u w})
    [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
noncomputable def functorToPresheavesIso (X : Type (max u w)) :
    functorToPresheaves.{u, w}.obj X ≅ ((TopCat.discrete.obj X).toSheafCompHausLike P hs).obj :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

/-- `CompHausLike.LocallyConstant.functorToPresheaves` lands in sheaves. -/
@[simps! obj_obj_obj obj_obj_map map_hom_app]
def functor :
    haveI := CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) :=
  ObjectProperty.lift _ (functorToPresheaves.{u, w}) (fun X ↦ by
    rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIso P hs X)]
    exact ((TopCat.discrete.obj X).toSheafCompHausLike P hs).property)

@[deprecated (since := "2026-03-20")] alias functor_obj_obj := functor_obj_obj_obj
@[deprecated (since := "2026-03-20")] alias functor_map_hom := functor_map_hom_app

/--
`CompHausLike.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToSheafCompHausLike` to discrete topological spaces.
-/
noncomputable def functorIso :
    functor.{u, w} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))

set_option backward.isDefEq.respectTransparency false in
/-- The counit is natural in both `S : CompHausLike P` and
`Y : Sheaf (coherentTopology (CompHausLike P)) (Type (max u w))` -/
@[simps!]
noncomputable def counit [HasExplicitFiniteCoproducts.{u} P] : haveI := CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X := haveI := CompHausLike.preregular hs
    (ObjectProperty.homMk) (counitApp X.obj)
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply InducedCategory.hom_ext
    simp only [functor, Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
      ObjectProperty.lift_obj_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      ObjectProperty.ι_map, ObjectProperty.lift_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [NatTrans.comp_app, counitApp_app, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply]
    apply presheaf_ext (f.map (g.hom.app (op (CompHausLike.of P PUnit.{u + 1}))))
    intro a
    simp only [functorToPresheaves_obj_obj, functorToPresheaves_map_app, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, dsimp% incl_of_counitAppApp]
    apply presheaf_ext (f.comap (sigmaIncl _ _).hom.hom)
    intro b
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp,
      map_apply, IsTerminal.comp_from, ← map_preimage_eq_image_map]
    change (_ ≫ Y.obj.map _) _ = (_ ≫ Y.obj.map _) _
    simp only [← g.hom.naturality]
    rw [show sigmaIncl (f.comap (sigmaIncl (f.map _) a).hom.hom) b ≫ sigmaIncl (f.map _) a =
        CompHausLike.ofHom P (X := fiber _ b) (sigmaInclIncl f _ a b) ≫ sigmaIncl f (Fiber.mk f _)
      by ext; rfl]
    simp only [op_comp, Functor.map_comp, types_comp_apply, dsimp% incl_of_counitAppApp]
    simp only [counitAppAppImage, ← Functor.map_comp_apply, ← op_comp]
    rw [mk_image]
    change (X.obj.map _ ≫ _) _ = (X.obj.map _ ≫ _) _
    simp only [g.hom.naturality]
    simp only [types_comp_apply]
    have := map_preimage_eq_image (f := g.hom.app _ ∘ f) (a := a)
    simp only [Function.comp_apply] at this
    rw [this]
    apply congrArg
    symm
    convert (b.preimage).prop
    exact (mem_iff_eq_image (g.hom.app _ ∘ f) _ _).symm

/--
The unit of the adjunction is given by mapping each element to the corresponding constant map.
-/
@[simps]
def unit : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  app _ := TypeCat.ofHom (fun x ↦ LocallyConstant.const _ x)

/-- The unit of the adjunction is an iso. -/
noncomputable def unitIso : 𝟭 (Type (max u w)) ≅ functor.{u, w} P hs ⋙
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  hom := unit P hs
  inv := { app _ := TypeCat.ofHom (fun f ↦ f.toFun PUnit.unit) }

lemma adjunction_left_triangle [HasExplicitFiniteCoproducts.{u} P]
    (X : Type (max u w)) : functorToPresheaves.{u, w}.map ((unit P hs).app X) ≫
      ((counit P hs).app ((functor P hs).obj X)).hom = 𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, functor_obj_obj_obj, functorToPresheaves_obj_obj, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj, unit_app, NatTrans.comp_app,
    functorToPresheaves_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.toFun_apply,
    CategoryTheory.comp_apply, TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply]
  simp only [counit]
  have := CompHausLike.preregular hs
  apply presheaf_ext
    (X := ((functor P hs).obj X).obj) (Y := ((functor.{u, w} P hs).obj X).obj)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj,
    ObjectProperty.ι_obj, unit_app, counitAppAppImage, functor_obj_obj_map,
    Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom]
  ext x
  erw [← map_eq_image _ a x]
  rfl

/--
`CompHausLike.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
@[simps]
noncomputable def adjunction [HasExplicitFiniteCoproducts.{u} P] :
    functor.{u, w} P hs ⊣ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u + 1}⟩ where
  unit := unit P hs
  counit := counit P hs
  left_triangle_components := by
    intro X
    ext : 1
    exact adjunction_left_triangle P hs X
  right_triangle_components X := by
    ext (x : X.obj.obj _)
    dsimp
    have := CompHausLike.preregular hs
    letI : PreservesFiniteProducts ((sheafToPresheaf (coherentTopology _) _).obj X) :=
      inferInstanceAs (PreservesFiniteProducts X.obj)
    apply presheaf_ext ((unit P hs).app _ x)
    intro a
    erw [incl_of_counitAppApp]
    simp only [unit_app, counitAppAppImage]
    erw [← map_eq_image _ a ⟨PUnit.unit, by simp [mem_iff_eq_image, ← map_preimage_eq_image]⟩]
    rfl

instance [HasExplicitFiniteCoproducts.{u} P] : IsIso (adjunction P hs).unit :=
  inferInstanceAs (IsIso (unitIso P hs).hom)

end Adjunction

end CompHausLike.LocallyConstant

section Condensed

open Condensed CompHausLike

namespace CondensedSet.LocallyConstant

/-- The functor from sets to condensed sets given by locally constant maps into the set. -/
abbrev functor : Type (u + 1) ⥤ CondensedSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u + 1} (P := fun _ ↦ True)
    (hs := fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
`CondensedSet.LocallyConstant.functor` is isomorphic to `Condensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def iso : functor ≅ discrete (Type (u + 1)) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

/-- `CondensedSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def functorFullyFaithful : functor.FullyFaithful :=
  (LocallyConstant.adjunction.{u, u + 1} _ _).fullyFaithfulLOfIsIsoUnit

noncomputable instance : functor.Faithful := functorFullyFaithful.faithful

noncomputable instance : functor.Full := functorFullyFaithful.full

instance : (discrete <| Type _).Faithful := Functor.Faithful.of_iso iso

noncomputable instance : (discrete <| Type _).Full := Functor.Full.of_iso iso

end CondensedSet.LocallyConstant

namespace LightCondSet.LocallyConstant

/-- The functor from sets to light condensed sets given by locally constant maps into the set. -/
abbrev functor : Type u ⥤ LightCondSet.{u} :=
  CompHausLike.LocallyConstant.functor.{u, u}
    (P := fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

instance (S : LightProfinite.{u}) (p : S → Prop) :
    HasProp (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X) (Subtype p) :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace (Subtype p)),
    (inferInstance : SecondCountableTopology {s | p s})⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is isomorphic to `LightCondensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def iso : functor ≅ LightCondensed.discrete (Type u) :=
  (LocallyConstant.adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

/-- `LightCondSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def functorFullyFaithful : functor.{u}.FullyFaithful :=
  (LocallyConstant.adjunction _ _).fullyFaithfulLOfIsIsoUnit

instance : functor.{u}.Faithful := functorFullyFaithful.faithful

instance : LightCondSet.LocallyConstant.functor.Full := functorFullyFaithful.full

instance : (LightCondensed.discrete <| Type u).Faithful := Functor.Faithful.of_iso iso.{u}

instance : (LightCondensed.discrete <| Type u).Full := Functor.Full.of_iso iso.{u}

end LightCondSet.LocallyConstant

end Condensed
