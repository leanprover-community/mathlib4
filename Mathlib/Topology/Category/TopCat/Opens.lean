/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Sets.Opens

/-!
# The category of open sets in a topological space.

We define `toTopCat : Opens X ⥤ TopCat` and
`map (f : X ⟶ Y) : Opens Y ⥤ Opens X`, given by taking preimages of open sets.

Unfortunately `Opens` isn't (usefully) a functor `TopCat ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `Eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`mapId : map (𝟙 X) ≅ 𝟭 (Opens X)` and
`mapComp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/

@[expose] public section


open CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace TopologicalSpace.Opens

variable {X Y Z : TopCat.{u}} {U V W : Opens X}

/-!
Since `Opens X` has a partial order, it automatically receives a `Category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ULift (PLift (U ≤ V))`.
-/

instance opensHom.instFunLike : FunLike (U ⟶ V) U V where
  coe f := Set.inclusion f.le
  coe_injective' := by rintro ⟨⟨_⟩⟩ _ _; congr!

lemma apply_def (f : U ⟶ V) (x : U) : f x = ⟨x, f.le x.2⟩ := rfl

@[simp] lemma apply_mk (f : U ⟶ V) (x : X) (hx) : f ⟨x, hx⟩ = ⟨x, f.le hx⟩ := rfl

@[simp] lemma val_apply (f : U ⟶ V) (x : U) : (f x : X) = x := rfl

@[simp, norm_cast] lemma coe_id (f : U ⟶ U) : ⇑f = id := rfl

lemma id_apply (f : U ⟶ U) (x : U) : f x = x := rfl

@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U) : (f ≫ g) x = g (f x) := rfl

/-!
We now construct as morphisms various inclusions of open sets.
-/


-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...
/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def infLELeft (U V : Opens X) : U ⊓ V ⟶ U :=
  inf_le_left.hom

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
noncomputable def infLERight (U V : Opens X) : U ⊓ V ⟶ V :=
  inf_le_right.hom

/-- The inclusion `U i ⟶ iSup U` as a morphism in the category of open sets.
-/
noncomputable def leSupr {ι : Type*} (U : ι → Opens X) (i : ι) : U i ⟶ iSup U :=
  (le_iSup U i).hom

/-- The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def botLE (U : Opens X) : ⊥ ⟶ U :=
  bot_le.hom

/-- The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
noncomputable def leTop (U : Opens X) : U ⟶ ⊤ :=
  le_top.hom

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `SheafOfFunctions`.
theorem infLELeft_apply (U V : Opens X) (x) :
    (infLELeft U V) x = ⟨x.1, (@inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
  rfl

@[simp]
theorem infLELeft_apply_mk (U V : Opens X) (x) (m) :
    (infLELeft U V) ⟨x, m⟩ = ⟨x, (@inf_le_left _ _ U V : _ ≤ _) m⟩ :=
  rfl

@[simp]
theorem leSupr_apply_mk {ι : Type*} (U : ι → Opens X) (i : ι) (x) (m) :
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_iSup U i :) m⟩ :=
  rfl

/-- The functor from open sets in `X` to `TopCat`,
realising each open set as a topological space itself.
-/
def toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where
  obj U := TopCat.of U
  map i := TopCat.ofHom ⟨fun x ↦ ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an open subset to the whole space, as a morphism in `TopCat`.
-/
@[simps! -fullyApplied]
def inclusion' {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X :=
  TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]
theorem coe_inclusion' {X : TopCat} {U : Opens X} :
    (inclusion' U : U → X) = Subtype.val := rfl

theorem isOpenEmbedding {X : TopCat.{u}} (U : Opens X) : IsOpenEmbedding (inclusion' U) :=
  U.2.isOpenEmbedding_subtypeVal

/-- The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

/-- `Opens.map f` gives the functor from open sets in Y to open set in X,
given by taking preimages under f. -/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X where
  obj U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.hom.continuous⟩
  map i := ⟨⟨fun _ h => i.le h⟩⟩

@[simp]
theorem map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl

@[simp]
theorem mem_map {f : X ⟶ Y} {U : Opens Y} {x : X} :
    x ∈ (map f).obj U ↔ f.hom x ∈ U := .rfl

@[simp]
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩ :=
  rfl

@[simp]
lemma map_homOfLE (f : X ⟶ Y) {U V : Opens Y} (e : U ≤ V) :
    (TopologicalSpace.Opens.map f).map (homOfLE e) =
      homOfLE (show (Opens.map f).obj U ≤ (Opens.map f).obj V from fun _ hx ↦ e hx) :=
  rfl

@[simp]
theorem map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl

@[simp]
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U := by
  simp

theorem op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by simp

@[simp]
lemma map_top (f : X ⟶ Y) : (Opens.map f).obj ⊤ = ⊤ := rfl

/-- The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
noncomputable def leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤ :=
  leTop U

@[simp]
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl

@[simp]
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
    (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl

@[simp]
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) :
    (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl

@[simp]
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl

@[simp]
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl

theorem map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι → Opens Y) :
    (map f).obj (iSup U) = iSup ((map f).obj ∘ U) := by
  ext
  simp

section

variable (X)

/-- The functor `Opens X ⥤ Opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where
  hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

theorem map_id_eq : map (𝟙 X) = 𝟭 (Opens X) := by
  rfl

end

/-- The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where
  hom := { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }

theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
/-- If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `Opens Y ⥤ Opens X` they induce are isomorphic.
-/
def mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])

theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g := by
  subst h
  rfl

@[simp]
theorem mapIso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _) :=
  rfl

@[simp]
theorem mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).hom.app U = eqToHom (by rw [h]) :=
  rfl

@[simp]
theorem mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).inv.app U = eqToHom (by rw [h]) :=
  rfl

/-- A homeomorphism of spaces gives an equivalence of categories of open sets. -/
@[simps! unitIso counitIso]
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X :=
  (TopCat.homeoOfIso H).opensCongr.equivalence.symm

@[simp]
lemma mapMapIso_functor {X Y : TopCat} (H : X ≅ Y) :
    (mapMapIso H).functor = map H.hom := rfl

@[simp]
lemma mapMapIso_inverse {X Y : TopCat} (H : X ≅ Y) :
    (mapMapIso H).inverse = map H.inv := rfl

end TopologicalSpace.Opens

/-- If `f : X ⟶ Y` is a map of topological spaces and `U ⊆ V` are open subsets of `X` whose
images are open, this is the morphism `f'' U ⟶ f'' Y` in `Opens Y`. Useful for applications
to presheaves when we don't want to suppose that `f` is an open map.
-/
def IsOpenMap.functorMap {X Y : TopCat.{u}} {f : X ⟶ Y} {U V : Opens X}
     (HU : IsOpen (f '' U)) (HV : IsOpen (f '' V)) (le : U ≤ V) :
     (⟨_, HU⟩ : Opens Y) ⟶ ⟨_, HV⟩ := ⟨⟨Set.image_mono le⟩⟩

/-- An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
@[simps obj_coe]
def IsOpenMap.functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map {U V} h := IsOpenMap.functorMap (hf _ U.2) (hf _ V.2) h.down.down

/-- An open map `f : X ⟶ Y` induces an adjunction between `Opens X` and `Opens Y`.
-/
def IsOpenMap.adjunction {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor ⊣ Opens.map f where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

instance IsOpenMap.functorFullOfMono {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) [H : Mono f] :
    hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

instance IsOpenMap.functor_faithful {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.Faithful where

/-- An open embedding `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
We define `IsOpenEmbedding.functor` as `IsOpenEmbedding.isOpenMap.functor`, so it won't
default to `IsInducing.functor` (which is equal but not defeq).
-/
abbrev Topology.IsOpenEmbedding.functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenEmbedding f) :=
    hf.isOpenMap.functor

lemma Topology.IsOpenEmbedding.functor_obj_injective {X Y : TopCat} {f : X ⟶ Y}
    (hf : IsOpenEmbedding f) : Function.Injective hf.functor.obj :=
  fun _ _ e ↦ Opens.ext (Set.image_injective.mpr hf.injective (congr_arg (↑· : Opens Y → Set Y) e))

namespace Topology.IsInducing

/-- Given an inducing map `X ⟶ Y` and some `U : Opens X`, this is the union of all open sets
whose preimage is `U`. This is right adjoint to `Opens.map`. -/
@[nolint unusedArguments]
def functorObj {X Y : TopCat} {f : X ⟶ Y} (_ : IsInducing f) (U : Opens X) : Opens Y :=
  sSup { s : Opens Y | (Opens.map f).obj s = U }

lemma map_functorObj {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f)
    (U : Opens X) :
    (Opens.map f).obj (hf.functorObj U) = U := by
  apply le_antisymm
  · rintro x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x ∈ s⟩; exact hx
  · intro x hx
    obtain ⟨U, hU⟩ := U
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
    exact Opens.mem_sSup.mpr ⟨⟨_, ht⟩, rfl, hx⟩

lemma mem_functorObj_iff {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f) (U : Opens X)
    {x : X} : f x ∈ hf.functorObj U ↔ x ∈ U := by
  conv_rhs => rw [← hf.map_functorObj U]
  rfl

lemma le_functorObj_iff {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f) {U : Opens X}
    {V : Opens Y} : V ≤ hf.functorObj U ↔ (Opens.map f).obj V ≤ U := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.mp hU
  constructor
  · exact fun i x hx ↦ (hf.mem_functorObj_iff ((Opens.map f).obj ⟨t, ht⟩)).mp (i hx)
  · intro h x hx
    refine Opens.mem_sSup.mpr ⟨⟨_, V.2.union ht⟩, Opens.ext ?_, Set.mem_union_left t hx⟩
    dsimp
    rwa [Set.union_eq_right]

/-- An inducing map `f : X ⟶ Y` induces a Galois insertion between `Opens Y` and `Opens X`. -/
def opensGI {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f) :
    GaloisInsertion (Opens.map f).obj hf.functorObj :=
  ⟨_, fun _ _ ↦ hf.le_functorObj_iff.symm, fun U ↦ (hf.map_functorObj U).ge, fun _ _ ↦ rfl⟩

/-- An inducing map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`. -/
@[simps]
def functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens X ⥤ Opens Y where
  obj := hf.functorObj
  map {U V} h := homOfLE (hf.le_functorObj_iff.mpr ((hf.map_functorObj U).trans_le h.le))

/-- An inducing map `f : X ⟶ Y` induces an adjunction between `Opens Y` and `Opens X`. -/
def adjunction {X Y : TopCat} {f : X ⟶ Y} (hf : IsInducing f) :
    Opens.map f ⊣ hf.functor :=
  hf.opensGI.gc.adjunction

end Topology.IsInducing

namespace TopologicalSpace.Opens

open TopologicalSpace

@[simp]
theorem isOpenEmbedding_obj_top {X : TopCat} (U : Opens X) :
    U.isOpenEmbedding.functor.obj ⊤ = U := by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]
theorem inclusion'_map_eq_top {X : TopCat} (U : Opens X) : (Opens.map U.inclusion').obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
theorem adjunction_counit_app_self {X : TopCat} (U : Opens X) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app U = eqToHom (by simp) := Subsingleton.elim _ _

theorem inclusion'_top_functor (X : TopCat) :
    (@Opens.isOpenEmbedding X ⊤).functor = map (inclusionTopIso X).inv := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton

theorem functor_obj_map_obj {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y) :
    hf.functor.obj ((Opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U := by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

lemma set_range_inclusion' {X : TopCat} (U : Opens X) :
    Set.range (inclusion' U) = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]
theorem functor_map_eq_inf {X : TopCat} (U V : Opens X) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V ⊓ U := by
  ext1
  simp only [IsOpenMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]

theorem map_functor_eq' {X U : TopCat} (f : U ⟶ X) (hf : IsOpenEmbedding f) (V) :
    ((Opens.map f).obj <| hf.functor.obj V) = V :=
  Opens.ext <| Set.preimage_image_eq _ hf.injective

@[simp]
theorem map_functor_eq {X : TopCat} {U : Opens X} (V : Opens U) :
    ((Opens.map U.inclusion').obj <| U.isOpenEmbedding.functor.obj V) = V :=
  TopologicalSpace.Opens.map_functor_eq' _ U.isOpenEmbedding V

@[simp]
theorem adjunction_counit_map_functor {X : TopCat} {U : Opens X} (V : Opens U) :
    U.isOpenEmbedding.isOpenMap.adjunction.counit.app (U.isOpenEmbedding.functor.obj V) =
      eqToHom (by dsimp; rw [map_functor_eq V]) := by
  subsingleton

end TopologicalSpace.Opens
