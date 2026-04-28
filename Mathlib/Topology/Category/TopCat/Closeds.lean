/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Sets.Closeds

/-!
# The category of closed sets in a topological space.

We define `toTopCat : Closeds X ⥤ TopCat` and
`map (f : X ⟶ Y) : Closeds Y ⥤ Closeds X`, given by taking preimages of closed sets.

This file is almost entirely copied from `Mathlib.Topology.Category.TopCat.Opens`
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace TopologicalSpace.Closeds

variable {X Y Z : TopCat.{u}} {U V W : Closeds X}

/-!
Since `Closeds X` has a partial order, it automatically receives a `SmallCategory` instance, see
`Preorder.smallCategory` in the file `Mathlib/CategoryTheory/Category/Preorder.lean`
-/

instance closedsHom.instFunLike : FunLike (U ⟶ V) U V where
  coe f := Set.inclusion f.le
  coe_injective' := by rintro ⟨⟨_⟩⟩ _ _; congr!

lemma apply_def (f : U ⟶ V) (x : U) : f x = ⟨x, f.le x.2⟩ := rfl

@[simp] lemma apply_mk (f : U ⟶ V) (x : X) (hx) : f ⟨x, hx⟩ = ⟨x, f.le hx⟩ := rfl

@[simp] lemma val_apply (f : U ⟶ V) (x : U) : (f x : X) = x := rfl

@[simp, norm_cast] lemma coe_id (f : U ⟶ U) : ⇑f = id := rfl

lemma id_apply (f : U ⟶ U) (x : U) : f x = x := rfl

@[simp] lemma comp_apply (f : U ⟶ V) (g : V ⟶ W) (x : U) : (f ≫ g) x = g (f x) := rfl


/-- The functor from closed sets in `X` to `TopCat`,
realising each closed set as a topological space itself.
-/
def toTopCat (X : TopCat.{u}) : Closeds X ⥤ TopCat where
  obj U := TopCat.of U
  map i := TopCat.ofHom ⟨fun x ↦ ⟨x.1, i.le x.2⟩,
    IsEmbedding.subtypeVal.continuous_iff.2 continuous_induced_dom⟩

@[simp]
theorem toTopCat_map (X : TopCat.{u}) {U V : Closeds X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an closed subset to the whole space, as a morphism in `TopCat`.
-/
@[simps! -fullyApplied]
def inclusion' {X : TopCat.{u}} (U : Closeds X) : (toTopCat X).obj U ⟶ X :=
  TopCat.ofHom
  { toFun := _
    continuous_toFun := continuous_subtype_val }

@[simp]
theorem coe_inclusion' {X : TopCat} {U : Closeds X} :
    (inclusion' U : U → X) = Subtype.val := rfl

theorem isClosedEmbedding {X : TopCat.{u}} (U : Closeds X) : IsClosedEmbedding (inclusion' U) :=
  U.2.isClosedEmbedding_subtypeVal

/-- The inclusion of the top closed subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion' ⊤
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun _ ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

/-- `Closeds.map f` gives the functor from closed sets in Y to closed set in X,
given by taking preimages under f. -/
def map (f : X ⟶ Y) : Closeds Y ⥤ Closeds X where
  obj U := ⟨f ⁻¹' (U : Set Y), U.isClosed.preimage f.hom.continuous⟩
  map i := ⟨⟨fun _ h => i.le h⟩⟩

@[simp]
theorem map_coe (f : X ⟶ Y) (U : Closeds Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl

@[simp]
theorem mem_map {f : X ⟶ Y} {U : Closeds Y} {x : X} :
    x ∈ (map f).obj U ↔ f.hom x ∈ U := .rfl

@[simp]
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.hom.continuous⟩ :=
  rfl

@[simp]
lemma map_homOfLE (f : X ⟶ Y) {U V : Closeds Y} (e : U ≤ V) :
    (TopologicalSpace.Closeds.map f).map (homOfLE e) =
      homOfLE (show (Closeds.map f).obj U ≤ (Closeds.map f).obj V from fun _ hx ↦ e hx) :=
  rfl

@[simp]
theorem map_id_obj (U : Closeds X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl

@[simp]
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

theorem map_id_obj_unop (U : (Closeds X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U := by
  simp

theorem op_map_id_obj (U : (Closeds X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by simp

@[simp]
lemma map_top (f : X ⟶ Y) : (Closeds.map f).obj ⊤ = ⊤ := rfl

/-- The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of closed sets.
-/
def leMapTop (f : X ⟶ Y) (U : Closeds X) : U ⟶ (map f).obj ⊤ :=
  le_top.hom

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

theorem map_iInf (f : X ⟶ Y) {ι : Type*} (U : ι → Closeds Y) :
    (map f).obj (iInf U) = iInf ((map f).obj ∘ U) := by
  ext
  simp

section

variable (X)

/-- The functor `Closeds X ⥤ Closeds X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def mapId : map (𝟙 X) ≅ 𝟭 (Closeds X) where
  hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

theorem map_id_eq : map (𝟙 X) = 𝟭 (Closeds X) := by
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
then the functors `Closeds Y ⥤ Closeds X` they induce are isomorphic.
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
theorem mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Closeds Y) :
    (mapIso f g h).hom.app U = eqToHom (by rw [h]) :=
  rfl

@[simp]
theorem mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Closeds Y) :
    (mapIso f g h).inv.app U = eqToHom (by rw [h]) :=
  rfl

/-- A homeomorphism of spaces gives an equivalence of categories of closed sets.

TODO: define `OrderIso.equivalence`, use it.
-/
@[simps]
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Closeds Y ≌ Closeds X where
  functor := map H.hom
  inverse := map H.inv
  unitIso := NatIso.ofComponents fun U => eqToIso (by aesop)
  counitIso := NatIso.ofComponents fun U => eqToIso (by aesop)

end TopologicalSpace.Closeds

/-- An closed map `f : X ⟶ Y` induces a functor `Closeds X ⥤ Closeds Y`.
-/
@[simps obj_coe]
def IsClosedMap.functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsClosedMap f) :
    Closeds X ⥤ Closeds Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map h := ⟨⟨Set.image_mono h.down.down⟩⟩

/-- An closed map `f : X ⟶ Y` induces an adjunction between `Closeds X` and `Closeds Y`.
-/
def IsClosedMap.adjunction {X Y : TopCat} {f : X ⟶ Y} (hf : IsClosedMap f) :
    hf.functor ⊣ Closeds.map f where
  unit := { app := fun _ => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
  counit := { app := fun _ => homOfLE fun _ ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV }

instance IsClosedMap.functorFullOfMono {X Y : TopCat} {f : X ⟶ Y} (hf : IsClosedMap f)
    [H : Mono f] : hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

instance IsClosedMap.functor_faithful {X Y : TopCat} {f : X ⟶ Y} (hf : IsClosedMap f) :
    hf.functor.Faithful where

lemma Topology.IsClosedEmbedding.functor_obj_injective {X Y : TopCat} {f : X ⟶ Y}
    (hf : IsClosedEmbedding f) : Function.Injective hf.isClosedMap.functor.obj :=
  fun _ _ e ↦ Closeds.ext
    (Set.image_injective.mpr hf.injective (congr_arg (↑· : Closeds Y → Set Y) e))

namespace TopologicalSpace.Closeds

open TopologicalSpace

@[simp]
theorem isClosedEmbedding_obj_top {X : TopCat} (U : Closeds X) :
    U.isClosedEmbedding.isClosedMap.functor.obj ⊤ = U := by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]
theorem inclusion'_map_eq_top {X : TopCat} (U : Closeds X) :
    (Closeds.map U.inclusion').obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
theorem adjunction_counit_app_self {X : TopCat} (U : Closeds X) :
    U.isClosedEmbedding.isClosedMap.adjunction.counit.app U = eqToHom (by simp) :=
  Subsingleton.elim _ _

theorem inclusion'_top_functor (X : TopCat) :
    (@Closeds.isClosedEmbedding X ⊤).isClosedMap.functor = map (inclusionTopIso X).inv := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · subsingleton

theorem functor_obj_map_obj {X Y : TopCat} {f : X ⟶ Y} (hf : IsClosedMap f) (U : Closeds Y) :
    hf.functor.obj ((Closeds.map f).obj U) = hf.functor.obj ⊤ ⊓ U := by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

lemma set_range_inclusion' {X : TopCat} (U : Closeds X) :
    Set.range (inclusion' U) = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]
theorem functor_map_eq_inf {X : TopCat} (U V : Closeds X) :
    U.isClosedEmbedding.isClosedMap.functor.obj ((Closeds.map U.inclusion').obj V) = V ⊓ U := by
  ext1
  simp only [IsClosedMap.coe_functor_obj, map_coe, coe_inf,
    Set.image_preimage_eq_inter_range, set_range_inclusion' U]

theorem map_functor_eq' {X U : TopCat} (f : U ⟶ X) (hf : IsClosedEmbedding f) (V) :
    ((Closeds.map f).obj <| hf.isClosedMap.functor.obj V) = V :=
  Closeds.ext <| Set.preimage_image_eq _ hf.injective

@[simp]
theorem map_functor_eq {X : TopCat} {U : Closeds X} (V : Closeds U) :
    ((Closeds.map U.inclusion').obj <| U.isClosedEmbedding.isClosedMap.functor.obj V) = V :=
  TopologicalSpace.Closeds.map_functor_eq' _ U.isClosedEmbedding V

@[simp]
theorem adjunction_counit_map_functor {X : TopCat} {U : Closeds X} (V : Closeds U) :
    U.isClosedEmbedding.isClosedMap.adjunction.counit.app
      (U.isClosedEmbedding.isClosedMap.functor.obj V) = eqToHom
      (by dsimp; rw [map_functor_eq V]) := by
  subsingleton

end TopologicalSpace.Closeds
