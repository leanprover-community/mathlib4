/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Sets.Opens

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
`mapId : map (𝟙 X) ≅ 𝟭 (opens X)` and
`mapComp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/


open CategoryTheory TopologicalSpace Opposite

universe u

namespace TopologicalSpace.Opens

variable {X Y Z : TopCat.{u}}

/-!
Since `Opens X` has a partial order, it automatically receives a `Category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ULift (PLift (U ≤ V))`.
-/


instance opensHomHasCoeToFun {U V : Opens X} : CoeFun (U ⟶ V) fun _ => U → V :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩

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
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_iSup U i : _) m⟩ :=
  rfl

/-- The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where
  obj U := ⟨U, inferInstance⟩
  map i :=
    ⟨fun x => ⟨x.1, i.le x.2⟩,
      (Embedding.continuous_iff embedding_subtype_val).2 continuous_induced_dom⟩

@[simp]
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an open subset to the whole space, as a morphism in `TopCat`.
-/
@[simps (config := .asFn)]
def inclusion {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X where
  toFun := _
  continuous_toFun := continuous_subtype_val

@[simp]
theorem coe_inclusion {X : TopCat} {U : Opens X} :
    (inclusion U : U → X) = Subtype.val := rfl

theorem openEmbedding {X : TopCat.{u}} (U : Opens X) : OpenEmbedding (inclusion U) :=
  IsOpen.openEmbedding_subtype_val U.2

/-- The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion ⊤
  inv := ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun U ⟨_, hS, hSU⟩ => hSU ▸ hS⟩

/-- `Opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X where
  obj U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.continuous⟩
  map i := ⟨⟨fun x h => i.le h⟩⟩

@[simp]
theorem map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl

@[simp]
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.continuous⟩ :=
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

@[simp 1100]
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

@[simp 1100]
theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
  let ⟨_, _⟩ := U.unop
  rfl

@[simp 1100]
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
  ext1; rw [iSup_def, iSup_def, map_obj]
  dsimp; rw [Set.preimage_iUnion]

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

/-- A homeomorphism of spaces gives an equivalence of categories of open sets.

TODO: define `OrderIso.equivalence`, use it.
-/
@[simps]
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X where
  functor := map H.hom
  inverse := map H.inv
  unitIso := NatIso.ofComponents fun U => eqToIso (by simp [map, Set.preimage_preimage])
  counitIso := NatIso.ofComponents fun U => eqToIso (by simp [map, Set.preimage_preimage])

end TopologicalSpace.Opens

/-- An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
@[simps obj_coe]
def IsOpenMap.functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map h := ⟨⟨Set.image_subset _ h.down.down⟩⟩

/-- An open map `f : X ⟶ Y` induces an adjunction between `Opens X` and `Opens Y`.
-/
def IsOpenMap.adjunction {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    Adjunction hf.functor (TopologicalSpace.Opens.map f) :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun U => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
      counit := { app := fun V => homOfLE fun y ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV } }

instance IsOpenMap.functorFullOfMono {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) [H : Mono f] :
    hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩

instance IsOpenMap.functor_faithful {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.Faithful where

lemma OpenEmbedding.functor_obj_injective {X Y : TopCat} {f : X ⟶ Y} (hf : OpenEmbedding f) :
    Function.Injective hf.isOpenMap.functor.obj :=
  fun _ _ e ↦ Opens.ext (Set.image_injective.mpr hf.inj (congr_arg (↑· : Opens Y → Set Y) e))

namespace TopologicalSpace.Opens

open TopologicalSpace

@[simp]
theorem openEmbedding_obj_top {X : TopCat} (U : Opens X) :
    U.openEmbedding.isOpenMap.functor.obj ⊤ = U := by
  ext1
  exact Set.image_univ.trans Subtype.range_coe

@[simp]
theorem inclusion_map_eq_top {X : TopCat} (U : Opens X) : (Opens.map U.inclusion).obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
theorem adjunction_counit_app_self {X : TopCat} (U : Opens X) :
    U.openEmbedding.isOpenMap.adjunction.counit.app U = eqToHom (by simp) := Subsingleton.elim _ _

theorem inclusion_top_functor (X : TopCat) :
    (@Opens.openEmbedding X ⊤).isOpenMap.functor = map (inclusionTopIso X).inv := by
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

-- Porting note: added to ease the proof of `functor_map_eq_inf`
lemma set_range_forget_map_inclusion {X : TopCat} (U : Opens X) :
    Set.range ((forget TopCat).map (inclusion U)) = (U : Set X) := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

@[simp]
theorem functor_map_eq_inf {X : TopCat} (U V : Opens X) :
    U.openEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion).obj V) = V ⊓ U := by
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  erw [set_range_forget_map_inclusion U]
  rfl

theorem map_functor_eq' {X U : TopCat} (f : U ⟶ X) (hf : OpenEmbedding f) (V) :
    ((Opens.map f).obj <| hf.isOpenMap.functor.obj V) = V :=
  Opens.ext <| Set.preimage_image_eq _ hf.inj

@[simp]
theorem map_functor_eq {X : TopCat} {U : Opens X} (V : Opens U) :
    ((Opens.map U.inclusion).obj <| U.openEmbedding.isOpenMap.functor.obj V) = V :=
  TopologicalSpace.Opens.map_functor_eq' _ U.openEmbedding V

@[simp]
theorem adjunction_counit_map_functor {X : TopCat} {U : Opens X} (V : Opens U) :
    U.openEmbedding.isOpenMap.adjunction.counit.app (U.openEmbedding.isOpenMap.functor.obj V) =
      eqToHom (by dsimp; rw [map_functor_eq V]) := by
  subsingleton

end TopologicalSpace.Opens
