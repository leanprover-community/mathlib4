/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Sets.Opens

#align_import topology.category.Top.opens from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

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
#align topological_space.opens.opens_hom_has_coe_to_fun TopologicalSpace.Opens.opensHomHasCoeToFun

/-!
We now construct as morphisms various inclusions of open sets.
-/


-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...
/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def infLELeft (U V : Opens X) : U ⊓ V ⟶ U :=
  inf_le_left.hom
#align topological_space.opens.inf_le_left TopologicalSpace.Opens.infLELeft

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
noncomputable def infLERight (U V : Opens X) : U ⊓ V ⟶ V :=
  inf_le_right.hom
#align topological_space.opens.inf_le_right TopologicalSpace.Opens.infLERight

/-- The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
noncomputable def leSupr {ι : Type*} (U : ι → Opens X) (i : ι) : U i ⟶ iSup U :=
  (le_iSup U i).hom
#align topological_space.opens.le_supr TopologicalSpace.Opens.leSupr

/-- The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
noncomputable def botLE (U : Opens X) : ⊥ ⟶ U :=
  bot_le.hom
#align topological_space.opens.bot_le TopologicalSpace.Opens.botLE

/-- The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
noncomputable def leTop (U : Opens X) : U ⟶ ⊤ :=
  le_top.hom
#align topological_space.opens.le_top TopologicalSpace.Opens.leTop

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `SheafOfFunctions`.
theorem infLELeft_apply (U V : Opens X) (x) :
    (infLELeft U V) x = ⟨x.1, (@inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
  rfl
#align topological_space.opens.inf_le_left_apply TopologicalSpace.Opens.infLELeft_apply

@[simp]
theorem infLELeft_apply_mk (U V : Opens X) (x) (m) :
    (infLELeft U V) ⟨x, m⟩ = ⟨x, (@inf_le_left _ _ U V : _ ≤ _) m⟩ :=
  rfl
#align topological_space.opens.inf_le_left_apply_mk TopologicalSpace.Opens.infLELeft_apply_mk

@[simp]
theorem leSupr_apply_mk {ι : Type*} (U : ι → Opens X) (i : ι) (x) (m) :
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_iSup U i : _) m⟩ :=
  rfl
#align topological_space.opens.le_supr_apply_mk TopologicalSpace.Opens.leSupr_apply_mk

/-- The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def toTopCat (X : TopCat.{u}) : Opens X ⥤ TopCat where
  obj U := ⟨U, inferInstance⟩
  map i :=
    ⟨fun x => ⟨x.1, i.le x.2⟩,
      (Embedding.continuous_iff embedding_subtype_val).2 continuous_induced_dom⟩
set_option linter.uppercaseLean3 false in
#align topological_space.opens.to_Top TopologicalSpace.Opens.toTopCat

@[simp]
theorem toTopCat_map (X : TopCat.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} :
    ((toTopCat X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl
set_option linter.uppercaseLean3 false in
#align topological_space.opens.to_Top_map TopologicalSpace.Opens.toTopCat_map

/-- The inclusion map from an open subset to the whole space, as a morphism in `TopCat`.
-/
@[simps (config := .asFn)]
def inclusion {X : TopCat.{u}} (U : Opens X) : (toTopCat X).obj U ⟶ X where
  toFun := _
  continuous_toFun := continuous_subtype_val
#align topological_space.opens.inclusion TopologicalSpace.Opens.inclusion

@[simp]
theorem coe_inclusion {X : TopCat} {U : Opens X} :
    (inclusion U : U → X) = Subtype.val := rfl

theorem openEmbedding {X : TopCat.{u}} (U : Opens X) : OpenEmbedding (inclusion U) :=
  IsOpen.openEmbedding_subtype_val U.2
#align topological_space.opens.open_embedding TopologicalSpace.Opens.openEmbedding

/-- The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : TopCat.{u}) : (toTopCat X).obj ⊤ ≅ X where
  hom := inclusion ⊤
  inv := ⟨fun x => ⟨x, trivial⟩, continuous_def.2 fun U ⟨_, hS, hSU⟩ => hSU ▸ hS⟩
#align topological_space.opens.inclusion_top_iso TopologicalSpace.Opens.inclusionTopIso

/-- `Opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X where
  obj U := ⟨f ⁻¹' (U : Set Y), U.isOpen.preimage f.continuous⟩
  map i := ⟨⟨fun x h => i.le h⟩⟩
#align topological_space.opens.map TopologicalSpace.Opens.map

@[simp]
theorem map_coe (f : X ⟶ Y) (U : Opens Y) : ((map f).obj U : Set X) = f ⁻¹' (U : Set Y) :=
  rfl
#align topological_space.opens.map_coe TopologicalSpace.Opens.map_coe

@[simp]
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.continuous⟩ :=
  rfl
#align topological_space.opens.map_obj TopologicalSpace.Opens.map_obj

@[simp]
theorem map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl
#align topological_space.opens.map_id_obj TopologicalSpace.Opens.map_id_obj

@[simp 1100]
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl
#align topological_space.opens.map_id_obj' TopologicalSpace.Opens.map_id_obj'

@[simp 1100]
theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
  let ⟨_, _⟩ := U.unop
  rfl
#align topological_space.opens.map_id_obj_unop TopologicalSpace.Opens.map_id_obj_unop

@[simp 1100]
theorem op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by simp
#align topological_space.opens.op_map_id_obj TopologicalSpace.Opens.op_map_id_obj

@[simp]
lemma map_top (f : X ⟶ Y) : (Opens.map f).obj ⊤ = ⊤ := rfl

/-- The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
noncomputable def leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤ :=
  leTop U
#align topological_space.opens.le_map_top TopologicalSpace.Opens.leMapTop

@[simp]
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl
#align topological_space.opens.map_comp_obj TopologicalSpace.Opens.map_comp_obj

@[simp]
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
    (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl
#align topological_space.opens.map_comp_obj' TopologicalSpace.Opens.map_comp_obj'

@[simp]
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) :
    (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl
#align topological_space.opens.map_comp_map TopologicalSpace.Opens.map_comp_map

@[simp]
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl
#align topological_space.opens.map_comp_obj_unop TopologicalSpace.Opens.map_comp_obj_unop

@[simp]
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl
#align topological_space.opens.op_map_comp_obj TopologicalSpace.Opens.op_map_comp_obj

theorem map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι → Opens Y) :
    (map f).obj (iSup U) = iSup ((map f).obj ∘ U) := by
  ext1; rw [iSup_def, iSup_def, map_obj]
  dsimp; rw [Set.preimage_iUnion]
#align topological_space.opens.map_supr TopologicalSpace.Opens.map_iSup

section

variable (X)

/-- The functor `Opens X ⥤ Opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where
  hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }
#align topological_space.opens.map_id TopologicalSpace.Opens.mapId

theorem map_id_eq : map (𝟙 X) = 𝟭 (Opens X) := by
  rfl
#align topological_space.opens.map_id_eq TopologicalSpace.Opens.map_id_eq

end

/-- The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where
  hom := { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }
#align topological_space.opens.map_comp TopologicalSpace.Opens.mapComp

theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl
#align topological_space.opens.map_comp_eq TopologicalSpace.Opens.map_comp_eq

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
/-- If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `Opens Y ⥤ Opens X` they induce are isomorphic.
-/
def mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  NatIso.ofComponents fun U => eqToIso (by rw [congr_arg map h])
#align topological_space.opens.map_iso TopologicalSpace.Opens.mapIso

theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g := by
  subst h
  rfl
#align topological_space.opens.map_eq TopologicalSpace.Opens.map_eq

@[simp]
theorem mapIso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _) :=
  rfl
#align topological_space.opens.map_iso_refl TopologicalSpace.Opens.mapIso_refl

@[simp]
theorem mapIso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).hom.app U = eqToHom (by rw [h]) :=
  rfl
#align topological_space.opens.map_iso_hom_app TopologicalSpace.Opens.mapIso_hom_app

@[simp]
theorem mapIso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).inv.app U = eqToHom (by rw [h]) :=
  rfl
#align topological_space.opens.map_iso_inv_app TopologicalSpace.Opens.mapIso_inv_app

/-- A homeomorphism of spaces gives an equivalence of categories of open sets.

TODO: define `OrderIso.equivalence`, use it.
-/
@[simps]
def mapMapIso {X Y : TopCat.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X where
  functor := map H.hom
  inverse := map H.inv
  unitIso := NatIso.ofComponents fun U => eqToIso (by simp [map, Set.preimage_preimage])
  counitIso := NatIso.ofComponents fun U => eqToIso (by simp [map, Set.preimage_preimage])
#align topological_space.opens.map_map_iso TopologicalSpace.Opens.mapMapIso

end TopologicalSpace.Opens

/-- An open map `f : X ⟶ Y` induces a functor `Opens X ⥤ Opens Y`.
-/
@[simps obj_coe]
def IsOpenMap.functor {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj U := ⟨f '' (U : Set X), hf (U : Set X) U.2⟩
  map h := ⟨⟨Set.image_subset _ h.down.down⟩⟩
#align is_open_map.functor IsOpenMap.functor

/-- An open map `f : X ⟶ Y` induces an adjunction between `Opens X` and `Opens Y`.
-/
def IsOpenMap.adjunction {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    Adjunction hf.functor (TopologicalSpace.Opens.map f) :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun U => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
      counit := { app := fun V => homOfLE fun y ⟨_, hfxV, hxy⟩ => hxy ▸ hfxV } }
#align is_open_map.adjunction IsOpenMap.adjunction

instance IsOpenMap.functorFullOfMono {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) [H : Mono f] :
    hf.functor.Full where
  map_surjective i :=
    ⟨homOfLE fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (TopCat.mono_iff_injective f).mp H eq ▸ hy, rfl⟩
#align is_open_map.functor_full_of_mono IsOpenMap.functorFullOfMono

instance IsOpenMap.functor_faithful {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) :
    hf.functor.Faithful where
#align is_open_map.functor_faithful IsOpenMap.functor_faithful

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
#align topological_space.opens.open_embedding_obj_top TopologicalSpace.Opens.openEmbedding_obj_top

@[simp]
theorem inclusion_map_eq_top {X : TopCat} (U : Opens X) : (Opens.map U.inclusion).obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _
#align topological_space.opens.inclusion_map_eq_top TopologicalSpace.Opens.inclusion_map_eq_top

@[simp]
theorem adjunction_counit_app_self {X : TopCat} (U : Opens X) :
    U.openEmbedding.isOpenMap.adjunction.counit.app U = eqToHom (by simp) := Subsingleton.elim _ _
#align topological_space.opens.adjunction_counit_app_self TopologicalSpace.Opens.adjunction_counit_app_self

theorem inclusion_top_functor (X : TopCat) :
    (@Opens.openEmbedding X ⊤).isOpenMap.functor = map (inclusionTopIso X).inv := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro U
    ext x
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivial⟩, h, rfl⟩⟩
  · intros U V f
    apply Subsingleton.elim
#align topological_space.opens.inclusion_top_functor TopologicalSpace.Opens.inclusion_top_functor

theorem functor_obj_map_obj {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap f) (U : Opens Y) :
    hf.functor.obj ((Opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U := by
  ext
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial, rfl⟩, hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
#align topological_space.opens.functor_obj_map_obj TopologicalSpace.Opens.functor_obj_map_obj

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
#align topological_space.opens.functor_map_eq_inf TopologicalSpace.Opens.functor_map_eq_inf

theorem map_functor_eq' {X U : TopCat} (f : U ⟶ X) (hf : OpenEmbedding f) (V) :
    ((Opens.map f).obj <| hf.isOpenMap.functor.obj V) = V :=
  Opens.ext <| Set.preimage_image_eq _ hf.inj
#align topological_space.opens.map_functor_eq' TopologicalSpace.Opens.map_functor_eq'

@[simp]
theorem map_functor_eq {X : TopCat} {U : Opens X} (V : Opens U) :
    ((Opens.map U.inclusion).obj <| U.openEmbedding.isOpenMap.functor.obj V) = V :=
  TopologicalSpace.Opens.map_functor_eq' _ U.openEmbedding V
#align topological_space.opens.map_functor_eq TopologicalSpace.Opens.map_functor_eq

@[simp]
theorem adjunction_counit_map_functor {X : TopCat} {U : Opens X} (V : Opens U) :
    U.openEmbedding.isOpenMap.adjunction.counit.app (U.openEmbedding.isOpenMap.functor.obj V) =
      eqToHom (by dsimp; rw [map_functor_eq V]) := by
  apply Subsingleton.elim
#align topological_space.opens.adjunction_counit_map_functor TopologicalSpace.Opens.adjunction_counit_map_functor

end TopologicalSpace.Opens
