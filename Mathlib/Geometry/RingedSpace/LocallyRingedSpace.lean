/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.Stalks

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`IsLocalHom` on the stalk maps).
-/

-- Explicit universe annotations were used in this file to improve performance #12737

universe u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  localRing : ∀ x, LocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.localRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- An alias for `toSheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
 -/
def toRingedSpace : RingedSpace :=
  X.toSheafedSpace

/-- The underlying topological space of a locally ringed space. -/
def toTopCat : TopCat :=
  X.1.carrier

instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

instance (x : X) : LocalRing (X.presheaf.stalk x) :=
  X.localRing x

-- PROJECT: how about a typeclass "HasStructureSheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for `PresheafedSpace`, `LocallyRingedSpace`, `Scheme`, etc.
/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphisms induced on stalks are local ring homomorphisms. -/
@[ext]
structure Hom (X Y : LocallyRingedSpace.{u}) : Type _ where
  /-- the underlying morphism between ringed spaces -/
  val : X.toSheafedSpace ⟶ Y.toSheafedSpace
  /-- the underlying morphism induces a local ring homomorphism on stalks -/
  prop : ∀ x, IsLocalHom (val.stalkMap x)

instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩

@[ext] lemma Hom.ext' (X Y : LocallyRingedSpace.{u}) {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext h

/-- A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable def Hom.stalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) :
    Y.presheaf.stalk (f.1.1 x) ⟶ X.presheaf.stalk x :=
  f.val.stalkMap x

@[instance]
theorem isLocalHomStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x) :=
  f.2 x

@[deprecated (since := "2024-10-10")]
alias isLocalRingHomStalkMap := isLocalHomStalkMap

@[instance]
theorem isLocalHomValStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.val.stalkMap x) :=
  f.2 x

@[deprecated (since := "2024-10-10")]
alias isLocalRingHomValStalkMap := isLocalHomValStalkMap

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace.{u}) : Hom X X :=
  ⟨𝟙 _, fun x => by erw [PresheafedSpace.stalkMap.id]; apply isLocalHom_id⟩

instance (X : LocallyRingedSpace.{u}) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of locally ringed spaces. -/
def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.val ≫ g.val, fun x => by
    erw [PresheafedSpace.stalkMap.comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ (f.2 _) (g.2 _)⟩

/-- The category of locally ringed spaces. -/
instance : Category LocallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp {_ _ _} f g := comp f g
  comp_id {X Y} f := Hom.ext <| by simp [comp]
  id_comp {X Y} f := Hom.ext <| by simp [comp]
  assoc {_ _ _ _} f g h := Hom.ext <| by simp [comp]

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
@[simps]
def forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X := X.toSheafedSpace
  map {_ _} f := f.1

instance : forgetToSheafedSpace.Faithful where
  map_injective {_ _} _ _ h := Hom.ext h

/-- The forgetful functor from `LocallyRingedSpace` to `Top`. -/
@[simps!]
def forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]
theorem comp_val {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp] theorem id_val' (X : LocallyRingedSpace.{u}) : Hom.val (𝟙 X) = 𝟙 X.toSheafedSpace :=
  rfl

-- Porting note: complains that `(f ≫ g).val.c` can be further simplified
-- so changed to its simp normal form `(f.val ≫ g.val).c`
@[simp]
theorem comp_val_c {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f.1 ≫ g.1).c = g.val.c ≫ (Presheaf.pushforward _ g.val.base).map f.val.c :=
  rfl

theorem comp_val_c_app {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app (op <| (Opens.map g.val.base).obj U.unop) :=
  rfl

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `isoOfSheafedSpaceIso`.
-/
@[simps]
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y :=
  Hom.mk f fun x =>
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    show IsLocalHom ((SheafedSpace.forgetToPresheafedSpace.map f).stalkMap x) by
      infer_instance

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forgetToSheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) :
    X ≅ Y where
  hom := homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := Hom.ext f.hom_inv_id
  inv_hom_id := Hom.ext f.inv_hom_id

instance : forgetToSheafedSpace.ReflectsIsomorphisms where reflects {_ _} f i :=
  { out :=
      ⟨homOfSheafedSpaceHomOfIsIso (CategoryTheory.inv (forgetToSheafedSpace.map f)),
        Hom.ext (IsIso.hom_inv_id (I := i)), Hom.ext (IsIso.inv_hom_id (I := i))⟩ }

instance is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.1 :=
  LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

/-- The restriction of a locally ringed space along an open embedding.
-/
@[simps!]
def restrict {U : TopCat} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : OpenEmbedding f) :
    LocallyRingedSpace where
  localRing := by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.localRing _ _ _ (X.localRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

/-- The canonical map from the restriction to the subspace. -/
def ofRestrict {U : TopCat} (X : LocallyRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

/-- The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.openEmbedding ⊤) ≅ X :=
  isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : LocallyRingedSpace.{u}ᵒᵖ) : Γ.obj X = X.unop.presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : LocallyRingedSpace.{u}) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

/-- The empty locally ringed space. -/
def empty : LocallyRingedSpace.{u} where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  localRing x := PEmpty.elim x

instance : EmptyCollection LocallyRingedSpace.{u} := ⟨LocallyRingedSpace.empty⟩

/-- The canonical map from the empty locally ringed space. -/
def emptyTo (X : LocallyRingedSpace) : ∅ ⟶ X :=
  ⟨⟨⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable
instance {X : LocallyRingedSpace} : Unique (∅ ⟶ X) where
  default := LocallyRingedSpace.emptyTo X
  uniq f := by ext ⟨⟩ x; aesop_cat

/-- The empty space is initial in `LocallyRingedSpace`. -/
noncomputable
def emptyIsInitial : Limits.IsInitial (∅ : LocallyRingedSpace.{u}) := Limits.IsInitial.ofUnique _

-- This actually holds for all ringed spaces with nontrivial stalks.
theorem basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) :
    X.toRingedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ := by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
    exists_and_right, exists_eq_right, Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intros hx
  rw [map_zero, isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) ≠ (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]
lemma basicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
    (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) :
    X.toRingedSpace.basicOpen f = ⊥ := by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [←  X.toRingedSpace.basicOpen_pow f n h, hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h, pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]

instance component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U] :
    Nontrivial (X.presheaf.obj <| op U) :=
  (X.presheaf.germ _ _ hU.some.2).domain_nontrivial

@[simp]
lemma iso_hom_val_base_inv_val_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.hom.val.base ≫ e.inv.val.base = 𝟙 _ := by
  rw [← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val]
  simp

@[simp]
lemma iso_hom_val_base_inv_val_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X) :
    (e.inv.val.base (e.hom.val.base x)) = x := by
  show (e.hom.val.base ≫ e.inv.val.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]
lemma iso_inv_val_base_hom_val_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.inv.val.base ≫ e.hom.val.base = 𝟙 _ := by
  rw [← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val]
  simp

@[simp]
lemma iso_inv_val_base_hom_val_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y) :
    (e.hom.val.base (e.inv.val.base y)) = y := by
  show (e.inv.val.base ≫ e.hom.val.base) y = 𝟙 Y.toPresheafedSpace y
  simp

section Stalks

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp]
lemma stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x

lemma stalkMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.val.base x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.val g.val x

@[reassoc]
lemma stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.val.base.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.val h

lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.val.base.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (stalkSpecializes_stalkMap f x x' h) y

@[reassoc]
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ hxx' ▸ rfl) ≫ g.stalkMap x' := by
  subst hfg
  subst hxx'
  simp

@[reassoc]
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ rfl) ≫
      g.stalkMap x := by
  subst hfg
  simp

@[reassoc]
lemma stalkMap_congr_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hxx' ▸ rfl) ≫ f.stalkMap x' := by
  subst hxx'
  simp

@[reassoc (attr := simp)]
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.val.base y) ≫ e.inv.stalkMap y =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

@[simp]
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.val.base y) z) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) z :=
  DFunLike.congr_fun (stalkMap_hom_inv e y) z

@[reassoc (attr := simp)]
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.val.base x) ≫ e.hom.stalkMap x =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

@[simp]
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.val.base x) y) =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) y :=
  DFunLike.congr_fun (stalkMap_inv_hom e x) y

@[reassoc (attr := simp)]
lemma stalkMap_germ (U : Opens Y) (x : X) (hx : f.val.base x ∈ U) :
    Y.presheaf.germ U (f.val.base x) hx ≫ f.stalkMap x =
      f.val.c.app (op U) ≫ X.presheaf.germ ((Opens.map f.1.base).obj U) x hx :=
  PresheafedSpace.stalkMap_germ f.val U x hx

lemma stalkMap_germ_apply (U : Opens Y) (x : X) (hx : f.val.base x ∈ U) (y) :
    f.stalkMap x (Y.presheaf.germ U (f.val.base x) hx y) =
      X.presheaf.germ ((Opens.map f.1.base).obj U) x hx (f.val.c.app (op U) y) :=
  PresheafedSpace.stalkMap_germ_apply f.val U x hx y

theorem preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
    (s : Y.presheaf.obj (op U)) :
    (Opens.map f.1.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.1.base).obj U) (f.1.c.app _ s) := by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe, X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.val.stalkMap _).isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, toRingedSpace] at hx ⊢
    rw [RingedSpace.mem_basicOpen _ s (f.1.base x) hxU]
    rw [← stalkMap_germ_apply] at hx
    exact (isUnit_map_iff (f.val.stalkMap _) _).mp hx

variable {U : TopCat} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : OpenEmbedding f)
  (V : Opens U) (x : U) (hx : x ∈ V)

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at t `x`. -/
noncomputable
def restrictStalkIso : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x) :=
  X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]
lemma restrictStalkIso_hom_eq_germ :
    (X.restrict h).presheaf.germ _ x hx ≫ (X.restrictStalkIso h x).hom =
      X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx

lemma restrictStalkIso_hom_eq_germ_apply (y) :
    (X.restrictStalkIso h x).hom ((X.restrict h).presheaf.germ _ x hx y) =
      X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ y :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]
lemma restrictStalkIso_inv_eq_germ :
    X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ ≫
      (X.restrictStalkIso h x).inv = (X.restrict h).presheaf.germ _ x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx

lemma restrictStalkIso_inv_eq_germ_apply (y) :
    (X.restrictStalkIso h x).inv
      (X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ y) =
        (X.restrict h).presheaf.germ _ x hx y :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y

lemma restrictStalkIso_inv_eq_ofRestrict :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x :=
  PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x

instance ofRestrict_stalkMap_isIso : IsIso ((X.ofRestrict h).stalkMap x) :=
  PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

end Stalks

end LocallyRingedSpace

end AlgebraicGeometry
