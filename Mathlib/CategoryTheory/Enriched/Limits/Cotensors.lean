/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.CategoryTheory.Enriched.TensorProductCategory

universe u u₁ v w

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory

open scoped MonoidalClosed

namespace CategoryTheory.Enriched

abbrev Ihom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] (x y : V) : V :=
  (ihom x).obj y

-- The variable V is explicit here since trying to make it implicit throws errors in practice
abbrev Ehom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (C : Type v) [EnrichedCategory V C] (x y : C) : V :=
  @EnrichedCategory.Hom V _ _ _ _ x y

variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

/-- The structure of the cotensoring of `x : C` by `v : V` -/
structure Precotensor (v : V) (x : C) where
  obj : C
  cone : v ⟶ (Ehom V C obj x)

/-- The adjoint tranpose of precotensor_eval -/
def Precotensor.coneNatTrans {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    (Ehom V C y vx.obj) ⟶ (Ihom V v (Ehom V C y x)) :=
  curry ((β_ v (Ehom V C y vx.obj)).hom ≫ Ehom V C y vx.obj ◁ vx.cone ≫ eComp V y vx.obj x)

lemma Precotensor.coneNatTrans_eq {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    uncurry (vx.coneNatTrans y) = (β_ _ _).hom ≫ _ ◁ vx.cone ≫ eComp V y vx.obj x :=
  uncurry_curry _

lemma Precotensor.coneNatTrans_braid_eq {v : V} {x : C} (vx : Precotensor v x) (y : C) :
    (β_ _ _).inv ≫ uncurry (vx.coneNatTrans y) = _ ◁ vx.cone ≫ eComp V y vx.obj x :=
  (Iso.inv_comp_eq (β_ _ _)).mpr (coneNatTrans_eq vx y)

/-- A Cotensor is a Precotensor such that coneNatTransInv is an inverse to coneNatTrans. -/
structure Cotensor (v : V) (x : C) extends (Precotensor v x) where
  coneNatTransInv (y : C) :
    (Ihom V v (Ehom V C y x)) ⟶ (Ehom V C y obj)
  NatTransInv_NatTrans_eq (y : C) :
    (coneNatTransInv y ≫ Precotensor.coneNatTrans toPrecotensor y = 𝟙 _)
  NatTrans_NatTransInv_eq (y : C) :
    (Precotensor.coneNatTrans toPrecotensor y ≫ coneNatTransInv y = 𝟙 _)

/-- A cotensor of `x : C` by `v : V` determines an isomorphism of hom-objects
`C(y, v ⋔ x) ≅ V(v, C(y, x))` whose forward morphism is given by `coneNatTrans`. -/
@[simps]
def Cotensor.coneNatTransIso {v : V} {x : C} (vx : Cotensor v x) (y : C) : Ehom V C y vx.obj ≅
    Ihom V v (Ehom V C y x) where
  hom := vx.coneNatTrans y
  inv := vx.coneNatTransInv y
  hom_inv_id := vx.NatTrans_NatTransInv_eq y
  inv_hom_id := vx.NatTransInv_NatTrans_eq y

open CategoryTheory.Enriched

/- My own namespace for proving things about cotensors -/

variable (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

-- Postcomposition and its coherences
def postcompose {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    Ehom V C x y ⟶ Ehom V C vx.obj vy.obj :=
  curry (vx.cone ▷ Ehom V C x y ≫ eComp V vx.obj x y) ≫ vy.coneNatTransInv vx.obj

lemma postcompose_coneNatTrans_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    postcompose V vx vy ≫ vy.coneNatTrans _ = curry (vx.cone ▷ _ ≫ eComp V _ _ _) :=
  ((Category.assoc _ _ _).trans (whisker_eq _ (vy.NatTransInv_NatTrans_eq _))).trans (Category.comp_id _)

lemma uncurry_postcompose_coneNatTrans_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    uncurry (postcompose V vx vy ≫ vy.coneNatTrans _) = vx.cone ▷ _ ≫ eComp V _ _ _ := by
  simp only [postcompose_coneNatTrans_eq, uncurry_curry]

lemma postcompose_selfEval_comp_eq {x y : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y) :
    (postcompose V vx vy ⊗ₘ vy.cone) ≫ (eComp V vx.obj vy.obj y)
      = (β_ v _).inv ≫ (vx.cone ▷ _) ≫ (eComp V vx.obj x y) := by
  rw [tensorHom_def_assoc, ← vy.coneNatTrans_braid_eq, braiding_inv_naturality_left_assoc]
  refine (Iso.cancel_iso_inv_left _ _ _).mpr (curry_injective ?_)
  rw [curry_natural_left, curry_uncurry]
  exact postcompose_coneNatTrans_eq V vx vy

-- Precomposition and its coherences
def IhomPrecompose {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    Ihom V w v ⟶ Ehom V C vx.obj wx.obj :=
  (ihom w).map vx.cone ≫ wx.coneNatTransInv vx.obj

def EhomPrecompose {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x)
    : Ehom V V w v ⟶ Ehom V C vx.obj wx.obj := IhomPrecompose V _ _

lemma IhomPrecompose_coneNatTrans_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    IhomPrecompose V wx vx ≫ wx.coneNatTrans _ = (ihom w).map vx.cone :=
  ((Category.assoc _ _ _).trans (whisker_eq _ (wx.NatTransInv_NatTrans_eq _))).trans (Category.comp_id _)

lemma EhomPrecompose_coneNatTrans_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    EhomPrecompose V wx vx ≫ wx.coneNatTrans _ = (ihom w).map vx.cone :=
  IhomPrecompose_coneNatTrans_eq V wx vx

-- Functorality of post-composition
theorem postcompose_comp_eq {x y z : C} {v : V} (vx : Cotensor v x) (vy : Cotensor v y)
    (vz : Cotensor v z) : eComp V x y z ≫ postcompose V vx vz =
      (postcompose V vx vy ⊗ₘ postcompose V vy vz) ≫ eComp V _ _ _ := by
  rw [postcompose, ← Category.assoc]
  refine (Iso.comp_inv_eq (vz.coneNatTransIso _)).mpr ?_
  -- LHS
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, whisker_exchange_assoc]
  -- RHS
  rw [uncurry_natural_left]
  rw [vz.coneNatTransIso_hom, vz.coneNatTrans_eq _]
  rw [braiding_naturality_right_assoc]
  rw [← tensorHom_def_assoc _ vz.cone]
  rw [← tensorHom_comp_whiskerRight_assoc]
  rw [braiding_tensor_right_hom_assoc]
  rw [← associator_inv_naturality_assoc]
  rw [e_assoc]
  rw [tensorHom_def_assoc]
  rw [whisker_exchange_assoc]
  simp_rw [← whiskerLeft_comp_assoc]
  rw [postcompose_selfEval_comp_eq]
  rw [Iso.hom_inv_id_assoc]
  rw [whiskerLeft_comp_assoc]
  rw [← associator_naturality_left_assoc]
  rw [← associator_naturality_middle_assoc]
  rw [e_assoc']
  simp_rw [← comp_whiskerRight_assoc]
  rw [← tensorHom_def_assoc _ vy.cone]
  rw [postcompose_selfEval_comp_eq]
  rw [Iso.hom_inv_id_assoc]
  rw [comp_whiskerRight_assoc]
  rw [← associator_inv_naturality_left_assoc]
  rw [e_assoc]

theorem postcompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V x ≫ postcompose V vx vx = eId V vx.obj := by
  rw [postcompose, ← Category.assoc]
  refine (Iso.comp_inv_eq (vx.coneNatTransIso _)).mpr ?_
  apply uncurry_injective
  simp_rw [uncurry_natural_left]
  rw [uncurry_curry, vx.coneNatTransIso_hom, vx.coneNatTrans_eq, ← braiding_naturality_left_assoc]
  simp_rw [whisker_exchange_assoc]
  simp

lemma IhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    ((IhomPrecompose V wx vx) ⊗ₘ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).inv ≫ (ihom.ev w).app v ≫ vx.cone := by
  rw [← ihom.ev_naturality, ← braiding_inv_naturality_left_assoc]
  unfold IhomPrecompose
  rw [← tensorHom_comp_whiskerRight_assoc, tensorHom_def_assoc, whisker_exchange_assoc]
  refine _ ≫= ((Iso.inv_comp_eq (whiskerRightIso (wx.coneNatTransIso vx.obj) _)).mpr ?_)
  change (_ ≫ _ = (wx.coneNatTrans _ ▷ w) ≫ _ ≫ _)
  rw [braiding_inv_naturality_left_assoc, ← uncurry_eq]
  exact (Precotensor.coneNatTrans_braid_eq wx.toPrecotensor vx.obj).symm

lemma EhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    ((EhomPrecompose V wx vx) ⊗ₘ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).inv ≫ (ihom.ev w).app v ≫ vx.cone :=
  IhomPrecompose_selfEval_comp_eq V wx vx

-- Functoriality of precomposition
theorem precompose_comp_eq {x : C} {u v w : V} (ux : Cotensor u x) (vx : Cotensor v x)
    (wx : Cotensor w x) : eComp V u v w ≫ EhomPrecompose V ux wx =
      (EhomPrecompose V ux vx ⊗ₘ EhomPrecompose V vx wx) ≫ (β_ _ _).hom ≫ eComp V _ _ _ := by
  refine (Iso.cancel_iso_hom_right _ _ (ux.coneNatTransIso _)).mp ?_
  simp only [Category.assoc]
  rw [braiding_naturality_assoc] -- Experiment with this line
  rw [ux.coneNatTransIso_hom, EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  rw [uncurry_natural_right]
  -- RHS
  simp_rw [uncurry_natural_left]
  rw [ux.coneNatTrans_eq]
  rw [braiding_naturality_right_assoc]
  rw [braiding_naturality_right_assoc]
  -- Expand braiding of product
  rw [← tensorHom_id]
  rw [← whisker_exchange_assoc]
  rw [braiding_tensor_right_hom_assoc]
  rw [← associator_inv_naturality_assoc]
  rw [← associator_inv_naturality_right_assoc]
  rw [e_assoc]
  rw [tensorHom_def_assoc, tensorHom_id]
  simp_rw [← whiskerLeft_comp_assoc]
  rw [← tensorHom_def_assoc _ ux.cone, EhomPrecompose_selfEval_comp_eq]
  simp_rw [whiskerLeft_comp_assoc]
  rw [whisker_exchange_assoc]
  erw [Iso.hom_inv_id_assoc (whiskerLeftIso (Ehom V C wx.obj vx.obj) (β_ u (Ehom V V u v)))]
  -- ALTERNATIVE TO THIS erw CALL:
  -- slice_rhs 5 10 =>
  --   change _ ≫ (whiskerLeftIso _ (β_ u (Ehom V V u v))).hom ≫ (whiskerLeftIso _ (β_ u (Ehom V V u v))).inv ≫ _
  --   rw [Iso.hom_inv_id_assoc (whiskerLeftIso (Ehom V C wx.obj vx.obj) (β_ u (Ehom V V u v)))]
  -- END ALTERNATIVE
  rw [← whisker_exchange_assoc]
  rw [← tensorHom_def_assoc]
  rw [EhomPrecompose_selfEval_comp_eq]
  erw [braiding_inv_naturality_right_assoc] -- TODO: avoid using erw?
  erw [uncurry_curry] -- TODO: avoid using erw?
  rw [compTranspose_eq]
  -- This should follow from simp at this point, but ihom vs ehom is causing problems
  slice_lhs 1 3 =>
    change (α_ _ (Ehom V V u v) (Ehom V V v w)).inv ≫ _ ▷ (Ehom V V v w) ≫ _
  simp

theorem precompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V v ≫ EhomPrecompose V vx vx = eId V vx.obj := by
  refine (Iso.cancel_iso_hom_right _ _ (vx.coneNatTransIso _)).mp ?_
  simp only [Category.assoc]
  rw [vx.coneNatTransIso_hom, EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_left, vx.coneNatTrans_eq,
    braiding_naturality_right_assoc, ← whisker_exchange_assoc]
  erw [uncurry_curry] -- TODO: avoid using erw?
  simp

/-- Commutativity of postcomposition with precoposition -/
theorem post_pre_eq_pre_post {x y : C} {w v : V} (wx : Cotensor w x) (wy : Cotensor w y)
    (vx : Cotensor v x) (vy : Cotensor v y) :
  (EhomPrecompose V wx vx ⊗ₘ postcompose V wx wy) ≫ eComp V vx.obj wx.obj wy.obj =
    (EhomPrecompose V wy vy ⊗ₘ postcompose V vx vy) ≫ (β_ _ _).hom
      ≫ eComp V vx.obj vy.obj wy.obj := by
  refine (Iso.cancel_iso_hom_right _ _ (wy.coneNatTransIso _)).mp ?_
  simp only [Category.assoc]
  apply uncurry_injective
  simp_rw [uncurry_natural_left]
  simp_rw [wy.coneNatTransIso_hom, wy.coneNatTrans_eq]
  -- LHS
  simp_rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [← tensorHom_def_assoc]
  rw [← e_assoc']
  rw [associator_naturality_assoc]
  rw [tensorHom_def_assoc]
  rw [← whiskerLeft_comp_assoc, postcompose_selfEval_comp_eq]
  simp_rw [whiskerLeft_comp_assoc]
  rw [← whisker_exchange_assoc]
  rw [← tensorHom_def_assoc]
  rw [← tensorHom_id]
  rw [← e_assoc]
  rw [associator_inv_naturality_assoc]
  rw [tensorHom_id]
  rw [← comp_whiskerRight_assoc]
  rw [EhomPrecompose_selfEval_comp_eq]
  simp_rw [comp_whiskerRight_assoc]
  -- RHS
  slice_rhs 1 6 =>
    rw [← comp_whiskerRight_assoc]
    rw [braiding_naturality]
    rw [comp_whiskerRight_assoc]
    rw [← whisker_exchange_assoc]
    rw [← tensorHom_id (_ ⊗ₘ _)]
    rw [← e_assoc']
    rw [associator_naturality_right_assoc]
    rw [associator_naturality_assoc]
    rw [tensorHom_def_assoc]
    repeat rw [← whiskerLeft_comp_assoc]
    rw [tensorHom_id]
    rw [← tensorHom_def]
    rw [EhomPrecompose_selfEval_comp_eq]
    repeat rw [whiskerLeft_comp_assoc]
    rw [← whisker_exchange_assoc]
    rw [← whisker_exchange_assoc]
    rw [← tensorHom_def_assoc]
    rw [postcompose_selfEval_comp_eq]
  -- This *should* follow from monoidal identities, but again definitions are failing to unfold...
  rw [braiding_inv_naturality_right_assoc]
  slice_lhs 1 5 =>
    simp
    rw [← comp_whiskerRight]
    erw [Iso.hom_inv_id]
    rw [id_whiskerRight, Category.comp_id]
  slice_rhs 1 5 =>
    simp only [braiding_tensor_right_hom, braiding_tensor_left_inv, Category.assoc]
    simp only [yang_baxter_assoc]
    erw [Iso.hom_inv_id_assoc (whiskerLeftIso _ _)]
    erw [Iso.hom_inv_id_assoc]
    erw [Iso.hom_inv_id_assoc (whiskerRightIso _ _)]
    erw [Iso.inv_hom_id_assoc]
    erw [Iso.hom_inv_id_assoc (whiskerLeftIso _ _)]
  exact rfl

class CotensoredCategory (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [BraidedCategory V] (C : Type v) [EnrichedCategory V C] where
  cotensor : (v : V) → (x : C) → Cotensor v x

def selfEnrichedPrecotensorCone (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [BraidedCategory V] (v x : V) : v ⟶ (ihom ((ihom v).obj x)).obj x := curry ((β_ _ _).inv ≫ (ihom.ev v).app x)

def selfEnrichedPrecotensor (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [BraidedCategory V] (v x : V) : Precotensor v x where
  obj := (ihom v).obj x
  cone := selfEnrichedPrecotensorCone V v x

lemma selfEnrichedPrecotensor_cone_eq (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [BraidedCategory V] (v x : V) : (selfEnrichedPrecotensor V v x).cone
      = curry ((β_ _ _).inv ≫ (ihom.ev v).app x) :=
  rfl

-- Develop the interal curry-uncurry isomorphism
-- This is used to show that if `V` is a symmetric closed monoidal category then, as a `V`-cateogory,
-- it admits all cotensors

/-- The currying operation taking a morphism `(z ⊗ y) ⟶ x` to a morphism `y ⟶ hom(z, x)`,
  constructed as a morphism in `V` between internal homs. -/
def internalHomCurry (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : (ihom (z ⊗ y)).obj x ⟶ (ihom y).obj ((ihom z).obj x) :=
  curry (curry ((α_ z y _).inv ≫ (ihom.ev _).app x))

lemma internalHomCurry_uncurry_eq (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V]
    [Closed z] [Closed y] [Closed (z ⊗ y)] : uncurry (internalHomCurry V z y x)
      = curry ((α_ z y _).inv ≫ (ihom.ev _).app x) :=
  uncurry_curry _

lemma internalHomCurry_uncurry_uncurry_eq (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V]
    [Closed z] [Closed y] [Closed (z ⊗ y)] : uncurry (uncurry (internalHomCurry V z y x))
      = (α_ z y _).inv ≫ (ihom.ev _).app x := by
  simp only [internalHomCurry_uncurry_eq, uncurry_curry]

/-- The uncurrying operation taking a morphism `y ⟶ hom(z, x)` to a morphism `(z ⊗ y) ⟶ x`,
  constructed as a morphism in `V` between internal homs. -/
def internalHomUncurry (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : (ihom y).obj ((ihom z).obj x) ⟶ (ihom (z ⊗ y)).obj x :=
  curry ((α_ z y _).hom ≫ z ◁ (ihom.ev y).app ((ihom z).obj x) ≫ (ihom.ev z).app x)

lemma internalHomUncurry_uncurry_eq (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V]
    [Closed z] [Closed y] [Closed (z ⊗ y)] : uncurry (internalHomUncurry V z y x)
      = (α_ z y _).hom ≫ z ◁ (ihom.ev y).app ((ihom z).obj x) ≫ (ihom.ev z).app x :=
  uncurry_curry _

theorem internalHom_uncurry_curry (V : Type u) (z x y : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : internalHomUncurry V z y x ≫ internalHomCurry V z y x = 𝟙 _ := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_id_eq_ev, internalHomCurry_uncurry_uncurry_eq]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, internalHomUncurry_uncurry_eq,
    Iso.inv_hom_id_assoc]
  exact rfl

theorem internalHom_curry_uncurry (V : Type u) (z x y : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : internalHomCurry V z y x ≫ internalHomUncurry V z y x = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_id_eq_ev, internalHomUncurry_uncurry_eq,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq,
    ← uncurry_eq, internalHomCurry_uncurry_uncurry_eq, Iso.hom_inv_id_assoc _ _]

def internalHomCurryIso (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : (ihom (z ⊗ y)).obj x ≅ (ihom y).obj ((ihom z).obj x) where
  hom := internalHomCurry V z y x
  inv := internalHomUncurry V z y x
  hom_inv_id := internalHom_curry_uncurry V z x y
  inv_hom_id := internalHom_uncurry_curry V z x y

lemma internalHomCurryIso_hom (V : Type u) (z y x : V) [Category.{u₁} V] [MonoidalCategory V] [Closed z]
    [Closed y] [Closed (z ⊗ y)] : (internalHomCurryIso V z y x).hom = internalHomCurry V z y x := rfl

@[reassoc]
def internalHomCurry_PrecotensorCone_eq (V : Type u) [Category.{u₁} V] [MonoidalCategory V]
    [MonoidalClosed V] [BraidedCategory V] (v y x : V) : internalHomCurry V v y x
      ≫ (selfEnrichedPrecotensor V v x).coneNatTrans y = (pre (β_ v y).inv).app x ≫ internalHomCurry V y v x := by
  --Unfolding
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left]
  rw [internalHomCurry_uncurry_uncurry_eq]
  rw [Precotensor.coneNatTrans_eq]
  rw [uncurry_natural_left]
  rw [uncurry_natural_left]
  erw [uncurry_curry]
  rw [compTranspose_eq]
  -- LHS
  erw [associator_inv_naturality_right_assoc]
  erw [whisker_exchange_assoc]
  erw [← uncurry_eq]
  erw [uncurry_curry]
  rw [← whiskerLeft_comp_assoc]
  erw [braiding_naturality_right]
  rw [whiskerLeft_comp_assoc]
  erw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc]
  erw [← uncurry_eq]
  erw [uncurry_curry]
  erw [braiding_inv_naturality_left_assoc]
  rw [← uncurry_eq, uncurry_curry]
  -- RHS
  rw [associator_inv_naturality_right_assoc]
  rw [id_tensor_pre_app_comp_ev]
  simp

@[reassoc]
def internalHomCurry_PrecotensorCone_reverse_eq (V : Type u) (v y x : V) [Category.{u₁} V] [MonoidalCategory V]
    [MonoidalClosed V] [e : BraidedCategory V] : internalHomCurry V v y x
      ≫ (@Precotensor.coneNatTrans V _ _ (reverseBraiding V) _ _ _ _ _ (@selfEnrichedPrecotensor V _ _ _ (reverseBraiding V) v x)) y
      = (pre (β_ y v).hom).app x ≫ internalHomCurry V y v x := by
  have p := @internalHomCurry_PrecotensorCone_eq V _ _ _ (reverseBraiding V) v y x
  have q : (BraidedCategory.braiding (self := reverseBraiding V) v y).inv = (β_ y v).hom := rfl
  rw [q] at p
  exact p

instance selfEnrichedCotensor (V : Type u) [Category.{u₁} V] [MonoidalCategory V] [MonoidalClosed V]
    [BraidedCategory V] : CotensoredCategory V V where
  cotensor v x := {
    toPrecotensor := selfEnrichedPrecotensor V v x
    coneNatTransInv := fun y => (@Precotensor.coneNatTrans V _ _ (reverseBraiding V) _ _ _ _ _ (@selfEnrichedPrecotensor V _ _ _ (reverseBraiding V) y x)) v
    NatTransInv_NatTrans_eq := fun y => by
      refine (Iso.cancel_iso_hom_left (internalHomCurryIso V y v x) _ (𝟙 ((ihom v).obj ((ihom y).obj x)))).mp ?_
      rw [internalHomCurryIso_hom]
      rw [internalHomCurry_PrecotensorCone_reverse_eq_assoc]
      rw [internalHomCurry_PrecotensorCone_eq]
      rw [← Category.assoc, ← internalHomCurryIso_hom]
      rw [← NatTrans.comp_app]
      rw [← pre_map]
      simp
    NatTrans_NatTransInv_eq := fun y => by
      refine (Iso.cancel_iso_hom_left (internalHomCurryIso V v y x) _ (𝟙 ((ihom y).obj ((ihom v).obj x)))).mp ?_
      rw [internalHomCurryIso_hom]
      rw [internalHomCurry_PrecotensorCone_eq_assoc]
      rw [internalHomCurry_PrecotensorCone_eq]
      rw [← Category.assoc, ← internalHomCurryIso_hom]
      refine ((Iso.comp_inv_eq _).mp ?_).symm
      rw [← NatTrans.comp_app]
      rw [← pre_map]
      -- have : (@BraidedCategory.braiding V _ _ (reverseBraiding V) y v).inv = (β_ v y).hom := rfl
      erw [Iso.inv_hom_id]
      simp
  }

section

variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] [SymmetricCategory V]
variable {C : Type v} [EnrichedCategory V C]

def cotensor_bifunc [CotensoredCategory V C] : EnrichedBifunctor V Vᵒᵖ C C where
  obj v x := (CotensoredCategory.cotensor v.unop x).obj
  map_left v w x := EhomPrecompose V (CotensoredCategory.cotensor w.unop x) (CotensoredCategory.cotensor v.unop x)
  map_right v x y := postcompose V (CotensoredCategory.cotensor v.unop x) (CotensoredCategory.cotensor v.unop y)
  id_left v x := precompose_id_eq V (CotensoredCategory.cotensor v.unop x)
  id_right v x := postcompose_id_eq V (CotensoredCategory.cotensor v.unop x)
  comp_left u v w x := by
      have : eComp V u v w = (β_ _ _).hom ≫ eComp V w.unop v.unop u.unop := rfl
      simp only [this, Category.assoc]
      rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
      refine ((Iso.inv_comp_eq _).mpr ?_)
      rw [← BraidedCategory.braiding_naturality_assoc]
      exact precompose_comp_eq V (CotensoredCategory.cotensor w.unop x) (CotensoredCategory.cotensor v.unop x) (CotensoredCategory.cotensor u.unop x)
  comp_right v x y z := postcompose_comp_eq V
      (CotensoredCategory.cotensor v.unop x)
      (CotensoredCategory.cotensor v.unop y)
      (CotensoredCategory.cotensor v.unop z)
  left_right_naturality w v x y := by
      rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
      exact post_pre_eq_pre_post V (CotensoredCategory.cotensor v.unop x) (CotensoredCategory.cotensor v.unop y) (CotensoredCategory.cotensor w.unop x) (CotensoredCategory.cotensor w.unop y)

end

end CategoryTheory.Enriched
