/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/

module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Enriched.TensorProductCategory

universe u u₁ v w

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory SymmetricCategory

open scoped MonoidalClosed

/- My own namesapce for experimenting with enriched categories -/
namespace myEnrichedCategories

-- Playing with instances

noncomputable example : MonoidalCategory SSet.{v} := by infer_instance

noncomputable example : EnrichedCategory SSet.{v} SSet.{v} := by infer_instance

example {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] : EnrichedCategory V V := by infer_instance

noncomputable example : EnrichedCategory SSet.{v} SSet.{v} := by infer_instance

abbrev Ihom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] (x y : V) : V :=
  (ihom x).obj y

-- The variable V is explicit here since trying to make it implicit throws errors in practice
abbrev Ehom (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (C : Type v) [EnrichedCategory V C] (x y : C) : V :=
  @EnrichedCategory.Hom V _ _ _ _ x y

def Ihom_NatTrans_NatTransInv_eq (V : Type u) [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]
    (x y : V) : Ihom V x y = Ehom V V x y :=
  rfl

-- New stuff
variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
variable {C : Type v} [EnrichedCategory V C]

example {x y z : V} {f f' : x ⟶ y} {g g' : y ⟶ z} : (f = f') → (g = g') → (x ◁ f ≫ x ◁ g = x ◁ f' ≫ x ◁ g') := by
  intro p q
  rw [p, q]

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

instance {v : V} {x : C} {vx : Cotensor v x} {y : C} : IsIso (vx.coneNatTransInv y) where
  out := ⟨vx.coneNatTrans y, {
    left := vx.NatTransInv_NatTrans_eq y
    right := vx.NatTrans_NatTransInv_eq y
  }⟩

instance {v : V} {x : C} {vx : Cotensor v x} {y : C} : IsIso (vx.coneNatTrans y) where
  out := ⟨vx.coneNatTransInv y, {
    left := vx.NatTrans_NatTransInv_eq y
    right := vx.NatTransInv_NatTrans_eq y
  }⟩

end myEnrichedCategories

open myEnrichedCategories

/- My own namespace for proving things about cotensors -/
namespace Cotensor

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
    (postcompose V vx vy ▷ _) ≫ (_ ◁ vy.cone) ≫ (eComp V vx.obj vy.obj y)
      = (β_ v _).inv ≫ (vx.cone ▷ _) ≫ (eComp V vx.obj x y) := by
  rw [← vy.coneNatTrans_braid_eq, braiding_inv_naturality_left_assoc]
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
      (postcompose V vx vy ⊗ postcompose V vy vz) ≫ eComp V _ _ _ := by
  -- Work the LHS
  apply (cancel_mono (vz.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [Category.assoc]
  rw [uncurry_natural_left]
  rw [uncurry_postcompose_coneNatTrans_eq]
  -- This final exchange solves at the end
  rw [whisker_exchange_assoc]

  -- Work the RHS
  simp only [tensorHom_def, uncurry_natural_left,
    MonoidalCategory.whiskerLeft_comp, vz.coneNatTrans_eq, Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [braiding_naturality_right_assoc]
  nth_rw 2 [← whisker_exchange_assoc]
  simp only [braiding_tensor_right, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← associator_inv_naturality_right_assoc]
  rw [e_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  -- This invokes commutativity of post with selfEval
  simp only [Category.assoc, postcompose_selfEval_comp_eq,
    MonoidalCategory.whiskerLeft_comp]
  -- Now we can use symmetry
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- Moving a morphism through a bunch of associators and braids >_>
  rw [associator_inv_naturality_middle_assoc]
  -- Annoying
  rw [← comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [comp_whiskerRight_assoc]
  --
  rw [← associator_naturality_middle_assoc]
  --
  rw [(e_assoc' V vx.obj vy.obj y z)]
  --
  nth_rw 3 [← comp_whiskerRight_assoc]
  nth_rw 2 [← comp_whiskerRight_assoc]
  simp only [postcompose_selfEval_comp_eq, comp_whiskerRight, Category.assoc]
  -- Take out the symmetry
  rw [← comp_whiskerRight_assoc]
  simp only [Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  -- All posts are gone from the equation
  rw [← associator_inv_naturality_left_assoc]
  rw [e_assoc]

theorem postcompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V x ≫ postcompose V vx vx = eId V vx.obj := by
  -- These lines are copied from the last proof - consider isolating!
  apply (cancel_mono (vx.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [Category.assoc]
  rw [uncurry_natural_left]
  rw [uncurry_postcompose_coneNatTrans_eq]
  -- This is copied from the RHS part of the previous proof
  simp only [uncurry_natural_left, MonoidalCategory.whiskerLeft_comp,
    vx.coneNatTrans_eq, Category.assoc]
  simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
    Category.assoc]
  -- Braiding has been replaced by unitors
  apply (Iso.inv_comp_eq _).mp
  -- Moving selfEval up on the LHS
  rw [whisker_exchange_assoc]
  rw [← rightUnitor_inv_naturality_assoc]
  -- Moving up selfEval on the RHS
  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  -- Final step
  rw [e_id_comp, e_comp_id]

lemma IhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    (IhomPrecompose V wx vx) ▷ _ ≫ (_ ◁ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).inv ≫ (ihom.ev w).app v ≫ vx.cone := by
  rw [← ihom.ev_naturality]
  rw [← braiding_inv_naturality_left_assoc]
  unfold IhomPrecompose
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  apply whisker_eq
  apply (cancel_epi ((wx.coneNatTrans _) ▷ w)).mp
  rw [← comp_whiskerRight_assoc]
  simp only [wx.NatTrans_NatTransInv_eq, id_whiskerRight, Category.id_comp]
  rw [braiding_inv_naturality_left_assoc]
  rw [← uncurry_eq]
  exact (Precotensor.coneNatTrans_braid_eq wx.toPrecotensor vx.obj).symm

lemma EhomPrecompose_selfEval_comp_eq {x : C} {w v : V} (wx : Cotensor w x) (vx : Cotensor v x) :
    (EhomPrecompose V wx vx) ▷ _ ≫ (_ ◁ wx.cone) ≫ eComp V _ _ _
      = (β_ _ _).inv ≫ (ihom.ev w).app v ≫ vx.cone :=
  IhomPrecompose_selfEval_comp_eq V wx vx

-- Functoriality of precomposition
theorem precompose_comp_eq {x : C} {u v w : V} (ux : Cotensor u x) (vx : Cotensor v x)
    (wx : Cotensor w x) : eComp V u v w ≫ EhomPrecompose V ux wx =
      (EhomPrecompose V ux vx ⊗ EhomPrecompose V vx wx) ≫ (β_ _ _).hom ≫ eComp V _ _ _ := by
  apply (cancel_mono (ux.coneNatTrans _)).mp
  simp only [Category.assoc]
  rw [EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  simp only [uncurry_natural_left]
  rw [ux.coneNatTrans_eq]
  -- Moving comp to after selfEval
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  -- Moving Precompose down to comp
  simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
  -- Annoying move again
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_left]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [braiding_naturality_right_assoc]
  simp only [braiding_tensor_right, whisker_assoc, tensor_whiskerLeft,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [e_assoc]
  nth_rw 4 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 3 [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [EhomPrecompose_selfEval_comp_eq, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  -- Another very bad
  have : (β_ u (Ehom V V u v)).hom = (β_ u ((ihom u).obj v)).hom := rfl
  rw [this]
  rw [Iso.hom_inv_id]
  --
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- The lemma again
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]
  -- and again...
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  --
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [EhomPrecompose_selfEval_comp_eq]

  -- There are no more pre's in the equation
  --Very bad
  have : (β_ v ((ihom v).obj w)).inv = (β_ v (Ehom V V v w)).inv := rfl
  rw [this]
  --
  rw [braiding_inv_naturality_right_assoc]
  simp only [braiding_inv_tensor_left]
  simp only [Functor.id_obj, Category.assoc]
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc]
  simp only [Iso.hom_inv_id]
  simp only [id_whiskerRight]
  simp only [Category.id_comp]
  simp only [Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- Forced to unfold uncurry
  rw [uncurry_eq]
  rw [(ihom.ev_naturality u)]
  -- lemma about the enriched structure on V
  have : eComp V u v w = comp u v w := rfl
  rw [this]
  have : u ◁ comp u v w ≫ (ihom.ev u).app w
    = uncurry (comp u v w) := rfl
  have := eq_whisker this wx.cone
  simp only [Category.assoc] at this
  rw [this]
  rw [comp_eq]
  rw [uncurry_curry]
  rw [compTranspose_eq]
  simp only [Category.assoc]
  exact rfl

theorem precompose_id_eq {x : C} {v : V} (vx : Cotensor v x) :
    eId V v ≫ EhomPrecompose V vx vx = eId V vx.obj := by
  -- Copied from the last proof
  apply (cancel_mono (vx.coneNatTrans _)).mp
  simp only [Category.assoc]
  rw [EhomPrecompose_coneNatTrans_eq]
  apply uncurry_injective
  simp only [uncurry_natural_left]
  rw [vx.coneNatTrans_eq]
  simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
    Category.assoc]
  rw [uncurry_eq]

  -- apply (Iso.inv_comp_eq _).mp
  -- Moving selfEval up on the LHS
  -- rw [whisker_exchange_assoc]
  -- rw [← rightUnitor_inv_naturality_assoc]
  -- Moving up selfEval on the RHS
  rw [← whisker_exchange_assoc]
  rw [← leftUnitor_inv_naturality_assoc]
  simp only [e_id_comp, Category.comp_id]
  rw [ihom.ev_naturality]

  -- Annoying
  have : eId V v = MonoidalClosed.id v := rfl
  rw [this]
  -- Even more annoying - this came up in the enriched thing!
  rw [MonoidalClosed.id_eq]
  have := uncurry_eq (curry (ρ_ v).hom)
  have := eq_whisker this.symm vx.cone
  simp only [Category.assoc] at this
  rw [this]
  --
  rw [uncurry_curry]

/-- Commutativity of postcomposition with precoposition -/
theorem post_pre_eq_pre_post {x y : C} {w v : V} (wx : Cotensor w x) (wy : Cotensor w y)
    (vx : Cotensor v x) (vy : Cotensor v y) :
  (EhomPrecompose V wx vx ⊗ postcompose V wx wy) ≫ eComp V vx.obj wx.obj wy.obj =
    (EhomPrecompose V wy vy ⊗ postcompose V vx vy) ≫ (β_ _ _).hom
      ≫ eComp V vx.obj vy.obj wy.obj := by
  -- Turn EHom to IHom, uncurry, and simplify the result
  apply (cancel_mono (wy.coneNatTrans _)).mp
  apply uncurry_injective
  simp only [uncurry_natural_left]
  unfold Precotensor.coneNatTrans
  rw [uncurry_curry]
  rw [MonoidalCategory.tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

  -- Remove post w from the LHS
  rw [braiding_naturality_right_assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  -- simp only [MonoidalCategory.comp_whiskerRight]
  -- simp only [Category.assoc]

  rw [← (e_assoc' V vx.obj wx.obj wy.obj y)]

  rw [associator_naturality_right_assoc]
  rw [associator_naturality_middle_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [postcompose_selfEval_comp_eq]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

  -- Remove pre x from the LHS
  rw [braiding_tensor_right_assoc]
  rw [Iso.inv_hom_id_assoc]
  -- This uses the symmetry!
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Iso.hom_inv_id, whiskerLeft_id_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]
  -- Candidate for moving to its own lemma
  rw [← comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [comp_whiskerRight_assoc]
  --
  rw [← (e_assoc V vx.obj wx.obj x y)]
  rw [← whisker_assoc_assoc]
  repeat rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [EhomPrecompose_selfEval_comp_eq]

  -- Remove pre y from the RHS
  rw [MonoidalCategory.tensorHom_def']
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [braiding_naturality_right_assoc]
  rw [← whisker_exchange_assoc]
  rw [← e_assoc']
  rw [associator_naturality_right_assoc]
  rw [braiding_tensor_right_assoc]
  rw [Iso.inv_hom_id_assoc]
  -- Candidate for moving to its own lemma
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_left]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [associator_naturality_right_assoc]
  -- Candidate for moving to its own lemma
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  --
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [EhomPrecompose_selfEval_comp_eq]
  -- Very bad
  have u : (β_ w ((ihom w).obj v)).inv = (β_ w (Ehom V V w v)).inv := rfl
  rw [u]
  rw [Iso.hom_inv_id_assoc]
  --
  rw [Iso.hom_inv_id_assoc]
  simp only [Functor.id_obj, comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp]


  -- Remove post x from the RHS
  -- simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  -- Candidate again...
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  --
  rw [associator_inv_naturality_middle_assoc]

  -- Candidate on the right
  nth_rw 2 [← MonoidalCategory.comp_whiskerRight_assoc]
  rw [braiding_naturality_right]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  -- --
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc]
  -- simp only [Functor.id_obj]
  -- -- Weakened assumptions to braiding only, and this additional step popped up
  -- rw [← whisker_exchange_assoc]
  -- rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  -- rw [Iso.hom_inv_id]
  -- simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- rw [← whisker_exchange_assoc]
  -- --
  rw [postcompose_selfEval_comp_eq]

  -- -- There are no more post's or pre's in the equation
  -- -- Braiding assumption: New end to proof
  -- simp only [comp_whiskerRight]
  rw [braiding_inv_naturality_right_assoc]
  -- apply (Iso.inv_comp_eq _).mpr
  -- rw [← braiding_inv_tensor_left_assoc]
  -- have : (β_ (w ⊗ (ihom w).obj v) (Ehom V C x y)).inv = (β_ (w ⊗ Ehom V V w v) (Ehom V C x y)).inv := rfl
  -- rw [this]
  -- rw [Iso.hom_inv_id_assoc]
  -- exact Category.assoc _ _ _
  simp only [braiding_inv_tensor_left, Category.assoc, Iso.hom_inv_id_assoc,
    hom_inv_whiskerRight_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]

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
  simp only [uncurry_natural_left]
  have : (a b c : V) → (eComp V a b c) = MonoidalClosed.comp a b c := fun a b c => rfl
  rw [this]
  rw [MonoidalClosed.comp_eq]
  rw [uncurry_curry]
  rw [compTranspose_eq]

  -- LHS
  have : (EnrichedCategory.Hom y (selfEnrichedPrecotensor V v x).obj) ◁ (selfEnrichedPrecotensor V v x).cone = ((ihom y).obj _) ◁ (selfEnrichedPrecotensor V v x).cone := rfl
  rw [this]
  have : (a b : V) → (α_ a b ((ihom (selfEnrichedPrecotensor V v x).obj).obj x)).inv = (α_ a b (Ehom V V (selfEnrichedPrecotensor V v x).obj x)).inv := fun a b => rfl
  rw [this]
  rw [associator_inv_naturality_right_assoc]
  have : (w : V) → (f : (y ⊗ (ihom y).obj (selfEnrichedPrecotensor V v x).obj) ⟶ w) → (f ▷ (ihom (selfEnrichedPrecotensor V v x).obj).obj x = f ▷ Ehom V V (selfEnrichedPrecotensor V v x).obj x) := fun w f => rfl
  rw [this]
  rw [whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [← uncurry_eq]

  rw [selfEnrichedPrecotensor_cone_eq]
  rw [uncurry_curry]
  have : (β_ v ((ihom v).obj x)).inv = (β_ v ((selfEnrichedPrecotensor V v x).obj)).inv := rfl
  rw [this]
  rw [braiding_inv_naturality_left_assoc]
  simp only [braiding_inv_tensor_right_assoc, Iso.inv_hom_id_assoc]
  nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
  have : β_ v (EnrichedCategory.Hom y (selfEnrichedPrecotensor V v x).obj) = β_ v ((ihom y).obj (selfEnrichedPrecotensor V v x).obj) := rfl
  rw [this]
  rw [Iso.hom_inv_id]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]

  -- RHS
  rw [associator_inv_naturality_right_assoc]
  rw [id_tensor_pre_app_comp_ev]

  refine ((Iso.inv_comp_eq _).mpr ?_).symm
  rw [← associator_naturality_right_assoc]
  have : α_ y v ((ihom y).obj (selfEnrichedPrecotensor V v x).obj) = α_ y v ((ihom y).obj ((ihom v).obj x)) := rfl
  rw [this]
  rw [Iso.hom_inv_id_assoc]
  have : (β_  v y).inv ▷ (ihom y).obj (selfEnrichedPrecotensor V v x).obj = (β_ v y).inv ▷ ((ihom y).obj ((ihom v).obj x)) := rfl
  rw [this]
  rw [whisker_exchange_assoc]
  refine (β_ v y).inv ▷ (ihom (v ⊗ y)).obj x ≫= ?_
  have : α_ v y ((ihom y).obj (selfEnrichedPrecotensor V v x).obj) = α_ v y ((ihom y).obj ((ihom v).obj x)) := rfl
  rw [this]
  rw [associator_naturality_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have : (ihom.ev y).app (selfEnrichedPrecotensor V v x).obj = (ihom.ev y).app ((ihom v).obj x) := rfl
  rw [this]
  rw [← uncurry_eq]
  rw [← uncurry_eq]
  rw [internalHomCurry_uncurry_uncurry_eq]
  rw [Iso.hom_inv_id_assoc]

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
      rw [Category.comp_id]
      rw [internalHomCurryIso_hom]
      rw [internalHomCurry_PrecotensorCone_reverse_eq_assoc]
      rw [internalHomCurry_PrecotensorCone_eq]
      rw [← Category.assoc, ← internalHomCurryIso_hom]
      refine ((Iso.comp_inv_eq _).mp ?_).symm
      rw [Iso.hom_inv_id]
      rw [← NatTrans.comp_app]
      rw [← pre_map]
      simp only [Iso.inv_hom_id, pre_id, NatTrans.id_app]
    NatTrans_NatTransInv_eq := fun y => by
      refine (Iso.cancel_iso_hom_left (internalHomCurryIso V v y x) _ (𝟙 ((ihom y).obj ((ihom v).obj x)))).mp ?_
      rw [Category.comp_id]
      rw [internalHomCurryIso_hom]
      rw [internalHomCurry_PrecotensorCone_eq_assoc]
      rw [internalHomCurry_PrecotensorCone_eq]
      rw [← Category.assoc, ← internalHomCurryIso_hom]
      refine ((Iso.comp_inv_eq _).mp ?_).symm
      rw [Iso.hom_inv_id]
      rw [← NatTrans.comp_app]
      rw [← pre_map]
      have : (@BraidedCategory.braiding V _ _ (reverseBraiding V) y v).inv = (β_ v y).hom := rfl
      simp only [this, Iso.hom_inv_id, pre_id, NatTrans.id_app]
  }

open CotensoredCategory

section

variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V] [SymmetricCategory V]
variable {C : Type v} [EnrichedCategory V C]

-- (wx : Cotensor w x) : eComp V u v w ≫ EhomPrecompose V ux wx =
--   (EhomPrecompose V ux vx ⊗ EhomPrecompose V vx wx) ≫ (β_ _ _).hom ≫ eComp V _ _ _ :

def cotensor_bifunc [CotensoredCategory V C] : EnrichedBifunctor V Vᵒᵖ C C where
  obj v x := (cotensor v.unop x).obj
  map_left v w x := EhomPrecompose V (cotensor w.unop x) (cotensor v.unop x)
  map_right v x y := postcompose V (cotensor v.unop x) (cotensor v.unop y)
  id_left v x := precompose_id_eq V (cotensor v.unop x)
  id_right v x := postcompose_id_eq V (cotensor v.unop x)
  comp_left u v w x := by
      have : eComp V u v w = (β_ _ _).hom ≫ eComp V w.unop v.unop u.unop := rfl
      simp only [this, Category.assoc]
      rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
      refine ((Iso.inv_comp_eq _).mpr ?_)
      rw [← BraidedCategory.braiding_naturality_assoc]
      exact precompose_comp_eq V (cotensor w.unop x) (cotensor v.unop x) (cotensor u.unop x)
  comp_right v x y z := postcompose_comp_eq V
      (cotensor v.unop x)
      (cotensor v.unop y)
      (cotensor v.unop z)
  left_right_naturality w v x y := by
      rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
      exact post_pre_eq_pre_post V (cotensor v.unop x) (cotensor v.unop y) (cotensor w.unop x) (cotensor w.unop y)
  -- have := post_pre_eq_pre_post V
  --     (cotensor v.unop x)
  --     (cotensor v.unop y)
  --     (cotensor w.unop x)
  --     (cotensor w.unop y)

-- def cotensor_bifunc [CotensoredCategory V C] : EnrichedFunctor V (Vᵒᵖ × C) C :=
--   enrichedBifunctor.mk V Vᵒᵖ C
--     (fun v x ↦ (cotensor v.unop x).obj)
--     (fun v w x ↦ EhomPrecompose V (cotensor w.unop x) (cotensor v.unop x))
--     (fun v x y ↦ postcompose V (cotensor v.unop x) (cotensor v.unop y))
--     (fun v x ↦ precompose_id_eq V (cotensor v.unop x))
--     (fun v x ↦ postcompose_id_eq V (cotensor v.unop x))
--     (fun u v w x ↦ by
--       have : eComp V u v w = (β_ _ _).hom ≫ eComp V w.unop v.unop u.unop := rfl
--       simp only [this, Category.assoc]

--       -- rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
--       refine ((Iso.inv_comp_eq _).mp ?_).symm
--       rw [← BraidedCategory.braiding_inv_naturality_assoc]
--       exact precompose_comp_eq V
--         (cotensor w.unop x) (cotensor v.unop x) (cotensor u.unop x))
--     (fun v x y z ↦ postcompose_comp_eq V
--       (cotensor v.unop x)
--       (cotensor v.unop y)
--       (cotensor v.unop z))
--     (fun w v x y ↦ post_pre_eq_pre_post V
--       (cotensor v.unop x)
--       (cotensor v.unop y)
--       (cotensor w.unop x)
--       (cotensor w.unop y))

end

end Cotensor
