/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Products in `Type`

We describe arbitrary products in the category of types, as well as binary products,
and the terminal object.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

example : HasProducts.{v} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasProducts.{v} (Type u) := inferInstance

-- This shortcut instance is required in `Mathlib/CategoryTheory/Closed/Types.lean`,
-- although I don't understand why, and wish it wasn't.
instance : HasProducts.{v} (Type v) := inferInstance

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`. -/
-- The increased `@[simp]` priority here results in a minor speed up in
-- `Mathlib/CategoryTheory/Sites/EqualizerSheafCondition.lean`.
@[simp 1001]
theorem pi_lift_π_apply {β : Type v} [Small.{u} β] (f : β → Type u) {P : Type u}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  ConcreteCategory.congr_hom (limit.lift_π (Fan.mk P s) ⟨b⟩) x

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`,
with specialized universes. -/
theorem pi_lift_π_apply' {β : Type v} (f : β → Type v) {P : Type v}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    Pi.π f b (@Pi.lift β _ _ f _ P s x) = s b x := by
  simp

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`. -/
-- Not `@[simp]` since `simp` can prove it.
theorem pi_map_π_apply {β : Type v} [Small.{u} β] {f g : β → Type u}
    (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    Pi.π g b (Pi.map α x) = α b ((Pi.π f b) x) :=
  limMap_π_apply _ _ _

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`,
with specialized universes. -/
theorem pi_map_π_apply' {β : Type v} {f g : β → Type v} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    Pi.π g b (Pi.map α x) = α b ((Pi.π f b) x) := by
  simp [pi_map_π_apply]

/-- The terminal object in `Type u` is `PUnit`. -/
def isTerminalPUnit : IsTerminal (PUnit : Type u) :=
  letI (X : Type u) : Unique (X ⟶ PUnit) := TypeCat.homEquiv.unique
  .ofUnique _

@[simp]
lemma isTerminalPUnit_from_apply {X : Type u} (x : X) : isTerminalPUnit.from X x = .unit := rfl

@[deprecated (since := "2026-02-08")] alias isTerminalPunit := isTerminalPUnit

/-- The category of types has `PUnit` as a terminal object. -/
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) := ⟨_, isTerminalPUnit⟩

/-- The terminal object in `Type u` is `PUnit`. -/
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit

/-- A type is terminal if and only if it contains exactly one element. -/
def isTerminalEquivUnique (X : Type u) : IsTerminal X ≃ Unique X :=
  equivOfSubsingletonOfSubsingleton
    (fun h => (IsTerminal.uniqueUpToIso h isTerminalPUnit).toEquiv.unique)
    (fun _ => IsTerminal.ofIso isTerminalPUnit (Equiv.toIso (Equiv.ofUnique _ _)))

/-- A type is terminal if and only if it is isomorphic to `PUnit`. -/
def isTerminalEquivIsoPUnit (X : Type u) : IsTerminal X ≃ (X ≅ PUnit) := by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso

noncomputable instance : Unique (⊤_ (Type u)) := isTerminalEquivUnique _ terminalIsTerminal

open CategoryTheory.Limits.WalkingPair

-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps! pt]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk (TypeCat.ofHom _root_.Prod.fst) (TypeCat.ofHom _root_.Prod.snd)

@[simp]
theorem binaryProductCone_fst (X Y : Type u) :
    (binaryProductCone X Y).fst = TypeCat.ofHom _root_.Prod.fst :=
  rfl

@[simp]
theorem binaryProductCone_snd (X Y : Type u) :
    (binaryProductCone X Y).snd = TypeCat.ofHom _root_.Prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) := TypeCat.ofHom (fun x => (s.fst x, s.snd x))
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext x
    apply Prod.ext
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) x, ConcreteCategory.congr_hom (w ⟨right⟩) x]

/-- The category of types has `X × Y`, the usual Cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

/-- The categorical binary product in `Type u` is Cartesian product. -/
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ TypeCat.ofHom _root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ TypeCat.ofHom _root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.fst = TypeCat.ofHom _root_.Prod.fst :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.snd = TypeCat.ofHom _root_.Prod.snd :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps]
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj X :=
    { obj := fun Y => X × Y
      map := fun {_ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk (TypeCat.ofHom _root_.Prod.fst) (TypeCat.ofHom _root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      (binaryProductLimit X₂ Y).lift (BinaryFan.mk (TypeCat.ofHom _root_.Prod.fst ≫ f)
      (TypeCat.ofHom _root_.Prod.snd)) }

set_option backward.isDefEq.respectTransparency false in
/-- The product functor given by the instance `HasBinaryProducts (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binaryProductIsoProd :
    binaryProductFunctor ≅ (prod.functor : Type u ⥤ _) := by
  refine NatIso.ofComponents (fun X => ?_) (fun _ => ?_)
  · refine NatIso.ofComponents (fun Y => ?_) (fun _ => ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl

/--
The category of types has `Π j, f j` as the product of a type family `f : J → Type max v u`.
-/
def productLimitCone {J : Type v} (F : J → Type (max v u)) :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := (∀ j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ => TypeCat.ofHom (fun f => f j)) }
  isLimit :=
    { lift := fun s => TypeCat.ofHom fun x j => s.π.app ⟨j⟩ x
      uniq := fun _ _ w => by
        ext x j
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

/-- The categorical product in `Type max v u` is the type-theoretic product `Π j, F j`. -/
noncomputable def productIso {J : Type v} (F : J → Type (max v u)) :
    ∏ᶜ F ≅ (∀ j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)

@[elementwise (attr := simp)]
theorem productIso_hom_comp_eval {J : Type v} (F : J → Type (max v u)) (j : J) :
    (productIso.{v, u} F).hom ≫ TypeCat.ofHom (fun f => f j) = Pi.π F j := by
  rfl

-- -- Used to be generated by `elementwise`
-- @[simp]
-- theorem productIso_hom_comp_eval_apply {J : Type v} (F : J → Type (max v u)) (j : J)
--     (x : ∏ᶜ F) : (Types.productIso F).hom x j = Pi.π F j x :=
--   rfl

@[elementwise (attr := simp)]
theorem productIso_inv_comp_π {J : Type v} (F : J → Type max v u) (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = TypeCat.ofHom fun f => f j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

namespace Small

variable {J : Type v} (F : J → Type u) [Small.{u} J]

set_option backward.defeqAttrib.useBackward true in
/--
A variant of `productLimitCone` using a `Small` hypothesis rather than a function to `Type`.
-/
noncomputable def productLimitCone :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := Shrink (∀ j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ =>
        TypeCat.ofHom (fun f => (equivShrink (∀ j, F j)).symm f j)) }
  isLimit :=
    have : Small.{u} (∀ j, F j) := inferInstance
    { lift := fun s => TypeCat.ofHom fun x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => ConcreteCategory.hom_ext _ _ fun x => Shrink.ext (funext fun j => by
        simpa using ConcreteCategory.congr_hom (w ⟨j⟩) x) }

/-- The categorical product in `Type u` indexed in `Type v`
is the type-theoretic product `Π j, F j`, after shrinking back to `Type u`. -/
noncomputable def productIso :
    (∏ᶜ F : Type u) ≅ Shrink (∀ j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)

@[elementwise (attr := simp)]
theorem productIso_hom_comp_eval (j : J) :
    (productIso.{v, u} F).hom ≫ TypeCat.ofHom (fun f => (equivShrink (∀ j, F j)).symm f j) =
      Pi.π F j :=
  limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩

@[elementwise (attr := simp)]
theorem productIso_inv_comp_π (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j =
      TypeCat.ofHom (fun f => ((equivShrink (∀ j, F j)).symm f) j) :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

end Small

end CategoryTheory.Limits.Types
