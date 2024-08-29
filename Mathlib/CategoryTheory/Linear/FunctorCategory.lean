/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Mathlib.Util.CountHeartbeats
import Batteries.Tactic.ShowUnused

universe uvw -- leave this here to make some vim macros work



section Mathlib.Algebra.Group.ZeroOne

class Zero.{u} (α : Type u) where
  zero : α

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

universe u

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

end Mathlib.Algebra.Group.ZeroOne


section Mathlib.Algebra.Group.Defs

universe u v w

open Function

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

infixr:73 " • " => SMul.smul

macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

variable {G : Type u}

section Mul

variable [Mul G]

class IsLeftCancelAdd (G : Type u) [Add G] : Prop where

class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

class IsCancelAdd (G : Type u) [Add G] extends IsLeftCancelAdd G, IsRightCancelAdd G : Prop
section IsRightCancelMul

end IsRightCancelMul

end Mul

section IsRightCancelAdd

variable [Add G] [IsRightCancelAdd G] {a b c : G}

theorem add_right_cancel : a + b = c + b → a = c :=
  IsRightCancelAdd.add_right_cancel a b c

theorem add_right_cancel_iff : b + a = c + a ↔ b = c :=
  ⟨add_right_cancel, congrArg (· + a)⟩

end IsRightCancelAdd

class Semigroup (G : Type u) extends Mul G where

class AddSemigroup (G : Type u) extends Add G where
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

section AddSemigroup

variable [AddSemigroup G]

theorem add_assoc : ∀ a b c : G, a + b + c = a + (b + c) :=
  AddSemigroup.add_assoc

end AddSemigroup

section Semigroup

variable [Semigroup G]

end Semigroup

class AddCommMagma (G : Type u) extends Add G where
  protected add_comm : ∀ a b : G, a + b = b + a

class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

section AddCommMagma

variable [AddCommMagma G]

theorem add_comm : ∀ a b : G, a + b = b + a := AddCommMagma.add_comm

end AddCommMagma

class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  protected add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

class MulOneClass (M : Type u) extends One M, Mul M where

class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a

section AddZeroClass

variable {M : Type u} [AddZeroClass M]

@[simp]
theorem zero_add : ∀ a : M, 0 + a = a :=
  AddZeroClass.zero_add

@[simp]
theorem add_zero : ∀ a : M, a + 0 = a :=
  AddZeroClass.add_zero

end AddZeroClass

section

variable {M : Type u}

end

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZeroClass.toAdd

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where

section Monoid
variable {M : Type u} [AddMonoid M] {a b c : M} {m n : Nat}

theorem left_neg_eq_right_neg (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]

end Monoid

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

section LeftCancelMonoid

class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoid M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

end LeftCancelMonoid

section RightCancelMonoid

class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoid M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

end RightCancelMonoid

section CancelMonoid

class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

instance (priority := 100) AddCancelMonoid.toIsCancelAdd (M : Type u) [AddCancelMonoid M] :
    IsCancelAdd M :=
  { add_right_cancel := AddRightCancelSemigroup.add_right_cancel }

end CancelMonoid

section InvolutiveInv

class InvolutiveNeg (A : Type u) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x

variable [InvolutiveNeg G]

theorem neg_neg (a : G) : - -a = a :=
  InvolutiveNeg.neg_neg _

end InvolutiveInv

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl

section DivInvMonoid

variable [SubNegMonoid G] {a b : G}

theorem sub_eq_add_neg (a b : G) : a - b = a + -b :=
  SubNegMonoid.sub_eq_add_neg _ _

end DivInvMonoid

class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_eq_of_add (a b : G) : a + b = 0 → -a = b

section DivisionMonoid

variable [SubtractionMonoid G] {a b : G}

theorem neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b :=
  SubtractionMonoid.neg_eq_of_add _ _

theorem neg_eq_of_add_eq_zero_left (h : a + b = 0) : -b = a := by
  rw [← neg_eq_of_add_eq_zero_right h, neg_neg]

theorem eq_neg_of_add_eq_zero_left (h : a + b = 0) : a = -b :=
  (neg_eq_of_add_eq_zero_left h).symm

end DivisionMonoid

class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

section Group

variable [AddGroup G] {a b c : G}

@[simp]
theorem neg_add_cancel (a : G) : -a + a = 0 :=
  AddGroup.neg_add_cancel a

private theorem neg_eq_of_add (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h

@[simp]
theorem add_neg_cancel (a : G) : a + -a = 0 := by
  rw [← neg_add_cancel (-a), neg_eq_of_add (neg_add_cancel a)]

@[simp]
theorem add_neg_cancel_right (a b : G) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

instance (priority := 100) AddGroup.toSubtractionMonoid : SubtractionMonoid G :=
  { neg_neg := fun a ↦ neg_eq_of_add (neg_add_cancel a)
    neg_eq_of_add := fun _ _ ↦ neg_eq_of_add }

-- see Note [lower instance priority]
instance (priority := 100) AddGroup.toAddCancelMonoid (G : Type _) [AddGroup G] : AddCancelMonoid G :=
  { ‹AddGroup G› with
    add_right_cancel := fun a b c h ↦ by rw [← add_neg_cancel_right a b, h, add_neg_cancel_right] }

end Group

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

end Mathlib.Algebra.Group.Defs

universe x w v u v' u' v₁ v₂ v₃ u₁ u₂ u₃

section Mathlib.Algebra.Group.Hom.Defs.Modified

structure AddMonoidHom (M : Type u) (N : Type v) [AddMonoid M] [AddMonoid N] where
  toFun : M → N
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

infixr:25 " →+ " => AddMonoidHom

namespace AddMonoidHom

variable {M : Type u} {N : Type v}

instance [AddMonoid M] [AddMonoid N] : CoeFun (M →+ N) (fun _ => M → N) where
  coe := toFun

section

variable [AddMonoid M] [AddGroup N]

def mk' (f : M → N) (map_add : ∀ a b : M, f (a + b) = f a + f b) : M →+ N where
  toFun := f
  map_add' := map_add

end

section

variable [AddGroup M] [AddGroup N]

theorem map_zero (f : M →+ N) : f 0 = 0 := by
  have := calc 0 + f 0
            = f (0 + 0) := by simp
          _ = f 0 + f 0 := by rw [f.map_add']
  rw [add_right_cancel_iff] at this
  exact this.symm

theorem map_neg (f : M →+ N) (m : M) : f (-m) = - (f m) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← f.map_add']
  simp [f.map_zero]

theorem map_sub (f : M →+ N) (m n : M) : f (m - n) = f m - f n := by
  rw [sub_eq_add_neg, sub_eq_add_neg, f.map_add', f.map_neg]

end

end AddMonoidHom

end Mathlib.Algebra.Group.Hom.Defs.Modified

section Mathlib.Algebra.GroupWithZero.Defs

variable {G₀ : Type u} {M₀ : Type u₁} {M₀' : Type u₂} {G₀' : Type u₃}

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where

end Mathlib.Algebra.GroupWithZero.Defs


section Mathlib.Algebra.Group.Action.Defs

variable {M : Type u} {α : Type v}

class MulAction (α : Type u) (β : Type v) [Monoid α] extends SMul α β where
  protected one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

variable [Monoid M] [MulAction M α]

variable (M)

end Mathlib.Algebra.Group.Action.Defs


section Mathlib.Algebra.GroupWithZero.Action.Defs

class DistribMulAction (M : Type u) (A : Type v) [Monoid M] [AddMonoid A] extends MulAction M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

export DistribMulAction (smul_zero smul_add)

end Mathlib.Algebra.GroupWithZero.Action.Defs

section Mathlib.Algebra.Ring.Defs

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

class Distrib (R : Type u) extends Mul R, Add R where

class Semiring (α : Type u) extends AddCommMonoid α, Distrib α, Monoid α, MulZeroClass α where

end Mathlib.Algebra.Ring.Defs


section Mathlib.Algebra.Module.Defs

open Function

class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

export Module (add_smul zero_smul)

end Mathlib.Algebra.Module.Defs


section Mathlib.Combinatorics.Quiver.Basic

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

end Mathlib.Combinatorics.Quiver.Basic


section Mathlib.CategoryTheory.Category.Basic

namespace CategoryTheory

class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

scoped notation "𝟙" => CategoryStruct.id  -- type as \b1

scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

attribute [simp] Category.id_comp Category.comp_id Category.assoc

end CategoryTheory

end Mathlib.CategoryTheory.Category.Basic


section Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

section

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where

end

infixr:26 " ⥤ " => Functor -- type as \func

end CategoryTheory

end Mathlib.CategoryTheory.Functor.Basic

section Mathlib.CategoryTheory.NatTrans

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

@[ext]
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

attribute [simp] NatTrans.naturality

@[simp]
theorem NatTrans.naturality_assoc {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y) {Z : D}
    (h : G.obj Y ⟶ Z) : F.map f ≫ self.app Y ≫ h = self.app X ≫ G.map f ≫ h := by
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]

namespace NatTrans

protected def id (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := by 
    intro X Y f
    simp_all only [Category.comp_id, Category.id_comp]

@[simp]
theorem id_app' (F : C ⥤ D) (X : C) : (NatTrans.id F).app X = 𝟙 (F.obj X) := rfl

open Category

open CategoryTheory.Functor

section

variable {F G H I : C ⥤ D}

def vcomp (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := by 
    intro X Y f
    simp_all only [naturality_assoc, naturality, assoc]

theorem vcomp_app (α : NatTrans F G) (β : NatTrans G H) (X : C) :
    (vcomp α β).app X = α.app X ≫ β.app X := rfl

end

end NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.NatTrans

section Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory

open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {F G H I : C ⥤ D}

instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β
  id_comp := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', id_comp]
  comp_id := by 
    intro X Y f
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, id_app', comp_id]
  assoc := by 
    intro W X Y Z f g h
    simp_all only
    ext x : 2
    simp_all only [vcomp_app, assoc]

namespace NatTrans

-- Porting note: the behaviour of `ext` has changed here.
-- We need to provide a copy of the `NatTrans.ext` lemma,
-- written in terms of `F ⟶ G` rather than `NatTrans F G`,
-- or `ext` will not retrieve it from the cache.
@[ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

end NatTrans

open NatTrans

end CategoryTheory
end Mathlib.CategoryTheory.Functor.Category

noncomputable
section Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open scoped Classical

end Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

attribute [instance] Preadditive.homGroup

attribute [simp] Preadditive.add_comp

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] Preadditive.comp_add

end CategoryTheory

namespace CategoryTheory

namespace Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

@[simp]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

@[simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

@[simp]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

@[simp]
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

@[simp]
theorem comp_zero : f ≫ (0 : Q ⟶ R) = 0 :=
  show leftComp R f 0 = 0 from map_zero _

@[simp]
theorem zero_comp : (0 : P ⟶ Q) ≫ g = 0 :=
  show rightComp P g 0 = 0 from map_zero _

end Preadditive

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

open Preadditive

variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero :=
   { app := fun X => 0
     naturality := by 
       intro X Y f
       rw [Preadditive.comp_zero, Preadditive.zero_comp] }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β :=
  { app := fun X => α.app X + β.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_add, NatTrans.naturality, add_comp] }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α :=
  { app := fun X => -α.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_neg, NatTrans.naturality, neg_comp] }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { sub := fun α β =>
      { app := fun X => α.app X - β.app X
        naturality := by 
          intro X Y f
          simp_all only [comp_sub, NatTrans.naturality, sub_comp] }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        dsimp
        ext
        apply zero_add
      add_zero := by
        intros
        dsimp
        ext
        apply add_zero
      add_comm := by
        intros
        dsimp
        ext
        apply add_comm
      sub_eq_add_neg := by
        intros
        dsimp
        ext
        apply sub_eq_add_neg
      neg_add_cancel := by
        intros
        dsimp
        ext
        apply neg_add_cancel }
  add_comp := by
    intros
    dsimp
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp
    ext
    apply comp_add

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Linear.Basic

namespace CategoryTheory

class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

attribute [instance] Linear.homModule

end CategoryTheory

end Mathlib.CategoryTheory.Linear.Basic

-- set_option trace.profiler true
-- set_option trace.profiler.useHeartbeats true
-- set_option pp.oneline true

open CategoryTheory

namespace CategoryTheory

open Linear
open CategoryTheory.Linear

variable {R : Type u₃} [Semiring R]
variable {C : Type u₁} {D : Type u₂} [Category C] [Category D] [Preadditive D] [Linear R D]

count_heartbeats in
instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    { 
      smul := fun r α ↦ 
        { app := fun X ↦ r • α.app X
          naturality := by
            intros
            rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }
      one_smul := by
        intros
        ext
        apply MulAction.one_smul
      zero_smul := by
        intros
        ext
        apply Module.zero_smul
      smul_zero := by
        intros
        ext
        apply DistribMulAction.smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply DistribMulAction.smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

instance functorCategorySMul (F G : C ⥤ D) : SMul R (F ⟶ G) where
  smul r α := 
    { app := fun X => r • α.app X
      naturality := by
        intros
        rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }

instance functorCategoryLinear' : Linear R (C ⥤ D) where
  homModule F G :=
    { one_smul := by
        intros
        ext
        apply MulAction.one_smul
      zero_smul := by
        intros
        ext
        apply Module.zero_smul
      smul_zero := by
        intros
        ext
        apply DistribMulAction.smul_zero
      add_smul := by
        intros
        ext
        apply Module.add_smul
      smul_add := by
        intros
        ext
        apply DistribMulAction.smul_add
      mul_smul := by
        intros
        ext
        apply MulAction.mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

end CategoryTheory

/- #show_unused CategoryTheory.functorCategoryLinear -/
#show_unused CategoryTheory.functorCategoryLinear
