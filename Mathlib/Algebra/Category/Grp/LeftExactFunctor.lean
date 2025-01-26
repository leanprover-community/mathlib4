/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence
-/

open CategoryTheory Limits

universe v v' u u'

section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

structure AbelianGroupObject (X : C) where
  m : X ⨯ X ⟶ X
  e : ⊤_ C ⟶ X
  inv : X ⟶ X
  assoc : (prod.associator X X X).hom ≫ prod.map (𝟙 X) m ≫ m = prod.map m (𝟙 X) ≫ m
  comm : (prod.braiding X X).hom ≫ m = m
  left_id : prod.lift (terminal.from X ≫ e) (𝟙 X) ≫ m = 𝟙 X
  right_id : prod.lift (𝟙 X) (terminal.from X ≫ e) ≫ m = 𝟙 X
  left_inv : prod.lift inv (𝟙 X) ≫ m = terminal.from _ ≫ e
  right_inv : prod.lift (𝟙 X) inv ≫ m = terminal.from _ ≫ e

  -- -- assoc : m ≫ m = (prod.fst ≫ m) ≫ m ≫ m
  -- comm : m = m ≫ (prod.snd ≫ prod.fst)
  -- left_id : (e ≫ prod.fst) ≫ m = prod.snd
  -- right_id : (prod.fst ≫ e) ≫ m = prod.fst
  -- left_inv : (inv ≫ prod.fst) ≫ m = e
  -- right_inv : (prod.fst ≫ inv) ≫ m = e

-- structure InternalAddCommGrp (X : C) where
--   presheaf : Cᵒᵖ ⥤ AddCommGrp.{v}
--   iso : presheaf ⋙ forget _ ≅ yoneda.obj X

-- def add {X : Type v} (G : InternalAddCommGrp X) : X × X → X :=
--   fun x y => _

-- variable {D : Type u} [Category.{v} D] (F : C ⥤ D) [PreservesFiniteLimits F]

-- def InternalAddCommGrp.map {X : C} (G : InternalAddCommGrp X) : InternalAddCommGrp (F.obj X) where
--   presheaf := sorry
--   iso := sorry

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable def Preadditive.abelianGroupObject (X : C) : AbelianGroupObject X where
  m := prod.fst + prod.snd
  e := IsZero.to_ (IsZero.of_mono_zero (⊤_ C) X) _
  inv := -𝟙 X
  assoc := by
    rw [← cancel_epi (biprod.isoProd _ _).hom]
    simp [add_assoc]
  comm := by
    rw [← cancel_epi (biprod.isoProd _ _).hom]
    simp [add_comm]
  left_id := by simp [IsZero.to_eq _ 0]
  right_id := by simp [IsZero.to_eq _ 0]
  left_inv := by simp [IsZero.to_eq _ 0]
  right_inv := by simp [IsZero.to_eq _ 0]

end

section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F]

noncomputable def Functor.mapAbelianGroupObject {X : C} (G : AbelianGroupObject X) :
    AbelianGroupObject (F.obj X) where
  m := (PreservesLimitPair.iso F X X).inv ≫ F.map G.m
  e := (PreservesTerminal.iso F).inv ≫ F.map G.e
  inv := sorry
  assoc := sorry
  comm := sorry
  left_id := sorry
  right_id := sorry
  left_inv := sorry
  right_inv := sorry

end

namespace AbelianGroupObject.Types

section

noncomputable def add {X : Type v} (G : AbelianGroupObject X) : Add X where
  add x y := G.m ((Types.binaryProductIso _ _).inv (x, y))

noncomputable def neg {X : Type v} (G : AbelianGroupObject X) : Neg X where
  neg x := G.inv x

noncomputable def zero {X : Type v} (G : AbelianGroupObject X) : Zero X where
  zero := G.e default

protected theorem add_comm {X : Type v} (G : AbelianGroupObject X) (x y : X) :
    letI : Add X := add G
    x + y = y + x := by
  dsimp only [(· + ·)]
  rw [Add.add, add]
  simp only
  conv_lhs => rw [← G.comm]
  simp
  apply congr_arg G.m
  apply (Types.binaryProductIso _ _).toEquiv.injective
  ext
  · simp [elementwise_of% (prod.lift_fst (prod.snd : X ⨯ X ⟶ X) prod.fst)]
  · simp [elementwise_of% (prod.lift_snd (prod.snd : X ⨯ X ⟶ X) prod.fst)]

end

end AbelianGroupObject.Types

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

variable (F : C ⥤ Type v) [PreservesFiniteLimits F]

section

variable (X : C)

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

#check F.map <| Limits.biprod.desc (𝟙 X) (𝟙 X)

def addCommGroup : AddCommGroup (F.obj X) := sorry

end

def lift (F : C ⥤ Type v) : C ⥤ AddCommGrp.{v} := sorry

def liftCompForget (F : C ⥤ Type v) : lift F ⋙ forget _ ≅ F := sorry

instance : PreservesFiniteLimits (lift F) := sorry

def liftIso :
    ((LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget AddCommGrp))).obj
      (LeftExactFunctor.of (lift F)) ≅ LeftExactFunctor.of F :=
  InducedCategory.isoMk (liftCompForget F)

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

section

variable (F : C ⥤ AddCommGrp.{v}) [PreservesFiniteLimits F] (X : C)

def q : F.obj X ≅ @AddCommGrp.of ((F ⋙ forget _).obj X) (addCommGroup (F ⋙ forget _) X) := sorry

end

instance : Functor.IsEquivalence <|
    (LeftExactFunctor.whiskeringRight C _ _).obj ⟨forget AddCommGrp.{v}, inferInstance⟩ where
  full := sorry
  faithful := sorry
  essSurj := ⟨(⟨_, ⟨liftIso ·.1⟩⟩)⟩

end
