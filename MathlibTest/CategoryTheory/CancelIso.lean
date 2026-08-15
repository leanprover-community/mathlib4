import Mathlib.Tactic.CategoryTheory.CancelIso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Opposites

open CategoryTheory
open Opposite
variable {C : Type*} [Category* C]

section Basic
-- Basic cancellation
example {X Y : C} (f : X ⟶ Y) [IsIso f] : f ≫ inv f = 𝟙 _ := by simp only [cancelIso]
example {X Y : C} (f : X ⟶ Y) [IsIso f] : inv f ≫ f = 𝟙 _ := by simp only [cancelIso]

-- Associativity (Left and Right)
example {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : X ⟶ Z) : f ≫ inv f ≫ g = g := by
  simp only [cancelIso]

example {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) : inv f ≫ f ≫ g = g := by
  simp only [cancelIso]

-- Multiple cancellations in a row
example {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    f ≫ g ≫ inv g ≫ inv f = 𝟙 _ := by
  simp only [cancelIso]

example {X Y Z W : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] (h : X ⟶ W) :
    f ≫ g ≫ inv g ≫ inv f ≫ h = h := by
  simp only [cancelIso]

-- Bad associativity: expected to fail.
/-- error: `simp` made no progress -/
#guard_msgs in
example {W X Y Z : C} (a : W ⟶ X) (f : X ⟶ Y) [IsIso f] (b : X ⟶ Z) :
    (a ≫ f) ≫ inv f ≫ b = a ≫ b := by
  simp only [cancelIso]

example {W X Y Z : C} (a : W ⟶ X) (f : X ⟶ Y) [IsIso f] (b : X ⟶ Z) :
    (a ≫ f) ≫ inv f ≫ b = a ≫ b := by
  simp only [Category.assoc, cancelIso]

-- Cancellation for Iso.hom/inv
example {X Y : C} (e : X ≅ Y) : e.hom ≫ e.inv = 𝟙 _ := by simp only [cancelIso]

-- Checking if typeclass synthesis can be stuck
/--
error: `simp` made no progress
---
error: unsolved goals
case refine_2
C : Type u_1
inst✝¹ : Category.{v_1, u_1} C
X Y : C
inst✝ : ∀ (f : X ⟶ Y), IsIso f
this : ∀ (f : X ⟶ sorry) (g : sorry ⟶ X), f ≫ g = 𝟙 X
⊢ False
-/
#guard_msgs in
example {X Y : C} [∀ f : X ⟶ Y, IsIso f] : False := by
  have (f : X ⟶ ?_) (g) : f ≫ g = 𝟙 _ := by
    simp only [cancelIso]
  sorry

end Basic

section Functors
variable {T D E K L J : Type*}
  [Category* D] [Category* E] [Category* K] [Category* L] [Category* J] [Category* T]
  (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K) (I : K ⥤ L) (U : L ⥤ T)
  (η : F ≅ F)
  (K' : C ⥤ (J ⥤ D)) (ε : K' ≅ K')
  (M : C ⥤ D ⥤ E ⥤ K) (ρ : M ≅ M)

-- Standard functorial cancellation
example {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map f ≫ F.map (inv f) = 𝟙 _ := by
  simp only [cancelIso]

-- Cancellation with extra morphisms under a functor
example {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : X ⟶ Z) :
    F.map f ≫ F.map (inv f) ≫ F.map g = F.map g := by
  simp only [cancelIso]

-- Nested functors
example {X Y : C} (f : X ⟶ Y) [IsIso f] :
    G.map (F.map f) ≫ G.map (F.map (inv f)) = 𝟙 _ := by
  simp only [cancelIso]

-- nested curried functors and nested functors.
example {X : C} {Y : D} {Z : E}
    (c d : U.obj (I.obj (((M.obj X).obj Y).obj Z)) ⟶ U.obj (I.obj (((M.obj X).obj Y).obj Z))) :
    c ≫ U.map (I.map (((ρ.hom.app X).app Y).app Z)) ≫
    U.map (inv (I.map (((ρ.hom.app X).app Y).app Z))) ≫ d = c ≫ d := by
  simp only [cancelIso]

end Functors

open MonoidalCategory in
-- Nested whiskering
example {M : Type*} [Category* M] [MonoidalCategory M] {X Y : M}
    (e : X ≅ Y) (A B C D E F G H : M) :
    A ◁ B ◁ inv (C ◁ D ◁ e.inv ▷ E ▷ F ▷ G ▷ H) ≫ A ◁ B ◁ C ◁ D ◁ e.inv ▷ E ▷ F ▷ G ▷ H = 𝟙 _ := by
  simp only [cancelIso]

-- Cancellation in the opposite category
example {X Y : C} (f : X ⟶ Y) [IsIso f] : f.op.op.unop.op.op ≫ (inv f).op.op.unop.op.op = 𝟙 _ := by
  simp only [cancelIso]

open Bicategory in
example {B : Type*} [Bicategory B] {a b c d e : B} (f : a ⟶ b) {g k : b ⟶ c}
    (η : g ≅ k) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (η.inv ▷ h) ▷ i ≫ inv (f ◁ (η.inv ▷ h) ▷ i) = 𝟙 _ := by
  simp only [cancelIso]

-- CategoryStruct without a Category instance. Should make no progress but no error.
/-- error: `simp` made no progress -/
#guard_msgs in
example {B : Type*} [CategoryStruct B] {a : B} (f g h k : a ⟶ a) :
    f ≫ g ≫ h ≫ k = 𝟙 _ := by
  simp only [cancelIso]

-- Verify that `simpa` calls with MVars are fine.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
example {C : Type*} [Category* C] {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    f ≫ g ≫ h = (f ≫ g) ≫ h := by
  have foo {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : f ≫ g ≫ h = (f ≫ g) ≫ h :=
    sorry
  /- `simp only [-Category.assoc, cancelIso]` fails as expected
  `simpa only using Category.assoc _ _ _ fails` as expected
  and also fails unless the `isDefeq` calls in `cancelIso`
  are wrapped in a `withNewMCtxDepth`. -/
  simpa [-Category.assoc, cancelIso] using foo _ _ _
