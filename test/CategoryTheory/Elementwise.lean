import Mathlib.Tactic.CategoryTheory.Elementwise
--import Mathlib.Algebra.Category.Mon.Basic

set_option autoImplicit true

namespace ElementwiseTest
open CategoryTheory

set_option linter.existingAttributeWarning false in
attribute [simp] Iso.hom_inv_id Iso.inv_hom_id IsIso.hom_inv_id IsIso.inv_hom_id

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

@[elementwise]
theorem ex1 [Category C] [ConcreteCategory C] (X : C) (f g h : X ⟶ X) (h' : g ≫ h = h ≫ g) :
    f ≫ g ≫ h = f ≫ h ≫ g := by rw [h']

-- If there is already a `ConcreteCategory` instance, do not add a new argument.
example : ∀ C [Category C] [ConcreteCategory C] (X : C) (f g h : X ⟶ X) (_ : g ≫ h = h ≫ g)
    (x : X), h (g (f x)) = g (h (f x)) := @ex1_apply

@[elementwise]
theorem ex2 [Category C] (X : C) (f g h : X ⟶ X) (h' : g ≫ h = h ≫ g) :
    f ≫ g ≫ h = f ≫ h ≫ g := by rw [h']

-- If there is not already a `ConcreteCategory` instance, insert a new argument.
example : ∀ C [Category C] (X : C) (f g h : X ⟶ X) (_ : g ≫ h = h ≫ g) [ConcreteCategory C]
    (x : X), h (g (f x)) = g (h (f x)) := @ex2_apply

-- Need nosimp on the following `elementwise` since the lemma can be proved by simp anyway.
@[elementwise nosimp]
theorem ex3 [Category C] {X Y : C} (f : X ≅ Y) : f.hom ≫ f.inv = 𝟙 X :=
  Iso.hom_inv_id _

example : ∀ C [Category C] (X Y : C) (f : X ≅ Y) [ConcreteCategory C] (x : X),
    f.inv (f.hom x) = x := @ex3_apply

-- Make sure there's no `id x` in there:
example : ∀ C [Category C] (X Y : C) (f : X ≅ Y) [ConcreteCategory C] (x : X),
    f.inv (f.hom x) = x := by intros; simp only [ex3_apply]

@[elementwise]
lemma foo [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

@[elementwise]
lemma foo' [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

lemma bar [Category C] [ConcreteCategory C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) : g (f x) = h x := by
  apply foo_apply w

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : M), g (f x) = h x
  exact this x

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := (elementwise_of% w) x

example [Category C] [ConcreteCategory C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : M), g (f x) = h x
  exact this x

-- `elementwise_of%` allows a level metavariable for its `ConcreteCategory` instance.
example [Category C] [ConcreteCategory C]
    (h : ∀ D [Category D] (X Y : D) (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X)
    {M N : C} {f : M ⟶ N} {g : N ⟶ M} (x : M) : g (f x) = x := by
  have := elementwise_of% h
  guard_hyp this : ∀ D [Category D] (X Y : D) (f : X ⟶ Y) (g : Y ⟶ X)
    [ConcreteCategory D] (x : X), g (f x) = x
  rw [this]

section Mon
-- TODO: switch to actual Mon when it is ported
variable (Mon : Type _) [Category Mon] [ConcreteCategory Mon]

lemma bar' {M N K : Mon} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by exact foo_apply w x

lemma bar'' {M N K : Mon} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

lemma bar''' {M N K : Mon} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

example (M N K : Mon) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [elementwise_of% w]

example (M N K : Mon) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by
  -- Porting note: did not port `elementwise!` tactic
  replace w := elementwise_of% w
  apply w

end Mon

example {α β : Type} (f g : α ⟶ β) (w : f = g) (a : α) : f a = g a := by
  -- Porting note: did not port `elementwise!` tactic
  replace w := elementwise_of% w
  guard_hyp w : ∀ (x : α), f x = g x
  rw [w]


example {α β : Type} (f g : α ⟶ β) (w : f ≫ 𝟙 β = g) (a : α) : f a = g a := by
  -- Porting note: did not port `elementwise!` tactic
  replace w := elementwise_of% w
  guard_hyp w : ∀ (x : α), f x = g x
  rw [w]

variable {C : Type*} [Category C]

def f (X : C) : X ⟶ X := 𝟙 X
def g (X : C) : X ⟶ X := 𝟙 X
def h (X : C) : X ⟶ X := 𝟙 X

lemma gh (X : C) : g X = h X := rfl

@[elementwise]
theorem fh (X : C) : f X = h X := gh X

variable (X : C) [ConcreteCategory C] (x : X)

-- Prior to https://github.com/leanprover-community/mathlib4/pull/13413 this would produce
-- `fh_apply X x : (g X) x = (h X) x`.
/-- info: fh_apply X x : (f X) x = (h X) x -/
#guard_msgs in
#check fh_apply X x

end ElementwiseTest
