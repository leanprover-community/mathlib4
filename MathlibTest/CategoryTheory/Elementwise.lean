import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Algebra.Category.MonCat.Basic

set_option autoImplicit true

namespace ElementwiseTest
open CategoryTheory

namespace HasForget

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id IsIso.hom_inv_id IsIso.inv_hom_id

@[elementwise]
theorem ex1 {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (X : C)
    (f g h : X ⟶ X) (h' : g ≫ h = h ≫ g) :
    f ≫ g ≫ h = f ≫ h ≫ g := by rw [h']

-- If there is already a `ConcreteCategory` instance, do not add a new argument.
example : ∀ {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (X : C)
    (f g h : X ⟶ X) (_ : g ≫ h = h ≫ g)
    (x : ToType X), h (g (f x)) = g (h (f x)) := @ex1_apply

@[elementwise]
theorem ex2 [Category C] (X : C) (f g h : X ⟶ X) (h' : g ≫ h = h ≫ g) :
    f ≫ g ≫ h = f ≫ h ≫ g := by rw [h']

-- If there is not already a `ConcreteCategory` instance, insert a new argument.
example : ∀ C [Category C] (X : C) (f g h : X ⟶ X) (_ : g ≫ h = h ≫ g)
    {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    (x : ToType X), h (g (f x)) = g (h (f x)) := @ex2_apply

-- Need nosimp on the following `elementwise` since the lemma can be proved by simp anyway.
@[elementwise nosimp]
theorem ex3 [Category C] {X Y : C} (f : X ≅ Y) : f.hom ≫ f.inv = 𝟙 X :=
  Iso.hom_inv_id _

example : ∀ C [Category C] (X Y : C) (f : X ≅ Y)
    {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    (x : ToType X), f.inv (f.hom x) = x := @ex3_apply

-- Make sure there's no `id x` in there:
example : ∀ C [Category C] (X Y : C) (f : X ≅ Y)
    {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    (x : ToType X), f.inv (f.hom x) = x := by intros; simp only [ex3_apply]

@[elementwise]
lemma foo [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

@[elementwise]
lemma foo' [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

lemma bar [Category C] {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : ToType M) : g (f x) = h x := by
  apply foo_apply w

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : M), g (f x) = h x
  exact this x

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := (elementwise_of% w) x

example [Category C] {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h)
    (x : ToType M) :
    g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : ToType M), g (f x) = h x
  exact this x

-- `elementwise_of%` allows a level metavariable for its `ConcreteCategory` instance.
-- Previously this example did not specify that the universe levels of `C` and `D` (inside `h`)
-- were the same, and this constraint was added post-hoc by the proof term.
-- After https://github.com/leanprover/lean4/pull/4493 this no longer works (happily!).
example {C : Type u} [Category.{v} C] {FC : C → C → Type _} {CC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
    (h : ∀ (D : Type u) [Category.{v} D] (X Y : D) (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X)
    {M N : C} {f : M ⟶ N} {g : N ⟶ M} (x : ToType M) : g (f x) = x := by
  have := elementwise_of% h
  guard_hyp this : ∀ D [Category D] (X Y : D) (f : X ⟶ Y) (g : Y ⟶ X)
    {FD : D → D → Type _} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD] (x : ToType X), g (f x) = x
  rw [this]

section Mon

lemma bar' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by exact foo_apply w x

lemma bar'' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

lemma bar''' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

example (M N K : MonCat) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [elementwise_of% w]

example (M N K : MonCat) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by
  replace w := elementwise_of% w
  apply w

end Mon

example {α β : Type} (f g : α ⟶ β) (w : f = g) (a : α) : f a = g a := by
  replace w := elementwise_of% w
  guard_hyp w : ∀ (x : α), f x = g x
  rw [w]


example {α β : Type} (f g : α ⟶ β) (w : f ≫ 𝟙 β = g) (a : α) : f a = g a := by
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

variable (X : C) {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC] (x : ToType X)

-- Prior to https://github.com/leanprover-community/mathlib4/pull/13413 this would produce
-- `fh_apply X x : (g X) x = (h X) x`.
/-- info: fh_apply X x : (ConcreteCategory.hom (f X)) x = (ConcreteCategory.hom (h X)) x -/
#guard_msgs in
#check fh_apply X x

end HasForget

namespace ConcreteCategory

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id IsIso.hom_inv_id IsIso.inv_hom_id

attribute [simp] Iso.hom_inv_id Iso.inv_hom_id IsIso.hom_inv_id IsIso.inv_hom_id

variable {C : Type*} {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]

@[elementwise]
theorem ex1 [Category C] [ConcreteCategory C FC] (X : C) (f g h : X ⟶ X) (h' : g ≫ h = h ≫ g) :
    f ≫ g ≫ h = f ≫ h ≫ g := by rw [h']

-- If there is already a `ConcreteCategory` instance, do not add a new argument.
example : ∀ C {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [Category C] [ConcreteCategory C FC] (X : C) (f g h : X ⟶ X) (_ : g ≫ h = h ≫ g)
    (x : ToType X), h (g (f x)) = g (h (f x)) := @ex1_apply

@[elementwise]
lemma foo [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

@[elementwise]
lemma foo' [Category C]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) : f ≫ 𝟙 N ≫ g = h := by
  simp [w]

lemma bar [Category C]
    {FC : C → C → Type _} {CC : C → Type _} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : ToType M) : g (f x) = h x := by
  apply foo_apply w

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : M), g (f x) = h x
  exact this x

example {M N K : Type} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
  g (f x) = h x := (elementwise_of% w) x

example [Category C] {FC : C → C → Type _} {CC : C → Type _}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : ToType M) :
    g (f x) = h x := by
  have := elementwise_of% w
  guard_hyp this : ∀ (x : ToType M), g (f x) = h x
  exact this x

section Mon

lemma bar' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by exact foo_apply w x

lemma bar'' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

lemma bar''' {M N K : MonCat} {f : M ⟶ N} {g : N ⟶ K} {h : M ⟶ K} (w : f ≫ g = h) (x : M) :
    g (f x) = h x := by apply foo_apply w

example (M N K : MonCat) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by rw [elementwise_of% w]

example (M N K : MonCat) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
    g (f m) = h m := by
  replace w := elementwise_of% w
  apply w

end Mon

example {α β : Type} (f g : α ⟶ β) (w : f = g) (a : α) : f a = g a := by
  replace w := elementwise_of% w
  guard_hyp w : ∀ (x : α), f x = g x
  rw [w]


example {α β : Type} (f g : α ⟶ β) (w : f ≫ 𝟙 β = g) (a : α) : f a = g a := by
  replace w := elementwise_of% w
  guard_hyp w : ∀ (x : α), f x = g x
  rw [w]

end ConcreteCategory

end ElementwiseTest
