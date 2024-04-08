import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C]

def compose_n (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) {n m : ℕ}
    (hh : n ≤ m) : f m ⟶ f n :=
  Nat.leRecOn hh (fun g ↦ h _ ≫ g) (𝟙 _)

lemma compose_n_id (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) (n : ℕ) :
    compose_n f h (le_refl n) = 𝟙 _ :=
  Nat.leRecOn_self _

lemma compose_n_succ (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) (n : ℕ) :
    compose_n f h (Nat.le_succ n) = h n := by
  simp [compose_n, Nat.leRecOn_succ, Nat.leRecOn_self]

lemma compose_n_trans (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    compose_n f h (h₁.trans h₂) = compose_n f h h₂ ≫ compose_n f h h₁ := by
  induction h₂ with
  | refl =>
    simp [compose_n, Nat.leRecOn_self _]
  | @step p h₂ ih =>
    rw [compose_n, Nat.leRecOn_succ (h₁.trans h₂)]
    simp only [compose_n] at ih
    rw [ih, compose_n, compose_n, ← Category.assoc]
    congr
    exact (Nat.leRecOn_succ _ _).symm

@[simps!]
def Nat.functor_mk (f : ℕ → C) (h : (n : ℕ) → f (n + 1) ⟶ f n) :
    ℕᵒᵖ ⥤ C where
  obj n := f n.unop
  map := @fun ⟨_⟩ ⟨_⟩ ⟨⟨⟨hh⟩⟩⟩ ↦ compose_n f h hh
  map_id _ := compose_n_id _ _ _
  map_comp _ _ := compose_n_trans _ _ _ _

def compose_n' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) {n m : ℕ}
    (hh : n ≤ m) : f n ⟶ f m :=
  Nat.leRecOn hh (fun g ↦ g ≫ h _) (𝟙 _)

lemma compose_n_id' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) (n : ℕ) :
    compose_n' f h (le_refl n) = 𝟙 _ :=
  Nat.leRecOn_self _

lemma compose_n_succ' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) (n : ℕ) :
    compose_n' f h (Nat.le_succ n) = h n := by
  simp [compose_n', Nat.leRecOn_succ, Nat.leRecOn_self]

lemma compose_n_trans' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    compose_n' f h (h₁.trans h₂) = compose_n' f h h₁ ≫ compose_n' f h h₂ := by
  induction h₂ with
  | refl =>
    simp [compose_n', Nat.leRecOn_self _]
  | @step p h₂ ih =>
    rw [compose_n', Nat.leRecOn_succ (h₁.trans h₂)]
    simp only [compose_n'] at ih
    rw [ih, compose_n', compose_n', Category.assoc]
    congr
    rw [Nat.leRecOn_succ]

@[simps!]
def Nat.functor_mk' (f : ℕ → C) (h : (n : ℕ) → f n ⟶ f (n + 1)) :
    ℕ ⥤ C where
  obj n := f n
  map := @fun _ _ ⟨⟨hh⟩⟩ ↦ compose_n' f h hh
  map_id _ := compose_n_id' _ _ _
  map_comp _ _ := compose_n_trans' _ _ _ _

-- variable {J D : Type*} [Category J] [Category D] (F : J ⥤ C) (G : C ⥤ D) [ReflectsLimit F G]
--     [HasLimit (F ⋙ G)]

-- instance : HasLimit F := sorry

end CategoryTheory

namespace LightProfinite

variable (X : LightProfinite.{u}) (f : ℕ → ℕ) (hf : Monotone f) (hf' : ∀ n, (∃ m, n ≤ f m))

@[simps!]
def Nat.functor : ℕ ⥤ ℕ := Nat.functor_mk' f (fun n ↦ homOfLE (hf (Nat.le_succ n)))

lemma final : (Nat.functor f hf).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun n ↦ ?_, fun _ _ ↦ ⟨_, 𝟙 _, rfl⟩⟩
  obtain ⟨m, hm⟩ := hf' n
  exact ⟨m, ⟨homOfLE hm⟩⟩

lemma initial : (Nat.functor f hf).op.Initial :=
  have := final f hf hf'
  Functor.initial_op_of_final _

noncomputable def reindex : LightProfinite where
  diagram := (Nat.functor f hf).op ⋙ X.diagram
  cone := X.cone.whisker (Nat.functor f hf).op
  isLimit := ((initial f hf hf').isLimitWhiskerEquiv _).symm X.isLimit
