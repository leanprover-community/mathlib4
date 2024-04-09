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

@[simps]
def natTrans_nat_mk {F G : ℕ ⥤ C} (f : (n : ℕ) → F.obj n ⟶ G.obj n)
    (w : ∀ n, F.map (homOfLE (Nat.le_succ _)) ≫ f (n + 1) = f n ≫ G.map (homOfLE (Nat.le_succ _))) :
    F ⟶ G where
  app n := f n
  naturality n m h := by
    have h' : n ≤ m := leOfHom h
    induction h' with
    | refl =>
      change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
      simp
    | @step k a ih =>
      have a' : n ≤ k := a
      have : h = homOfLE a' ≫ homOfLE (Nat.le_succ k) := rfl
      simp only [this, Functor.map_comp, Category.assoc]
      rw [w k, ← Category.assoc, ih (homOfLE _)]
      simp

@[simps]
def natTrans_nat_op_mk {F G : ℕᵒᵖ ⥤ C}
    (f : (n : ℕ) → F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
    (w : ∀ n, F.map ⟨homOfLE (Nat.le_succ _)⟩ ≫ f n = f (n + 1) ≫ G.map ⟨homOfLE (Nat.le_succ _)⟩) :
    F ⟶ G where
  app := fun ⟨n⟩ ↦ f n
  naturality := by
    intro ⟨n⟩ ⟨m⟩ h
    have h' : m ≤ n := leOfHom h.unop
    induction h' with
    | refl =>
      change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
      simp
    | @step k a ih =>
      have a' : m ≤ k := a
      have : h = (homOfLE a' ≫ homOfLE (Nat.le_succ k)).op := rfl
      rw [op_comp] at this
      simp only [this, Functor.map_comp, Category.assoc]
      rw [ih, ← Category.assoc]
      have := w k
      change F.map (homOfLE _).op ≫ _ = _ at this
      rw [this, Category.assoc]
      rfl

@[simps]
def Functor.nat_op_cone_mk (F : ℕᵒᵖ ⥤ C) (X : C) (f : (n : ℕ) → X ⟶ F.obj ⟨n⟩)
    (h : ∀ n, f (n+1) ≫ F.map (homOfLE (Nat.le_succ n)).op = f n) : Cone F where
  pt := X
  π := natTrans_nat_op_mk f fun n ↦ (by simpa using (h n).symm)

variable (g : ℕ → ℕ) (hg : Monotone g) (hg' : ∀ n, (∃ m, n ≤ g m))

@[simps!]
def Nat.functor : ℕ ⥤ ℕ := Nat.functor_mk' g (fun n ↦ homOfLE (hg (Nat.le_succ n)))

lemma final : (Nat.functor g hg).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun n ↦ ?_, fun _ _ ↦ ⟨_, 𝟙 _, rfl⟩⟩
  obtain ⟨m, hm⟩ := hg' n
  exact ⟨m, ⟨homOfLE hm⟩⟩

lemma initial : (Nat.functor g hg).op.Initial :=
  have := final g hg hg'
  Functor.initial_op_of_final _


@[simps!]
noncomputable
def Functor.nat_op_cone_mk' (F : ℕᵒᵖ ⥤ C) (X : C) (f : (n : ℕ) → (X ⟶ F.obj ⟨g n⟩))
    (h : ∀ n, f (n+1) ≫ F.map (homOfLE (hg (Nat.le_succ n))).op = f n) : Cone F :=
  have := initial g hg hg'
  (Functor.Initial.conesEquiv (Nat.functor g hg).op _).functor.obj
    (Functor.nat_op_cone_mk _ X f h)

def f_initial (F : ℕᵒᵖ ⥤ C) (X : C) (m : ℕ) (f : (n : ℕ) → m ≤ n → (X ⟶ F.obj ⟨n⟩)) :
    let g := fun n : ℕ ↦ max m n
    -- have hg : Monotone g := fun _ _ h ↦ max_le_max_left _ h
    -- have hg' : ∀ n, ∃ a, n ≤ g a := fun n ↦ ⟨n, le_max_right _ _⟩
    (n : ℕ) → X ⟶ F.obj ⟨g n⟩ := fun n ↦ f (max m n) (le_max_left _ _)

lemma h_initial (F : ℕᵒᵖ ⥤ C) (X : C) (m : ℕ) (f : (n : ℕ) → m ≤ n → (X ⟶ F.obj ⟨n⟩))
    (h : ∀ n (h : m ≤ n), f (n+1) (h.trans (Nat.le_succ n)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = f n h) :
    let g := fun n : ℕ ↦ max m n
    have hg : Monotone g := fun _ _ h ↦ max_le_max_left _ h
    have hg' : ∀ n, ∃ a, n ≤ g a := fun n ↦ ⟨n, le_max_right _ _⟩
    ∀ n, f_initial F X m f (n+1) ≫ F.map (homOfLE (hg (Nat.le_succ n))).op =
      f_initial F X m f n := by
  intro g hg hg' n
  simp [f_initial]
  induction m with
  | zero =>
    have hh : ∀ k, max 0 k = k := by simp
    change _ ≫ F.map ((eqToHom (hh (n+1))).op ≫
      (homOfLE (Nat.le_succ n)).op ≫ (eqToHom (hh n)).op) = _
    simp only [Nat.zero_eq, op_id, eqToHom_op, Functor.map_comp, eqToHom_map, ← Category.assoc]
    simp only [Nat.zero_eq, ge_iff_le, zero_le, max_eq_right, eqToHom_naturality, Category.assoc]
    -- have : f (n + 1) (zero_le (n+1)) = eqToHom _ ≫ f _ _ := sorry
    have : F.obj ⟨n⟩ = F.obj ⟨max 0 n⟩ := by simp
    have : f (max 0 n) (zero_le _) = f n (zero_le _) ≫ eqToHom this := by
      simp only [ge_iff_le, zero_le, max_eq_right, ← eqToHom_map]
      rw [← h n, ← h (max 0 n)]
      sorry
    sorry
  | succ n ih => sorry

end CategoryTheory
