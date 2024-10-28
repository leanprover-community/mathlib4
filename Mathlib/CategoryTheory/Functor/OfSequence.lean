/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.EqToHom

/-!
# Functors from the category of the ordered set `ℕ`

In this file, we provide a constructor `Functor.ofSequence`
for functors `ℕ ⥤ C` which takes as an input a sequence
of morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.

We also provide a constructor `NatTrans.ofSequence` for natural
transformations between functors `ℕ ⥤ C` which allows to check
the naturality condition only for morphisms `n ⟶ n + 1`.

The duals of the above for functors `ℕᵒᵖ ⥤ C` are given by `Functor.ofOpSequence` and
`NatTrans.ofOpSequence`.

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category C]

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

namespace OfSequence

lemma congr_f (i j : ℕ) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The morphism `X i ⟶ X j` obtained by composing morphisms of
the form `X n ⟶ X (n + 1)` when `i ≤ j`. -/
def map : ∀ {X : ℕ → C} (_ : ∀ n, X n ⟶ X (n + 1)) (i j : ℕ), i ≤ j → (X i ⟶ X j)
  | _, _, 0, 0 => fun _ ↦ 𝟙 _
  | _, f, 0, 1 => fun _ ↦ f 0
  | _, f, 0, l + 1 => fun _ ↦ f 0 ≫ map (fun n ↦ f (n + 1)) 0 l (by omega)
  | _, _, _ + 1, 0 => nofun
  | _, f, k + 1, l + 1 => fun _ ↦ map (fun n ↦ f (n + 1)) k l (by omega)

lemma map_id (i : ℕ) : map f i i (by omega) = 𝟙 _ := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

lemma map_le_succ (i : ℕ) : map f i (i + 1) (by omega) = f i := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

@[reassoc]
lemma map_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  revert X f j k
  induction i with
  | zero =>
      intros X f j
      revert X f
      induction j with
      | zero =>
          intros X f k hij hjk
          rw [map_id, id_comp]
      | succ j hj =>
          rintro X f (_|_|k) hij hjk
          · omega
          · obtain rfl : j = 0 := by omega
            rw [map_id, comp_id]
          · dsimp [map]
            rw [hj (fun n ↦ f (n + 1)) (k + 1) (by omega) (by omega)]
            obtain _|j := j
            all_goals simp [map]
  | succ i hi =>
      rintro X f (_|j) (_|k)
      · omega
      · omega
      · omega
      · intros
        exact hi _ j k (by omega) (by omega)

-- `map` has good definitional properties when applied to explicit natural numbers
example : map f 5 5 (by omega) = 𝟙 _ := rfl
example : map f 0 3 (by omega) = f 0 ≫ f 1 ≫ f 2 := rfl
example : map f 3 7 (by omega) = f 3 ≫ f 4 ≫ f 5 ≫ f 6 := rfl

end OfSequence

/-- The functor `ℕ ⥤ C` constructed from a sequence of
morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`. -/
@[simps obj]
def ofSequence : ℕ ⥤ C where
  obj := X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]
lemma ofSequence_map_homOfLE_succ (n : ℕ) :
    (ofSequence f).map (homOfLE (Nat.le_add_right n 1)) = f n :=
  OfSequence.map_le_succ f n

end Functor

namespace NatTrans

variable {F G : ℕ ⥤ C} (app : ∀ (n : ℕ), F.obj n ⟶ G.obj n)
  (naturality : ∀ (n : ℕ), F.map (homOfLE (n.le_add_right 1)) ≫ app (n + 1) =
      app n ≫ G.map (homOfLE (n.le_add_right 1)))

/-- Constructor for natural transformations `F ⟶ G` in `ℕ ⥤ C` which takes as inputs
the morphisms `F.obj n ⟶ G.obj n` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps app]
def ofSequence : F ⟶ G where
  app := app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by omega))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by omega
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by omega
        simp only [← homOfLE_comp (show i ≤ i + k by omega) (show i + k ≤ i + k + 1 by omega),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]

end NatTrans

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n)

namespace OfOpSequence

lemma congr_f (i j : ℕ) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The morphism `X j ⟶ X i` obtained by composing morphisms of
the form `X (n + 1) ⟶ X n` when `i ≤ j`. -/
def map : ∀ {X : ℕ → C} (_ : ∀ n, X (n + 1) ⟶ X n) (i j : ℕ), i ≤ j → (X j ⟶ X i)
  | _, _, 0, 0 => fun _ ↦ 𝟙 _
  | _, f, 0, 1 => fun _ ↦ f 0
  | _, f, 0, l + 1 => fun _ ↦ f l ≫ map f 0 l (by omega)
  | _, _, _ + 1, 0 => nofun
  | X, f, k + 1, l + 1 => fun _ ↦ map (X := fun n ↦ X (n + 1)) (fun n ↦ f (n + 1)) k l (by omega)


lemma map_id (i : ℕ) : map f i i (by omega) = 𝟙 _ := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

lemma map_le_succ (i : ℕ) : map f i (i + 1) (by omega) = f i := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

lemma map_zero_succ (i : ℕ) : map f 0 (i + 1) (by omega) = f i ≫ map f 0 i (by omega) := by
  revert X f
  induction i with
  | zero => intros; simp [map]
  | succ _ _ => intros; simp [map]

lemma map_succ (i j : ℕ) (h : j ≤ i) :
    map f j (i + 1) (by omega) = map f (j + 1) (i + 1) (by omega) ≫ f j := by
  revert X f i
  induction j with
  | zero =>
      intro X f i
      induction i with
      | zero => simp [map]
      | succ _ hi => simp [map, map_zero_succ, hi]
  | succ j hj => rintro X f (_|i) h; exacts [by omega, hj _ _ (by omega)]

@[reassoc]
lemma map_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f j k hjk ≫ map f i j hij := by
  revert X f i j
  induction k with
  | zero =>
      intros X f j
      revert X f
      induction j with
      | zero =>
          intros X f k hij hjk
          obtain rfl : k = 0 := by omega
          rw [map_id, comp_id]
      | succ j hj =>
          rintro X f (_|_|k) hij hjk
          · omega
          · obtain rfl : j = 0 := by omega
            rw [map_id, comp_id]
          · omega
  | succ k hk =>
      rintro X f (_|i)
      · intro j
        induction j with
        | zero => intros; simp [map]
        | succ j hj =>
            intro _ h
            nth_rewrite 2 [map_zero_succ]
            rw [hj (by omega) (by omega), map_succ _ k j (by omega)]
            simp
      · rintro (_|j)
        · omega
        · intros
          exact hk _ i j (by omega) (by omega)

-- `map` has good definitional properties when applied to explicit natural numbers
example : map f 5 5 (by omega) = 𝟙 _ := rfl
example : map f 0 3 (by omega) = f 2 ≫ f 1 ≫ f 0 := rfl
example : map f 3 7 (by omega) = f 6 ≫ f 5 ≫ f 4 ≫ f 3 := rfl

end OfOpSequence

/-- The functor `ℕᵒᵖ ⥤ C` constructed from a sequence of
morphisms `f : X (n + 1) ⟶ X n` for all `n : ℕ`. -/
@[simps obj]
def ofOpSequence : ℕᵒᵖ ⥤ C where
  obj n := X n.unop
  map φ := OfOpSequence.map f _ _ (leOfHom φ.unop)
  map_id i := OfOpSequence.map_id f i.unop
  map_comp α β := OfOpSequence.map_comp f _ _ _ (leOfHom β.unop) (leOfHom α.unop)

@[simp]
lemma ofOpSequence_map_homOfLE_succ (n : ℕ) :
    (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op = f n :=
  OfOpSequence.map_le_succ f n

end Functor

namespace NatTrans

variable {F G : ℕᵒᵖ ⥤ C} (app : ∀ (n : ℕ), F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
  (naturality : ∀ (n : ℕ), F.map (homOfLE (n.le_add_right 1)).op ≫ app n =
      app (n + 1) ≫ G.map (homOfLE (n.le_add_right 1)).op)

/-- Constructor for natural transformations `F ⟶ G` in `ℕᵒᵖ ⥤ C` which takes as inputs
the morphisms `F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps app]
def ofOpSequence : F ⟶ G where
  app n := app n.unop
  naturality := by
    intro ⟨i⟩ ⟨j⟩ ⟨(φ : j ⟶ i)⟩
    change F.map φ.op ≫ _ = _ ≫ G.map φ.op
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by omega))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by omega
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : i = j + k + 1 := by omega
        simp only [← homOfLE_comp (show j ≤ j + k by omega) (show j + k ≤ j + k + 1 by omega),
          Functor.map_comp, assoc, naturality, op_comp, hk _ j rfl ]
        simp only [homOfLE_leOfHom, ← assoc, naturality]

end NatTrans

end CategoryTheory
