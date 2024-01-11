/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought as families of `n` composable
arrows in `C`. In this file, we introduce and study this category `ComposableArrows C n`
of `n` composable arrows in `C`.

If `F : ComposableArrows C n`, we define `F.left` as the leftmost object, `F.right` as the
rightmost object, and `F.hom : F.left ⟶ F.right` is the canonical map.

The most significant definition in this file is the constructor
`F.precomp f : ComposableArrows C (n + 1)` for `F : ComposableArrows C n` and `f : X ⟶ F.left`:
"it shifts `F` towards the right and inserts `f` on the left". This `precomp` has
good definitional properties.

In the namespace `CategoryTheory.ComposableArrows`, we provide constructors
like `mk₁ f`, `mk₂ f g`, `mk₃ f g h` for `ComposableArrows C n` for small `n`.

TODO (@joelriou):
* define various constructors for objects, morphisms, isomorphisms in `ComposableArrows C n`
* redefine `Arrow C` as `ComposableArrow C 1`?
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
the precomposition with which shall induce funtors
`ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
(specifically faces) with good definitional properties (this might be necessary for
up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

namespace CategoryTheory

open Category

variable (C : Type*) [Category C]

/-- `ComposableArrows C n` is the type of functors `Fin (n + 1) ⥤ C`. -/
abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n m : ℕ}
variable (F G : ComposableArrows C n)

/-- The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`. -/
@[simp]
abbrev obj' (i : ℕ) (hi : i ≤ n := by linarith) : C := F.obj ⟨i, by linarith⟩

/-- The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`. -/
@[simp]
abbrev map' (i j : ℕ) (hij : i ≤ j := by linarith) (hjn : j ≤ n := by linarith) :
  F.obj ⟨i, by linarith⟩ ⟶ F.obj ⟨j, by linarith⟩ := F.map (homOfLE (by
    simp only [Fin.mk_le_mk]
    linarith))

lemma map'_self (i : ℕ) (hi : i ≤ n := by linarith) :
    F.map' i i = 𝟙 _ := F.map_id _

lemma map'_comp (i j k : ℕ) (hij : i ≤ j := by linarith)
    (hjk : j ≤ k := by linarith) (hk : k ≤ n := by linarith) :
    F.map' i k = F.map' i j ≫ F.map' j k :=
  F.map_comp _ _

/-- The leftmost object of `F : ComposableArrows C n`. -/
abbrev left := obj' F 0

/-- The rightmost object of `F : ComposableArrows C n`. -/
abbrev right := obj' F n

/-- The canonical map `F.left ⟶ F.right` for `F : ComposableArrows C n`. -/
abbrev hom : F.left ⟶ F.right := map' F 0 n

variable {F G}

/-- The map `F.obj' i ⟶ G.obj' i` induced on `i`th objects by a morphism `F ⟶ G`
in `ComposableArrows C n` when `i` is a natural number such that `i ≤ n`. -/
@[simp]
abbrev app' (φ : F ⟶ G) (i : ℕ) (hi : i ≤ n := by linarith) :
    F.obj' i ⟶ G.obj' i := φ.app _

/-- Constructor for `ComposableArrows C 0`. -/
@[simps!]
def mk₀ (X : C) : ComposableArrows C 0 := (Functor.const (Fin 1)).obj X

namespace Mk₁

variable (X₀ X₁ : C)

/-- The map which sends `0 : Fin 2` to `X₀` and `1` to `X₁`. -/
@[simp]
def obj : Fin 2 → C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩  => X₁

variable {X₀ X₁} (f : X₀ ⟶ X₁)

/-- The obvious map `obj X₀ X₁ i ⟶ obj X₀ X₁ j` whenever `i j : Fin 2` satisfy `i ≤ j`. -/
@[simp]
def map : ∀ (i j : Fin 2) (_ : i ≤ j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _

lemma map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _ :=
  match i with
    | 0 => rfl
    | 1 => rfl

lemma map_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk :=
  match i with
    | 0 =>
        match j with
          | 0 => by rw [map_id, id_comp]
          | 1 => by
              obtain rfl : k = 1 := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
              rw [map_id, comp_id]
    | 1 => by
        obtain rfl := j.eq_one_of_neq_zero (by rintro rfl; simp at hij)
        obtain rfl := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
        rw [map_id, id_comp]

end Mk₁

/-- Constructor for `ComposableArrows C 1`. -/
@[simps]
def mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) : ComposableArrows C 1 where
  obj := Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

/-- Constructor for morphisms `F ⟶ G` in `ComposableArrows C n` which takes as inputs
a family of morphisms `F.obj i ⟶ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
def homMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ⟶ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)) :
    F ⟶ G where
  app := app
  naturality := by
    suffices ∀ (k i j : ℕ) (hj : i + k = j) (hj' : j ≤ n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact this k i j hk (by linarith)
    intro k
    induction' k with k hk
    · intro i j hj hj'
      simp only [Nat.zero_eq, add_zero] at hj
      obtain rfl := hj
      rw [F.map'_self i, G.map'_self i, id_comp, comp_id]
    · intro i j hj hj'
      rw [Nat.succ_eq_add_one, ← add_assoc] at hj
      subst hj
      rw [F.map'_comp i (i + k) (i + k + 1), G.map'_comp i (i + k) (i + k + 1), assoc,
        w (i + k) (by linarith), reassoc_of% (hk i (i + k) rfl (by linarith))]

/-- Constructor for isomorphisms `F ≅ G` in `ComposableArrows C n` which takes as inputs
a family of isomorphisms `F.obj i ≅ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
def isoMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ≅ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n),
      F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)) :
    F ≅ G where
  hom := homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    dsimp only
    rw [← cancel_epi ((app _).hom), ← reassoc_of% (w i hi), Iso.hom_inv_id, comp_id,
      Iso.hom_inv_id_assoc])

lemma ext {F G : ComposableArrows C n} (h : ∀ i, F.obj i = G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) =
      eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm) : F = G :=
  Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h (fun i => rfl)

/-- Constructor for morphisms in `ComposableArrows C 0`. -/
@[simps!]
def homMk₀ {F G : ComposableArrows C 0} (f : F.obj' 0 ⟶ G.obj' 0) : F ⟶ G :=
  homMk (fun i => match i with
    | ⟨0, _⟩ => f) (fun i hi => by simp at hi)

@[ext]
lemma hom_ext₀ {F G : ComposableArrows C 0} {φ φ' : F ⟶ G}
    (h : app' φ 0 = app' φ' 0) :
    φ = φ' := by
  ext i
  fin_cases i
  exact h

/-- Constructor for isomorphisms in `ComposableArrows C 0`. -/
@[simps!]
def isoMk₀ {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0) : F ≅ G where
  hom := homMk₀ e.hom
  inv := homMk₀ e.inv

lemma ext₀ {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0) : F = G :=
  ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)

lemma mk₀_surjective (F : ComposableArrows C 0) : ∃ (X : C), F = mk₀ X :=
  ⟨F.obj' 0, ext₀ rfl⟩

/-- Constructor for morphisms in `ComposableArrows C 1`. -/
@[simps!]
def homMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ⟶ G.obj' 0) (right : F.obj' 1 ⟶ G.obj' 1)
    (w : F.map' 0 1 ≫ right = left ≫ G.map' 0 1 := by aesop_cat) :
    F ⟶ G :=
  homMk (fun i => match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right) (by
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact w)

@[ext]
lemma hom_ext₁ {F G : ComposableArrows C 1} {φ φ' : F ⟶ G}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
    φ = φ' := by
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

/-- Constructor for isomorphisms in `ComposableArrows C 1`. -/
@[simps!]
def isoMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ≅ G.obj' 0) (right : F.obj' 1 ≅ G.obj' 1)
    (w : F.map' 0 1 ≫ right.hom = left.hom ≫ G.map' 0 1 := by aesop_cat) :
    F ≅ G where
  hom := homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom, assoc, assoc, w, right.inv_hom_id, left.inv_hom_id_assoc]
    apply comp_id)

lemma map'_eq_hom₁ (F : ComposableArrows C 1) : F.map' 0 1 = F.hom := rfl

lemma ext₁ {F G : ComposableArrows C 1}
    (left : F.left = G.left) (right : F.right = G.right)
    (w : F.hom = eqToHom left ≫ G.hom ≫ eqToHom right.symm) : F = G :=
  Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

lemma mk₁_surjective (X : ComposableArrows C 1) : ∃ (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f :=
  ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

variable (F)

namespace Precomp

variable (X : C)

/-- The map `Fin (n + 1 + 1) → C` which "shifts" `F.obj'` to the right and inserts `X` in
the zeroth position. -/
def obj : Fin (n + 1 + 1) → C
  | ⟨0, _⟩ => X
  | ⟨i + 1, hi⟩ => F.obj' i

@[simp]
lemma obj_zero : obj F X 0 = X := rfl

@[simp]
lemma obj_one : obj F X 1 = F.obj' 0 := rfl

@[simp]
lemma obj_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) : obj F X ⟨i + 1, hi⟩ = F.obj' i := rfl

variable {X} (f : X ⟶ F.left)

/-- Auxiliary definition for the action on maps of the functor `F.precomp f`.
It sends `0 ≤ 1` to `f` and `i + 1 ≤ j + 1` to `F.map' i j`. -/
def map : ∀ (i j : Fin (n + 1 + 1)) (_ : i ≤ j), obj F X i ⟶ obj F X j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨0, _⟩, ⟨j + 2, hj⟩, _ => f ≫ F.map' 0 (j + 1)
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => F.map' i j (by simpa using hij)

@[simp]
lemma map_zero_zero : map F f 0 0 (by simp) = 𝟙 X := rfl

@[simp]
lemma map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _) := rfl

@[simp]
lemma map_zero_one : map F f 0 1 (by simp) = f := rfl

@[simp]
lemma map_zero_one' : map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f := rfl

@[simp]
lemma map_zero_succ_succ (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    map F f 0 ⟨j + 2, hj⟩ (by simp) = f ≫ F.map' 0 (j+1) := rfl

@[simp]
lemma map_succ_succ (i j : ℕ) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
    (hij : i + 1 ≤ j + 1) :
    map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j := rfl

@[simp]
lemma map_one_succ (j : ℕ) (hj : j + 1 < n + 1 + 1) :
    map F f 1 ⟨j + 1, hj⟩ (by simp [Fin.le_def]) = F.map' 0 j := rfl

lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  obtain ⟨i, hi⟩ := i
  cases i
  · rfl
  · apply F.map_id

lemma map_comp {i j k : Fin (n + 1 + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | _ | j := j
    · dsimp
      rw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · dsimp
        rw [F.map_id, comp_id]
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def, Nat.succ_eq_add_one] at hjk
      · dsimp
        rw [assoc, ← F.map_comp, homOfLE_comp]
  · obtain _ | j := j
    · simp [Fin.ext_iff] at hij
    · obtain _ | k := k
      · simp [Fin.ext_iff] at hjk
      · dsimp
        rw [← F.map_comp, homOfLE_comp]

end Precomp

/-- "Precomposition" of `F : ComposableArrows C n` by a morphism `f : X ⟶ F.left`. -/
@[simps]
def precomp {X : C} (f : X ⟶ F.left) : ComposableArrows C (n + 1) where
  obj := Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := (Precomp.map_comp F f (leOfHom g) (leOfHom g'))

/-- Constructor for `ComposableArrows C 2`. -/
@[simp]
def mk₂ {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : ComposableArrows C 2 :=
  (mk₁ g).precomp f

/-- Constructor for `ComposableArrows C 3`. -/
@[simp]
def mk₃ {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : ComposableArrows C 3 :=
  (mk₂ g h).precomp f

section

variable {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)

/-! These examples are meant to test the good definitional properties of `precomp`,
and that `dsimp` can see through. -/

example : map' (mk₂ f g) 0 1 = f := by dsimp
example : map' (mk₂ f g) 1 2 = g := by dsimp
example : map' (mk₂ f g) 0 2 = f ≫ g := by dsimp
example : (mk₂ f g).hom = f ≫ g := by dsimp
example : map' (mk₂ f g) 0 0 = 𝟙 _ := by dsimp
example : map' (mk₂ f g) 1 1 = 𝟙 _ := by dsimp
example : map' (mk₂ f g) 2 2 = 𝟙 _ := by dsimp

example : map' (mk₃ f g h) 0 1 = f := by dsimp
example : map' (mk₃ f g h) 1 2 = g := by dsimp
example : map' (mk₃ f g h) 2 3 = h := by dsimp
example : map' (mk₃ f g h) 0 3 = f ≫ g ≫ h := by dsimp
example : (mk₃ f g h).hom = f ≫ g ≫ h := by dsimp
example : map' (mk₃ f g h) 0 2 = f ≫ g := by dsimp
example : map' (mk₃ f g h) 1 3 = g ≫ h := by dsimp

end

/-- The map `ComposableArrows C m → ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
def whiskerLeft (F : ComposableArrows C m) (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C n := Φ ⋙ F

/-- The functor `ComposableArrows C m ⥤ ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
def whiskerLeftFunctor (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C m ⥤ ComposableArrows C n where
  obj F := F.whiskerLeft Φ
  map f := CategoryTheory.whiskerLeft Φ f

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.succ`. -/
@[simps]
def _root_.Fin.succFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.succ
  map {i j} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the first arrow. -/
@[simps!]
def δ₀Functor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.succFunctor (n + 1))

/-- The `ComposableArrows C n` obtained by forgetting the first arrow. -/
abbrev δ₀ (F : ComposableArrows C (n + 1)) := δ₀Functor.obj F

@[simp]
lemma precomp_δ₀ {X : C} (f : X ⟶ F.left) : (F.precomp f).δ₀ = F := rfl

end ComposableArrows

variable {C}

/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` obtained by postcomposition
with a functor `C ⥤ D`. -/
@[simps!]
def Functor.mapComposableArrows {D : Type*} [Category D] (G : C ⥤ D) (n : ℕ) :
    ComposableArrows C n ⥤ ComposableArrows D n :=
  (whiskeringRight _ _ _).obj G

end CategoryTheory
