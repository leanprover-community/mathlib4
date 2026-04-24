/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SuppressCompilation
/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought of as families of `n` composable
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
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
  the precomposition with which shall induce functors
  `ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
  (specifically faces) with good definitional properties (this might be necessary for
  up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

@[expose] public section

set_option backward.privateInPublic true

/-!
New `simprocs` that run even in `dsimp` have caused breakages in this file.

(e.g. `dsimp` can now simplify `2 + 3` to `5`)

For now, we just turn off the offending simprocs in this file.

*However*, hopefully it is possible to refactor the material here so that no disabling of
simprocs is needed.

See issue https://github.com/leanprover-community/mathlib4/issues/27382.
-/
attribute [-simp] Fin.reduceFinMk

namespace CategoryTheory

open Category

variable (C : Type*) [Category* C]

/-- `ComposableArrows C n` is the type of functors `Fin (n + 1) ⥤ C`. -/
abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n m : ℕ}
variable (F G : ComposableArrows C n)

-- We do not yet replace `omega` with `lia` here, as it is measurably slower.
/-- A wrapper for `omega` which prefaces it with some quick and useful attempts -/
macro "valid" : tactic =>
  `(tactic| first | assumption | apply zero_le | apply le_rfl | transitivity <;> assumption | omega)

/-- The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`. -/
@[simp]
abbrev obj' (i : ℕ) (hi : i ≤ n := by valid) : C := F.obj ⟨i, by lia⟩

/-- The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`. -/
@[simp]
abbrev map' (i j : ℕ) (hij : i ≤ j := by valid) (hjn : j ≤ n := by valid) :
    F.obj ⟨i, by lia⟩ ⟶ F.obj ⟨j, by lia⟩ :=
  F.map (homOfLE (by simp only [Fin.mk_le_mk]; valid))

lemma map'_self (i : ℕ) (hi : i ≤ n := by valid) : F.map' i i = 𝟙 _ := F.map_id _

lemma map'_comp (i j k : ℕ) (hij : i ≤ j := by valid)
    (hjk : j ≤ k := by valid) (hk : k ≤ n := by valid) :
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
abbrev app' (φ : F ⟶ G) (i : ℕ) (hi : i ≤ n := by valid) :
    F.obj' i ⟶ G.obj' i := φ.app _

@[reassoc]
lemma naturality' (φ : F ⟶ G) (i j : ℕ) (hij : i ≤ j := by valid)
    (hj : j ≤ n := by valid) :
    F.map' i j ≫ app' φ j = app' φ i ≫ G.map' i j :=
  φ.naturality _

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

variable {X₀ X₁}
variable (f : X₀ ⟶ X₁)

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
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  obtain rfl | rfl : i = j ∨ j = k := by lia
  · rw [map_id, id_comp]
  · rw [map_id, comp_id]

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
      exact this k i j hk (by valid)
    intro k
    induction k with intro i j hj hj'
    | zero =>
      simp only [add_zero] at hj
      obtain rfl := hj
      rw [F.map'_self i, G.map'_self i, id_comp, comp_id]
    | succ k hk =>
      rw [← add_assoc] at hj
      subst hj
      rw [F.map'_comp i (i + k) (i + k + 1), G.map'_comp i (i + k) (i + k + 1), assoc,
        w (i + k) (by valid), reassoc_of% (hk i (i + k) rfl (by valid))]

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
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h

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

#adaptation_note /-- After leanprover/lean4#13363, the `hom_inv_id` and `inv_hom_id` fields
needed to be supplied explicitly. Previously they were not necessary, and were proved by the
`auto_param`.
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
/-- Constructor for isomorphisms in `ComposableArrows C 0`. -/
@[simps!]
def isoMk₀ {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0) : F ≅ G where
  hom := homMk₀ e.hom
  inv := homMk₀ e.inv
  hom_inv_id := by apply hom_ext₀; with_unfolding_all exact e.hom_inv_id
  inv_hom_id := by apply hom_ext₀; with_unfolding_all exact e.inv_hom_id

lemma isIso_iff₀ {F G : ComposableArrows C 0} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ h 0, fun _ i ↦ by fin_cases i; assumption⟩

lemma ext₀ {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0) : F = G :=
  ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)

lemma mk₀_surjective (F : ComposableArrows C 0) : ∃ (X : C), F = mk₀ X :=
  ⟨F.obj' 0, ext₀ rfl⟩

/-- Constructor for morphisms in `ComposableArrows C 1`. -/
@[simps!]
def homMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ⟶ G.obj' 0) (right : F.obj' 1 ⟶ G.obj' 1)
    (w : F.map' 0 1 ≫ right = left ≫ G.map' 0 1 := by cat_disch) :
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

#adaptation_note /-- After leanprover/lean4#13363, the `hom_inv_id` and `inv_hom_id` fields
needed to be supplied explicitly. Previously they were not necessary, and were proved by the
`auto_param`.
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
/-- Constructor for isomorphisms in `ComposableArrows C 1`. -/
@[simps!]
def isoMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ≅ G.obj' 0) (right : F.obj' 1 ≅ G.obj' 1)
    (w : F.map' 0 1 ≫ right.hom = left.hom ≫ G.map' 0 1 := by cat_disch) :
    F ≅ G where
  hom := homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom, assoc, assoc, w, right.inv_hom_id, left.inv_hom_id_assoc]
    apply comp_id)
  hom_inv_id := by
    apply hom_ext₁
    · change left.hom ≫ left.inv = 𝟙 _
      simp
    · change right.hom ≫ right.inv = 𝟙 _
      simp
  inv_hom_id := by
    apply hom_ext₁
    · change left.inv ≫ left.hom = 𝟙 _
      simp
    · change right.inv ≫ right.hom = 𝟙 _
      simp

lemma map'_eq_hom₁ (F : ComposableArrows C 1) : F.map' 0 1 = F.hom := rfl

lemma isIso_iff₁ {F G : ComposableArrows C 1} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1⟩, fun _ i ↦ by fin_cases i <;> tauto⟩

set_option backward.isDefEq.respectTransparency false in
lemma ext₁ {F G : ComposableArrows C 1}
    (left : F.left = G.left) (right : F.right = G.right)
    (w : F.hom = eqToHom left ≫ G.hom ≫ eqToHom right.symm) : F = G :=
  Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

set_option backward.isDefEq.respectTransparency false in
lemma mk₁_surjective (X : ComposableArrows C 1) : ∃ (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f :=
  ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

lemma mk₁_eqToHom_comp {X₀' X₀ X₁ : C} (h : X₀' = X₀) (f : X₀ ⟶ X₁) :
    ComposableArrows.mk₁ (eqToHom h ≫ f) = ComposableArrows.mk₁ f := by
  cat_disch

lemma mk₁_comp_eqToHom {X₀ X₁ X₁' : C} (f : X₀ ⟶ X₁) (h : X₁ = X₁') :
    ComposableArrows.mk₁ (f ≫ eqToHom h) = ComposableArrows.mk₁ f := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
lemma mk₁_hom (X : ComposableArrows C 1) :
    mk₁ X.hom = X :=
  ext₁ rfl rfl (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between `ComposableArrows C 1` and `Arrow C`. -/
@[simps]
def arrowEquiv : ComposableArrows C 1 ≃ Arrow C where
  toFun F := Arrow.mk F.hom
  invFun f := mk₁ f.hom
  left_inv F := ComposableArrows.ext₁ rfl rfl (by simp)
  right_inv _ := rfl

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
    map F f 0 ⟨j + 2, hj⟩ (by simp) = f ≫ F.map' 0 (j + 1) := rfl

@[simp]
lemma map_succ_succ (i j : ℕ) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
    (hij : i + 1 ≤ j + 1) :
    map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j := rfl

@[simp]
lemma map_one_succ (j : ℕ) (hj : j + 1 < n + 1 + 1) :
    map F f 1 ⟨j + 1, hj⟩ (by simp [Fin.le_def]) = F.map' 0 j := rfl

lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  obtain ⟨_ | _, hi⟩ := i <;> simp

set_option backward.isDefEq.respectTransparency false in
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
      · simp
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def] at hjk
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
  map_comp g g' := Precomp.map_comp F f (leOfHom g) (leOfHom g')

/-- Constructor for `ComposableArrows C 2`. -/
abbrev mk₂ {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : ComposableArrows C 2 :=
  (mk₁ g).precomp f

/-- Constructor for `ComposableArrows C 3`. -/
abbrev mk₃ {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : ComposableArrows C 3 :=
  (mk₂ g h).precomp f

/-- Constructor for `ComposableArrows C 4`. -/
abbrev mk₄ {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) :
    ComposableArrows C 4 :=
  (mk₃ g h i).precomp f

/-- Constructor for `ComposableArrows C 5`. -/
abbrev mk₅ {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) :
    ComposableArrows C 5 :=
  (mk₄ g h i j).precomp f

section

variable {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)

/-! These examples are meant to test the good definitional properties of `precomp`,
and that `dsimp` can see through. -/

example : map' (mk₂ f g) 0 1 = f := by with_unfolding_all rfl
example : map' (mk₂ f g) 1 2 = g := by with_unfolding_all rfl
example : map' (mk₂ f g) 0 2 = f ≫ g := by with_unfolding_all rfl
example : (mk₂ f g).hom = f ≫ g := by with_unfolding_all rfl
example : map' (mk₂ f g) 0 0 = 𝟙 _ := by with_unfolding_all rfl
example : map' (mk₂ f g) 1 1 = 𝟙 _ := by with_unfolding_all rfl
example : map' (mk₂ f g) 2 2 = 𝟙 _ := by with_unfolding_all rfl

example : map' (mk₃ f g h) 0 1 = f := by with_unfolding_all rfl
example : map' (mk₃ f g h) 1 2 = g := by with_unfolding_all rfl
example : map' (mk₃ f g h) 2 3 = h := by with_unfolding_all rfl
example : map' (mk₃ f g h) 0 3 = f ≫ g ≫ h := by with_unfolding_all rfl
example : (mk₃ f g h).hom = f ≫ g ≫ h := by with_unfolding_all rfl
example : map' (mk₃ f g h) 0 2 = f ≫ g := by with_unfolding_all rfl
example : map' (mk₃ f g h) 1 3 = g ≫ h := by with_unfolding_all rfl

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
  map f := Functor.whiskerLeft Φ f

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.succ`. -/
@[simps]
def _root_.Fin.succFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.succ
  map {_ _} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the first arrow. -/
@[simps!]
def δ₀Functor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.succFunctor (n + 1))

/-- The `ComposableArrows C n` obtained by forgetting the first arrow. -/
abbrev δ₀ (F : ComposableArrows C (n + 1)) := δ₀Functor.obj F

@[simp]
lemma precomp_δ₀ {X : C} (f : X ⟶ F.left) : (F.precomp f).δ₀ = F := rfl

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.castSucc`. -/
@[simps]
def _root_.Fin.castSuccFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.castSucc
  map hij := hij

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the last arrow. -/
@[simps!]
def δlastFunctor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))

/-- The `ComposableArrows C n` obtained by forgetting the first arrow. -/
abbrev δlast (F : ComposableArrows C (n + 1)) := δlastFunctor.obj F

section

variable {F G : ComposableArrows C (n + 1)}


/-- Inductive construction of morphisms in `ComposableArrows C (n + 1)`: in order to construct
a morphism `F ⟶ G`, it suffices to provide `α : F.obj' 0 ⟶ G.obj' 0` and `β : F.δ₀ ⟶ G.δ₀`
such that `F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1`. -/
def homMkSucc (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
    (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1) : F ⟶ G :=
  homMk
    (fun i => match i with
      | ⟨0, _⟩ => α
      | ⟨i + 1, hi⟩ => app' β i)
    (fun i hi => by
      obtain _ | i := i
      · exact w
      · exact naturality' β i (i + 1))

variable (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
  (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1 := by cat_disch)

@[simp]
lemma homMkSucc_app_zero : (homMkSucc α β w).app 0 = α := rfl

@[simp]
lemma homMkSucc_app_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) :
    (homMkSucc α β w).app ⟨i + 1, hi⟩ = app' β i := rfl

end

lemma hom_ext_succ {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
    (h₀ : app' f 0 = app' g 0) (h₁ : δ₀Functor.map f = δ₀Functor.map g) : f = g := by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · exact congr_app h₁ ⟨i, by valid⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inductive construction of isomorphisms in `ComposableArrows C (n + 1)`: in order to
construct an isomorphism `F ≅ G`, it suffices to provide `α : F.obj' 0 ≅ G.obj' 0` and
`β : F.δ₀ ≅ G.δ₀` such that `F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1`. -/
@[simps]
def isoMkSucc {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
    (β : F.δ₀ ≅ G.δ₀) (w : F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1) : F ≅ G where
  hom := homMkSucc α.hom β.hom w
  inv := homMkSucc α.inv β.inv (by
    rw [← cancel_epi α.hom, ← reassoc_of% w, α.hom_inv_id_assoc, β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp

set_option backward.isDefEq.respectTransparency false in
lemma ext_succ {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
    (h : F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫
      eqToHom (Functor.congr_obj h.symm 0)) : F = G := by
  have : ∀ i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    rcases i with - | i
    · exact h₀
    · exact Functor.congr_obj h ⟨i, by valid⟩
  exact Functor.ext_of_iso (isoMkSucc (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      rw [eqToHom_app, assoc, assoc, eqToHom_trans, eqToHom_refl, comp_id])) this
    (by rintro ⟨_ | _, hi⟩ <;> simp)

lemma precomp_surjective (F : ComposableArrows C (n + 1)) :
    ∃ (F₀ : ComposableArrows C n) (X₀ : C) (f₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀ :=
  ⟨F.δ₀, _, F.map' 0 1, ext_succ rfl (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)

/-- Constructor for morphisms in `ComposableArrows C 2`. -/
def homMk₂ : f ⟶ g := homMkSucc app₀ (homMk₁ app₁ app₂ w₁) w₀

@[simp]
lemma homMk₂_app_zero : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀ := rfl

@[simp]
lemma homMk₂_app_one : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁ := rfl

@[simp]
lemma homMk₂_app_two : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂ := rfl

@[simp]
lemma homMk₂_app_two' : (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by valid⟩ = app₂ := rfl

end

@[ext]
lemma hom_ext₂ {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

#adaptation_note /-- After leanprover/lean4#13363, the `hom_inv_id` and `inv_hom_id` fields
needed to be supplied explicitly. Previously they were not necessary, and were proved by the
`auto_param`.
The replacement proof is a short-term fix, and we request that the authors/maintainers of
this file review the proof, and either approve it by removing this adaptation note, revise
the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
needs addressing. -/
/-- Constructor for isomorphisms in `ComposableArrows C 2`. -/
@[simps]
def isoMk₂ {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2 := by cat_disch) : f ≅ g where
  hom := homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
  hom_inv_id := by apply hom_ext₂ <;> (with_unfolding_all dsimp; simp)
  inv_hom_id := by apply hom_ext₂ <;> (with_unfolding_all dsimp; simp)

lemma isIso_iff₂ {F G : ComposableArrows C 2} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) ∧ IsIso (f.app 2) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun _ i ↦ by fin_cases i <;> tauto⟩

lemma ext₂ {f g : ComposableArrows C 2}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm) : f = g :=
  ext_succ h₀ (ext₁ h₁ h₂ w₁) w₀

set_option backward.isDefEq.respectTransparency false in
lemma mk₂_surjective (X : ComposableArrows C 2) :
    ∃ (X₀ X₁ X₂ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂), X = mk₂ f₀ f₁ :=
  ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩

lemma ext₂_of_arrow {f g : ComposableArrows C 2}
    (h₀₁ : Arrow.mk (f.map' 0 1) = Arrow.mk (g.map' 0 1))
    (h₁₂ : Arrow.mk (f.map' 1 2) = Arrow.mk (g.map' 1 2)) : f = g := by
  obtain ⟨x₀, x₁, x₂, f, f', rfl⟩ := mk₂_surjective f
  obtain ⟨y₀, y₁, y₂, g, g', rfl⟩ := mk₂_surjective g
  obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj h₀₁
  obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj h₀₁
  obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj h₁₂
  obtain rfl : f = g := by rwa [← Arrow.mk_inj]
  obtain rfl : f' = g' := by rwa [← Arrow.mk_inj]
  rfl

section

variable
  {f g : ComposableArrows C 3}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)

/-- Constructor for morphisms in `ComposableArrows C 3`. -/
def homMk₃ : f ⟶ g := homMkSucc app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

@[simp]
lemma homMk₃_app_zero : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀ := rfl

@[simp]
lemma homMk₃_app_one : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁ := rfl

@[simp]
lemma homMk₃_app_two : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by valid⟩ = app₂ :=
  rfl

@[simp]
lemma homMk₃_app_three : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by valid⟩ = app₃ :=
  rfl

end

@[ext]
lemma hom_ext₃ {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

/-- Constructor for isomorphisms in `ComposableArrows C 3`. -/
@[simps]
def isoMk₃ {f g : ComposableArrows C 3}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3) : f ≅ g where
  hom := homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
    (by rw [← cancel_epi app₂.hom, ← reassoc_of% w₂, app₃.hom_inv_id,
      comp_id, app₂.hom_inv_id_assoc])

lemma ext₃ {f g : ComposableArrows C 3}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm) : f = g :=
  ext_succ h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

set_option backward.isDefEq.respectTransparency false in
lemma mk₃_surjective (X : ComposableArrows C 3) :
    ∃ (X₀ X₁ X₂ X₃ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃), X = mk₃ f₀ f₁ f₂ :=
  ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 4}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)

/-- Constructor for morphisms in `ComposableArrows C 4`. -/
def homMk₄ : f ⟶ g := homMkSucc app₀ (homMk₃ app₁ app₂ app₃ app₄ w₁ w₂ w₃) w₀

@[simp]
lemma homMk₄_app_zero : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 0 = app₀ := rfl

@[simp]
lemma homMk₄_app_one : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁ := rfl

@[simp]
lemma homMk₄_app_two :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨2, by valid⟩ = app₂ := rfl

@[simp]
lemma homMk₄_app_three :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨3, by valid⟩ = app₃ := rfl

@[simp]
lemma homMk₄_app_four :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨4, by valid⟩ = app₄ := rfl

end

@[ext]
lemma hom_ext₄ {f g : ComposableArrows C 4} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₃ h₁ h₂ h₃ h₄)

lemma map'_inv_eq_inv_map' {n m : ℕ} (h : n + 1 ≤ m) {f g : ComposableArrows C m}
    (app : f.obj' n ≅ g.obj' n) (app' : f.obj' (n + 1) ≅ g.obj' (n + 1))
    (w : f.map' n (n + 1) ≫ app'.hom = app.hom ≫ g.map' n (n + 1)) :
    map' g n (n + 1) ≫ app'.inv = app.inv ≫ map' f n (n + 1) := by
  rw [← cancel_epi app.hom, ← reassoc_of% w, app'.hom_inv_id, comp_id, app.hom_inv_id_assoc]

/-- Constructor for isomorphisms in `ComposableArrows C 4`. -/
@[simps]
def isoMk₄ {f g : ComposableArrows C 4}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4) :
    f ≅ g where
  hom := homMk₄ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom w₀ w₁ w₂ w₃
  inv := homMk₄ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])

lemma ext₄ {f g : ComposableArrows C 4}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm) :
    f = g :=
  ext_succ h₀ (ext₃ h₁ h₂ h₃ h₄ w₁ w₂ w₃) w₀

set_option backward.isDefEq.respectTransparency false in
lemma mk₄_surjective (X : ComposableArrows C 4) :
    ∃ (X₀ X₁ X₂ X₃ X₄ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄),
      X = mk₄ f₀ f₁ f₂ f₃ :=
  ⟨_, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4,
    ext₄ rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 5}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4) (app₅ : f.obj' 5 ⟶ g.obj' 5)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)
  (w₄ : f.map' 4 5 ≫ app₅ = app₄ ≫ g.map' 4 5 := by cat_disch)

/-- Constructor for morphisms in `ComposableArrows C 5`. -/
def homMk₅ : f ⟶ g := homMkSucc app₀ (homMk₄ app₁ app₂ app₃ app₄ app₅ w₁ w₂ w₃ w₄) w₀

@[simp]
lemma homMk₅_app_zero : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 0 = app₀ := rfl

@[simp]
lemma homMk₅_app_one : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁ := rfl

@[simp]
lemma homMk₅_app_two :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨2, by valid⟩ = app₂ := rfl

@[simp]
lemma homMk₅_app_three :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨3, by valid⟩ = app₃ := rfl

@[simp]
lemma homMk₅_app_four :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨4, by valid⟩ = app₄ := rfl

@[simp]
lemma homMk₅_app_five :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨5, by valid⟩ = app₅ := rfl

end

@[ext]
lemma hom_ext₅ {f g : ComposableArrows C 5} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) (h₅ : app' φ 5 = app' φ' 5) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₄ h₁ h₂ h₃ h₄ h₅)

/-- Constructor for isomorphisms in `ComposableArrows C 5`. -/
@[simps]
def isoMk₅ {f g : ComposableArrows C 5}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4) (app₅ : f.obj' 5 ≅ g.obj' 5)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4)
    (w₄ : f.map' 4 5 ≫ app₅.hom = app₄.hom ≫ g.map' 4 5) :
    f ≅ g where
  hom := homMk₅ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom app₅.hom w₀ w₁ w₂ w₃ w₄
  inv := homMk₅ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv app₅.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])
    (by rw [map'_inv_eq_inv_map' (by valid) app₄ app₅ w₄])

lemma ext₅ {f g : ComposableArrows C 5}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4) (h₅ : f.obj' 5 = g.obj' 5)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm)
    (w₄ : f.map' 4 5 = eqToHom h₄ ≫ g.map' 4 5 ≫ eqToHom h₅.symm) :
    f = g :=
  ext_succ h₀ (ext₄ h₁ h₂ h₃ h₄ h₅ w₁ w₂ w₃ w₄) w₀

set_option backward.isDefEq.respectTransparency false in
lemma mk₅_surjective (X : ComposableArrows C 5) :
    ∃ (X₀ X₁ X₂ X₃ X₄ X₅ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
      (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅), X = mk₅ f₀ f₁ f₂ f₃ f₄ :=
  ⟨_, _, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4, X.map' 4 5,
    ext₅ rfl rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)⟩

/-- The `i`th arrow of `F : ComposableArrows C n`. -/
def arrow (i : ℕ) (hi : i < n := by valid) :
    ComposableArrows C 1 := mk₁ (F.map' i (i + 1))

section mkOfObjOfMapSucc

variable (obj : Fin (n + 1) → C) (mapSucc : ∀ (i : Fin n), obj i.castSucc ⟶ obj i.succ)

set_option backward.isDefEq.respectTransparency false in
lemma mkOfObjOfMapSucc_exists : ∃ (F : ComposableArrows C n) (e : ∀ i, F.obj i ≅ obj i),
    ∀ (i : ℕ) (hi : i < n), mapSucc ⟨i, hi⟩ =
      (e ⟨i, _⟩).inv ≫ F.map' i (i + 1) ≫ (e ⟨i + 1, _⟩).hom := by
  induction n with
  | zero => exact ⟨mk₀ (obj 0), fun 0 => Iso.refl _, fun i hi => by simp at hi⟩
  | succ n hn =>
    obtain ⟨F, e, h⟩ := hn (fun i => obj i.succ) (fun i => mapSucc i.succ)
    refine ⟨F.precomp (mapSucc 0 ≫ (e 0).inv), fun i => match i with
      | 0 => Iso.refl _
      | ⟨i + 1, hi⟩ => e _, fun i hi => ?_⟩
    obtain _ | i := i
    · simp
    · exact h i (by valid)

/-- Given `obj : Fin (n + 1) → C` and `mapSucc i : obj i.castSucc ⟶ obj i.succ`
for all `i : Fin n`, this is `F : ComposableArrows C n` such that `F.obj i` is
definitionally equal to `obj i` and such that `F.map' i (i + 1) = mapSucc ⟨i, hi⟩`. -/
noncomputable def mkOfObjOfMapSucc : ComposableArrows C n :=
  (mkOfObjOfMapSucc_exists obj mapSucc).choose.copyObj obj
    (mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose

@[simp]
lemma mkOfObjOfMapSucc_obj (i : Fin (n + 1)) :
    (mkOfObjOfMapSucc obj mapSucc).obj i = obj i := rfl

lemma mkOfObjOfMapSucc_map_succ (i : ℕ) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).map' i (i + 1) = mapSucc ⟨i, hi⟩ :=
  ((mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose_spec i hi).symm

set_option backward.isDefEq.respectTransparency false in
lemma mkOfObjOfMapSucc_arrow (i : ℕ) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).arrow i = mk₁ (mapSucc ⟨i, hi⟩) :=
  ext₁ rfl rfl (by simpa using mkOfObjOfMapSucc_map_succ obj mapSucc i hi)

end mkOfObjOfMapSucc

suppress_compilation in
variable (C n) in
/-- The equivalence `(ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n` obtained
by reversing the arrows. -/
@[simps!]
def opEquivalence : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n :=
  ((orderDualEquivalence (Fin (n + 1))).symm.trans
      Fin.revOrderIso.equivalence).symm.congrLeft.op.trans
    (Functor.leftOpRightOpEquiv (Fin (n + 1)) C)

end ComposableArrows

section

open ComposableArrows

variable {C} {D : Type*} [Category* D] (G : C ⥤ D) (n : ℕ)

/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` obtained by postcomposition
with a functor `C ⥤ D`. -/
@[simps!]
def Functor.mapComposableArrows :
    ComposableArrows C n ⥤ ComposableArrows D n :=
  (whiskeringRight _ _ _).obj G

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `(G.mapComposableArrows 1).obj (.mk₁ f)` and
`.mk₁ (G.map f)`. -/
@[simps!]
def Functor.mapComposableArrowsObjMk₁Iso {X Y : C} (f : X ⟶ Y) :
    (G.mapComposableArrows 1).obj (.mk₁ f) ≅ .mk₁ (G.map f) :=
  isoMk₁ (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between `(G.mapComposableArrows 2).obj (.mk₂ f g)` and
`.mk₂ (G.map f) (G.map g)`. -/
@[simps!]
def Functor.mapComposableArrowsObjMk₂Iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G.mapComposableArrows 2).obj (.mk₂ f g) ≅ .mk₂ (G.map f) (G.map g) :=
  isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _)

suppress_compilation in
/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` induced by `G : C ⥤ D`
commutes with `opEquivalence`. -/
def Functor.mapComposableArrowsOpIso :
    G.mapComposableArrows n ⋙ (opEquivalence D n).functor.rightOp ≅
      (opEquivalence C n).functor.rightOp ⋙ (G.op.mapComposableArrows n).op :=
  Iso.refl _

end

end CategoryTheory
