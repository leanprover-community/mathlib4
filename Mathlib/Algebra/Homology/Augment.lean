/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Homology.Single

/-!
# Augmentation and truncation of `ℕ`-indexed (co)chain complexes.
-/


noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V]

namespace ChainComplex

/-- The truncation of an `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [HasZeroMorphisms V] : ChainComplex V ℕ ⥤ ChainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => C.shape _ _ <| by simpa }
  map f := { f := fun i => f.f (i + 1) }

/-- There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
def truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V ℕ) :
    truncate.obj C ⟶ (single₀ V).obj (C.X 0) :=
  (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by simp⟩

-- PROJECT when `V` is abelian (but not generally?)
-- `[∀ n, Exact (C.d (n+2) (n+1)) (C.d (n+1) n)] [Epi (C.d 1 0)]` iff `QuasiIso (C.truncate_to)`
variable [HasZeroMorphisms V]

/-- We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    ChainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape
    | 1, 0, h => absurd rfl h
    | _ + 2, 0, _ => rfl
    | 0, _, _ => rfl
    | i + 1, j + 1, h => by
      simp only; exact C.shape i j (Nat.succ_ne_succ_iff.1 h)
  d_comp_d'
    | _, _, 0, rfl, rfl => w
    | _, _, k + 1, rfl, rfl => C.d_comp_d _ _ _

@[simp]
theorem augment_X_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
theorem augment_X_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
theorem augment_d_one_zero (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).d 1 0 = f :=
  rfl

@[simp]
theorem augment_d_succ_succ (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j := by
  cases i <;> rfl

/-- Truncating an augmented chain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncateAugment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext (_ | i) <;> simp
  inv_hom_id := by
    ext (_ | i) <;> simp

@[simp]
theorem truncateAugment_hom_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
theorem truncateAugment_inv_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
theorem chainComplex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : ChainComplex V ℕ) :
    augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        match i with
        | 0 | 1 | n+2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  inv :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        match i with
          | 0 | 1 | n+2 =>
          rcases j with - | j <;> dsimp [augment, truncate] <;> simp
    }
  hom_inv_id := by
    ext i
    cases i <;> simp
  inv_hom_id := by
    ext i
    cases i <;> simp

@[simp]
theorem augmentTruncate_hom_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augmentTruncate_hom_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
theorem augmentTruncate_inv_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augmentTruncate_inv_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

This is the inverse construction of `truncateTo`.
-/
def toSingle₀AsComplex [HasZeroObject V] (C : ChainComplex V ℕ) (X : V)
    (f : C ⟶ (single₀ V).obj X) : ChainComplex V ℕ :=
  let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

end ChainComplex

namespace CochainComplex

/-- The truncation of an `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [HasZeroMorphisms V] : CochainComplex V ℕ ⥤ CochainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

/-- There is a canonical chain map from the truncation of a cochain complex `C` to
the "single object" cochain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 0 1` in degree 0, and zero otherwise.
-/
def toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V ℕ) :
    (single₀ V).obj (C.X 0) ⟶ truncate.obj C :=
  (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by simp⟩

variable [HasZeroMorphisms V]

/-- We can "augment" a cochain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    CochainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape i j s := by
    rcases j with (_ | _ | j) <;> cases i <;> try simp
    · contradiction
    · rw [C.shape]
      simp only [ComplexShape.up_Rel] at ⊢ s
      contrapose! s
      rw [← s]
  d_comp_d' i j k hij hjk := by
    rcases k with (_ | _ | k) <;> rcases j with (_ | _ | j) <;> cases i <;> try simp
    cases k
    · exact w
    · rw [C.shape, comp_zero]
      simp only [ComplexShape.up_Rel, zero_add]
      exact (Nat.one_lt_succ_succ _).ne

@[simp]
theorem augment_X_zero (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).X 0 = X :=
  rfl

@[simp]
theorem augment_X_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i : ℕ) : (augment C f w).X (i + 1) = C.X i :=
  rfl

@[simp]
theorem augment_d_zero_one (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).d 0 1 = f :=
  rfl

@[simp]
theorem augment_d_succ_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j :=
  rfl

/-- Truncating an augmented cochain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncateAugment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;> simp }
  hom_inv_id := by
    ext i
    cases i <;> simp
  inv_hom_id := by
    ext i
    cases i <;> simp

@[simp]
theorem truncateAugment_hom_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) : (truncateAugment C f w).hom.f i = 𝟙 (C.X i) :=
  rfl

@[simp]
theorem truncateAugment_inv_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
  rfl

@[simp]
theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : CochainComplex V ℕ) :
    augment (truncate.obj C) (C.d 0 1) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;> aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> rcases i with - | i <;> aesop }

@[simp]
theorem augmentTruncate_hom_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).hom.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augmentTruncate_hom_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).hom.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

@[simp]
theorem augmentTruncate_inv_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.X 0) :=
  rfl

@[simp]
theorem augmentTruncate_inv_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.X (i + 1)) :=
  rfl

/-- A chain map from a single object cochain complex in degree zero to a cochain complex
can be reinterpreted as a cochain complex.

This is the inverse construction of `toTruncate`.
-/
def fromSingle₀AsComplex [HasZeroObject V] (C : CochainComplex V ℕ) (X : V)
    (f : (single₀ V).obj X ⟶ C) : CochainComplex V ℕ :=
  let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

end CochainComplex
