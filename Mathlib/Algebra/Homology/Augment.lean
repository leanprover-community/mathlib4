/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.augment
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Single

/-!
# Augmentation and truncation of `ℕ`-indexed (co)chain complexes.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V]

namespace ChainComplex

/-- The truncation of a `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [HasZeroMorphisms V] : ChainComplex V ℕ ⥤ ChainComplex V ℕ
    where
  obj C :=
    { pt := fun i => C.pt (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape' := fun i j w => by
        apply C.shape
        simpa }
  map C D f := { f := fun i => f.f (i + 1) }
#align chain_complex.truncate ChainComplex.truncate

/-- There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
def truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V ℕ) :
    truncate.obj C ⟶ (single₀ V).obj (C.pt 0) :=
  (toSingle₀Equiv (truncate.obj C) (C.pt 0)).symm ⟨C.d 1 0, by tidy⟩
#align chain_complex.truncate_to ChainComplex.truncateTo

-- PROJECT when `V` is abelian (but not generally?)
-- `[∀ n, exact (C.d (n+2) (n+1)) (C.d (n+1) n)] [epi (C.d 1 0)]` iff `quasi_iso (C.truncate_to)`
variable [HasZeroMorphisms V]

/-- We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) : ChainComplex V ℕ
    where
  pt i :=
    match i with
    | 0 => X
    | i + 1 => C.pt i
  d i j :=
    match i, j with
    | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape' i j s := by
    simp at s
    rcases i with (_ | _ | i) <;> cases j <;> unfold_aux <;> try simp
    · simpa using s
    · rw [C.shape]
      simpa [← Ne.def, Nat.succ_ne_succ] using s
  d_comp_d' i j k hij hjk :=
    by
    rcases i with (_ | _ | i) <;> rcases j with (_ | _ | j) <;> cases k <;> unfold_aux <;> try simp
    cases i
    · exact w
    · rw [C.shape, zero_comp]
      simpa using i.succ_succ_ne_one.symm
#align chain_complex.augment ChainComplex.augment

@[simp]
theorem augment_x_zero (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).pt 0 = X :=
  rfl
#align chain_complex.augment_X_zero ChainComplex.augment_x_zero

@[simp]
theorem augment_x_succ (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (augment C f w).pt (i + 1) = C.pt i :=
  rfl
#align chain_complex.augment_X_succ ChainComplex.augment_x_succ

@[simp]
theorem augment_d_one_zero (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (augment C f w).d 1 0 = f :=
  rfl
#align chain_complex.augment_d_one_zero ChainComplex.augment_d_one_zero

@[simp]
theorem augment_d_succ_succ (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j :=
  by
  dsimp [augment]
  rcases i with (_ | i)
  rfl
  rfl
#align chain_complex.augment_d_succ_succ ChainComplex.augment_d_succ_succ

/-- Truncating an augmented chain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncateAugment (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    truncate.obj (augment C f w) ≅ C
    where
  Hom := { f := fun i => 𝟙 _ }
  inv :=
    { f := fun i => 𝟙 _
      comm' := fun i j => by
        cases j <;>
          · dsimp
            simp }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
#align chain_complex.truncate_augment ChainComplex.truncateAugment

@[simp]
theorem truncateAugment_hom_f (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).Hom.f i = 𝟙 (C.pt i) :=
  rfl
#align chain_complex.truncate_augment_hom_f ChainComplex.truncateAugment_hom_f

@[simp]
theorem truncateAugment_inv_f (C : ChainComplex V ℕ) {X : V} (f : C.pt 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).pt i) :=
  rfl
#align chain_complex.truncate_augment_inv_f ChainComplex.truncateAugment_inv_f

@[simp]
theorem chainComplex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 :=
  by
  rw [C.shape]
  simpa using i.succ_succ_ne_one.symm
#align chain_complex.chain_complex_d_succ_succ_zero ChainComplex.chainComplex_d_succ_succ_zero

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : ChainComplex V ℕ) :
    augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C
    where
  Hom :=
    { f := fun i => by cases i <;> exact 𝟙 _
      comm' := fun i j => by
        rcases i with (_ | _ | i) <;> cases j <;>
          · dsimp
            simp }
  inv :=
    { f := fun i => by cases i <;> exact 𝟙 _
      comm' := fun i j => by
        rcases i with (_ | _ | i) <;> cases j <;>
          · dsimp
            simp }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
#align chain_complex.augment_truncate ChainComplex.augmentTruncate

@[simp]
theorem augmentTruncate_hom_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).Hom.f 0 = 𝟙 (C.pt 0) :=
  rfl
#align chain_complex.augment_truncate_hom_f_zero ChainComplex.augmentTruncate_hom_f_zero

@[simp]
theorem augmentTruncate_hom_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).Hom.f (i + 1) = 𝟙 (C.pt (i + 1)) :=
  rfl
#align chain_complex.augment_truncate_hom_f_succ ChainComplex.augmentTruncate_hom_f_succ

@[simp]
theorem augmentTruncate_inv_f_zero (C : ChainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.pt 0) :=
  rfl
#align chain_complex.augment_truncate_inv_f_zero ChainComplex.augmentTruncate_inv_f_zero

@[simp]
theorem augmentTruncate_inv_f_succ (C : ChainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.pt (i + 1)) :=
  rfl
#align chain_complex.augment_truncate_inv_f_succ ChainComplex.augmentTruncate_inv_f_succ

/-- A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

Ths is the inverse construction of `truncate_to`.
-/
def toSingle₀AsComplex [HasZeroObject V] (C : ChainComplex V ℕ) (X : V)
    (f : C ⟶ (single₀ V).obj X) : ChainComplex V ℕ :=
  let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w
#align chain_complex.to_single₀_as_complex ChainComplex.toSingle₀AsComplex

end ChainComplex

namespace CochainComplex

/-- The truncation of a `ℕ`-indexed cochain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [HasZeroMorphisms V] : CochainComplex V ℕ ⥤ CochainComplex V ℕ
    where
  obj C :=
    { pt := fun i => C.pt (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape' := fun i j w => by
        apply C.shape
        simpa }
  map C D f := { f := fun i => f.f (i + 1) }
#align cochain_complex.truncate CochainComplex.truncate

/-- There is a canonical chain map from the truncation of a cochain complex `C` to
the "single object" cochain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 0 1` in degree 0, and zero otherwise.
-/
def toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V ℕ) :
    (single₀ V).obj (C.pt 0) ⟶ truncate.obj C :=
  (fromSingle₀Equiv (truncate.obj C) (C.pt 0)).symm ⟨C.d 0 1, by tidy⟩
#align cochain_complex.to_truncate CochainComplex.toTruncate

variable [HasZeroMorphisms V]

/-- We can "augment" a cochain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0) :
    CochainComplex V ℕ
    where
  pt i :=
    match i with
    | 0 => X
    | i + 1 => C.pt i
  d i j :=
    match i, j with
    | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape' i j s := by
    simp at s
    rcases j with (_ | _ | j) <;> cases i <;> unfold_aux <;> try simp
    · simpa using s
    · rw [C.shape]
      simp only [ComplexShape.up_Rel]
      contrapose! s
      rw [← s]
  d_comp_d' i j k hij hjk :=
    by
    rcases k with (_ | _ | k) <;> rcases j with (_ | _ | j) <;> cases i <;> unfold_aux <;> try simp
    cases k
    · exact w
    · rw [C.shape, comp_zero]
      simp only [Nat.zero_eq, ComplexShape.up_Rel, zero_add]
      exact (Nat.one_lt_succ_succ _).Ne
#align cochain_complex.augment CochainComplex.augment

@[simp]
theorem augment_x_zero (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).pt 0 = X :=
  rfl
#align cochain_complex.augment_X_zero CochainComplex.augment_x_zero

@[simp]
theorem augment_x_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0)
    (i : ℕ) : (augment C f w).pt (i + 1) = C.pt i :=
  rfl
#align cochain_complex.augment_X_succ CochainComplex.augment_x_succ

@[simp]
theorem augment_d_zero_one (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0) :
    (augment C f w).d 0 1 = f :=
  rfl
#align cochain_complex.augment_d_zero_one CochainComplex.augment_d_zero_one

@[simp]
theorem augment_d_succ_succ (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0)
    (i j : ℕ) : (augment C f w).d (i + 1) (j + 1) = C.d i j :=
  rfl
#align cochain_complex.augment_d_succ_succ CochainComplex.augment_d_succ_succ

/-- Truncating an augmented cochain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncateAugment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0) (w : f ≫ C.d 0 1 = 0) :
    truncate.obj (augment C f w) ≅ C
    where
  Hom := { f := fun i => 𝟙 _ }
  inv :=
    { f := fun i => 𝟙 _
      comm' := fun i j => by
        cases j <;>
          · dsimp
            simp }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
#align cochain_complex.truncate_augment CochainComplex.truncateAugment

@[simp]
theorem truncateAugment_hom_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) : (truncateAugment C f w).Hom.f i = 𝟙 (C.pt i) :=
  rfl
#align cochain_complex.truncate_augment_hom_f CochainComplex.truncateAugment_hom_f

@[simp]
theorem truncateAugment_inv_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.pt 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) :
    (truncateAugment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).pt i) :=
  rfl
#align cochain_complex.truncate_augment_inv_f CochainComplex.truncateAugment_inv_f

@[simp]
theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 :=
  by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).Ne
#align cochain_complex.cochain_complex_d_succ_succ_zero CochainComplex.cochainComplex_d_succ_succ_zero

/-- Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augmentTruncate (C : CochainComplex V ℕ) :
    augment (truncate.obj C) (C.d 0 1) (C.d_comp_d _ _ _) ≅ C
    where
  Hom :=
    { f := fun i => by cases i <;> exact 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;>
          · dsimp
            simp }
  inv :=
    { f := fun i => by cases i <;> exact 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;>
          · dsimp
            simp }
  hom_inv_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id' := by
    ext i
    cases i <;>
      · dsimp
        simp
#align cochain_complex.augment_truncate CochainComplex.augmentTruncate

@[simp]
theorem augmentTruncate_hom_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).Hom.f 0 = 𝟙 (C.pt 0) :=
  rfl
#align cochain_complex.augment_truncate_hom_f_zero CochainComplex.augmentTruncate_hom_f_zero

@[simp]
theorem augmentTruncate_hom_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).Hom.f (i + 1) = 𝟙 (C.pt (i + 1)) :=
  rfl
#align cochain_complex.augment_truncate_hom_f_succ CochainComplex.augmentTruncate_hom_f_succ

@[simp]
theorem augmentTruncate_inv_f_zero (C : CochainComplex V ℕ) :
    (augmentTruncate C).inv.f 0 = 𝟙 (C.pt 0) :=
  rfl
#align cochain_complex.augment_truncate_inv_f_zero CochainComplex.augmentTruncate_inv_f_zero

@[simp]
theorem augmentTruncate_inv_f_succ (C : CochainComplex V ℕ) (i : ℕ) :
    (augmentTruncate C).inv.f (i + 1) = 𝟙 (C.pt (i + 1)) :=
  rfl
#align cochain_complex.augment_truncate_inv_f_succ CochainComplex.augmentTruncate_inv_f_succ

/-- A chain map from a single object cochain complex in degree zero to a cochain complex
can be reinterpreted as a cochain complex.

Ths is the inverse construction of `to_truncate`.
-/
def fromSingle₀AsComplex [HasZeroObject V] (C : CochainComplex V ℕ) (X : V)
    (f : (single₀ V).obj X ⟶ C) : CochainComplex V ℕ :=
  let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w
#align cochain_complex.from_single₀_as_complex CochainComplex.fromSingle₀AsComplex

end CochainComplex

