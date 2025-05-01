/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Connecting a chain complex and a cochain complex

Given a chain complex `K`: `... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0`,
a cochain complex `L`: `L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
a morphism `d₀: K.X 0 ⟶ L.X 0` satisfying the identifies `K.d 1 0 ≫ d₀ = 0`
and `d₀ ≫ L.d 0 1 = 0`, we construct a cochain complex indexed by `ℤ` of the form
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
where `K.X 0` lies in degree `-1` and `L.X 0` in degree `0`.

-/

universe v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace CochainComplex

variable (K : ChainComplex C ℕ) (L : CochainComplex C ℕ)

/-- Given `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, this data
allows to connect `K` and `L` in order to get a cochain complex indexed by `ℤ`,
see `ConnectData.cochainComplex`. -/
structure ConnectData where
  /-- the differential which connect `K` and `L` -/
  d₀ : K.X 0 ⟶ L.X 0
  comp_d₀ : K.d 1 0 ≫ d₀ = 0
  d₀_comp : d₀ ≫ L.d 0 1 = 0

namespace ConnectData

attribute [reassoc (attr := simp)] comp_d₀ d₀_comp

variable {K L} (h : ConnectData K L)

variable (K L) in
/-- Auxiliary definition for `ConnectData.cochainComplex`. -/
def X : ℤ → C
  | .ofNat n => L.X n
  | .negSucc n => K.X n

@[simp] lemma X_ofNat (n : ℕ) : X K L n = L.X n := rfl
@[simp] lemma X_negSucc (n : ℕ) : X K L (.negSucc n) = K.X n := rfl
@[simp] lemma X_zero : X K L 0 = L.X 0 := rfl
@[simp] lemma X_negOne : X K L (-1) = K.X 0 := rfl

/-- Auxiliary definition for `ConnectData.cochainComplex`. -/
def d : ∀ (n m : ℤ), X K L n ⟶ X K L m
  | .ofNat n, .ofNat m => L.d n m
  | .negSucc n, .negSucc m => K.d n m
  | .negSucc 0, .ofNat 0 => h.d₀
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, .ofNat _ => 0

@[simp] lemma d_ofNat (n m : ℕ) : h.d n m = L.d n m := rfl
@[simp] lemma d_negSucc (n m : ℕ) : h.d (.negSucc n) (.negSucc m) = K.d n m := by simp [d]
@[simp] lemma d_sub_one_zero : h.d (-1) 0 = h.d₀ := rfl
@[simp] lemma d_zero_one : h.d 0 1 = L.d 0 1 := rfl
@[simp] lemma d_sub_two_sub_one : h.d (-2) (-1) = K.d 1 0 := rfl

lemma shape (n m : ℤ) (hnm : n + 1 ≠ m) : h.d n m = 0 :=
  match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; omega)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using K.shape n m (by simp at hnm ⊢; omega)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ | n := n
    · obtain _ | m := m
      · simp at hnm
      · rfl
    · rfl

@[reassoc (attr := simp)]
lemma d_comp_d (n m p : ℤ) : h.d n m ≫ h.d m p = 0 := by
  by_cases hnm : n + 1 = m; swap
  · rw [h.shape n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [h.shape m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; omega
    simp only [Int.ofNat_eq_coe, X_ofNat, d_ofNat, HomologicalComplex.d_comp_d]
  · obtain rfl : m = 0 := by omega
    obtain rfl : p = 1 := by omega
    simp
  · obtain rfl : m = -1 := by omega
    obtain rfl : p = 0 := by omega
    simp
  · obtain rfl : m = .negSucc (n + 1) := by omega
    obtain rfl : p = .negSucc n := by omega
    simp

/-- Given `h : ConnectData K L` where `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`,
this is the cochain complex indexed by `ℤ` obtained by connecting `K` and `L`:
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`. -/
@[simps]
def cochainComplex : CochainComplex C ℤ where
  X := X K L
  d := h.d
  shape := h.shape

end ConnectData

end CochainComplex
