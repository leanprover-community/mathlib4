/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Connecting a chain complex and a cochain complex

Given a chain complex `K`: `... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0`,
a cochain complex `L`: `L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
a morphism `d₀ : K.X 0 ⟶ L.X 0` satisfying the identifies `K.d 1 0 ≫ d₀ = 0`
and `d₀ ≫ L.d 0 1 = 0`, we construct a cochain complex indexed by `ℤ` of the form
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
where `K.X 0` lies in degree `-1` and `L.X 0` in degree `0`.

## Main definitions

Say `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, so `... ⟶ K₂ ⟶ K₁ ⟶ K₀`
and `L⁰ ⟶ L¹ ⟶ L² ⟶ ...`.

* `ConnectData K L`: an auxiliary structure consisting of `d₀ : K₀ ⟶ L⁰` "connecting" the
  complexes and proofs that the induced maps `K₁ ⟶ K₀ ⟶ L⁰` and `K₀ ⟶ L⁰ ⟶ L¹` are both zero.

Now say `h : ConnectData K L`.

* `CochainComplex.ConnectData.cochainComplex h` : the induced ℤ-indexed complex
  `... ⟶ K₁ ⟶ K₀ ⟶ L⁰ ⟶ L¹ ⟶ ...`
* `CochainComplex.ConnectData.homologyIsoPos h (n : ℕ) (m : ℤ)` : if `m = n + 1`,
  the isomorphism `h.cochainComplex.homology m ≅ L.homology (n + 1)`
* `CochainComplex.ConnectData.homologyIsoNeg h (n : ℕ) (m : ℤ)` : if `m = -(n + 2)`,
  the isomorphism `h.cochainComplex.homology m ≅ K.homology (n + 1)`

## TODO

* Computation of `h.cochainComplex.homology k` when `k = 0` or `k = -1`.

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
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; grind)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using K.shape n m (by simp at hnm ⊢; grind)
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
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; grind
    simp only [Int.ofNat_eq_coe, X_ofNat, d_ofNat, HomologicalComplex.d_comp_d]
  · obtain rfl : m = 0 := by grind
    obtain rfl : p = 1 := by grind
    simp
  · obtain rfl : m = -1 := by grind
    obtain rfl : p = 0 := by grind
    simp
  · obtain rfl : m = .negSucc (n + 1) := by grind
    obtain rfl : p = .negSucc n := by grind
    simp

/-- Given `h : ConnectData K L` where `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`,
this is the cochain complex indexed by `ℤ` obtained by connecting `K` and `L`:
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`. -/
@[simps]
def cochainComplex : CochainComplex C ℤ where
  X := X K L
  d := h.d
  shape := h.shape

open HomologicalComplex

/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `L` in degrees `≥ 0`. -/
@[simps!]
def restrictionGEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntGE 0) ≅ L :=
  Hom.isoOfComponents
    (fun n ↦ h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := n) (i' := n) (by simp)) (by
    rintro n _ rfl
    dsimp only
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntGE 0)) _ (i' := n)
      (j' := (n + 1 : ℕ)) (by simp) (by simp), cochainComplex_d, h.d_ofNat]
    simp)

/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `K` in degrees `≤ -1`. -/
@[simps!]
def restrictionLEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntLE (-1)) ≅ K :=
  Hom.isoOfComponents
    (fun n ↦ h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; grind)) (by
    rintro _ n rfl
    dsimp only
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) (by dsimp; grind) (by dsimp; grind),
      cochainComplex_d, d_negSucc]
    simp)

/-- Given `h : ConnectData K L` and `n : ℕ`, the homology
of `h.cochainComplex` in degree `n + 1` identifies to the homology of `L` in degree `n + 1`. -/
noncomputable def homologyIsoPos (n : ℕ) (m : ℤ)
    [h.cochainComplex.HasHomology m] [L.HasHomology (n + 1)]
    (hm : m = (n + 1 : ℕ)) :
    h.cochainComplex.homology m ≅ L.homology (n + 1) :=
  have := hasHomology_of_iso h.restrictionGEIso.symm (n + 1)
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntGE 0) n (n + 1) (n + 2) (by simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by simp; grind) (by simp; grind)
      (by simp; grind) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionGEIso (n + 1)

/-- Given `h : ConnectData K L` and `n : ℕ`, the homology
of `h.cochainComplex` in degree `-(n + 2)` identifies to the homology of `K` in degree `n + 1`. -/
noncomputable def homologyIsoNeg (n : ℕ) (m : ℤ)
    [h.cochainComplex.HasHomology m] [K.HasHomology (n + 1)]
    (hm : m = -(n + 2 : ℕ)) :
    h.cochainComplex.homology m ≅ K.homology (n + 1) :=
  have := hasHomology_of_iso h.restrictionLEIso.symm (n + 1)
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntLE (-1)) (n + 2) (n + 1) n (by simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1)
      (by simp; grind) (by simp; grind) (by simp; grind) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionLEIso (n + 1)

end ConnectData

end CochainComplex
