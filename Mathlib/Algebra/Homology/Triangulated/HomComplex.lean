/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Linarith

--import algebra.homology.homotopy
--import algebra.homology.additive
--import algebra.category.Group.abelian
--import algebra.homology.short_exact.preadditive
--import for_mathlib.algebra.homology.homological_complex_X_iso_of_eq

open CategoryTheory Category Preadditive Limits

universe v u


namespace HomologicalComplex

variable {C ι : Type _} [Category C] [HasZeroMorphisms C]
  {c : ComplexShape ι}

def XIsoOfEq (K : HomologicalComplex C c) {p q : ι} (h : p = q) :
  K.X p ≅ K.X q := eqToIso (by rw [h])

end HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

namespace HomComplex

def ε (n : ℤ) : ℤ := (-1 : Units ℤ) ^ n

lemma ε_add (n₁ n₂ : ℤ) : ε (n₁ + n₂) = ε n₁ * ε n₂ := by
  simp only [ε, ← Units.val_mul, ← Units.ext_iff, zpow_add]

@[simp]
lemma ε_0 : ε 0 = 1 := rfl

@[simp]
lemma ε_1 : ε 1 = -1 := rfl

lemma ε_succ (n : ℤ) : ε (n + 1) = - ε n := by
  simp only [ε_add, ε_1, mul_neg, mul_one]

lemma ε_even (n : ℤ) (hn : Even n) : ε n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [ε, ← Units.ext_iff, zpow_add, ← mul_zpow, mul_neg, mul_one, neg_neg, one_zpow]

lemma ε_odd (n : ℤ) (hn : Odd n) : ε n = -1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [ε_add, ε_even (2 * k) ⟨k, two_mul k⟩, one_mul, ε_1]

lemma ε_eq_one_iff (n : ℤ) : ε n = 1 ↔ Even n := by
  constructor
  . intro h
    rw [Int.even_iff_not_odd]
    intro h'
    rw [ε_odd _ h'] at h
    simp only at h
  . exact ε_even n

lemma ε_eq_neg_one_iff (n : ℤ) : ε n = -1 ↔ Odd n := by
  constructor
  . intro h
    rw [Int.odd_iff_not_even]
    intro h'
    rw [ε_even _ h'] at h
    simp only at h
  . exact ε_odd n

lemma ε_neg (n : ℤ) : ε (-n) = ε n := by
  dsimp [ε]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

lemma ε_sub (n₁ n₂ : ℤ) : ε (n₁ - n₂) = ε n₁ * ε n₂ := by
  simp only [sub_eq_add_neg, ε_add, ε_neg]

lemma ε_eq_iff (n₁ n₂ : ℤ) : ε n₁ = ε n₂ ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  . rw [ε_even _ h₂, Int.even_sub, ε_eq_one_iff]
    tauto
  . rw [← Int.odd_iff_not_even] at h₂
    rw [ε_odd _ h₂, Int.even_sub, ε_eq_neg_one_iff,
      Int.even_iff_not_odd, Int.even_iff_not_odd]
    tauto

@[simp]
lemma mul_ε_self (n : ℤ) : ε n * ε n = 1 := by
  simpa only [← ε_add] using ε_even _ (even_add_self n)

@[simp]
lemma ε_mul_self (n : ℤ) : ε (n * n) = ε n := by
  by_cases hn : Even n
  . rw [ε_even _ hn, ε_even]
    rw [Int.even_mul]
    tauto
  . rw [← Int.odd_iff_not_even] at hn
    rw [ε_odd _ hn, ε_odd]
    rw [Int.odd_mul]
    tauto

structure Triplet (n : ℤ) := (p : ℤ) (q : ℤ) (hpq : p + n = q)

variable (F G)

def Cochain := ∀ (T : Triplet n), F.X T.p ⟶ G.X T.q

instance : AddCommGroup (Cochain F G n) := by
  dsimp only [Cochain]
  infer_instance

namespace Cochain

variable {F G n}

def mk (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n :=
  fun ⟨p, q, hpq⟩ => v p q hpq

def v (γ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
  F.X p ⟶ G.X q := γ ⟨p, q, hpq⟩

@[simp]
lemma mk_v (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q)
    (p q : ℤ) (hpq : p + n = q) : (Cochain.mk v).v p q hpq = v p q hpq := rfl

lemma congr_v {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : ℤ) (hpq : p + n = q) :
  z₁.v p q hpq = z₂.v p q hpq := by subst h ; rfl

@[ext]
lemma ext (z₁ z₂ : Cochain F G n)
    (h : ∀ (T : Triplet n), z₁.v T.p T.q T.hpq = z₂.v T.p T.q T.hpq) : z₁ = z₂ := by
    funext
    apply h

@[ext 1100]
lemma ext₀ (z₁ z₂ : Cochain F G 0)
    (h : ∀ (p : ℤ), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂ := by
    ext ⟨p, q, hpq⟩
    obtain rfl : q = p := by rw [← hpq, add_zero]
    exact h q

@[simp]
lemma zero_v {n : ℤ} (p q : ℤ) (hpq : p + n = q) : (0 : Cochain F G n).v p q hpq = 0 := rfl

@[simp]
lemma add_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁+z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq := rfl

@[simp]
lemma sub_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁-z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq := rfl

@[simp]
lemma neg_v {n : ℤ} (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (-z).v p q hpq = - (z.v p q hpq) := rfl

@[simp]
lemma zsmul_v {n k : ℤ} (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

def ofHoms (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) : Cochain F G 0 :=
Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]
lemma ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
    (ofHoms ψ).v p p (add_zero p) = ψ p := by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]
lemma ofHoms_zero : ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0 := by aesop_cat

@[simp]
lemma ofHoms_v_comp_d (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHoms ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q' := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]
lemma d_comp_ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p' p q  : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

def ofHom (φ : F ⟶ G) : Cochain F G 0 := ofHoms (fun p => φ.f p)

@[simp]
lemma ofHom_zero : ofHom (0 : F ⟶ G) = 0 := by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

@[simp]
lemma ofHom_v (φ : F ⟶ G) (p : ℤ) : (ofHom φ).v p p (add_zero p) = φ.f p := by
  simp only [ofHom, ofHoms_v]

@[simp]
lemma ofHom_v_comp_d (φ : F ⟶ G) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' :=
by simp only [ofHom, ofHoms_v_comp_d]

@[simp]
lemma d_comp_ofHom_v (φ : F ⟶ G) (p' p q  : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHom φ).v p q hpq = F.d p' q ≫ φ.f q := by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]
def ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1) :=
  Cochain.mk (fun p q _ => ho.hom p q)

@[reassoc (attr := simp)]
lemma v_comp_X_iso_of_eq_hom
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

protected def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
    Cochain F K n₁₂ := Cochain.mk (fun p q hpq => z₁.v p (p+n₁) rfl ≫ z₂.v (p+n₁) q (by linarith))

--notation a " ≫[":81 b "] " c:80 => Cochain.comp a c b
notation a " ≫[" b "] " c:80 => Cochain.comp a c b

protected lemma comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : ℤ) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁ ; rfl

protected lemma zero_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (0 : Cochain F G n₁).comp z₂ h = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), zero_v, zero_comp]

@[simp]
protected lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁+z₁').comp z₂ h = z₁.comp z₂ h + z₁'.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), add_v, add_comp]

@[simp]
protected lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁-z₁').comp z₂ h = z₁.comp z₂ h - z₁'.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), sub_v, sub_comp]

@[simp]
protected lemma neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₁).comp z₂ h = -z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), neg_v, neg_comp]

@[simp]
protected lemma zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), zsmul_v, zsmul_comp]

@[simp]
lemma zero_cochain_comp_v {n : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n)
    (p q : ℤ) (hpq : p + n = q) : (z₁.comp z₂ (zero_add n)).v p q hpq =
      z₁.v p p (add_zero p) ≫ z₂.v p q hpq :=
  Cochain.comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

lemma zero_cochain_comp_v' {n : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n)
    (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + 0 = p₂) (h₂₃ : p₂ + n =p₃) :
    (z₁.v p₁ p₂ h₁₂ ≫ z₂.v p₂ p₃ h₂₃ : F.X p₁ ⟶ K.X p₃) =
      z₁.v p₁ p₁ (add_zero p₁) ≫ z₂.v p₁ p₃ (show p₁ + n = p₃ by rw [← h₂₃, ← h₁₂, add_zero]) := by
  rw [add_zero] at h₁₂
  subst h₁₂
  rfl

@[simp]
protected lemma id_comp {n : ℤ} (z₂ : Cochain F G n) :
    (Cochain.ofHom (𝟙 F)).comp z₂ (zero_add n) = z₂ := by
  ext ⟨p, q, hpq⟩
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]
protected lemma comp_zero {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (0 : Cochain G K n₂) h = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), zero_v, comp_zero]

@[simp]
protected lemma comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂+z₂') h = z₁.comp z₂ h + z₁.comp z₂' h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), add_v, comp_add]

@[simp]
protected lemma comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂-z₂') h = z₁.comp z₂ h - z₁.comp  z₂' h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), sub_v, comp_sub]

@[simp]
protected lemma comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  (h : n₁ + n₂ = n₁₂) : z₁.comp (-z₂) h = -z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), neg_v, comp_neg]

@[simp]
protected lemma comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  (h : n₁ + n₂ = n₁₂ ) : z₁.comp (k • z₂) h = k • z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ h p _ q rfl (by linarith), zsmul_v, comp_zsmul]

@[simp]
lemma comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0)
    (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq =
      z₁.v p q hpq ≫ z₂.v q q (add_zero q) :=
  Cochain.comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

lemma comp_zero_cochain_v' (z₁ : Cochain F G n) (z₂ : Cochain G K 0)
    (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 0 = p₃) :
    (z₁.v p₁ p₂ h₁₂ ≫ z₂.v p₂ p₃ h₂₃ : F.X p₁ ⟶ K.X p₃) =
  z₁.v p₁ p₃ (show p₁ + n = p₃ by rw [← h₂₃, h₁₂, add_zero]) ≫ z₂.v p₃ p₃ (add_zero p₃) := by
  rw [add_zero] at h₂₃
  subst h₂₃
  rfl

@[simp]
protected lemma comp_id {n : ℤ} (z₁ : Cochain F G n) :
    z₁.comp (Cochain.ofHom (𝟙 G)) (add_zero n) = z₁ := by
  ext ⟨p, q, hpq⟩
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]
lemma ofHoms_comp (φ : ∀ (p : ℤ), F.X p ⟶ G.X p) (ψ : ∀ (p : ℤ), G.X p ⟶ K.X p) :
    (ofHoms φ).comp (ofHoms ψ) (zero_add 0) = ofHoms (fun p => φ p ≫ ψ p) := by aesop_cat

@[simp]
lemma ofHom_comp (f : F ⟶ G) (g : G ⟶ K) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0) := by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

lemma comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      z₁.comp (z₂.comp z₃ h₂₃) (show n₁ + n₂₃ = n₁₂₃ by rw [← h₂₃, ← h₁₂₃, add_assoc]) := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [Cochain.comp_v _ _ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) p (p + n₁₂) q rfl (by linarith),
    Cochain.comp_v _ _ h₁₂ p (p+n₁) (p+n₁₂) rfl (by linarith),
    Cochain.comp_v _ _ (show n₁ + n₂₃ = n₁₂₃ by linarith) p (p+n₁) q rfl (by linarith),
    Cochain.comp_v _ _ h₂₃ (p+n₁) (p+n₁₂) q (by linarith) (by linarith), assoc]

@[simp]
lemma comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : ℤ}
    (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₂₃ : n₂ + n₃ = n₂₃) :
  (z₁.comp z₂ (zero_add n₂)).comp z₃ h₂₃ =
    z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃) :=
  comp_assoc z₁ z₂ z₃ (zero_add n₂) h₂₃ (by linarith)

@[simp]
lemma comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) :
    (z₁.comp z₂ (add_zero n₁)).comp z₃ h₁₃ =
      z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃ :=
  comp_assoc z₁ z₂ z₃ (add_zero n₁) (zero_add n₃) (by linarith)

@[simp]
lemma comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃ (add_zero n₁₂) =
      z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂ :=
  comp_assoc z₁ z₂ z₃ h₁₂ (add_zero n₂) (by linarith)

variable (K)

def diff : Cochain K K 1 := Cochain.mk (fun p q _ => K.d p q)

@[simp]
lemma diff_v (p q : ℤ) (hpq : p + 1 = q) :
  (diff K).v p q hpq = K.d p q := rfl

end Cochain

/- Differentials -/

variable {F G}

def δ (z : Cochain F G n) : Cochain F G m :=
  Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    ε (n + 1) • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))

lemma δ_v (hnm : n + 1 = m) (z : Cochain F G n) (p q : ℤ) (hpq : p + m = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) : (δ n m z).v p q hpq =
    z.v p q₁ (by rw [hq₁, ← hpq, ← hnm, ← add_assoc, add_sub_cancel]) ≫ G.d q₁ q
      + ε (n + 1) • F.d p q₂ ≫ z.v q₂ q (by rw [← hq₂, add_assoc, add_comm 1, hnm, hpq]) := by
  obtain rfl : q₁ = p + n := by linarith
  obtain rfl : q₂ = p + m - n := by linarith
  rfl

lemma δ_shape (hnm : ¬ n + 1 = m) (z : Cochain F G n) : δ n m z = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp [δ, Cochain.v, Cochain.mk]
  rw [F.shape, G.shape, comp_zero, zero_add, zero_comp, smul_zero]
  . rfl
  all_goals
    change ¬ _=_
    rintro h
    apply hnm
    linarith

variable (F G)

def δ_hom : Cochain F G n →+ Cochain F G m where
  toFun := δ n m
  map_zero' := by
    ext ⟨p, q, hpq⟩
    simp [δ]
  map_add' _ _ := by
    dsimp only
    by_cases n + 1 = m
    . ext ⟨p, q, hpq⟩
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, zsmul_add]
      abel
    . simp only [δ_shape _ _ h, add_zero]

variable {F G}

@[simp] lemma δ_add (z₁ z₂ : Cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom F G n m).map_add z₁ z₂

@[simp] lemma δ_sub (z₁ z₂ : Cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom F G n m).map_sub z₁ z₂

@[simp] lemma δ_zero : δ n m (0 : Cochain F G n) = 0 := (δ_hom F G n m).map_zero

@[simp] lemma δ_neg (z : Cochain F G n) : δ n m (-z) = - δ n m z :=
  (δ_hom F G n m).map_neg z

@[simp] lemma δ_zsmul (k : ℤ) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom F G n m).map_zsmul z k

lemma δδ (n₀ n₁ n₂ : ℤ) (z : Cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂ ; swap ; rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁ ; swap ; rw [δ_shape _ _ h₀₁, δ_zero]
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q-1) (by linarith) (q-2) _ (by linarith) rfl,
    δ_v n₀ n₁ h₀₁ z (p+1) q (by linarith) _ (p+2) rfl (by linarith),
    ← h₀₁, ε_succ, neg_smul, sub_add_cancel, add_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, neg_comp, zero_add, neg_neg, comp_add,
    comp_neg, comp_zsmul, HomologicalComplex.d_comp_d_assoc, zero_comp, zsmul_zero,
    neg_zero, add_zero, zsmul_comp, add_left_neg]

#exit

lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂)
  (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂+1 = m₁₂) (h₁ : n₁+1 = m₁) (h₂ : n₂+1 = m₂) :
δ n₁₂ m₁₂ (cochain.comp z₁ z₂ h) = cochain.comp z₁ (δ n₂ m₂ z₂) (by linarith) + ε n₂ • cochain.comp (δ n₁ m₁ z₁) z₂ (by linarith) :=
begin
  substs h₁₂ h₁ h₂,
  ext,
  have eq : ε (n₁₂ + 1) = ε n₂ * ε (n₁+1),
  { rw ← ε_add, congr' 1, linarith, },
  simp only [cochain.add_v, cochain.zsmul_v,
    cochain.comp_v z₁ (δ n₂ (n₂+1) z₂) (show n₁₂+1=n₁+(n₂+1), by linarith) p _ q rfl (by linarith),
    cochain.comp_v (δ n₁ (n₁+1) z₁) z₂ (show n₁₂+1=_, by linarith) p (p+n₁+1) q (by linarith) (by linarith),
    cochain.comp_v z₁ z₂ h p (p+n₁) (p+n₁₂) rfl (by linarith),
    cochain.comp_v z₁ z₂ h (p+1) (p+n₁+1) q (by linarith) (by linarith),
    δ_v n₁₂ _ rfl (cochain.comp z₁ z₂ h) p q hpq (p+n₁₂) _ (by linarith) rfl,
    δ_v n₁ (n₁+1) rfl z₁ p (p+n₁+1) (by linarith) (p+n₁) (p+1) (by linarith) rfl,
    δ_v n₂ (n₂+1) rfl z₂ (p+n₁) q (by linarith) (p+n₁₂) (p+n₁+1) (by linarith) rfl,
    assoc, comp_add, comp_zsmul, zsmul_add, add_comp, zsmul_comp, smul_smul, eq,
    ε_add n₂ 1, ε_1, mul_neg, mul_one, neg_zsmul, comp_neg, ← add_assoc],
  suffices : ∀ (a b c : F.X p ⟶ K.X q), a+b=a+(-c)+c+b,
  { apply this, },
  intros a b c,
  abel,
end

@[simp]
lemma δ_comp_of_first_is_zero_cochain {n₂ : ℤ} (z₁ : cochain F G 0) (z₂ : cochain G K n₂)
  (m₂ : ℤ) (h₂ : n₂+1 = m₂) :
δ n₂ m₂ (cochain.comp z₁ z₂ (zero_add n₂).symm) =
  cochain.comp z₁ (δ n₂ m₂ z₂) (by linarith) + ε n₂ • cochain.comp (δ 0 1 z₁) z₂ (by linarith) :=
δ_comp z₁ z₂ (zero_add n₂).symm 1 m₂ m₂ h₂ (zero_add 1) h₂

@[simp]
lemma δ_comp_of_second_is_zero_cochain {n₁ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K 0)
  (m₁ : ℤ) (h₁ : n₁+1 = m₁) : δ n₁ m₁ (cochain.comp z₁ z₂ (add_zero n₁).symm) =
  cochain.comp z₁ (δ 0 1 z₂) h₁.symm + cochain.comp (δ n₁ m₁ z₁) z₂ (add_zero m₁).symm :=
by simp only [δ_comp z₁ z₂ (add_zero n₁).symm m₁ 1 m₁ h₁ h₁ (zero_add 1), ε_0, one_zsmul]

end hom_complex

variables (F G)

open hom_complex

def hom_complex : cochain_complex AddCommGroup ℤ :=
{ X := λ i, AddCommGroup.of (cochain F G i),
  d := λ i j, AddCommGroup.of_hom (δ_hom F G i j),
  shape' := λ i j hij, by { ext1 z, exact δ_shape i j hij z, },
  d_comp_d' := λ i j k hij hjk, by { ext1 f, apply δδ, } }

namespace hom_complex

def cocycle : add_subgroup (cochain F G n) :=
add_monoid_hom.ker ((hom_complex F G).d n (n+1))

namespace cocycle

variables {F G}

lemma mem_iff (hnm : n+1=m) (z : cochain F G n) :
  z ∈ cocycle F G n ↔ δ n m z = 0 :=
by { subst hnm, refl, }

variable {n}

@[simps]
def mk (z : cochain F G n) (m : ℤ) (hnm : n+1 = m) (h : δ n m z = 0) : cocycle F G n :=
⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
lemma δ_eq_zero {n : ℤ} (z : cocycle F G n) (m : ℤ) : δ n m (z : cochain F G n) = 0 :=
begin
  by_cases n+1=m,
  { rw ← mem_iff n m h,
    exact z.2, },
  { apply δ_shape n m h, }
end

@[simps]
def of_hom (φ : F ⟶ G) : cocycle F G 0 := mk (cochain.of_hom φ) 1 (zero_add 1)
begin
  ext,
  simp only [δ_v 0 1 (zero_add 1) _ p q hpq p q (by linarith) hpq,
    cochain.of_hom_v, homological_complex.hom.comm, ε_1, neg_smul, one_zsmul,
    add_right_neg, cochain.zero_v, zero_add],
end

@[simp]
lemma δ_cochain_of_hom (φ : F ⟶ G) : δ 0 1 (cochain.of_hom φ) = 0 :=
by apply δ_eq_zero (of_hom φ)

@[simps]
def hom_of (z : cocycle F G 0) : F ⟶ G :=
{ f := λ i, (z : cochain F G 0).v i i (add_zero i).symm,
  comm' := λ i j hij, begin
    change i+1=j at hij,
    have hz₁ := z.2,
    rw mem_iff 0 1 (zero_add 1) at hz₁,
    simpa only [δ_v 0 1 (zero_add 1) z.1 i j hij.symm i j (by linarith) hij.symm,
      zero_add, ε_1, neg_smul, one_zsmul, cochain.zero_v, add_neg_eq_zero]
      using cochain.congr_v hz₁ i j hij.symm,
  end, }

@[simp]
lemma hom_of_of_hom_eq_self (φ : F ⟶ G) : hom_of (of_hom φ) = φ :=
by { ext i, simp only [of_hom, hom_of_f, mk_coe, cochain.of_hom_v], }

@[simp]
lemma of_hom_hom_of_eq_self (z : cocycle F G 0) : of_hom (hom_of z) = z :=
begin
  ext,
  simp only [of_hom, mk_coe, cochain.of_hom_v, hom_of_f],
end

@[simp]
lemma cochain_of_hom_hom_of_eq_coe (z : cocycle F G 0) :
  (cochain.of_hom (hom_of z) : cochain F G 0) = (z : cochain F G 0) :=
by simpa only [subtype.ext_iff] using of_hom_hom_of_eq_self z

variables (F G)

@[simps]
def equiv_hom : (F ⟶ G) ≃+ cocycle F G 0 :=
{ to_fun := of_hom,
  inv_fun := hom_of,
  left_inv := hom_of_of_hom_eq_self,
  right_inv := of_hom_hom_of_eq_self,
  map_add' := λ φ₁ φ₂, begin
    ext,
    simp only [of_hom, cochain.of_hom, cochain.of_homs, cochain.mk, cochain.v,
      homological_complex.add_f_apply, mk_coe, eq_to_hom_refl, comp_id,
      add_subgroup.coe_add, pi.add_apply],
  end, }

def of_d : cocycle K K 1 :=
cocycle.mk (cochain.of_d K) 2 rfl begin
  ext p q hpq,
  simp only [δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, cochain.of_d_v,
    homological_complex.d_comp_d, smul_zero, add_zero, cochain.zero_v],
end

end cocycle

namespace cochain

variables {F G}

lemma of_hom_injective {f₁ f₂ : F ⟶ G} (h : of_hom f₁ = of_hom f₂) : f₁ = f₂ :=
begin
  rw [← cocycle.hom_of_of_hom_eq_self f₁, ← cocycle.hom_of_of_hom_eq_self f₂],
  congr' 1,
  ext1,
  simpa only [cocycle.of_hom_coe] using h,
end

end cochain

variables {F G}

@[simps]
def equiv_homotopy (φ₁ φ₂ : F ⟶ G) :
  homotopy φ₁ φ₂ ≃
    { z : cochain F G (-1) // cochain.of_hom φ₁ = δ (-1) 0 z + cochain.of_hom φ₂ } :=
{ to_fun := λ ho, begin
    refine ⟨cochain.of_homotopy ho, _⟩,
    ext,
    have comm := ho.comm p,
    rw [d_next_eq ho.hom rfl, prev_d_eq ho.hom (sub_add_cancel p 1)] at comm,
    rw [cochain.add_v, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl],
    simp only [δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl,
      add_left_neg, ε_0, one_zsmul, cochain.mk, cochain.of_hom_v, cochain.v,
      cochain.of_homotopy, cochain.of_hom_v],
    dsimp only,
    suffices : ∀ (a b c d : F.X p ⟶ G.X p) (h : a = b+c+d), a=c+b+d,
    { exact this _ _ _ _ comm, },
    { intros a b c d h, rw h, abel, },
  end,
  inv_fun := λ z,
    { hom := λ i j, begin
        by_cases j+1=i,
        { exact (z : cochain F G (-1)).v i j (by linarith), },
        { exact 0, },
      end,
      zero' := λ i j hij, begin
        change ¬ j+1 = i at hij,
        rw dif_neg hij,
      end,
      comm := λ p, begin
        have h₁ : p+1 = p+1 := rfl,
        have h₂ : p-1+1 = p := by linarith,
        have h₁' : (complex_shape.up ℤ).rel p (p+1) := h₁,
        have h₂' : (complex_shape.up ℤ).rel (p-1) p := h₂,
        rw [d_next_eq _ h₁', prev_d_eq _ h₂', dif_pos h₁, dif_pos h₂],
        have hz := cochain.congr_v z.2 p p (add_zero p).symm,
        simp only [cochain.add_v, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl,
          cochain.of_hom_v, add_left_neg, ε_0, one_zsmul] at hz,
        suffices : ∀ (a b c d : F.X p ⟶ G.X p) (h : a = b+c+d), a=c+b+d,
        { exact this _ _ _ _ hz, },
        { intros a b c d h, rw h, abel, },
      end, },
  left_inv := λ ho, begin
    ext i j,
    dsimp,
    split_ifs,
    { refl, },
    { rw ho.zero i j h, },
  end,
  right_inv := λ z, begin
    ext,
    dsimp [cochain.mk, cochain.v],
    simpa only [dif_pos (show q+1=p, by linarith)],
  end, }

lemma δ_cochain_of_homotopy {φ₁ φ₂ : F ⟶ G} (h : homotopy φ₁ φ₂) :
  δ (-1) 0 (cochain.of_homotopy h) = cochain.of_hom φ₁ - cochain.of_hom φ₂ :=
by rw [((equiv_homotopy _ _) h).2, add_sub_cancel,
  subtype.val_eq_coe, equiv_homotopy_apply_coe]

namespace cochain

variable {n}

def lift_to_kernel' (z : cochain L G n) {i : F ⟶ G} {f : G ⟶ K} (hip : is_termwise_kernel i f)
  (hz : cochain.comp z (of_hom f) (add_zero n).symm = 0) (p q : ℤ) (hpq : q=p+n):=
kernel_fork.is_limit.lift' (hip.is_limit q) (z.v p q hpq)
(by simpa only [comp_zero_cochain, of_hom_v] using congr_v hz p q hpq)

def lift_to_kernel (z : cochain L G n) {i : F ⟶ G} {f : G ⟶ K} (hip : is_termwise_kernel i f)
  (hz : cochain.comp z (of_hom f) (add_zero n).symm = 0) : cochain L F n :=
cochain.mk (λ p q hpq, (lift_to_kernel' z hip hz p q hpq).1)

@[simp]
lemma lift_to_kernel_comp (z : cochain L G n) {i : F ⟶ G} {f : G ⟶ K} (hip : is_termwise_kernel i f)
  (hz : cochain.comp z (of_hom f) (add_zero n).symm = 0) :
  cochain.comp (z.lift_to_kernel hip hz) (cochain.of_hom i) (add_zero n).symm = z :=
begin
  ext,
  simpa only [comp_v _ _ (add_zero n).symm p q q hpq (add_zero q).symm,
    of_hom_v] using (lift_to_kernel' z hip hz p q hpq).2,
end

end cochain

namespace cocycle

variable {n}

def lift_to_kernel (z : cocycle L G n) {i : F ⟶ G} {f : G ⟶ K} (hip : is_termwise_kernel i f)
  (hz : cochain.comp (z : cochain L G n) (cochain.of_hom f) (add_zero n).symm = 0) :
  cocycle L F n :=
cocycle.mk (cochain.lift_to_kernel (z : cochain L G n) hip hz) _ rfl
begin
  suffices : δ n (n + 1) (cochain.comp
    ((z : cochain L G n).lift_to_kernel hip hz) (cochain.of_hom i) (add_zero n).symm) = 0,
  { ext,
    haveI : mono (i.f q) := hip.termwise_mono q,
    simpa only [← cancel_mono (i.f q), cochain.zero_v, zero_comp,
      δ_comp_of_second_is_zero_cochain, δ_cochain_of_hom,
      cochain.comp_zero, zero_add, cochain.comp_zero_cochain,
      cochain.of_hom_v, cochain.zero_v] using cochain.congr_v this p q hpq, },
  simp only [cochain.lift_to_kernel_comp, δ_eq_zero],
end

lemma lift_to_kernel_comp (z : cocycle L G n) {i : F ⟶ G} {f : G ⟶ K} (hip : is_termwise_kernel i f)
  (hz : cochain.comp (z : cochain L G n) (cochain.of_hom f) (add_zero n).symm = 0) :
  cochain.comp (lift_to_kernel z hip hz : cochain L F n) (cochain.of_hom i) (add_zero n).symm =
  (z : cochain L G n) := by apply cochain.lift_to_kernel_comp

end cocycle

section

variables {n} {D : Type*} [category D] [preadditive D] (z z' : cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [functor.additive Φ]

namespace cochain

def map : cochain ((functor.map_homological_complex Φ _).obj K)
  ((functor.map_homological_complex Φ _).obj L) n :=
cochain.mk (λ p q hpq, Φ.map (z.v p q hpq))

@[simp]
lemma map_v (p q : ℤ) (hpq : q=p+n) :
  (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

@[simp]
lemma map_add : (z+z').map Φ = z.map Φ + z'.map Φ := by tidy

@[simp]
lemma map_neg : (-z).map Φ = -z.map Φ := by tidy

@[simp]
lemma map_sub : (z-z').map Φ = z.map Φ - z'.map Φ := by tidy

variables (K L n)

@[simp]
lemma map_zero : (0 : cochain K L n).map Φ = 0 := by tidy

@[simp]
lemma map_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂)
  (Φ : C ⥤ D) [functor.additive Φ] :
  (z₁.comp z₂ h).map Φ = (z₁.map Φ).comp (z₂.map Φ) h :=
begin
  ext p q hpq,
  simp only [map_v, comp_v _ _ h p _ q rfl (by linarith), Φ.map_comp],
end

@[simp]
lemma map_of_hom : (cochain.of_hom f).map Φ =
  cochain.of_hom ((Φ.map_homological_complex _).map f) := by tidy

end cochain

variables (n m)

@[simp]
lemma δ_map : δ n m (z.map Φ) = (δ n m z).map Φ :=
begin
  by_cases hnm : n+1=m,
  { ext p q hpq,
    simp only [δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl, cochain.map_v],
    simp only [functor.map_homological_complex_obj_d, ε_succ, neg_smul, functor.map_add,
      functor.map_comp, functor.map_neg, add_right_inj, neg_inj, Φ.map_zsmul], },
  { simp only [δ_shape _ _ hnm, cochain.map_zero], },
end

end

namespace cocycle

variables {n} {D : Type*} [category D] [preadditive D] (z z' : cocycle K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [functor.additive Φ]

@[simps]
def map : cocycle ((functor.map_homological_complex Φ _).obj K)
  ((functor.map_homological_complex Φ _).obj L) n :=
cocycle.mk ((z : cochain K L n).map Φ) (n+1) rfl (by simp)

@[simp]
lemma map_add : cocycle.map (z+z') Φ = cocycle.map z Φ + cocycle.map z' Φ :=
by { ext1, simp, }

@[simp]
lemma map_neg : cocycle.map (-z) Φ = -cocycle.map z Φ :=
by { ext1, simp, }

@[simp]
lemma map_sub : cocycle.map (z-z') Φ = cocycle.map z Φ - cocycle.map z' Φ :=
by { ext1, simp, }

@[simp]
lemma map_of_hom : cocycle.map (cocycle.of_hom f) Φ =
  cocycle.of_hom ((Φ.map_homological_complex _).map f) := by tidy

variables (K L n)

@[simp]
lemma map_zero : cocycle.map (0 : cocycle K L n) Φ = 0 :=
by { ext1, simp, }

end cocycle

end hom_complex

end cochain_complex
