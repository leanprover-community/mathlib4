/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Epsilon
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

open CategoryTheory Category Preadditive Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

section

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

namespace HomComplex

structure Triplet (n : ℤ) where
  p : ℤ
  q : ℤ
  hpq : p + n = q

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

variable (F G)

@[simp]
lemma ofHom_zero : ofHom (0 : F ⟶ G) = 0 := by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

variable {F G}

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
lemma ofHom_add (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ + φ₂) = Cochain.ofHom φ₁ + Cochain.ofHom φ₂ := by aesop_cat

@[simp]
lemma ofHom_sub (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ - φ₂) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by aesop_cat

@[simp]
lemma ofHom_neg (φ : F ⟶ G) :
    Cochain.ofHom (-φ) = -Cochain.ofHom φ := by aesop_cat

def ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1) :=
  Cochain.mk (fun p q _ => ho.hom p q)

@[simp]
lemma ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    ofHomotopy (Homotopy.ofEq h) = 0 := by rfl

@[simp]
lemma ofHomotopy_refl (φ : F ⟶ G) :
    ofHomotopy (Homotopy.refl φ) = 0 := by rfl

@[reassoc]
lemma v_comp_XIsoOfEq_hom
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]
lemma v_comp_XIsoOfEq_inv
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q' = q) :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').inv = γ.v p q' (by rw [hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

-- add similar lemmas as above : XIsoOfEq_hom/inv_comp_v

protected def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
    Cochain F K n₁₂ := Cochain.mk (fun p q hpq => z₁.v p (p+n₁) rfl ≫ z₂.v (p+n₁) q (by linarith))

notation a " ≫[" b "] " c:80 => Cochain.comp a c b

lemma comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : ℤ) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁ ; rfl

@[simp]
protected lemma zero_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (0 : Cochain F G n₁).comp z₂ h = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), zero_v, zero_comp]

@[simp]
protected lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁+z₁').comp z₂ h = z₁.comp z₂ h + z₁'.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), add_v, add_comp]

@[simp]
protected lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁-z₁').comp z₂ h = z₁.comp z₂ h - z₁'.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), sub_v, sub_comp]

@[simp]
protected lemma neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₁).comp z₂ h = -z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), neg_v, neg_comp]

@[simp]
protected lemma zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), zsmul_v, zsmul_comp]

@[simp]
lemma zero_cochain_comp_v {n : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n)
    (p q : ℤ) (hpq : p + n = q) : (z₁.comp z₂ (zero_add n)).v p q hpq =
      z₁.v p p (add_zero p) ≫ z₂.v p q hpq :=
  comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

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
  simp only [comp_v _ _ h p _ q rfl (by linarith), zero_v, comp_zero]

@[simp]
protected lemma comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂+z₂') h = z₁.comp z₂ h + z₁.comp z₂' h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), add_v, comp_add]

@[simp]
protected lemma comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂-z₂') h = z₁.comp z₂ h - z₁.comp  z₂' h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), sub_v, comp_sub]

@[simp]
protected lemma comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  (h : n₁ + n₂ = n₁₂) : z₁.comp (-z₂) h = -z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), neg_v, comp_neg]

@[simp]
protected lemma comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
  (h : n₁ + n₂ = n₁₂ ) : z₁.comp (k • z₂) h = k • z₁.comp z₂ h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [comp_v _ _ h p _ q rfl (by linarith), zsmul_v, comp_zsmul]

@[simp]
lemma comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0)
    (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq =
      z₁.v p q hpq ≫ z₂.v q q (add_zero q) :=
  comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

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
  simp only [comp_v _ _ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) p (p + n₁₂) q rfl (by linarith),
    comp_v _ _ h₁₂ p (p+n₁) (p+n₁₂) rfl (by linarith),
    comp_v _ _ (show n₁ + n₂₃ = n₁₂₃ by linarith) p (p+n₁) q rfl (by linarith),
    comp_v _ _ h₂₃ (p+n₁) (p+n₁₂) q (by linarith) (by linarith), assoc]

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

@[simp]
lemma comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ : n₁ + (-n₂) = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, neg_add_self, add_zero]) =
      z₁.comp (z₂.comp z₃ (neg_add_self n₂)) (add_zero n₁) :=
  comp_assoc z₁ z₂ z₃ h₁₂ (neg_add_self n₂) (by linarith)

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

lemma δ_eq (hnm : n + 1 = m) (z : Cochain F G n) :
    δ n m z = z.comp (Cochain.diff G) hnm +
      ε (n + 1) • (Cochain.diff F).comp z (by rw [← hnm, add_comm 1]) := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [δ_v n m hnm z p q hpq (q-1) (p+1) rfl rfl,
    Cochain.comp_v _ _ hnm p (q-1) q (by linarith) (by linarith),
    Cochain.comp_v _ _ (show 1+n = m by linarith) p (p+1) q (by linarith) (by linarith),
    Cochain.diff_v]

@[simp]
lemma δ_zero_cochain_v (z : Cochain F G 0) (p q : ℤ) (hpq : p + 1 = q) :
    (δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q):= by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by linarith) hpq, zero_add, ε_1,
    neg_smul, one_smul, sub_eq_add_neg]

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

-- TODO use the external multiplication instead of composition, with reverse order of parameters
-- so that this reads as `δ (α • β) = (δ α) • β + (-1)^(deg α) α • δ β`
lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
  δ n₁₂ m₁₂ (z₁.comp z₂ h) = z₁.comp (δ n₂ m₂ z₂) (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
    ε n₂ • (δ n₁ m₁ z₁).comp z₂ (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  subst h₁₂ h₁ h₂ h
  ext ⟨p, q, hpq⟩
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by linarith),
    Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by linarith) p (p+n₁+1) q (by linarith) (by linarith),
    δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by linarith) rfl,
    z₁.comp_v z₂ rfl p _ _ rfl rfl,
    z₁.comp_v z₂ rfl (p+1) (p+n₁+1) q (by linarith) (by linarith),
    δ_v n₂ (n₂+1) rfl z₂ (p+n₁) q (by linarith) (p+n₁+n₂) _ (by linarith) rfl]
  rw [δ_v n₁ (n₁+1) rfl z₁ p (p+n₁+1) (by linarith) (p+n₁) _ (by linarith) rfl]
  simp only [assoc, comp_add, add_comp, ε_add, ε_1, mul_neg, mul_one, zsmul_add, neg_zsmul,
    neg_comp, zsmul_neg, zsmul_comp, smul_smul, comp_neg, comp_zsmul, mul_comm (ε n₁) (ε n₂)]
  abel

lemma δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
    (m₂ : ℤ) (h₂ : n₂+1 = m₂) :
    δ n₂ m₂ (z₁.comp z₂ (zero_add n₂)) =
      z₁.comp (δ n₂ m₂ z₂) (by rw [zero_add]) + ε n₂ • (δ 0 1 z₁).comp z₂ (by rw [add_comm, h₂]) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

lemma δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) : δ n₁ m₁ (z₁.comp z₂ (add_zero n₁)) =
      z₁.comp (δ 0 1 z₂) h₁ + (δ n₁ m₁ z₁).comp z₂ (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), ε_0, one_zsmul]

@[simp]
lemma δ_ofHom {p : ℤ} (φ : F ⟶ G) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : p = 1
  . subst h
    ext
    simp
  . rw [δ_shape]
    intro
    apply h
    linarith

@[simp]
lemma δ_ofHomomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel p (p+1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (p-1) p by simp)] at eq
  rw [Cochain.ofHomotopy, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [Cochain.mk_v, ComplexShape.up_Rel, sub_add_cancel, not_true, add_left_neg, ε_0,
    one_smul, Cochain.zero_v, Cochain.sub_v, Cochain.ofHom_v, eq]
  abel

lemma δ_neg_one_cochain (z : Cochain F G (-1)) :
    δ (-1) 0 z = Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij ; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [neg_add_self, ε_0, one_smul, Cochain.ofHom_v]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p-1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p+1) by simp)]
  abel

end HomComplex

variable (F G)

open HomComplex

def HomComplex : CochainComplex AddCommGroupCat ℤ where
  X i := AddCommGroupCat.of (Cochain F G i)
  d i j := AddCommGroupCat.ofHom (δ_hom F G i j)
  shape _ _ hij := by ext ; apply δ_shape _ _ hij
  d_comp_d' _ _ _ _ _  := by ext ; apply δδ

namespace HomComplex

def cocycle : AddSubgroup (Cochain F G n) :=
  AddMonoidHom.ker (δ_hom F G n (n+1))

def Cocycle : Type _ := cocycle F G n

instance : AddCommGroup (Cocycle F G n) := by
  dsimp only [Cocycle]
  infer_instance

namespace Cocycle

variable {F G n}

instance : Coe (Cocycle F G n) (Cochain F G n) where
  coe x := x.1

@[ext]
lemma ext (z₁ z₂ : Cocycle F G n) (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

lemma ext_iff (z₁ z₂ : Cocycle F G n) : z₁ = z₂ ↔ (z₁ : Cochain F G n) = z₂ := by
  constructor
  . rintro rfl
    rfl
  . apply ext

variable (F G n)

@[simp]
lemma coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0 := by rfl

variable {F G n}

@[simp]
lemma coe_add (z₁ z₂ : Cocycle F G n) : (↑(z₁ + z₂) : Cochain F G n) =
  (z₁ : Cochain F G n) + (z₂ : Cochain F G n) := rfl

@[simp]
lemma coe_neg (z : Cocycle F G n) : (↑(-z) : Cochain F G n) =
  -(z : Cochain F G n):= rfl

@[simp]
lemma coe_zsmul (z : Cocycle F G n) (x : ℤ) : (↑(x • z) : Cochain F G n) =
  x • (z : Cochain F G n) := rfl

@[simp]
lemma coe_sub (z₁ z₂ : Cocycle F G n) : (↑(z₁ - z₂) : Cochain F G n) =
  (z₁ : Cochain F G n) - (z₂ : Cochain F G n) := rfl

variable (n)

lemma mem_iff (hnm : n+1=m) (z : Cochain F G n) :
    z ∈ cocycle F G n ↔ δ n m z = 0 := by
  subst hnm
  rfl

variable {n}

@[simps]
def mk (z : Cochain F G n) (m : ℤ) (hnm : n+1 = m) (h : δ n m z = 0) : Cocycle F G n :=
  ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
lemma δ_eq_zero {n : ℤ} (z : Cocycle F G n) (m : ℤ) : δ n m (z : Cochain F G n) = 0 := by
  by_cases h : n+1 = m
  . rw [← mem_iff n m h]
    exact z.2
  . apply δ_shape n m h

@[simps!]
def ofHom (φ : F ⟶ G) : Cocycle F G 0 := mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

@[simps]
def homOf (z : Cocycle F G 0) : F ⟶ G where
  f i := (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, ComplexShape.up_Rel, not_true, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i+1) rfl

@[simp]
lemma homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ := by aesop_cat

@[simp]
lemma ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z := by aesop_cat

@[simp]
lemma cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) :
    (Cochain.ofHom (homOf z) : Cochain F G 0) = (z : Cochain F G 0) := by
  simpa only [ext_iff] using ofHom_homOf_eq_self z

variable (F G)

@[simps]
def equivHom : (F ⟶ G) ≃+ Cocycle F G 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by aesop_cat

variable (K)

@[simps!]
def diff : Cocycle K K 1 :=
  Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext ⟨p, q, hpq⟩
    dsimp
    simp only [δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

end Cocycle

namespace Cochain

variable {F G}

@[simps]
def equivHomotopy (φ₁ φ₂ : F ⟶ G) :
    Homotopy φ₁ φ₂ ≃
      { z : Cochain F G (-1) // Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } where
  toFun ho := ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => dite (i+ (-1) = j) (z.1.v i j) (fun _ => 0)
      zero := fun i j (hij : ¬ j+1 = i) => by
        dsimp
        rw [dif_neg]
        intro
        apply hij
        linarith
      comm := fun p => by
        have eq := z.2
        rw [δ_neg_one_cochain] at eq
        replace eq := Cochain.congr_v eq p p (add_zero p)
        simp only [Cochain.ofHom_v, ComplexShape.up_Rel, Cochain.add_v,
          Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p-1) p by simp)
            (show (ComplexShape.up ℤ).Rel p (p+1) by simp)] at eq
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by simp), eq, dif_pos, dif_pos] }
  left_inv := fun ho => by
    ext i j
    dsimp
    split_ifs with h
    . rfl
    . rw [ho.zero i j]
      dsimp
      intro
      apply h
      linarith
  right_inv := fun z => by
    ext ⟨p, q, hpq⟩
    dsimp [Cochain.ofHomotopy]
    rw [dif_pos]

@[simp]
lemma equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    (equivHomotopy _ _ (Homotopy.ofEq h)).1 = 0 := rfl

lemma ofHom_injective {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂) : f₁ = f₂ := by
  rw [← Cocycle.homOf_ofHom_eq_self f₁, ← Cocycle.homOf_ofHom_eq_self f₂]
  congr 1
  ext1
  simp only [Cocycle.ofHom_coe, h]

end Cochain

section

variable {n} {D : Type _} [Category D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

namespace Cochain

def map : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]
lemma map_v (p q : ℤ) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

@[simp]
lemma map_add : (z+z').map Φ = z.map Φ + z'.map Φ := by aesop_cat

@[simp]
lemma map_neg : (-z).map Φ = -z.map Φ := by aesop_cat

@[simp]
lemma map_sub : (z-z').map Φ = z.map Φ - z'.map Φ := by aesop_cat

variable (K L n)

@[simp]
lemma map_zero : (0 : Cochain K L n).map Φ = 0 := by aesop_cat

@[simp]
lemma map_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (Φ : C ⥤ D) [Φ.Additive] :
    (z₁.comp z₂ h).map Φ = (z₁.map Φ).comp (z₂.map Φ) h := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by linarith), Φ.map_comp]

@[simp]
lemma map_ofHom : (Cochain.ofHom f).map Φ =
  Cochain.ofHom ((Φ.mapHomologicalComplex _).map f) := by aesop_cat

end Cochain

variable (n)

@[simp]
lemma δ_map : δ n m (z.map Φ) = (δ n m z).map Φ := by
  by_cases hnm : n + 1 = m
  . ext ⟨p, q, hpq⟩
    dsimp
    simp only [δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_zsmul,
      Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  . simp only [δ_shape _ _ hnm, Cochain.map_zero]

end

namespace Cocycle

variable {n} {D : Type _} [Category D] [Preadditive D] (z z' : Cocycle K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

@[simps!]
def map : Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map Φ) (n+1) rfl (by simp)

@[simp]
lemma map_add : Cocycle.map (z + z') Φ = Cocycle.map z Φ + Cocycle.map z' Φ := by aesop_cat

@[simp]
lemma map_neg : Cocycle.map (-z) Φ = -Cocycle.map z Φ := by aesop_cat

@[simp]
lemma map_sub : Cocycle.map (z-z') Φ = Cocycle.map z Φ - Cocycle.map z' Φ := by aesop_cat

@[simp]
lemma map_of_hom : Cocycle.map (Cocycle.ofHom f) Φ =
  Cocycle.ofHom ((Φ.mapHomologicalComplex _).map f) := by aesop_cat

variable (K L n)

@[simp]
lemma map_zero : Cocycle.map (0 : Cocycle K L n) Φ = 0 := by aesop_cat

end Cocycle

end HomComplex

end

section Shift

namespace HomComplex

variable {n : ℤ} {K L M : CochainComplex C ℤ}

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by linarith)).inv)

lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
  (p' : ℤ) (hp' : p + n = p') :
  (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
    (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => ε (a * n' + (a*(a-1)/2)) •
    (K.shiftFunctorObjXIso a p (p+a) rfl).hom ≫ γ.v (p+a) q (by linarith))

lemma leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = ε (a * n' + (a*(a-1)/2)) • (K.shiftFunctorObjXIso a p p'
      (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p+a := by linarith
  dsimp only [leftShift]
  simp only [mk_v]

lemma leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (γ' : Cochain L M m)
    (h : n + m = t) (ht' : t + a = t'):
    (γ.comp γ' h).leftShift a t' ht' =  ε (a * m) • (γ.leftShift a n' hn').comp γ'
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext ⟨p, q, hpq⟩
  have h' : n' + m = t' := by linarith
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p+n') q rfl (by linarith),
    γ.leftShift_v a n' hn' p (p+n') rfl (p+a) (by linarith),
    (γ.comp γ' h).leftShift_v a t' (by linarith) p q hpq (p+a) (by linarith),
    smul_smul, zsmul_comp, comp_v _ _ h (p+a) (p+n') q (by linarith) (by linarith), assoc,
    ε_add, ← mul_assoc, ← h']
  congr 2
  rw [add_comm n', mul_add, ε_add]

@[simp]
lemma leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (γ' : Cochain L M 0) :
    (γ.comp γ' h).leftShift a n' hn' = (γ.leftShift a n' hn').comp γ' (add_zero n') := by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn', mul_zero, ε_0, one_smul]

def shift (a : ℤ) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p+a) (q+a) (by linarith) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

lemma shift_v' (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

@[simp]
lemma shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p+a) (q+a) (by rw [← hpq, add_assoc, add_comm a, add_assoc]) := by
  simp only [shift_v' γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

variable (K L)

@[simp]
lemma rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp
  rw [rightShift_v _ a n' hn' p q hpq _ rfl, zero_v, zero_comp]

@[simp]
lemma leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain K L n).leftShift a n' hn' = 0 := by
  ext ⟨p, q, hpq⟩
  dsimp
  rw [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), zero_v, comp_zero, zsmul_zero]

@[simp]
lemma shift_zero (a : ℤ) :
    (0 : Cochain K L n).shift a = 0 := by aesop_cat

variable {K L}

@[simp]
lemma rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
  (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, neg_v, neg_comp]

@[simp]
lemma leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), neg_v,
    comp_neg, neg_zsmul, zsmul_neg]

@[simp]
lemma shift_neg (a : ℤ) :
    (-γ).shift a = -γ.shift a := by aesop_cat

@[simp]
lemma rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
  (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

@[simp]
lemma leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), add_v,
    comp_add, zsmul_add]

@[simp]
lemma shift_add (a : ℤ) :
    (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a := by aesop_cat

@[simp]
lemma rightShift_zsmul (a n' : ℤ) (hn' : n' + a = n) (x : ℤ) :
  (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, zsmul_v, zsmul_comp]

@[simp]
lemma leftShift_zsmul (a n' : ℤ) (hn' : n + a = n') (x : ℤ):
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext ⟨p, q, hpq⟩
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), zsmul_v, smul_smul,
    comp_zsmul, mul_comm x]

@[simp]
lemma shift_zsmul (a : ℤ) (x : ℤ):
    (x • γ).shift a = x • γ.shift a := by aesop_cat

lemma δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = ε a • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  . have hnm' : n' + 1 = m' := by linarith
    ext ⟨p, q, hpq⟩
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p+m) rfl (p+n) (p+1) (by linarith) rfl,
      δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by linarith) rfl,
      γ.rightShift_v a n' hn' p (p+n') rfl (p+n) rfl,
      γ.rightShift_v a n' hn' (p+1) q _ (p+m) (by linarith)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      comp_zsmul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, zsmul_comp, smul_add,
      smul_smul, add_right_inj]
    congr
    rw [hnm, hnm', ← hm', add_comm m', ε_add, ← mul_assoc, mul_ε_self, one_mul]
  . have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by linarith)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

lemma δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = ε a • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  . have hnm' : n' + 1 = m' := by linarith
    ext ⟨p, q, hpq⟩
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p+a) (by linarith)]
    rw [δ_v n m hnm _ (p+a) q (by linarith) (p+n') (p+1+a) (by linarith) (by
      linarith)]
    rw [δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by linarith) rfl]
    rw [γ.leftShift_v a n' hn' p (p+n') rfl (p+a) (by linarith)]
    rw [γ.leftShift_v a n' hn' (p+1) q (by linarith) (p+1+a) (by linarith)]
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp,
      shiftFunctor_obj_d', comp_add, smul_add, shiftFunctor_obj_X, smul_smul, zsmul_comp,
      comp_zsmul]
    congr 2
    . rw [ε_add, ε_add, ← mul_assoc, ← hnm', add_comm n', mul_add, ε_add, mul_one,
        ← mul_assoc, mul_ε_self, one_mul]
    . simp only [ε_add, ε_1, mul_one, ← hn', ← hm', mul_add, ← hnm]
      ring
  . have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by linarith)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

@[simp]
lemma δ_shift (a m : ℤ) :
    δ n m (γ.shift a) = ε a • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  . ext ⟨p, q, hpq⟩
    dsimp
    simp only [shift_v, sub_add_cancel, shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl,
      δ_v n m hnm _ (p+a) (q+a) (by linarith) (q-1+a) (p+1+a) (by linarith) (by linarith),
      smul_add, comp_zsmul, zsmul_comp, smul_smul, mul_comm (ε a)]
  . rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]


end Cochain

namespace Cocycle

variable (γ : Cocycle K L n)

@[simps!]
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk ((γ : Cochain K L n).rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n'+1) hn' (n+1) (by linarith),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

@[simps!]
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cocycle (K⟦a⟧) L n' :=
  Cocycle.mk ((γ : Cochain K L n).leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n'+1) hn' (n+1) (by linarith),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

@[simps!]
def shift (a : ℤ) : Cocycle (K⟦a⟧) (L⟦a⟧) n :=
  Cocycle.mk ((γ : Cochain K L n).shift a) _ rfl (by simp)

end Cocycle

end HomComplex

end Shift

namespace HomComplex

variable {K L : CochainComplex C ℤ}

@[simp]
lemma δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : ℤ) :
    δ n m (z₁.comp (z₂ : Cochain G K 0) (add_zero n)) =
      (δ n m z₁).comp (z₂ : Cochain G K 0) (add_zero m) := by
  by_cases hnm : n + 1 = m
  . simp only [δ_comp_zero_cochain _ _ _ hnm, Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add]
  . simp only [δ_shape _ _ hnm, Cochain.zero_comp]

@[simp]
lemma δ_comp_ofHom {n : ℤ} (z₁ : Cochain F G n) (f : G ⟶ K) (m : ℤ) :
    δ n m (z₁.comp (Cochain.ofHom f) (add_zero n)) =
      (δ n m z₁).comp (Cochain.ofHom f) (add_zero m) := by
  rw [← Cocycle.ofHom_coe, δ_comp_zero_cocycle]

@[simp]
lemma δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : ℤ) :
    δ n m ((z₁ : Cochain F G 0).comp z₂ (zero_add n)) =
      (z₁ : Cochain F G 0).comp (δ n m z₂) (zero_add m) := by
  by_cases hnm : n + 1 = m
  . simp only [δ_zero_cochain_comp _ _ _ hnm, Cocycle.δ_eq_zero, Cochain.zero_comp,
      smul_zero, add_zero]
  . simp only [δ_shape _ _ hnm, Cochain.comp_zero]

@[simp]
lemma δ_ofHom_comp {n : ℤ} (f : F ⟶ G) (z : Cochain G K n) (m : ℤ) :
    δ n m ((Cochain.ofHom f).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (δ n m z) (zero_add m) := by
  rw [← Cocycle.ofHom_coe, δ_zero_cocycle_comp]

end HomComplex

end CochainComplex
