/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Resultant.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Vieta


/-!
# Universal Resultant

The resultant can be seen as a polynomial in `ℤ[a₀, ..., aₘ, b₀, ..., bₙ]` where `aᵢ` and `bⱼ` are
the "universal coefficients" of the polynomial `p(x) = a₀ + a₁ x + ... + aₘ xᵐ` and
`q(x) = b₀ + b₁ x + ... + bₙ xⁿ`. This is implemented as either
`MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ`, or `MvPolynomial (ℕ ⊕ ℕ) ℤ` to unify
the different polynomials.

The universal construction allows one to reason about the resultant more abstractly, and to prove
certain identities involving the resultant.

-/


noncomputable section

section TO_MOVE

theorem MvPolynomial.IsWeightedHomogeneous.C_mul {R M σ : Type*} [CommRing R] [AddCommMonoid M]
      {w : σ → M} {φ : MvPolynomial σ R} {m : M} (r : R) (hφ : φ.IsWeightedHomogeneous w m) :
    (C r * φ).IsWeightedHomogeneous w m :=
  zero_add m ▸ (isWeightedHomogeneous_C _ _).mul hφ

theorem MvPolynomial.IsWeightedHomogeneous.zsmul {R M σ : Type*} [CommRing R] [AddCommMonoid M]
      {w : σ → M} {φ : MvPolynomial σ R} {m : M} (n : ℤ) (hφ : φ.IsWeightedHomogeneous w m) :
    (n • φ).IsWeightedHomogeneous w m := by
  rw [zsmul_eq_mul, ← map_intCast (C (σ:=σ) (R:=R))]; exact hφ.C_mul _

theorem MvPolynomial.IsWeightedHomogeneous.eval₂ {α β M R : Type*}
    [AddCommMonoid M] [CommRing R]
    (f : MvPolynomial α R) (bind : α → MvPolynomial β R) (w₁ : α → M) (w₂ : β → M) {m : M}
    (hf : f.IsWeightedHomogeneous w₁ m)
    (hb : ∀ x, (bind x).IsWeightedHomogeneous w₂ (w₁ x)) :
    (f.eval₂ MvPolynomial.C bind).IsWeightedHomogeneous w₂ m := by
  rw [f.as_sum, ← coe_eval₂Hom, map_sum]
  refine .sum _ _ _ (fun p hp ↦ ?_)
  have := hf (mem_support_iff.1 hp)
  rw [Finsupp.weight_apply] at this
  rw [eval₂Hom_monomial, ← this]
  exact .C_mul _ (.prod _ _ _ (fun _ _ ↦ .pow (hb _) _))

-- instance foo (σ : Type*) [LinearOrder σ] : LinearOrder (σ →₀ ℕ) := by apply?
#check Finsupp.Lex
#check exists_wellOrder

/-- Under a linear order on the indeterminates, the monomials are linearly ordered using the
lexicographical order. Then, if `i` and `j` are the lowest monomials in `p` and `q` respectively,
then the lowest term in `(p * q)` is `pᵢ qⱼ Xⁱ⁺ᴶ`. -/
theorem MvPolynomial.min_prod {σ R : Type*} [CommRing R] [IsDomain R] [LinearOrder σ]
      (p q : MvPolynomial σ R) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    ((p * q).support.map toLex.toEmbedding).min =
      (p.support.map toLex.toEmbedding).min + (q.support.map toLex.toEmbedding).min := by
  _

theorem MvPolynomial.IsWeightedHomogeneous.of_mul_right {σ R : Type*} [CommRing R] [IsDomain R]
    {p q : MvPolynomial σ R} {w : σ → ℕ} {m n : ℕ} (hp : p.IsWeightedHomogeneous w m)
    (hpq : (p * q).IsWeightedHomogeneous w (m + n)) (hp0 : p ≠ 0) :
    q.IsWeightedHomogeneous w n := by
  rw [MvPolynomial.isWeightedHomogeneous_iff_comp_smul_eq_pow_smul] at *
  rw [_root_.map_mul, _root_.map_mul, pow_add, mul_assoc, mul_left_comm _ (rename _ p) (rename _ q),
      ← mul_assoc, hp] at hpq
  exact mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero _ (X_ne_zero _))
    ((map_ne_zero_iff _ (rename_injective _ (Option.some_injective _))).mpr
      hp0)) hpq

/-- Two multivariate polynomials that are homogeneous of the same degree and divide each other,
are equal up to constants. -/
lemma MvPolynomial.IsWeightedHomogeneous.exists_C_mul_eq_of_dvd [IsDomain R] {σ : Type*}
    {w : σ → ℕ} (hw : NonTorsionWeight w)
    {P Q : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w n) (hQ : Q.IsWeightedHomogeneous w n)
    (hdvd : P ∣ Q) :
    ∃ c, C c * P = Q := by
  obtain ⟨R, rfl⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  by_cases hR0 : R = 0
  · use 0
    simp [hR0]
  obtain ⟨x, rfl⟩ : ∃ x, R = C x :=
    ((IsWeightedHomogeneous.of_mul_right hP (by simpa) hP0).zero_iff_exists_C hw hR0).mp rfl
  exact ⟨x, mul_comm _ _⟩

end TO_MOVE
/-

namespace Polynomial

section universal

variable (m n : ℕ)

/-- The universal polynomial `aₙ xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universal : (MvPolynomial (Fin (n+1)) ℤ)[X] :=
  ∑ i : Fin (n+1), .C (.X i) * .X ^ i.1

/-- The universal polynomial `aₙ xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universal' : (MvPolynomial ℕ ℤ)[X] :=
  .map (MvPolynomial.rename Fin.val).toRingHom (.universal n)

/-- The universal monic polynomial `xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universalMonic : (MvPolynomial (Fin n) ℤ)[X] :=
  (universal n).map (MvPolynomial.aeval <| Fin.lastCases 1 MvPolynomial.X).toRingHom

/-- The universal monic polynomial `xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universalMonic' : (MvPolynomial ℕ ℤ)[X] :=
  .map (MvPolynomial.rename Fin.val).toRingHom (.universalMonic n)

/-- The universal split polynomial `∏ (X - aᵢ)`. -/
def universalSplit : (MvPolynomial (Fin n) ℤ)[X] :=
  ∏ i : Fin n, (.X - .C (.X i))

def universalPair : (MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ)[X] ×
    (MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ)[X] :=
  ((universal m).map (MvPolynomial.rename Sum.inl).toRingHom,
   (universal n).map (MvPolynomial.rename Sum.inr).toRingHom)

def universalSplitPair : (MvPolynomial (Fin m ⊕ Fin n) ℤ)[X] ×
    (MvPolynomial (Fin m ⊕ Fin n) ℤ)[X] :=
  ((universalSplit m).map (MvPolynomial.rename Sum.inl).toRingHom,
   (universalSplit n).map (MvPolynomial.rename Sum.inr).toRingHom)

/-- The universal polynomial that represents the resultant as a "formula" in terms of the
coefficients of two polynomials, here seen as formal indeterminates. For example,
`Resultant(ax^2 + bx + c, dx + e) = cd² - bde + ae²`. -/
def universalResultant : MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ :=
  resultant (universalPair m n).1 (universalPair m n).2

def universalSylvester : Matrix (Fin (n+m)) (Fin (n+m)) (MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ) :=
  sylvester (universalPair m n).1 (universalPair m n).2 _ _

/-- The quantity `Res(∏(X-aᵢ),∏(X-bⱼ))` expressed as a formula in terms of formal indeterminates.
We prove that it can be expressed as `(-1)ᵐⁿ∏∏(aᵢ-bⱼ)`. -/
def universalSplitResultant : MvPolynomial (Fin m ⊕ Fin n) ℤ :=
  resultant (universalSplitPair m n).1 (universalSplitPair m n).2

@[simp] lemma universal_degree : (universal n).degree = n := by
  refine degree_eq_of_le_of_coeff_ne_zero
    ((degree_sum_le _ _).trans <| Finset.sup_le <| fun i _ ↦ (degree_C_mul_X_pow_le _ _).trans <|
      Nat.cast_le.2 <| Nat.lt_succ.1 i.isLt)
    ?_
  rw [universal, finset_sum_coeff, Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _),
    Fin.val_last, coeff_C_mul_X_pow, if_pos rfl]
  · exact MvPolynomial.X_ne_zero _
  · intro b  _ hb
    rw [coeff_C_mul_X_pow, if_neg (by exact Fin.ext_iff.not.1 (Ne.symm hb))]

@[simp] lemma universal_natDegree : (universal n).natDegree = n :=
  natDegree_eq_of_degree_eq_some <| universal_degree _

@[simp] lemma universalPair_natDegree_left : (universalPair m n).1.natDegree = m :=
  (natDegree_map_eq_of_injective (MvPolynomial.rename_injective _ Sum.inl_injective) _).trans
    (universal_natDegree m)

@[simp] lemma universalPair_natDegree_right : (universalPair m n).2.natDegree = n :=
  (natDegree_map_eq_of_injective (MvPolynomial.rename_injective _ Sum.inr_injective) _).trans
    (universal_natDegree n)

@[simp] lemma universal_coeff_fin (i : Fin (n+1)) : (universal n).coeff i = .X i := by
  simp [universal, ← Fin.ext_iff]

@[simp] lemma universal_coeff (i) : (universal n).coeff i =
    if H : i < n + 1 then (.X ⟨i, H⟩) else 0 := by
  split_ifs with H
  · exact universal_coeff_fin n ⟨i, H⟩
  · simp [universal]
    exact Finset.sum_eq_zero (fun x _ ↦ if_neg fun hix ↦ H (hix.trans_lt x.2))

@[simp] lemma universalPair_coeff_left (i) : (universalPair m n).1.coeff i =
    if H : i < m + 1 then (.X (Sum.inl ⟨i, H⟩)) else 0 := by
  rw [universalPair, coeff_map, universal_coeff]; split_ifs <;> simp

@[simp] lemma universalPair_coeff_fin_left (i : Fin (m+1)) :
    (universalPair m n).1.coeff i = .X (Sum.inl i) :=
  (universalPair_coeff_left _ _ _).trans (dif_pos i.2)

@[simp] lemma universalPair_coeff_right (i) : (universalPair m n).2.coeff i =
    if H : i < n + 1 then (.X (Sum.inr ⟨i, H⟩)) else 0 := by
  rw [universalPair, coeff_map, universal_coeff]; split_ifs <;> simp

@[simp] lemma universalPair_coeff_fin_right (i : Fin (n+1)) :
    (universalPair m n).2.coeff i = .X (Sum.inr i) :=
  (universalPair_coeff_right _ _ _).trans (dif_pos i.2)

lemma universalResultant_eq : universalResultant m n = (universalSylvester m n).det := by
  rw [universalResultant, universalSylvester, resultant_def,
    universalPair_natDegree_left, universalPair_natDegree_right]

theorem universalSplit_coeff {i} (hin : i ≤ n) : (universalSplit n).coeff i =
    (-1)^(n - i) * MvPolynomial.esymm (Fin n) ℤ (n - i) :=
  have hn : (Finset.univ.val.map (MvPolynomial.X : Fin n → MvPolynomial _ ℤ)).card = n := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  calc
  _ = ((Finset.univ.val.map MvPolynomial.X).map
        fun r ↦ (.X - .C r : (MvPolynomial (Fin n) ℤ)[X])).prod.coeff i := by
    rw [Multiset.map_map, universalSplit, Finset.prod_map_val]; rfl
  _ = _ := Multiset.prod_X_sub_C_coeff _ (by rwa [hn])
  _ = _ := by rw [MvPolynomial.esymm_eq_multiset_esymm, hn]

@[simp] lemma universalSplit_degree : (universalSplit n).degree = n := calc
  _ = ∑ i, (.X - .C (.X i) : (MvPolynomial (Fin n) ℤ)[X]).degree := by
    rw [universalSplit, degree_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)]
  _ = ∑ i, 1 := Finset.sum_congr rfl (fun _ _ ↦ degree_X_sub_C _)
  _ = n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_one]

@[simp] lemma universalSplit_natDegree : (universalSplit n).natDegree = n :=
natDegree_eq_of_degree_eq_some <| universalSplit_degree n

@[simp] lemma universalSplitPair_natDegree_left : (universalSplitPair m n).1.natDegree = m :=
  (natDegree_map_eq_of_injective (MvPolynomial.rename_injective _ Sum.inl_injective) _).trans
    (universalSplit_natDegree m)

@[simp] lemma universalSplitPair_natDegree_right : (universalSplitPair m n).2.natDegree = n :=
  (natDegree_map_eq_of_injective (MvPolynomial.rename_injective _ Sum.inr_injective) _).trans
    (universalSplit_natDegree n)

end universal


section universal_properties

variable {m n : ℕ} {R : Type*} [CommRing R] {f g : R[X]}
  (hf : f.degree ≤ m) (hg : g.degree ≤ n)

variable (n f) in
/-- Given a polynomial `f : R[X]`, we construct a "universal" map `ℤ[a₀,⋯,aₙ] → R` that sends
`Polynomial.universal n` to `f`. -/
def uEval : MvPolynomial (Fin (n+1)) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun i ↦ f.coeff i)

include hf in
lemma uEval_universal : (universal m).map (uEval m f) = f := by
  ext i; simp [uEval]; split_ifs with hi <;> simp
  rw [Nat.lt_succ, not_le, ← WithBot.coe_lt_coe] at hi
  exact (coeff_eq_zero_of_degree_lt <| hf.trans_lt hi).symm

variable (m n f g) in
/-- Given two polynomials `f g : R[X]`, we construct a "universal" map
`ℤ[a₀,⋯,aₘ,b₀,⋯,bₙ → R` that sends `Polynomial.universalPair n` to `f, g`. -/
def uEval₂ : MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (Sum.elim (fun i ↦ f.coeff i) (fun j ↦ g.coeff j))

include hf in
lemma uEval₂_universalPair_left : (universalPair m n).1.map (uEval₂ m n f g) = f := by
  ext i; simp [universalPair, uEval₂]; split_ifs with hi <;> simp
  rw [Nat.lt_succ, not_le, ← WithBot.coe_lt_coe] at hi
  exact (coeff_eq_zero_of_degree_lt <| hf.trans_lt hi).symm

include hg in
lemma uEval₂_universalPair_right : (universalPair m n).2.map (uEval₂ m n f g) = g := by
  ext i; simp [universalPair, uEval₂]; split_ifs with hi <;> simp
  rw [Nat.lt_succ, not_le, ← WithBot.coe_lt_coe] at hi
  exact (coeff_eq_zero_of_degree_lt <| hg.trans_lt hi).symm

lemma uEval₂_universalSylvester : (universalSylvester m n).map (uEval₂ m n f g) =
    sylvester f g m n := by
  ext i j; rw [universalSylvester, ← sylvester_map, sylvester, sylvester]; congr 1 <;>
    ext k <;> split_ifs with h₁ <;> simp [uEval₂] <;>
    rw [dif_pos (Nat.lt_succ.2 (Nat.sub_le_iff_le_add'.2 h₁.2))] <;> simp

lemma uEval₂_universalResultant : (uEval₂ f.natDegree g.natDegree f g) (universalResultant _ _) =
    resultant f g := by
  rw [universalResultant_eq, RingHom.map_det, RingHom.mapMatrix_apply,
    uEval₂_universalSylvester, resultant_def]

lemma universalSplitResultant_eq' : universalSplitResultant m n =
    (universalResultant m n).eval₂ MvPolynomial.C (Sum.elim
      (fun i ↦ ((-1)^(m-i) : ℤ) * .rename Sum.inl (.esymm _ _ (m-i)) :
        Fin (m+1) → MvPolynomial (Fin m ⊕ Fin n) ℤ)
      (fun j ↦ ((-1)^(n-j) : ℤ) * .rename Sum.inr (.esymm _ _ (n-j)) :
        Fin (n+1) → MvPolynomial (Fin m ⊕ Fin n) ℤ)) := by
  rw [universalSplitResultant, ← uEval₂_universalResultant, universalSplitPair_natDegree_left,
    universalSplitPair_natDegree_right, ← MvPolynomial.coe_eval₂Hom]
  refine congr_fun (congr_arg _ (MvPolynomial.ringHom_ext (fun r ↦ ?_)
    (Sum.rec (fun i ↦ ?_) (fun j ↦ ?_)))) _
  · rw [uEval₂, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]; rfl
  · rw [uEval₂, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simp [universalSplitPair]
    rw [universalSplit_coeff m i.is_le, map_mul, map_pow, map_neg, map_one]
  · rw [uEval₂, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    simp [universalSplitPair]
    rw [universalSplit_coeff n j.is_le, map_mul, map_pow, map_neg, map_one]

end universal_properties


section IsHomogeneous

variable {M : Type*} [AddCommGroup M] (r s d : M) (m n : ℕ) (σ : Equiv.Perm (Fin (n+m)))

-- theorem resultant_IsHomogeneous :
--     (universalResultant m n).IsHomogeneous (m + n) := by
--   sorry

/-- The Sylvester matrix can be "expanded" to fill out the space by continuing the
  arithmetic sequences even when the entries are `0`. -/
def sylvesterWeight : Matrix (Fin (n+m)) (Fin (n+m)) M :=
  fun i ↦ Fin.addCases (fun j ↦ r + (i-j : ℤ) • d) (fun j ↦ s + (i-j : ℤ) • d)

/-- The top row of the matrix of weights. -/
def sylvesterWeightZero :  Fin (n+m) → M :=
  Fin.addCases (fun j ↦ r - (j : ℤ) • d) (fun j ↦ s - (j : ℤ) • d)

lemma sylvesterWeight_apply_eq_zero (i j : Fin (n+m)) :
    sylvesterWeight r s d m n i j = sylvesterWeightZero r s d m n j + (i : ℤ) • d := by
  rw [sylvesterWeight, sylvesterWeightZero]
  cases j using Fin.addCases with
  | left j => simp only [Fin.addCases_left, sub_smul, natCast_zsmul, add_comm_sub]
  | right j => simp only [Fin.addCases_right, sub_smul, natCast_zsmul, add_comm_sub]

lemma sylvesterWeight_apply_same_left (i : Fin n) :
    sylvesterWeight r s d m n (i.castAdd m) (i.castAdd m) = r := by
  rw [sylvesterWeight, Fin.addCases_left, Fin.coe_castAdd, sub_self, zero_smul, add_zero]

lemma sylvesterWeight_apply_same_right (i : Fin m) :
    sylvesterWeight r s d m n (i.natAdd n) (i.natAdd n) = s + n • d := by
  rw [sylvesterWeight, Fin.addCases_right, Fin.coe_natAdd, Nat.cast_add,
    add_sub_cancel_right, natCast_zsmul]

/-- The sum of the weights across any permutation is the constant `m • s + n • r + (m*n) • d`. -/
lemma sylvesterWeight_sum :
    ∑ i, sylvesterWeight r s d m n (σ i) i = m • s + n • r + (m*n) • d := calc
  _ = ∑ i, (sylvesterWeightZero r s d m n i + (σ i : ℤ) • d) :=
        Fintype.sum_congr _ _ <| fun _ ↦ sylvesterWeight_apply_eq_zero ..
  _ = ∑ i, (sylvesterWeightZero r s d m n i) + ∑ i, (σ i : ℤ) • d :=
        Finset.sum_add_distrib
  _ = (∑ i, sylvesterWeightZero r s d m n i) + (∑ i : Fin (n+m), (i : ℤ) • d) :=
        congr_arg (_ + ·) <| Fintype.sum_equiv σ _ _ <| fun _ ↦ rfl
  _ = ∑ i, (sylvesterWeightZero r s d m n i + (i : ℤ) • d) :=
        Finset.sum_add_distrib.symm
  _ = ∑ i, (sylvesterWeight r s d m n i i) :=
        Fintype.sum_congr _ _ <| fun _ ↦ Eq.symm <| sylvesterWeight_apply_eq_zero ..
  _ = ∑ i, sylvesterWeight r s d m n (Fin.castAdd m i) (Fin.castAdd m i) +
          ∑ i, sylvesterWeight r s d m n (Fin.natAdd n i) (Fin.natAdd n i) :=
        Fin.sum_univ_add _
  _ = (∑ i : Fin n, r) + ∑ i : Fin m, (s + n • d) :=
        congr_arg₂ (· + ·) (Fintype.sum_congr _ _ <| sylvesterWeight_apply_same_left _ _ _ _ _)
          (Fintype.sum_congr _ _ <| sylvesterWeight_apply_same_right _ _ _ _ _)
  _ = _ := by rw [Fin.sum_const, Fin.sum_const, smul_add, add_left_comm, add_assoc, mul_smul]

/-- Any one entry of the sylvester matrix is homogeneous. -/
lemma sylvester_homogeneous_single (i j) : MvPolynomial.IsWeightedHomogeneous
    (Sum.elim (fun i ↦ r + (i:ℤ) • d : Fin (m+1) → M) (fun j ↦ s + (j:ℤ) • d : Fin (n+1) → M))
    (universalSylvester m n i j)
    (sylvesterWeight r s d m n i j) := by
  rw [universalSylvester]
  cases j using Fin.addCases with
  | left j => cases i using sylvester_induction_left j with
    | fst_coeff k =>
        rw [sylvester_fst_coeff, universalPair_coeff_fin_left]
        convert MvPolynomial.isWeightedHomogeneous_X ..
        simp [sylvesterWeight]
    | fst_zero₁ i => rw [sylvester_fst_zero₁]; exact MvPolynomial.isWeightedHomogeneous_zero ..
    | fst_zero₂ i => rw [sylvester_fst_zero₂]; exact MvPolynomial.isWeightedHomogeneous_zero ..
  | right j => cases i using sylvester_induction_right j with
    | snd_coeff k =>
        rw [sylvester_snd_coeff, universalPair_coeff_fin_right]
        convert MvPolynomial.isWeightedHomogeneous_X ..
        simp [sylvesterWeight]
    | snd_zero₁ i => rw [sylvester_snd_zero₁]; exact MvPolynomial.isWeightedHomogeneous_zero ..
    | snd_zero₂ i => rw [sylvester_snd_zero₂]; exact MvPolynomial.isWeightedHomogeneous_zero ..

/-- Product across any permutation of the sylvester matrix is homogeneous. -/
lemma sylvester_homogeneous_perm : MvPolynomial.IsWeightedHomogeneous
    (Sum.elim (fun i ↦ r + (i:ℤ) • d : Fin (m+1) → M) (fun j ↦ s + (j:ℤ) • d : Fin (n+1) → M))
    (∏ i, universalSylvester m n (σ i) i)
    (m • s + n • r + (m*n) • d) := by
  rw [← sylvesterWeight_sum (σ:=σ)]
  exact .prod _ _ _ (fun i _ ↦ sylvester_homogeneous_single ..)

/-- The resultant is a weighted homogeneous polynomial where the weights can belong to any
arithmetic sequence (with the same common difference). Let the weight of `aᵢ` be `r+(i•d)` and
the weight of `bⱼ` be `s+(j•d)`. Then the weight of `Res(∑aᵢXⁱ,∑bⱼXʲ)` is `m•s+n•r+(m*n)•d` where
`m` and `n` are the degrees of the two universal polynomials respectively. -/
theorem universalResultant_isWeightedHomogeneous_aux :
    (universalResultant m n).IsWeightedHomogeneous
      (Sum.elim (fun i ↦ r + (i:ℤ) • d : Fin (m+1) → M) (fun j ↦ s + (j:ℤ) • d : Fin (n+1) → M))
      (m • s + n • r + (m*n) • d) := by
  rw [universalResultant_eq, Matrix.det_apply]
  refine .sum _ _ _ (fun σ _ ↦ (sylvester_homogeneous_perm ..).zsmul _)

-- TODO: This can be generalised to monoids but with more work. We might also just be better off
-- working in ℤ from now on.

/-- The resultant is a weighted homogeneous polynomial where the weight of `aᵢ` is `m-i` and
the weight of `bⱼ` is `n-j`, of weighted degree `m*n`. -/
theorem universalResultant_isWeightedHomogeneous_int :
    (universalResultant m n).IsWeightedHomogeneous
      (Sum.elim (fun i ↦ m - i : Fin (m+1) → ℤ) (fun j ↦ n - j : Fin (n+1) → ℤ))
      (m * n : ℤ) := by
  convert universalResultant_isWeightedHomogeneous_aux (m:ℤ) n (-1) .. using 1 <;>
    simp [Int.add_neg_eq_sub, mul_comm]

/-- The resultant is a weighted homogeneous polynomial where the weight of `aᵢ` is `m-i` and
the weight of `bⱼ` is `n-j`, of weighted degree `m*n`. -/
theorem universalResultant_isWeightedHomogeneous :
    (universalResultant m n).IsWeightedHomogeneous
      (Sum.elim (fun i ↦ m - i : Fin (m+1) → ℕ) (fun j ↦ n - j : Fin (n+1) → ℕ))
      (m * n : ℕ) := by
  intro σ hσ
  refine Int.natCast_inj.1 ?_
  have := universalResultant_isWeightedHomogeneous_int m n hσ
  simp [Finsupp.weight_apply] at this ⊢
  convert this using 5 with a b; cases a <;> exact Int.ofNat_sub (Fin.is_le _)

theorem universalResultant_isHomogeneous_int :
    (universalResultant m n).IsWeightedHomogeneous (fun _ ↦ (1 : ℤ)) (m + n : ℤ) := by
  convert universalResultant_isWeightedHomogeneous_aux (1:ℤ) 1 0 .. using 1 <;> simp

/-- The resultant is a homogeneous polynomial of degree `m+n`. -/
theorem universalResultant_isHomogeneous : (universalResultant m n).IsHomogeneous (m + n) :=
  fun σ hσ ↦ Int.natCast_inj.1
    (by simpa [Finsupp.weight_apply] using universalResultant_isHomogeneous_int m n hσ)

/-- The split resultant `Res(∏(X-aᵢ),∏(X-bⱼ))` is homogeneous of degree `mn`. -/
theorem universalSplitResultant_isHomogeneous :
    (universalSplitResultant m n).IsHomogeneous (m * n) := by
  rw [universalSplitResultant_eq']
  refine (universalResultant_isWeightedHomogeneous m n).eval₂ _ _ _ _
    (Sum.rec (fun i ↦ ?_) (fun j ↦ ?_))
  · simp only [Sum.elim_inl, MvPolynomial.esymm_eq_sum_subtype, ← zsmul_eq_mul, map_sum, map_prod,
      MvPolynomial.rename_X]
    refine .zsmul _ (.sum _ _ _ (fun s _ ↦ ?_))
    conv => enter [3]; rw [← s.2, Finset.card_eq_sum_ones]
    exact .prod s.1 _ 1 (fun j _ ↦ MvPolynomial.isWeightedHomogeneous_X _ _ _)
  · simp only [Sum.elim_inr, MvPolynomial.esymm_eq_sum_subtype, ← zsmul_eq_mul, map_sum, map_prod,
      MvPolynomial.rename_X]
    refine .zsmul _ (.sum _ _ _ (fun s _ ↦ ?_))
    conv => enter [3]; rw [← s.2, Finset.card_eq_sum_ones]
    exact .prod s.1 _ 1 (fun j _ ↦ MvPolynomial.isWeightedHomogeneous_X _ _ _)

end IsHomogeneous


section formula

variable (m n : ℕ)

/-- The fundamental theorem of resultants: `Res(∏(X-aᵢ),∏(X-bⱼ)) = (-1)ᵐⁿ∏∏(aᵢ-bⱼ)`. -/
theorem universalSplitResultant_eq : universalSplitResultant m n =
  ((-1)^(m*n) : ℤˣ) • ∏ i : Fin m, ∏ j : Fin n, (.X (Sum.inl i) - .X (Sum.inr j)) :=
_

#check exists_C_mul_eq_of_dvd

end formula


end Polynomial

#lint
