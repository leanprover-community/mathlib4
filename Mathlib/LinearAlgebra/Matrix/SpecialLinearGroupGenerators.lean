import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

def IntegralMatrices (m : ℤ) := { A : Matrix n n R // A.det = m }

open ModularGroup Matrix SpecialLinearGroup MatrixGroups

local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2)  ℤ)

local notation:1024 "Δ" m : 1024 => (IntegralMatrices (Fin 2) ℤ m)

lemma S_pow_two : ↑ₘ(S ^ 2) = -1 := by
  simp_rw [S, pow_two]
  simp
  exact Eq.symm (eta_fin_two (-1))

def reps (m : ℤ) : Set (Δ m) :=
  { A : Δ m | (A.1 1 0) = 0 ∧ 0 < A.1 0 0 ∧ 0 ≤ A.1 0 1 ∧  |(A.1 0 1)| < |(A.1 1 1)|}


variable (m : ℤ) (g : SpecialLinearGroup n R) (A : Δ m) (R : Type*) [CommRing R]

instance (m : outParam ℤ)  : HSMul (SpecialLinearGroup n R) (IntegralMatrices n R m)
  ((IntegralMatrices n R m)) :=
{ hSMul := fun g A => ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩}

lemma smul_def (m : ℤ) (g : SpecialLinearGroup n R) (A : (IntegralMatrices n R m)) : g • A =
  ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ := rfl

instance (m : ℤ) :
 MulAction (SpecialLinearGroup n R) (IntegralMatrices n R m):=
{ smul := fun g A => g • A
  one_smul := by intro b; rw [smul_def]; simp
  mul_smul := by
      intro x y b
      simp_rw [smul_def, ←mul_assoc]
      rfl
 }

lemma smul_coe (m : ℤ) (g : SpecialLinearGroup n R) (A : (IntegralMatrices n R m)) :
  (g • A).1 = g * A.1 := by
  rw [smul_def]

lemma aux1 (m : ℤ)  (A : Δ m) :
  A.1 0 0 -( A.1 1 0)*(A.1 0 0/ A.1 1 0)= A.1 0 0 % A.1 1 0:= by
  simp only [Int.cast_id, Fin.isValue]
  exact Eq.symm (Int.emod_def (A.1 0 0) (A.1 1 0))

/--Reduction step to matrices in `Mat m` which moves the matrices towars `reps`.-/
def reduce_step (A : Δ m) : Δ m :=  S • ( (T^(-((A.1 0 0)/(A.1 1 0)))) • A)

lemma reduce_aux (m : ℤ) (A : Δ m) (h : Int.natAbs (A.1 1 0) ≠ 0) :
  Int.natAbs ((reduce_step m A).1 1 0) < Int.natAbs (A.1 1 0) := by
  rw [reduce_step]
  have ha : A.1 1 0 ≠ 0 := by
    exact Int.natAbs_ne_zero.mp h
  simp only [Int.cast_id, Fin.isValue,gt_iff_lt]
  have h1 := aux1 m A
  simp_rw [smul_coe]
  rw [coe_T_zpow]
  rw [S]
  simp only [Int.reduceNeg, Fin.isValue, Int.cast_id, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    empty_mul, Equiv.symm_apply_apply, vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul,
    one_smul, empty_vecMul, add_zero, zero_add, of_apply, cons_val', Pi.neg_apply, empty_val',
    cons_val_fin_one, cons_val_one, head_fin_const, gt_iff_lt]
  rw [vecMul]
  simp [vecHead, vecTail]
  rw [mul_comm]
  rw [← @Int.sub_eq_add_neg, h1]
  have := Int.mod_lt_of_pos
  have :=  Int.emod_lt (A.1 0 0) ha
  zify
  apply le_trans _ this
  simp
  have := Int.emod_nonneg (A.1 0 0) ha
  have := abs_eq_self.mpr this
  rw [this]

@[elab_as_elim]
def reduce_rec {C : Δ m → Sort*}
(h0 : ∀ A : Δ m, Int.natAbs (A.1 1 0) = 0 → C A)
(h1 : ∀ A : Δ m, Int.natAbs ((A.1 1 0)) ≠ 0 → C (reduce_step m A) → C A): ∀ A, C A := fun A => by
    by_cases h : Int.natAbs (A.1 1 0) = 0
    · apply h0
      apply h
    · exact h1 A h (reduce_rec h0 h1 (reduce_step m A))
    termination_by A => Int.natAbs (A.1 1 0)
    decreasing_by
      simp
      apply reduce_aux m A
      simp
      rw [@Int.natAbs_eq_zero] at h
      exact h

def reduce : Δ m → Δ m := fun A => by
  if h : Int.natAbs (A.1 1 0) = 0 then
    if ha : 0 < A.1 0 0 then exact (T^(-(A.1 0 1/A.1 1 1))) • A else exact
      (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A))
  else
    exact reduce (reduce_step m A)
  termination_by b => Int.natAbs (b.1 1 0)
  decreasing_by
      simp
      apply reduce_aux m
      simp
      rw [@Int.natAbs_eq_zero] at h
      exact h

lemma reduce_eqn1 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : 0 < A.1 0 0) :
  reduce m A = (T^(-(A.1 0 1/A.1 1 1))) • A := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc]
  rw [if_pos ha]

lemma reduce_eqn2 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : ¬ 0 < A.1 0 0) :
  reduce m A = (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A)) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc]
  rw [if_neg ha]

lemma reduce_eqn3 (A : Δ m) (hc : ¬ Int.natAbs (A.1 1 0) = 0) :
  reduce m A = reduce m (reduce_step m A) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_neg hc]

example (a b : ℤ) : a < b ↔ 0 < b - a := by
  exact Iff.symm Int.sub_pos

lemma A_d_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp at this
  aesop

lemma reduce_mem_reps (m : ℤ) (hm : m ≠ 0)  : ∀ A : Δ m, reduce m A ∈ reps m := by
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    rw [reduce_eqn1 _ _ h h1]
    rw [reps]

    simp
    rw [smul_coe]
    simp
    simp_rw [coe_T_zpow]
    simp
    simp_rw [vecMul]
    simp [vecHead, vecTail]
    refine ⟨ Int.natAbs_eq_zero.mp h, by simp at h; rw [h]; simp [h1], by
      apply Int.ediv_mul_le ; apply A_d_ne_zero _ _ (by simpa using h) hm, by
      rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (A.1 0 1) (A.1 1 1)).symm]
      have :=  Int.emod_lt (A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm)
      apply le_trans _ this
      simp
      have := Int.emod_nonneg (A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm)
      rw [abs_eq_self.mpr this]⟩
    rw [reduce_eqn2 _ _ h h1]
    rw [reps]
    simp
    rw [smul_coe]
    simp
    simp_rw [coe_T_zpow]
    simp
    simp_rw [vecMul]
    simp [vecHead, vecTail, smul_def, ← mul_assoc]
    rw [← pow_two]
    have := S_pow_two
    simp at this
    rw [this]
    simp
    sorry




    --exact ⟨rfl, h, le_refl _, Int.nat_abs_of_nat h⟩
  · intro A h1 h2
    rw [reduce_eqn3]
    exact h2
    sorry
