import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.SuppressCompilation

open scoped Polynomial
open Polynomial (C X)

variable {R} [Semiring R] (p q : R[X])

class Polynomial.ComputableRepr where
  coeff : ℕ → R
  degreeBound : ℕ
  coeff_eq ⦃n : ℕ⦄ : p.coeff n = coeff n
  support_subset : p.support ⊆ Finset.range degreeBound

open Polynomial.ComputableRepr

instance : (0 : R[X]).ComputableRepr where
  coeff _ := 0
  degreeBound := 0
  coeff_eq := by simp
  support_subset := by simp

-- Can't make this work:
/- noncomputable instance (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : R[X]).ComputableRepr where
  coeff n := if n = 0 then m else 0
  degreeBound := 1
  coeff_eq := by sorry
  support_subset := sorry
example : (2 : ℤ[X]).ComputableRepr := inferInstance -- fails -/

instance (r : R) : (C r).ComputableRepr where
  coeff n := if n = 0 then r else 0
  degreeBound := 1
  coeff_eq := by simp [Polynomial.coeff_C]
  support_subset := by rw [← Polynomial.monomial_zero_left]; apply Polynomial.support_monomial'

instance : (X : R[X]).ComputableRepr where
  coeff n := if n = 1 then 1 else 0
  degreeBound := 2
  coeff_eq _ := by simp_rw [Polynomial.coeff_X, eq_comm]
  support_subset := by
    rw [← Polynomial.monomial_one_one_eq_X]
    exact (Polynomial.support_monomial' _ _).trans (by simp)

def Nat.withBotAdd : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _, 0 => 0
  | m + 1, n + 1 => m + n + 1

@[simps] def WithBot.natSuccIso : WithBot ℕ ≃o ℕ where
  toFun m := m.recBotCoe 0 (· + 1)
  invFun m := m.rec ⊥ (↑)
  left_inv m := by cases m <;> rfl
  right_inv m := by cases m <;> rfl
  map_rel_iff' {m n} := by
    cases m; · simp [recBotCoe]
    cases n; · simp [recBotCoe]
    simp [recBotCoe]

def WithBot.natSucc (n : WithBot ℕ) : ℕ := WithBot.natSuccIso n

lemma Polynomial.natSucc_degree (hp : p ≠ 0) : p.degree.natSucc = p.natDegree + 1 := by
  rw [natDegree, ← WithBot.coe_unbot _ (degree_eq_bot.not.mpr hp)]; rfl

lemma WithBot.natSucc_withBotAdd (m n : WithBot ℕ) :
    m.natSucc.withBotAdd n.natSucc = (m + n).natSucc := by cases m <;> cases n <;> rfl

lemma WithBot.natSuccIso_symm_withBotAdd (m n : ℕ) :
    WithBot.natSuccIso.symm (m.withBotAdd n) =
    WithBot.natSuccIso.symm m + WithBot.natSuccIso.symm n := by cases m <;> cases n <;> rfl

variable [p.ComputableRepr]

lemma natSucc_degree_le_degreeBound : p.degree.natSucc ≤ degreeBound p := by
  obtain rfl | hp := eq_or_ne p 0; · exact bot_le
  have := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [Polynomial.leadingCoeff, ← Polynomial.mem_support_iff] at this
  rw [Polynomial.natSucc_degree p hp]
  exact Finset.mem_range.mp (support_subset this)

omit [p.ComputableRepr] in
lemma Polynomial.support_subset_range : p.support ⊆ Finset.range p.degree.natSucc := fun n h ↦ by
  by_cases hp : degree p = ⊥
  · simp_all
  · rw [natSucc_degree p (degree_eq_bot.not.mp hp), Finset.mem_range_succ_iff]
    contrapose! h
    exact notMem_support_iff.mpr (coeff_eq_zero_of_natDegree_lt h)

-- TODO: replace assumptions of `support_smul` and here by `[SMulZeroClass S R]`
instance {S} [Monoid S] [DistribMulAction S R] (s : S) : (s • p).ComputableRepr where
  coeff n := s • coeff p n
  degreeBound := degreeBound p
  coeff_eq _ := by rw [Polynomial.coeff_smul, coeff_eq]
  support_subset := (Polynomial.support_smul _ _).trans support_subset

namespace Polynomial.ComputableRepr

variable {p} in
theorem coeff_eq_zero_of_le {n : ℕ} (hn : degreeBound p ≤ n) : p.coeff n = 0 :=
  notMem_support_iff.mp fun h ↦ hn.not_lt (Finset.mem_range.mp <| support_subset h)

@[reducible] def ofEq (h : p = q) : q.ComputableRepr where
  coeff := coeff p
  degreeBound := degreeBound p
  coeff_eq _ := by rw [← coeff_eq, h]
  support_subset := h ▸ support_subset

section degreeAux

def degreeAux (P : ℕ → Prop) [DecidablePred P] : ℕ → WithBot ℕ
  | 0 => ⊥
  | n + 1 => if P n then n else degreeAux P n

variable (P : ℕ → Prop) [DecidablePred P] (n : ℕ)

-- not used
lemma degreeAux_lt : degreeAux P n < n := by
  induction' n with n ih; · apply WithBot.bot_lt_coe
  rw [degreeAux]; split_ifs
  on_goal 2 => apply ih.trans
  all_goals exact WithBot.coe_lt_coe.mpr n.lt_succ_self

lemma degreeAux_of_forall_not (h : ∀ m < n, ¬ P m) : degreeAux P n = ⊥ := by
  induction' n with n ih; · rfl
  rw [degreeAux, if_neg (h n n.lt_succ_self)]; exact ih fun m hm ↦ h m (hm.trans n.lt_succ_self)

lemma degreeAux_spec_of_exists (h : ∃ m < n, P m) :
    ∃ m < n, P m ∧ (∀ k < n, m < k → ¬ P k) ∧ degreeAux P n = m := by
  induction' n with n ih
  · obtain ⟨m, hmn, -⟩ := h; cases hmn
  by_cases hn : P n
  · refine ⟨n, n.lt_succ_self, hn, fun k hkn hnk ↦ (hnk.not_le <| Nat.lt_succ.mp hkn).elim, ?_⟩
    rw [degreeAux, if_pos hn]
  obtain ⟨m, hmn, hm⟩ := h
  obtain rfl | hmn := (Nat.lt_succ.mp hmn).eq_or_lt
  · exact (hn hm).elim
  obtain ⟨m, hmn, hm, ih, _⟩ := ih ⟨m, hmn, hm⟩
  refine ⟨m, hmn.trans n.lt_succ_self, hm, fun k hkn hmk ↦ ?_, ?_⟩
  · obtain rfl | hkn := (Nat.lt_succ.mp hkn).eq_or_lt; exacts [hn, ih k hkn hmk]
  · rwa [degreeAux, if_neg hn]

end degreeAux

variable [DecidableEq R]

def degree : WithBot ℕ := degreeAux (coeff p · ≠ 0) (degreeBound p)
def natDegree : ℕ := (degree p).unbotD 0
def leadingCoeff : R := coeff p (natDegree p)
abbrev Monic : Prop := leadingCoeff p = 1

lemma degree_eq : p.degree = degree p := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [degree, degreeAux_of_forall_not, degree_zero]
    rintro m -; rw [← coeff_eq]; exact not_not_intro (coeff_zero m)
  have := leadingCoeff_ne_zero.mpr hp
  obtain ⟨m, -, hpm, hmax, eq⟩ := degreeAux_spec_of_exists (coeff p · ≠ 0) (degreeBound p)
    ⟨p.natDegree, Finset.mem_range.mp (support_subset <| mem_support_iff.mpr this),
      by simp_rw [← coeff_eq]; exact this⟩
  rw [degree, eq]
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by rwa [coeff_eq])
  rw [degree_le_iff_coeff_zero]
  intro n hmn
  obtain hnd | hdn := lt_or_le n (degreeBound p)
  · rw [coeff_eq]; exact of_not_not (hmax n hnd <| WithBot.coe_lt_coe.mp hmn)
  · exact coeff_eq_zero_of_le hdn

lemma natDegree_eq : p.natDegree = natDegree p := by rw [natDegree, ← degree_eq]; rfl
lemma leadingCoeff_eq : p.leadingCoeff = leadingCoeff p := by
  rw [leadingCoeff, ← coeff_eq, ← natDegree_eq]; rfl
lemma monic_iff : p.Monic ↔ Monic p := by rw [Monic, ← leadingCoeff_eq]; rfl

instance : Decidable p.Monic := decidable_of_iff _ (monic_iff p).symm

end Polynomial.ComputableRepr

noncomputable instance : (1 : R[X]).ComputableRepr := .ofEq (C 1) _ (map_one C)
noncomputable instance (m : ℕ) : (m : R[X]).ComputableRepr := .ofEq _ _ (Polynomial.C_eq_natCast m)

variable [q.ComputableRepr]

instance : (p + q).ComputableRepr where
  coeff n := coeff p n + coeff q n
  degreeBound := max (degreeBound p) (degreeBound q)
  coeff_eq _ := by simp_rw [Polynomial.coeff_add, coeff_eq]
  support_subset := Polynomial.support_add.trans <|
    (Finset.union_subset_union support_subset support_subset).trans fun _ _ ↦ by simp_all

open scoped BigOperators

instance : (p * q).ComputableRepr where
  coeff n := ∑ i ∈ Finset.range (min (degreeBound p) (n + 1)), coeff p i * coeff q (n - i)
  degreeBound := (degreeBound p).withBotAdd (degreeBound q)
  coeff_eq n := by
    simp_rw [← coeff_eq, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_range_add_sum_Ico _ (min_le_right _ _)]
    convert add_zero _
    refine Finset.sum_eq_zero fun n h ↦ ?_
    rw [Finset.mem_Ico, min_le_iff, ← not_lt, or_iff_left h.2.not_le, ← Finset.mem_range] at h
    rw [Polynomial.notMem_support_iff.mp fun hn ↦ h.1 (support_subset hn), zero_mul]
  support_subset := (p * q).support_subset_range.trans <| Finset.range_mono <|
    (WithBot.natSuccIso.monotone <| p.degree_mul_le q).trans <| by
      rw [← WithBot.natSuccIso.symm.map_rel_iff, OrderIso.symm_apply_apply,
        WithBot.natSuccIso_symm_withBotAdd]
      apply add_le_add <;> rw [OrderIso.le_symm_apply] <;> apply natSucc_degree_le_degreeBound

abbrev Nat.strongRec₀ {p : ℕ → Sort*} (H : Π n, (Π m, m < n → p m) → p n) (n : ℕ) : p n :=
  H _ <| n.rec (fun _ h ↦ by simp at h)
    fun n ih m hmn ↦ H _ fun l hlm ↦ ih _ (hlm.trans_le <| Nat.le_of_lt_succ hmn)

suppress_compilation in
instance (priority := mid) pow : (n : ℕ) → (p ^ n).ComputableRepr :=
  Nat.strongRec₀ fun n ih ↦ if h0 : n = 0 then
    ofEq 1 _ (h0 ▸ pow_zero _).symm else
    letI := ih (n / 2) (by omega)
    let pow_half := p ^ (n / 2)
    n.even_or_odd.by_cases (fun h ↦ ofEq (pow_half * pow_half) _ <| by
      rw [← Nat.two_mul_div_two_of_even h, two_mul, pow_add])
    fun h ↦ ofEq (p * (pow_half * pow_half)) _ <| by
      rw [← Nat.two_mul_div_two_add_one_of_odd h, add_comm, two_mul, pow_add, pow_add, pow_one]

/-suppress_compilation in
-- less efficient version of the above
instance (priority := mid) pow' : (n : ℕ) → (p ^ n).ComputableRepr :=
  Nat.rec (ofEq 1 _ (pow_zero _).symm) fun n _ ↦ ofEq (p * p ^ n) _ (pow_succ' _ _).symm -/

instance (m : ℕ) : (X ^ m : R[X]).ComputableRepr where
  coeff n := if n = m then 1 else 0
  degreeBound := m + 1
  coeff_eq _ := by simp_rw [Polynomial.coeff_X_pow]
  support_subset := by
    rw [← Polynomial.monomial_one_right_eq_X_pow]
    exact (Polynomial.support_monomial' _ _).trans (by simp)

noncomputable instance {S} [Semiring S] (f : R →+* S) : (p.map f).ComputableRepr where
  coeff n := f (coeff p n)
  degreeBound := degreeBound p
  coeff_eq _ := by rw [Polynomial.coeff_map, coeff_eq]
  support_subset := (Polynomial.support_map_subset _ _).trans support_subset

section

variable {S} [Ring S] (p q : S[X]) [p.ComputableRepr] [q.ComputableRepr]

instance : (-p).ComputableRepr where
  coeff n := - coeff p n
  degreeBound := degreeBound p
  coeff_eq _ := by rw [Polynomial.coeff_neg, coeff_eq]
  support_subset := by rw [Polynomial.support_neg]; exact support_subset

-- `coeff p n - coeff q n` more efficient?
noncomputable instance : (p - q).ComputableRepr := .ofEq (p + -q) _ (sub_eq_add_neg _ _)

end

theorem Polynomial.ComputableRepr.eq_iff : p = q ↔
    ∀ i ∈ Finset.range (max (degreeBound p) (degreeBound q)), coeff p i = coeff q i :=
  ⟨fun h _ _ ↦ by simp_rw [← coeff_eq, h], fun h ↦ ext fun n ↦ by
    simp only [Finset.mem_range, lt_max_iff] at h
    by_cases hn : n < degreeBound p ∨ n < degreeBound q
    · simp_rw [coeff_eq]; exact h n hn
    · simp_rw [not_or, not_lt] at hn; rw [coeff_eq_zero_of_le hn.1, coeff_eq_zero_of_le hn.2]⟩

instance [DecidableEq R] : Decidable (p = q) := decidable_of_iff _ (eq_iff p q).symm

example : (X + X : ℤ[X]) = (2 * X : ℤ[X]) := by
  rw [← Nat.cast_ofNat] -- have to do this
  decide

noncomputable def H : ℚ[X] := X ^ 3 - (C (6/8) * X) - C (1/8)
noncomputable def H' : ℤ[X] := C 8 * X ^ 3 - (C 6 * X) - C 1

lemma H_H' : C 8 * H = H'.map (algebraMap ℤ ℚ) := by
  rw [H, H']; with_unfolding_all decide

lemma H'_degree : H'.natDegree = 3 := by rw [H', natDegree_eq]; rfl
lemma H_degree : H.natDegree = 3 := by rw [H, natDegree_eq]; with_unfolding_all rfl
lemma H_monic : H.Monic := by rw [H, monic_iff]; with_unfolding_all rfl
lemma H_ne_zero : H ≠ 0 := by rw [H]; with_unfolding_all decide
lemma H'_coeff_zero : H'.coeff 0 = -1 := by rw [H', coeff_eq]; rfl
lemma H'_leading : H'.leadingCoeff = 8 := by rw [H', leadingCoeff_eq]; rfl

example :
    (X ^ 1000000000000 + 1 : ℚ[X]).degree = 1000000000000 := by
  rw [degree_eq]; with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : (X ^ 100 : ℕ[X]) * (X ^ 100 : ℕ[X]) = X ^ 200 := by
  decide

example : (X : ℚ[X]) ^ 2 = X ^ 2 - X + X := by with_unfolding_all decide

set_option profiler true
example : (X + 1 : (ZMod 11)[X]) ^ 11 = X ^ 11 + 1 := by
  with_unfolding_all decide
/- Exponential by squaring:
tactic execution of Lean.Parser.Tactic.decide took 2.98s
tactic execution of Lean.Parser.Tactic.tacticSeq1Indented took 166ms
Using `pow'` instead of `pow`:
tactic execution of Lean.Parser.Tactic.decide took 17.9s
tactic execution of Lean.Parser.Tactic.tacticSeq1Indented took 818ms -/

example : (X ^ 100 + 1 : ℕ[X]) * (X ^ 100 + 1 : ℕ[X]) = X ^ 200 + 2 * X ^ 100 + 1 := by
  simp_rw [mul_add, add_mul]; ring

example :
    (1 + X + X ^ 2 - X ^ 5 - X ^ 6 - 2 * X ^ 7 - X ^ 8 - X ^ 9 + X ^ 12 + X ^ 13 + X ^ 14 +
        X ^ 15 + X ^ 16 + X ^ 17 - X ^ 20 - X ^ 22 - X ^ 24 - X ^ 26 - X ^ 28 + X ^ 31 + X ^ 32 +
        X ^ 33 + X ^ 34 + X ^ 35 + X ^ 36 - X ^ 39 - X ^ 40 - 2 * X ^ 41 - X ^ 42 - X ^ 43 +
        X ^ 46 + X ^ 47 + X ^ 48 : ℤ[X]).degree = 48 := by
  rw [← Nat.cast_ofNat (R := ℤ[X]) (n := 2), degree_eq]; rfl
/- typeclass inference of Polynomial.ComputableRepr took 116ms
elaboration took 161ms -/

set_option maxRecDepth 1000 in
example :
    (1 + X + X ^ 2 - X ^ 5 - X ^ 6 - 2 * X ^ 7 - X ^ 8 - X ^ 9 + X ^ 12 + X ^ 13 + X ^ 14 +
        X ^ 15 + X ^ 16 + X ^ 17 - X ^ 20 - X ^ 22 - X ^ 24 - X ^ 26 - X ^ 28 + X ^ 31 + X ^ 32 +
        X ^ 33 + X ^ 34 + X ^ 35 + X ^ 36 - X ^ 39 - X ^ 40 - 2 * X ^ 41 - X ^ 42 - X ^ 43 +
        X ^ 46 + X ^ 47 + X ^ 48 : ℚ[X]).degree = 48 := by
  rw [← Nat.cast_ofNat (R := ℚ[X]) (n := 2), degree_eq]; with_unfolding_all rfl
/- typeclass inference of Polynomial.ComputableRepr took 114ms
elaboration took 169ms -/
