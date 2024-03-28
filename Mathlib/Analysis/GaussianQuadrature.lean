import Mathlib.Analysis.Complex.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Basic

open MeasureTheory Polynomial Set Real Finset BigOperators Lagrange

noncomputable section


-- An interval of ℝ with a nonatomic measure, and where polynomials are integrable
structure IntervalWithMeasure where
  a : ℝ
  b : ℝ
  hab : a < b
  μ : Measure ℝ
  hna : MeasureTheory.NoAtoms μ
  hp : μ (Ioc a b) > 0
  hpi (p : ℝ[X]) : IntervalIntegrable (fun x => (p.eval x)) μ a b


-- Integral of a polynomial
def IntervalWithMeasure.int (s : IntervalWithMeasure) (p : ℝ[X]) : ℝ :=
  ∫ x in s.a..s.b, p.eval x ∂s.μ


-- L² scalar product between 2 polynomials
def IntervalWithMeasure.dot (s: IntervalWithMeasure)(p q : ℝ[X]) : ℝ :=
  ∫ x in s.a..s.b, (p * q).eval x ∂s.μ


-- the scalar product of 2 polynomials is well posed, since it's integrable
theorem IntervalWithMeasure.IntervalIntegrable_dot (s : IntervalWithMeasure)(p q : ℝ[X]) :
    IntervalIntegrable (fun x => p.eval x * q.eval x) s.μ s.a s.b:= by
  let h (x : ℝ) : p.eval x * q.eval x = (p * q).eval x := by
    simp only [eval_mul]
  simp only [h]
  exact s.hpi (p * q)


-- polynomials with a structure of inner product space
@[inline, reducible]
abbrev MySpace (s: IntervalWithMeasure) := WithLp 2 ℝ[X]


variable { s : IntervalWithMeasure }


instance : NoAtoms s.μ where
  measure_singleton := by
    intro x
    apply s.hna.measure_singleton


instance MySpace.instInner : Inner ℝ (MySpace s) where
  inner := s.dot


instance MySpace.inst_HMul_poly : HMul ℝ[X] (MySpace s) (MySpace s) := by
    simp_rw [MySpace]
    simp_rw [WithLp]
    infer_instance


instance MySpace.inst_HMul_poly' : HMul (MySpace s) ℝ[X] (MySpace s) := by
    simp_rw [MySpace]
    simp_rw [WithLp]
    infer_instance


instance MySpace.instDecidableEq : DecidableEq (MySpace s) := by
  simp_rw [MySpace]
  simp_rw [WithLp]
  infer_instance


theorem MySpace.inner_def (x y : MySpace s) : ⟪x, y⟫_ℝ = s.dot x y :=
  rfl


-- a nonzero polynomial that is nonnegative on an open interval, has positive integral in that interval
theorem MySpace.integral_pos_of_pos {p : MySpace s} (hne0 : p ≠ 0)
    (hpos : ∀ x : ℝ, x ∈ Ioo s.a s.b → p.eval x ≥ 0) : 0 < ∫ (x : ℝ) in s.a..s.b, p.eval x ∂s.μ := by

  have hpge0ae : 0 ≤ᶠ[MeasureTheory.Measure.ae (MeasureTheory.Measure.restrict s.μ (Ι s.a s.b))] p.eval := by
    apply MeasureTheory.ae_restrict_uIoc_iff.mpr
    simp only [Pi.zero_apply]
    constructor
    have : ∀ᵐ (x : ℝ) ∂Measure.restrict s.μ (Set.Ioc s.a s.b), x ∈ Ioc s.a s.b :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    apply Filter.Eventually.mp this
    apply ae_of_all
    intro x hx
    have hx := Set.Ioc_subset_Icc_self hx
    apply le_on_closure hpos
    apply continuousOn_const
    apply Polynomial.continuousOn
    rw [closure_Ioo]
    exact hx
    exact LT.lt.ne s.hab
    rw [Set.Ioc_eq_empty (LT.lt.not_lt s.hab)]
    simp only [Measure.restrict_empty, ae_zero, Filter.eventually_bot]

  have hroot : {x : ℝ | p.eval x = 0} = {x : ℝ | Polynomial.IsRoot p x} := by
    simp only [mul_eq_zero, or_self, IsRoot.def]
  have hff0 : Set.Finite {x : ℝ | p.eval x = 0} := by
    rw [hroot]
    exact Polynomial.finite_setOf_isRoot hne0

  have hsp : s.μ (Function.support (p.eval) ∩ Ioc s.a s.b) > 0 := by
    unfold Function.support
    have hd2 : Disjoint ({x : ℝ | p.eval x ≠ 0} ∩ Ioc s.a s.b) ({x : ℝ | p.eval x = 0} ∩ Ioc s.a s.b) := by
      apply Set.disjoint_left.mpr
      intro a
      intro ha
      have ha := Set.mem_of_mem_inter_left ha
      intro hna
      have hna := Set.mem_of_mem_inter_left hna
      have hna := Set.mem_setOf.mp hna
      contradiction
    have hf : Set.Finite ({x : ℝ | p.eval x = 0} ∩ Ioc s.a s.b) := by
      apply Set.Finite.subset hff0
      apply Set.inter_subset_left
    have hu : ({x : ℝ | p.eval x ≠ 0} ∩ Ioc s.a s.b) ∪ ({x : ℝ | p.eval x = 0} ∩ Ioc s.a s.b) = Ioc s.a s.b := by
      rw [← Set.union_inter_distrib_right]
      rw [←Set.setOf_or]
      have duh (x : ℝ) : (p.eval x ≠ 0 ∨ p.eval x = 0) = True := eq_true (ne_or_eq (p.eval x) 0)
      simp only [duh]
      simp only [setOf_true, Set.univ_inter]
    have h : s.μ ({x : ℝ | p.eval x ≠ 0} ∩ Ioc s.a s.b) + s.μ ({x : ℝ | p.eval x = 0} ∩ Ioc s.a s.b) =
        s.μ (Ioc s.a s.b) := by
      rw [← (MeasureTheory.measure_union hd2 (Set.Finite.measurableSet hf))]
      rw [hu]

    rw [(Set.Finite.measure_zero hf s.μ)] at h
    rw [add_zero] at h
    rw [h]
    apply s.hp

  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hpge0ae (s.hpi p)).mpr
  constructor
  exact s.hab
  exact hsp


def MySpace.InnerProductSpaceCore : InnerProductSpace.Core ℝ (MySpace s) where
  conj_symm := by
    intro p q
    simp only [conj_trivial, inner_def, IntervalWithMeasure.dot]
    apply intervalIntegral.integral_congr
    unfold EqOn
    simp
    intro x
    intro _
    rw [mul_comm (q.eval _) (p.eval _)]
  nonneg_re := by
    intro p
    simp only [IsROrC.re_to_real, MySpace.inner_def, IntervalWithMeasure.dot]
    apply intervalIntegral.integral_nonneg (le_of_lt s.hab)
    intro x
    intro _
    rw [eval_mul]
    rw [← sq (p.eval x)]
    exact sq_nonneg (p.eval x)
  definite := by
    intro p
    simp only [IsROrC.re_to_real, MySpace.inner_def, IntervalWithMeasure.dot]
    intro hi0

    by_contra hpn0

    have hp2n0 : ((↑p * ↑p) : ℝ[X]) ≠ 0 := by
      apply mul_ne_zero
      <;> exact hpn0

    apply Eq.not_gt hi0

    apply MySpace.integral_pos_of_pos hp2n0
    intro x _
    rw [eval_mul]
    rw [← sq (p.eval x)]
    exact sq_nonneg (p.eval x)

  add_left := by
    intro p q r
    simp only [IsROrC.re_to_real, MySpace.inner_def, IntervalWithMeasure.dot]
    rw [← intervalIntegral.integral_add]
    apply intervalIntegral.integral_congr
    unfold EqOn
    simp
    intro x
    intro _
    rw [Polynomial.eval_add]
    ring_nf
    apply s.hpi
    apply s.hpi

  smul_left := by
    intro p q
    intro α
    simp only [IsROrC.re_to_real, MySpace.inner_def, IntervalWithMeasure.dot, conj_trivial]
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    unfold EqOn
    simp only [Algebra.smul_mul_assoc, eval_smul, eval_mul, smul_eq_mul, implies_true, forall_const]


instance MySpace.instNormedAddCommGroup : NormedAddCommGroup (MySpace s) :=
  MySpace.InnerProductSpaceCore.toNormedAddCommGroup


instance MySpace.instInnerProductSpace : InnerProductSpace ℝ (MySpace s) :=
  InnerProductSpace.ofCore MySpace.InnerProductSpaceCore


def pows : ℕ → MySpace s := by
  intro k
  exact X^k


-- orthogonal polynomials on an interval with respect to a specified measure
def OrthoPoly(s: IntervalWithMeasure) : ℕ → MySpace s := gramSchmidt ℝ pows


-- orthogonal polynomials are orthogonal
theorem OrthoPoly_orthogonal {a b : ℕ} (hab : a ≠ b) : ⟪OrthoPoly s a, OrthoPoly s b⟫_ℝ = 0 := by
  unfold OrthoPoly
  apply gramSchmidt_orthogonal
  exact hab


-- the span of the first n orthogonal polynomials is all the polynomials of degree ≤ n
theorem OrthoPoly_span (s) (n : ℕ) :
    Submodule.span ℝ ((OrthoPoly s) '' (Finset.range (n + 1))) = Polynomial.degreeLE ℝ n := by
  unfold OrthoPoly
  simp only [coe_range]
  rw [span_gramSchmidt_Iio ℝ pows]
  unfold pows
  rw [← coe_range]
  simp only [degreeLE_eq_span_X_pow]
  simp only [coe_range, coe_image]


theorem OrthoPoly_orthogonal_low_deg {n : ℕ} {p : MySpace s} (hdegp : degree p ≤ n) :
    ⟪OrthoPoly s (n + 1), p⟫_ℝ = 0 := by
  have h := mem_degreeLE.mpr hdegp
  rw [← OrthoPoly_span] at h
  have : ∀ ⦃u : MySpace s⦄, u ∈ (OrthoPoly s) '' (Finset.range (n+1)) →
         ∀ ⦃v : MySpace s⦄, v ∈ {(OrthoPoly s (n+1))} →
         ⟪u, v⟫_ℝ = 0 := by
    intro u hu
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    simp only [coe_range, Set.mem_image, Set.mem_Iio] at hu
    have ⟨m, ⟨hm, ho⟩⟩ := hu
    rw [← ho]
    apply OrthoPoly_orthogonal (ne_of_lt hm)
  apply Submodule.isOrtho_span.mpr this
  exact h
  exact Submodule.mem_span_singleton_self (OrthoPoly s (n+1))


theorem natbot_le_of_lt_add_one {a b : WithBot Nat} (hlt : a < b + 1) : a ≤ b := by
  rw [← WithBot.coe_one] at hlt
  cases a with
  | none =>
    simp
  | some a =>
    cases b with
    | none =>
      rw [WithBot.none_eq_bot]
      rw [WithBot.none_eq_bot] at hlt
      exfalso
      exact not_lt_bot hlt
    | some b =>
      have hlt : a < Nat.succ b := by
        simp [WithBot.some_eq_coe] at *
        rw [← WithBot.coe_one] at *
        rw [← WithBot.coe_add _ 1] at *
        exact WithBot.coe_lt_coe.mp hlt
      simp only [WithBot.some_le_some]
      apply Order.le_of_lt_succ hlt


theorem natbot_lt_of_le_sub_one {a : WithBot ℕ} {b : ℕ} (hpos : 0 < b) (hlt : a ≤ ↑(b - 1)) : a < ↑b := by
  cases h : a with
  | none =>
    apply WithBot.none_lt_some
  | some d =>
    rw [h] at hlt
    apply WithBot.coe_lt_coe.mpr
    have := WithBot.coe_le_coe.mp hlt
    simp only [Nat.cast_id, gt_iff_lt]
    simp only [Nat.cast_tsub, Nat.cast_id, Nat.cast_one] at this
    rw [← Nat.pred_eq_sub_one] at this
    apply Nat.lt_of_le_pred hpos this


theorem natbot_le_sub_one_of_lt {a : WithBot ℕ} {b : ℕ} (hle : a < ↑b) : a ≤ ↑(b - 1) := by
  cases h : a with
  | none => simp only [WithBot.none_le]
  | some d =>
    rw [h] at hle
    apply WithBot.coe_le_coe.mpr
    have := WithBot.coe_lt_coe.mp hle
    simp only [Nat.cast_tsub, Nat.cast_id, Nat.cast_one, ge_iff_le]
    simp only [Nat.cast_id] at this
    rw [← Nat.pred_eq_sub_one]
    apply Nat.le_pred_of_lt this


theorem OrthoPoly_orthogonal_low_deg' {n : ℕ} {p : MySpace s} (hdegp : degree p < n) : ⟪OrthoPoly s n, p⟫_ℝ = 0 := by
  cases n with
  | zero =>
    rw [Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hdegp)]
    simp only [Nat.zero_eq, inner_zero_right]
  | succ m =>
    have : degree p <= m := by
      simp at hdegp
      exact natbot_le_of_lt_add_one hdegp
    exact OrthoPoly_orthogonal_low_deg this


theorem OrthoPoly_linearIndependent : LinearIndependent ℝ (OrthoPoly s) := by
  apply gramSchmidt_linearIndependent
  have := Basis.linearIndependent (Polynomial.basisMonomials ℝ)
  simp only [coe_basisMonomials] at this
  unfold monomial at this
  unfold pows
  simp only [X_pow_eq_monomial]
  exact this


theorem OrthoPoly_ne_zero {n : ℕ} : OrthoPoly s n ≠ 0 := by
  exact LinearIndependent.ne_zero n OrthoPoly_linearIndependent


theorem OrthoPoly_deg (n : ℕ) : degree (OrthoPoly s n) = n := by
  cases n with
  | zero =>
    unfold OrthoPoly
    simp only [Nat.zero_eq, CharP.cast_eq_zero]
    rw [← bot_eq_zero]
    rw [gramSchmidt_zero]
    rw [bot_eq_zero]
    unfold pows
    simp only [pow_zero, degree_one]
  | succ n =>
    rw [Nat.succ_eq_add_one n]
    have hle : degree (OrthoPoly s (n+1)) ≤ n+1 := by
      apply Polynomial.mem_degreeLE.mp
      have := OrthoPoly_span s (n+1)
      simp only [Nat.cast_add, Nat.cast_one] at this
      rw [← this]
      apply Submodule.subset_span
      simp only [coe_range, Set.mem_image, Set.mem_Iio]
      use (n+1)
      constructor
      simp only [lt_add_iff_pos_right, zero_lt_one]
      rfl
    cases LE.le.lt_or_eq hle with
    | inl hlt =>
      exfalso
      have h0 := OrthoPoly_orthogonal_low_deg (natbot_le_of_lt_add_one hlt)
      simp only [inner_self_eq_zero] at h0
      have hne0 : OrthoPoly s (n+1) ≠ 0 := OrthoPoly_ne_zero
      exact hne0 h0
    | inr heq =>
      exact heq


theorem OrthoPoly_natdeg (n : ℕ) : natDegree (OrthoPoly s n) = n := by
  have : (OrthoPoly s n).degree = (OrthoPoly s n).natDegree := Polynomial.degree_eq_natDegree OrthoPoly_ne_zero
  rw [OrthoPoly_deg] at this
  simp only [Nat.cast_inj] at this
  rw [← this]


theorem IntervalWithMeasure.xp_dot_q_eq_p_dot_xq (p q : MySpace s) :
    ⟪X * p, q⟫_ℝ = ⟪p, X * q⟫_ℝ := by
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  ring_nf


theorem three_term_recurrence (n : ℕ) : ∃ a b c : ℝ, OrthoPoly s (n+2) =
    (a • X + Polynomial.C b) * (OrthoPoly s (n+1)) + (c • OrthoPoly s n) := by
  have : ∃ a : ℝ, degree ((OrthoPoly s (n+2)) - (a • X : ℝ[X]) * (OrthoPoly s (n+1))) <= n+1 := by
    let a := (OrthoPoly s (n+2) : ℝ[X]).leadingCoeff / (OrthoPoly s (n+1) : ℝ[X]).leadingCoeff
    have : OrthoPoly s (n+2) ≠ 0 ∧ OrthoPoly s (n+1) ≠ 0 := by
      simp only [ne_eq, OrthoPoly_ne_zero, not_false_eq_true, and_self]
    have hane0 : a ≠ 0 := by
      simp only [a, ne_eq, _root_.div_eq_zero_iff, leadingCoeff_eq_zero]
      exact not_or.mpr this
    use a
    have hdeg : degree (OrthoPoly s (n+2)) = degree ((a • X : ℝ[X]) * (OrthoPoly s (n+1))) := by
      rw [Polynomial.degree_mul, OrthoPoly_deg (n+2), OrthoPoly_deg (n+1), smul_eq_C_mul a,
          Polynomial.degree_mul, degree_X, Polynomial.degree_C hane0]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [← add_assoc]
      nth_rw 3 [add_comm]
      exact rfl
    have hlco : (OrthoPoly s (n+2) : ℝ[X]).leadingCoeff = ((a • X : ℝ[X]) * (OrthoPoly s (n+1))).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, smul_eq_C_mul a, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_C a, Polynomial.leadingCoeff_X]
      simp only [a]
      rw [mul_one]
      exact eq_mul_of_mul_inv_eq₀ hane0 rfl
    have := Polynomial.degree_sub_lt hdeg OrthoPoly_ne_zero hlco
    rw [OrthoPoly_deg (n+2)] at this
    exact natbot_le_of_lt_add_one this
  rcases this with ⟨ a, ha ⟩
  use a
  set p := (OrthoPoly s (n+2)) - (a • X : ℝ[X]) * (OrthoPoly s (n+1))
  have : p ∈ Submodule.span ℝ ((OrthoPoly s) '' (Finset.range (n + 2))) := by
    rw [OrthoPoly_span s (n+1)]
    exact Polynomial.mem_degreeLE.mpr ha

  have : ∃ coef : ℕ  → ℝ, p = ( ∑ i in Finset.range (n+2), (coef i) • (OrthoPoly s i) ) := by
    rw [mem_span_set] at this
    rcases this with ⟨C, ⟨hc1,hc2⟩⟩
    use C ∘ (λ x => OrthoPoly s x)
    rw [← hc2, Finsupp.sum]
    let hfinite := Fintype.ofFinite ↑(OrthoPoly s '' ↑(Finset.range (n + 2)))
    let D := (λ j => C j • j)
    have hsupport : D.support ⊆ C.support := by
      rw [Function.support]
      intro x my_hp
      simp only [mem_coe, Finsupp.mem_support_iff, ne_eq]
      exact (fun j a a_1 ↦ a ((fun x hp ↦ smul_eq_zero.mpr (Or.inl hp)) j a_1)) x my_hp
    let hc4 := Finite.Set.subset (C.support) hsupport
    let hfinite2 := Fintype.ofFinite D.support
    have : ∑ j in Set.toFinset D.support, D j = ∑ j in Set.toFinset (OrthoPoly s '' ↑(Finset.range (n + 2))), D j := by
      rw [←(finsum_eq_sum_of_support_toFinset_subset D hc4 (fun ⦃a⦄ a_1 ↦ (subset_toFinset.mpr hc1) ((toFinset_subset.mpr hsupport) a_1)))]
      exact (finsum_eq_sum_of_support_toFinset_subset D hc4 fun ⦃a⦄ a ↦ a).symm
    have : ∑ j in C.support, C j • j = ∑ j in toFinset (OrthoPoly s '' (Finset.range (n + 2))), C j • j := by
      rw [←this, ←(finsum_eq_sum_of_support_toFinset_subset D hc4 (toFinset_subset.mpr hsupport))]
      exact finsum_eq_sum_of_support_toFinset_subset D hc4 fun ⦃a⦄ a ↦ a
    rw [this]
    have : (natDegree ∘ OrthoPoly s).Injective := by
      rw [Function.Injective]
      intro a1 a2 hp
      have hq : natDegree (OrthoPoly s a1) = natDegree (OrthoPoly s a2) := hp
      rw [OrthoPoly_natdeg a1, OrthoPoly_natdeg a2] at hq
      exact hq
    have injective_sum (f : ℕ → MySpace s)(g : MySpace s → MySpace s)(A : Finset ℕ)(hp: Fintype (f '' A))(hf : f.Injective) :
      ∑ j in Set.toFinset (f '' A), g j = ∑ i in A, g (f i) := by
      simp only [toFinset_image, Finset.toFinset_coe]
      exact (Finset.sum_image (fun x _ y _ a ↦ hf a))
    rw [injective_sum (OrthoPoly s) (λ x => C x • x) (Finset.range (n + 2)) hfinite (Function.Injective.of_comp this)]
    exact rfl

  rcases this with ⟨ coef, hcoef ⟩
  have : OrthoPoly s (n + 2) - (a • X : ℝ[X]) * OrthoPoly s (n + 1) = OrthoPoly s (n + 2) + C (-a) * X * OrthoPoly s (n + 1) := by
    rw [Polynomial.smul_eq_C_mul a, Polynomial.C_neg]
    simp only [neg_mul]
    exact rfl
  have : p = (OrthoPoly s (n+2)) + (Polynomial.C (-a) * X) * (OrthoPoly s (n+1)) := this

  have p_1 : ∀ j ∈ Finset.range n , ⟪p, (OrthoPoly s j)⟫_ℝ = 0 := by
    rw [this]
    intro i hilessn
    rw [MySpace.InnerProductSpaceCore.add_left (OrthoPoly s (n + 2)) ((Polynomial.C (-a) * X) * OrthoPoly s (n + 1)) (OrthoPoly s i),
      OrthoPoly_orthogonal (Nat.ne_of_gt (Nat.le.step (Nat.le.step (List.mem_range.mp hilessn))))]
    have : -a • (X * OrthoPoly s (n + 1)) = C (-a) * X * OrthoPoly s (n + 1) := by
      simp only [neg_smul, map_neg, neg_mul, neg_inj]
      rw [(fun q ↦ Polynomial.smul_eq_C_mul a) (X * OrthoPoly s (n + 1))]
      exact Mathlib.Tactic.RingNF.mul_assoc_rev (C a) X (OrthoPoly s (n + 1))
    have ht : degree (OrthoPoly s i) < n := by
      rw [OrthoPoly_deg i]
      simp only [Nat.cast_lt]
      exact Finset.mem_range.mp hilessn
    have : ⟪C (-a) * X * OrthoPoly s (n + 1), OrthoPoly s i⟫_ℝ = 0 := by
      rw [←this, MySpace.InnerProductSpaceCore.smul_left (X * OrthoPoly s (n + 1)) (OrthoPoly s i) (-a)]
      have : degree (X * OrthoPoly s i) ≤ n := by
        rw [congrArg degree (mul_comm X (OrthoPoly s i)), Polynomial.degree_mul_X]
        exact Nat.WithBot.add_one_le_of_lt ht
      have : ⟪X * OrthoPoly s (n + 1), OrthoPoly s i⟫_ℝ = 0 := by
        rw [IntervalWithMeasure.xp_dot_q_eq_p_dot_xq (OrthoPoly s (n + 1)) (OrthoPoly s i)]
        exact OrthoPoly_orthogonal_low_deg this
      exact mul_eq_zero_of_right ((starRingEnd ℝ) (-a)) this
    exact Linarith.eq_of_eq_of_eq rfl this

  have p_2 : ∀ j ∈ Finset.range n, ∑ i in Finset.range (n + 2), ⟪coef i • OrthoPoly s i, OrthoPoly s j⟫_ℝ = 0 := by
    intro j hq
    have := p_1 j hq
    rw [hcoef, sum_inner (Finset.range (n + 2)) (λi => coef i • OrthoPoly s i) (OrthoPoly s j)] at this
    exact this
  have hcoefeq0 : ∀ i ∈ Finset.range n , coef i = 0 := by
    intro j hp
    have : ∀ i ∈ Finset.range (n+2), i ≠ j → ⟪coef i • OrthoPoly s i, OrthoPoly s j⟫_ℝ = 0 := by
      intro i _ inotj
      rw [MySpace.InnerProductSpaceCore.smul_left]
      exact mul_eq_zero_of_right ((starRingEnd ℝ) (coef i)) (OrthoPoly_orthogonal inotj)
    have hh : ⟪coef j • OrthoPoly s j, OrthoPoly s j⟫_ℝ = 0 := by
      rw [←(sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.le.step (Nat.le.step (List.mem_range.mp hp)))) this)]
      exact (p_2 j hp)
    rw [MySpace.InnerProductSpaceCore.smul_left, mul_eq_zero, or_iff_not_imp_right] at hh
    exact hh ((fun a a_1 ↦ a ((MySpace.InnerProductSpaceCore.definite (OrthoPoly s j)) a_1)) OrthoPoly_ne_zero)
  have : p = (coef n) • (OrthoPoly s n) + (coef (n+1)) • (OrthoPoly s (n+1)) := by
    rw [hcoef, Finset.sum_range_succ (fun x ↦ coef x • OrthoPoly s x) (n + 1)]
    simp only [add_left_inj]
    rw [Finset.sum_range_succ (fun x ↦ coef x • OrthoPoly s x) (n)]
    simp only [add_left_eq_self]
    exact Finset.sum_eq_zero (fun i hp ↦ smul_eq_zero.mpr (Or.inl (hcoefeq0 i hp)))
  have : p = C (coef (n + 1)) * (OrthoPoly s (n + 1)) + (coef n • OrthoPoly s n) := by
    rw [this, add_comm]
    simp only [add_left_inj]
    rw [Polynomial.smul_eq_C_mul]
  use (coef (n+1))
  use (coef n)
  rw [add_mul, add_assoc, ←this]
  simp only [p]
  rw [← add_sub_assoc, add_comm (a • X * OrthoPoly s (n+1)) _, add_sub_assoc, sub_self, add_zero]


-- distinct roots of an orthogonal polynomial that belong to the domain interval
def OrthoPoly_internal_roots (s : IntervalWithMeasure) (n : ℕ) : Finset ℝ :=
  Finset.filter (fun r => r ∈ Ioo s.a s.b) (OrthoPoly s n).roots.toFinset


theorem OrthoPoly_internal_roots_le (s : IntervalWithMeasure) (n : ℕ) : (OrthoPoly_internal_roots s n).card ≤ n := by
  unfold OrthoPoly_internal_roots
  have h : (OrthoPoly s n).roots.toFinset.card <= n := by
    have := Multiset.toFinset_card_le (OrthoPoly s n).roots
    apply LE.le.trans this
    have : natDegree (OrthoPoly s n) = n := OrthoPoly_natdeg n
    nth_rw 2 [← this]
    apply Polynomial.card_roots'
  have := Finset.filter_subset (fun r => r ∈ Ioo s.a s.b) (OrthoPoly s n).roots.toFinset
  have h2 := Finset.card_mono this
  apply LE.le.trans h2 h


-- the n-th orthogonal polynomial has n distinct roots in the internal part of the domain interval
theorem OrthoPoly_internal_roots_eq (s : IntervalWithMeasure) (n : ℕ) : (OrthoPoly_internal_roots s n).card = n := by
  have hor := LE.le.lt_or_eq (OrthoPoly_internal_roots_le s n)

  cases hor with
  | inl hlt =>
    exfalso
    unfold OrthoPoly_internal_roots at hlt
    let internal_roots : Multiset ℝ := Multiset.filter (fun r => r ∈ Ioo s.a s.b) (OrthoPoly s n).roots
    have his : internal_roots ≤ (OrthoPoly s n).roots := by
      simp only [Set.mem_Ioo, Multiset.filter_le]
    have hd := ((Multiset.prod_X_sub_C_dvd_iff_le_roots OrthoPoly_ne_zero) internal_roots).mpr his
    have ⟨r, hf⟩ := dvd_def.mpr hd

    have hnir : Multiset.filter (fun μ => μ ∈ Ioo s.a s.b) r.roots = 0 := by
      have hnir : OrthoPoly s n ≠ 0 := OrthoPoly_ne_zero
      rw [hf] at hnir
      have hnir := roots_mul hnir
      rw [← hf] at hnir
      simp only [roots_multiset_prod_X_sub_C] at hnir
      have := Multiset.filter_add (fun μ => μ ∈ Ioo s.a s.b) internal_roots r.roots
      rw [← hnir] at this
      rw [Multiset.filter_filter] at this
      simp only [and_self, self_eq_add_right] at this
      exact this

    have hrne0 : r ≠ 0 := by
      by_contra h
      rw [h] at hf
      simp only [mul_zero] at hf
      exact OrthoPoly_ne_zero hf

    have hrevne0 (x : ℝ) : x ∈ Ioo s.a s.b → r.eval x ≠ 0 := by
      intro hin
      by_contra h
      have : x ∈ Multiset.filter (fun μ ↦ μ ∈ Set.Ioo s.a s.b) (roots r) := by
        simp only [Multiset.mem_filter, mem_roots', ne_eq, IsRoot.def]
        constructor
        constructor
        exact hrne0
        exact h
        exact hin
      rw [hnir] at this
      contradiction

    have hrs : (∀ x : ℝ, x ∈ Ioo s.a s.b → r.eval x < 0) ∨ (∀ x : ℝ, x ∈ Ioo s.a s.b → r.eval x > 0) := by
      have ⟨y, hy⟩ := Set.nonempty_Ioo.mpr s.hab
      have hevy := hrevne0 y hy
      cases ne_iff_lt_or_gt.mp hevy with
      | inl hlt =>
        left
        intro x hx
        by_contra hevx
        simp only [not_lt] at hevx
        have : ContinuousOn r.eval (Set.Ioo s.a s.b) := Polynomial.continuousOn r
        have := ContinuousOn.surjOn_Icc this hy hx
        have h0 : 0 ∈ Set.Icc (eval y r) (eval x r) := by
          apply Set.mem_Icc.mpr
          constructor
          exact LE.le.ge (LT.lt.le hlt)
          exact hevx
        have ⟨z, ⟨hz, hevz⟩⟩ := (Set.mem_image r.eval (Set.Ioo s.a s.b) 0).mp (this h0)
        exact (hrevne0 z hz) hevz
      | inr hgt =>
        right
        intro x hx
        by_contra hevx
        simp only [not_lt] at hevx
        have : ContinuousOn r.eval (Set.Ioo s.a s.b) := Polynomial.continuousOn r
        have := ContinuousOn.surjOn_Icc this hx hy
        have h0 : 0 ∈ Set.Icc (eval x r) (eval y r) := by
          apply Set.mem_Icc.mpr
          constructor
          exact hevx
          exact LT.lt.le hgt
        have ⟨z, ⟨hz, hevz⟩⟩ := (Set.mem_image r.eval (Set.Ioo s.a s.b) 0).mp (this h0)
        exact (hrevne0 z hz) hevz

    let odd_roots : Finset ℝ :=
      Finset.filter (fun r => r ∈ Ioo s.a s.b) (
        Multiset.filter (fun r => (OrthoPoly s n).roots.count r % 2 = 1) (OrthoPoly s n).roots
      ).toFinset

    have hoc : odd_roots.card < n := by
      simp only [count_roots, Multiset.toFinset_filter]
      rw [Finset.filter_comm]
      apply lt_of_le_of_lt _ hlt
      apply Finset.card_mono
      simp only [Finset.le_eq_subset, Finset.filter_subset]

    let po : ℝ[X] := Finset.prod odd_roots (fun μ : ℝ => X - C μ)

    have hpod : po.degree < n := by
      rw [Polynomial.degree_prod]
      simp only [Polynomial.degree_X_sub_C]
      simp only [sum_const, nsmul_eq_mul,
        mul_one, Nat.cast_lt]
      exact hoc

    have hip0 : ⟪OrthoPoly s n, po⟫_ℝ = 0 := OrthoPoly_orthogonal_low_deg' hpod

    have hipn0 : ⟪OrthoPoly s n, po⟫_ℝ ≠ 0 := by
      have : (fun x => (↑(OrthoPoly s n) : ℝ[X]).eval x * po.eval x) =
          (fun x => (↑(OrthoPoly s n) * po).eval x) := by
        simp only [eval_mul]

      rw [MySpace.inner_def, IntervalWithMeasure.dot]

      have ⟨q, hq2⟩ : ∃q : ℝ[X], q*q = Multiset.prod (Multiset.map (fun a ↦ X - C a) internal_roots) * po := by
        simp only [count_roots, Multiset.toFinset_filter]
        rw [Finset.prod_eq_multiset_prod]
        rw [← Multiset.prod_add]
        rw [← Multiset.map_add]
        rw [Finset.filter_val]
        rw [← Multiset.filter_add]
        have ⟨q, hq2⟩ : ∃q : Multiset ℝ, (OrthoPoly s n).roots + (Finset.filter (fun r ↦
            rootMultiplicity r (OrthoPoly s n) % 2 = 1) (OrthoPoly s n).roots.toFinset).val = 2 • q:= by
          apply Multiset.exists_smul_of_dvd_count
          rw [Finset.filter_val]
          intro a ha
          have ha : a ∈ (OrthoPoly s n).roots := by
            have := Multiset.mem_add.mp ha
            cases this with
            | inl hl => exact hl
            | inr hr =>
              have := Multiset.mem_of_mem_filter hr
              simp only [Multiset.toFinset_val, Multiset.mem_dedup] at this
              exact this
          rw [Multiset.count_add]
          rw [Multiset.count_filter]
          simp only [count_roots, Multiset.toFinset_val, Multiset.nodup_dedup]
          rw [Multiset.count_dedup]
          simp only [ha]
          simp only [↓reduceIte]
          apply Nat.modEq_zero_iff_dvd.mp
          by_cases ho : (rootMultiplicity a (OrthoPoly s n) % 2 = 1)
          <;> simp only [Nat.mod_two_ne_one] at ho
          <;> simp only [ho]
          <;> simp
          <;> have := Nat.mod_modEq (rootMultiplicity a (OrthoPoly s n)) 2
          <;> rw [ho] at this
          have := Nat.ModEq.add_right 1 this
          simp only [Nat.reduceAdd] at this
          apply Nat.ModEq.trans (Nat.ModEq.symm this)
          apply Nat.modEq_zero_iff_dvd.mpr
          exact dvd_refl 2
          exact Nat.ModEq.symm this

        use Multiset.prod (Multiset.map (fun a ↦ X - C a) (Multiset.filter (fun r ↦ r ∈ Set.Ioo s.a s.b) q))
        rw [hq2]
        rw [← Multiset.prod_add, ← Multiset.map_add, ← Multiset.filter_add, two_smul]

      have hne0 : po * Multiset.prod (Multiset.map (fun a ↦ X - C a) internal_roots) ≠ 0 := by
        apply mul_ne_zero_iff.mpr
        constructor
        <;> apply Multiset.prod_ne_zero
        <;> rw [Multiset.mem_map, not_exists]
        <;> intro _
        <;> apply not_and.mpr
        <;> intro _
        <;> apply Polynomial.X_sub_C_ne_zero

      have hle : ∀x : ℝ, (Multiset.prod (Multiset.map (fun a ↦ X - C a) internal_roots) * po).eval x ≥ 0 := by
        intro x
        rw [← hq2]
        simp only [eval_mul, ge_iff_le]
        rw [← sq]
        apply sq_nonneg (q.eval x)

      rw [hf, mul_comm, ← mul_assoc]
      cases hrs with
      | inl hneg =>
        apply neg_ne_zero.mp
        apply ne_of_gt
        rw [← intervalIntegral.integral_neg]

        have : ∫ (x : ℝ) in s.a..s.b, -eval x
                (po * Multiset.prod (Multiset.map (fun a ↦ X - C a) internal_roots) * r) ∂s.μ =
               ∫ (x : ℝ) in s.a..s.b, eval x
                (po * Multiset.prod (Multiset.map (fun a ↦ X - C a) internal_roots) * (-r)) ∂s.μ := by
          apply intervalIntegral.integral_congr
          rw [Set.EqOn]
          intro x _
          rw [← Polynomial.eval_neg]
          simp only [eval_neg, eval_mul, mul_neg]

        rw [this]
        apply MySpace.integral_pos_of_pos
        apply mul_ne_zero_iff.mpr ⟨hne0, neg_ne_zero.mpr hrne0⟩
        intro x hx
        rw [eval_mul]
        apply mul_nonneg
        rw [mul_comm]
        exact GE.ge.le (hle x)
        rw [Polynomial.eval_neg]
        rw [le_neg]
        rw [neg_zero]
        exact LT.lt.le (hneg x hx)
      | inr hpos =>
        apply ne_of_gt
        apply MySpace.integral_pos_of_pos
        apply mul_ne_zero_iff.mpr ⟨hne0, hrne0⟩
        intro x hx
        rw [eval_mul]
        apply mul_nonneg
        rw [mul_comm]
        exact GE.ge.le (hle x)
        exact LT.lt.le (hpos x hx)

    exact hipn0 hip0
  | inr heq =>
    exact heq

theorem OrthoPoly_factorization (s : IntervalWithMeasure) (n : ℕ) : ∃a : ℝ, a ≠ 0 ∧
    (OrthoPoly s n) = a • Finset.prod (OrthoPoly_internal_roots s n) (fun μ ↦ (X - C μ : ℝ[X])) := by
  let internal_roots := OrthoPoly_internal_roots s n
  have his : internal_roots.val ≤ (OrthoPoly s n).roots := by
    simp only
    unfold OrthoPoly_internal_roots
    simp only [filter_val, Multiset.toFinset_val]
    apply le_trans _ (Multiset.dedup_le (OrthoPoly s n).roots)
    apply Multiset.filter_le

  have hd := ((Multiset.prod_X_sub_C_dvd_iff_le_roots OrthoPoly_ne_zero) internal_roots.val).mpr his
  have ⟨r, hf⟩ := dvd_def.mpr hd
  simp only [prod_map_val] at hf
  rw [mul_comm] at hf

  have hrd : r.degree = 0 := by
    have : (OrthoPoly s n).degree = n := OrthoPoly_deg n
    rw [hf] at this
    rw [Polynomial.degree_mul] at this
    rw [Polynomial.degree_prod] at this
    simp only [degree_X_sub_C, sum_const, nsmul_eq_mul, mul_one] at this
    rw [OrthoPoly_internal_roots_eq] at this
    nth_rewrite 2 [← zero_add (↑n : WithBot ℕ)] at this
    apply WithBot.add_right_cancel _ this
    simp only [ne_eq, WithBot.nat_ne_bot, not_false_eq_true]

  have := Polynomial.degree_le_zero_iff.mp (Eq.le hrd)
  use coeff r 0
  constructor
  by_contra h
  rw [h] at this
  simp only [map_zero] at this
  rw [this, degree_zero] at hrd
  contradiction
  rw [Polynomial.smul_eq_C_mul, ← this]
  exact hf


-- a quadrature formula : finitely many nodes and the corresponding weights
structure Quadrature where
  nodes : Finset ℝ
  weights : nodes → ℝ


def Quadrature.card (q : Quadrature) : ℕ :=
  q.nodes.card


theorem Quadrature.eq {a b : Quadrature} (hn : a.nodes = b.nodes) (hw : HEq a.weights b.weights) : a = b := by
  cases a with
  | mk na wa =>
    cases b with
    | mk nb wb =>
      simp only [mk.injEq]
      constructor
      exact hn
      exact hw


-- numerical integration with the quadrature formula
def Quadrature.nint (q : Quadrature) (p : ℝ[X]) :=
  ∑ n : q.nodes, (q.weights n) * p.eval ↑n


-- the notion of exactness: a quadrature formula is exact of degree n if it integrates
-- all polynomials of degree ≤ n exactly
def Quadrature.exact (q : Quadrature) (s : IntervalWithMeasure) (n : ℕ) :=
  ∀p : ℝ[X], p.degree ≤ n → q.nint p = s.int p


-- an interpolatory quadrature formula: a quadrature formula that approximates the integral
-- of a polynomial with the exact integral of its Lagrange interpolant on the quadrature nodes
def Quadrature.interp (s : IntervalWithMeasure) (F : Finset ℝ) : Quadrature where
  nodes := F
  weights : F -> ℝ := fun i => s.int (Lagrange.basis F id i)


theorem Quadrature.interp_card (s : IntervalWithMeasure) (F : Finset ℝ) :
    (Quadrature.interp s F).card = F.card := by
  unfold interp
  unfold card
  simp only


theorem Quadrature.interp_nint (s : IntervalWithMeasure) (F : Finset ℝ) (p : ℝ[X]) :
    (Quadrature.interp s F).nint p = s.int (Lagrange.interpolate F id p.eval) := by
  unfold nint
  unfold interp
  simp only [Lagrange.interpolate_apply]
  unfold IntervalWithMeasure.int
  simp only [Polynomial.eval_finset_sum]
  rw [intervalIntegral.integral_finset_sum]
  simp only [eval_mul]
  simp only [eval_C, intervalIntegral.integral_const_mul]
  simp only [mul_comm (∫ (x_1 : ℝ) in s.a..s.b, eval x_1 (Lagrange.basis F id _) ∂s.μ)]
  let f : ℝ -> ℝ := fun x => eval (↑x) p * ∫ (x_1 : ℝ) in s.a..s.b, eval x_1 (Lagrange.basis F id ↑x) ∂s.μ
  rw [Finset.sum_coe_sort F f]
  intro i _
  apply s.hpi


-- an interpolatory quadrature formula with n nodes has exactness at least n-1
theorem Quadrature.interp_exact (s : IntervalWithMeasure) (F : Finset ℝ) (hpos : 0 < F.card) :
    Quadrature.exact (Quadrature.interp s F) s (F.card - 1) := by
  unfold exact
  intro p hdp

  have hpos' : 1 ≤ F.card := by
    by_contra h
    simp only [not_le, Nat.lt_one_iff] at h
    exact (LT.lt.ne hpos) (Eq.symm h)
  have : p.degree < F.card := by
    by_contra h
    simp at h
    have := le_trans h hdp
    simp only [Nat.cast_withBot] at this
    have := WithBot.coe_le_coe.mp this
    have := add_le_add_right this 1
    rw [Nat.sub_add_cancel hpos'] at this
    have := add_lt_add_of_le_of_lt this zero_lt_one
    rw [add_zero] at this
    simp only [lt_self_iff_false] at this
  have hinj : InjOn id F.toSet := by
    apply Function.Injective.injOn
    unfold Function.Injective
    simp only [id_eq, imp_self, forall_const]

  rw [Quadrature.interp_nint]
  nth_rewrite 2 [Lagrange.eq_interpolate hinj this]
  simp only [id_eq]


-- a quadrature formula on n nodes with exactnes at least n-1 is interpolatory
theorem Quadrature.is_interp (q : Quadrature) (s : IntervalWithMeasure) (hex : q.exact s (q.card-1)) :
    ∃ F : Finset ℝ, q = Quadrature.interp s F := by
  use q.nodes
  unfold interp
  apply Quadrature.eq
  simp only
  simp only [heq_eq_eq]
  apply @_root_.funext
  intro x
  let p := (Lagrange.basis q.nodes id ↑x)
  have hinj := Function.Injective.injOn Function.injective_id q.nodes.toSet
  have := Eq.le (Lagrange.degree_basis hinj x.property)
  unfold exact at hex
  have := hex p this
  unfold nint at this
  simp only at this
  have hev (x y : q.nodes) : eval ↑y (Lagrange.basis q.nodes id ↑x) = if x = y then 1 else 0 := by
    by_cases h : x = y
    simp [h]
    apply Lagrange.eval_basis_self hinj y.property
    simp [h]
    have h : ¬x.val = y.val := by
      by_contra he
      exact h (Subtype.eq he)
    have : eval (id ↑y) (Lagrange.basis q.nodes id ↑x) = 0 := Lagrange.eval_basis_of_ne h y.property
    rw [id_eq] at this
    exact this
  simp_rw [hev] at this
  simp only [univ_eq_attach, mul_ite, mul_one, mul_zero, sum_ite_eq, Finset.mem_attach, ↓reduceIte] at this
  exact this

-- a quadrature formula on n nodes with exactness at least 2n - 2 has positive weights
theorem Quadrature.pos_weights (q : Quadrature) (s : IntervalWithMeasure) (hex : q.exact s (2*(q.card - 1))) :
    ∀ x : q.nodes, q.weights x > 0 := by
  intro x

  let p := Finset.prod (q.nodes.erase x) (fun n => (X - C n)^2)
  have hdp : p.degree = ↑((2 : ℕ)*(q.card-1 : ℕ)) := by
    rw [degree_prod]
    simp only [degree_pow, degree_X_sub_C, nsmul_eq_mul, Nat.cast_ofNat, mul_one, sum_const]
    unfold card
    rw [mul_comm]
    simp only [coe_mem, card_erase_of_mem, Nat.cast_mul, Nat.cast_ofNat]
  have hex := hex p (Eq.le hdp)
  have (x : ℝ) : p.eval x ≥ 0 := by
    rw [eval_prod]
    apply Finset.prod_nonneg
    intro i _
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply sq_nonneg
  have : ∀x : ℝ, x ∈ Ioo s.a s.b → p.eval x ≥ 0 := by
    intro x _
    exact this x
  have hpne0 : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_sub_C_ne_zero]
  have hpos := MySpace.integral_pos_of_pos hpne0 this
  unfold IntervalWithMeasure.int at hex
  rw [← hex] at hpos
  unfold nint at hpos
  have hif : (fun y : q.nodes => q.weights y * p.eval (↑y)) =
      (fun y : q.nodes => if x = y then q.weights y * p.eval ↑x else 0) := by
    apply @_root_.funext
    intro y
    by_cases h : x = y
    rw [← h]
    simp only [↓reduceIte]
    simp only [h, ↓reduceIte, mul_eq_zero]
    right
    have hy : ↑y ∈ q.nodes.erase ↑x := by
      apply Finset.mem_erase.mpr
      constructor
      by_contra he
      exact h (Subtype.eq (Eq.symm he))
      exact y.property
    have h0 : eval (↑y : ℝ) ((X - C (↑y : ℝ)) ^ 2) = 0 := by
      simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
    rw [eval_prod]
    apply Finset.prod_eq_zero hy h0
  rw [hif] at hpos
  rw [sum_ite_eq] at hpos
  simp only [Finset.mem_univ, ↓reduceIte, gt_iff_lt] at hpos
  have : p.eval ↑x > 0 := by
    simp only
    rw [eval_prod]
    apply Finset.prod_pos
    intro y hy
    have ⟨hne, _⟩ := Finset.mem_erase.mp hy
    simp only [eval_pow, eval_sub, eval_X, eval_C, gt_iff_lt]
    apply sq_pos_of_ne_zero
    apply sub_ne_zero.mpr (Ne.symm hne)
  simp [this] at hpos
  exact hpos


-- a Gaussian quadrature: an interpolatory quadrature formula with nodes in the roots of the n-th
-- orthogonal polynomial
theorem Quadrature.Gaussian (s : IntervalWithMeasure) (n : ℕ) : Quadrature :=
  Quadrature.interp s (OrthoPoly_internal_roots s n)


theorem Quadrature.Gaussian_card (s : IntervalWithMeasure) (n : ℕ) : (Quadrature.Gaussian s n).card = n := by
  unfold card
  unfold Gaussian
  unfold interp
  simp only
  exact OrthoPoly_internal_roots_eq s n


-- a Gaussian quadrature formula on n nodes has exactness 2n - 1
theorem Quadrature.Gaussian_exact (s : IntervalWithMeasure) (n : ℕ) (hpos : 0 < n) :
    Quadrature.exact (Quadrature.Gaussian s n) s (2*n - 1) := by
  rw [exact]
  intro p hpdeg
  let a : ℝ[X] := C (Polynomial.leadingCoeff (OrthoPoly s n))⁻¹ * (OrthoPoly s n)
  have hmonic: Polynomial.Monic a := by
    simp only
    rw [mul_comm]
    apply Polynomial.monic_mul_leadingCoeff_inv
    apply OrthoPoly_ne_zero
  have hdiv:= (Polynomial.modByMonic_add_div p hmonic)
  have hcoeffne0 : (leadingCoeff (OrthoPoly s n))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, leadingCoeff_eq_zero]
    exact OrthoPoly_ne_zero
  have hadeg : degree a = n := by
    simp only
    rw [degree_mul]
    simp [OrthoPoly_deg, Polynomial.degree_C hcoeffne0]

  have : degree (p/ₘa) ≤ ↑(n-1) := by
    have : p/ₘa * a = (p - p%ₘa):= by
      nth_rw 2 [← hdiv]
      rw [add_comm, add_sub_cancel, mul_comm]
    have somma : degree (p/ₘa) + degree a = degree (p - p%ₘa) := by
      have : degree (p/ₘa * a) = degree (p - p%ₘa) := congrArg degree this
      rw [Polynomial.degree_mul] at this
      exact this
    have lemax: degree (p - p%ₘa) ≤ max (degree p) (degree (p %ₘ a)) :=
      Polynomial.degree_sub_le p (p %ₘ a)
    rw [←somma] at lemax
    have :  (degree (p %ₘ a)) ≤ (degree p) := by
      by_cases h : degree a ≤ degree p
      have := Polynomial.degree_modByMonic_le p hmonic
      exact LE.le.trans this h
      have : p %ₘ a = p := (Polynomial.modByMonic_eq_self_iff hmonic).mpr (not_le.mp h)
      rw [this]
    have : max (degree p) (degree (p %ₘ a)) = (degree p) :=
      max_eq_iff.mpr (Or.inl { left := rfl, right := this })
    rw [this, hadeg] at lemax
    have hqdeg : degree (p /ₘ a) + ↑n ≤ ↑(2 * n - 1) := LE.le.trans lemax hpdeg
    rw [←Nat.sub_one_add_self] at hqdeg
    have : degree (p /ₘ a) ≤ ↑(n - 1) := by
      apply ((WithBot.add_le_add_iff_right (WithBot.nat_ne_bot n)).mp)
      exact hqdeg
    exact this

  have hdegdiv : degree (p/ₘa) < ↑n := natbot_lt_of_le_sub_one hpos this

  have hdegmod : degree (p%ₘa) < n := by
    rw [←hadeg]
    apply Polynomial.degree_modByMonic_lt
    simp only
    apply hmonic

  have : nint (Gaussian s n) p = nint (Gaussian s n) (p %ₘ a) := by
    unfold nint Gaussian
    nth_rw 1 [←hdiv]
    simp only
    apply Finset.sum_congr
    simp only
    intro x _
    simp only [eval_add, eval_mul, mul_eq_mul_left_iff, add_right_eq_self, mul_eq_zero]
    left
    left
    have : Polynomial.IsRoot (OrthoPoly s n) ↑x := by
      have h := x.property
      unfold interp at h
      simp only at h
      unfold OrthoPoly_internal_roots at h
      have := Finset.mem_of_mem_filter _ h
      have := Multiset.mem_toFinset.mp this
      apply Polynomial.isRoot_of_mem_roots this
    have := Polynomial.IsRoot.eq_zero this
    rw [eval_mul]
    simp only [this, mul_zero]
  rw [this]
  have : s.int p = s.int (p %ₘ a) + s.int (a * (p /ₘ a)) := by
    nth_rw 1 [← hdiv]
    repeat rw [IntervalWithMeasure.int, IntervalWithMeasure.int, IntervalWithMeasure.int]
    simp only [eval_add]
    rw [intervalIntegral.integral_add]
    all_goals apply s.hpi
  rw [this]
  have : s.int (a * (p /ₘ a)) = 0 := by
    change IntervalWithMeasure.dot s a (p /ₘ a) = 0
    change IntervalWithMeasure.dot s (C (Polynomial.leadingCoeff (OrthoPoly s n))⁻¹ * (OrthoPoly s n)) (p /ₘ a) = 0
    unfold IntervalWithMeasure.dot
    rw [mul_assoc, mul_comm, mul_assoc]
    change IntervalWithMeasure.dot s (OrthoPoly s n) (p /ₘ a * C (leadingCoeff (OrthoPoly s n))⁻¹)  = 0
    apply OrthoPoly_orthogonal_low_deg'
    rw [degree_mul,  Polynomial.degree_C hcoeffne0, add_zero]
    exact hdegdiv
  rw [this, add_zero]
  unfold Gaussian
  apply interp_exact s
  <;> rw [OrthoPoly_internal_roots_eq]
  exact hpos

  exact natbot_le_sub_one_of_lt hdegmod


-- there are no quadrature formulas on n nodes with exactness 2n
theorem Quadrature.max_exactness (q : Quadrature) (s : IntervalWithMeasure) : ¬ q.exact s (2*q.card) := by
  unfold exact
  simp only [Nat.cast_mul, Nat.cast_ofNat, not_forall, exists_prop]
  let p := Finset.prod q.nodes (fun n => (X - C n)^2)
  use p
  constructor
  apply Eq.le
  rw [degree_prod]
  simp only [degree_pow, degree_X_sub_C, nsmul_eq_mul, Nat.cast_ofNat, mul_one, sum_const]
  unfold card
  rw [mul_comm]
  have (x : ℝ) : p.eval x ≥ 0 := by
    rw [eval_prod]
    apply Finset.prod_nonneg
    intro i _
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply sq_nonneg
  have : ∀x : ℝ, x ∈ Ioo s.a s.b → p.eval x ≥ 0 := by
    intro x _
    exact this x
  have hpne0 : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_sub_C_ne_zero]
  have hpos := MySpace.integral_pos_of_pos hpne0 this

  have h0 : q.nint p = 0 := by
    unfold nint
    have (x : q.nodes) : p.eval ↑x = 0 := by
      have ⟨a, ha⟩ := x
      simp only
      rw [eval_prod]
      apply Finset.prod_eq_zero ha
      simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
    simp only [univ_eq_attach, this, mul_zero, sum_const_zero]

  rw [h0]
  unfold IntervalWithMeasure.int
  exact LT.lt.ne hpos
