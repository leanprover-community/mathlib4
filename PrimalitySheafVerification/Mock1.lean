/-
================================================================================
  Mock1.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "Entropy–Growth and Sheaf Stability for Mock Partial Theta
                     and Jacobi Objects".

  Kernel-checked against Mathlib; NO `sorry`, NO new global `axiom`.

  ------------------------------------------------------------------------------
  SCOPE.  This paper is overwhelmingly ANALYTIC (mock theta functions, harmonic
  Maass forms, completion/shadow, Rademacher expansion, Kloosterman sums,
  Dirichlet twists, p-adic interpolation, archimedean entropy–growth).  None of
  that machinery is in Mathlib, so it is honestly OMITTED (not stubbed).  What
  IS elementary and verifiable is the *embedded SPT / sheaf-stability block* the
  paper reuses (Lemma 2 "Gate and equalizer stability under CRT", Prop I.3
  "p-adic gluing", Thm I.8 base-change stability) — the same equalizer–Tor–CRT
  calculus as the spt-series.  That block is verified here in full.

  ------------------------------------------------------------------------------
  §-by-§ MAP (verifiable block ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Lem 2 (gate/equalizer stability under CRT)  ker = (M)∩(pᵏ) = (lcm), Tor₁≅ℤ/gcd
                ↦ kernel_mem_iff_lcm, card_ker_mulLeft, obstructionFree_iff_*     PROVED
    Prop I.3 (p-adic gluing)  span{M} ⊔ span{pᵏ} = (gcd);  glue ⇔ gcd ∣ (a-b)
                ↦ span_sup_eq_gcd, crt_solvable_iff                              PROVED
    (IC / primewise)  |Tor| = ∏ qᵃ = exp(IC), monotone/additive
                ↦ gcd_eq_prod_primeFactors, card_Tor_eq_exp_IC                   PROVED
    Thm I.8 (base-change stability)  per-prime exponent invariant
                ↦ thickness_stable_coprime                                       PROVED

  OMITTED (deep analysis, absent from Mathlib): Completion law (Thm A / 3.2),
  Shadow determination (Prop 2, Prop A.1, Lem C.1), S-transport (Lem 1), modular
  completion & growth (Prop 3), Rademacher/unfolding (Lem 5–9, Prop I.1/J.1),
  Kloosterman control (Lem 7), Dirichlet twist (Lem 6), root-number filter
  (Lem 8), Euler decomposition (Prop K.1, Thm K.2), p-adic interpolation /
  analytic range (Prop I.3/I.4/I.5, Thm I.6), entropy–growth asymptotics
  `log|a(n)| = α√n - ½log n + β + o(1)` (Thm I.A), β-kernel `erfc`.
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD

open scoped BigOperators

namespace Mock1

/-! ## §A — Embedded SPT block: equalizer kernel = (M)∩(N) = (lcm) (Lemma 2). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-! ## §B — p-adic gluing (Prop I.3): the ideal SUP is `(gcd)` (dual to ker = lcm). -/

/-- **Prop I.3 (p-adic gluing).** The sum of the two principal ideals is generated
    by the gcd — complementary to the equalizer kernel `(M)∩(N) = (lcm)`. -/
theorem span_sup_eq_gcd (M N : ℤ) :
    Ideal.span {M} ⊔ Ideal.span {N} = Ideal.span {gcd M N} := by
  rw [span_gcd, Ideal.span_insert]

/-- **Prop I.3 (gluing criterion).** Local witnesses `a, b` glue iff `gcd ∣ (a-b)`. -/
theorem crt_solvable_iff (M N a b : ℤ) :
    (∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b)) ↔ (↑(Int.gcd M N) : ℤ) ∣ (a - b) := by
  constructor
  · rintro ⟨x, hMa, hNb⟩
    have h1 : (↑(Int.gcd M N) : ℤ) ∣ (x - a) := (Int.gcd_dvd_left M N).trans hMa
    have h2 : (↑(Int.gcd M N) : ℤ) ∣ (x - b) := (Int.gcd_dvd_right M N).trans hNb
    simpa [sub_sub_sub_cancel_right] using dvd_sub h2 h1
  · rintro ⟨w, hw⟩
    have hbez : (↑(Int.gcd M N) : ℤ) = M * Int.gcdA M N + N * Int.gcdB M N := Int.gcd_eq_gcd_ab M N
    have hab : a - b = (M * Int.gcdA M N + N * Int.gcdB M N) * w := by rw [← hbez, hw]
    refine ⟨a - M * Int.gcdA M N * w, ⟨-(Int.gcdA M N) * w, by ring⟩, ⟨Int.gcdB M N * w, ?_⟩⟩
    have hrw : a - M * Int.gcdA M N * w - b = (a - b) - M * Int.gcdA M N * w := by ring
    rw [hrw, hab]; ring

noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

/-! ## §C — Derived (Tor) readout and obstruction-free criterion (Lemma 2). -/

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

theorem range_mulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    (AddMonoidHom.mulLeft (M : ZMod N)).range = AddSubgroup.zmultiples (M : ZMod N) := by
  ext y
  rw [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x.val : ℤ), ?_⟩
    rw [zsmul_eq_mul]; push_cast; rw [ZMod.natCast_zmod_val]; simp [mul_comm]
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ZMod N), by rw [zsmul_eq_mul]; simp [mul_comm]⟩

/-- `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
theorem card_ker_mulLeft (N : ℕ) [NeZero N] (M : ℕ) :
    Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker = Nat.gcd N M := by
  have hG : Nat.card (ZMod N) = N := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hr : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).range = N / N.gcd M := by
    rw [range_mulLeft, Nat.card_zmultiples, ZMod.addOrderOf_coe M (NeZero.ne N)]
  have hmul : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker
              * Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).range = N := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, hG]
  rw [hr] at hmul
  have hg : 0 < N.gcd M := Nat.gcd_pos_of_pos_left M (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdvd : N.gcd M ∣ N := Nat.gcd_dvd_left N M
  have hdpos : 0 < N / N.gcd M :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hg
  have hfin : Nat.card (AddMonoidHom.mulLeft (M : ZMod N)).ker * (N / N.gcd M)
        = N.gcd M * (N / N.gcd M) := by rw [hmul, Nat.mul_div_cancel' hdvd]
  exact Nat.eq_of_mul_eq_mul_right hdpos hfin

theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §D — Primewise decomposition, indicator complexity, base-change stability. -/

theorem gcd_eq_prod_primeFactors {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    Nat.gcd M N = ∏ q ∈ N.primeFactors, q ^ min (M.factorization q) (N.factorization q) := by
  have hg : Nat.gcd M N ≠ 0 := Nat.gcd_ne_zero_left hM
  have hsub : (Nat.gcd M N).primeFactors ⊆ N.primeFactors :=
    Nat.primeFactors_mono (Nat.gcd_dvd_right M N) hN
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hg]
  rw [Finsupp.prod, Nat.support_factorization]
  rw [Finset.prod_congr rfl (fun q _ => by rw [factorization_gcd_apply hM hN])]
  refine Finset.prod_subset hsub ?_
  intro q hqN hqg
  have h0 : min (M.factorization q) (N.factorization q) = 0 := by
    rw [← factorization_gcd_apply hM hN, Nat.factorization_eq_zero_iff]
    exact Or.inr (Or.inl (fun hdvd =>
      hqg (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hqN).1, hdvd, hg⟩)))
  rw [h0, pow_zero]

noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **Thm I.8 (base-change stability).** The per-prime obstruction exponent is
    invariant under enlarging `N` by a factor coprime to `q`. -/
theorem thickness_stable_coprime {M N c : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0)
    {q : ℕ} (hq : ¬ q ∣ c) :
    (Nat.gcd M (N * c)).factorization q = (Nat.gcd M N).factorization q := by
  rw [factorization_gcd_apply hM (Nat.mul_ne_zero hN hc),
      factorization_gcd_apply hM hN, Nat.factorization_mul hN hc]
  have hcq : c.factorization q = 0 :=
    (Nat.factorization_eq_zero_iff c q).mpr (Or.inr (Or.inl hq))
  simp [Finsupp.add_apply, hcq]

/-! ## Examples. -/

section Examples
example : Nat.gcd 12 9 = 3 := by norm_num
example : Nat.lcm 6 9 = 18 := by norm_num
/-- p-adic gluing: residues `a=1, b=0` over `(6,9)` do NOT glue (`gcd 3 ∤ 1`). -/
example : ¬ (∃ x : ℤ, (6:ℤ) ∣ (x - 1) ∧ (9:ℤ) ∣ (x - 0)) := by
  rw [crt_solvable_iff]; decide
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms kernel_mem_iff_lcm
#print axioms span_sup_eq_gcd
#print axioms crt_solvable_iff
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms card_ker_mulLeft
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms thickness_stable_coprime
end AxiomAudit

end Mock1
