/-
================================================================================
  Spt3.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  Every theorem is machine-checked by the Lean 4 kernel against Mathlib, with NO
  `sorry` and NO new global `axiom`.  The `AxiomAudit` section runs `#print axioms`
  on each result: they depend only on `[propext, Classical.choice, Quot.sound]`
  (never `sorryAx`); the conditional results (§G) carry their assumptions as
  EXPLICIT HYPOTHESES, visible in the signature.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    §2.2/3.3/3.5, Lem 5, Prop(2171)  kernel = (M)∩(N) = (lcm)
                                      ↦ kernel_mem_iff_lcm, kernel_ideal_inter PROVED
    §3.4(3) Zero-Class rule (CORRECTED) T∈(M)∩(N) ⇔ lcm∣T ⇔ vp≥max
                                      ↦ zeroClass_mem_iff_lcm, lcm_dvd_iff_max  PROVED
    §3.4/3.5, Prop 7  thickness (CORRECTED)  gcd→min, lcm→max
                                      ↦ factorization_gcd_apply / lcm_apply     PROVED
    Lem 6/12, Cor(2721)  Tor₁(ℤ/M,ℤ/pᵏ) ≅ ℤ/gcd, order = gcd
                                      ↦ card_ker_mulLeft, commonResidueFiber_card,
                                        obstructionFree_iff_card/coprime         PROVED
    Lem A/10/11, Thm 14, Rem 19  CRT split, primewise, |Tor| = ∏ qᵃ
                                      ↦ crt_iso, gcd_eq_prod_primeFactors        PROVED
    §3.4(7), Cor(2777), Lem 15/16  IC = ∑ min·log q, |Tor| = exp(IC), mono, add
                                      ↦ IC, card_Tor_eq_exp_IC, IC_mono,
                                        IC_coprime_add                           PROVED
    Prop 8/Cor 9  stability under CRT refinement
                                      ↦ thickness_stable_coprime                PROVED
    Thm 20, Cor(D(∆))  derived equalizer = cotangent test (CONDITIONAL)
                                      ↦ derived_equalizer_tfae                  PROVED (cond.)
    Thm 1/18  X prime ⇔ ∃ global section
                                      ↦ overlap_glue_iff_lcm (gluing core only)  PARTIAL

  ⚠ CORRECTIONS found while formalizing:
    • §3.4(3) "Zero-Class Decision Rule" states T ∈ (M)∩(pᵏ) ⇔ gcd(M,pᵏ)∣T ⇔
      vp(T) ≥ min{vp M, k}.  This is FALSE: (M)∩(pᵏ) = (lcm), so the correct rule
      is `lcm∣T ⇔ vp(T) ≥ max{vp M, k}`.  The `gcd`/`min` belongs to the common
      residue fiber `ℤ/gcd` (and Tor₁), NOT to the intersection.  We prove the
      corrected rule (`zeroClass_mem_iff_lcm`, `lcm_dvd_iff_max`) and the gcd/min
      facts separately so the distinction is explicit.
    • The "localized thickness `((M)∩(pᵏ))_(p) = p^{min}`" (eq. (4), §3.5, Prop 7)
      is the same conflation: the intersection localises to `p^{max}`; `min` is
      the gcd/Tor thickness.

  HONEST SCOPE of Theorem 18 (X prime ⇔ ∃ global section):  this is the
  framework's SOUNDNESS + COMPLETENESS claim.  Its `(⇐)` direction asserts that
  the four layers (incl. the EC/AKS regularity layer) exclude every composite —
  a deep claim that is NOT an elementary arithmetic fact and that would be
  CIRCULAR to assume as a hypothesis.  So we do NOT certify "prime ⇔ certificate".
  We formalize only the gluing MECHANISM the proof uses (overlap equalizer = lcm,
  CRT), which is genuine.  Likewise the p-adic log bridge and the EC/étale/motivic
  detectors are omitted (Mathlib lacks the infrastructure).
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators

namespace Spt3

/-! ## §A — Equalizer kernel = ideal intersection = lcm (Lem 5, §3.3/3.5). -/

/-- `ker(ℤ → ℤ/M × ℤ/N) = (M)∩(N) = (lcm)` (membership form). -/
theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form. -/
theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-! ## §B — Zero-Class rule (CORRECTED) and thickness (Prop 7, §3.4/3.5).

The paper's §3.4(3) attaches `gcd`/`min` to the intersection; the truth is
`lcm`/`max`.  Both are proved here so the distinction is explicit. -/

/-- **Zero-Class rule, CORRECTED.** `T ∈ (M)∩(N) ↔ lcm M N ∣ T` (not `gcd ∣ T`). -/
theorem zeroClass_mem_iff_lcm (M N T : ℤ) :
    (T ∈ Ideal.span {M} ⊓ Ideal.span {N}) ↔ lcm M N ∣ T := by
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- `v_p(gcd M N) = min(v_p M, v_p N)` — the common-residue-fiber / Tor thickness. -/
theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

/-- `v_p(lcm M N) = max(v_p M, v_p N)` — the *intersection* thickness (CORRECTED). -/
theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-- The valuation form of the corrected Zero-Class rule:
    `lcm M N ∣ T ↔ ∀ p, max(v_p M, v_p N) ≤ v_p T`. -/
theorem lcm_dvd_iff_max {M N T : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hT : T ≠ 0) :
    Nat.lcm M N ∣ T ↔ ∀ p, max (M.factorization p) (N.factorization p) ≤ T.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (Nat.lcm_ne_zero hM hN) hT]
  constructor
  · intro h p; have := h p; rwa [Nat.factorization_lcm hM hN, Finsupp.sup_apply] at this
  · intro h p; rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]; exact h p

/-- The gcd/min fact, kept separate: `gcd M N ∣ T ↔ ∀ p, min(v_p M, v_p N) ≤ v_p T`. -/
theorem gcd_dvd_iff_min {M N T : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hT : T ≠ 0) :
    Nat.gcd M N ∣ T ↔ ∀ p, min (M.factorization p) (N.factorization p) ≤ T.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hM) hT]
  constructor
  · intro h p; have := h p; rwa [Nat.factorization_gcd hM hN, Finsupp.inf_apply] at this
  · intro h p; rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]; exact h p

/-! ## §C — Derived/Tor readout (Lem 6/12, Cor 2721): Tor₁ ≅ ℤ/gcd. -/

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

/-- **Lemma 6/12.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = |ker(×M on ℤ/N)| = gcd(N, M)`. -/
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

/-- Order of the common residue fiber `ℤ/gcd`. -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] : Fintype.card (ZMod g) = g := ZMod.card g

/-- **Cor 2721.** Obstruction-free ⟺ Tor vanishes (fiber is a point). -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §D — CRT / primewise decomposition (Lem A/10/11, Thm 14). -/

/-- **Lemma A / 10 (CRT split).** `ℤ/(ab) ≅ ℤ/a × ℤ/b` for coprime `a, b`. -/
noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

/-- **Theorem 14.** Primewise factorisation of the obstruction `gcd(M, N)`. -/
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

/-! ## §E — Indicator complexity (§3.4(7), Cor 2777, Lem 15/16). -/

/-- **Definition (IC).** `IC(M;N) = ∑_{q∣N} min(v_q M, v_q N)·log q`. -/
noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

/-- **Cor 2777.** `|Tor₁| = gcd(M,N) = exp(IC(M;N))`. -/
theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **Lemma 15 (monotonicity).** If `N' ∣ N` then `IC(M;N') ≤ IC(M;N)`. -/
theorem IC_mono {M N' N : ℕ} (hN : N ≠ 0) (hdvd : N' ∣ N) : IC M N' ≤ IC M N := by
  have hN' : N' ≠ 0 := fun h => hN (by simpa [h] using hdvd)
  have hle : N'.factorization ≤ N.factorization := (Nat.factorization_le_iff_dvd hN' hN).mpr hdvd
  calc IC M N'
      ≤ ∑ q ∈ N'.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        apply mul_le_mul_of_nonneg_right _ hlog
        exact min_le_min le_rfl (by exact_mod_cast hle q)
    _ ≤ IC M N := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hdvd hN)
        intro q hq _
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_nonneg (by positivity) hlog

/-- **Lemma 16 (additivity on coprime factors).** -/
theorem IC_coprime_add {M N1 N2 : ℕ} (hN1 : N1 ≠ 0) (hN2 : N2 ≠ 0) (h : Nat.Coprime N1 N2) :
    IC M (N1 * N2) = IC M N1 + IC M N2 := by
  have hco : Nat.gcd N1 N2 = 1 := h
  unfold IC
  rw [Nat.primeFactors_mul hN1 hN2, Finset.sum_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq2 : N2.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl (fun hd => (Nat.mem_primeFactors.mp hq).1.ne_one
        (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hq).2.1 hd))))
    rw [Nat.factorization_mul hN1 hN2]; simp [hq2]
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq1 : N1.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inr (Or.inl (fun hd => (Nat.mem_primeFactors.mp hq).1.ne_one
        (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd hd (Nat.mem_primeFactors.mp hq).2.1))))
    rw [Nat.factorization_mul hN1 hN2]; simp [hq1]

/-! ## §F — Stability under CRT refinement (Prop 8, Cor 9). -/

/-- The per-prime obstruction exponent is invariant under enlarging `N` by a
    factor coprime to `q`. -/
theorem thickness_stable_coprime {M N c : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0)
    {q : ℕ} (hq : ¬ q ∣ c) :
    (Nat.gcd M (N * c)).factorization q = (Nat.gcd M N).factorization q := by
  rw [factorization_gcd_apply hM (Nat.mul_ne_zero hN hc),
      factorization_gcd_apply hM hN, Nat.factorization_mul hN hc]
  have hcq : c.factorization q = 0 :=
    (Nat.factorization_eq_zero_iff c q).mpr (Or.inr (Or.inl hq))
  simp [Finsupp.add_apply, hcq]

/-! ## §G — Conditional derived equalizer = cotangent test (Theorem 20).

The bridge `H¹(L_{X_p}) = 0 ↔ smooth` (two-term model, Mathlib lacks the cotangent
complex) and `smooth ↔ gcd = 1` (good-prime gate) are taken as EXPLICIT
hypotheses; the elementary `gcd = 1 ↔ Tor = 0` is unconditional.  `#print axioms`
shows no `sorryAx` and no new global axiom. -/

/-- **Theorem 20 (conditional).** On overlaps above `p`, the derived equalizer
(`gcd = 1`), smoothness, and the cotangent test (`der = 0`) are equivalent. -/
theorem derived_equalizer_tfae (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate.symm
  tfae_have 2 ↔ 3 := Hder.symm
  tfae_finish

/-! ## §H — Global certification (Theorem 1/18): the gluing mechanism only.

We do NOT certify "X prime ⇔ ∃ global section" (the framework's soundness +
completeness claim, which rests on the non-elementary EC/AKS layer).  We formalize
the equalizer gluing it uses: two local witnesses `a, b` agree on a modular/p-adic
overlap iff their difference lies in `(M)∩(N) = (lcm)`. -/

/-- Overlap gluing condition: local witnesses `a, b` are compatible on the
    `(M, N)` overlap iff `lcm M N ∣ (a - b)`. -/
theorem overlap_glue_iff_lcm (M N a b : ℤ) :
    (M ∣ (a - b) ∧ N ∣ (a - b)) ↔ lcm M N ∣ (a - b) :=
  lcm_dvd_iff.symm

/-! ## Examples (Examples 1–3 of §4.3) and the corrected discrepancy. -/

section Examples
/-- Example 1 (mixed composite): `M = 2³·3 = 24`, `N = 2⁵·3²·5 = 1440`; `gcd = 24`. -/
example : Nat.gcd 24 1440 = 24 := by norm_num
/-- Example 2 (coprime): `gcd(35, 24) = 1`, so `Tor₁ = 0`. -/
example : Nat.gcd 35 24 = 1 := by norm_num
/-- Example 3 (single prime power): `gcd(12, 9) = 3`, so `Tor₁ ≅ ℤ/3`. -/
example : Nat.gcd 12 (3 ^ 2) = 3 := by norm_num
/-- The corrected Zero-Class discrepancy on `M=12, N=9`: the intersection is
    `(lcm 12 9) = (36)`, with `36 ∣ T` (not `gcd 3 ∣ T`) the true membership test. -/
example : Nat.lcm 12 9 = 36 := by norm_num
example : (9 : ℕ) ∣ Nat.lcm 12 9 := by norm_num     -- v₃(intersection) = 2 = max
example : ¬ (27 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms kernel_mem_iff_lcm
#print axioms zeroClass_mem_iff_lcm
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms lcm_dvd_iff_max
#print axioms card_ker_mulLeft
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms IC_mono
#print axioms IC_coprime_add
#print axioms thickness_stable_coprime
#print axioms derived_equalizer_tfae
#print axioms overlap_glue_iff_lcm
end AxiomAudit

end Spt3
