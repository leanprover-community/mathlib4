/-
================================================================================
  Spt7.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "Section 4: Overlaps, Tor, Koszul Regularity, and
                     Sheaf / Local Charts".

  Kernel-checked against Mathlib; NO `sorry`, NO new global `axiom`.  Conditional
  results carry their assumptions as explicit hypotheses.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Thm .1 (independence, canonical profile A=4, M=pₙ+3)
                       ↦ canonical_coprime, canonical_obstructionFree        PROVED
    Thm .3 / .19 / Lem .6 / .39, Cor .9 / .40  equalizer kernel = (lcm),
        Čech Ĥ¹ ≅ ℤ/gcd, Tor₁ ≅ ℤ/gcd, obstruction-free ⇔ gcd=1
                       ↦ kernel_mem_iff_lcm, crt_solvable_iff, card_ker_mulLeft,
                         obstructionFree_iff_*                                PROVED
    Thm .19(a) thickness (CORRECTED)  gcd→min, lcm→max
                       ↦ factorization_gcd_apply / lcm_apply                  PROVED
    Prop .8, IC; Cor .9  monotonicity/additivity of IC; |Tor| = exp(IC)
                       ↦ IC_mono, IC_coprime_add, card_Tor_eq_exp_IC          PROVED
    Lem .10 / .14, Thm .11 / .15, Prop .16  Koszul / regular-sequence criterion
                       ↦ stalk_regularity_test, singleton_regular_iff,
                         nil_regular, cons_regular_iff, regular_of_linearEquiv PROVED
    Thm .47 (Equivalence C) good-prime synchronization (CONDITIONAL)
                       ↦ equivalence_C                                       PROVED (cond.)

  ⚠ CORRECTION (7th paper, same error): Thm .19(a) gives `((M)∩(pᵏ))_(p) = p^{εp}`,
  `εp = min{vp M,k}`.  Wrong: the intersection is `(lcm)`, of `p`-thickness `max`;
  `min` is the valuation of `gcd` (failure fiber / Tor).

  HONEST OMISSIONS: the full Koszul-complex homology criterion (Thm .11 via
  `Hᵢ(K•) = 0`) needs the Koszul complex (only partial in Mathlib); we give the
  faithful regular-sequence API (`IsSMulRegular`, cons/singleton/nil).  The
  6-functor / weight / Deligne machinery (Lem .22–.46, Thm .42/.44, Equivalence C
  §) needs étale cohomology and weights, absent from Mathlib (conditional/omitted).
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators

namespace Spt7

/-! ## §A — Independence at good primes for the canonical profile (Theorem .1).

`A = 4`, `M = pₙ·1 + (A-1) = pₙ + 3`.  For a prime `p ≥ 5`, `vp(M) = 0`, so
`gcd(M, pᵏ) = 1` and `Tor₁ = 0` (the overlap is obstruction-free). -/

/-- **Theorem .1 (arithmetic core).** For prime `p ≥ 5` and `k ≥ 0`,
    `gcd(p+3, pᵏ) = 1` (i.e. `vp(p+3) = 0`). -/
theorem canonical_coprime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (k : ℕ) :
    Nat.Coprime (p + 3) (p ^ k) := by
  have hp3 : ¬ p ∣ (p + 3) := by
    intro h
    have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_refl p)).mp h
    have := Nat.le_of_dvd (by norm_num) h3; omega
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp3).symm.pow_right k

/-- **Theorem .1 (consequence).** The canonical overlap is obstruction-free. -/
theorem canonical_obstructionFree {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (k : ℕ) :
    Nat.gcd (p + 3) (p ^ k) = 1 := canonical_coprime hp h5 k

/-! ## §B — Equalizer / Čech–Tor / CRT (Thm .3/.19, Lem .6/.39, Cor .9/.40). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- **Lem .39 (Čech Ĥ¹ obstruction / gluing).** Local witnesses glue iff `gcd ∣ (a-b)`. -/
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

/-- **Lem .6 / Thm .3 / .19.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
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

/-- **Cor .9 / .40.** Obstruction-free ⟺ gcd = 1. -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §C — Primewise decomposition & indicator complexity (Prop .8). -/

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

/-- **Prop .8 (monotonicity).** `N' ∣ N ⇒ IC(M;N') ≤ IC(M;N)`. -/
theorem IC_mono {M N' N : ℕ} (hN : N ≠ 0) (hdvd : N' ∣ N) : IC M N' ≤ IC M N := by
  have hN' : N' ≠ 0 := fun h => hN (by simpa [h] using hdvd)
  have hle : N'.factorization ≤ N.factorization := (Nat.factorization_le_iff_dvd hN' hN).mpr hdvd
  calc IC M N'
      ≤ ∑ q ∈ N'.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_le_mul_of_nonneg_right (min_le_min le_rfl (by exact_mod_cast hle q)) hlog
    _ ≤ IC M N := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hdvd hN)
        intro q hq _
        have hlog : (0:ℝ) ≤ Real.log q :=
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.one_lt.le)
        exact mul_nonneg (by positivity) hlog

/-- **Prop .8 (additivity on coprime factors).** -/
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

/-! ## §D — Koszul / regular-sequence criterion (Lem .10/.14, Thm .11/.15, Prop .16).

Faithful regular-sequence API from Mathlib (`RingTheory.Sequence`).  `IsSMulRegular
M r` is "multiplication by `r` is injective on `M`" — the one-line stalk regularity
test; the inductive `cons` characterisation is the content of the Koszul criterion. -/

section Koszul
open RingTheory.Sequence
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Lem .10 / .14 (one-line stalk regularity test).** A single-element sequence
    `[r]` is regular iff `r` is `M`-regular (`IsSMulRegular`, i.e. multiplication by
    `r` is injective — a non-zero-divisor on the stalk). -/
theorem singleton_regular_iff (r : R) :
    IsWeaklyRegular M [r] ↔ IsSMulRegular M r := isWeaklyRegular_singleton_iff M r

/-- The empty sequence is (weakly) regular. -/
theorem nil_regular : IsWeaklyRegular M ([] : List R) := by simp

/-- **Theorem .11 / .15 (Koszul criterion, inductive content).** `r :: rs` is
    regular iff `r` is `M`-regular and `rs` is regular on `M/rM`. -/
theorem cons_regular_iff (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsWeaklyRegular (QuotSMulTop r M) rs :=
  isWeaklyRegular_cons_iff M r rs

/-- **Prop .16 (stability under linear isomorphism / base change).** Regularity
    transports along an `R`-linear equivalence. -/
theorem regular_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r :=
  e.isSMulRegular_congr r

end Koszul

/-! ## §E — Conditional good-prime synchronization / Equivalence C (Theorem .47).

The étale/motivic/cotangent/weight detectors are not in Mathlib; their bridges are
explicit hypotheses.  The arithmetic equalizer face (`gcd = 1`) is unconditional. -/

/-- **Theorem .47 (Equivalence C, conditional).** On `U = D(∆)`, the discriminant
    gate (`smooth`), the derived (Koszul/Tor) test (`der = 0`), and the equalizer
    face (`gcd = 1`) are equivalent. -/
theorem equivalence_C (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth) (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate.symm
  tfae_have 2 ↔ 3 := Hder.symm
  tfae_finish

/-! ## Examples. -/

section Examples
/-- Canonical profile: `p = 5` gives `gcd(8, 5ᵏ) = 1`. -/
example (k : ℕ) : Nat.Coprime (5 + 3) (5 ^ k) := canonical_coprime (by decide) (by decide) k
example : Nat.gcd (7 + 3) (7 ^ 4) = 1 := by norm_num   -- p = 7 ≥ 5
/-- Equalizer–Tor numeric: `gcd(12, 9) = 3`. -/
example : Nat.gcd 12 9 = 3 := by norm_num
/-- Regularity is preserved by the identity equivalence (sanity check). -/
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ IsSMulRegular M r :=
  regular_of_linearEquiv (LinearEquiv.refl R M) r
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms canonical_coprime
#print axioms kernel_mem_iff_lcm
#print axioms crt_solvable_iff
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms card_ker_mulLeft
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms IC_mono
#print axioms IC_coprime_add
#print axioms singleton_regular_iff
#print axioms cons_regular_iff
#print axioms regular_of_linearEquiv
#print axioms equivalence_C
end AxiomAudit

end Spt7
