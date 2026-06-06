/-
================================================================================
  Spt6.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun (paper #6: bump = Euler jump, good-prime synchronization,
                   equalizer–Tor, direct-sum H¹).

  Kernel-checked against Mathlib; NO `sorry`, NO new global `axiom`.  Conditional
  results carry their assumptions as explicit hypotheses (visible in signature).

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Lem 6.4, Prop 10.1, Thm 9.1/9.3(iii)  equalizer kernel = (M)∩(N) = (lcm)
                       ↦ kernel_mem_iff_lcm, kernel_ideal_inter             PROVED
    Prop 10.7, Thm 9.3(iii) thickness (CORRECTED)  gcd→min, lcm→max
                       ↦ factorization_gcd_apply / lcm_apply                 PROVED
    Thm 9.1, Prop 10.2/10.8  Tor₁ ≅ ℤ/gcd; obstruction-free ⇔ gcd=1
                       ↦ card_ker_mulLeft, obstructionFree_iff_*             PROVED
    Lem 6.4, CRT       crt split + gluing obstruction (gcd | a-b)
                       ↦ crt_iso, crt_solvable_iff                           PROVED
    primewise / IC     |Tor| = ∏ qᵃ = exp(IC)
                       ↦ gcd_eq_prod_primeFactors, card_Tor_eq_exp_IC        PROVED
    Prop 10.6 (algebraic shadow)  direct-sum H¹ ≅ ⊕Λ has card |Λ|ⁿ; H⁰ = 0
                       ↦ directSum_card, H0_zero                            PROVED (alg.)
    Thm 6.1 / Cor 6.3  bump = Euler jump; good-prime box (CONDITIONAL)
                       ↦ curve_master_identity, good_prime_box               PROVED (cond.)
    Thm 9.3 Good-Prime Synchronization (CONDITIONAL)
                       ↦ goodPrime_synchronization                          PROVED (cond.)

  ⚠ CORRECTION (6th paper, same error): Thm 9.3(iii)/Prop 10.7 give the localized
  intersection thickness as `p^{min{vp M,k}}`.  This is wrong: `(M)∩(pᵏ)=(lcm)`
  localises to `p^{max}`; `min` is the valuation of `gcd` (the failure fiber/Tor).

  HONEST OMISSIONS: bump/Euler jump and the direct-sum H¹ (Prop 10.6, Thm 6.1)
  require étale/motivic/sheaf cohomology of Spec ℤ — included only conditionally
  or as the algebraic shadow (finite-rank cardinality).  AB-linearization /
  p-adic log (Rem 6.5/10.5) is out of Mathlib scope.
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators

namespace Spt6

/-! ## §A — Equalizer kernel = (M)∩(N) = (lcm) (Lem 6.4, Prop 10.1, Thm 9.1/9.3(iii)). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- **Lem 6.4 (CRT / gluing obstruction).** Local witnesses `a, b` glue iff
    `gcd(M,N) ∣ (a - b)`. -/
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

/-! ## §B — Thickness, CORRECTED (Prop 10.7, Thm 9.3(iii)). -/

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-! ## §C — Equalizer–Tor (Thm 9.1, Prop 10.2/10.8). -/

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

/-- **Thm 9.1 / Prop 10.2.** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
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

/-! ## §D — Primewise decomposition and indicator complexity. -/

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

/-! ## §E — Direct-sum H¹ (Prop 10.6), algebraic shadow.

The sheaf-cohomology statement `H¹(S, K_{f,X}) ≅ ⊕_{p ≤ X, p ∈ P_f} Λ`, `H⁰ = 0`
needs cohomology of `Spec ℤ` with skyscraper coefficients (absent from Mathlib).
Its algebraic content — a finite direct sum of `n` copies of `Λ = ℤ/ℓ` has
cardinality `ℓⁿ`, and the zero module has cardinality `1` — is verified here. -/

/-- The detector group `⊕_{i<n} ℤ/ℓ` has cardinality `ℓⁿ` (= |Λ|^{#visible primes}). -/
theorem directSum_card (ℓ n : ℕ) [NeZero ℓ] :
    Fintype.card (Fin n → ZMod ℓ) = ℓ ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- `H⁰ = 0`: the zero module is a single point. -/
theorem H0_zero : Fintype.card (Fin 0 → ZMod 1) = 1 := by decide

/-! ## §F — Conditional good-prime synchronization (Thm 9.3, Thm 6.1, Cor 6.3).

The discriminant/Jacobian gate (smooth), the Hensel gate, the étale bump, and the
derived (Tor/cotangent) detector are linked by classical bridges that Mathlib
lacks (étale/motivic/cotangent).  These are explicit hypotheses; the arithmetic
equalizer face (`gcd = 1`) is unconditional. -/

/-- **Thm 9.3 (Good-Prime Synchronization, conditional).** On `U = D(∆)`, the
    discriminant/Hensel gate (`smooth`), the equalizer face (`gcd = 1`), the
    derived test (`der = 0`), and the étale bump (`bump = 0`) are all equivalent. -/
theorem goodPrime_synchronization (smooth : Prop) (der bump M pk : ℕ)
    (Hgate : smooth ↔ Nat.gcd M pk = 1) (Hder : der = 0 ↔ smooth) (Hbump : bump = 0 ↔ smooth) :
    [smooth, Nat.gcd M pk = 1, der = 0, bump = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate
  tfae_have 1 ↔ 3 := Hder.symm
  tfae_have 1 ↔ 4 := Hbump.symm
  tfae_finish

/-- **Thm 6.1 (bump = Euler jump, conditional).** `Δχ_mot = bump = b₁(Γ) + Σδ`. -/
theorem curve_master_identity (bump mot b1 deltaSum : ℕ)
    (Hbump : bump = b1 + deltaSum) (Hmot : mot = bump) :
    mot = b1 + deltaSum ∧ bump = b1 + deltaSum := ⟨Hmot.trans Hbump, Hbump⟩

/-- **Cor 6.3 (good-prime box, conditional).** On a smooth fiber all detectors vanish. -/
theorem good_prime_box (smooth : Prop) (bump mot der b1 deltaSum : ℕ)
    (Hder : der = 0 ↔ smooth) (Hbump : bump = b1 + deltaSum)
    (Hmot : mot = bump) (Hsing : smooth ↔ (b1 = 0 ∧ deltaSum = 0))
    (h : smooth) : bump = 0 ∧ mot = 0 ∧ der = 0 := by
  have hb : bump = 0 ↔ smooth := by rw [Hbump, Nat.add_eq_zero_iff, ← Hsing]
  exact ⟨hb.mpr h, Hmot ▸ hb.mpr h, Hder.mpr h⟩

/-! ## Examples. -/

section Examples
example : Nat.gcd 12 9 = 3 := by norm_num
example : Nat.lcm 6 9 = 18 := by norm_num
/-- Direct-sum cardinality: `⊕_{i<3} ℤ/5` has `5³ = 125` elements. -/
example : Fintype.card (Fin 3 → ZMod 5) = 125 := by rw [directSum_card]; norm_num
/-- Non-gluing example over `(6,9)` with residues `a=1,b=0` (`gcd 3 ∤ 1`). -/
example : ¬ (∃ x : ℤ, (6:ℤ) ∣ (x - 1) ∧ (9:ℤ) ∣ (x - 0)) := by
  rw [crt_solvable_iff]; decide
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms kernel_mem_iff_lcm
#print axioms crt_solvable_iff
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms card_ker_mulLeft
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms directSum_card
#print axioms goodPrime_synchronization
#print axioms good_prime_box
end AxiomAudit

end Spt6
