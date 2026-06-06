/-
================================================================================
  Spt4.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun (paper #4: primality sheaf, Čech H¹, cohomological density).

  Every theorem is kernel-checked against Mathlib, NO `sorry`, NO new global
  `axiom`.  The `AxiomAudit` section confirms `sorryAx`-freeness; conditional
  results carry their assumptions as explicit hypotheses.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result ↦ Lean name ↦ status)
  ------------------------------------------------------------------------------
    Prop 2.1, Lem 2.3, Thm 3.9   equalizer kernel = (M)∩(N) = (lcm)
                                  ↦ kernel_mem_iff_lcm, kernel_ideal_inter   PROVED
    Thm 3.9/3.15/3.23, Lem 3.22  Čech Ĥ¹ obstruction ≅ ℤ/gcd (gluing)
                                  ↦ crt_solvable_iff, obstr_vanishes_iff,
                                    commonResidueFiber_card                  PROVED
    Remark 3.10, §3.2.3 (CORRECTED) thickness: gcd→min, lcm→max
                                  ↦ factorization_gcd_apply / lcm_apply       PROVED
    Thm 6.35/6.36, Prop 7.6, Lem 8.3.1  Tor₁ ≅ ℤ/gcd, primewise, gcd=1⇔triv
                                  ↦ card_ker_mulLeft, obstructionFree_iff_*,
                                    gcd_eq_prod_primeFactors                  PROVED
    Cor 7.4/7.7/7.9, Prop 6.29, Cor 8.3.3  CRT gluing on coprime opens
                                  ↦ crt_iso, crt_solvable_iff                 PROVED
    §3.4(7)-type, IC; Cor "order=exp(IC)"  indicator complexity
                                  ↦ IC, card_Tor_eq_exp_IC                    PROVED
    Def 3.18, Prop 3.19/3.20     cohomological density δ_coh + monotonicity
                                  ↦ deltaCoh, deltaCoh_anti  (abstract)       PROVED (abs.)
    Prop 3.21, Rem 3.10          stability under CRT refinement
                                  ↦ thickness_stable_coprime                 PROVED
    Thm 7.1, Prop 7.3/3.26, Thm 8.2.2  good-prime box / detector equivalence
                                  ↦ derived_equalizer_tfae, good_prime_box   PROVED (cond.)

  ⚠ CORRECTION (repeated from papers 1/3):  the "localized thickness
  `((M)∩(pᵏ))_(p) = p^{εp}`, `εp = min{vp M, k}`" (eq. lines 269/431/979/1220,
  Remark 3.10) is WRONG.  The intersection is `(lcm)`, which localises to
  `p^{max}`; the `min` is the valuation of `gcd` (the common residue fiber and
  Tor₁), a different object.  Proved below (`factorization_gcd_apply` = min,
  `factorization_lcm_apply` = max).

  HONEST OMISSIONS (Mathlib lacks the infrastructure; NOT stubbed):
    • AB-linearization / p-adic log gate (§8.2, Thm 8.2.2): no p-adic log API.
    • Analytic density of the detector support and the analytic-vs-cohomological
      independence (Lem 8.3.4, Prop 8.3.5, Thm 8.3.6): need PNT / Dirichlet.
    • Conjecture 8.3.7: it is a conjecture.
    • Full sheaf cohomology of Spec ℤ / Ext¹ (Thm 3.17/3.24): δ_coh is therefore
      formalized abstractly (its detection predicate is a parameter).
    • étale/motivic/cotangent detectors (Thm 7.1, Prop 7.3): see §I (conditional).
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open scoped BigOperators

namespace Spt4

/-! ## §A — Equalizer kernel = ideal intersection = lcm (Prop 2.1, Lem 2.3, Thm 3.9). -/

theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a := lcm_dvd_iff.symm

theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a; simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-! ## §B — Čech Ĥ¹ gluing obstruction ≅ ℤ/gcd (Thm 3.9/3.15/3.23, Ex 2.7/2.8).

The two-open Čech computation gives a gluing obstruction group `ℤ/gcd(M,N)`:
two local witnesses `a, b` glue to a global `x` iff their residues agree modulo
`gcd`, i.e. the obstruction `a - b ∈ ℤ/gcd` vanishes.  (This is the CRT short
exact sequence `0 → ℤ/lcm → ℤ/M ⊕ ℤ/N → ℤ/gcd → 0` whose cokernel `ℤ/gcd` the
paper records as `Ĥ¹`, identified with `Tor₁` in Thm 3.17/3.24.) -/

/-- **CRT solvability / gluing criterion (Thm 3.9).** A pair of local residues
`(a mod M, b mod N)` lifts to a global integer iff `gcd(M,N) ∣ (a - b)`. -/
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

/-- The gluing obstruction lives in `ℤ/gcd`; it vanishes iff the data glue. -/
theorem obstr_vanishes_iff (M N a b : ℤ) :
    ((a - b : ℤ) : ZMod (Int.gcd M N)) = 0 ↔ (∃ x : ℤ, M ∣ (x - a) ∧ N ∣ (x - b)) := by
  rw [crt_solvable_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Order of the obstruction group `ℤ/gcd` (= |Ĥ¹| = |Tor₁|). -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] : Fintype.card (ZMod g) = g := ZMod.card g

/-! ## §C — Thickness, CORRECTED (Remark 3.10, §3.2.3). -/

theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]

theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]

/-! ## §D — Tor₁ ≅ ℤ/gcd (Thm 6.35/6.36, Prop 7.6, Lem 8.3.1). -/

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

/-- **Thm 6.35 (order form).** `|Tor₁^ℤ(ℤ/M, ℤ/N)| = gcd(N, M)`. -/
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

/-- **Lem 8.3.1.** Obstruction-free ⟺ gcd = 1 (fiber is a point). -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by simp [ZMod.card]

theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N := Iff.rfl

/-! ## §E — CRT split and primewise decomposition (Prop 6.29, Thm 6.36, Cor 8.3.3). -/

noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h

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

/-! ## §F — Indicator complexity (`order = exp(IC)`). -/

noncomputable def IC (M N : ℕ) : ℝ :=
  ∑ q ∈ N.primeFactors, (min (M.factorization q) (N.factorization q) : ℝ) * Real.log q

theorem card_Tor_eq_exp_IC {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    (Nat.gcd M N : ℝ) = Real.exp (IC M N) := by
  rw [IC, Real.exp_sum, gcd_eq_prod_primeFactors hM hN, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
  rw [Nat.cast_pow, ← Nat.cast_min, ← Real.log_pow, Real.exp_log (by positivity)]

/-! ## §G — Cohomological density δ_coh (Def 3.18, Prop 3.19/3.20), abstractly.

`δ_coh(P) = inf{ i | ∃ sheaf with Supp ⊆ P and Hⁱ ≠ 0 }` uses sheaf cohomology of
`Spec ℤ`, absent from Mathlib.  We model the detection predicate abstractly; the
content of Prop 3.20 (monotonicity) is exactly antitonicity of `sInf`. -/

/-- δ_coh as `sInf` of detection degrees (detection predicate abstract). -/
noncomputable def deltaCoh {S : Type*} (Detectable : Set S → ℕ∞ → Prop) (P : Set S) : ℕ∞ :=
  sInf {i | Detectable P i}

/-- **Prop 3.20 (monotonicity).** If `P ⊆ Q` then `δ_coh(Q) ≤ δ_coh(P)`
    (more support ⇒ more detectable ⇒ smaller minimal degree). -/
theorem deltaCoh_anti {S : Type*} (Detectable : Set S → ℕ∞ → Prop)
    (hmono : ∀ {P Q : Set S} {i}, P ⊆ Q → Detectable P i → Detectable Q i)
    {P Q : Set S} (hPQ : P ⊆ Q) : deltaCoh Detectable Q ≤ deltaCoh Detectable P := by
  unfold deltaCoh; exact sInf_le_sInf (fun i hi => hmono hPQ hi)

/-! ## §H — Stability under CRT refinement (Prop 3.21, Rem 3.10). -/

theorem thickness_stable_coprime {M N c : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hc : c ≠ 0)
    {q : ℕ} (hq : ¬ q ∣ c) :
    (Nat.gcd M (N * c)).factorization q = (Nat.gcd M N).factorization q := by
  rw [factorization_gcd_apply hM (Nat.mul_ne_zero hN hc),
      factorization_gcd_apply hM hN, Nat.factorization_mul hN hc]
  have hcq : c.factorization q = 0 :=
    (Nat.factorization_eq_zero_iff c q).mpr (Or.inr (Or.inl hq))
  simp [Finsupp.add_apply, hcq]

/-! ## §I — Conditional good-prime box / detector equivalence (Thm 7.1, Prop 7.3/3.26).

The étale bump, motivic Euler jump, and derived (cotangent) detector are not in
Mathlib; their classical bridges are taken as explicit hypotheses. -/

/-- **Prop 7.3 / 3.26, Thm 8.2.2 (conditional).** Derived equalizer, smoothness,
and the cotangent test are equivalent (given the two-term-model bridge and the
good-prime gate). -/
theorem derived_equalizer_tfae (smooth : Prop) (der M pk : ℕ)
    (Hder : der = 0 ↔ smooth) (Hgate : smooth ↔ Nat.gcd M pk = 1) :
    [Nat.gcd M pk = 1, smooth, der = 0].TFAE := by
  tfae_have 1 ↔ 2 := Hgate.symm
  tfae_have 2 ↔ 3 := Hder.symm
  tfae_finish

/-- **Thm 7.1 (curve master identity, conditional).** `Δχ_mot = bump = b₁(Γ)+Σδ`. -/
theorem curve_master_identity (bump mot b1 deltaSum : ℕ)
    (Hbump : bump = b1 + deltaSum) (Hmot : mot = bump) :
    mot = b1 + deltaSum ∧ bump = b1 + deltaSum := ⟨Hmot.trans Hbump, Hbump⟩

/-- **Prop 7.3 (good-prime box, conditional).** On a smooth fiber all detectors vanish. -/
theorem good_prime_box (smooth : Prop) (bump mot der b1 deltaSum : ℕ)
    (Hder : der = 0 ↔ smooth) (Hbump : bump = b1 + deltaSum)
    (Hmot : mot = bump) (Hsing : smooth ↔ (b1 = 0 ∧ deltaSum = 0))
    (h : smooth) : bump = 0 ∧ mot = 0 ∧ der = 0 := by
  have hb : bump = 0 ↔ smooth := by rw [Hbump, Nat.add_eq_zero_iff, ← Hsing]
  exact ⟨hb.mpr h, Hmot ▸ hb.mpr h, Hder.mpr h⟩

/-! ## Examples (Ex 2.7/2.8/3.16/3.25). -/

section Examples
/-- Ex 2.7 / 3.16 / 3.25: `(M, pᵏ) = (6, 9)`: `lcm = 18`, `gcd = 3`, so `Ĥ¹ ≅ ℤ/3`. -/
example : Nat.lcm 6 9 = 18 := by norm_num
example : Nat.gcd 6 9 = 3 := by norm_num
/-- Ex 2.8 / 3.25: `(M, pᵏ) = (10, 9)`: `gcd = 1`, so `Ĥ¹ = 0` (obstruction-free). -/
example : Nat.gcd 10 9 = 1 := by norm_num
/-- Gluing obstruction for residues `a=1, b=0` over `(M,N)=(6,9)` is non-trivial
    (since `gcd 6 9 = 3 ∤ 1`), so the pieces do NOT glue. -/
example : ¬ (∃ x : ℤ, (6:ℤ) ∣ (x - 1) ∧ (9:ℤ) ∣ (x - 0)) := by
  rw [crt_solvable_iff]; decide
end Examples

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms kernel_mem_iff_lcm
#print axioms crt_solvable_iff
#print axioms obstr_vanishes_iff
#print axioms factorization_gcd_apply
#print axioms factorization_lcm_apply
#print axioms card_ker_mulLeft
#print axioms obstructionFree_iff_card
#print axioms gcd_eq_prod_primeFactors
#print axioms card_Tor_eq_exp_IC
#print axioms deltaCoh_anti
#print axioms thickness_stable_coprime
#print axioms derived_equalizer_tfae
#print axioms good_prime_box
end AxiomAudit

end Spt4
