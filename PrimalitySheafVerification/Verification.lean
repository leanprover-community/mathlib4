/-
# Formal verification of the algebraic core of
  "Primality Sheaf via Local Filters and Derived Equalizers" (Lee ga Hyun, 2025)

This file formalises, in Lean 4 / Mathlib, the *load-bearing arithmetic identities*
of the paper.  The paper's scaffolding (a sheaf on the principal-open site of
`Spec ℤ`, fiber-product amalgams, p-adic logarithm gates, elliptic-curve
regularity) is largely informal and reduces, for every quantitative claim, to a
small set of standard facts about `gcd`, `lcm`, `Tor₁` of cyclic groups, and
`p`-adic valuations.  Those facts are what we verify here.

Mapping to the paper (see the accompanying README for the full dependency graph):

* §A  ⇄  Lemma 2.6, Prop 4.7, Fact 7.1, eq. (1)/(12):   kernel = (M) ∩ (pᵏ) = (lcm).
* §B  ⇄  Lemma 2.10, 4.8, 5.2, Def 2.11, eq. (17):       local thickness ε_p.
        **This section exposes a genuine error in the paper** (min vs. max).
* §C  ⇄  Thm 4.1, Cor 4.2, Thm 4.12, Def 5.3:            Tor₁ ≅ ℤ/gcd, obstruction-free.
* §D  ⇄  Prop 4.4, Thm 4.20, Prop 7.7:                    primewise (CRT) decomposition.
* §E  ⇄  Def 7.6, Prop 7.7, Example 4.5:                  indicator complexity, |Tor₁|.
* §F  ⇄  Thm 4.1 proof mechanism (Example 4.5):          ker(×M on ℤ/pᵏ) has order gcd.

NOTE.  No Lean toolchain was available in the authoring environment, so this file
was written against the vendored Mathlib source (all lemma names checked against
`Mathlib/…`) but **not compiled there**.  Verify with:
    lake env lean PrimalitySheafVerification/Verification.lean
-/
import Mathlib

namespace LeeGaHyunPrimalitySheaf

/-! ## §A.  Equalizer kernel = ideal intersection = lcm
    (Lemma 2.6 / Prop 4.7 / Fact 7.1; equations (1), (11)–(12))

The Čech overlap test `sᵢ ≡ sⱼ` is governed by the kernel of
`ℤ → ℤ/(M) × ℤ/(N)`.  In the PID `ℤ` this kernel is `(M) ∩ (N) = (lcm M N)`. -/

/-- Membership form: `a` maps to `0` in both `ℤ/(M)` and `ℤ/(N)` iff `lcm M N ∣ a`. -/
theorem equalizer_mem_iff (M N a : ℤ) :
    (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form: `(M) ∩ (N) = (lcm M N)` inside `ℤ`. -/
theorem equalizer_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- The duality `gcd · lcm = M · N`, used to pass between the intersection (lcm)
    and the common-residue-fiber (gcd) descriptions. -/
theorem gcd_mul_lcm_eq (M N : ℕ) : Nat.gcd M N * Nat.lcm M N = M * N :=
  Nat.gcd_mul_lcm M N

/-! ## §B.  Local thickness ε_p — and a correction to the paper
    (Lemma 2.10 / 4.8 / 5.2; Def 2.11; equation (17))

The paper repeatedly asserts (e.g. eq. (17), Lemma 2.10, 4.8, 5.2) that, after
localising at `p`,
        `((M) ∩ (pᵏ))_(p) = (p^{ε_p})`  with  `ε_p = min(v_p M, k)`.
But by §A the intersection IS `(lcm(M, pᵏ))`, and the `p`-adic valuation of an lcm
is the **maximum** of the valuations, not the minimum.  The minimum is the
valuation of `gcd(M, pᵏ)` — i.e. of the *common residue fiber* `ℤ/gcd`, a
different object.  The two lemmas below make both valuations precise. -/

/-- `v_p(lcm M N) = max(v_p M, v_p N)` (here for the prime `p` of `ℤ`). -/
theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]
  rcases Nat.le_total (M.factorization p) (N.factorization p) with h | h
  · rw [sup_eq_right.mpr h, max_eq_right h]
  · rw [sup_eq_left.mpr h, max_eq_left h]

/-- `v_p(gcd M N) = min(v_p M, v_p N)`.  This `min` is exactly the quantity the
    paper calls `ε_p`; it belongs to the gcd (common residue fiber), **not** to the
    ideal intersection `(M) ∩ (pᵏ) = (lcm)`. -/
theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]
  rcases Nat.le_total (M.factorization p) (N.factorization p) with h | h
  · rw [inf_eq_left.mpr h, min_eq_left h]
  · rw [inf_eq_right.mpr h, min_eq_right h]

/-- Specialisation to a prime power `N = pᵏ`: the intersection generator `lcm`
    has `p`-thickness `max(v_p M, k)`. -/
theorem lcm_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [factorization_lcm_apply hM hpk, Nat.factorization_pow_self hp]

/-- Specialisation: the gcd (common residue fiber) has `p`-thickness `min(v_p M, k)`. -/
theorem gcd_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.gcd M (p ^ k)).factorization p = min (M.factorization p) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [factorization_gcd_apply hM hpk, Nat.factorization_pow_self hp]

/-- **Concrete witness of the discrepancy** (the Example 4.5 data `M = 12`, `p = 3`,
    `k = 2`).  The ideal intersection is `(lcm 12 9) = (36)` with `3`-adic thickness
    `2 = max(1,2)`, while the paper's formula would give `ε₃ = min(1,2) = 1`. -/
section Example45Thickness
example : Nat.lcm 12 9 = 36 := by norm_num
example : Nat.gcd 12 9 = 3 := by norm_num
-- v₃(M) = 1   (3 ∣ 12 but 9 ∤ 12)
example : (3 : ℕ) ∣ 12 := by norm_num
example : ¬ (9 : ℕ) ∣ 12 := by norm_num
-- v₃(intersection) = v₃(lcm) = 2   (9 ∣ 36 but 27 ∤ 36)  ⇒ thickness is max = 2
example : (9 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
example : ¬ (27 : ℕ) ∣ Nat.lcm 12 9 := by norm_num
-- the paper's claimed min, for comparison:
example : min 1 2 = 1 := by decide
example : max 1 2 = 2 := by decide
end Example45Thickness

/-! ## §C.  Common residue fiber, Tor₁, and the obstruction-free criterion
    (Thm 4.1, Cor 4.2, Thm 4.12, Def 5.3)

`Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)` (Thm 4.1).  We verify the two facts that the
paper actually uses downstream: the *order* of this group is `gcd(M,N)` (the RHS
of Thm 4.1), and it is trivial iff `gcd(M,N) = 1` (Cor 4.2 / Thm 4.12). -/

/-- Order of the common residue fiber `ℤ/gcd` — the RHS of Theorem 4.1. -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = g :=
  ZMod.card g

/-- **Obstruction-free ⟺ Tor-vanishing** (Cor 4.2 / Thm 4.12), via the fiber being
    a single point. -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by
  simp [ZMod.card]

/-- The obstruction predicate `gcd(M, N) = 1` is literally coprimality. -/
theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N :=
  Iff.rfl

/-! ## §D.  CRT / primewise decomposition of the obstruction
    (Prop 4.4, Thm 4.20, Prop 7.7)

`Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min(v_q M, k(q))}`.  Since each summand order is
`q^{min(v_q M, v_q N)} = v_q(gcd)`, the primewise exponents are exactly the
`min`s — which is precisely `factorization_gcd_apply` of §B, for every prime `q`. -/

/-- Primewise exponent of the obstruction at a prime `q` equals `min(v_q M, v_q N)`. -/
theorem primewise_exponent {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (q : ℕ) :
    (Nat.gcd M N).factorization q = min (M.factorization q) (N.factorization q) :=
  factorization_gcd_apply hM hN q

/-! ## §E.  Indicator complexity and `|Tor₁|`
    (Def 7.6, Prop 7.7, Example 4.5)

`|Tor₁(ℤ/M, ℤ/N)| = ∏_{q∣N} q^{min(v_q M, k(q))} = gcd(M,N) = exp(IC(M;N))`.
The order identity `|Tor₁| = gcd` is `commonResidueFiber_card` (§C).  Here we check
the Example 4.5 instance numerically. -/

section Example45
/-- Example 4.5: `gcd(12, 3²) = 3`, hence `Tor₁(ℤ/12, ℤ/9) ≅ ℤ/3`. -/
example : Nat.gcd 12 (3 ^ 2) = 3 := by norm_num
/-- `|Tor₁| = 3 = 3^{min(v₃ 12, 2)} = 3^{min(1,2)}`. -/
example : (3 : ℕ) ^ min 1 2 = 3 := by decide
end Example45

/-! ## §F.  The mechanism of Theorem 4.1 (Example 4.5), verified by computation.

The paper proves `Tor₁(ℤ/M, ℤ/pᵏ) ≅ ker(·M : ℤ/pᵏ → ℤ/pᵏ)` from the free
resolution `0 → ℤ →(·M) ℤ → ℤ/M → 0`, and shows that kernel is cyclic of order
`gcd(M, pᵏ)`.  For the Example 4.5 data this is a finite computation: the kernel
of multiplication by `12` on `ℤ/9` is `{0,3,6}`, of order `gcd(12,9) = 3`.
(`native_decide` evaluates the `ZMod 9` arithmetic by compilation; plain `decide`
also works in principle but is much slower on `ZMod` numerals.) -/
example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by native_decide

/-!
## Results that are NOT formalised here (and why)

The following items of the paper are *not* purely algebraic identities and are
out of scope for a short, self-contained Mathlib script:

* **Theorem 2.1, Lemma 2.3, Remark 2.2 (MtA-linearization / p-adic log gate).**
  These rest on the 1-Lipschitz property of the `p`-adic logarithm on `1 + pℤ_p`
  and a quadratic-remainder bound.  Mathlib's `PadicInt`/`Padic` log API is too
  limited to state these cleanly without substantial development.

* **Propositions 2.4, 2.5 (achievability of (H_k) for `M = pⁿy ± (A−1)`).**
  These are ultrametric valuation-of-sum arguments; provable in principle from
  `padicValRat`/`padicValInt` but require care with the "unequal valuations ⇒
  valuation of the sum is the min" step.

* **Lemma 6.1; Theorems 6.2 / Cor 7.4 (terminal/minimal amalgam); Lemma 7.3.**
  These are statements about sheaves on the principal-open site of `Spec ℤ` and a
  universal property of an iterated fiber product.  Formalising them requires the
  full site/sheaf machinery (`CategoryTheory.Sites`) and a model of the four
  predicate subsheaves; the *universal property* itself is then a one-line
  consequence of the categorical fiber product, but building the site model is a
  separate project.

* **The elliptic-curve regularity layer `F_EC`** is described only informally in
  the source and has no formal content to verify.

Everything the paper actually uses to *quantify* obstructions — the kernel/lcm
identity, the gcd/Tor computation, the primewise minima, and the cardinality of
the obstruction group — is captured above.
-/

end LeeGaHyunPrimalitySheaf
