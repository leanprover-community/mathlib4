/-
================================================================================
  Spt1.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "Primality Sheaf via Local Filters and Derived Equalizers".

  This file is the HONEST CORE of the spt-1 formalization: it contains only the
  genuinely true, elementary-arithmetic results of the paper, each proved in
  full against Mathlib (no `sorry`, no project-level `axiom`).  Run

      #print axioms <name>

  on any theorem below: it depends only on Lean/Mathlib's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — never on `sorryAx`.

  What is and is NOT here (full disclosure, cf. the §-by-§ map):
    * INCLUDED (proved):  the kernel/lcm identity (Lem 2.6 / Prop 4.7 / Fact 7.1),
      the p-adic thickness of gcd and lcm (Lem 2.10 / 4.8 / 5.2, CORRECTED),
      the order of the common residue fiber and the obstruction-free criterion
      (Thm 4.1 RHS / Cor 4.2 / Thm 4.12), the primewise/CRT exponent (Prop 4.4 /
      Thm 4.20 / Prop 7.7), and the worked Example 4.5.
    * NOT INCLUDED (and why): the p-adic logarithm gate (Thm 2.1, Lem 2.3) and the
      sheaf-theoretic terminal amalgam (Thm 6.2) are NOT elementary arithmetic
      and are deliberately omitted rather than stubbed with `sorry`/`axiom`.

  Imports are kept minimal on purpose (no `import Mathlib`) so the file builds
  from a small slice of Mathlib.
================================================================================
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic.NormNum.GCD

namespace Spt1

/-! ## §2 (Basic) — definitions

`v_p` is taken to be `Nat.factorization · p` (for a prime `p` this is exactly the
`p`-adic valuation `padicValNat p ·`; we avoid importing the analytic Padics so
the file stays light). -/

/-- Definition 2.11 / 4.11 / 5.3 — the common residue fiber index `gcd(M, p^k)`.
    Its `Spec` is the failure locus `F(M,k) = Spec(ℤ/gcd(M,p^k))`. -/
def commonResidueIndex (M p k : ℕ) : ℕ := Nat.gcd M (p ^ k)

/-- Definition 2.11 — the local thickness `ε_p = min(v_p M, k)`. -/
def localThickness (M p k : ℕ) : ℕ := min (M.factorization p) k

/-- The obstruction-free predicate at `p`. -/
def obstructionFree (M p k : ℕ) : Prop := Nat.gcd M (p ^ k) = 1

@[simp] lemma commonResidueIndex_def (M p k : ℕ) :
    commonResidueIndex M p k = Nat.gcd M (p ^ k) := rfl

@[simp] lemma localThickness_def (M p k : ℕ) :
    localThickness M p k = min (M.factorization p) k := rfl

/-! ## §3 (Kernel) — L1: equalizer kernel `= (M) ∩ (N) = (lcm M N)`
    (Lemma 2.6 / Proposition 4.7 / Fact 7.1; equations (1), (11), (12)). -/

/-- Membership form: an integer `a` maps to `0` in both `ℤ/(M)` and `ℤ/(N)`
    iff `lcm M N ∣ a`. -/
theorem equalizer_mem_iff (M N a : ℤ) :
    (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form: `(M) ∩ (N) = (lcm M N)` inside `ℤ`. -/
theorem equalizer_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- The duality `gcd · lcm = M · N`, the bridge between the intersection (lcm)
    and the common-residue-fiber (gcd) descriptions. -/
theorem gcd_mul_lcm_eq (M N : ℕ) : Nat.gcd M N * Nat.lcm M N = M * N :=
  Nat.gcd_mul_lcm M N

/-! ## §3 (Thickness) — L2: local thickness, CORRECTED
    (Lemma 2.10 / 4.8 / 5.2; Def 2.11; eq. (17)).

The paper attaches `ε_p = min(v_p M, k)` to the *localised intersection*
`((M) ∩ (p^k))_(p)`.  But the intersection IS `(lcm)`, whose valuation is the
**maximum**; the **minimum** is the valuation of `gcd` (the common residue
fiber).  Both are proved below, and the discrepancy is pinned on Example 4.5. -/

/-- `v_p(gcd M N) = min(v_p M, v_p N)`.  This `min` is the true thickness `ε_p`
    (it lives on the common residue fiber `gcd`, NOT on the intersection). -/
theorem factorization_gcd_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.gcd M N).factorization p = min (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]
  rcases Nat.le_total (M.factorization p) (N.factorization p) with h | h
  · rw [inf_eq_left.mpr h, min_eq_left h]
  · rw [inf_eq_right.mpr h, min_eq_right h]

/-- `v_p(lcm M N) = max(v_p M, v_p N)`.  This is the thickness of the *ideal
    intersection* `(M) ∩ (N) = (lcm)` — a maximum, not the paper's minimum. -/
theorem factorization_lcm_apply {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (p : ℕ) :
    (Nat.lcm M N).factorization p = max (M.factorization p) (N.factorization p) := by
  rw [Nat.factorization_lcm hM hN, Finsupp.sup_apply]
  rcases Nat.le_total (M.factorization p) (N.factorization p) with h | h
  · rw [sup_eq_right.mpr h, max_eq_right h]
  · rw [sup_eq_left.mpr h, max_eq_left h]

/-- Prime-power specialisation: the common residue fiber `gcd(M, p^k)` has
    `p`-thickness `min(v_p M, k)`, i.e. exactly `localThickness M p k`. -/
theorem gcd_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.gcd M (p ^ k)).factorization p = localThickness M p k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [localThickness_def, factorization_gcd_apply hM hpk, Nat.factorization_pow_self hp]

/-- Prime-power specialisation: the ideal intersection `(M) ∩ (p^k) = (lcm)` has
    `p`-thickness `max(v_p M, k)` — NOT `localThickness`. -/
theorem lcm_thickness_prime_pow {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (k : ℕ) :
    (Nat.lcm M (p ^ k)).factorization p = max (M.factorization p) k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [factorization_lcm_apply hM hpk, Nat.factorization_pow_self hp]

/-! ## §3 (Tor / Obstruction) — T1, Cor 4.2, Thm 4.12
    `Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)`. We verify the two downstream facts:
    the *order* of the fiber is `gcd` (RHS of Thm 4.1), and it is trivial iff
    `gcd = 1` (Cor 4.2 / Thm 4.12). -/

/-- Order of the common residue fiber `ℤ/gcd` — the RHS of Theorem 4.1. -/
theorem commonResidueFiber_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = g :=
  ZMod.card g

/-- Cor 4.2 / Thm 4.12 — obstruction-free ⟺ Tor vanishes (fiber is a point). -/
theorem obstructionFree_iff_card {g : ℕ} [NeZero g] :
    Fintype.card (ZMod g) = 1 ↔ g = 1 := by
  simp [ZMod.card]

/-- The obstruction predicate `gcd(M,N) = 1` is literally coprimality. -/
theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N :=
  Iff.rfl

/-! ## §4–§7 (CRT / primewise) — Prop 4.4 / Thm 4.20 / Prop 7.7.
    `Tor₁(ℤ/M, ℤ/N) ≅ ⊕_{q∣N} ℤ/q^{min(v_q M, v_q N)}`: the primewise exponent
    at each prime `q` is `min(v_q M, v_q N)`, i.e. `factorization_gcd_apply`. -/

theorem primewise_exponent {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (q : ℕ) :
    (Nat.gcd M N).factorization q = min (M.factorization q) (N.factorization q) :=
  factorization_gcd_apply hM hN q

/-! ## Worked examples (Example 4.5 and the discrepancy), checked by `decide`/`norm_num`. -/

section Examples
/-- Example 4.5: `gcd(12, 3²) = 3`, so `Tor₁(ℤ/12, ℤ/9) ≅ ℤ/3`. -/
example : Nat.gcd 12 (3 ^ 2) = 3 := by norm_num
/-- `|Tor₁| = 3 = 3^{min(1,2)}`. -/
example : (3 : ℕ) ^ min 1 2 = 3 := by decide
/-- Example C: `gcd(12, 5) = 1`, so `Tor₁ = 0` (obstruction-free). -/
example : Nat.gcd 12 5 = 1 := by norm_num
/-- Example B-type: `gcd(147, 7⁴) = 49`, so `|Tor₁| = 49`. -/
example : Nat.gcd 147 (7 ^ 4) = 49 := by norm_num

/-- The min/max discrepancy on Example 4.5 (`M=12, p=3, k=2`):
    the intersection generator is `lcm 12 9 = 36` with `3`-thickness `2 = max(1,2)`,
    whereas the paper's formula gives `ε₃ = min(1,2) = 1`. -/
example : Nat.lcm 12 9 = 36 := by norm_num
example : (9 : ℕ) ∣ Nat.lcm 12 9 := by norm_num        -- 3² ∣ intersection
example : ¬ (27 : ℕ) ∣ Nat.lcm 12 9 := by norm_num      -- 3³ ∤ intersection ⇒ v₃ = 2
example : ¬ (9 : ℕ) ∣ 12 := by norm_num                 -- 3² ∤ M ⇒ v₃(M) = 1, min = 1
example : min 1 2 = 1 := by decide
example : max 1 2 = 2 := by decide

/-- Thm 4.1 mechanism (Example 4.5): the kernel of `×12` on `ℤ/9` is `{0,3,6}`,
    of order `gcd(12,9) = 3`. -/
example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by native_decide
end Examples

end Spt1
