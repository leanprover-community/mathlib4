# Verification of *"Primality Sheaf via Local Filters and Derived Equalizers"*

Lean 4 / Mathlib formalisation of the algebraic core of the paper by **Lee ga Hyun**
(September 2025).

- Lean file: [`Verification.lean`](./Verification.lean)
- Target: Mathlib (toolchain `leanprover/lean4:v4.30.0-rc1`, as pinned by the repo's
  `lean-toolchain`).

## How to check

```bash
# from the repository root, with the Mathlib build cache available
lake env lean PrimalitySheafVerification/Verification.lean
```

A successful run with no errors means every theorem and `example` in the file has
been machine-checked by the Lean kernel.

> **Authoring note.** No Lean toolchain was installed in the environment where this
> was written, so the file was authored against the *vendored Mathlib source*
> (every lemma name was checked against `Mathlib/…`) but not compiled there.
> Please run the command above to confirm.

---

## 1. Complete catalogue of the paper's statements

Numbering follows the manuscript (which restarts the counter in places).

| # | Kind | Short name |
|---|------|-----------|
| Thm 2.1 | Theorem | MtA-linearization for the canonical Sₖ-expansion |
| Rmk 2.2 | Remark | Uniform remainder, certification of (Hₖ) |
| Lem 2.3 | Lemma | 1-Lipschitz log and uniform remainder |
| Prop 2.4 | Proposition | Achievability of (Hₖ) for `q = pⁿ` |
| Prop 2.5 | Proposition | `q`-dependent uniform parameter design |
| Lem 2.6 | Lemma | Kernel as ideal intersection (`ker Φ = (M)∩(pᵏ) = (lcm)`) |
| Rmk 2.7 | Remark | Common residue fiber and support |
| Rmk 2.8 | Remark | Local thickness and stability |
| Cor 2.9 | Corollary | Unobstructed overlaps (`gcd = 1 ⇒` glue) |
| Lem 2.10 | Lemma | Local thickness `ε_p = min(v_p M, k)` |
| Def 2.11 | Definition | Common residue fiber and thickness index |
| Cor 2.12 | Corollary | Unobstructed region |
| Rmk 2.13 | Remark | Stability under base change |
| Prop 2.14 | Proposition | Zero-Class Decision Rule |
| Thm 4.1 | Theorem | `Tor₁^ℤ(ℤ/M, ℤ/pᵏ) ≅ ℤ/gcd(M,pᵏ)` |
| Cor 4.2 | Corollary | Obstruction-free ⟺ Tor-vanishing |
| Lem 4.3 | Lemma | Bridge from equalizer to Tor₁ |
| Prop 4.4 | Proposition | CRT stability and primewise decomposition |
| Ex 4.5 | Example | `Tor₁(ℤ/12, ℤ/9) ≅ ℤ/3` |
| Lem 4.6 | Lemma | Stability box |
| Prop 4.7 | Proposition | Equalizer kernel and support |
| Lem 4.8 | Lemma | Localized thickness |
| Prop 4.9 | Proposition | Stalk calculation |
| Rmk 4.10 | Remark | Completion-ready constraints |
| Def 4.11 | Definition | Common residue fiber |
| Thm 4.12 | Theorem | Obstruction-free criterion (4 equivalences) |
| Def 4.13 | Definition | Primewise / composite descriptions |
| Lem 4.14 | Lemma | CRT as a fiber product |
| Rmk 4.15 | Remark | Compatibility of congruence and modular layer |
| Prop 4.16 | Proposition | Primewise ⟺ composite |
| Cor 4.17 | Corollary | Monotonicity under restriction |
| Prop 4.18 | Proposition | Equalizer kernel/support invariant under CRT refinement |
| Lem 4.19 | Lemma | Failure locus & thickness stable under refinement |
| Thm 4.20 | Theorem | Primewise/CRT decomposition of Tor₁ |
| Cor 4.21 | Corollary | Stability of obstruction magnitudes |
| Rmk 4.22 | Remark | Base-change / restriction stability |
| Thm 5.1 | Theorem | Base-change stability of the failure sheaf |
| Lem 5.2 | Lemma | Localized thickness |
| Def 5.3 | Definition | Common residue fiber |
| Prop 5.4 | Proposition | Stalk and "obstruction-free" locus |
| Rmk 5.5 | Remark | Compatibility with `p`-adic completion |
| Lem 6.1 | Lemma | Pairwise independence on principal opens |
| Thm 6.2 | Theorem | Terminal / minimal amalgam |
| Rmk 6.3 | Remark | Bridge to obstruction narrative |
| Fact 7.1 | Fact | Equalizer kernel and support (recap) |
| Fact 7.2 | Fact | CRT decomposition of Tor₁ (recap) |
| Lem 7.3 | Lemma | No redundant predicate |
| Cor 7.4 | Corollary | Terminal / minimal amalgam (reprise) |
| Prop 7.5 | Proposition | Restriction/completion/base-change stability |
| Def 7.6 | Definition | Indicator complexity `IC(M;N)` |
| Prop 7.7 | Proposition | `|Tor₁| = ∏ q^{min} = exp(IC)` |
| Cor 7.8 | Corollary | Stability of indicator complexity |
| Prop 7.9 | Proposition | Obstruction = equalizer kernel on common fiber |
| Prop 7.10 | Proposition | Sectionwise equalizer model |
| Cor 7.11 | Corollary | Bridge to §4.4 |

## 2. Logical dependency order

The paper has **one arithmetic spine** plus two analytic/categorical side-branches.

```
                       gcd · lcm = M·N   (gcd_mul_lcm_eq, §A)
                                │
   Lem 2.6 = Prop 4.7 = Fact 7.1: ker(ℤ→ℤ/M×ℤ/pᵏ) = (M)∩(pᵏ) = (lcm)   [§A]
                                │
          ┌─────────────────────┼───────────────────────────┐
          ▼                     ▼                            ▼
 Lem 2.10/4.8/5.2:      Rmk 2.7 / Def 2.11/4.11/5.3:   Thm 4.1: Tor₁ ≅ ℤ/gcd  [§C]
 thickness ε_p          common residue fiber                  │
 (gcd/lcm valuations)   Spec ℤ/gcd                            ▼
        [§B]                                       Cor 4.2 = Thm 4.12 (iv):
          │                                        gcd=1 ⟺ Tor₁=0   [§C]
          ▼                                                   │
 Cor 2.9/2.12, Prop 5.4: unobstructed locus        ┌──────────┴───────────┐
          │                                         ▼                      ▼
          ▼                              Prop 4.4 = Thm 4.20 = Fact 7.2:  Lem 4.3
 Prop 2.14 (Zero-Class Rule)            primewise CRT decomposition       (equalizer↔Tor)
                                         Tor₁ ≅ ⊕ ℤ/q^{min}   [§D]
                                                  │
                                                  ▼
                                  Def 7.6 / Prop 7.7: |Tor₁| = exp(IC)   [§E]
                                                  │
                                                  ▼
                                  Cor 4.21 / Cor 7.8: stability of IC

  Side-branch I  (analytic, feeds the modular/p-adic faces of §A):
     Prop 2.4 / 2.5  ──▶  hypothesis (Hₖ)  ──▶  Thm 2.1 / Lem 2.3 (p-adic log gate)
                                              ──▶ congruence (4) used in §2.3 bridge

  Side-branch II (categorical, packaging of §A–§E into a sheaf):
     Lem 6.1 (pairwise independence) ──▶ Thm 6.2 / Cor 7.4 (terminal/minimal amalgam)
     Lem 7.3 (no redundancy) ──▶ Prop 7.9 (obstruction = kernel on fiber)
     Stability: Rmk 2.8/2.13, Lem 4.6, Thm 5.1, Prop 7.5  (uniform "stability box")
```

Foundational, everything-else-depends-on-it: **Lem 2.6** (= Prop 4.7 = Fact 7.1) and
**Thm 4.1**. The "stability box" lemmas (Rmk 2.8/2.13, Lem 4.6, Thm 5.1, Prop 7.5,
Rmk 4.22) are independent restatements of "valuations/kernels commute with
localization & completion" and are reused throughout.

## 3. What is formalised (`Verification.lean`)

| Paper result | Lean name |
|---|---|
| Lem 2.6 / Prop 4.7 / Fact 7.1 (membership) | `equalizer_mem_iff` |
| Lem 2.6 / Prop 4.7 / Fact 7.1 (ideals) | `equalizer_ideal_inter` |
| `gcd·lcm = M·N` | `gcd_mul_lcm_eq` |
| Lem 4.8 / 5.2 (lcm valuation, general) | `factorization_lcm_apply` |
| Def 2.11 thickness `min` (gcd valuation, general) | `factorization_gcd_apply` |
| Lem 2.10 prime-power lcm thickness = **max** | `lcm_thickness_prime_pow` |
| Lem 2.10 prime-power gcd thickness = **min** | `gcd_thickness_prime_pow` |
| Thm 4.1 RHS — `|ℤ/gcd| = gcd` | `commonResidueFiber_card` |
| Cor 4.2 / Thm 4.12 — obstruction-free ⟺ trivial | `obstructionFree_iff_card` |
| Thm 4.12(i) — `gcd = 1` ⟺ coprime | `obstructionFree_iff_coprime` |
| Prop 4.4 / Thm 4.20 / Prop 7.7 — primewise exponent | `primewise_exponent` |
| Ex 4.5 + Prop 7.7 (`|Tor₁|`) | `Example45` section |
| Thm 4.1 mechanism (ker of `·M` on `ℤ/9`) | final `example` |

## 4. ⚠ A correctness issue found during formalisation

The paper states (Lemma 2.10, Lemma 4.8, Lemma 5.2, eq. (17), and the abstract)
that the **localised ideal intersection** has thickness

> `((M) ∩ (pᵏ))_(p) = (p^{ε_p})`, with `ε_p = min(v_p M, k)`.

This is **inconsistent** with the paper's own (correct) identity
`(M) ∩ (pᵏ) = (lcm(M, pᵏ))`: the `p`-adic valuation of an `lcm` is the **maximum**
of the valuations, so the true thickness of the intersection is
`max(v_p M, k)`, not `min(v_p M, k)`.

The minimum `min(v_p M, k)` is correct, but it is the valuation of
`gcd(M, pᵏ)` — i.e. of the **common residue fiber `ℤ/gcd`** (and of the `Tor₁`
group), which is a *different* object from the intersection ideal.

The file proves both valuations separately (`lcm_thickness_prime_pow` →
`max`, `gcd_thickness_prime_pow` → `min`) and pins the discrepancy on the
paper's own Example 4.5 data (`M = 12`, `p = 3`, `k = 2`): the intersection is
`(lcm 12 9) = (36)` with 3-adic thickness `2 = max(1,2)`, whereas the paper's
formula yields `1 = min(1,2)`.

This does **not** affect the downstream obstruction calculus, because that calculus
is driven by `gcd(M, pᵏ)` (Tor₁, the common residue fiber) — where `min` is the
right answer. Only the sentences that attach `min` to the *intersection/lcm* are
mislabelled; replacing "intersection thickness" by "common-residue-fiber thickness"
(or `min → max` for the intersection) repairs the statements.
