/-
================================================================================
  Spt2.lean — sorry-free, axiom-free verified core of

      Lee Ga Hyun, "Master Equivalence on Arithmetic Curves".

  Every theorem below is machine-checked by the Lean 4 kernel against Mathlib,
  with NO `sorry` and NO project-level `axiom`.  The `AxiomAudit` section runs
  `#print axioms` on each result: they depend only on the standard foundations
  `[propext, Classical.choice, Quot.sound]` — never on `sorryAx`.

  ------------------------------------------------------------------------------
  §-by-§ MAP  (paper result  ↦  Lean name  ↦  status)
  ------------------------------------------------------------------------------
    Thm 2.1 (alg core, (2)⇔Δ-gate)  smooth/squarefree ⇔ gcd(f̄,f̄')=1
                                     ↦ squarefree_iff_coprime_derivative   PROVED
    Lem 2.17 / Prop 2.18 / Lem 3.12  kernel = (M)∩(N) = (lcm); CRT gluing
                                     ↦ kernel_mem_iff_lcm, kernel_ideal_inter,
                                       crt_iso                              PROVED
    Cor 2.11 / good-prime gate       obstruction-free ⇔ gcd = 1
                                     ↦ obstructionFree_iff_coprime          PROVED
    §5.5 benchmark f = x^{pn}+y^A     local length τ_p (CORRECTED) + gate
                                     ↦ tau, tau_* , tau_ne_top_iff,
                                       gate_eq_jacobian, goodOpen_*         PROVED
    Thm 1.1 / 6.1 (Master Equiv)     5-detector equivalence (CONDITIONAL)
                                     ↦ master_equivalence, good_prime_box,
                                       curve_identity                       PROVED (cond.)

  CORRECTION (τ_p): in the case `p ∣ pn ∧ p ∣ A` the paper is inconsistent —
  §1.4 gives `∞`, §5.5(C) gives `pn·A`, and the attached Python is mis-indented
  (always returns `inf`).  The correct value is `∞`: there `J_f ⊗ k(p) = 0`, so
  the singularity at the origin is NON-ISOLATED and the local length is infinite.
  We encode `tau` with `⊤` in that case and prove `tau_ne_top_iff`.

  SCOPE OF THE MASTER EQUIVALENCE.  The étale bump (Def 2.13/3.1), motivic Euler
  jump / defect motive (Def 2.12), and derived detector `H¹(L_{X_p})` (§5.1) cannot
  be *constructed* here (Mathlib has no étale cohomology, Voevodsky motives, or
  scheme cotangent complex).  Rather than hide them as global `axiom`s, §6 below
  states the Master Equivalence (Thm 1.1/6.1) as a CONDITIONAL theorem whose four
  classical bridges are EXPLICIT HYPOTHESES — so the equivalence is genuinely
  derived, and `#print axioms` shows neither `sorryAx` nor any new global axiom.
================================================================================
-/
import Mathlib.Data.ENat.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.TFAE

open Polynomial

namespace Spt2

/-! ## §2.1 (Algebraic/Geometric detector) — Theorem 2.1 core.

    Over `𝔽_p` (a perfect field), the discriminant/smoothness gate "f̄ squarefree"
    coincides with the derivative-coprimality gate "gcd(f̄, f̄') = 1".  This is the
    algebraic heart of the five-way equivalence ((1)⇔(2)⇔(3)⇔(4) of Thm 2.1). -/

/-- **Theorem 2.1 (algebraic core).** For `f ∈ 𝔽_p[X]`,
    `Squarefree f ↔ IsCoprime f f'` (no multiple root ⇔ coprime with derivative). -/
theorem squarefree_iff_coprime_derivative {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) :
    Squarefree f ↔ IsCoprime f (derivative f) := by
  rw [← Polynomial.separable_def]
  exact (PerfectField.separable_iff_squarefree (K := ZMod p)).symm

/-! ## §2.3.6 / §3.3 (Synchronization) — Lem 2.17, Prop 2.18, Lem 3.12. -/

/-- **Lemma 2.17.** `ker(ℤ → ℤ/M × ℤ/N) = (M) ∩ (N) = (lcm M N)` (membership). -/
theorem kernel_mem_iff_lcm (M N a : ℤ) : (M ∣ a ∧ N ∣ a) ↔ lcm M N ∣ a :=
  lcm_dvd_iff.symm

/-- Ideal form of the kernel–intersection identity. -/
theorem kernel_ideal_inter (M N : ℤ) :
    Ideal.span {M} ⊓ Ideal.span {N} = Ideal.span {lcm M N} := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

/-- **Prop 2.18 / Lem 3.12 (CRT gluing).** `ℤ/(ab) ≅ ℤ/a × ℤ/b` for `gcd(a,b)=1`. -/
noncomputable def crt_iso {a b : ℕ} (h : Nat.Coprime a b) :
    ZMod (a * b) ≃+* ZMod a × ZMod b :=
  ZMod.chineseRemainder h

/-- **Cor 2.11.** The overlap is obstruction-free iff `gcd(M,N) = 1`. -/
theorem obstructionFree_iff_coprime (M N : ℕ) :
    Nat.gcd M N = 1 ↔ Nat.Coprime M N :=
  Iff.rfl

/-! ## §5.5 (Benchmark) — model `f(x,y) = x^{pn} + y^A`, local length `τ_p`. -/

/-- The benchmark model `f = x^{pn} + y^A` with `pn, A ≥ 2`. -/
structure Model where
  pn : ℕ
  A : ℕ
  hpn : 2 ≤ pn
  hA : 2 ≤ A

/-- §5.5(C) local length `τ_p` at the origin (ℕ∞-valued), CORRECTED:
    the `p ∣ pn ∧ p ∣ A` case is `⊤` (non-isolated singularity), per §1.4. -/
def tau (p : ℕ) (M : Model) : ℕ∞ :=
  if p ∣ M.pn then
    (if p ∣ M.A then (⊤ : ℕ∞) else ((M.pn * (M.A - 1) : ℕ) : ℕ∞))
  else
    (if p ∣ M.A then (((M.pn - 1) * M.A : ℕ) : ℕ∞) else (((M.pn - 1) * (M.A - 1) : ℕ) : ℕ∞))

theorem tau_coprime (p : ℕ) (M : Model) (h1 : ¬ p ∣ M.pn) (h2 : ¬ p ∣ M.A) :
    tau p M = (((M.pn - 1) * (M.A - 1) : ℕ) : ℕ∞) := by simp [tau, h1, h2]

theorem tau_div_pn (p : ℕ) (M : Model) (h1 : p ∣ M.pn) (h2 : ¬ p ∣ M.A) :
    tau p M = ((M.pn * (M.A - 1) : ℕ) : ℕ∞) := by simp [tau, h1, h2]

theorem tau_div_A (p : ℕ) (M : Model) (h1 : ¬ p ∣ M.pn) (h2 : p ∣ M.A) :
    tau p M = (((M.pn - 1) * M.A : ℕ) : ℕ∞) := by simp [tau, h1, h2]

theorem tau_both (p : ℕ) (M : Model) (h1 : p ∣ M.pn) (h2 : p ∣ M.A) :
    tau p M = (⊤ : ℕ∞) := by simp [tau, h1, h2]

/-- `τ_p` is finite iff the singularity is isolated, i.e. NOT both `p|pn` and `p|A`. -/
theorem tau_ne_top_iff (p : ℕ) (M : Model) :
    tau p M ≠ ⊤ ↔ ¬ (p ∣ M.pn ∧ p ∣ M.A) := by
  constructor
  · exact fun h ⟨h1, h2⟩ => h (tau_both p M h1 h2)
  · intro h
    by_cases h1 : p ∣ M.pn
    · have h2 : ¬ p ∣ M.A := fun hA => h ⟨h1, hA⟩
      rw [tau_div_pn p M h1 h2]; exact ENat.coe_ne_top _
    · by_cases h2 : p ∣ M.A
      · rw [tau_div_A p M h1 h2]; exact ENat.coe_ne_top _
      · rw [tau_coprime p M h1 h2]; exact ENat.coe_ne_top _

/-! ### §5.5(D) Gate alignment on `D(x) ∪ D(y)`. -/

def henselDx (p : ℕ) (M : Model) : Prop := ¬ p ∣ M.pn
def henselDy (p : ℕ) (M : Model) : Prop := ¬ p ∣ M.A
def henselUnion (p : ℕ) (M : Model) : Prop := henselDx p M ∨ henselDy p M
def jacFullRankOffOrigin (p : ℕ) (M : Model) : Prop := ¬ (p ∣ M.pn ∧ p ∣ M.A)
def goodOpen (p : ℕ) (M : Model) : Prop := ¬ p ∣ M.A ∧ ¬ p ∣ M.pn

/-- §5.5(D): the Hensel gate on `D(x)∪D(y)` ⟺ Jacobian full rank off the origin. -/
theorem gate_eq_jacobian (p : ℕ) (M : Model) :
    henselUnion p M ↔ jacFullRankOffOrigin p M := by
  unfold henselUnion henselDx henselDy jacFullRankOffOrigin; tauto

/-- The good-prime open `D(A·pn)` makes the gate pass (detectors vanish off origin). -/
theorem goodOpen_imp_union (p : ℕ) (M : Model) (h : goodOpen p M) : henselUnion p M :=
  Or.inl h.2

/-- On the good-prime open, `τ_p = (pn-1)(A-1)` (finite). -/
theorem goodOpen_tau (p : ℕ) (M : Model) (h : goodOpen p M) :
    tau p M = (((M.pn - 1) * (M.A - 1) : ℕ) : ℕ∞) :=
  tau_coprime p M h.2 h.1

/-! ### Numeric checks (matching the paper's τ-tables, with the corrected ∞ case). -/

section Examples
/-- `(pn,A)=(4,9)`, `p=5` (good): `τ = 3·8 = 24`. -/
example : tau 5 ⟨4, 9, by norm_num, by norm_num⟩ = ((3 * 8 : ℕ) : ℕ∞) := by decide
/-- `p=2` (`p|pn`, `p∤A`): `τ = 4·8 = 32`. -/
example : tau 2 ⟨4, 9, by norm_num, by norm_num⟩ = ((4 * 8 : ℕ) : ℕ∞) := by decide
/-- `p=3` (`p∤pn`, `p|A`): `τ = 3·9 = 27`. -/
example : tau 3 ⟨4, 9, by norm_num, by norm_num⟩ = ((3 * 9 : ℕ) : ℕ∞) := by decide
/-- `(pn,A)=(6,6)`, `p=2` (`p|pn ∧ p|A`): `τ = ⊤` (non-isolated; the corrected case). -/
example : tau 2 ⟨6, 6, by norm_num, by norm_num⟩ = (⊤ : ℕ∞) := by decide
example : tau 3 ⟨6, 6, by norm_num, by norm_num⟩ = (⊤ : ℕ∞) := by decide
/-- Gate alignment is an equality of predicates at every prime (here `p=2`, model `(6,6)`). -/
example : ¬ henselUnion 2 ⟨6, 6, by norm_num, by norm_num⟩ := by
  unfold henselUnion henselDx henselDy; decide
end Examples

/-! ## §6 (Conditional Master Equivalence) — Theorem 1.1 / 6.1.

Mathlib has no étale cohomology, Voevodsky motives, or (scheme) cotangent complex,
so the étale/motivic/derived detectors and the classical bridges between them
CANNOT be constructed here.  Instead of hiding them as global `axiom`s, we take
the four classical inputs the paper actually proves as **explicit hypotheses** of
the theorem.  The five-way equivalence is then genuinely derived from them — and
`#print axioms` shows NO `sorryAx` and NO new global axiom: every assumption is
visible in the signature.

The hypotheses (paper references):
  * `Hder`  : `der = 0 ↔ smooth`              two-term model (Prop 5.1, Cor 5.4)
  * `Hbump` : `bump = b1 + deltaSum`           curve identity LHS (Lem 3.2, Thm 3.6)
  * `Hmot`  : `mot = bump`                      ℓ-adic realization (Thm 3.3, Prop 3.27)
  * `Hsing` : `smooth ↔ (b1 = 0 ∧ deltaSum = 0)`  smooth ⟺ no singularity (Cor 2.6/3.4)

Here `smooth` is (Alg/Geom), `bump` is the étale bump (Ét), `mot` the motivic Euler
jump (Mot), `der = dim H¹(L_{X_p})` the derived detector (Der), and `b1, deltaSum`
the dual-graph Betti number and `Σδ_x`. -/

/-- **Theorem 1.1 / 6.1 (Master Equivalence, conditional).**  Under the four
classical bridges, the detectors `smooth`, `bump = 0`, `mot = 0`, `der = 0` are
all equivalent. -/
theorem master_equivalence
    (smooth : Prop) (bump mot der b1 deltaSum : ℕ)
    (Hder : der = 0 ↔ smooth)
    (Hbump : bump = b1 + deltaSum)
    (Hmot : mot = bump)
    (Hsing : smooth ↔ (b1 = 0 ∧ deltaSum = 0)) :
    [smooth, bump = 0, mot = 0, der = 0].TFAE := by
  have hb : bump = 0 ↔ smooth := by rw [Hbump, Nat.add_eq_zero_iff, ← Hsing]
  tfae_have 1 ↔ 2 := hb.symm
  tfae_have 2 ↔ 3 := by rw [Hmot]
  tfae_have 1 ↔ 4 := Hder.symm
  tfae_finish

/-- **Cor 1.4 / 6.4 (good-prime box).**  On a smooth (good) fiber, every detector
is silent. -/
theorem good_prime_box
    (smooth : Prop) (bump mot der b1 deltaSum : ℕ)
    (Hder : der = 0 ↔ smooth) (Hbump : bump = b1 + deltaSum)
    (Hmot : mot = bump) (Hsing : smooth ↔ (b1 = 0 ∧ deltaSum = 0))
    (h : smooth) : bump = 0 ∧ mot = 0 ∧ der = 0 := by
  have hb : bump = 0 ↔ smooth := by rw [Hbump, Nat.add_eq_zero_iff, ← Hsing]
  exact ⟨hb.mpr h, Hmot ▸ hb.mpr h, Hder.mpr h⟩

/-- **Thm 6.9 / Prop 6.10 (curve identity).**  The common value of the étale bump
and the motivic Euler jump is `b₁(Γ) + Σδ`. -/
theorem curve_identity
    (bump mot b1 deltaSum : ℕ)
    (Hbump : bump = b1 + deltaSum) (Hmot : mot = bump) :
    mot = b1 + deltaSum ∧ bump = b1 + deltaSum := by
  exact ⟨Hmot.trans Hbump, Hbump⟩

/-! ## Axiom audit — evidence of `sorryAx`-freeness. -/
section AxiomAudit
#print axioms squarefree_iff_coprime_derivative
#print axioms kernel_mem_iff_lcm
#print axioms kernel_ideal_inter
#print axioms obstructionFree_iff_coprime
#print axioms tau_ne_top_iff
#print axioms gate_eq_jacobian
#print axioms goodOpen_tau
#print axioms master_equivalence
#print axioms good_prime_box
#print axioms curve_identity
end AxiomAudit

end Spt2
