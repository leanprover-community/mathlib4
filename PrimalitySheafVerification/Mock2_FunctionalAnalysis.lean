/-
================================================================================
  Mock2_FunctionalAnalysis.lean — UNCONDITIONAL Hilbert-space results for

      Lee Ga Hyun, "Global Poincaré Matching and Kloosterman-Compatible Test
                     Kernels for Half-Integral Weight Mock-Theta Gauge Objects".

  These are the genuine functional-analytic results (Prop 1 Cauchy–Schwarz/Hölder
  and Lemma 1.1 Lax–Milgram), proved OUTRIGHT in Mathlib's inner-product-space /
  Lax–Milgram library — NO `sorry`, NO `axiom`, NO hypotheses beyond the standard
  Hilbert-space structure.  (Earlier these were omitted only because the
  `InnerProductSpace`/`LaxMilgram` modules were not yet built in this checkout;
  now they are.)

  §-by-§ MAP
    Prop 1 (Cauchy–Schwarz / dual Hölder bound on `H¹_{1/2}`)
                                  ↦ cauchy_schwarz, dual_holder           GENUINE (uncond.)
    Lemma 1.1 (Lax–Milgram: coercive form ⇒ unique representing iso)
                                  ↦ lax_milgram                           GENUINE (uncond.)
================================================================================
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

open scoped RealInnerProductSpace
open InnerProductSpace

namespace Mock2FA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Prop 1 (Cauchy–Schwarz).** On the weighted automorphic inner-product space
    `H¹_{1/2}`, `|⟪u, v⟫| ≤ ‖u‖·‖v‖`. -/
theorem cauchy_schwarz (u v : E) : ‖⟪u, v⟫_ℝ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v

/-- **Prop 1 (dual Hölder bound).** A bounded functional `f ∈ V'` satisfies
    `|⟪f, v⟫_{V',V}| ≤ ‖f‖·‖v‖`. -/
theorem dual_holder (f : E →L[ℝ] ℝ) (v : E) : ‖f v‖ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v

/-- **Lemma 1.1 (Lax–Milgram).** On a real Hilbert space, every continuous coercive
    bilinear form `B` is represented by a (unique) continuous linear isomorphism
    `φ`: `⟪φ v, w⟫ = B v w` for all `v, w`.  This is the existence/uniqueness step
    of the variational formulation (Step 3 of the paper). -/
theorem lax_milgram [CompleteSpace E] (B : E →L[ℝ] E →L[ℝ] ℝ) (coercive : IsCoercive B) :
    ∃ φ : E ≃L[ℝ] E, ∀ v w : E, ⟪φ v, w⟫_ℝ = B v w :=
  ⟨coercive.continuousLinearEquivOfBilin, coercive.continuousLinearEquivOfBilin_apply⟩

/-! ## Axiom audit. -/
section AxiomAudit
#print axioms cauchy_schwarz
#print axioms dual_holder
#print axioms lax_milgram
end AxiomAudit

end Mock2FA
