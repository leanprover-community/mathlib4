import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Complex

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals


## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

Availability of other theorems used in the proof:
- 3.14: compactly supported continuous functions are dense in `L^p`
(depends on 3.13 `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`, this is written only for
`NormalSpace α` and approximation given by bounded functions)
- 6.12: polar decomposition of a complex measure
(the Jordan decomposition `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` is
available for `SignedMeasure`. need to write it as a `rnDeriv`, and make it also for
`ComplexMeasure`)
- 6.13: total variation (`MeasureTheory.SignedMeasure.totalVariation`) is equal to integral (short
proof which depends on 6.12)
- 6.16: Duality of `L^1` and `L^∞` (not in Mathlib [https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Lp.20duality/near/495207025])
-/

section TotalVariation

open MeasureTheory BigOperators ENNReal

variable {X : Type*} [MeasurableSpace X]
  {V 𝕜 : Type*} [SeminormedAddCommGroup V]  (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 V]
  (μ : VectorMeasure X V)

noncomputable def supOuterMeasure : OuterMeasure X where
  measureOf (s : Set X) :=
    ⨅ t ∈ {t' : Set X | MeasurableSet t' ∧ s ⊆ t'},
      ⨆ E ∈ {E' : ℕ → Set X | Pairwise (Function.onFun Disjoint E') ∧
             ⋃ n, E' n = t},
      ∑' n, ENNReal.ofReal ‖μ (E n)‖
  empty := by
    simp only [Set.empty_subset, and_true, Set.mem_setOf_eq]
    apply le_antisymm
    · apply le_trans (biInf_le _ MeasurableSet.empty)
      simp only [Set.iUnion_eq_empty, nonpos_iff_eq_zero, iSup_eq_zero, ENNReal.tsum_eq_zero,
        and_imp]
      intro _ _ hEempty n
      simp [hEempty n]
    · simp
  mono {s₁ s₂} h := by
    simp only [Set.mem_setOf_eq, le_iInf_iff, and_imp]
    intro t ht hst
    have ht' : t ∈ {t' : Set X | MeasurableSet t' ∧ s₁ ⊆ t'} := by
      rw [Set.setOf_and]
      exact ⟨ht, (Set.Subset.trans h hst)⟩
    apply le_trans (biInf_le _ ht')
    exact le_of_eq rfl
  iUnion_nat := by
    sorry

noncomputable def supTotalVariation : Measure X :=
  { (supOuterMeasure μ).trim with
    m_iUnion := sorry
    -- countable additivity for measurable sets, follow Rudin
    -- use `OuterMeasure.trim_eq` for measurable sets
    trim_le := le_of_eq (OuterMeasure.trim_trim (supOuterMeasure μ)) }

/-- **Theorem**
Let `Φ` be a linear functional on `C_0(X, ℂ)`. Suppsoe that `μ`, `μ'` are complex Borel measures
such that, `∀ f : C_0(X, ℂ)`, `Φ f = ∫ x, f x ∂μ` and `Φ f = ∫ x, f x ∂μ'`. Then `μ = μ'`. -/
theorem uniqueness : True := sorry

-- **Proof** [Rudin 87, Theorem 6.19]
-- Suppose `μ` is a regular complex Borel measure on `X`
-- and that `∫ f dμ = 0` for all `f \in C_0(X)`.
-- *Theorem 6.12* gives a Borel function `h`, such that `|h| = 1` and `dμ = h d|μ|`.
-- For any sequence `{f_n}` in `C_0(X)` we then have
-- `|μ|(X) = \int_X (\bar{h} - f_n) h`, `d|μ| ≤ \int_X |\bar{h} - f_n| \, d|μ|`.
-- Since `C_c(X)` is dense in `L^1(|μ|)` (*Theorem 3.14*), `\{f_n\}` can be
-- so chosen that the last expression in the above tends to 0 as `n → \infty`.
-- Thus `|μ|(X) = 0`, and `μ = 0`.
-- It is easy to see that the difference of two regular complex Borel measures on `X` is regular.


section ComplexRMK

open NNReal
open ZeroAtInfty MeasureTheory CompactlySupported CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

-- TO DO: define `norm` as a `ContinuousMap` and use `norm ∘ f` in the following instead of the
-- `absOfFunc X f` hack.
def absOfFunc₀ (f : C₀(X, ℂ)) : C₀(X, ℝ) := sorry
def absOfFunc_c (f : C_c(X, ℂ)) : C_c(X, ℝ) := sorry

-- TO DO: figure out using this coercial directly in the argument.
def toZeroAtInftyContinuousMap : C_c(X, ℂ) → C₀(X, ℂ) := fun f ↦ (f : C₀(X, ℂ))
def toZeroAtInftyContinuousMap' : C_c(X, ℝ) → C₀(X, ℝ) := fun f ↦ (f : C₀(X, ℝ))

noncomputable def identity : C_c(X, ℝ≥0) → C_c(X, ℝ) := CompactlySupportedContinuousMap.toReal

-- TO DO: define the identity between the ℝ and ℂ spaces of continuous functions,
-- similar to `CompactlySupportedContinuousMap.toReal`.
def toComplex : C_c(X, ℝ) → C_c(X, ℂ) := by sorry


/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that, `∀ f : C₀(X, ℂ)`, `|Φ f| ≤ Λ |f|` and `Λ |f| ≤ ‖f‖` (`‖⬝‖` denotes
the supremum norm). [Rudin 87, part of proof of Theorem 6.19] -/
theorem exists_pos_lin_func : ∃ (Λ : C₀(X, ℝ) →L[ℝ] ℝ), ∀ (f : C₀(X, ℂ)),
    ‖Φ f‖ ≤ Λ (absOfFunc₀ f) ∧ Λ (absOfFunc₀ f) ≤ ‖f‖ := by

  -- If `f ∈` [class of all nonnegative real members of `C_c(X, ℝ)`],
  -- define `Λ f = \sup { |Φ(h)| : h ∈ C_c(X, ℂ), |h| ≤ f }`.
  let U (f : C_c(X, ℝ≥0)) := toZeroAtInftyContinuousMap '' {h : C_c(X, ℂ) | ∀ x : X, ‖h x‖ ≤ f x}
  let Λ' (f : C_c(X, ℝ≥0)) := sSup (norm '' (Φ '' U f))

  -- Then `Λ f ≥ 0`, `Λ` satisfies the two required inequalities,
  have (f : C_c(X, ℝ≥0)) : 0 ≤ Λ' f := by
    -- because it is the sup of nonnegative quantities
    sorry
  have (f : C_c(X, ℝ≥0)) : ‖Φ (toComplex (f.toReal))‖ ≤ Λ' f := by
    sorry
  have (f : C_c(X, ℝ≥0)) : Λ' f ≤ ‖toZeroAtInftyContinuousMap' f.toReal‖ := by
    sorry

  -- `0 ≤ f_1 ≤ f_2` implies `Λ f_1 ≤ Λ f_2`, and `Λ (cf) = c Λ f` if `c` is a positive constant.

  -- We have to show that
  -- (10) `Λ(f + g) = Λ f + Λ g` whenever `f, g ∈ C_c^+(X)`,
  -- and we then have to extend `Λ` to a linear functional on `C_c(X, ℝ)`.
  -- Fix `f` and `g \in C_c^+(X)`.
  -- If `ε > 0`, there exist `h_1, h_2 \in C_c(X, ℝ)` such that `|h_1| ≤ f`, `|h_2| ≤ g`,
  -- `Λ f ≤ |Φ(h_1)| + ε`, `Λ g ≤ |Φ(h_2)| + ε`.
  -- There are complex numbers `α_i`, `|α_i| = 1`, so that `α_i Φ(h_i) = |Φ(h_i)|`, `i = 1, 2`.
  -- Then
  -- `Λ f + Λ g ≤ |Φ(h_1)| + |Φ(h_2)| + 2ε`
  -- `_ = Φ(α_1 h_1 + α_2 h_2) + 2ε`
  -- `_ ≤ Λ(|h_1| + |h_2|) + 2ε`
  -- `_ ≤ Λ(f + g) + 2ε`
  -- so that the inequality `≥` holds in (10).
  -- Next, choose `h ∈ C_c(X)`, subject only to the condition `|h| ≤ f + g`,
  -- let `V = { x : f(x) + g(x) > 0 }`, and define
  -- `h_1(x) = \frac{f(x) h(x)}{f(x) + g(x)}`,
  -- `h_2(x) = \frac{g(x) h(x)}{f(x) + g(x)}` when `x ∈ V`,
  -- `h_1(x) = h_2(x) = 0` when `x ∉ V`.
  -- It is clear that `h_1` is continuous at every point of `V`.
  -- If `x_0 ∉ V`, then `h(x_0) = 0`;
  -- since `h` is continuous and since `|h_1(x)| ≤ |h(x)|` for all `x ∈ X`,
  -- it follows that `x_0` is a point of continuity of `h_1`.
  -- Thus `h_1 \in C_c(X)`, and the same holds for `h_2`.
  -- Since `h_1 + h_2 = h` and `|h_1| ≤ f`, `|h_2| ≤ g`, we have
  -- `|Φ(h)| = |Φ(h_1) + Φ(h_2)| ≤ |Φ(h_1)| + |Φ(h_2)| ≤ Λ f + Λ g`.
  -- Hence `Λ(f + g) ≤ Λ f + Λ g`, and we have proved (10).
  -- If `f` is now a real function, `f \in C_c(X)`, then `2f^+ = |f| + f`,
  -- so that `f^+ \in C_c^+(X)`;
  -- likewise, `f^- \in C_c^+(X)`; and since `f = f^+ - f^-`, it is natural to define
  -- `Λ f = Λ f^+ - Λ f^- ` for `f \in C_c(X)`, `f` real
  -- and
  -- `Λ(u + iv) = Λ u + i Λ v`.
  -- Simple algebraic manipulations, just like those which occur in the proof of
  -- Theorem 1.32, show now that our extended functional `Λ` is linear on `C_c(X)`.

  sorry


variable [MeasurableSpace X] [BorelSpace X]

/-- **Theorem**
Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. Then (1) there exists a complex Borel measure
`μ` such that, `∀ f : C₀(X, ℂ)`, `Φ f = ∫ x, f x ∂μ`, (2) `‖Φ‖ = |μ|(X)`. -/
theorem Complex.integral_rieszMeasure : True := by
  -- ∃ (μ : ComplexMeasure X), ∀ (f : C₀(X, ℂ)),
  --  Φ f = ∫ x, f x ∂μ
  --  ∧ ‖Φ‖ = ComplexMeasureMeasure.totalVariation μ X
  -- TO DO: define `ComplexMeasureMeasure.totalVariation`
  -- TO DO: define `ComplexMeasure.integral`, maybe in general `VectorMeasure.integral`

  -- **Proof** [Rudin 87, Theorem 6.19]
  -- Assume `‖Φ‖ = 1`, without loss of generality.
  -- *Part 1:*
  -- Using `exists_pos_lin_func` we obtain a *positive* linear functional `Λ` on `C_c(X)`, such that
  -- (4) `|Φ(f)| ≤ Λ(|f|) ≤ ‖f‖` for all `f \in C_c(X))`.
  -- Once we have this `Λ`, we associate with it a positive Borel measure `λ`, given by
  -- have := RealRMK.integral_rieszMeasure
  -- `RealRMK.rieszMeasure hΛ` and which is a representation by `RealRMK.integral_rieszMeasure`.
  -- It also implies that `λ` is regular if `λ(X) < \infty`.
  -- Since `Λ(X) = \sup {Λ f : 0 ≤ f ≤ 1, f \in C_c(X)}`
  -- and since `|Λ f| ≤ 1` if `‖f‖ ≤ 1`, we see that actually `λ(X) ≤ 1`.
  -- We also deduce from (4) that
  -- `|Φ(f)| ≤ Λ(|f|) = ∫_X |f| dλ = ‖f‖_1`, `f \in C_c(X))`.
  -- The last norm refers to the space `L^1(λ)`.
  -- Thus `Φ` is a linear functional on `C_c(X)` of norm at most 1, with respect to the `L^1(λ)`-norm
  -- on `C_c(X)`.
  -- There is a norm-preserving extension of `Φ` to a linear functional on `L^1(λ)`, and therefore
  -- *Theorem 6.16* (the case `p = 1`) gives a Borel function `g`, with `|g| ≤ 1`, such that
  -- (6) `Φ(f) = ∫_X fg dλ`, `f \in C_c(X)`.
  -- Each side of (6) is a continuous functional on `C_0(X)`, and `C_c(X)` is dense in `C_0(X)`.
  -- Hence (6) holds for all `f \in C_0(X)`, and we obtain the representation with `dμ = g dλ`.
  -- *Part 2:*
  -- Since `\|Φ\| = 1`, (6) shows that
  -- `∫_X |g| dλ ≥ \sup { |Φ(f)| : f \in C_0(X), ‖f‖ ≤ 1 } = 1`.
  -- We also know that `λ(X) ≤ 1` and `|g| ≤ 1`.
  -- These facts are compatible only if `λ(X) = 1` and `|g| = 1` a.e. `[λ]`.
  -- Thus `d|μ| = |g| dλ = dλ`, by *Theorem 6.13*,
  -- and `|μ|(X) = λ(X) = 1 = ‖Φ‖`,
  sorry


end ComplexRMK
