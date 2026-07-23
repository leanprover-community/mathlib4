/-
Copyright (c) 2026 Jon Crall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.CourantFischer

/-! # Davis–Kahan cross-block bound (elementary finite-dimensional form)

For two self-adjoint operators `T`, `S` on a finite-dimensional inner product
space that are close in operator norm, the eigenvectors associated to a
well-separated block of the spectrum are nearly orthogonal across the gap.  This
is the (squared) sin-Θ theorem of Davis and Kahan, in the most elementary
finite-dimensional packaging: a direct consequence of the spectral cross-term
identity `⟪uᵢ, (S − T) v̂ⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, v̂ⱼ⟫`
(`LinearMap.IsSymmetric.inner_eigenvectorBasis_map_sub_eigenvectorBasis`) and
Parseval, with no resolvents or contour integrals.

`Analysis/InnerProductSpace/Rayleigh` covers only the extreme eigenvalues.  Two
constants are provided: the sharp Frobenius sin-Θ bound
`‖sin Θ‖_F ≤ ‖S − T‖_F / gap` (no operator-norm hypothesis, no dimension factor),
and the crude operator-norm corollary `n ε² / gap²` obtained from it via
`‖S − T‖²_F ≤ n ε²`.

## Main results

* `LinearMap.IsSymmetric.sum_sq_norm_inner_eigenvectorBasis_map_sub_eq`: the Parseval
  identity `∑_{i,j} ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖² = ∑ⱼ ‖(S − T) v̂ⱼ‖²`, expressing the total
  off-diagonal energy as the squared Hilbert–Schmidt (Frobenius) norm of `S − T`.
* `LinearMap.IsSymmetric.sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt`:
  the sharp cross-block bound `∑_{i < d, j ≥ d} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ ‖S − T‖²_F / gap²`, with
  no operator-norm hypothesis and no dimension factor.
* `LinearMap.IsSymmetric.sum_cross_norm_inner_eigenvectorBasis_sq_le`: its crude
  operator-norm corollary `∑_{i < d, j ≥ d} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ n ε² / gap²`.
* `Orthonormal.starProjection_span_image_apply`: the orthogonal projection onto
  the span of an orthonormal subfamily is the sum of the corresponding rank-one
  projections (`Submodule.starProjection` form; holds in any inner product space).
* `OrthonormalBasis.norm_sq_sub_starProjection_span_image`: the complementary
  Parseval identity `‖x − P x‖² = ∑_{i ∉ s} ‖⟪wᵢ, x⟫‖²` for the residual of the
  projection onto the span of an orthonormal-basis subfamily.
* `OrthonormalBasis.sum_norm_sub_starProjection_span_sq_eq`: the projector
  identity — the squared Frobenius distance between the projections onto
  two orthonormal-subfamily spans is `2 ·` the cross overlap sum.
* `LinearMap.IsSymmetric.sum_norm_sub_starProjection_span_sq_le_hilbertSchmidt`: the
  sharp sin-Θ projector bound `‖P̂ − P‖_F² ≤ 2 ‖S − T‖_F² / gap²`, with
  `LinearMap.IsSymmetric.sum_norm_sub_starProjection_span_sq_le` its crude
  `2 n ε² / gap²` operator-norm corollary.

## References

* [C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*][davis_kahan_1970].
* [Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*][yu_wang_samworth_2015].
-/

public section

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

namespace LinearMap.IsSymmetric

/-! ### Eigenvector cross-block bounds -/

/-- **Parseval identity for the total cross-energy.** In the eigenbases `u` of `T` and
`v̂` of `S`, the sum of all squared off-diagonal entries of `S − T` equals the sum of the
squared column norms — the squared Hilbert–Schmidt (Frobenius) norm of `S − T`:
`∑ᵢⱼ ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖² = ∑ⱼ ‖(S − T) v̂ⱼ‖²`.  The inner sum over `i` is Parseval in the
orthonormal eigenbasis `u`.  (The right-hand side is basis-independent: it is `‖S − T‖²_F`
for any orthonormal basis in place of `v̂`.) -/
theorem sum_sq_norm_inner_eigenvectorBasis_map_sub_eq
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) :
    ∑ i : Fin n, ∑ j : Fin n,
      ‖⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜‖ ^ 2
      = ∑ j : Fin n, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ =>
    (hT.eigenvectorBasis hn).sum_sq_norm_inner_right _

/-- The squared Hilbert–Schmidt norm of an `ε`-operator-bounded `S − T` is at most `n ε²`:
each of the `n` columns `‖(S − T) v̂ⱼ‖²` is `≤ ε²` since `v̂ⱼ` is a unit vector.  This is the
one place the crude constant's dimension factor `n` is introduced. -/
theorem sum_norm_eigenvectorBasis_map_sub_sq_le
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ j : Fin n, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2 ≤ (n : ℝ) * ε ^ 2 := by
  set v := hS.eigenvectorBasis hn
  calc ∑ j : Fin n, ‖(S - T) (v j)‖ ^ 2
      ≤ ∑ _j : Fin n, ε ^ 2 := Finset.sum_le_sum fun j _ => by
        have := hε (v j); rw [v.orthonormal.1 j, mul_one] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = (n : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Total cross-energy bound.** With `T`, `S` self-adjoint and close in operator
norm (`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), the sum over all eigenvector pairs of the
squared off-diagonal entries of `S − T` is at most `n ε²`.

This is the Parseval identity `sum_sq_norm_inner_eigenvectorBasis_map_sub_eq`
followed by the columnwise bound `sum_norm_eigenvectorBasis_map_sub_sq_le`. -/
theorem sum_norm_inner_eigenvectorBasis_map_sub_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i : Fin n, ∑ j : Fin n,
      ‖⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 := by
  rw [sum_sq_norm_inner_eigenvectorBasis_map_sub_eq hT hS hn]
  exact sum_norm_eigenvectorBasis_map_sub_sq_le hS hn hε

/-- **Sharp Davis–Kahan cross-block bound (Frobenius sin-Θ).** Suppose `T`, `S` are
self-adjoint and there is a positive `gap` separating the first `d` eigenvalues of
`T` from the trailing eigenvalues of `S`
(`(i : ℕ) < d → d ≤ (j : ℕ) → gap ≤ |λᵢ(T) − λⱼ(S)|`).  Then the total squared overlap
between the leading eigenvectors of `T` and the trailing eigenvectors of `S` is bounded by
the squared Hilbert–Schmidt (Frobenius) norm of the perturbation over `gap²`:
`∑_{i < d} ∑_{d ≤ j} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ (∑ⱼ ‖(S − T) v̂ⱼ‖²) / gap²`.

There is no operator-norm hypothesis and no dimension factor: this is the sharp
`‖sin Θ‖_F ≤ ‖S − T‖_F / gap` form.  The cross-term identity
`⟪uᵢ, (S − T) v̂ⱼ⟫ = (λ̂ⱼ − λᵢ) ⟪uᵢ, v̂ⱼ⟫` gives `gap² ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖²`
on cross pairs, and the cross block is a sub-block of the full Frobenius sum
(`sum_sq_norm_inner_eigenvectorBasis_map_sub_eq`).  The crude `n ε² / gap²` bound
(`sum_cross_norm_inner_eigenvectorBasis_sq_le`) is the corollary via `‖S − T‖²_F ≤ n ε²`. -/
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ (∑ j : Fin n, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2) / gap ^ 2 := by
  set u := hT.eigenvectorBasis hn with hu
  set v := hS.eigenvectorBasis hn with hv
  -- Per-pair: `gap² ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ ‖⟪uᵢ, (S − T) v̂ⱼ⟫‖²` for cross pairs.
  have hpair : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ^ 2 * ‖⟪u i, v j⟫_𝕜‖ ^ 2 ≤ ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
    intro i j hi hj
    -- The cross-term identity turns the perturbation entry into the eigenvalue
    -- difference times the overlap.
    have hsq : ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
        = (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2 * ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
      rw [hu, hv, inner_eigenvectorBasis_map_sub_eigenvectorBasis hT hS hn i j,
        norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
    have hsqgap : gap ^ 2 ≤ (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2 := by
      rw [show (hS.eigenvalues hn j - hT.eigenvalues hn i) ^ 2
          = |hT.eigenvalues hn i - hS.eigenvalues hn j| ^ 2 by rw [sq_abs]; ring]
      exact pow_le_pow_left₀ hgap_pos.le (hgap i j hi hj) 2
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hsqgap (sq_nonneg _)
  -- Sum the per-pair bound over the cross block.
  have hcross : gap ^ 2 * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          ‖⟪u i, v j⟫_𝕜‖ ^ 2)
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    exact hpair i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  -- The cross block is a sub-block of the full Frobenius sum (all terms nonneg),
  -- which by Parseval equals the sum of squared column norms `∑ⱼ ‖(S − T) v̂ⱼ‖²`.
  have hsub : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
      ≤ ∑ i : Fin n, ∑ j : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2 :=
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun j _ _ => sq_nonneg _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun i _ _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hfull : ∑ i : Fin n, ∑ j : Fin n, ‖⟪u i, (S - T) (v j)⟫_𝕜‖ ^ 2
      = ∑ j : Fin n, ‖(S - T) (v j)‖ ^ 2 := by
    rw [hu, hv]; exact sum_sq_norm_inner_eigenvectorBasis_map_sub_eq hT hS hn
  -- Chain: gap² · CROSS ≤ full Frobenius energy = ‖S − T‖²_F.
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < gap ^ 2), mul_comm]
  exact (hcross.trans hsub).trans hfull.le

/-- **Davis–Kahan cross-block bound (crude operator-norm form).**
Suppose `T`, `S` are self-adjoint, close in operator norm
(`∀ x, ‖(S − T) x‖ ≤ ε ‖x‖`), and there is a positive `gap` separating the first
`d` eigenvalues of `T` from the trailing eigenvalues of `S`
(`(i : ℕ) < d → d ≤ (j : ℕ) → gap ≤ |λᵢ(T) − λⱼ(S)|`).  Then the total squared
overlap between the leading eigenvectors of `T` and the trailing eigenvectors of
`S` is bounded: `∑_{i < d} ∑_{d ≤ j} ‖⟪uᵢ, v̂ⱼ⟫‖² ≤ n ε² / gap²`.

Corollary of the sharp `sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt`
by degrading `‖S − T‖²_F ≤ n ε²`; the dimension factor `n` is not sharp. -/
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ (n : ℝ) * ε ^ 2 / gap ^ 2 := by
  refine (sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt
    hT hS hn d hgap_pos hgap).trans ?_
  gcongr
  exact sum_norm_eigenvectorBasis_map_sub_sq_le hS hn hε

/-! ### Rank-`d` population structure: gap from an eigenvalue floor

The common statistical setup (Yu–Wang–Samworth): the population operator `T` is
positive semidefinite of rank `d` with a spectral floor `α` on its nonzero
eigenvalues, and the sample `S` is `ε`-operator-close with `ε ≤ α / 2`.  Weyl's
inequality then pushes every trailing sample eigenvalue below `α / 2`, giving a
population eigengap of `α / 2` and a clean `4 n ε² / α²` cross-block bound. -/

/-- **Gap from rank and eigenvalue floor.**  If `T`'s leading `d` (sorted)
eigenvalues are at least `α` and its trailing eigenvalues vanish, and `S` is
`ε`-operator-close to `T` with `ε ≤ α / 2`, then every leading eigenvalue of `T`
is separated from every trailing eigenvalue of `S` by at least `α / 2`.  This is
exactly the gap hypothesis of `sum_cross_norm_inner_eigenvectorBasis_sq_le`. -/
theorem gap_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ}
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      α / 2 ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j| := by
  intro i j hi hj
  have hweyl := abs_eigenvalues_sub_le hT hS hn hε j
  rw [htail j hj, zero_sub, abs_neg] at hweyl
  have hSj : hS.eigenvalues hn j ≤ α / 2 := (le_abs_self _).trans (hweyl.trans hsmall)
  have := hα i hi
  exact (by linarith : α / 2 ≤ hT.eigenvalues hn i - hS.eigenvalues hn j).trans (le_abs_self _)

/-- **Davis–Kahan cross-block bound under rank-`d` population structure.**
Composition of `gap_of_rank_floor` with
`sum_cross_norm_inner_eigenvectorBasis_sq_le`: when `T` is positive semidefinite
of rank `d` with spectral floor `α` and `S` is `ε`-operator-close with
`ε ≤ α / 2`, the squared overlap between the leading eigenvectors of `T` and the
trailing eigenvectors of `S` is at most `4 n ε² / α²`. -/
theorem sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (d : ℕ) {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn j = 0)
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖)
    (hsmall : ε ≤ α / 2) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * (n : ℝ) * ε ^ 2 / α ^ 2 := by
  have hε' : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖ := fun x => by
    rw [LinearMap.sub_apply, ← norm_neg, neg_sub, ← LinearMap.sub_apply]; exact hε x
  have hgap := gap_of_rank_floor hT hS hn d hα htail hε' hsmall
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        ‖⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
        ≤ (n : ℝ) * ε ^ 2 / (α / 2) ^ 2 :=
          sum_cross_norm_inner_eigenvectorBasis_sq_le hT hS hn d
            (by positivity : (0 : ℝ) < α / 2) hgap hε
    _ = 4 * (n : ℝ) * ε ^ 2 / α ^ 2 := by field_simp; ring

end LinearMap.IsSymmetric

/-! ### Projector (sin-Θ) form via `Submodule.starProjection`

The cross-block sum is exactly half the squared Frobenius distance between the
orthogonal projections onto the two spectral subspaces.  The projections are
Mathlib's `Submodule.starProjection` of the spans of the selected eigenvectors,
the field is any `RCLike 𝕜`, and the selected index set is an arbitrary
`s : Finset (Fin m)` (the sorted-cutoff case is `s = {i | (i : ℕ) < d}`). -/

section Projector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! The three bridge lemmas hold for an orthonormal family in *any* inner product
space: the span of a finite subfamily is finite-dimensional, so it always carries
an orthogonal projection. -/

-- REVIEWER INPUT REQUESTED: `Orthonormal.starProjection_span_image_apply` /
-- `_apply_self` / `norm_sq_starProjection_span_image` are general orthonormal-family
-- projection facts (no Davis–Kahan content). Keep them here, or relocate to
-- `Analysis/InnerProductSpace/Projection` / an `Orthonormal` projection file?
/-- **Projection onto the span of an orthonormal subfamily.** For an orthonormal
family `w` and a finite index set `s`, the orthogonal projection onto
`span 𝕜 (w '' s)` acts as `x ↦ ∑ i ∈ s, ⟪w i, x⟫ • w i`. -/
theorem Orthonormal.starProjection_span_image_apply {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection x = ∑ i ∈ s, ⟪w i, x⟫_𝕜 • w i := by
  classical
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.sum_smul_mem _ _ fun i hi =>
      Submodule.subset_span (Set.mem_image_of_mem w (by exact_mod_cast hi))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hj' : j ∈ s := by exact_mod_cast hj
      rw [inner_sub_left, sum_inner, Finset.sum_congr rfl (fun i _ => by
        rw [inner_smul_left, orthonormal_iff_ite.mp hw i j, mul_ite, mul_one, mul_zero])]
      rw [Finset.sum_ite_eq' s j fun i => (starRingEnd 𝕜) ⟪w i, x⟫_𝕜, if_pos hj',
        inner_conj_symm, sub_self]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

/-- On a member `w k` of the orthonormal family, the projection onto
`span 𝕜 (w '' s)` keeps it iff `k ∈ s`. -/
theorem Orthonormal.starProjection_span_image_apply_self {ι : Type*} [DecidableEq ι]
    {w : ι → F} (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (k : ι) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection (w k) = if k ∈ s then w k else 0 := by
  rw [Orthonormal.starProjection_span_image_apply hw s (w k),
    Finset.sum_congr rfl (fun i _ => by
      rw [orthonormal_iff_ite.mp hw i k, ite_smul, one_smul, zero_smul]),
    Finset.sum_ite_eq' s k fun i => w i]

/-- Parseval for the projection onto the span of an orthonormal subfamily:
`‖P x‖² = ∑ i ∈ s, ‖⟪w i, x⟫‖²`. -/
theorem Orthonormal.norm_sq_starProjection_span_image {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    ‖(Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ ^ 2 = ∑ i ∈ s, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  have hcast : ((‖(Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ : ℝ) : 𝕜) ^ 2
      = ((∑ i ∈ s, ‖⟪w i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜),
      Orthonormal.starProjection_span_image_apply hw s x, _root_.Orthonormal.inner_sum hw]
    rw [Finset.sum_congr rfl fun i _ => RCLike.conj_mul ⟪w i, x⟫_𝕜]
    push_cast
    rfl
  exact_mod_cast hcast

variable [FiniteDimensional 𝕜 F] {m : ℕ}

/-- **Complementary Parseval for a projection residual.** For a subfamily of an orthonormal
*basis* `w`, the residual of the projection onto its span carries the complementary Parseval
sum: `‖x − P x‖² = ∑_{i ∉ s} ‖⟪w i, x⟫‖²`.  Companion to
`Orthonormal.norm_sq_starProjection_span_image` (`‖P x‖² = ∑_{i ∈ s}`); together they split
Parseval `‖x‖² = ∑_i ‖⟪w i, x⟫‖²` across `s` and its complement. -/
theorem OrthonormalBasis.norm_sq_sub_starProjection_span_image
    (w : OrthonormalBasis (Fin m) 𝕜 F) (s : Finset (Fin m)) (x : F) :
    ‖x - (Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ ^ 2
      = ∑ i ∈ sᶜ, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  -- `x − P x = Pᗮ x`, and `‖x‖² = ‖P x‖² + ‖Pᗮ x‖²`; subtract off `‖P x‖² = ∑_s` from
  -- Parseval `‖x‖² = ∑_i` to leave the complement sum.
  have hres : x - (Submodule.span 𝕜 (w '' ↑s)).starProjection x
      = (Submodule.span 𝕜 (w '' ↑s))ᗮ.starProjection x :=
    (Submodule.starProjection_orthogonal_val x).symm
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection x (Submodule.span 𝕜 (w '' ↑s))
  rw [Orthonormal.norm_sq_starProjection_span_image w.orthonormal s x] at hdecomp
  rw [hres]
  linarith [w.sum_sq_norm_inner_right x,
    Finset.sum_add_sum_compl s fun i => ‖⟪w i, x⟫_𝕜‖ ^ 2, hdecomp]

omit [FiniteDimensional 𝕜 F] in
/-- Symmetric block-counting identity for two orthonormal bases `u`, `v` and an
index set `s`: the squared overlaps summed over the `(sᶜ, s)` block equal those
summed over the `(s, sᶜ)` block.  Both equal `s.card` minus the leading–leading
overlap sum, by Parseval (each row of overlaps sums to `1`). -/
private theorem sum_inner_sq_compl_block_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [Finset.sum_comm]
  -- For a unit vector `w` and orthonormal basis `b`, the overlaps split as
  -- `∑_{sᶜ} = 1 − ∑_s` by Parseval.
  have key : ∀ (b : OrthonormalBasis (Fin m) 𝕜 F) (w : F), ‖w‖ = 1 →
      ∑ k ∈ sᶜ, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 - ∑ k ∈ s, ‖⟪w, b k⟫_𝕜‖ ^ 2 := by
    intro b w hw
    have hpar : ∑ k, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun k _ => by rw [norm_inner_symm],
        b.sum_sq_norm_inner_right w, hw, one_pow]
    linarith [Finset.sum_add_sum_compl s fun k => ‖⟪w, b k⟫_𝕜‖ ^ 2]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ s) => key u (v j) (v.orthonormal.1 j),
    Finset.sum_congr rfl fun i (_ : i ∈ s) => key v (u i) (u.orthonormal.1 i),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm])

/-- **Projector form of the Davis–Kahan identity.** For two orthonormal bases `u`,
`v` of a finite-dimensional inner product space over `𝕜 = ℝ, ℂ` and an index set
`s`, the squared Frobenius distance (computed in the basis `u`) between the
orthogonal projections onto `span (v '' s)` and `span (u '' s)` is twice the
cross overlap sum:
`∑ₖ ‖(P_v − P_u) uₖ‖² = 2 ∑_{i ∈ s} ∑_{j ∉ s} ‖⟪uᵢ, vⱼ⟫‖²`. -/
theorem OrthonormalBasis.sum_norm_sub_starProjection_span_sq_eq
    (u v : OrthonormalBasis (Fin m) 𝕜 F) (s : Finset (Fin m)) :
    ∑ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  -- Per-`k` reduction: the `k`-th term is a single cross-overlap row.
  have hQnorm : ∀ k, ‖(Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)‖ ^ 2
      = ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 :=
    fun k => Orthonormal.norm_sq_starProjection_span_image v.orthonormal s (u k)
  have hterm : ∀ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = if k ∈ s then ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2 else ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 := by
    intro k
    rw [show (((Submodule.span 𝕜 (v '' ↑s)).starProjection
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k))
        = (Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection (u k) from rfl,
      Orthonormal.starProjection_span_image_apply_self u.orthonormal s k]
    split <;> rename_i hk
    · -- `k ∈ s`: `P_u` keeps `uₖ`, so the term is the residual of `uₖ` against the `v`-span,
      -- which is the complementary Parseval sum.
      rw [norm_sub_rev]
      exact OrthonormalBasis.norm_sq_sub_starProjection_span_image v s (u k)
    · -- `k ∉ s`: the `u`-projection vanishes; the term is the `v`-projection norm.
      rw [sub_zero, hQnorm k]
  -- Sum the per-`k` formula and swap the two cross blocks into each other.
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_add_sum_compl s]
  rw [Finset.sum_congr rfl fun k (hk : k ∈ s) => if_pos hk,
    Finset.sum_congr rfl fun k (hk : k ∈ sᶜ) => if_neg (Finset.mem_compl.mp hk)]
  -- First block is the target cross sum (after swapping the inner-product slots).
  have hswap : ∀ (i j : Fin m), ‖⟪v j, u i⟫_𝕜‖ = ‖⟪u i, v j⟫_𝕜‖ := fun i j =>
    norm_inner_symm (v j) (u i)
  have hA : ∑ k ∈ s, ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hswap i j]
  -- Second block equals the first by the symmetric block-counting identity.
  have hB : ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := sum_inner_sq_compl_block_eq u v s
  rw [hA, hB]
  ring

/-- **Sharp Davis–Kahan, projector form (Frobenius sin-Θ).** The squared Frobenius
distance between the orthogonal projections onto the leading-`d` spectral subspaces
of two self-adjoint operators with eigengap `gap` is at most twice the squared
Hilbert–Schmidt (Frobenius) norm of the perturbation over `gap²`:
`‖P̂ − P‖²_F ≤ 2 (∑ₖ ‖(S − T) v̂ₖ‖²) / gap²`.  No operator-norm hypothesis and no
dimension factor — the sharp `‖sin Θ‖_F ≤ ‖S − T‖_F / gap`.  The projections are
`Submodule.starProjection` of the spans of the leading `d` eigenvectors. -/
theorem LinearMap.IsSymmetric.sum_norm_sub_starProjection_span_sq_le_hilbertSchmidt
    {T S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 F = m)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin m, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|) :
    ∑ k, ‖((Submodule.span 𝕜 (hS.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun j : Fin m => (j : ℕ) < d))).starProjection
        - (Submodule.span 𝕜 (hT.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun i : Fin m => (i : ℕ) < d))).starProjection)
        (hT.eigenvectorBasis hn k)‖ ^ 2
      ≤ 2 * ((∑ j : Fin m, ‖(S - T) (hS.eigenvectorBasis hn j)‖ ^ 2) / gap ^ 2) := by
  rw [OrthonormalBasis.sum_norm_sub_starProjection_span_sq_eq]
  -- The complement of the leading filter is the trailing filter.
  have hcompl : (Finset.univ.filter fun i : Fin m => (i : ℕ) < d)ᶜ
      = Finset.univ.filter fun j : Fin m => d ≤ (j : ℕ) := by
    ext j; simp [not_lt]
  rw [hcompl]
  have hbound := hT.sum_cross_norm_inner_eigenvectorBasis_sq_le_hilbertSchmidt
    hS hn d hgap_pos hgap
  linarith [hbound]

/-- **Davis–Kahan, projector form (crude operator-norm form).** The squared Frobenius
distance between the orthogonal projections onto the leading-`d` spectral subspaces of two
`ε`-operator-close self-adjoint operators with eigengap `gap` is at most `2 m ε² / gap²`.
The projections are `Submodule.starProjection` of the spans of the leading `d` eigenvectors.

Corollary of the sharp `sum_norm_sub_starProjection_span_sq_le_hilbertSchmidt` by degrading
`‖S − T‖²_F ≤ m ε²`; the dimension factor `m` is not sharp. -/
theorem LinearMap.IsSymmetric.sum_norm_sub_starProjection_span_sq_le {T S : F →ₗ[𝕜] F}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 F = m)
    (d : ℕ) {gap : ℝ} (hgap_pos : 0 < gap)
    (hgap : ∀ i j : Fin m, (i : ℕ) < d → d ≤ (j : ℕ) →
      gap ≤ |hT.eigenvalues hn i - hS.eigenvalues hn j|)
    {ε : ℝ} (hε : ∀ x : F, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ k, ‖((Submodule.span 𝕜 (hS.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun j : Fin m => (j : ℕ) < d))).starProjection
        - (Submodule.span 𝕜 (hT.eigenvectorBasis hn ''
          ↑(Finset.univ.filter fun i : Fin m => (i : ℕ) < d))).starProjection)
        (hT.eigenvectorBasis hn k)‖ ^ 2
      ≤ 2 * ((m : ℝ) * ε ^ 2 / gap ^ 2) := by
  refine (hT.sum_norm_sub_starProjection_span_sq_le_hilbertSchmidt
    hS hn d hgap_pos hgap).trans ?_
  gcongr
  exact hS.sum_norm_eigenvectorBasis_map_sub_sq_le hn hε

end Projector
