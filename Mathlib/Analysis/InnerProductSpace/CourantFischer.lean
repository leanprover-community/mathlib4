/-
Copyright (c) 2026 Jon Crall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Courant–Fischer min-max and Weyl's eigenvalue perturbation inequality

For a symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ`, Mathlib provides the decreasingly sorted eigenvalues
`LinearMap.IsSymmetric.eigenvalues` together with an orthonormal eigenbasis
`LinearMap.IsSymmetric.eigenvectorBasis`.  This file proves the discrete
Courant–Fischer characterization of these sorted eigenvalues and derives from
it Weyl's eigenvalue perturbation inequality
`|λₖ(T) − λₖ(S)| ≤ ε` whenever `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`.

## Main results

* `LinearMap.IsSymmetric.re_inner_map_self_eq_sum_eigenvalues_mul_sq`:
  diagonalization of the quadratic form,
  `re ⟪T x, x⟫ = ∑ i, λᵢ * ‖(b.repr x) i‖ ^ 2` in the eigenbasis `b` of `T`.
* `LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue`:
  Courant–Fischer, upper direction — every subspace of dimension `k + 1` contains
  a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`.
* `LinearMap.IsSymmetric.forall_unit_vector_eigenvalue_le_re_inner`:
  Courant–Fischer, lower direction — some subspace of dimension `k + 1` satisfies
  `λₖ(T) ≤ re ⟪T x, x⟫` for all unit vectors `x` in it.
* `LinearMap.IsSymmetric.abs_eigenvalues_sub_le`: **Weyl's inequality** — the
  `k`-th sorted eigenvalues of two symmetric operators differ by at most an
  operator-norm bound `ε` on their difference (`∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`).
* `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm`: Weyl's inequality phrased
  directly with the continuous-linear-map operator norm `‖T − S‖`.

## References

* [R. A. Horn, C. R. Johnson, *Matrix Analysis*][horn_johnson_2013] —
  Theorem 4.2.6 (Courant–Fischer) and Theorem 4.3.1 (Weyl).
* [R. Bhatia, *Matrix Analysis*][bhatia_1997] — Corollary III.2.6 (Weyl).
-/

@[expose] public section

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-! ### Spectral subspaces

The span of the orthonormal subfamily selected by a predicate `p`, with its
dimension and the vanishing of `b`-coordinates outside `p`.  Internal scaffolding
(general orthonormal-span facts, not Courant–Fischer-specific), hence `private`. -/

-- REVIEWER INPUT REQUESTED: `specSubspace` / `finrank_specSubspace` /
-- `repr_eq_zero_of_mem_specSubspace` / `sum_sq_norm_repr_eq_sq_norm` are general
-- orthonormal-basis facts. Keep them `private` here, or upstream any as public API
-- (e.g. in `InnerProductSpace/Orthonormal.lean`)?
/-- The subspace spanned by the orthonormal basis vectors `b i` for indices `i`
satisfying `p i`. -/
private noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
private theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

/-- A vector in a spectral subspace has zero `b`-coordinate at any index outside
the selecting predicate. -/
private theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E)
    (p : Fin n → Prop) {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Parseval: in an orthonormal basis the squared norms of the coordinates sum
to the squared norm.  Thin wrapper around
`OrthonormalBasis.sum_sq_norm_inner_right`. -/
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

namespace LinearMap.IsSymmetric

/-! ### The quadratic form in the eigenbasis -/

-- REVIEWER INPUT REQUESTED: this is a general quadratic-form diagonalization with no
-- Courant–Fischer content. Should it live in `InnerProductSpace/Spectrum.lean`, next to
-- the rest of the `IsSymmetric.eigenvalues` / `eigenvectorBasis` API, rather than here?
/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator, diagonalized in its
eigenbasis: the eigenvalue-weighted sum of the squared coordinate norms. -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

/-! ### Discrete Courant–Fischer directional bounds -/

-- REVIEWER INPUT REQUESTED: `card_filter_le` / `card_filter_ge` are general `Fin n`
-- Finset-cardinality facts (not currently in Mathlib). Keep `private`, or upstream as
-- public lemmas near `Fin.card_Ici` / `Fin.card_Iic`?
/-- Counting lemma: the number of indices `i : Fin n` with `k ≤ i` is `n - k`. -/
private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]

/-- Counting lemma: the number of indices `i : Fin n` with `i ≤ k` is `k + 1`. -/
private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension `k + 1`
there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`, where `λ` is the decreasing
enumeration `LinearMap.IsSymmetric.eigenvalues`.

By dimension counting `V` meets the tail eigenspace `span {bᵢ : k ≤ i}`, on which
the quadratic form is `≤ λₖ`. -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  -- `x ∈ W`, so its `b`-coordinates vanish for `i < k`.
  have hxW : x ∈ W := W.smul_mem _ hzW
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x]
  -- Bound each surviving term by `λₖ * ‖(b.repr x) i‖ ^ 2`.
  have hbound : ∀ i ∈ Finset.univ,
      hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 ≤ hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 := by
    intro i _
    by_cases hik : k ≤ i
    · exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone hn hik) (sq_nonneg _)
    · have : b.repr x i = 0 :=
        repr_eq_zero_of_mem_specSubspace b _ hxW hik
      simp [this]
  calc ∑ i : Fin n, hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2
      ≤ ∑ i : Fin n, hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 :=
        Finset.sum_le_sum hbound
    _ = hT.eigenvalues hn k * ∑ i : Fin n, ‖b.repr x i‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [sum_sq_norm_repr_eq_sq_norm]
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ re ⟪T x, x⟫`.

Witness: `V = span {bᵢ : i ≤ k}`, on which the quadratic form is `≥ λₖ`. -/
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx
    rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x]
    have hbound : ∀ i ∈ Finset.univ,
        hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 ≤ hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 := by
      intro i _
      by_cases hik : i ≤ k
      · exact mul_le_mul_of_nonneg_right
          (hT.eigenvalues_antitone hn hik) (sq_nonneg _)
      · have : b.repr x i = 0 :=
          repr_eq_zero_of_mem_specSubspace b _ hxV hik
        simp [this]
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ = hT.eigenvalues hn k * ∑ i : Fin n, ‖b.repr x i‖ ^ 2 := by
          rw [sum_sq_norm_repr_eq_sq_norm]
      _ = ∑ i : Fin n, hT.eigenvalues hn k * ‖b.repr x i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin n, hT.eigenvalues hn i * ‖b.repr x i‖ ^ 2 := Finset.sum_le_sum hbound

/-! ### Weyl's inequality -/

/-- One-sided Weyl bound `λₖ(S) − λₖ(T) ≤ ‖S − T‖op`; Weyl's inequality follows by
symmetry.  Combine the lower direction for `S` and the upper direction for `T` on a
shared `(k + 1)`-dimensional subspace, then bound the gap by Cauchy–Schwarz. -/
private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ := forall_unit_vector_eigenvalue_le_re_inner hS hn k
  obtain ⟨x, hxV, hnx, hTup⟩ := exists_unit_vector_re_inner_le_eigenvalue hT hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    have := hε x
    rwa [hnx, mul_one] at this ⊢
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality** for symmetric operators on a finite-dimensional inner
product space over `𝕜 = ℝ, ℂ`: the `k`-th sorted eigenvalues of `T` and `S` differ
by at most the operator-norm bound `ε` on `T − S` (`∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`).

See [horn_johnson_2013] Theorem 4.3.1 or [bhatia_1997] Corollary III.2.6. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- Apply `eigenvalues_sub_le` both ways; `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

/-- **Weyl's inequality**, operator-norm form.  The `k`-th sorted eigenvalues of
two symmetric operators `T`, `S` on a finite-dimensional inner product space
differ by at most the (continuous-linear-map) operator norm `‖T − S‖` of their
difference.  This is `abs_eigenvalues_sub_le` with the bound supplied by
`ContinuousLinearMap.le_opNorm`. -/
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalues_sub_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

end LinearMap.IsSymmetric
