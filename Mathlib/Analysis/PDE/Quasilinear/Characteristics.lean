import Mathlib.Analysis.Calculus.PDE.LinearFirstOrder.Defs
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # The Methods of Characteristics for first order quasilinear PDEs

This file develops some basic theory of first order quasilinear PDEs and
their characteristic curves.

## Main results
- `solution_constant_characteristic`: if `u` is a solution to quasilinear PDE
  `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` and `γ = (X, U)` is a characteristic curve of `E` then
  the composite `u ∘ X` satisfies `d/dt (u ∘ X) = U`


## TODO
- Local existence of characteristics

-/

open Set

open scoped Topology

section MainTheorem

open FirstOrderQuasiLinearPDE

/-

In this section, we prove the following key result: if `(X, U)` is a parametrisation of a characteristic curve of
`E` and `u` is a solution to `E` then we have `u ∘ X(t) = U(t)` for all reasonable times `t`.

The proof goes roughly as follows:
- Consider the function `Δ(t) = |u ∘ X(t) - U(t)|^2`. This is differentiable and so on.
- Show that for `|Δ'(t)| ≤ C|Δ(t)|` for small times `t`.
- By a consequence of Gronwall's inequality (already formalised in other file), this implies that `Δ = 0` for small times `t`
- This gives the result locally. The global version follows easily from this.

-/

/-
TODO(Paul-Lez):
- Harmonise usage of `fderiv` vs `HasFDeriv` and so on.
- Split/tidy proofs
-/

variable {𝕜 V : Type*}

variable {γ : ℝ → V × ℝ} {s : Set ℝ} {u : V → ℝ}

variable (γ u) in
abbrev Δ : ℝ → ℝ := (fun (t : ℝ) ↦ |u (γ t).fst - (γ t).snd|^2)

lemma Δ_eq_zero_iff {t} : Δ γ u t = 0 ↔ u (γ t).fst = (γ t).snd := by
  rw [Δ, sq_eq_zero_iff, abs_eq_zero, sub_eq_zero]

section Continuous

variable [TopologicalSpace V] (hγ : Continuous γ)  (hu' : Continuous u)

include hγ hu'

lemma Δ_cts' : Continuous (Δ γ u) := by fun_prop

lemma Δ_cts : ContinuousOn (Δ γ u) s :=
  (Δ_cts' hγ hu').continuousOn

section sSups_and_sInfs

/--
Let `t₀` be a time such that `u(X(t₀)) = U(t₀)`. Then for any `t ≥ t₀`, the
supremum of the set `{τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0}` lies in the set
-/
theorem csSup_zero_set (hs' : IsConnected s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (hγ₁ : (γ t₀).snd = u (γ t₀).fst)
    (ht : t ∈ s) (ht₀' : t₀ ≤ t) :
    --we can strengthen this quite easily if needed
    sSup {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0} ∈ {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0} := by
  let ε := sSup {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0}
  have t₀_mem : t₀ ∈ {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0} :=
    ⟨ht₀, ht₀', Δ_eq_zero_iff.mpr hγ₁.symm⟩
  have bdd_above : BddAbove {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0} := by
    use t
    intro v hv
    exact hv.right.left
  have Δ_ε : Δ γ u ε = 0 := by
    --We should be able to weaken the continuity requirements on `u` and `γ` here
    apply ContinousWithinAt.eq_const_of_mem_closure (Continuous.continuousWithinAt _) (csSup_mem_closure (nonempty_of_mem t₀_mem) bdd_above)
    · intro y hy
      exact hy.right.right
    · apply Δ_cts' hγ hu'
  suffices ε ∈ Set.Icc t₀ t by
    refine ⟨(IsConnected.Icc_subset hs' ht₀ ht) this, (Set.mem_Icc.mp this).right, Δ_ε⟩
  rw [Set.mem_Icc]
  refine ⟨le_csSup bdd_above t₀_mem , csSup_le (nonempty_of_mem t₀_mem) fun v hv => hv.right.left⟩


/--
Let `t₀` be a time such that `u(X(t₀)) = U(t₀)`. Then for any `t ≤ t₀`, the
infimum of the set `{τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0}` lies in the set
-/
theorem csInf_zero_set (hs' : IsConnected s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (hγ₁ : (γ t₀).snd = u (γ t₀).fst)
    (ht : t ∈ s) (ht₀' : t ≤ t₀) :
    sInf {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0} ∈ {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0} := by
  let ε := sInf {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0}
  have t₀_mem : t₀ ∈ {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0} :=
    ⟨ht₀, ht₀', Δ_eq_zero_iff.mpr hγ₁.symm⟩
  have bdd_below : BddBelow {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0} := by
    use t
    intro v hv
    exact hv.right.left
  have Δ_ε : Δ γ u ε = 0 := by
    --We should be able to weaken the continuity requirements on `u` and `γ` here
    apply ContinousWithinAt.eq_const_of_mem_closure (Continuous.continuousWithinAt _) (csInf_mem_closure (nonempty_of_mem t₀_mem) bdd_below)
    · intro y hy
      exact hy.right.right
    · apply Δ_cts' hγ hu'
  suffices ε ∈ Set.Icc t t₀ by
    refine ⟨(IsConnected.Icc_subset hs' ht ht₀) this, (Set.mem_Icc.mp this).left, Δ_ε⟩
  rw [Set.mem_Icc]
  refine ⟨le_csInf (nonempty_of_mem t₀_mem) fun v hv => hv.right.left, csInf_le bdd_below t₀_mem ⟩

end sSups_and_sInfs

end Continuous

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {E : FirstOrderQuasiLinearPDE ℝ V} (hγ₂ : ∀ t ∈ s, E.HasCharacteristicAt γ t)
variable (hu : ∀ t ∈ s, E.HasSolutionAt u (γ t).fst)

include hu
include hγ₂

/--
`Δ` is differentiable.
-/
lemma Δ_diff {t : ℝ} (ht : t ∈ s) : DifferentiableAt ℝ (Δ γ u) t := by
  have : Δ γ u = fun t => (u (γ t).fst - (γ t).snd)^2 := by ext; simp [Δ]
  rw [this]
  apply DifferentiableAt.pow
  apply DifferentiableAt.sub _ (hγ₂ t ht).differentiableAt.snd
  apply DifferentiableAt.comp
  apply differentiableAt_of_hasSolutionAt (hu t ht)
  apply (hγ₂ t ht).differentiableAt.fst

/--
`Δ'(t) = 2(u(X(t)) - U(t)) (∇u(X(t)) • X'(t) - U'(t)) = 2(u(X(t)) - U(t)) (∇u(X(t)) • a(X(t), U(t)) - c(X(t), U(t)))`
-/
lemma hasDerivAt_Δ_step₁ (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (Δ γ u) (2*(u (γ t).fst - (γ t).snd) * (fderiv ℝ u ((γ t).fst) (a[E] (γ t)) - (c[E] (γ t)))) t := by
  have deriv_lem₁ : HasDerivAt (fun t => u (γ t).fst - (γ t).snd) (fderiv ℝ u ((γ t).fst) (a[E] (γ t)) - (c[E] (γ t))) t := by
    have : HasDerivAt (fun t => u (γ t).fst) (fderiv ℝ u ((γ t).fst) (a[E] (γ t))) t := by
      have := (DifferentiableAt.hasFDerivAt (differentiableAt_of_hasSolutionAt (hu t ht))).comp_hasDerivAt _ (hγ₂ t ht).fst
      exact this
    have : HasDerivAt (fun t => (γ t).snd) (c[E] (γ t)) t := (hγ₂ t ht).snd
    apply HasDerivAt.sub ((DifferentiableAt.hasFDerivAt (differentiableAt_of_hasSolutionAt (hu t ht))).comp_hasDerivAt _ (hγ₂ t ht).fst) (hγ₂ t ht).snd
  have : Δ γ u = fun t ↦ (u (γ t).fst - (γ t).snd)^2 := by ext; simp [Δ]
  simpa [this] using deriv_lem₁.pow 2

/--
`Δ'(t) = 2(u(X(t)) - U(t)) (∇u(X(t)) • (a(X(t), U(t)) - a(X(t), (u ∘ X)(t)) - (c(X(t), U(t)) - c(X(t), (u ∘ X)(t)))`
-/
lemma hasDerivAt_Δ_step₂ (t : ℝ) (ht : t ∈ s) :
    HasDerivAt (Δ γ u) (2*(u (γ t).fst - (γ t).snd) * (fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - (a[E] ((γ t).fst, u (γ t).fst))) - ((c[E]) (γ t) - (c[E]) ((γ t).fst, u (γ t).fst)))) t := by
  suffices (2*(u (γ t).fst - (γ t).snd) * (fderiv ℝ u ((γ t).fst) (a[E] (γ t)) - (c[E]) (γ t))) = (2*(u (γ t).fst - (γ t).snd) *(fderiv ℝ u ((γ t).fst)  ((a[E] (γ t)) - (a[E] ((γ t).fst, u (γ t).fst)) : V) - ((c[E]) (γ t) - (c[E]) ((γ t).fst, u (γ t).fst)))) by
    have lem := hasDerivAt_Δ_step₁ hγ₂ hu t ht
    rwa [this] at lem
  congr 1
  have : fderiv ℝ u ((γ t).fst) (a[E] (γ t)) - fderiv ℝ u ((γ t).fst) (a[E] ((γ t).1, u (γ t).1)) - (E.const (γ t) - E.const ((γ t).1, u (γ t).1))
      = fderiv ℝ u ((γ t).fst) (a[E] (γ t)) - E.const (γ t) - (fderiv ℝ u ((γ t).fst) (a[E] ((γ t).1, u (γ t).1)) - E.const ((γ t).1, u (γ t).1)) := by
    abel
  rw [map_sub, this]
  have : fderiv ℝ u ((γ t).fst) (a[E] ((γ t).1, u (γ t).1)) - E.const ((γ t).1, u (γ t).1) = 0 := by
    simpa only [sub_eq_zero, FirstOrderQuasiLinearPDE.HasSolutionAt, FirstOrderQuasiLinearPDE.HasSolutionAt] using fderiv_apply_of_hasSolutionAt (hu t ht)
  rw [this, sub_zero]


/--
`|Δ'(t)| ≤ 2|u(X(t)) - U(t)| * (||∇u(X(t))|| * ||a(X(t), U(t)) - a(X(t), (u ∘ X)(t))|| + ||c(X(t), U(t)) - c(X(t), (u ∘ X)(t))||`
-/
lemma hasDerivAt_Δ_bound (t : ℝ) (ht : t ∈ s) :
    ‖deriv (Δ γ u) t‖ ≤ 2*|(u (γ t).fst - (γ t).snd)| * (‖((a[E] (γ t)) - (a[E] ((γ t).fst, u (γ t).fst)) : V)‖ * ‖fderiv ℝ u ((γ t).fst)‖ +
      |(c[E]) (γ t) - (c[E]) ((γ t).fst, u (γ t).fst)|) := by
  have := hasDerivAt_Δ_step₂ hγ₂ hu t ht
  rw [this.deriv]
  have step₁ : ‖2 * (u (γ t).1 - (γ t).2) * (fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - a[E] (((γ t).1, u (γ t).1))) -
      (E.const (γ t) - E.const ((γ t).1, u (γ t).1)))‖  = 2 * |(u (γ t).1 - (γ t).2)| *
        ‖fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - a[E] (((γ t).1, u (γ t).1))) -
        (c[E] (γ t) - c[E] ((γ t).1, u (γ t).1))‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    congr
  have step₂ : 2 * |(u (γ t).1 - (γ t).2)| *
        ‖fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - a[E] (((γ t).1, u (γ t).1))) -
        (c[E] (γ t) - c[E] ((γ t).1, u (γ t).1))‖ ≤ 2 * |(u (γ t).1 - (γ t).2)| * (|fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - a[E] (((γ t).1, u (γ t).1)))|
        + |c[E] (γ t) - c[E] ((γ t).1, u (γ t).1)|) := by
    apply mul_le_mul_of_nonneg_left
    · apply abs_sub
    · apply mul_nonneg zero_le_two (abs_nonneg _)
  have step₃ : 2 * |(u (γ t).1 - (γ t).2)| * (|fderiv ℝ u ((γ t).fst) ((a[E] (γ t)) - a[E] (((γ t).1, u (γ t).1)))|
        + |c[E] (γ t) - c[E] ((γ t).1, u (γ t).1)|)
    ≤ 2 * |(u (γ t).1 - (γ t).2)| * (‖((a[E] (γ t)) - (a[E] (((γ t).1, u (γ t).1)) : V) : V)‖ * ‖
          fderiv ℝ u ((γ t).fst)‖  + |c[E] (γ t) - c[E] ((γ t).1, u (γ t).1)|) := by
    apply mul_le_mul_of_nonneg_left
    apply add_le_add_right
    · rw [mul_comm]
      apply (fderiv ℝ u ((γ t).fst)).le_opNorm
    · apply mul_nonneg zero_le_two (abs_nonneg _)
  rw [step₁]
  apply le_trans step₂ step₃

--TODO: Add results like `ContDiff.smul_const` and that seem to be missing!

variable (hγ : Continuous γ)  (hu' : Continuous u) (hs : IsOpen s) (hE : E.RegularBy (ContDiff ℝ 1))

include hγ hu' hs hE

/--
If `u` is a solution to quasilinear PDE `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` and `γ = (X, U)`
is a characteristic curve of `E` such that `U(t₀) = u(X(t₀))` then for `t` near `t₀` we have
`|d/dt Δ(t)| ≤ C|Δ(t)|` for some absolute constant `C`.
-/
lemma Δ_deriv_norm_le (huGrad : ContinuousOn (fderiv ℝ u) ((Prod.fst ∘ γ) '' s)) (t : ℝ) (ht : t ∈ s) (ht' : (γ t).snd = u (γ t).fst) :
    ∃ r > 0, Set.Icc (t - r) (t + r) ⊆ s ∧ ∃ C, ∀ t' ∈ Set.Icc (t - r) (t + r),  ‖deriv (Δ γ u) t'‖ ≤ C * ‖Δ γ u t'‖ := by
  have ha : LocallyLipschitz (fun x => (a[E] x : V)) := by
    apply ContDiff.locallyLipschitz hE.reg.fst
  have hc : LocallyLipschitz (fun x => (c[E] x : ℝ)) := by
    apply ContDiff.locallyLipschitz hE.reg.snd
  obtain ⟨Ka, S₁, hKaS₁⟩ := ha (γ t)
  obtain ⟨Kc, S₂, hKcS₂⟩ := hc (γ t)
  obtain ⟨U₁, hU₁⟩ := mem_nhds_iff.mp hKaS₁.left
  obtain ⟨U₂, hU₂⟩ := mem_nhds_iff.mp hKcS₂.left
  set Ω' : Set ℝ := connectedComponentIn (γ⁻¹' (U₁ ∩ U₂) ∩ ((fun t => ((γ t).fst, u (γ t).fst))⁻¹' (U₁ ∩ U₂)) ∩ s) t with hΩ'
  have t_mem : t ∈ (γ⁻¹' (U₁ ∩ U₂) ∩ ((fun t => ((γ t).fst, u (γ t).fst))⁻¹' (U₁ ∩ U₂)) ∩ s) := by
    rw [Set.mem_inter_iff]
    refine ⟨?_, ht⟩
    simpa [preimage_inter, mem_inter_iff, mem_preimage, ←ht'] using ⟨hU₁.right.right, hU₂.right.right⟩
  have Ω'_subset_s : Ω' ⊆ s := by rw [hΩ'] ; apply subset_trans (connectedComponentIn_subset _ _) Set.inter_subset_right
  have Ω'_open : IsOpen Ω' := by
    apply IsOpen.connectedComponentIn
    apply IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · apply Continuous.isOpen_preimage hγ
      · apply IsOpen.inter hU₁.right.left hU₂.right.left
    · apply Continuous.isOpen_preimage
      · rw [continuous_prod_mk]
        refine  ⟨hγ.fst, Continuous.comp hu' hγ.fst⟩
      · apply IsOpen.inter hU₁.right.left hU₂.right.left
    · exact hs
  rw [Metric.isOpen_iff'] at Ω'_open
  obtain ⟨r, hr, hr'⟩ := Ω'_open t (mem_connectedComponentIn t_mem)
  use r, hr
  rw [←Real.closedBall_eq_Icc]
  refine ⟨subset_trans hr' <| subset_trans (connectedComponentIn_subset _ _) Set.inter_subset_right, ?_⟩
  · obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Metric.closedBall t r, ‖fderiv ℝ u ((γ s).fst)‖ ≤ M := by
      set M := ((fun (t : ℝ) ↦ ‖fderiv ℝ u ((γ t).fst)‖) : ℝ → ℝ) '' (Set.Icc (t-r) (t+r)) with hM
      use sSup M
      intro s hs
      rw [hM]
      apply  ContinuousOn.le_sSup_image_Icc (f := (fun (t : ℝ) ↦ ‖fderiv ℝ u ((γ t).fst)‖))
      · --`‖u (γ t).fst‖` is continuous
        apply Continuous.comp_continuousOn continuous_norm
        · apply ContinuousOn.comp huGrad
          apply hγ.fst.continuousOn
          --the interval `[t-r,t+r]` maps into `γ '' s`.
          intro v hv
          rw [Set.mem_image]
          use v
          refine ⟨?_, rfl⟩
          apply subset_trans ?_ Ω'_subset_s hv
          rw [←Real.closedBall_eq_Icc]
          exact hr'
      · rwa [←Real.closedBall_eq_Icc]
    use (2 * (Ka * M + Kc))
    intro t ht
    have gamma_t_mem : γ t ∈ S₁ := by
      rw [←Set.mem_preimage]
      apply preimage_mono (subset_trans inter_subset_left hU₁.left)
      apply inter_subset_left
      apply inter_subset_left
      apply connectedComponentIn_subset
      apply hr' ht
    have gamma_t_first_prod_mem : ((γ t).fst, u (γ t).fst) ∈ S₁ := by
      rw [←Set.mem_preimage (f:= (fun t ↦ ((γ t).1, u (γ t).1)))]
      apply preimage_mono (subset_trans (inter_subset_left ) hU₁.left)
      apply inter_subset_right
      apply inter_subset_left
      apply connectedComponentIn_subset
      apply hr' ht
    have gamma_t_mem₂ : γ t ∈ S₂ := by
      rw [←Set.mem_preimage]
      apply preimage_mono (subset_trans inter_subset_right hU₂.left)
      apply inter_subset_left
      apply inter_subset_left
      apply connectedComponentIn_subset
      apply hr' ht
    have gamma_t_first_prod_mem₂ : ((γ t).fst, u (γ t).fst) ∈ S₂ := by
      rw [←Set.mem_preimage (f:= (fun t ↦ ((γ t).1, u (γ t).1)))]
      apply preimage_mono (subset_trans (inter_subset_right ) hU₂.left)
      apply inter_subset_right
      apply inter_subset_left
      apply connectedComponentIn_subset
      apply hr' ht
    have step₁ : ‖deriv (Δ γ u) t‖  ≤ 2*|(u (γ t).fst - (γ t).snd)| * (‖((a[E] (γ t)) - (a[E] ((γ t).fst, u (γ t).fst)) : V)‖ * ‖fderiv ℝ u ((γ t).fst)‖ +
            |(c[E]) (γ t) - (c[E]) ((γ t).fst, u (γ t).fst)|) := by
      apply hasDerivAt_Δ_bound hγ₂ hu t
      apply subset_trans (hr') (subset_trans (connectedComponentIn_subset _ _) Set.inter_subset_right) ht
    have step₂ : 2*|(u (γ t).fst - (γ t).snd)| * (‖((a[E] (γ t)) - (a[E] ((γ t).fst, u (γ t).fst)) : V)‖ * ‖fderiv ℝ u ((γ t).fst)‖ +
            |(c[E]) (γ t) - (c[E]) ((γ t).fst, u (γ t).fst)|) ≤ 2*|(u (γ t).fst - (γ t).snd)| * (Ka * ‖ γ t - ((γ t).fst, u (γ t).fst)‖ * ‖fderiv ℝ u ((γ t).fst)‖ + Kc * ‖ γ t - ((γ t).fst, u (γ t).fst)‖) := by
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_two (abs_nonneg _))
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_right
          rw [←dist_eq_norm, ←dist_eq_norm]
          exact hKaS₁.right.dist_le_mul _ gamma_t_mem _ gamma_t_first_prod_mem
          · exact norm_nonneg (fderiv ℝ u ((γ t).fst))
        · rw [←dist_eq_norm, ←Real.dist_eq]
          exact hKcS₂.right.dist_le_mul _ gamma_t_mem₂ _ gamma_t_first_prod_mem₂
    have step₃ : 2*|(u (γ t).fst - (γ t).snd)| * (Ka * ‖ γ t - ((γ t).fst, u (γ t).fst)‖ * ‖fderiv ℝ u ((γ t).fst)‖ + Kc * ‖ γ t - ((γ t).fst, u (γ t).fst)‖)
      ≤ 2*|(u (γ t).fst - (γ t).snd)| * (Ka * ‖ γ t - ((γ t).fst, u (γ t).fst)‖ * M + Kc * ‖ γ t - ((γ t).fst, u (γ t).fst)‖) := by
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_two (abs_nonneg _))
      rw [add_le_add_iff_right]
      apply mul_le_mul_of_nonneg_left
      apply hM t ht
      apply mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
    have step₄ : 2*|(u (γ t).fst - (γ t).snd)| * (Ka * ‖ γ t - ((γ t).fst, u (γ t).fst)‖ * M + Kc * ‖ γ t - ((γ t).fst, u (γ t).fst)‖)
      = 2*|(u (γ t).fst - (γ t).snd)| * (Ka * M + Kc) * ‖γ t - ((γ t).fst, u (γ t).fst)‖ := by ring
    have step₅ : 2*|(u (γ t).fst - (γ t).snd)| * (Ka * M + Kc) * ‖γ t - ((γ t).fst, u (γ t).fst)‖
      = 2*|(u (γ t).fst - (γ t).snd)| * (Ka * M + Kc) * ‖(γ t).snd - u (γ t).fst‖ := by
      congr
      nth_rewrite 1 [←Prod.mk.eta (p:= γ t)]
      rw [Prod.mk_sub_mk, sub_self]
      simp
    have step₆ : 2*|(u (γ t).fst - (γ t).snd)| * (Ka * M + Kc) * ‖(γ t).snd - u (γ t).fst‖
      = (2 * (Ka * M + Kc)) * |(u (γ t).fst - (γ t).snd)|^2 := by
      rw [Real.norm_eq_abs,  abs_sub_comm (γ t).2]
      ring
    have step₇ : (2 * (Ka * M + Kc)) * |(u (γ t).fst - (γ t).snd)|^2 = (2 * (Ka * M + Kc)) * ‖(Δ γ u) t‖ := by
      rw [Δ, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |u (γ t).1 - (γ t).2|)]
    rw [←step₇, ←step₆, ←step₅, ←step₄]
    apply le_trans step₁ (le_trans step₂ step₃)

/--
If `u` is a solution to quasilinear PDE `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` and `γ = (X, U)`
is a characteristic curve of `E` such that `U(t₀) = u(X(t₀))` then the composite `u ∘ X` satisfies `d/dt (u ∘ X) = U`
for `t₀ ≤ t`
-/
theorem solution_constant_characteristic_aux_t₀_le (hs' : IsConnected s) (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (huGrad : ContinuousOn (fderiv ℝ u) ((Prod.fst ∘ γ)''s))
    (hγ₁ : (γ t₀).snd = u (γ t₀).fst)
    (t : ℝ) (ht : t ∈ s) (ht₀' : t₀ ≤ t) :
    u (γ t).fst = (γ t).snd := by
  by_contra! Ht
  let ε := sSup {τ : ℝ | τ ∈ s ∧ τ ≤ t ∧ Δ γ u τ = 0}
  let ⟨ε_mem, ε_le, Δ_ε⟩ := csSup_zero_set hγ hu' hs' ht₀ hγ₁ ht ht₀'
  obtain ⟨r, hr, hr', ⟨C, hC⟩⟩ := Δ_deriv_norm_le hγ₂ hu hγ hu' hs hE huGrad ε ε_mem (Δ_eq_zero_iff.mp Δ_ε).symm
  obtain ⟨τ, hτ, hτ', hτ''⟩ : ∃ τ, τ ∈ s ∧ ε < τ ∧
    ∀ t ∈ Set.Icc ε τ, Δ γ u t = 0 := by
    use (ε + r)
    have h₁ : ε < ε + r := by linarith
    have h₂ : Set.Icc ε (ε + r) ⊆ s := by
      apply subset_trans (Set.Icc_subset_Icc_left (by linarith)) hr'
    refine ⟨h₂ (Set.right_mem_Icc.mpr <| le_of_lt <| h₁), h₁, ?_⟩
    intro v hv
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_left (K:=C) («a» := ε) (b := ε+r) ?_ (fun x hx => DifferentiableWithinAt.hasDerivWithinAt ?_) Δ_ε
    · intro x hx
      rw [DifferentiableAt.derivWithin (Δ_diff hγ₂ hu _) (uniqueDiffWithinAt_Ici _)]
      apply hC x <|  Set.Icc_subset_Icc_left (by linarith) (Set.Ico_subset_Icc_self hx)
      apply h₂ (Set.Ico_subset_Icc_self hx)
    · apply hv
    · apply (Δ_cts hγ hu').mono h₂
    · apply DifferentiableAt.differentiableWithinAt
      apply Δ_diff hγ₂ hu (h₂ (Set.Ico_subset_Icc_self hx))
  by_cases hτ''' : τ < t
  · apply (lt_iff_not_le.mp hτ')
    refine le_csSup ?_ ⟨hτ, le_of_lt hτ''', hτ'' τ (Set.right_mem_Icc.mpr <| le_of_lt hτ')⟩
    use t
    intro v hv
    exact hv.right.left
  · apply Ht
    rw [←Δ_eq_zero_iff]
    apply hτ''
    rw [Set.mem_Icc]
    refine ⟨ε_le, le_of_not_lt hτ'''⟩

/--
If `u` is a solution to quasilinear PDE `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` and `γ = (X, U)`
is a characteristic curve of `E` such that `U(t₀) = u(X(t₀))` then the composite `u ∘ X` satisfies `d/dt (u ∘ X) = U`
for `t₀ ≥ t`
-/
theorem solution_constant_characteristic_aux_t₀_ge (hs' : IsConnected s) (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (huGrad : ContinuousOn (fderiv ℝ u) ((Prod.fst ∘ γ)''s))
    (hγ₁ : (γ t₀).snd = u (γ t₀).fst)
    (t : ℝ) (ht : t ∈ s) (ht₀' : t ≤ t₀) :
    u (γ t).fst = (γ t).snd := by
  by_contra! Ht
  let ε := sInf {τ : ℝ | τ ∈ s ∧ t ≤ τ ∧ Δ γ u τ = 0}
  let ⟨ε_mem, ε_ge, Δ_ε⟩ := csInf_zero_set hγ hu' hs' ht₀ hγ₁ ht ht₀'
  obtain ⟨r, hr, hr', ⟨C, hC⟩⟩ := Δ_deriv_norm_le hγ₂ hu hγ hu' hs hE huGrad ε ε_mem (Δ_eq_zero_iff.mp Δ_ε).symm
  obtain ⟨τ, hτ, hτ', hτ''⟩ : ∃ τ, τ ∈ s ∧ τ < ε ∧
    ∀ t ∈ Set.Icc τ ε, Δ γ u t = 0 := by
    use (ε - r)
    have h₁ : ε - r < ε := by linarith
    have h₂ : Set.Icc (ε-r) ε ⊆ s := by
      apply subset_trans (Set.Icc_subset_Icc_right (by linarith)) hr'
    refine ⟨h₂ (Set.left_mem_Icc.mpr <| le_of_lt <| h₁), h₁, ?_⟩
    intro v hv
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K:=C) («a» := ε-r) (b := ε) ?_ (fun x hx => DifferentiableWithinAt.hasDerivWithinAt ?_) Δ_ε
    · intro x hx
      rw [DifferentiableAt.derivWithin (Δ_diff hγ₂ hu _) (uniqueDiffWithinAt_Iic _)]
      apply hC x <|  Set.Icc_subset_Icc_right (by linarith) (Set.Ioc_subset_Icc_self hx)
      apply h₂ (Set.Ioc_subset_Icc_self hx)
    · apply hv
    · apply (Δ_cts hγ hu').mono h₂
    · apply DifferentiableAt.differentiableWithinAt
      apply Δ_diff hγ₂ hu (h₂ (Set.Ioc_subset_Icc_self hx))
  by_cases hτ''' : t < τ
  · apply (lt_iff_not_le.mp hτ')
    refine csInf_le ?_ ⟨hτ, le_of_lt hτ''', hτ'' τ (Set.left_mem_Icc.mpr <| le_of_lt hτ')⟩
    use t
    intro v hv
    exact hv.right.left
  · apply Ht
    rw [←Δ_eq_zero_iff]
    apply hτ''
    rw [Set.mem_Icc]
    refine ⟨le_of_not_lt hτ''', ε_ge⟩

/--
If `u` is a solution to quasilinear PDE `E : a₁ ∂₁u + ... + aₙ ∂ₙu = c` and `γ = (X, U)`
is a characteristic curve of `E` such that `U(t₀) = u(X(t₀))` then the composite `u ∘ X` satisfies `d/dt (u ∘ X) = U`
for `t`
-/
theorem solution_constant_characteristic (hs' : IsConnected s) (t₀ : ℝ) (ht₀ : t₀ ∈ s)
    (huGrad : ContinuousOn (fderiv ℝ u) ((Prod.fst ∘ γ)''s))
    (hγ₁ : (γ t₀).snd = u (γ t₀).fst)
    (t : ℝ) (ht : t ∈ s) : u (γ t).fst = (γ t).snd := by
  rcases le_total t t₀ with ht₀' | ht₀'
  · apply solution_constant_characteristic_aux_t₀_ge hγ₂ hu hγ hu' hs hE hs' t₀ ht₀ huGrad hγ₁ t ht ht₀'
  · apply solution_constant_characteristic_aux_t₀_le hγ₂ hu hγ hu' hs hE hs' t₀ ht₀ huGrad hγ₁ t ht ht₀'

end MainTheorem


variable {𝕜 V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {γ : ℝ → V × ℝ} {u : V → ℝ}  {E : FirstOrderQuasiLinearPDE ℝ V}

theorem solution_constant_characteristic_univ
    (hγ₂ : ∀ t, E.HasCharacteristicAt γ t) (hu : ∀ t, E.HasSolutionAt u (γ t).1) (hγ : Continuous γ)
    (hu' : Continuous u) (hE : E.RegularBy (ContDiff ℝ 1)) (t₀ : ℝ)
    (huGrad : ContinuousOn (fderiv ℝ u) (Prod.fst ∘ γ '' Set.univ)) (hγ₁ : (γ t₀).2 = u (γ t₀).1) (t : ℝ) :
    u (γ t).1 = (γ t).2 :=
  solution_constant_characteristic (fun t _ => hγ₂ t) (fun t _ => hu t)
    hγ hu' isOpen_univ hE isConnected_univ t₀ (Set.mem_univ _) huGrad hγ₁ t (Set.mem_univ _)
