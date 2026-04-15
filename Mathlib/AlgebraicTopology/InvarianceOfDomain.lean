import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

set_option linter.directoryDependency false

open MeasureTheory MeasureTheory.Measure Metric
open scoped Topology
variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (E) in class BrouwerFixedPoint : Prop where
  brouwer_fixed_point (f : (closedBall (0 : E) 1) → (closedBall 0 1))
    (hf : Continuous f) : ∃ x, f x = x
variable [BrouwerFixedPoint E]

omit [BrouwerFixedPoint E] in
theorem differentiable_approx_of_continuous {δ : ℝ} (hδ : 0 < δ) {U : Set E}
    (hUcompact : IsCompact U) (G : E → E) (hG_cont : Continuous G) [Nontrivial E] :
    ∃ (P : C(E, E)), Differentiable ℝ P ∧ ∀ y ∈ U, ‖P y - G y‖ < δ := by
  let basis := stdOrthonormalBasis ℝ E
  let n := Module.finrank ℝ E
  -- We construct the subalgebra of polynomials from `ℝ^n` to `ℝ` and show they are differentiable
  -- Projecting onto one of the axes is continuous and differentiable
  let coord_sigma (i : Fin n) : C(E, ℝ) :=
    { toFun := fun x => basis.toBasis.equivFunL x i
      continuous_toFun := by fun_prop}
  have hcoord_diff (i : Fin n) : Differentiable ℝ (coord_sigma i) :=
    ((ContinuousLinearMap.proj i).comp
    (basis.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable
  -- This gives us the subalgebra of polynomials.
  let generator_sigma : Set C(E, ℝ) := Set.range coord_sigma
  have hgen_diff : ∀ f ∈ generator_sigma, Differentiable ℝ f := by
    rintro _ ⟨i, rfl⟩
    exact hcoord_diff i
  let A_sigma : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator_sigma
  have hA_diff : ∀ f ∈ A_sigma, Differentiable ℝ f := by
    let D : Subalgebra ℝ C(E, ℝ) :=
      { carrier := {f | Differentiable ℝ f}
        zero_mem' := differentiable_const 0
        one_mem' := differentiable_const 1
        add_mem' := fun hf hg => hf.add hg
        mul_mem' := fun hf hg => hf.mul hg
        algebraMap_mem' := fun r => differentiable_const r }
    have hgen_sub : generator_sigma ⊆ D := hgen_diff
    have hA_sub : A_sigma ≤ D := Algebra.adjoin_le hgen_sub
    exact fun f hf => hA_sub hf
  -- This subalgebra of polynomials separates points.
  have sep_sigma : A_sigma.SeparatesPoints := by
    intro x y hxy
    have hequiv: basis.toBasis.equivFunL x ≠ basis.toBasis.equivFunL y := by simpa
    obtain ⟨i, hi⟩ : ∃ i : (Fin n), basis.toBasis.equivFunL x i ≠ basis.toBasis.equivFunL y i := by
      contrapose! hequiv
      ext i
      exact (hequiv i)
    have hf_mem : coord_sigma i ∈ A_sigma := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨coord_sigma i, Set.mem_image_of_mem (fun f ↦ f.1) hf_mem, hi⟩
  let G_i (i : Fin n) : C(E, ℝ) :=
    { toFun := fun y => basis.toBasis.equivFunL (G y) i, continuous_toFun := by fun_prop }
  let coordEquiv := basis.toBasis.equivFunL
  have hpos_symm : 0 < ‖(coordEquiv.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h_eq => ?_
    let w : Fin n → ℝ := fun _ => 1
    have hw : w ≠ 0 := by
      have : 0 < n := Module.finrank_pos
      haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp this
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
      intro h
      have : w i = 0 := congr_fun h i
      linarith
    have hw0 : (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by
      rw [norm_eq_zero.1 h_eq.symm]
      rfl
    have hfalse : coordEquiv (coordEquiv.symm w) = coordEquiv 0 := congrArg coordEquiv hw0
    rw [coordEquiv.apply_symm_apply w, map_zero] at hfalse
    exact hw hfalse
  -- Define `C` as the operator norm for l.symm
  let C := ‖(coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E)‖
  let ε' := δ / (2 * C)
  have hε' : 0 < ε' := div_pos (RCLike.ofReal_pos.mp hδ) (mul_pos zero_lt_two hpos_symm)
  -- Using the Stone-Weierstrass theorem, pick each `P_i` to be `ε'-close` to each `G_i`.
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    sep_sigma (G_i i) hUcompact hε'
  choose p_i hp_i using approx
  -- Construct `P` as a function from `ℝ^n` to `ℝ^n` using the component functions `P_i`.
  let P : C(E, E) :=
    { toFun := fun y => basis.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
      continuous_toFun := by fun_prop}
  -- The difference between `P` and `G` on `Σ` is bounded by `δ`
  have hP_bound : ∀ y ∈ U , ‖P y - G y‖ < δ := by
    intro y hy
    let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (basis.toBasis.equivFunL (G y)) i
    have hv i : |v i| < ε' := by
      have := (hp_i i).2 y hy
      simp_all only [ ContinuousMap.coe_mk, Real.norm_eq_abs, G_i, v]
    have hnorm_v : ‖v‖ < ε' := by rw [pi_norm_lt_iff hε']; exact fun i => hv i
    have hP_eq : P y - G y = coordEquiv.symm v := by
      dsimp [P, v]
      have h_repr_eq : basis.toBasis.repr (G y) = coordEquiv (G y) := rfl
      have hG : G y = coordEquiv.symm (coordEquiv (G y)) := (coordEquiv.symm_apply_apply (G y)).symm
      have h_simp : coordEquiv (coordEquiv.symm (coordEquiv (G y))) = coordEquiv (G y) :=
        by rw [coordEquiv.symm_apply_apply (G y)]
      rw [h_repr_eq, hG, ← coordEquiv.symm.map_sub, h_simp]
      rfl
    rw [hP_eq]
    calc
      ‖coordEquiv.symm v‖
      ≤ C * ‖v‖ := ContinuousLinearMap.le_opNorm
          (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) v
    _ < C * ε' := mul_lt_mul_of_pos_left hnorm_v hpos_symm
    _ = δ / 2 := by
        unfold ε'
        field_simp [ne_of_gt hpos_symm]
        exact div_self (ne_of_gt hpos_symm)
    _ < δ := half_lt_self hδ
  have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
  have hP_diff : Differentiable ℝ P :=
    (basis.toBasis.equivFunL.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp
    (differentiable_pi.mpr hp_i_diff)
  use P







/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be an continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f ''(closedBall 0 1)) := by
  -- In the case where `n = 0`, `ℝ^0` has only a single point.
  cases subsingleton_or_nontrivial E
  · have : Set.Nonempty (interior (f '' closedBall 0 1)) := by simp
    rw [Set.Nonempty.eq_univ this]
    simp
  -- The equivalence between `B^n` and `f(B^n)`.
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  -- The inverse map of `f` is continuous.
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  -- `f(B^n)` is closed.
  have hballimageclosed : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
  -- The Tietze extension theorem, finding a continuous function `G` that extends `f⁻¹`.
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed FInvCmap
  -- `G` has a zero at `f 0`.
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' closedBall 0 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' closedBall 0 1) = FEquiv ⟨0, by simp⟩ :=
      Subtype.ext rfl
    simp [this, FInvCmap, fzero', H]
  -- Let `Gtilde : f(B^n) → ℝ^n` be a continuous function such that
  -- `‖G(y) - Gtilde(y)‖ ≤ 1 ∀ y ∈ f(B^n)`. Then `∃ y ∈ f (B^n)` such that `Gtilde(y)=0`.
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
    -- We apply Brouwer's fixed point theorem to diff_fun.
    let diff_fun : E → E := fun x => x - Gtilde (f x)
    -- `B^n` contains the image of itself under diff_fun.
    have hMaps_To : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) := by
      intro x hx
      have hfxin : f x ∈ f '' closedBall 0 1 := Set.mem_image_of_mem f hx
      have hxeq : x = G (f x) := by
        let e := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
        have hfxeq : ⟨f (x : E), hfxin⟩ = e ⟨x, mem_closedBall.mpr hx⟩ := SetCoe.ext rfl
        simp only [← G.restrict_apply_mk _ _ hfxin, hG, ContinuousMap.coe_mk, FInvCmap, FEquiv]
        rw [hfxeq, (e.symm_apply_apply ⟨x, mem_closedBall.mpr hx⟩)]
      have hbound := hy (f x) hfxin
      simp only [diff_fun, mem_closedBall_zero_iff]
      nth_rw 1 [hxeq]
      exact hbound
    -- diff_fun is continuous on `B^n`
    have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1) :=
      (continuousOn_id' _).sub (hGtilde.comp hf_cont (Set.mapsTo_image f _))
    -- We apply Brouwer's theorem. In particular, the fixed point of `Gtilde` is `f(x)`.
    obtain ⟨x, hx⟩ := BrouwerFixedPoint.brouwer_fixed_point (Set.MapsTo.restrict diff_fun
      (closedBall 0 1) (closedBall 0 1) hMaps_To)
      (ContinuousOn.mapsToRestrict diff_fun_cont_on hMaps_To)
    refine ⟨f x, ⟨⟨x ,⟨(by simp), rfl⟩⟩, ?_⟩⟩
    simp only [Subtype.ext_iff, Set.MapsTo.val_restrict_apply, sub_eq_self, diff_fun] at hx
    simp_all
  -- By way of contradiction, we assume that `f(0)` is not an interior point of `f(B^n)` .
  -- From this, we construct a `Gtilde` as in the above lemma to derive a contradiction.
  by_contra hnotinterior
  -- `G` is continuous at `f(0)`.
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  -- `G` is continuous on the whole space, so by picking `ε > 0` small enough,
  -- we can ensure `‖G(y)‖ ≤ 0.1` whenever `y ∈ ℝ^n` and `‖y - f(0)‖ ≤ 2ε`.
  obtain ⟨twoε, h2εpos, h2ε1⟩ := hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  -- As `f(0)` is not an interior point of `f(B^n)`, there exists a point `c ∈ ℝ^n` with
  -- `‖c - f(0)‖ < ε` not in `f(B^n)`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push_neg at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    obtain ⟨c, hc⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc.1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc.2⟩⟩
  -- `‖G(y)‖ ≤ 0.1` whenever `‖y - c‖ ≤ ε`.
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have hdist : ‖y - f 0‖ < 2 * ε := by
      have hineq := norm_add_le (y - c) (c - f 0)
      simp only [sub_add_sub_cancel] at hineq
      linarith
    rw [← h2εeq, ← dist_eq_norm ] at hdist
    have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp [mem_closedBall, zero_le_one], rfl⟩
    have hclose := h2ε1 hdist
    simp only [hG0, dist_zero_right] at hclose
    exact le_of_lt hclose
  -- Let `Σ₁ := {y ∈ f(B^n): ‖y - c‖ ≥ ε}`.
  let sigma1 : Set (E) := {y ∈ f '' closedBall 0 1 | ‖y - c‖ ≥ ε}
  -- Let `Σ₂ := {y ∈ ℝ^n : ‖y - c‖ = ε}`.
  let sigma2 : Set (E) := sphere c ε
  -- Let `Σ := Σ₁ ∪ Σ₂`.
  let sigma := sigma1 ∪ sigma2
  -- By construction, `Σ` is compact.
  -- `Σ₁` is compact.
  have hsigma1compact : IsCompact sigma1 := by
    rw [isCompact_iff_isClosed_bounded]
    -- `Σ₁` is the complement of the open ball, so it is closed.
    have hopen : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by simpa
    [← mem_ball_iff_norm, Set.compl_setOf, -isOpen_ball] using isOpen_ball (x := c) (ε := ε)
    -- `f(B^n)` is compact as it is the image of a compact set under a continuous function
    -- As compact sets are bounded and `Σ₁` is contained in this, `Σ₁` is bounded.
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    exact ⟨(IsClosed.and hballimageclosed ({isOpen_compl := (hopen) })), Bornology.IsBounded.subset
    (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
  -- It remains to be shown that `Σ₂` is compact, which follows from it being a sphere.
  have hsigmacompact : IsCompact sigma := IsCompact.union hsigma1compact (isCompact_sphere c ε)
  -- Let `Φ` be the function `Φ(y) := max(ε / ‖y - c‖, 1)) * (y - c)`.
  let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
  -- The image of `f(B^n)` under `Φ` is `Σ`.
  have hPhiimg (y : E) (hy : y ∈ f '' closedBall 0 1) : Phi y ∈ sigma := by
    by_cases h : ε < ‖y - c‖
    -- If `ε < ‖y - c‖`, then `Φ(y) ∈ Σ₁`.
    · left
      unfold Phi
      have hyc : 0 < ‖y - c‖ := by linarith
      have hright : ε / ‖y - c‖ < 1 := by rwa [div_lt_one hyc]
      simp only [max_eq_right_of_lt hright, one_smul, add_sub_cancel]
      exact ⟨hy, le_of_lt h⟩
    -- If `‖y - c‖ ≤ ε`, then `Φ(y) ∈ Σ₂`.
    · right
      simp only [not_lt] at h
      have hy_neq_c : c ≠ y := by
        by_contra h
        rw [← h] at hy
        exact hc2 hy
      have hleft : 1 ≤ ε / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr h
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by
        dsimp [Phi]
        rwa [max_eq_left]
      rw [hPhi]
      unfold sigma2
      simp [norm_smul, (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
  -- `Φ` is continuous.
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const (ContinuousOn.smul ?_
    (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const))
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const))) ?_) continuous_const
    intro x
    simp only [ne_eq, norm_eq_zero, sub_ne_zero]
    exact fun h => by subst h; simp_all
  -- By construction, `G` is non-zero on `Σ₁`
  have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
    intro y hy
    by_contra hGeq
    have hG_inj_on_image : Set.InjOn G (f '' closedBall 0 1) := by
      intro x hx y hy h
      have hx_eq : G x = FInvCmap ⟨x, hx⟩ := by
        rw [← ContinuousMap.restrict_apply G (f '' closedBall 0 1) ⟨x, hx⟩, hG]
      have hy_eq : G y = FInvCmap ⟨y, hy⟩ := by
        rw [← ContinuousMap.restrict_apply G (f '' closedBall 0 1) ⟨y, hy⟩, hG]
      rw [hx_eq, hy_eq] at h
      exact congr_arg Subtype.val (FEquiv.symm.injective h)
    have hyeq : y = f 0 := by
      have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
      apply hG_inj_on_image ((Set.mem_image f (closedBall 0 1) y).mpr hy.1)
        (Set.mem_image_of_mem f (by simp)) at heq
      assumption
    rw [Set.mem_sep_iff, hyeq] at hy
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1
    linarith
  -- The norm of `G` is continuous on `Σ₁`
  let normG : E → ℝ := fun y => ‖(G y : E)‖
  have hGconton : ContinuousOn G (f '' closedBall 0 1) := (ContinuousMap.continuous G).continuousOn
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1)
    fun x ↦ ‖x - c‖ ≥ ε)))
  -- As `Σ₁` is compact, `G` is bounded below on `Σ₁` by some `δ > 0`.
  -- We can shrink `δ` to assume `δ < 0.1`.
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := (min_le_right _ 0.05).trans_lt (by norm_num)
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := fun y hy => (min_le_left _ _).trans (hmin hy)
      exact ⟨δ, hδ_pos, hδ_lt_0_1, hδ_lower⟩
    · exact ⟨0.05, by norm_num, by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩
  obtain ⟨P, hP_diff, hP_bound⟩ :=
    differentiable_approx_of_continuous hδ1 hsigmacompact (fun (y: E) => (G y : E)) (by fun_prop)
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y : E)‖ ≥ δ := hδ3 y hy
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    simp only [h, _root_.zero_sub, norm_neg] at hP
    linarith
  -- It is possible that `P` vanishes on `Σ₂`, so we construct a perturbation `P'` that does not.
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `Σ₂` has measure `0`; `P` is differentiable. The image of `Σ₂` under P also has measure `0`.
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1))
  -- As the image of `Σ₂` under P also has measure `0`, we can find a point v in the ball of radius
  -- δ that is neither in `Σ₁` nor `Σ₂`
  obtain ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v : E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2 := by
    obtain hsigma1empty | hsigma1nonempty := sigma1.eq_empty_or_nonempty
    · have hball_pos := measure_ball_pos volume (0 : E) hδ1
      have hnot_subset2 : ¬ (ball 0 δ ⊆ P '' sigma2) := by
        intro hsub
        have : volume (ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
        grind
      rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
      exact ⟨v, ⟨mem_ball_zero_iff.mp hv_in_ball, ⟨by grind, by grind⟩⟩⟩
    have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
    -- Let `d` be a point of `Σ₁` such that `‖P(d)‖` takes its minimum value.
    let ⟨d, _, hd⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
    -- Let `k` be the minimum of these two, to ensure both properties.
    let k := min ‖P d‖ δ
    obtain ⟨v, hvnorm, hv1⟩ : ∃ a ∈ ball 0 k, a ∉ P '' sphere c ε := by
      rw [← Set.not_subset]
      intro hsub
      have : volume (ball (0 : E) k) ≤ 0 := by rw [← hP_image_null]; exact measure_mono hsub
      exact LT.lt.false (lt_of_lt_of_le (measure_ball_pos volume (0 : E)
        (lt_min_iff.mpr ⟨by simp only [norm_pos_iff, ne_eq]; grind, hδ1⟩)) this)
    refine ⟨v, ⟨by linarith [mem_ball_zero_iff.mp hvnorm, min_le_right ‖P d‖ δ],
      ⟨fun hin1 => ?_, fun hin2 ↦ hv1 hin2⟩⟩⟩
    rcases hin1 with ⟨x, hx, rfl⟩
    linarith [(isMinOn_iff.mp hd) x hx, mem_ball_zero_iff.mp hvnorm, min_le_left ‖P d‖ δ]
  -- Let `P'` be the perturbation of `P` such that `P'(y) = P(y) - v`.
  let P' : C(E, E) := {toFun := fun y => P y - v, continuous_toFun:= by fun_prop}
  -- `v` is not in `Σ`.
  have hv_notin_sigma : v ∉ P '' sigma := by grind
  -- Define `Gtilde : f(B^n) → ℝ^n` as `Gtilde(y) = P'(Φ(y))`.
  let Gtilde : E → E := fun y => P' (Phi y)
  -- `Gtilde` is continuous.
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1) :=
    (ContinuousMap.continuous P').comp_continuousOn hPhicont
  -- `P'` is never `0` on `Σ`. `Gtilde` is never `0`.
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 := by
    intro y hy h_eq
    exact hv_notin_sigma ⟨Phi y, hPhiimg y hy, sub_eq_zero.mp h_eq⟩
  -- We bound the difference between `G` and `Gtilde` by `1`.
  have hpeturbbound : ∀ y ∈ f '' (closedBall (0 : E) 1), ‖G y - Gtilde y‖ ≤ 1 := by
    intro y hy
    -- There are two possible cases for the norm of `y - c`.
    by_cases hP : ε < ‖y - c‖
    · -- If `ε < ‖y - c‖`, then `Φ(y) = y`
      -- Thus `Gtilde(y) = G(Φ(y))`
      unfold Gtilde
      have hPhi : Phi y = y := by
        unfold Phi
        have hright : ε / ‖y - c‖ < 1 := by
          have hyc : 0 < ‖y - c‖ := by linarith
          rwa [div_lt_one hyc]
        simp [max_eq_right_of_lt hright]
      rw [hPhi]
      -- We are using `P' = P - v`, `∀ y ∈ Σ, ‖P y - ↑(G y)‖ < δ` and `‖v‖ < δ`
      calc
        ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
        _ ≤ _ := by grw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_le, norm_sub_rev,
          hP_bound y (Or.inl ⟨hy, le_of_lt hP⟩), add_comm, hvnorm]
        _ ≤ _ := by linarith
    · -- If `‖y - c‖ ≤ ε`, then `Φ y ∈ Σ₂`.
      simp only [not_lt] at hP
      unfold Gtilde
      have hy_neq_c : c ≠ y := by
        by_contra h
        rw [← h] at hy
        exact hc2 hy
      have hleft : 1 ≤ ε / ‖y - c‖ :=
        (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr hP
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by
        unfold Phi
        rwa [max_eq_left]
      have hyimg : Phi y ∈ sphere c ε := by
        rw [hPhi]
        simp [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
      have hP_approx : ‖P (Phi y) - G (Phi y)‖ < δ := hP_bound (Phi y) (Or.inr hyimg)
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ := by
        have h : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + ‖P (Phi y) - (G (Phi y) : E)‖ :=
          norm_le_norm_add_norm_sub' _ _
        linarith [norm_sub_rev (P (Phi y)) (G (Phi y) : E)]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have hdist : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖ = ‖(Phi y - c) + (c - f 0)‖ := by grw [sub_add_sub_cancel]
          _ ≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at hdist
        have hclose := h2ε1 hdist
        simp only [hG0, dist_zero_right] at hclose
        exact le_of_lt hclose
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  -- We derive a contradiction using the lemma for the stability of zero.
  obtain ⟨y, hy1, hy2⟩ := (hStability_of_zero Gtilde hGtilde_cont) hpeturbbound
  exact hGtilde_nonzero y hy1 hy2

/-- Let `f : ℝ^n → ℝ^n` be a continuous and injective function. Then f is an open mapping. -/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U := by
    intro x' hx'
    obtain ⟨ε, hε, hball⟩ := hU x' hx'
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (div_two_lt_of_pos hε)).trans hball⟩
  obtain ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  -- Define `g` as a scaling and translating function.
  let g := fun (v : E) => ε • v + x
  have hg_cont : Continuous g := ((continuous_const_smul ε).add continuous_const : Continuous g)
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    unfold g
    rw [← Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1), Set.image_smul,
      smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have he_cont : ContinuousOn e (closedBall 0 1):=
    ContinuousOn.image_comp_continuous (h_g_eq ▸ hf_cont.mono hclosedball) (hg_cont)
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  -- `e(0)` is in the interior using the prior version.
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    invariance_of_domain_interior e he_cont he_inj
  refine ⟨interior (f '' U), ⟨interior_subset, isOpen_interior, ?_⟩⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior

/-- If `f` is a partial equivalence continuous on its source, then it maps
    neighbourhoods of `x` (contained in the source) to neighbourhoods of `f(x)`. -/
theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) := by
  intro hsin hsubset
  obtain ⟨a, ha1, ha2, ha3⟩ := _root_.mem_nhds_iff.mp hsin
  have ha4 : a ⊆ f.source := ha1.trans hsubset
  exact _root_.mem_nhds_iff.mpr ⟨f '' a, Set.image_mono ha1, invariance_of_domain_open_map (↑f) a
  ha2 (ContinuousOn.mono hCont ha4) (Set.InjOn.mono ha4 (PartialEquiv.injOn f)),
  Set.mem_image_of_mem (↑f) ha3⟩


/-- If there is an injective map `f` from `ℝ^n` to `ℝ^m`, then `n ≤ m`. -/
theorem invariance_of_dimension_of_injective
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [BrouwerFixedPoint E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    Module.finrank ℝ E ≤ Module.finrank ℝ F := by
  -- Suppose by contradiction that `m < n`.
  by_contra h
  rw [not_le] at h
  let n := (Module.finrank ℝ E)
  let m := (Module.finrank ℝ F)
  have hdimlt : m < n :=  Nat.lt_of_succ_le h
  -- Get bases and isomorphisms with Euclidean space.
  let basisE := stdOrthonormalBasis ℝ E
  let basisF := stdOrthonormalBasis ℝ F
  let coordE := basisE.repr
  let coordF := basisF.repr
  -- Takes a vector in `ℝ^m` to `ℝ^n` by filling the last entries with `0`,
  -- `(x₀, ..., x_m) → (x₀, ..., x_m, 0, ..., 0)`
  let pad : (Fin m → ℝ) → (Fin n → ℝ) := fun v i => if hi : i.val < m then v ⟨i.val, hi⟩ else 0
  let coordF_padded : F → (Fin n → ℝ) := fun x => pad (coordF x)
  let toEuclideanE : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  -- The inclusion map from `ℝ^m` to `ℝ^n`. It is continuous and injective.
  let incl : F → E := fun x =>
    coordE.symm (((EuclideanSpace.equiv (Fin n) ℝ).symm) (coordF_padded x))
  have hincl_cont : Continuous incl := by
    apply Continuous.comp' (LinearIsometryEquiv.continuous _)
    apply Continuous.comp' (ContinuousLinearEquiv.continuous _)
    exact continuous_pi fun i => by
      simp only [coordF_padded, pad, coordF]
      by_cases hi : i.val < m
      · simp only [dif_pos hi]; fun_prop
      · simp only [dif_neg hi]; exact continuous_const
  have hincl_inj : Function.Injective incl := by
    intro x y hxy
    apply coordF.injective
    ext i
    have hi : i.val < m := i.isLt
    have h : coordF_padded x = coordF_padded y := by
      have := congr_arg coordE hxy
      simp only [incl, LinearIsometryEquiv.apply_symm_apply,
        PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp.injEq] at this
      exact this
    have := congr_fun h ⟨i.val, by omega⟩
    simp only [coordF_padded, pad, hi, dif_pos] at this
    exact this
  -- The inclusion map composed with `f` gives `g`, a continuous and injective map
  -- from `ℝ^n` to `ℝ^n`.
  let g : E → E := incl ∘ f
  have hg_cont : Continuous g := hincl_cont.comp hf_cont
  have hg_inj : Function.Injective g := hincl_inj.comp hf_inj
  -- `ℝ^n` is open
  have hE_open : IsOpen (Set.univ : Set E) := isOpen_univ
  -- By invariance of domain, `g` is an open mapping and so `g(ℝ^n)` is open.
  have hg_img_open : IsOpen (g '' Set.univ) := invariance_of_domain_open_map g Set.univ isOpen_univ
    hg_cont.continuousOn hg_inj.injOn
  -- Use definition of open with balls.
  rw [Metric.isOpen_iff] at hg_img_open
  -- the `mth` coordinate of every point in the image is `0`.
  have hlastzero : ∀ x ∈ g '' Set.univ, (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ = 0 := by
    intro x ⟨y, _, hy⟩
    rw [← hy]
    simp only [PiLp.continuousLinearEquiv_symm_apply, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply, PiLp.continuousLinearEquiv_apply, lt_self_iff_false,
      ↓reduceDIte, coordE, g, incl, coordF_padded, pad]
  -- Consider some point `x` in the image of `g`.
  -- As the `mth` coordinate of every point of the image is `0`,
  have : (g '' Set.univ).Nonempty := Set.Nonempty.of_subtype
  let x : E := this.some
  have hx := Set.Nonempty.some_mem this
  -- There is a ball around it contained in `g(ℝ^n)`.
  rcases hg_img_open x hx with ⟨ε, hε, hball⟩
  -- `c` picks out the `mth` coordinate.
  let c : E → ℝ := fun y => (EuclideanSpace.equiv (Fin n) ℝ) (coordE y) ⟨m, h⟩
  -- The `mth` coordinate is `0` for every point in the ball around `x`.
  have hc_zero : ∀ y ∈ ball x ε, c y = 0 := fun y hy => (fun y hy => hlastzero y (hball hy)) y hy
  -- Take `x` and add `ε/2` in the `mth` coordinate to get a point `x'`.
  let x' : E := x + coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => if i = ⟨m, h⟩ then ε / 2 else 0))
  -- `x'` is in the `ε-ball` around `x`.
  have hx'_in_ball : x' ∈ ball x ε := by
    simp only [x', mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hconv : (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => if i = ⟨m, h⟩ then ε / 2 else 0) =
        EuclideanSpace.single ⟨m, h⟩ (ε / 2) := by
      ext i
      simp only [EuclideanSpace.single, EuclideanSpace.equiv,
        PiLp.continuousLinearEquiv_symm_apply]
      split_ifs with hi
      · rw [hi] ; simp
      · simp [hi]
    rw [LinearIsometryEquiv.norm_map, hconv, EuclideanSpace.norm_single,
      Real.norm_of_nonneg (by linarith)]
    linarith [half_lt_self hε]
  -- The `mth` coordinate of `x'` is non-zero, (as it is `ε/2`).
  have hx'_nonzero : c x' ≠ 0 := by
    have hsum : ((EuclideanSpace.equiv (Fin n) ℝ) (coordE x) + (EuclideanSpace.equiv (Fin n) ℝ)
      (coordE (coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
      fun i => if i = ⟨m, h⟩ then ε / 2 else 0)))) ⟨m, h⟩ =
      (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 := by simp [Pi.add_apply]
    have hcx : c x = 0 := hlastzero x hx
    unfold c at hcx
    have hsum2 : (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 = ε / 2 := by
      rw [hcx]
      ring
    simp only [x', c, map_add]
    rw [hsum, hsum2]
    linarith [half_pos hε]
  -- This contradicts all points in the ball having `mth` coordinate `0`.
  exact hx'_nonzero (hc_zero x' hx'_in_ball)

-- If there is a homeomorphism between `ℝ^m` and `ℝ^n`, then `m = n`
theorem invariance_of_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BrouwerFixedPoint E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BrouwerFixedPoint F]
    (φ : E ≃ₜ F) :
    Module.finrank ℝ E = Module.finrank ℝ F := by
  -- From the homeomorphism, getcontinuous and injective functions both ways and apply the above.
  let f : E → F := φ
  let g : F → E := φ.symm
  exact Nat.le_antisymm (invariance_of_dimension_of_injective f (φ.continuous) (φ.injective))
    (invariance_of_dimension_of_injective g (φ.symm.continuous) (φ.symm.injective))
