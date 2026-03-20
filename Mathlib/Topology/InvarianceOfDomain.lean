import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open MeasureTheory MeasureTheory.Measure Metric
open scoped Topology
variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (E) in class BrouwerFixedPoint : Prop where
  brouwer_fixed_point (f : (closedBall (0 : E) 1) → (closedBall 0 1))
    (hf : Continuous f) : ∃ x, f x = x
variable [BrouwerFixedPoint E]

/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be an continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f ''(closedBall 0 1)) := by
  -- In the case where `n = 0`, `ℝ^0` has only a single point.

  -- nontriviality E
  cases subsingleton_or_nontrivial E
  · have :  DiscreteTopology E := by infer_instance
    have : Set.Nonempty (interior (f '' closedBall 0 1)) := by simp
    have := Set.Nonempty.eq_univ this
    rw [this]
    exact Set.mem_univ (f 0)
  -- The equivalence between `B^n` and `f(B^n)`.
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  -- The inverse map of `f` is continuous.
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  -- `f(B^n)` is closed.
  have hballimageclosed : IsClosed (f '' closedBall 0 1) := IsClosed.mono
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed fun U a ↦ a
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
  -- `‖G(y)-Gtilde(y)‖ ≤ 1 ∀ y ∈ f(B^n)`. Then `∃ y ∈ f (B^n)` such that `Gtilde(y)=0`.
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
    -- We apply Brouwer's fixed point theorem to diff_fun.
    let diff_fun : E → E := fun x => x - Gtilde (f x)
    -- `B^n` contains the image of itself under diff_fun.
    have hMaps_To : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) := by
      intro x hx
      have hxeq : x = G (f x) := by
        have hfx : f x ∈ f '' closedBall 0 1 := Set.mem_image_of_mem f hx
        let e := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
        have hfxeq : ⟨f (x : E), hfx⟩ = e ⟨x, mem_closedBall.mpr hx⟩ := SetCoe.ext rfl
        simp only [← G.restrict_apply_mk _ _ hfx, hG, ContinuousMap.coe_mk, FInvCmap, FEquiv]
        rw [hfxeq, (e.symm_apply_apply ⟨x, mem_closedBall.mpr hx⟩)]
      have hfxin : f x ∈ f '' closedBall 0 1 := Set.mem_image_of_mem f hx
      apply hy (f x) at hfxin
      dsimp [diff_fun]
      nth_rw 1 [hxeq]
      exact mem_closedBall_zero_iff.mpr hfxin
    -- diff_fun is continuous on `B^n`
    have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1):= by
      apply ContinuousOn.sub (continuousOn_id' (closedBall 0 1))
      rw [continuousOn_iff_continuous_restrict]
      exact ContinuousOn.restrict
        (hGtilde.comp hf_cont (Set.mapsTo_image f (closedBall 0 1)))
    -- We apply Brouwer's theorem. In particular, the fixed point of `Gtilde` is `f(x)`.
    have ⟨x, hx⟩ := BrouwerFixedPoint.brouwer_fixed_point (Set.MapsTo.restrict diff_fun
      (closedBall 0 1) (closedBall 0 1) hMaps_To)
      (ContinuousOn.mapsToRestrict diff_fun_cont_on hMaps_To)
    refine ⟨f x, ⟨⟨x ,⟨(by simpa [mem_closedBall, dist_zero_right] using
      mem_closedBall_zero_iff.mp x.2), rfl⟩⟩, ?_⟩⟩
    simp only [Subtype.ext_iff, Set.MapsTo.val_restrict_apply, sub_eq_self, diff_fun] at hx
    simpa [Set.MapsTo.val_restrict_apply, sub_eq_self] using
      (AddOpposite.op_eq_zero_iff (Gtilde (f x))).mp (congrArg AddOpposite.op hx)
  -- By way of contradiction, we assume that `f(0)` is not an interior point of `f(B^n)` .
  -- From this, we construct a `Gtilde` as in the above lemma to derive a contradiction.
  by_contra hnotinterior
  -- `G` is continuous at `f(0)`.
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  -- `G` is continuous on the whole space, so by picking `ε > 0` small enough,
  -- we can ensure `‖G(y)‖ ≤ 0.1` whenever `y ∈ ℝ^n` and `‖y - f(0)‖ ≤ 2ε`.
  have ⟨twoε, h2εpos, h2ε1⟩ :=  hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  -- As `f(0)` is not an interior point of `f(B^n)`, there exists a point `c ∈ ℝ^n` with
  -- `‖c - f(0)‖ < ε` not in `f(B^n)`.
  have ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push_neg at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    have ⟨c, hc1, hc2⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc2⟩⟩
  -- `‖G(y)‖ ≤ 0.1` whenever `‖y - c‖ ≤ ε`.
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have : ‖y - f 0‖ < 2 * ε := calc
      ‖y - f 0‖ = ‖(y - c) + (c - f 0)‖ := by simp
      _≤ ‖y - c‖ + ‖c - f 0‖ := norm_add_le _ _
      _ < ε + ε := by linarith
      _ = 2 * ε := by ring
    rw [← h2εeq, ← dist_eq_norm ] at this
    have h0 : (0 : E) ∈ closedBall 0 1 := mem_closedBall_comm.mp (by simp)
    have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp [mem_closedBall, zero_le_one], rfl⟩
    have := h2ε1 this
    simp only [hG0, dist_zero_right] at this
    exact le_of_lt this
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
    have hcompl : {y | ‖y - c‖ ≥ ε}ᶜ = ball c ε := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_compl_iff, Set.notMem_setOf_iff, not_le] at hx
        exact mem_ball_iff_norm.mpr hx
      · intro hx
        simp only [ge_iff_le, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        exact mem_ball_iff_norm.mp hx
    have hopen : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by
      rw [hcompl]
      exact isOpen_ball
    -- `f(B^n)` is compact as it is the image of a compact set under a continuous function
    -- As compact sets are bounded and `Σ₁` is contained in this, `Σ₁` is bounded.
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    exact ⟨(IsClosed.and hballimageclosed ({isOpen_compl := hopen })), Bornology.IsBounded.subset
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
      have hright : ε / ‖y - c‖ < 1 := by
        rwa [div_lt_one hyc]
      simp only [max_eq_right_of_lt hright, one_smul, add_sub_cancel]
      exact ⟨hy, le_of_lt h⟩
    -- If `ε < ‖y - c‖`, then `Φ(y) ∈ Σ₂`.
    · right
      simp only [not_lt] at h
      have hy_neq_c : c ≠ y := by
        by_contra h
        rw [← h] at hy
        exact hc2 hy
      have hleft : 1 ≤ ε / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr h
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by
        unfold Phi
        rwa [max_eq_left]
      rw [hPhi]
      unfold sigma2
      simp [norm_smul, (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
  -- `Φ` is continuous.
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const ?_
    refine ContinuousOn.smul ?_
      (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const)
    rw [continuousOn_iff_continuous_restrict]
    refine Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const))) ?_) continuous_const
    intro x
    simp only [ne_eq, norm_eq_zero]
    by_contra hx
    rw [sub_eq_zero] at hx
    subst hx
    simp_all only [Subtype.coe_prop, not_true_eq_false]
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
  have hGconton := Continuous.continuousOn (ContinuousMap.continuous G)
    (s := f '' closedBall 0 1)
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1)
    fun x ↦ ‖x - c‖ ≥ ε)))
  -- As `Σ₁` is compact, `G` is bounded below on `Σ₁` by some `δ > 0`.
  -- We can shrink `δ` to assume `δ < 0.1`.
  have hδ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · have ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := by
        calc δ ≤ 0.05 := min_le_right (normG z) 5e-2
        _ < 0.1 := by norm_num
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := by
        intro y hy
        calc normG y ≥ normG z := hmin hy
          _ ≥ δ := min_le_left _ _
      use δ
    · exact ⟨0.05, ⟨by norm_num, ⟨by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩⟩⟩
  -- Take the standard orthonormal basis
  let b := stdOrthonormalBasis ℝ E
  let n := Module.finrank ℝ E
  -- We construct the subalgebra of polynomials from `ℝ^n` to `ℝ` and show they are differentiable
  -- Projecting onto one of the axes is continuous and differentiable
  let coord_sigma (i : Fin n) : C(E, ℝ) :=
    { toFun := fun x => b.toBasis.equivFunL x i
      continuous_toFun := by fun_prop }
  have hcoord_diff (i : Fin n) : Differentiable ℝ (coord_sigma i) := by
    let proj_i : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (proj_i.comp (b.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable
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
    have : generator_sigma ⊆ D := hgen_diff
    have : A_sigma ≤ D := Algebra.adjoin_le this
    exact fun f hf => this hf
  -- This subalgebra of polynomials separates points.
  have sep_sigma : A_sigma.SeparatesPoints := by
    intro x y hxy
    have hequiv: b.toBasis.equivFunL x ≠ b.toBasis.equivFunL y := by simpa
    obtain ⟨i, hi⟩ : ∃ i : (Fin n), b.toBasis.equivFunL x i ≠ b.toBasis.equivFunL y i := by
      contrapose! hequiv
      ext i
      exact (hequiv i)
    let f := coord_sigma i
    have hf_mem : f ∈ A_sigma := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨f, ⟨Set.mem_image_of_mem (fun f ↦ f.1) (hf_mem), hi⟩⟩
  -- Define component functions of `G`.
  let G_i (i : Fin n) : C(E, ℝ) :=
    { toFun := fun y => b.toBasis.equivFunL (G y) i,
      continuous_toFun := by
        fun_prop }
  let l := b.toBasis.equivFunL
  have hpos_symm : 0 < ‖(l.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      intro h_eq
      have h_zero : (l.symm : (Fin n → ℝ) →L[ℝ] E) = 0 := norm_eq_zero.1 h_eq.symm
      let w : Fin n → ℝ := fun _ => 1
      have hw : w ≠ 0 := by
        haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp
          ((Module.finrank_pos_iff_of_free ℝ E).mpr hnontrivial)
        rcases (show Nonempty (Fin n) by infer_instance) with ⟨i⟩
        intro h
        have : w i = 0 := congr_fun h i
        linarith
      have : (l.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by rw [h_zero]; rfl
      have : l (l.symm w) = l 0 := congrArg l this
      rw [l.apply_symm_apply w, map_zero] at this
      exact hw this
  -- Define `C` as the operator norm for l.symm
  let C := ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖
  rcases hδ with ⟨δ, hδ1, ⟨hδ2, hδ3⟩⟩
  let ε' := δ / (2 * C)
  have hε' : 0 < ε' := div_pos (RCLike.ofReal_pos.mp hδ1)
    (mul_pos zero_lt_two hpos_symm)
  -- Using the Stone-Weierstrass theorem, pick each `P_i` to be `ε'-close` to each `G_i`.
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    sep_sigma (G_i i) hsigmacompact hε'
  choose p_i hp_i using approx
  -- Construct `P` as a function from `ℝ^n` to `ℝ^n` using the component functions `P_i`.
  let P : C(E, E) :=
    { toFun := fun y => b.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
      continuous_toFun := by fun_prop}
  -- The difference between `P` and `G` on `Σ` is bounded by `δ`
  have hP_bound : ∀ y ∈ sigma , ‖P y - G y‖ < δ := by
    intro y hy
    let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (b.toBasis.equivFunL (G y)) i
    have hv i : |v i| < ε' := by
      have := (hp_i i).2 y hy
      simp_all only [ ContinuousMap.coe_mk, Real.norm_eq_abs, G_i, v]
    have hnorm_v : ‖v‖ < ε' := by
      rw [pi_norm_lt_iff hε']
      intro i
      exact hv i
    have hP_eq : P y - G y = l.symm v := by
      dsimp [P, v]
      have h_repr_eq : b.toBasis.repr (G y) = l (G y) := rfl
      have hG : G y = l.symm (l (G y)) := (l.symm_apply_apply (G y)).symm
      have h_simp : l (l.symm (l (G y))) = l (G y) := by rw [l.symm_apply_apply (G y)]
      rw [h_repr_eq, hG, ← l.symm.map_sub, h_simp]
      rfl
    rw [hP_eq]
    calc
      ‖l.symm v‖ < C * ε' := lt_of_le_of_lt (ContinuousLinearMap.le_opNorm_of_le
      (l.symm : (Fin n → ℝ) →L[ℝ] E) (le_refl ‖v‖)) (mul_lt_mul_of_pos_left hnorm_v hpos_symm)
      _ = δ / 2 := by
        unfold ε'
        field_simp
        rw [div_self_eq_one₀]
        exact Ne.symm (ne_of_lt hpos_symm)
      _ < δ := half_lt_self hδ1
  -- This ensures that `P` does not vanish on `Σ₁` using hδ3
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y :E)‖ ≥ δ := (hδ3 y hy)
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    rw [h] at hP
    have : ‖(G y : E)‖ = ‖G y - P y‖ := by rw [h, sub_zero]
    simp only [_root_.zero_sub, norm_neg] at hP
    linarith
  -- It is possible that `P` vanishes on `Σ₂`, so we construct a perturbation `P'` that does not.
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `Σ₂` has measure `0`.
  have h_sphere_null := MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1)
  -- `P` is differentiable.
  have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
  have hP_diff : Differentiable ℝ P :=
  (l.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp (differentiable_pi.mpr hp_i_diff)
  -- So the image of `Σ₂` under P also has measure `0`/
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn h_sphere_null
  -- As the image of `Σ₂` under P also has measure `0`, we can find a point v in the ball of radius
  -- δ that is neither in `Σ₁` nor `Σ₂`
  have ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v: E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2:= by
    by_cases hsigma1nonempty : sigma1.Nonempty
    · have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
      -- Let `d` be a point of `Σ₁` such that `‖P(d)‖` takes its minimum value.
      let ⟨d, hd, hd2⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
      have hnormpd : 0 < ‖P d‖ := by
        simp only [norm_pos_iff, ne_eq]
        by_contra heq0
        have : 0 ∈ P '' sigma1 := by
          rw [← heq0]
          exact Set.mem_image_of_mem (⇑P) hd
        exact h0_notin_image this
      -- Let `k` be the minimum of these two, to ensure both properties.
      let k := min ‖P d‖ δ
      have hk : 0 < k := lt_min_iff.mpr ⟨hnormpd, hδ1⟩
      have hball_pos := measure_ball_pos volume (0 : E) hk
      have hnot_subset : ¬ (ball 0 k ⊆ P '' sphere c ε) := by
        intro hsub
        have : volume (ball (0 : E) k) ≤ volume (P '' sphere c ε) := measure_mono hsub
        rw [hP_image_null] at this
        have := lt_of_lt_of_le hball_pos this
        exact LT.lt.false this
      rw [Set.not_subset] at hnot_subset
      rcases hnot_subset with ⟨v, hvnorm, hv1⟩
      use v
      refine ⟨by linarith [mem_ball_zero_iff.mp hvnorm, min_le_right ‖P d‖ δ],
        ⟨?_, fun hin2 ↦ hv1 hin2⟩⟩
      intro hin1
      rcases hin1 with ⟨x, hx, rfl⟩
      have : ‖P x‖ ≥ ‖P d‖ := by
        rw [isMinOn_iff] at hd2
        exact hd2 x hx
      have : ‖P x‖ < k := mem_ball_zero_iff.mp hvnorm
      have : k ≤ ‖P d‖ := min_le_left ‖P d‖ δ
      linarith
    · have hball_pos := measure_ball_pos volume (0 : E) hδ1
      have hnot_subset2 : ¬ (ball 0 δ ⊆ P '' sigma2) := by
        intro hsub
        have : volume (ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
        grind
      rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
      use v
      refine ⟨mem_ball_zero_iff.mp hv_in_ball, ⟨?_, by grind⟩⟩
      intro h1
      exfalso
      rcases h1 with ⟨x, hx, rfl⟩
      exact hsigma1nonempty ⟨x, hx⟩
  -- Let `P'` be the perturbation of `P` such that `P'(y) = P(y) - v`.
  let P' : C(E, E) := { toFun := fun y => P y - v, continuous_toFun:= by fun_prop}
  -- `v` is not in `Σ`.
  have hv_notin_sigma : v ∉ P '' sigma := by
    rw [Set.image_union]
    intro h
    rcases h with (h1 | h2)
    · exact hv1 h1
    · exact hv2 h2
  -- `P'` is never `0` on `Σ`.
  have hP'_nonvanishing_sigma : ∀ y ∈ sigma, P' y ≠ 0 := fun y hy h_eq ↦
    hv_notin_sigma ⟨y, hy, sub_eq_zero.mp h_eq⟩
  -- Define `Gtilde : f(B^n) → ℝ^n` as `Gtilde(y) = P'(Φ(y))`.
  let Gtilde : E → E := fun y => P' (Phi y)
  -- `Gtilde` is continuous.
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1):= by
    unfold Gtilde
    rw [continuousOn_iff_continuous_restrict]
    exact Continuous.comp (ContinuousMap.continuous P') (ContinuousOn.restrict hPhicont)
  -- `Gtilde` is never `0`.
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 :=
  fun y hy => hP'_nonvanishing_sigma (Phi y) (hPhiimg y hy)
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
        rw [max_eq_right_of_lt hright]
        simp
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
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ :=
        calc
          ‖P (Phi y)‖ = ‖G (Phi y) + (P (Phi y) - G (Phi y))‖ := by simp only [add_sub_cancel]
          _ ≤ ‖(G (Phi y) : E)‖ + δ := by grw [norm_add_le, add_le_add (le_refl ‖(G (Phi y) : E)‖)
            (le_of_lt hP_approx)]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖ = ‖(Phi y - c) + (c - f 0)‖ := by grw [sub_add_sub_cancel]
          _≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at this
        have := h2ε1 this
        simp only [hG0, dist_zero_right] at this
        exact le_of_lt this
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  -- We derive a contradiction using the lemma for the stability of zero.
  have ⟨y, hy1, hy2⟩ := (hStability_of_zero Gtilde hGtilde_cont) hpeturbbound
  exact hGtilde_nonzero y hy1 hy2

/-- Let `f : ℝ^n → ℝ^n` be a continuous and injective function.
Then f is an open mapping.-/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U:= by
    intro x' hx'
    specialize hU x'
    apply hU at hx'
    rcases hx' with ⟨ε, hε, hball⟩
    refine ⟨ε/2, half_pos hε, ?_⟩
    trans ball x' ε
    · exact closedBall_subset_ball (div_two_lt_of_pos hε)
    · exact hball
  have ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  -- Define `g` as a scaling and translating function.
  let g := fun (v : E) => ε • v + x
  have hg_cont : Continuous g := ((continuous_const_smul ε).add continuous_const : Continuous g)
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    unfold g
    rw [Eq.symm (Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1)),
      Set.image_smul, smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have hfconton : ContinuousOn f (g '' closedBall 0 1) := by
    rw [h_g_eq]
    exact ContinuousOn.mono hf_cont hclosedball
  have hfinjon : Set.InjOn f (g '' closedBall 0 1) := by
    rw [h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  have he_cont : ContinuousOn e (closedBall 0 1):= ContinuousOn.image_comp_continuous hfconton hg_cont
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  -- `e(0)` is in the interior using the prior version.
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    invariance_of_domain_interior e he_cont he_inj
  use interior (f '' U)
  refine ⟨interior_subset, isOpen_interior, ?_⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior


theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) := by
  intro hsin hsubset
  rw [_root_.mem_nhds_iff] at hsin
  have ⟨a, ha1, ha2, ha3⟩ := hsin
  have ha4 : a ⊆ f.source := LE.le.subset fun ⦃a_1⦄ a ↦ hsubset (ha1 a)
  have ha5 : ContinuousOn f a := ContinuousOn.mono hCont ha4
  have hf : Set.InjOn f f.source := PartialEquiv.injOn f
  have ha6 : Set.InjOn f a := Set.InjOn.mono ha4 hf
  have hfimg : IsOpen (f '' a) := invariance_of_domain_open_map (↑f) a ha2 ha5 ha6
  have hsubst : f '' a ⊆ f '' s := by exact Set.image_mono ha1
  apply _root_.mem_nhds_iff.mpr
  refine ⟨f '' a, hsubst, hfimg, Set.mem_image_of_mem (↑f) ha3⟩
