module

public import Mathlib

open Set Metric Function
open scoped Pointwise Topology

public section

@[to_additive (attr := simp)]
theorem Set.smul_set_eq_univ {G α : Type*} [Group G] [MulAction G α] {g : G} {s : Set α} :
    g • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, smul_set_univ]

namespace Complex

theorem exists_branch_log {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U) (hU₀ : 0 ∉ U) :
    ∃ f : ℂ → ℂ, ContinuousOn f U ∧ LeftInvOn exp f U := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : x₀ ≠ 0 := ne_of_mem_of_not_mem hx₀U hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts (.restrict U (.id ℂ)) (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem x.2 hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ z : U, g z = f z :=
    ⟨fun z ↦ if hz : z ∈ U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

theorem exists_branch_nthRoot {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U) (hU₀ : 0 ∉ U)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ f : ℂ → ℂ, ContinuousOn f U ∧ LeftInvOn (· ^ n) f U := by
  rcases exists_branch_log hUc hUo hU₀ with ⟨f, hfc, hf⟩
  refine ⟨fun z ↦ exp (f z / n), by fun_prop, fun z hz ↦ ?_⟩
  simp only [← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), hf hz]

theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU]) (x := -a + x)
      (by simpa [mem_vadd_set_iff_neg_vadd_mem]) (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf₁, hf_inj, hdf⟩
    refine ⟨f ∘ (-a + ·), hf₁.comp (mapsTo_image _ _),
      hf_inj.comp (by simp [InjOn]) (mapsTo_image _ _), fun z hz ↦ ?_⟩
    simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  rcases exists_branch_nthRoot hUc hUo hU₀ two_ne_zero with ⟨f, hfc, hf_inv⟩
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv hz
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · filter_upwards [hUo.mem_nhds hz] using hf_inv
  have hdf' : DifferentiableOn ℂ f U := fun z hz ↦
    (hdf z hz).hasFDerivAt.hasFDerivWithinAt.differentiableWithinAt
  have hfUx : f '' U ∈ 𝓝 (f x) := by
    rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
    exact Filter.image_mem_map <| hUo.mem_nhds hx
  have hdisj : ∀ a ∈ U, ∀ b ∈ U, f a + f b ≠ 0 := by
    intro a ha b hb hfab
    obtain rfl : b = a := by
      rw [← hf_inv ha, ← hf_inv hb]
      simp [eq_neg_iff_add_eq_zero.mpr hfab]
    have : f b = 0 := by linear_combination hfab / 2
    exact hf₀ b hb this
  have hfUxc : (f '' U)ᶜ ∈ 𝓝 (-f x) := by
    rw [nhds_neg, Filter.mem_neg]
    filter_upwards [hfUx]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hdisj a ha b hb (by linear_combination hab)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hfUxc with ⟨ε, hε₀, hε⟩
  use fun z ↦ ε / (f x + f z)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · by_contra! hle
      refine @hε (f z) ?_ (mem_image_of_mem f hz)
      simpa [dist_eq_norm, add_comm] using hle
    · simpa using hdisj x hx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inv.injOn.eq_iff hz hw] using heq
  case deriv =>
    intro z hz
    rw [(hasDerivAt_const _ _).fun_div ((hdf z hz).hasDerivAt.const_add _) _ |>.deriv]
    · simp [hε₀.ne', hf₀ z hz, hdisj x hx z hz]
    · exact hdisj x hx z hz

theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero₀ {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, f x = 0 ∧ MapsTo f U (ball 0 1) ∧ InjOn f U ∧
      ∀ z ∈ U, deriv f z ≠ 0 := by
  rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU hx with ⟨f, hfU, hf_inj, hdf⟩


end Complex
