/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! # The unitary group in a unital C⋆-algebra is locally path connected

When `A` is a unital C⋆-algebra and `u : unitary A` is a unitary element whose distance to `1` is
less that `2`, the spectrum of `u` is contained in the slit plane, so the principal branch of the
logarithm is continuous on the spectrum of `u` (or equivalently, `Complex.arg` is continuous on the
spectrum). The continuous functional calculus can then be used to define a selfadjoint element `x`
such that `u = exp (I • x)`. Moreover, there is a relatively nice relationship between the norm of
`x` and the norm of `u - 1`, namely `‖u - 1‖ ^ 2 = 2 * (1 - cos ‖x‖)`. In fact, these maps `u ↦ x`
and `x ↦ u` establish a partial homeomorphism between `ball (1 : unitary A) 2` and
`ball (0 : selfAdjoint A) π`.

The map `t ↦ exp (t • (I • x))` constitutes a path from `1` to `u`, showing that unitary elements
sufficiently close (i.e., within a distance `2`) to `1 : unitary A` are path connected to `1`.
This property can be translated around the unitary group to show that if `u v : unitary A` are
unitary elements with `‖u - v‖ < 2`, then there is a path joining them. In fact, this path has the
property that it lies within `closedBall u ‖u - v‖`, and consequently any ball of radius `δ < 2` in
`unitary A` is path connected. Therefore, the unitary group is locally path connected.

Finally, we provide the standard characterization of the path component of `1 : unitary A` as finite
products of exponential unitaries.

## Main results

+ `Unitary.argSelfAdjoint`: the selfadjoint element obtained by taking the argument (using the
  principal branch and the continuous functional calculus) of a unitary. This returns `0` if
  the principal branch of the logarithm is not continuous on the spectrum of the unitary element.
+ `selfAdjoint.norm_sq_expUnitary_sub_one`:
  `‖(selfAdjoint.expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)`
+ `Unitary.norm_argSelfAdjoint`:
  `‖Unitary.argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)`
+ `Unitary.openPartialHomeomorph`: the maps `Unitary.argSelfAdjoint` and `selfAdjoint.expUnitary`
  form a partial homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
+ `selfAdjoint.expUnitaryPathToOne`: the path `t ↦ expUnitary (t • x)` from `1` to
  `expUnitary x` for a selfadjoint element `x`.
+ `Unitary.isPathConnected_ball`: any ball of radius `δ < 2` in the unitary group of a unital
  C⋆-algebra is path connected.
+ `Unitary.instLocPathConnectedSpace`: the unitary group of a C⋆-algebra is locally path connected.
+ `Unitary.mem_pathComponentOne_iff`: The path component of the identity in the unitary group of a
  C⋆-algebra is the set of unitaries that can be expressed as a product of exponentials of
  selfadjoint elements.
-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A]

open Complex Metric NormedSpace selfAdjoint Unitary
open scoped Real

lemma Unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u ∈ unitary A)
    {z : ℂ} (hz : z ∈ spectrum ℂ u) :
    2 * (1 - z.re) ≤ ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  convert norm_apply_le_norm_cfc (fun z ↦ z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_eq_one this)).symm

@[deprecated (since := "2025-10-29")] alias unitary.two_mul_one_sub_le_norm_sub_one_sq :=
  Unitary.two_mul_one_sub_le_norm_sub_one_sq

lemma Unitary.norm_sub_one_sq_eq {u : A} (hu : u ∈ unitary A) {x : ℝ}
    (hz : IsLeast (re '' (spectrum ℂ u)) x) :
    ‖u - 1‖ ^ 2 = 2 * (1 - x) := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  have h_eqOn : (spectrum ℂ u).EqOn (fun z ↦ ‖z - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
    Complex.norm_sub_one_sq_eqOn_sphere.mono <| spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu
  have h₂ : IsGreatest ((fun z ↦ 2 * (1 - z.re)) '' (spectrum ℂ u)) (2 * (1 - x)) := by
    have : Antitone (fun y : ℝ ↦ 2 * (1 - y)) := by intro _ _ _; simp only; gcongr
    simpa [Set.image_image] using this.map_isLeast hz
  have h₃ : IsGreatest ((‖· - 1‖ ^ 2) '' spectrum ℂ u) (‖cfc (· - 1 : ℂ → ℂ) u‖ ^ 2) := by
    have := pow_left_monotoneOn (n := 2) |>.mono (s₂ := ((‖· - 1‖) '' spectrum ℂ u)) (by simp)
    simpa [Set.image_image] using this.map_isGreatest (IsGreatest.norm_cfc (fun z : ℂ ↦ z - 1) u)
  exact h₃.unique (h_eqOn.image_eq ▸ h₂)

@[deprecated (since := "2025-10-29")] alias unitary.norm_sub_one_sq_eq := Unitary.norm_sub_one_sq_eq

lemma Unitary.norm_sub_one_lt_two_iff {u : A} (hu : u ∈ unitary A) :
    ‖u - 1‖ < 2 ↔ -1 ∉ spectrum ℂ u := by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
    have := two_mul_one_sub_le_norm_sub_one_sq hu h1 |>.trans_lt h
    norm_num at this
  · contrapose!
    obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := ℂ) u |>.image continuous_re |>.exists_isLeast <|
      (spectrum.nonempty _).image _
    rw [norm_sub_one_sq_eq hu hx]
    obtain ⟨z, hz, rfl⟩ := hx.1
    intro key
    replace key : z.re ≤ -1 := by linarith
    have hz_norm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
    rw [← hz_norm, ← RCLike.re_eq_complex_re, RCLike.re_le_neg_norm_iff_eq_neg_norm, hz_norm] at key
    exact key ▸ hz

@[deprecated (since := "2025-10-29")] alias unitary.norm_sub_one_lt_two_iff :=
  Unitary.norm_sub_one_lt_two_iff

lemma Unitary.spectrum_subset_slitPlane_iff_norm_lt_two {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ slitPlane ↔ ‖u - 1‖ < 2 := by
  simp [subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary hu),
    norm_sub_one_lt_two_iff hu]

@[deprecated (since := "2025-10-29")] alias unitary.spectrum_subset_slitPlane_iff_norm_lt_two :=
  Unitary.spectrum_subset_slitPlane_iff_norm_lt_two

@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (ofReal ∘ arg : ℂ → ℂ) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

/-- The selfadjoint element obtained by taking the argument (using the principal branch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum of the unitary
element. -/
@[simps]
noncomputable def Unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A :=
  ⟨cfc (arg · : ℂ → ℂ) (u : A), .cfc_arg (u : A)⟩

@[deprecated (since := "2025-10-29")] alias unitary.argSelfAdjoint := Unitary.argSelfAdjoint

lemma selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ ≤ π) :
    ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) := by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul I _ (x : A), cfc_map_spectrum ..,
    ← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ,
    exp_ofReal_mul_I_re]
  refine ⟨?_, ?_⟩
  · cases CStarAlgebra.norm_or_neg_norm_mem_spectrum x.2 with
    | inl h => exact ⟨_, h, rfl⟩
    | inr h => exact ⟨_, h, by simp⟩
  · rintro - ⟨y, hy, rfl⟩
    exact Real.cos_abs y ▸ Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx <|
      spectrum.norm_le_norm_of_mem hy

lemma argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) :
    argSelfAdjoint (expUnitary x) = x := by
  nontriviality A
  ext
  have : spectrum ℂ (expUnitary x : A) ⊆ slitPlane := by
    rw [spectrum_subset_slitPlane_iff_norm_lt_two (expUnitary x).2,
      ← sq_lt_sq₀ (by positivity) (by positivity), norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1 - Real.cos π) := by
        gcongr
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
      _ = 2 ^ 2 := by norm_num
  simp only [argSelfAdjoint_coe, expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul .., ← cfc_comp' (hg := ?hg)]
  case hg =>
    refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
    rwa [expUnitary_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul ..,
      cfc_map_spectrum ..] at this
  conv_rhs => rw [← cfc_id' ℂ (x : A)]
  refine cfc_congr fun y hy ↦ ?_
  rw [← x.2.spectrumRestricts.algebraMap_image] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  simp only [coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ, ofReal_inj]
  replace hy : ‖y‖ < π := spectrum.norm_le_norm_of_mem hy |>.trans_lt hx
  simp only [Real.norm_eq_abs, abs_lt] at hy
  rw [← Circle.coe_exp, Circle.arg_exp hy.1 hy.2.le]

lemma expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) :=
    continuousOn_arg.mono <| (spectrum_subset_slitPlane_iff_norm_lt_two u.2).mpr hu
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

lemma Unitary.norm_argSelfAdjoint_le_pi (u : unitary A) :
    ‖argSelfAdjoint u‖ ≤ π :=
  norm_cfc_le (by positivity) fun y hy ↦ by simpa using abs_arg_le_pi y

@[deprecated (since := "2025-10-29")] alias unitary.norm_argSelfAdjoint_le_pi :=
  Unitary.norm_argSelfAdjoint_le_pi

lemma Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    2 * (1 - Real.cos ‖argSelfAdjoint u‖) = ‖(u - 1 : A)‖ ^ 2 := by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
  exact Eq.symm <| norm_sq_expUnitary_sub_one <| norm_argSelfAdjoint_le_pi u

@[deprecated (since := "2025-10-29")] alias unitary.two_mul_one_sub_cos_norm_argSelfAdjoint :=
  Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint

lemma Unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) := by
  refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_ |>.symm
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

@[deprecated (since := "2025-10-29")] alias unitary.norm_argSelfAdjoint :=
  Unitary.norm_argSelfAdjoint

set_option backward.isDefEq.respectTransparency false in
lemma Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(expUnitary (t • argSelfAdjoint u) - 1 : A)‖ ≤ ‖(u - 1 : A)‖ := by
  have key : ‖t • argSelfAdjoint u‖ ≤ ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUnitary_sub_one (key.trans <| norm_argSelfAdjoint_le_pi u)]
  trans 2 * (1 - Real.cos ‖argSelfAdjoint u‖)
  · gcongr
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (norm_argSelfAdjoint_le_pi u) key
  · exact (two_mul_one_sub_cos_norm_argSelfAdjoint hu).le

@[deprecated (since := "2025-10-29")] alias
  unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le :=
  Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le

@[fun_prop]
lemma Unitary.continuousOn_argSelfAdjoint :
    ContinuousOn (argSelfAdjoint : unitary A → selfAdjoint A) (ball (1 : unitary A) 2) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp only [SetLike.coe_sort_coe, Function.comp_def, argSelfAdjoint_coe]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le_of_lt (by positivity) huε
  have huε' : dist u 1 < √ε := Real.lt_sqrt_of_sq_lt huε
  apply ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_of_mem huε')
  apply ContinuousOn.image_comp_continuous ?_ continuous_subtype_val
  apply continuousOn_cfc A (s := sphere 0 1 ∩ {z | 2 * (1 - z.re) ≤ ε}) ?_ _ ?_ |>.mono
  · rintro - ⟨v, hv, rfl⟩
    simp only [Set.subset_inter_iff, Set.mem_setOf_eq]
    refine ⟨inferInstance, spectrum_subset_circle v, ?_⟩
    intro z hz
    simp only [Set.mem_setOf_eq]
    trans ‖(v - 1 : A)‖ ^ 2
    · exact two_mul_one_sub_le_norm_sub_one_sq v.2 hz
    · refine Real.le_sqrt (by positivity) (by positivity) |>.mp ?_
      simpa [Subtype.dist_eq, dist_eq_norm] using hv
  · exact isCompact_sphere 0 1 |>.inter_right <| isClosed_le (by fun_prop) (by fun_prop)
  · refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
    apply subset_slitPlane_iff_of_subset_sphere Set.inter_subset_left |>.mpr
    norm_num at hε2 ⊢
    exact hε2

@[deprecated (since := "2025-10-29")] alias unitary.continuousOn_argSelfAdjoint :=
  Unitary.continuousOn_argSelfAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`. -/
@[simps]
noncomputable def Unitary.openPartialHomeomorph :
    OpenPartialHomeomorph (unitary A) (selfAdjoint A) where
  toFun := argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos (1 - 2 ^ 2 / 2) := by
        apply Real.arccos_lt_arccos (by norm_num) (by gcongr)
        linarith [(by positivity : 0 ≤ ‖(u - 1 : A)‖ ^ 2 / 2)]
      _ = π := by norm_num
  map_target' x hx := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hx ⊢
    rw [← sq_lt_sq₀ (by positivity) (by positivity), norm_sq_expUnitary_sub_one hx.le]
    have : -1 < Real.cos ‖(x : A)‖ :=
      Real.cos_pi ▸ Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
    simp only [AddSubgroupClass.coe_norm, mul_sub, mul_one, sq, gt_iff_lt]
    linarith
  left_inv' u hu := expUnitary_argSelfAdjoint <| by
    simpa [Subtype.dist_eq, dist_eq_norm] using hu
  right_inv' x hx := argSelfAdjoint_expUnitary <| by simpa using hx
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop

@[deprecated (since := "2025-10-29")] alias unitary.openPartialHomeomorph :=
  Unitary.openPartialHomeomorph

lemma Unitary.norm_sub_eq (u v : unitary A) :
    ‖(u - v : A)‖ = ‖((u * star v : unitary A) - 1 : A)‖ := calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp

@[deprecated (since := "2025-10-29")] alias unitary.norm_sub_eq := Unitary.norm_sub_eq

lemma Unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) :
    expUnitary (argSelfAdjoint (u * star v)) = u * star v :=
  expUnitary_argSelfAdjoint <| norm_sub_eq u v ▸ huv

@[deprecated (since := "2025-10-29")] alias unitary.expUnitary_eq_mul_inv :=
  Unitary.expUnitary_eq_mul_inv

/-- For a selfadjoint element `x` in a C⋆-algebra, this is the path from `1` to `expUnitary x`
given by `t ↦ expUnitary (t • x)`. -/
@[simps]
noncomputable def selfAdjoint.expUnitaryPathToOne (x : selfAdjoint A) :
    Path 1 (expUnitary x) where
  toFun t := expUnitary ((t : ℝ) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
lemma selfAdjoint.joined_one_expUnitary (x : selfAdjoint A) :
    Joined (1 : unitary A) (expUnitary x) :=
  ⟨expUnitaryPathToOne x⟩

/-- The path `t ↦ expUnitary (t • argSelfAdjoint (v * star u)) * u`
from `u : unitary A` to `v` when `‖v - u‖ < 2`. -/
@[simps]
noncomputable def Unitary.path (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Path u v where
  toFun t := expUnitary ((t : ℝ) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

@[deprecated (since := "2025-10-29")] alias unitary.path := Unitary.path

/-- Two unitary elements `u` and `v` in a unital C⋆-algebra are joined by a path if the
distance between them is less than `2`. -/
lemma Unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Joined u v :=
  ⟨path u v huv⟩

@[deprecated (since := "2025-10-29")] alias unitary.joined := Unitary.joined

/-- Any ball of radius `δ < 2` in the unitary group of a unital C⋆-algebra is path connected. -/
lemma Unitary.isPathConnected_ball (u : unitary A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (u : unitary A) δ) := by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
    convert this |>.image (f := (u * ·)) (by fun_prop)
    ext v
    rw [← inv_mul_cancel u]
    simp [-inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu ↦ ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [Subtype.dist_eq, dist_eq_norm] using hu
  refine ⟨path 1 u (hu.trans hδ₂), fun t ↦ ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm] using
    norm_expUnitary_smul_argSelfAdjoint_sub_one_le u t.2 (hu.trans hδ₂) |>.trans_lt hu

@[deprecated (since := "2025-10-29")] alias unitary.isPathConnected_ball :=
  Unitary.isPathConnected_ball

/-- The unitary group in a C⋆-algebra is locally path connected. -/
instance Unitary.instLocPathConnectedSpace : LocPathConnectedSpace (unitary A) :=
  .of_bases (fun _ ↦ nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) <| by
    simpa using isPathConnected_ball

/-- The path component of the identity in the unitary group of a C⋆-algebra is the set of
unitaries that can be expressed as a product of exponential unitaries. -/
lemma Unitary.mem_pathComponentOne_iff {u : unitary A} :
    u ∈ pathComponent 1 ↔ ∃ l : List (selfAdjoint A), (l.map expUnitary).prod = u := by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, (hlv : (l.map expUnitary).prod = v)⟩, huv⟩⟩ := hu
    refine ⟨argSelfAdjoint (u * star v) :: l, ?_⟩
    simp [hlv, mul_assoc,
      expUnitary_eq_mul_inv u v (by simpa [Subtype.dist_eq, dist_eq_norm] using huv)]
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => simp
    | cons x xs ih => simpa using (joined_one_expUnitary x).mul ih

@[deprecated (since := "2025-10-29")] alias unitary.mem_pathComponentOne_iff :=
  Unitary.mem_pathComponentOne_iff
