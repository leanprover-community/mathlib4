/-
# Version-stable geometric lemmas for the Mercator connection

This file collects differential-geometry lemmas that do **not** depend on the
`extDerivFun` / `IsCovariantDerivativeOn` API (added to Mathlib later).  They are
about the tangent bundle of a general smooth manifold and are imported by
`MercatorV.lean`.

The central result is `mdifferentiableAt_mfderiv_apply`: pairing the differential
of a `C²` scalar function (a smooth section of the cotangent bundle) with a
differentiable vector field yields a differentiable scalar function.  This is the
key tool that lets differentiability of a *bundled* section be transferred to
differentiability of its components in the smooth coframe `{dθ, dφ}`.
-/

import Mathlib

open Bundle
open scoped Manifold Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

/-
Pairing the differential of a `C²` scalar function `f` (a smooth section of the
cotangent bundle) with a differentiable vector field `σ` yields a differentiable
scalar function `y ↦ (mfderiv I 𝓘(𝕜,𝕜) f y) (σ y)`.
-/
lemma mdifferentiableAt_mfderiv_apply
    (f : M → 𝕜) (σ : Π y : M, TangentSpace I y) (x : M)
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) 2 f x)
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, E))
      (fun y => TotalSpace.mk' E y (σ y)) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (fun y => (mfderiv I 𝓘(𝕜, 𝕜) f y) (σ y)) x := by
  have h_map : MDifferentiableAt I (𝓘(𝕜, 𝕜).prod 𝓘(𝕜, 𝕜)) (fun y => TotalSpace.mk' 𝕜 (f y) ((mfderiv I 𝓘(𝕜, 𝕜) f y) (σ y))) x := by
    have h_map : MDifferentiableAt I (𝓘(𝕜, E →L[𝕜] 𝕜)) (fun y => (inTangentCoordinates I 𝓘(𝕜, 𝕜) id f (fun y => mfderiv I 𝓘(𝕜, 𝕜) f y) x) y) x := by
      convert ( hf.mfderiv_const ( show 1 + 1 ≤ 2 by norm_num ) ) |> ContMDiffAt.mdifferentiableAt using 1;
      simp +decide;
    convert MDifferentiableAt.clm_apply_of_inCoordinates h_map hσ ( hf.mdifferentiableAt ( by norm_num ) ) using 1;
  rw [ mdifferentiableAt_totalSpace ] at h_map;
  convert h_map.2.congr_of_eventuallyEq _ using 1;
  simp +decide [ trivializationAt ]

end

/-
`Complex.arg` is `C^∞` on the slit plane.  Proved via the `arctan` formulas valid on the
three open pieces `{re > 0}`, `{im > 0}`, `{im < 0}` that cover the slit plane (avoiding
`Complex.log`, whose real smoothness runs into a scalar-tower instance issue).
-/
lemma arg_contDiffAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ (⊤ : ℕ∞) Complex.arg z := by
  revert z;
  -- Prove pointwise equality (valid on the stated open region):
  have h1 : ∀ z : ℂ, 0 < z.re → Complex.arg z = Real.arctan (z.im / z.re) := by
    intro z hz; rw [ Complex.arg, eq_comm ] ; rw [ Real.arctan_eq_arcsin ] ; ring_nf ; norm_num [ hz.ne', Complex.normSq, Complex.norm_def ] ;
    field_simp;
    rw [ if_pos hz.le, Real.sqrt_div ( by positivity ), Real.sqrt_sq hz.le, mul_div_cancel₀ _ hz.ne' ]
  have h2 : ∀ z : ℂ, 0 < z.im → Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
    intro z hz
    have h_arg : Complex.arg z ∈ Set.Ioo 0 Real.pi := by
      rw [ Complex.arg ];
      split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
      · exact ⟨ by nlinarith, lt_of_le_of_lt ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] ) ⟩;
      · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos hz ) ( Real.sqrt_pos.mpr ( by nlinarith ) ) ⟩;
      · linarith;
    have h_tan : Real.tan (Real.pi / 2 - Complex.arg z) = z.re / z.im := by
      rw [ Real.tan_pi_div_two_sub, Complex.tan_arg ];
      rw [ inv_div ];
    rw [ ← h_tan, Real.arctan_tan ] <;> linarith [ h_arg.1, h_arg.2 ]
  have h3 : ∀ z : ℂ, z.im < 0 → Complex.arg z = -Real.arctan (z.re / z.im) - Real.pi / 2 := by
    intro z hz
    have h_arg_neg : Complex.arg z = -Complex.arg (starRingEnd ℂ z) := by
      simp +decide [ Complex.arg_conj ];
      split_ifs <;> simp_all +decide [ Complex.arg_eq_pi_iff ];
    rw [ h_arg_neg, h2 ] <;> simp +decide [ hz ];
    rw [ ← Real.arctan_neg, div_neg ];
  intro z hz;
  by_cases hz_re : 0 < z.re;
  · refine' ContDiffAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) hz_re ) fun x hx => h1 x hx );
    exact ContDiffAt.arctan ( ContDiffAt.div ( Complex.imCLM.contDiff.contDiffAt ) ( Complex.reCLM.contDiff.contDiffAt ) hz_re.ne' );
  · cases lt_or_gt_of_ne ( show z.im ≠ 0 from by rintro h; simp_all +decide [ Complex.slitPlane ] ) <;> simp_all +decide [ Complex.slitPlane ];
    · refine' ContDiffAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_lt Complex.continuous_im continuous_const ) ‹_› ) fun x hx => h3 x hx );
      exact ContDiffAt.sub ( ContDiffAt.neg ( ContDiffAt.arctan ( ContDiffAt.div ( Complex.reCLM.contDiff.contDiffAt ) ( Complex.imCLM.contDiff.contDiffAt ) hz ) ) ) ( contDiffAt_const );
    · refine' ContDiffAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_im ) ‹_› ) fun w hw => h2 w hw );
      exact ContDiffAt.sub contDiffAt_const <| Real.contDiff_arctan.contDiffAt.comp _ <| ContDiffAt.div ( Complex.reCLM.contDiff.contDiffAt ) ( Complex.imCLM.contDiff.contDiffAt ) <| by positivity;

/-! ## Sphere infrastructure and the spherical chart

This section relocates the sphere / spherical-chart infrastructure (formerly in
`MercatorV.lean`) so that the version-stable geometric lemmas below, which refer to
it, live in a file free of the `extDerivFun` / `IsCovariantDerivativeOn` API. -/

set_option maxRecDepth 4000

open Real Set Metric
open Manifold
open scoped Manifold

noncomputable section Sphere

/-! ### The sphere and its open subset -/
abbrev S2 := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
def northPole : S2 := ⟨(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 0, 1], by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩
def southPole : S2 := ⟨(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 0, -1], by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩
-- S² minus the poles.
def S2_open : Set S2 := {p | p ≠ northPole ∧ p ≠ southPole}

/- Sum-of-squares identity for a point of the unit sphere. -/
lemma S2_coord_sq (p : S2) :
    (p.val 0) ^ 2 + (p.val 1) ^ 2 + (p.val 2) ^ 2 = 1 := by
  have h_norm : ‖p.val‖ ^ 2 = 1 := by
    simp +zetaDelta at *;
  rw [ ← h_norm, EuclideanSpace.norm_eq ] ; norm_num [ Fin.sum_univ_three ] ; ring_nf!;
  rw [ Real.sq_sqrt ( add_nonneg ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ( sq_nonneg _ ) ) ]

/-- The underlying vector of the inverse spherical map:
`(θ, φ) ↦ (sin θ cos φ, sin θ sin φ, cos θ)`. -/
def sphInvVec (q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![Real.sin (q 0) * Real.cos (q 1), Real.sin (q 0) * Real.sin (q 1), Real.cos (q 0)]

lemma sphInvVec_mem (q : EuclideanSpace ℝ (Fin 2)) : sphInvVec q ∈ S2 := by
  unfold S2; simp +decide only [sphInvVec,
   Fin.isValue, WithLp.equiv_symm_apply, mem_sphere_iff_norm, sub_zero] ; ring_nf;
  norm_num [ Norm.norm ];
  norm_num [ Fin.sum_univ_succ ] ; rw [ ← Real.sqrt_eq_rpow, Real.sqrt_eq_one ] ;
   nlinarith [ Real.sin_sq_add_cos_sq ( q.ofLp 0 ), Real.sin_sq_add_cos_sq ( q.ofLp 1 ) ] ;

/-- The inverse spherical map, as a map into the sphere. -/
def sphInv (q : EuclideanSpace ℝ (Fin 2)) : S2 := ⟨sphInvVec q, sphInvVec_mem q⟩

/-- The forward spherical map `p ↦ (arccos z, arg (x + y i))`. -/
def sphFwd (p : S2) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    ![Real.arccos (p.val 2), (Complex.equivRealProd.symm (p.val 0, p.val 1)).arg]

/-- The source: the sphere minus the closed meridian `{x ≤ 0, y = 0}`. -/
def sphSource : Set S2 := {p | 0 < p.val 0 ∨ p.val 1 ≠ 0}

/-- The target: `θ ∈ (0, π)`, `φ ∈ (-π, π)`. -/
def sphTarget : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | q 0 ∈ Ioo (0 : ℝ) π ∧ q 1 ∈ Ioo (-π) π}

lemma sph_map_source : ∀ ⦃p : S2⦄, p ∈ sphSource → sphFwd p ∈ sphTarget := by
  intro p hp
  constructor <;> norm_num [sphFwd, sphTarget]
  · have hz_sq : (p.val 2) ^ 2 < 1 := by
      have hz : p.val 0 ^ 2 + p.val 1 ^ 2 > 0 := by
        cases hp <;> simp_all only [Fin.isValue, gt_iff_lt] <;> positivity
      linarith [S2_coord_sq p]
    exact ⟨by nlinarith, lt_of_le_of_ne (Real.arccos_le_pi _)
      (by rw [Ne.eq_def, Real.arccos_eq_pi]; nlinarith)⟩
  · exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_lt_pi_iff.mpr (by
      cases hp with
      | inl h =>
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
          exact Or.inl (le_of_lt h)
      | inr h =>
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
            mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, zero_add, add_zero]
          exact Or.inr h)⟩

lemma sph_map_target : ∀ ⦃q : EuclideanSpace ℝ (Fin 2)⦄, q ∈ sphTarget → sphInv q ∈ sphSource := by
  intro q hq
  simp only [sphSource, sphInv, sphInvVec, mem_setOf_eq] at *
  by_cases hsin : Real.sin (q.ofLp 1) = 0
  · left
    have hphi : q.ofLp 1 = 0 := by
      rwa [Real.sin_eq_zero_iff_of_lt_of_lt hq.2.1 hq.2.2] at hsin
    simp only [hphi, Real.cos_zero, mul_one]
    exact Real.sin_pos_of_pos_of_lt_pi hq.1.1 hq.1.2
  · right
    exact mul_ne_zero
      (Real.sin_pos_of_pos_of_lt_pi hq.1.1 hq.1.2).ne'
      hsin

lemma sph_left_inv : ∀ p ∈ sphSource, sphInv (sphFwd p) = p := by
  intro p hp
  ext i
  simp only [sphInv, sphInvVec, sphFwd]
  fin_cases i <;>
    simp +decide only [Fin.isValue, Complex.equivRealProd_symm_apply, WithLp.equiv_symm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Real.sin_arccos, Complex.sin_arg]
  · rw [Complex.cos_arg] <;> norm_num [Complex.ext_iff]
    · rw [mul_div, div_eq_iff] <;> norm_num [Complex.normSq, Complex.norm_def]
      · rw [show (1 - (p.val 2) ^ 2 : ℝ) = (p.val 0) ^ 2 + (p.val 1) ^ 2
            by linarith [S2_coord_sq p]]
        ring_nf!
      · exact ne_of_gt <| Real.sqrt_pos.mpr <| by
          rcases hp with (hp | hp)
          · exact add_pos_of_pos_of_nonneg
              (mul_self_pos.mpr <| by simpa using hp.ne') (mul_self_nonneg _)
          · exact add_pos_of_nonneg_of_pos
              (mul_self_nonneg _) (mul_self_pos.mpr <| by simpa using hp)
    · cases hp <;> aesop
  · rw [mul_div, div_eq_iff] <;> norm_num [Complex.normSq, Complex.norm_def]
    · rw [show (1 - (p.val 2) ^ 2 : ℝ) = (p.val 0) ^ 2 + (p.val 1) ^ 2
          by linarith [S2_coord_sq p]]
      ring_nf!
    · simp_all +decide only [sphSource, Fin.isValue, ne_eq, mem_setOf_eq, ← sq, sqrt_eq_zero',
        not_le]
      cases hp <;> positivity
  · rw [Real.cos_arccos] <;>
      nlinarith [S2_coord_sq p,
        show (p.val 2) ^ 2 ≤ 1 by nlinarith [S2_coord_sq p]]

lemma sph_right_inv : ∀ q ∈ sphTarget, sphFwd (sphInv q) = q := by
  intro q hq
  simp only [sphFwd, sphInv, sphInvVec, Fin.isValue, WithLp.equiv_symm_apply, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.equivRealProd_symm_apply, Complex.ofReal_mul,
    Complex.ofReal_sin, Complex.ofReal_cos] at *
  ext i
  fin_cases i
  · simp_all +decide only [sphTarget, Fin.isValue, mem_Ioo, mem_setOf_eq, Fin.zero_eta,
      Matrix.cons_val_zero]
    rw [Real.arccos_cos] <;> linarith
  · simp_all +decide only [sphTarget, Fin.isValue, mem_Ioo, mem_setOf_eq, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    convert Complex.arg_mul_cos_add_sin_mul_I _ _ using 2
    rotate_left
    exacts [Real.sin (q.ofLp 0), Real.sin_pos_of_pos_of_lt_pi hq.1.1 hq.1.2,
      ⟨hq.2.1, hq.2.2.le⟩, by push_cast; ring]

lemma sph_open_source : IsOpen sphSource := by
  have h_open : IsOpen {v : EuclideanSpace ℝ (Fin 3) | 0 < v 0 ∨ v 1 ≠ 0} := by
    refine IsOpen.union ?_ ?_
    · exact isOpen_lt continuous_const
        (continuous_apply _ |> Continuous.comp <| continuous_induced_dom)
    · exact isOpen_ne.preimage (by fun_prop)
  convert h_open.preimage continuous_subtype_val using 1

lemma sph_open_target : IsOpen sphTarget := by
  refine isOpen_Ioo.preimage ?_ |> IsOpen.inter <| isOpen_Ioo.preimage ?_
  · fun_prop (disch := norm_num)
  · fun_prop

lemma sph_cont_to : ContinuousOn sphFwd sphSource := by
  intro p hp
  refine ContinuousWithinAt.comp
    (g := (WithLp.equiv 2 (Fin 2 → ℝ)).symm) (t := Set.univ) ?_ ?_ (Set.mapsTo_univ _ _)
  · exact Continuous.continuousWithinAt (by continuity)
  · refine tendsto_pi_nhds.mpr ?_
    intro i
    fin_cases i <;>
      simp +decide only [Fin.isValue, Complex.equivRealProd_symm_apply,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
    · refine Continuous.continuousWithinAt ?_
      fun_prop
    · refine Complex.continuousAt_arg ?_ |> fun h => h.comp_continuousWithinAt ?_
      · cases hp <;>
          simp_all +decide only [Fin.isValue, Complex.slitPlane, ne_eq, mem_setOf_eq,
            Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
            Complex.mul_im, zero_add, true_or, not_false_eq_true, or_true]
      · fun_prop

lemma sph_cont_inv : ContinuousOn sphInv sphTarget := by
  refine Continuous.continuousOn ?_
  have h_equiv_cont : Continuous (WithLp.equiv 2 (Fin 3 → ℝ)).symm :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  refine Continuous.subtype_mk ?_ _
  convert h_equiv_cont.comp
    (show Continuous fun q : EuclideanSpace ℝ (Fin 2) => fun i : Fin 3 =>
        if i = 0 then Real.sin (q 0) * Real.cos (q 1)
        else if i = 1 then Real.sin (q 0) * Real.sin (q 1) else Real.cos (q 0) from ?_) using 1
  · exact funext fun x => by ext i; fin_cases i <;> rfl
  · refine continuous_pi_iff.mpr ?_
    intro i
    split_ifs <;> fun_prop

noncomputable def sphericalChart :
    OpenPartialHomeomorph S2 (EuclideanSpace ℝ (Fin 2)) where
  toFun := sphFwd
  invFun := sphInv
  source := sphSource
  target := sphTarget
  map_source' := sph_map_source
  map_target' := sph_map_target
  left_inv' := sph_left_inv
  right_inv' := sph_right_inv
  open_source := sph_open_source
  open_target := sph_open_target
  continuousOn_toFun := sph_cont_to
  continuousOn_invFun := sph_cont_inv

lemma sphericalChart_source : sphericalChart.source = sphSource := rfl

/-- The chart domain avoids both poles: `sphSource ⊆ S2_open`. -/
lemma sphSource_subset_S2_open : sphSource ⊆ S2_open := by
  intro p hp
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hp <;>
    norm_num [sphSource, northPole, southPole] at hp

/-- The θ coordinate of a point. -/
noncomputable def θ_coord (x : S2) : ℝ := (sphericalChart x) 0

/-- The φ coordinate of a point. -/
noncomputable def φ_coord (x : S2) : ℝ := (sphericalChart x) 1

lemma θ_coord_eq (x : S2) : θ_coord x = Real.arccos (x.val 2) := rfl

/-- Away from the poles, `z² < 1`. -/
lemma z_sq_lt_one {x : S2} (hx : x ∈ S2_open) : (x.val 2) ^ 2 < 1 := by
  rcases lt_or_eq_of_le (show (x.val 2) ^ 2 ≤ 1 by
      nlinarith [S2_coord_sq x, sq_nonneg (x.val 0), sq_nonneg (x.val 1)]) with h | h
  · exact h
  · exfalso
    have h0 : x.val 0 = 0 := sq_eq_zero_iff.mp (by
      linarith [S2_coord_sq x, sq_nonneg (x.val 0), sq_nonneg (x.val 1)])
    have h1 : x.val 1 = 0 := sq_eq_zero_iff.mp (by
      linarith [S2_coord_sq x, sq_nonneg (x.val 0), sq_nonneg (x.val 1)])
    have h2 : (x.val 2 - 1) * (x.val 2 + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h2 | h2
    · refine hx.1 (Subtype.ext ?_)
      ext i
      fin_cases i <;> simp [northPole, h0, h1, sub_eq_zero.mp h2]
    · refine hx.2 (Subtype.ext ?_)
      ext i
      fin_cases i <;> simp [southPole, h0, h1, eq_neg_of_add_eq_zero_left h2]

/-- Away from the poles, `sin θ ≠ 0`. -/
theorem sinθ_ne_zero (x : S2) (hx : x ∈ S2_open) : Real.sin (θ_coord x) ≠ 0 := by
  have hz := z_sq_lt_one hx
  rw [θ_coord_eq]
  refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
  · exact Real.arccos_pos.mpr (by nlinarith [sq_nonneg (x.val 2 - 1)])
  · refine lt_of_le_of_ne (Real.arccos_le_pi _) fun h => ?_
    rw [Real.arccos_eq_pi] at h
    nlinarith [sq_nonneg (x.val 2 + 1)]

/-! ### Smoothness of the coordinate functions -/

/-
The `θ` coordinate `arccos ∘ z` is `C^∞` at points off the poles.
-/
lemma θ_coord_contMDiffAt {x : S2} (hx : x ∈ S2_open) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ⊤ θ_coord x := by
  convert ContMDiffAt.comp x ( Real.contDiffAt_arccos ?_ ?_ |> ContDiffAt.contMDiffAt ) ?_;
  · have := z_sq_lt_one hx; nlinarith!;
  · intro h; have := z_sq_lt_one hx; simp_all +decide ;
  · -- The projection function `v ↦ v 2` is `C^∞` since it is linear.
    have h_proj : ContDiff ℝ ⊤ (fun (v : EuclideanSpace ℝ (Fin 3)) => v 2) := by
      fun_prop;
    convert h_proj.contMDiff.contMDiffAt.comp x ( contMDiff_coe_sphere ?_ ) using 1

/-
The `φ` coordinate `arg (x + i y)` is `C^∞` at points of `sphSource`.
-/
lemma φ_coord_contMDiffAt {x : S2} (hx : x ∈ sphSource) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ_coord x := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  have hcoe : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun p : S2 => (p : EuclideanSpace ℝ (Fin 3))) x := (contMDiff_coe_sphere).contMDiffAt
  have h0 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : S2 => (p.val 0 : ℝ)) x :=
    ((ContinuousLinearMap.contMDiff (EuclideanSpace.proj (0 : Fin 3))).contMDiffAt).comp x hcoe
  have h1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : S2 => (p.val 1 : ℝ)) x :=
    ((ContinuousLinearMap.contMDiff (EuclideanSpace.proj (1 : Fin 3))).contMDiffAt).comp x hcoe
  have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (fun p : S2 => (p.val 0 : ℂ)) x :=
    (Complex.ofRealCLM.contMDiff.contMDiffAt).comp x h0
  have hB : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (fun p : S2 => (p.val 1 : ℝ) • Complex.I) x :=
    ((((ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I)).contMDiff.contMDiffAt).comp x h1
  have h_smooth : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞
      (fun p : S2 => (p.val 0 : ℂ) + (p.val 1 : ℂ) * Complex.I) x := by
    refine (hA.add hB).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun p => ?_))
    simp [Complex.real_smul]
  have hmem : ((x.val 0 : ℂ) + (x.val 1 : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    simpa using hx
  have h_arg : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p : S2 => Complex.arg ((p.val 0 : ℂ) + (p.val 1 : ℂ) * Complex.I)) x :=
    (arg_contDiffAt hmem).contMDiffAt.comp x h_smooth
  have hfun : φ_coord = fun p : S2 => Complex.arg ((p.val 0 : ℂ) + (p.val 1 : ℂ) * Complex.I) := by
    funext p
    simp [φ_coord, sphericalChart, sphFwd, Complex.equivRealProd_symm_apply]
  rw [hfun]; exact h_arg

/-
The inverse spherical map is `C^∞` as a map into the sphere.
-/
lemma sphInv_contMDiff : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) ⊤ sphInv := by
  convert ContMDiff.codRestrict_sphere _ _;
  · infer_instance;
  · rw [ contMDiff_iff_contDiff ];
    refine' ContDiff.comp ( _ : ContDiff ℝ ω _ ) _;
    · fun_prop;
    · refine' contDiff_pi.2 _;
      intro i; fin_cases i <;> norm_num [ Real.contDiff_sin, Real.contDiff_cos ] ;
      · fun_prop;
      · fun_prop;
      · fun_prop

/-
The forward spherical map is differentiable at points of `sphSource`.
-/
lemma sphFwd_mdiffAt {x : S2} (hx : x ∈ sphSource) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd x := by
  refine' MDifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun p => ( WithLp.equiv 2 ( Fin 2 → ℝ ) ).symm ![ θ_coord p, φ_coord p ];
  · have h_diff : MDifferentiableAt (𝓡 2) (𝓘(ℝ, Fin 2 → ℝ)) (fun p => ![θ_coord p, φ_coord p]) x := by
      have h_diff : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ)) θ_coord x ∧ MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ)) φ_coord x := by
        exact ⟨ θ_coord_contMDiffAt ( sphSource_subset_S2_open hx ) |> ContMDiffAt.mdifferentiableAt <| by norm_num, φ_coord_contMDiffAt hx |> ContMDiffAt.mdifferentiableAt <| by norm_num ⟩;
      rw [ mdifferentiableAt_iff ] at *;
      constructor;
      · exact tendsto_pi_nhds.mpr fun i => by fin_cases i <;> [ exact h_diff.1.1; exact h_diff.2.continuousAt ] ;
      · rw [ mdifferentiableAt_iff ] at h_diff;
        refine' DifferentiableWithinAt.congr _ _ _;
        use fun p => ![writtenInExtChartAt (𝓡 2) 𝓘(ℝ, ℝ) x θ_coord p, writtenInExtChartAt (𝓡 2) 𝓘(ℝ, ℝ) x φ_coord p];
        · exact differentiableWithinAt_pi.mpr fun i => by fin_cases i <;> [ exact h_diff.1.2; exact h_diff.2.2 ] ;
        · simp +decide [ writtenInExtChartAt ];
        · simp +decide [ writtenInExtChartAt ];
    have h_diff : MDifferentiableAt (𝓘(ℝ, Fin 2 → ℝ)) (𝓡 2) (fun p : Fin 2 → ℝ => (WithLp.equiv 2 (Fin 2 → ℝ)).symm p) ![θ_coord x, φ_coord x] := by
      have h_diff : ContDiffAt ℝ ⊤ (fun p : Fin 2 → ℝ => (WithLp.equiv 2 (Fin 2 → ℝ)).symm p) ![θ_coord x, φ_coord x] := by
        fun_prop;
      exact h_diff.contMDiffAt.mdifferentiableAt ( by norm_num );
    exact h_diff.comp x ‹_›;
  · exact Filter.Eventually.of_forall fun p => rfl

/-! ### The smooth coordinate coframe `{dθ, dφ}` and its dual frame `{Xθ, Xφ}`

The coframe is the genuine differential of the spherical coordinate functions (a smooth
section of the cotangent bundle), and the frame is the push-forward of the standard basis
under the chart inverse.  Both are honest tangent-bundle objects, unlike a constant model
frame. -/

/-- The coordinate coframe `dθ = d(θ_coord)`. -/
noncomputable def dθ (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ) θ_coord x
/-- The coordinate coframe `dφ = d(φ_coord)`. -/
noncomputable def dφ (x : S2) : TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ_coord x

/-- The coordinate vector field `∂θ`, the push-forward of the first standard basis vector
under `sphInv`. -/
noncomputable def Xθ (x : S2) : TangentSpace (𝓡 2) x :=
  mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x)
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
/-- The coordinate vector field `∂φ`, the push-forward of the second standard basis vector
under `sphInv`. -/
noncomputable def Xφ (x : S2) : TangentSpace (𝓡 2) x :=
  mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x)
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-
`{∂θ, ∂φ}` is the frame dual to the coframe `{dθ, dφ}` on `sphSource`: every tangent
vector `v` is recovered as `dθ(v) • ∂θ + dφ(v) • ∂φ`.  This follows from the chain rule
applied to `sphInv ∘ sphFwd = id` near `x`.
-/
lemma frame_dual {x : S2} (hx : x ∈ sphSource) (v : TangentSpace (𝓡 2) x) :
    dθ x v • Xθ x + dφ x v • Xφ x = v := by
  -- Let `Dfwd := mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd x` and `Dinv := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x)`, both continuous linear maps `EuclideanSpace ℝ (Fin 2) →L EuclideanSpace ℝ (Fin 2)` (`TangentSpace (𝓡 2) y` is defeq `EuclideanSpace ℝ (Fin 2)` for all `y`).
  set Dfwd : TangentSpace (𝓡 2) x →L[ℝ] EuclideanSpace ℝ (Fin 2) := mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd x
  set Dinv : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace (𝓡 2) x := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) sphInv (sphFwd x);
  -- By definition of `dθ` and `dφ`, we have `dθ x v = (EuclideanSpace.proj 0) (Dfwd v)` and `dφ x v = (EuclideanSpace.proj 1) (Dfwd v)`.
  have h_dθ_dφ : dθ x v = (Dfwd v) 0 ∧ dφ x v = (Dfwd v) 1 := by
    have h_deriv_fst : dθ x = (EuclideanSpace.proj 0).comp Dfwd := by
      apply HasMFDerivAt.mfderiv;
      have h_dθ : HasMFDerivAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) sphFwd x Dfwd := by
        grind +suggestions;
      convert HasMFDerivAt.comp x ( show HasMFDerivAt ( 𝓡 2 ) 𝓘(ℝ, ℝ) ( fun p : EuclideanSpace ℝ ( Fin 2 ) => p 0 ) ( sphFwd x ) ( EuclideanSpace.proj 0 ) from ?_ ) h_dθ using 1;
      constructor;
      · exact Continuous.continuousAt ( by exact continuous_apply _ |> Continuous.comp <| by exact continuous_induced_dom );
      · simp +decide [ hasFDerivWithinAt_iff_tendsto ]
    have h_deriv_snd : dφ x = (EuclideanSpace.proj 1).comp Dfwd := by
      apply_rules [ HasMFDerivAt.mfderiv ];
      apply HasMFDerivAt.comp x (ContinuousLinearMap.hasMFDerivAt (EuclideanSpace.proj 1)) (sphFwd_mdiffAt hx).hasMFDerivAt;
    aesop;
  -- By definition of `Xθ` and `Xφ`, we have `Xθ x = Dinv (EuclideanSpace.single 0 1)` and `Xφ x = Dinv (EuclideanSpace.single 1 1)`.
  have h_Xθ_Xφ : Xθ x = Dinv (EuclideanSpace.single 0 1) ∧ Xφ x = Dinv (EuclideanSpace.single 1 1) := by
    exact ⟨ rfl, rfl ⟩;
  -- By definition of `Dinv`, we have `Dinv (Dfwd v) = v`.
  have h_Dinv_Dfwd : Dinv (Dfwd v) = v := by
    have hid : mfderiv (𝓡 2) (𝓡 2) (sphInv ∘ sphFwd) x = ContinuousLinearMap.id (ℝ) (TangentSpace (𝓡 2) x) := by
      have h_inv : ∀ᶠ y in nhds x, sphInv (sphFwd y) = y :=
        Filter.eventually_of_mem ( IsOpen.mem_nhds sph_open_source hx ) fun y hy => sph_left_inv y hy
      exact HasMFDerivAt.mfderiv ( HasMFDerivAt.congr_of_eventuallyEq ( hasMFDerivAt_id _ ) h_inv )
    have hcomp : mfderiv (𝓡 2) (𝓡 2) (sphInv ∘ sphFwd) x = Dinv.comp Dfwd :=
      mfderiv_comp x ( sphInv_contMDiff.contMDiffAt.mdifferentiableAt ( by norm_num ) ) ( sphFwd_mdiffAt hx )
    have hcomp' : Dinv.comp Dfwd = ContinuousLinearMap.id (ℝ) (TangentSpace (𝓡 2) x) := by
      rw [← hcomp]; exact hid
    calc Dinv (Dfwd v) = (Dinv.comp Dfwd) v := rfl
      _ = v := by rw [hcomp']; rfl
  rw [ h_dθ_dφ.1, h_dθ_dφ.2, h_Xθ_Xφ.1, h_Xθ_Xφ.2 ];
  convert h_Dinv_Dfwd using 1;
  rw [ ← Dinv.map_smul, ← Dinv.map_smul ];
  rw [ ← Dinv.map_add ] ; congr ; ext i ; fin_cases i <;> simp +decide

end Sphere