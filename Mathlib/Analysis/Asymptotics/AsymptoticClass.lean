import Mathlib

open Filter Asymptotics NNReal

structure AsymptoticClass where
  (a b c : ℝ)

noncomputable
def AsymptoticClass.toFun (f : AsymptoticClass) (x : ℝ) : ℝ :=
  x ^ f.a * Real.exp (f.b * x) * Real.exp (f.c * x ^ 2)

noncomputable
instance : CoeFun AsymptoticClass (fun _ => ℝ → ℝ) where
  coe f x := f.toFun x

def AsymptoticClass.equiv (f g : AsymptoticClass) : Prop :=
  ∃ c > 0, IsBigOWith c .atTop f.toFun g.toFun

private theorem AsymptoticClass.eventually_norm_le_toFun
    (f : AsymptoticClass) {A B C : ℝ}
    (ha : f.a ≤ A) (hb : |f.b| ≤ B) (hc : |f.c| ≤ C) :
    ∀ᶠ x in atTop, ‖f x‖ ≤ (⟨A, B, C⟩ : AsymptoticClass) x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hbmul : f.b * x ≤ B * x := by
    gcongr
    exact (le_abs_self f.b).trans hb
  have hcmul : f.c * x ^ 2 ≤ C * x ^ 2 := by
    gcongr
    exact (le_abs_self f.c).trans hc
  simp only [AsymptoticClass.toFun]
  rw [Real.norm_of_nonneg (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hx0 _) (Real.exp_pos _).le) (Real.exp_pos _).le)]
  exact mul_le_mul
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx ha) (Real.exp_le_exp.mpr hbmul)
      (Real.exp_pos _).le (Real.rpow_nonneg hx0 _))
    (Real.exp_le_exp.mpr hcmul) (Real.exp_pos _).le
    (mul_nonneg (Real.rpow_nonneg hx0 _) (Real.exp_pos _).le)

def AsymptoticClass.add (f g : AsymptoticClass) : AsymptoticClass :=
  ⟨f.a + g.a, f.b + g.b, f.c + g.c⟩

def AsymptoticClass.scale (c : ℝ) (f : AsymptoticClass) : AsymptoticClass :=
  ⟨c * f.a, c * f.b, c * f.c⟩

theorem AsymptoticClass.add_isBigOWith (f g : AsymptoticClass) :
    (fun x => f x * g x) =O[.atTop] (fun x => f.add g x) := by
  refine EventuallyEq.isBigO ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [AsymptoticClass.toFun, AsymptoticClass.add]
  calc
    x ^ f.a * Real.exp (f.b * x) * Real.exp (f.c * x ^ 2) *
        (x ^ g.a * Real.exp (g.b * x) * Real.exp (g.c * x ^ 2))
        = (x ^ f.a * x ^ g.a) *
            (Real.exp (f.b * x) * Real.exp (g.b * x)) *
            (Real.exp (f.c * x ^ 2) * Real.exp (g.c * x ^ 2)) := by ring
    _ = x ^ (f.a + g.a) * Real.exp ((f.b + g.b) * x) *
          Real.exp ((f.c + g.c) * x ^ 2) := by
      rw [← Real.rpow_add hx, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring

protected noncomputable
def AsymptoticClass.neg (f : AsymptoticClass) : AsymptoticClass :=
  ⟨-f.a, -f.b, -f.c⟩

theorem AsymptoticClass.neg_isBigOWith (f : AsymptoticClass) :
    (fun x => 1 / f x) =O[.atTop] (fun x => f.neg x) := by
  refine EventuallyEq.isBigO ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : 0 ≤ x := hx.le
  have hxpow : x ^ f.a ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have he₁ : Real.exp (f.b * x) ≠ 0 := (Real.exp_pos _).ne'
  have he₂ : Real.exp (f.c * x ^ 2) ≠ 0 := (Real.exp_pos _).ne'
  have hbneg : Real.exp (-f.b * x) = (Real.exp (f.b * x))⁻¹ := by
    rw [show -f.b * x = -(f.b * x) by ring, Real.exp_neg]
  have hcneg : Real.exp (-f.c * x ^ 2) = (Real.exp (f.c * x ^ 2))⁻¹ := by
    rw [show -f.c * x ^ 2 = -(f.c * x ^ 2) by ring, Real.exp_neg]
  simp only [AsymptoticClass.toFun, AsymptoticClass.neg]
  rw [one_div, Real.rpow_neg hx0, hbneg, hcneg]
  field_simp [hxpow, he₁, he₂]

protected noncomputable
def AsymptoticClass.max (f g : AsymptoticClass) : AsymptoticClass :=
  ⟨max f.a g.a, max |f.b| |g.b| + 1, max |f.c| |g.c| + 1⟩

theorem AsymptoticClass.max_isBigOWith (f g : AsymptoticClass) :
    (fun x => f x + g x) =O[.atTop] (fun x => f.max g x) := by
  refine IsBigO.of_bound 2 ?_
  have hf : ∀ᶠ x in atTop, ‖f x‖ ≤ (f.max g) x := f.eventually_norm_le_toFun (le_max_left _ _)
    (by exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
    (by exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hg : ∀ᶠ x in atTop, ‖g x‖ ≤ (f.max g) x := g.eventually_norm_le_toFun (le_max_right _ _)
    (by exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
    (by exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hf, hg] with x hx hfx hgx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hnonneg : 0 ≤ (f.max g) x := by
    change 0 ≤ (f.max g).toFun x
    rw [AsymptoticClass.toFun]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0 _) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  calc
    ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ (f.max g) x + (f.max g) x := add_le_add hfx hgx
    _ = 2 * ‖(f.max g) x‖ := by rw [Real.norm_of_nonneg hnonneg]; ring


variable
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [ProperSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {A} [NormedRing A] [NormedAlgebra 𝕜 A]

open Real Filter Topology Asymptotics

structure IsOfAsymptoticClassAt (L : Filter X) (f : X → Y)
    (g : X → ℝ) (cls : AsymptoticClass) : Prop where
  asym : (‖f ·‖) =O[L] (cls.toFun ∘ g)
  /-- `g` is reaquired to diverge at `L` as AsymptoticClass represents singularity at infinity -/
  gdiverge : L.Tendsto g .atTop


namespace IsOfAsymptoticClassAt

omit [ProperSpace X] in
theorem tendsto_inv_norm_sub_at_point (x₀ : X) :
    Tendsto (fun x : X => ‖x - x₀‖⁻¹) (𝓝[≠] x₀) atTop := by
  exact tendsto_inv_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE x₀)

theorem id_at_inifinity : IsOfAsymptoticClassAt (.cocompact X) (fun x : X => x) (‖·‖) ⟨1,0,0⟩ := by
  constructor
  · refine IsBigO.of_bound' (Eventually.of_forall fun _ => ?_)
    simp [AsymptoticClass.toFun]
  · exact tendsto_norm_cocompact_atTop

theorem const_at_inifinity (y : Y) : IsOfAsymptoticClassAt (.cocompact X) (fun _ : X => y) (‖·‖) ⟨0,0,0⟩ := by
  constructor
  · refine IsBigO.of_bound (‖y‖) (Eventually.of_forall fun _ => ?_)
    simp [AsymptoticClass.toFun]
  · exact tendsto_norm_cocompact_atTop

theorem add_at_inifinity
    (f : X → Y) {f'} (hf : IsOfAsymptoticClassAt (.cocompact X) f (‖·‖) f')
    (g : X → Y) {g'} (hg : IsOfAsymptoticClassAt (.cocompact X) g (‖·‖) g') :
    IsOfAsymptoticClassAt (.cocompact X) (fun x => f x + g x) (‖·‖) (f'.max g') := by
  constructor
  · have hnorm : (fun x => ‖f x + g x‖) =O[.cocompact X]
        (fun x => ‖f x‖ + ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      have hle := norm_add_le (f x) (g x)
      simpa [Real.norm_of_nonneg (norm_nonneg (f x + g x)),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))] using hle
    have hclass : (fun x => ‖f x‖ + ‖g x‖) =O[.cocompact X]
        (fun x => f' ‖x‖ + g' ‖x‖) := by
      refine (hf.asym.add_add hg.asym).trans_eventuallyEq ?_
      exact Eventually.of_forall fun x => by
        simp [AsymptoticClass.toFun, Real.abs_rpow_of_nonneg (norm_nonneg x),
          abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos ‖x‖).le f'.b),
          abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos ‖x‖).le g'.b)]
    exact hnorm.trans <| hclass.trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.max_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_norm_cocompact_atTop

theorem mul_at_inifinity
    (f : X → A) {f'} (hf : IsOfAsymptoticClassAt (.cocompact X) f (‖·‖) f')
    (g : X → A) {g'} (hg : IsOfAsymptoticClassAt (.cocompact X) g (‖·‖) g') :
    IsOfAsymptoticClassAt (.cocompact X) (fun x => f x * g x) (‖·‖) (f'.add g') := by
  constructor
  · have hnorm : (fun x => ‖f x * g x‖) =O[.cocompact X]
        (fun x => ‖f x‖ * ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      have hle := norm_mul_le (f x) (g x)
      simpa [Real.norm_of_nonneg, mul_nonneg] using hle
    exact hnorm.trans <| (hf.asym.mul hg.asym).trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.add_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_norm_cocompact_atTop

omit [NormedSpace 𝕜 X] in
theorem smul_at_inifinity
    (f : X → 𝕜) {f'} (hf : IsOfAsymptoticClassAt (.cocompact X) f (‖·‖) f')
    (g : X → Y) {g'} (hg : IsOfAsymptoticClassAt (.cocompact X) g (‖·‖) g') :
    IsOfAsymptoticClassAt (.cocompact X) (fun x => f x • g x) (‖·‖) (f'.add g') := by
  constructor
  · have hnorm : (fun x => ‖f x • g x‖) =O[.cocompact X]
        (fun x => ‖f x‖ * ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hnorm.trans <| (hf.asym.mul hg.asym).trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.add_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_norm_cocompact_atTop


theorem exp_add
  (f : X → ℝ) {f'} (hf : IsOfAsymptoticClassAt L (fun x => exp (f x)) φ f')
  (g : X → ℝ) {g'} (hg : IsOfAsymptoticClassAt L (fun x => exp (g x)) φ g') :
  IsOfAsymptoticClassAt L (fun x => exp (f x + g x)) φ (f'.add g') := by
  constructor
  · have hnorm : (fun x => ‖exp (f x + g x)‖) =O[L]
        (fun x => ‖exp (f x)‖ * ‖exp (g x)‖) := by
      refine EventuallyEq.isBigO (Eventually.of_forall fun x => ?_)
      simp [Real.exp_add, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hnorm.trans <| (hf.asym.mul hg.asym).trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.add_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact hf.gdiverge

theorem exp_mul
    (f g : X → ℝ) {f' g' : AsymptoticClass}
    (hf : IsOfAsymptoticClassAt L f φ f') (hg : IsOfAsymptoticClassAt L g φ g')
    (hfa : f'.a ≤ 1) (hfb : f'.b = 0) (hfc : f'.c = 0)
    (hga : g'.a ≤ 1) (hgb : g'.b = 0) (hgc : g'.c = 0) :
    ∃ C ≥ 0, IsOfAsymptoticClassAt L (fun x => exp (f x * g x)) φ ⟨0,0,C⟩ := by
  have hfO : (fun x => ‖f x‖) =O[L] φ := by
    refine hf.asym.trans ?_
    refine IsBigO.of_bound' ?_
    filter_upwards [hf.gdiverge.eventually_ge_atTop 1] with x hx
    have hx0 : 0 ≤ φ x := zero_le_one.trans hx
    rw [Function.comp_apply, AsymptoticClass.toFun, hfb, hfc]
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.norm_of_nonneg hx0]
    exact Real.rpow_le_self_of_one_le hx hfa
  have hgO : (fun x => ‖g x‖) =O[L] φ := by
    refine hg.asym.trans ?_
    refine IsBigO.of_bound' ?_
    filter_upwards [hg.gdiverge.eventually_ge_atTop 1] with x hx
    have hx0 : 0 ≤ φ x := zero_le_one.trans hx
    rw [Function.comp_apply, AsymptoticClass.toFun, hgb, hgc]
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.norm_of_nonneg hx0]
    exact Real.rpow_le_self_of_one_le hx hga
  obtain ⟨Cf, hCf, hCfO⟩ := hfO.exists_nonneg
  obtain ⟨Cg, hCg, hCgO⟩ := hgO.exists_nonneg
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, ?_⟩
  constructor
  · refine IsBigO.of_bound' ?_
    filter_upwards [hCfO.bound, hCgO.bound, hf.gdiverge.eventually_ge_atTop 0] with x hfx hgx hφx
    have hfx' : |f x| ≤ Cf * |φ x| := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (f x))] using hfx
    have hgx' : |g x| ≤ Cg * |φ x| := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (g x))] using hgx
    have hprod : f x * g x ≤ (Cf * Cg) * φ x ^ 2 := by
      calc
        f x * g x ≤ |f x * g x| := le_abs_self _
        _ = |f x| * |g x| := abs_mul _ _
        _ ≤ (Cf * |φ x|) * (Cg * |φ x|) := by gcongr
        _ = (Cf * Cg) * φ x ^ 2 := by
          rw [abs_of_nonneg hφx]
          ring
    change ‖‖Real.exp (f x * g x)‖‖ ≤ ‖(⟨0, 0, Cf * Cg⟩ : AsymptoticClass).toFun (φ x)‖
    rw [AsymptoticClass.toFun]
    simp only [Function.comp_apply, Real.rpow_zero, one_mul, zero_mul, Real.exp_zero]
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hprod
  · exact hf.gdiverge



theorem exp_norm : IsOfAsymptoticClassAt (.cocompact X) (fun x : X => exp ‖x‖) (‖·‖) ⟨0,1,0⟩ := by
  constructor
  · refine EventuallyEq.isBigO ?_
    exact Eventually.of_forall fun x => by simp [AsymptoticClass.toFun]
  · exact tendsto_norm_cocompact_atTop

theorem exp_normSq : IsOfAsymptoticClassAt (.cocompact X) (fun x : X => exp (‖x‖ ^ 2)) (‖·‖) ⟨0,0,1⟩ := by
  constructor
  · refine EventuallyEq.isBigO ?_
    exact Eventually.of_forall fun x => by simp [AsymptoticClass.toFun]
  · exact tendsto_norm_cocompact_atTop

omit [ProperSpace X] in
theorem id_at_point (x₀ : X) :
    IsOfAsymptoticClassAt (𝓝[≠] x₀) (fun x : X => x) (fun x => ‖x - x₀‖⁻¹) ⟨0,0,0⟩ := by
  constructor
  · exact (((continuous_norm.tendsto x₀).mono_left inf_le_left).isBigO_one ℝ).trans_eventuallyEq
      (Eventually.of_forall fun x => by simp [AsymptoticClass.toFun])
  · exact tendsto_inv_norm_sub_at_point x₀

omit [ProperSpace X] in
theorem const_at_point (x₀ : X) (y : Y) :
    IsOfAsymptoticClassAt (𝓝[≠] x₀) (fun _ : X => y) (fun x => ‖x - x₀‖⁻¹) ⟨0,0,0⟩ := by
  constructor
  · refine IsBigO.of_bound (‖y‖) (Eventually.of_forall fun _ => ?_)
    simp [AsymptoticClass.toFun]
  · exact tendsto_inv_norm_sub_at_point x₀

omit [ProperSpace X] in
theorem add_at_point (x₀ : X)
    (f : X → Y) {f'} (hf : IsOfAsymptoticClassAt (𝓝[≠] x₀) f (fun x => ‖x - x₀‖⁻¹) f')
    (g : X → Y) {g'} (hg : IsOfAsymptoticClassAt (𝓝[≠] x₀) g (fun x => ‖x - x₀‖⁻¹) g') :
    IsOfAsymptoticClassAt (𝓝[≠] x₀) (fun x => f x + g x) (fun x => ‖x - x₀‖⁻¹) (f'.max g') := by
  constructor
  · have hnorm : (fun x => ‖f x + g x‖) =O[𝓝[≠] x₀]
        (fun x => ‖f x‖ + ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      have hle := norm_add_le (f x) (g x)
      simpa [Real.norm_of_nonneg (norm_nonneg (f x + g x)),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))] using hle
    have hclass : (fun x => ‖f x‖ + ‖g x‖) =O[𝓝[≠] x₀]
        (fun x => f' (‖x - x₀‖⁻¹) + g' (‖x - x₀‖⁻¹)) := by
      refine (hf.asym.add_add hg.asym).trans_eventuallyEq ?_
      exact Eventually.of_forall fun x => by
        simp [AsymptoticClass.toFun, Real.abs_rpow_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos (‖x - x₀‖⁻¹)).le f'.b),
          abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos (‖x - x₀‖⁻¹)).le g'.b)]
    exact hnorm.trans <| hclass.trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.max_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_inv_norm_sub_at_point x₀

omit [ProperSpace X] in
theorem mul_at_point (x₀ : X)
    (f : X → A) {f'} (hf : IsOfAsymptoticClassAt (𝓝[≠] x₀) f (fun x => ‖x - x₀‖⁻¹) f')
    (g : X → A) {g'} (hg : IsOfAsymptoticClassAt (𝓝[≠] x₀) g (fun x => ‖x - x₀‖⁻¹) g') :
    IsOfAsymptoticClassAt (𝓝[≠] x₀) (fun x => f x * g x) (fun x => ‖x - x₀‖⁻¹) (f'.add g') := by
  constructor
  · have hnorm : (fun x => ‖f x * g x‖) =O[𝓝[≠] x₀]
        (fun x => ‖f x‖ * ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      have hle := norm_mul_le (f x) (g x)
      simpa [Real.norm_of_nonneg, mul_nonneg] using hle
    exact hnorm.trans <| (hf.asym.mul hg.asym).trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.add_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_inv_norm_sub_at_point x₀

omit [NormedSpace 𝕜 X] [ProperSpace X] in
theorem smul_at_point (x₀ : X)
    (f : X → 𝕜) {f'} (hf : IsOfAsymptoticClassAt (𝓝[≠] x₀) f (fun x => ‖x - x₀‖⁻¹) f')
    (g : X → Y) {g'} (hg : IsOfAsymptoticClassAt (𝓝[≠] x₀) g (fun x => ‖x - x₀‖⁻¹) g') :
    IsOfAsymptoticClassAt (𝓝[≠] x₀) (fun x => f x • g x) (fun x => ‖x - x₀‖⁻¹) (f'.add g') := by
  constructor
  · have hnorm : (fun x => ‖f x • g x‖) =O[𝓝[≠] x₀]
        (fun x => ‖f x‖ * ‖g x‖) := by
      refine IsBigO.of_bound' (Eventually.of_forall fun x => ?_)
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hnorm.trans <| (hf.asym.mul hg.asym).trans <| by
      simpa [Function.comp_def] using
        ((AsymptoticClass.add_isBigOWith f' g').comp_tendsto hf.gdiverge)
  · exact tendsto_inv_norm_sub_at_point x₀


end IsOfAsymptoticClassAt
