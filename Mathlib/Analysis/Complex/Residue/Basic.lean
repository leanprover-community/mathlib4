/-
Copyright (c) 2025 Roman Kvasnytskyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Kvasnytskyi
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Residues at isolated singularities

We define the residue of a complex function at an isolated singularity and prove basic
properties. The residue is the coefficient of `(z - c)⁻¹` in the Laurent expansion around `c`,
which can be computed as `(2πi)⁻¹` times a circle integral.

## Main definitions

* `HasIsolatedSingularityAt f c`: `f` has an isolated singularity at `c`
* `HasRemovableSingularityAt f c`: `f` has a removable singularity at `c`
* `residue f c hf`: the residue of `f` at `c`

## Main results

* `residue_eq_two_pi_I_inv_smul_circleIntegral`: radius independence for residues
* `residue_of_holomorphic`: holomorphic functions have zero residue
* `residue_simple_pole`: residue formula for simple poles
-/

noncomputable section

open scoped Real Topology

open Set Metric Complex Filter

namespace Complex

/-- `f` has an isolated singularity at `c` if `f` is holomorphic in a punctured
neighborhood of `c`. -/
def HasIsolatedSingularityAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ R > 0, DifferentiableOn ℂ f (ball c R \ {c})

/-- `f` has a removable singularity at `c` if it has an isolated singularity there and
extends to a holomorphic function in a full neighborhood of `c`. -/
def HasRemovableSingularityAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  HasIsolatedSingularityAt f c ∧ ∃ (g : ℂ → ℂ) (R : ℝ) (_ : 0 < R),
    DifferentiableOn ℂ g (ball c R) ∧ EqOn f g (ball c R \ {c})

namespace HasIsolatedSingularityAt

variable {f g : ℂ → ℂ} {c : ℂ}

/-- Scalar multiples of functions with isolated singularities also have isolated singularities. -/
@[simp]
lemma smul (a : ℂ) (hf : HasIsolatedSingularityAt f c) :
    HasIsolatedSingularityAt (fun z => a * f z) c := by
  rcases hf with ⟨R, hR, hd⟩
  refine ⟨R, hR, ?_⟩
  simpa [Pi.smul_apply, smul_eq_mul] using hd.const_smul a

/-- Sums of functions with isolated singularities also have isolated singularities. -/
@[simp]
lemma add (hf : HasIsolatedSingularityAt f c) (hg : HasIsolatedSingularityAt g c) :
    HasIsolatedSingularityAt (fun z => f z + g z) c := by
  rcases hf with ⟨Rf, hRf, hdf⟩
  rcases hg with ⟨Rg, hRg, hdg⟩
  refine ⟨min Rf Rg, lt_min hRf hRg, ?_⟩
  have hsub : ball c (min Rf Rg) \ {c} ⊆ (ball c Rf \ {c}) ∩ (ball c Rg \ {c}) := by
    intro z hz
    rcases hz with ⟨hz, hzne⟩
    exact ⟨⟨(mem_ball.mpr <| lt_of_lt_of_le (mem_ball.mp hz) (min_le_left _ _)), hzne⟩,
      ⟨(mem_ball.mpr <| lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)), hzne⟩⟩
  have hdf' : DifferentiableOn ℂ f (ball c (min Rf Rg) \ {c}) :=
    hdf.mono (by intro z hz; exact (hsub hz).1)
  have hdg' : DifferentiableOn ℂ g (ball c (min Rf Rg) \ {c}) :=
    hdg.mono (by intro z hz; exact (hsub hz).2)
  simpa using hdf'.add hdg'

end HasIsolatedSingularityAt


/-- The residue of `f` at `c`. This is `(2πi)⁻¹` times the circle integral of `f` around `c`. -/
def residue (f : ℂ → ℂ) (c : ℂ) (hf : HasIsolatedSingularityAt f c) : ℂ := by
  classical
  -- Use Classical.choose to extract the witness radius from the existential
  let R : ℝ := Classical.choose hf
  exact (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R / 2), f z

/-- Radius-independence in the downward direction for the chosen witness radius: if 0 < r ≤ R/2
for the chosen witness R of the isolated singularity, then the residue equals the normalized
circle integral on the circle of radius r. -/
lemma residue_eq_two_pi_I_inv_smul_circleIntegral_of_le
    {f : ℂ → ℂ} {c : ℂ} (hf : HasIsolatedSingularityAt f c)
    {r : ℝ} (hr0 : 0 < r) (hrle : r ≤ (Classical.choose hf) / 2) :
    residue f c hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z := by
  classical
  -- Let R be the chosen witness radius for hf
  let R : ℝ := Classical.choose hf
  have hRpos : 0 < R := (Classical.choose_spec hf).1
  have hdiffR : DifferentiableOn ℂ f (ball c R \ {c}) := (Classical.choose_spec hf).2
  -- Annulus invariance from R/2 down to r
  have hsubset₁ : closedBall c (R / 2) \ ball c r ⊆ ball c R \ ({c} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    have hz_ballR : z ∈ ball c R := by
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz₁) (half_lt_self hRpos))
    have hz_ne : z ≠ c := by
      intro h
      have hc : c ∈ ball c r := mem_ball_self hr0
      have hzmem : z ∈ ball c r := by simpa [h] using hc
      exact hz₂ hzmem
    exact ⟨hz_ballR, by simp [Set.mem_singleton_iff, hz_ne]⟩
  have hcont : ContinuousOn f (closedBall c (R / 2) \ ball c r) :=
    (hdiffR.continuousOn).mono hsubset₁
  have hsubset₂ : ball c (R / 2) \ closedBall c r ⊆ ball c R \ ({c} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    have hz_ballR : z ∈ ball c R := by
      exact mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz₁) (le_of_lt (half_lt_self hRpos)))
    have hz_ne : z ≠ c := by
      intro h
      have hc : c ∈ closedBall c r := mem_closedBall_self hr0.le
      have hzmem : z ∈ closedBall c r := by simpa [h] using hc
      exact hz₂ hzmem
    exact ⟨hz_ballR, by simp [Set.mem_singleton_iff, hz_ne]⟩
  have hdiff : ∀ z ∈ ball c (R / 2) \ closedBall c r, DifferentiableAt ℂ f z := by
    intro z hz
    have hz' : z ∈ ball c R \ {c} := hsubset₂ hz
    have hop : IsOpen (ball c R \ ({c} : Set ℂ)) := by
      have hb : IsOpen (ball c R) := isOpen_ball
      exact hb.sdiff isClosed_singleton
    exact hdiffR.differentiableAt (hop.mem_nhds hz')
  have eqInt : (∮ z in C(c, R / 2), f z) = ∮ z in C(c, r), f z := by
    simpa using (circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := c)
      (r := r) (R := R / 2) (h0 := hr0) (hle := hrle)
      (hs := countable_empty) (hc := hcont) (hd := by
        intro z hz; exact hdiff z hz.1))
  have eqInt' : (∮ z in C(c, (Classical.choose hf) / 2), f z) = ∮ z in C(c, r), f z := by
    simpa [R] using eqInt
  -- Unfold residue and rewrite
  have : residue f c hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, (Classical.choose hf) / 2), f z := by
    simp [residue]
  simp [residue, eqInt'] at this ⊢

/-- Radius-independence in the upward direction for the chosen witness radius: if R/2 ≤ r < R
for the chosen witness R of the isolated singularity, then the residue equals the normalized
circle integral on the circle of radius r. -/
lemma residue_eq_two_pi_I_inv_smul_circleIntegral_of_ge
    {f : ℂ → ℂ} {c : ℂ} (hf : HasIsolatedSingularityAt f c)
    {r : ℝ} (hr_lt : r < Classical.choose hf) (hr_ge : (Classical.choose hf) / 2 ≤ r) :
    residue f c hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z := by
  classical
  -- Let R be the chosen witness radius for hf
  let R : ℝ := Classical.choose hf
  have hRpos : 0 < R := (Classical.choose_spec hf).1
  have hr0 : 0 < r := lt_of_lt_of_le (half_pos hRpos) hr_ge
  have hdiffR : DifferentiableOn ℂ f (ball c R \ {c}) := (Classical.choose_spec hf).2
  -- Annulus invariance from r down to R/2
  have hsubset₁ : closedBall c r \ ball c (R / 2) ⊆ ball c R \ ({c} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    have hz_ballR : z ∈ ball c R := by
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz₁) hr_lt)
    have hz_ne : z ≠ c := by
      intro h
      have hc : c ∈ ball c (R / 2) := mem_ball_self (half_pos hRpos)
      have hzmem : z ∈ ball c (R / 2) := by simpa [h] using hc
      exact hz₂ hzmem
    exact ⟨hz_ballR, by simp [Set.mem_singleton_iff, hz_ne]⟩
  have hcont : ContinuousOn f (closedBall c r \ ball c (R / 2)) :=
    (hdiffR.continuousOn).mono hsubset₁
  have hsubset₂ : ball c r \ closedBall c (R / 2) ⊆ ball c R \ ({c} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    have hz_ballR : z ∈ ball c R := by
      exact mem_ball.mpr (lt_trans (mem_ball.mp hz₁) hr_lt)
    have hz_ne : z ≠ c := by
      intro h
      have hc : c ∈ closedBall c (R / 2) := mem_closedBall_self (le_of_lt (half_pos hRpos))
      have hzmem : z ∈ closedBall c (R / 2) := by simpa [h] using hc
      exact hz₂ hzmem
    exact ⟨hz_ballR, by simp [Set.mem_singleton_iff, hz_ne]⟩
  have hdiff : ∀ z ∈ ball c r \ closedBall c (R / 2), DifferentiableAt ℂ f z := by
    intro z hz
    have hz' : z ∈ ball c R \ {c} := hsubset₂ hz
    have hop : IsOpen (ball c R \ ({c} : Set ℂ)) := by
      have hb : IsOpen (ball c R) := isOpen_ball
      exact hb.sdiff isClosed_singleton
    exact hdiffR.differentiableAt (hop.mem_nhds hz')
  have eqInt : (∮ z in C(c, r), f z) = ∮ z in C(c, R / 2), f z := by
    simpa using (circleIntegral_eq_of_differentiable_on_annulus_off_countable (c := c)
      (r := R / 2) (R := r) (h0 := half_pos hRpos) (hle := hr_ge)
      (hs := countable_empty) (hc := hcont) (hd := by
        intro z hz; exact hdiff z hz.1))
  have eqInt' : (∮ z in C(c, (Classical.choose hf) / 2), f z) = ∮ z in C(c, r), f z := by
    simpa [R] using Eq.symm eqInt
  -- Unfold residue and rewrite
  have : residue f c hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, (Classical.choose hf) / 2), f z := by
    simp [residue]
  simp [residue, eqInt'] at this ⊢

/-- The residue can be computed using any sufficiently small circle around the singularity. -/
@[simp]
lemma residue_eq_two_pi_I_inv_smul_circleIntegral {f : ℂ → ℂ} {c : ℂ}
    (hf : HasIsolatedSingularityAt f c)
    {r : ℝ} (hr0 : 0 < r) (hrlt : r < Classical.choose hf) :
    residue f c hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z := by
  classical
  let R := Classical.choose hf
  have hRpos : 0 < R := (Classical.choose_spec hf).1
  by_cases hrge : R / 2 ≤ r
  · exact residue_eq_two_pi_I_inv_smul_circleIntegral_of_ge hf hrlt hrge
  · have hrle : r ≤ R / 2 := le_of_not_ge hrge
    exact residue_eq_two_pi_I_inv_smul_circleIntegral_of_le hf hr0 hrle

section PrivateHelpers

/-- A technical lemma for choosing integration radii. -/
private lemma safe_radius {R Rw : ℝ} (hR : 0 < R) (hRw : 0 < Rw) :
    let r := min R Rw / 2
    0 < r ∧ r ≤ Rw / 2 ∧ r < R := by
  constructor
  · -- 0 < r
    have : 0 < min R Rw := lt_min hR hRw
    exact half_pos this
  constructor
  · -- r ≤ Rw / 2
    have : min R Rw ≤ Rw := min_le_right _ _
    exact div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2)
  · -- r < R
    calc min R Rw / 2
      ≤ R / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
      _ < R := half_lt_self hR

end PrivateHelpers


/-- Holomorphic functions have zero residue. -/
@[simp]
lemma residue_of_holomorphic {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hd : DifferentiableOn ℂ f (ball c R))
    (hf : HasIsolatedSingularityAt f c) :
    residue f c hf = 0 := by
  classical
  -- choose a safe radius inside both R and the witness radius
  let Rw : ℝ := Classical.choose hf
  have hRw : 0 < Rw := (Classical.choose_spec hf).1
  let r : ℝ := min R Rw / 2
  have ⟨hr0, hrle, hrr⟩ := safe_radius hR hRw
  -- reduce residue to integral on radius r
  have hres := residue_eq_two_pi_I_inv_smul_circleIntegral_of_le hf hr0 hrle
  -- continuity on closedBall c r
  have hsubset_cb_to_ball : closedBall c r ⊆ ball c R := by
    intro z hz
    apply mem_ball.mpr
    have hzle : dist z c ≤ r := mem_closedBall.mp hz
    calc dist z c ≤ r := hzle
      _ < R := hrr
  have hc : ContinuousOn f (closedBall c r) := (hd.continuousOn).mono hsubset_cb_to_ball
  -- differentiability on ball c r
  have hd' : ∀ z ∈ ball c r, DifferentiableAt ℂ f z := by
    intro z hz
    have hzR : z ∈ ball c R := by
      have : ball c r ⊆ ball c R := by
        intro w hw; apply mem_ball.mpr
        calc dist w c < r := mem_ball.mp hw
          _ < R := hrr
      exact this hz
    exact hd.differentiableAt (isOpen_ball.mem_nhds hzR)
  -- circle integral is zero at radius r
  have hint : (∮ z in C(c, r), f z) = 0 := by
    simpa using
      (circleIntegral_eq_zero_of_differentiable_on_off_countable (E := ℂ)
        (R := r) (c := c) (h0 := le_of_lt hr0) (s := (∅ : Set ℂ))
        (hc := hc) (hd := by intro z hz; exact hd' z hz.1))
  -- conclude
  rw [hres, hint]
  exact smul_zero _

/-- For a simple pole `f(z) = (z - c)⁻¹ * g(z)` with `g` holomorphic at `c`,
the residue equals `g(c)`. -/
@[simp]
lemma residue_simple_pole {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hfdef : ∀ z, f z = (z - c)⁻¹ * g z) (hf : HasIsolatedSingularityAt f c) :
    residue f c hf = g c := by
  classical
  -- choose a safe radius inside both R and the witness radius
  let Rw : ℝ := Classical.choose hf
  have hRw : 0 < Rw := (Classical.choose_spec hf).1
  let r : ℝ := min R Rw / 2
  have ⟨hr0, hrle, hrr⟩ := safe_radius hR hRw
  -- reduce residue to integral on r
  have hres := residue_eq_two_pi_I_inv_smul_circleIntegral_of_le hf hr0 hrle
  -- circle integral formula at radius r
  have hw : c ∈ ball c r := mem_ball_self hr0
  -- continuity of g on closedBall c r
  have hsubset_cb_to_ball : closedBall c r ⊆ ball c R := by
    intro z hz
    apply mem_ball.mpr
    have hzle : dist z c ≤ r := mem_closedBall.mp hz
    calc dist z c ≤ r := hzle
      _ < R := hrr
  have hc : ContinuousOn g (closedBall c r) := (hg.continuousOn).mono hsubset_cb_to_ball
  have hdg' : ∀ z ∈ ball c r, DifferentiableAt ℂ g z := by
    intro z hz
    have hzR : z ∈ ball c R := by
      have : ball c r ⊆ ball c R := by
        intro w hw; apply mem_ball.mpr
        calc dist w c < r := mem_ball.mp hw
          _ < R := hrr
      exact this hz
    exact hg.differentiableAt (isOpen_ball.mem_nhds hzR)
  have hcir : (∮ z in C(c, r), f z) = (2 * π * I : ℂ) * g c := by
    simpa [hfdef, smul_eq_mul] using
      (circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (E := ℂ) (R := r) (c := c) (w := c) (f := g)
        (hs := countable_empty) (hw := hw) (hc := hc)
        (hd := by intro z hz; exact hdg' z hz.1))
  -- conclude: residue equals normalized integral, equals g c
  have hnonzero : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    simp [this]
  rw [hres, hcir, smul_eq_mul]
  field_simp [hnonzero]

-- Note: A more complete theory of removable singularities and their residues
-- would be developed in a separate file focused on singularity classification.

/-! ### Examples -/

section Examples

/-- The residue of `1/z` at `0` is `1`. -/
example : ∃ (hf : HasIsolatedSingularityAt (fun z : ℂ => z⁻¹) 0),
    residue (fun z : ℂ => z⁻¹) 0 hf = 1 := by
  -- First show that 1/z has an isolated singularity at 0
  have hiso : HasIsolatedSingularityAt (fun z : ℂ => z⁻¹) 0 := by
    use 1, zero_lt_one
    intro z ⟨hz, hz0⟩
    -- z is in ball 0 1 \ {0}, so z ≠ 0
    simp at hz0
    -- Show differentiability of z⁻¹ at z ≠ 0
    have : DifferentiableAt ℂ (fun w => w⁻¹) z := differentiableAt_inv hz0
    exact this.differentiableWithinAt
  use hiso
  -- Apply the simple pole formula with g(z) = 1
  have h_eq : ∀ z : ℂ, z⁻¹ = (z - 0)⁻¹ * 1 := by intro z; simp
  have h_diff : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (ball (0 : ℂ) 1) :=
    differentiableOn_const (1 : ℂ)
  exact residue_simple_pole zero_lt_one h_diff h_eq hiso

/-- The residue can be computed using any sufficiently small radius. -/
example : ∃ (hf : HasIsolatedSingularityAt (fun z : ℂ => z⁻¹) 0) (r : ℝ) (_ : 0 < r),
    residue (fun z : ℂ => z⁻¹) 0 hf = (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), z⁻¹ := by
  -- Same isolated singularity proof
  have hiso : HasIsolatedSingularityAt (fun z : ℂ => z⁻¹) 0 := by
    use 1, zero_lt_one
    intro z ⟨hz, hz0⟩
    simp at hz0
    have : DifferentiableAt ℂ (fun w => w⁻¹) z := differentiableAt_inv hz0
    exact this.differentiableWithinAt
  use hiso
  -- We can choose any radius less than the witness radius
  let R := Classical.choose hiso
  have hRpos : 0 < R := (Classical.choose_spec hiso).1
  use R / 2, half_pos hRpos
  exact residue_eq_two_pi_I_inv_smul_circleIntegral hiso (half_pos hRpos) (half_lt_self hRpos)

/-- The residue of the holomorphic function `z ↦ z` at any point is `0`. -/
example (c : ℂ) : ∃ (hf : HasIsolatedSingularityAt (fun z : ℂ => z) c),
    residue (fun z : ℂ => z) c hf = 0 := by
  -- id has a (removable) singularity at c
  have hiso : HasIsolatedSingularityAt (fun z : ℂ => z) c := by
    use 1, zero_lt_one
    exact differentiableOn_id
  use hiso
  -- Apply the holomorphic residue formula
  exact residue_of_holomorphic zero_lt_one differentiableOn_id hiso



end Examples

end Complex
