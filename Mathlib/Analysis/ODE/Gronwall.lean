/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwallBound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `‖f a‖ ≤ δ`
and `∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then for all `x ∈ [a, b]` we have `‖f x‖ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwallBound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/

@[expose] public section

open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Technical lemmas about `gronwallBound` -/


/-- Upper bound used in several Grönwall-like inequalities. -/
noncomputable def gronwallBound (δ K ε x : ℝ) : ℝ :=
  if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)

theorem gronwallBound_K0 (δ ε : ℝ) : gronwallBound δ 0 ε = fun x => δ + ε * x :=
  funext fun _ => if_pos rfl

theorem gronwallBound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
    gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1) :=
  funext fun _ => if_neg hK

theorem hasDerivAt_gronwallBound (δ K ε x : ℝ) :
    HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
      ((((hasDerivAt_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1
    simp only [id]
    field

theorem hasDerivAt_gronwallBound_shift (δ K ε x a : ℝ) :
    HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x := by
  convert (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id, mul_one]

theorem gronwallBound_x0 (δ K ε : ℝ) : gronwallBound δ K ε 0 = δ := by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]

theorem gronwallBound_ε0 (δ K x : ℝ) : gronwallBound δ K 0 x = δ * exp (K * x) := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]

theorem gronwallBound_ε0_δ0 (K x : ℝ) : gronwallBound 0 K 0 x = 0 := by
  simp only [gronwallBound_ε0, zero_mul]

theorem gronwallBound_continuous_ε (δ K x : ℝ) : Continuous fun ε => gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hK]
    fun_prop

/-- The Grönwall bound is monotone with respect to the time variable `x`. -/
lemma gronwallBound_mono {δ K ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    Monotone (gronwallBound δ K ε) := by
  intro x₁ x₂ hx
  unfold gronwallBound
  split_ifs with hK₀
  · gcongr
  · have hK_pos : 0 < K := by positivity
    gcongr

/-! ### Inequality and corollaries -/

/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwallBound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwallBound_of_norm_deriv_right_le` for a version bounding `‖f x‖`,
`f : ℝ → E`. -/
theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε) :
    ∀ x ∈ Icc a b, f x ≤ gronwallBound δ K ε (x - a) := by
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioi ε, f x ≤ gronwallBound δ K ε' (x - a) := by
    intro x hx ε' (hε' : ε < ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
    · grind
    · exact hx
  intro x hx
  change f x ≤ (fun ε' => gronwallBound δ K ε' (x - a)) ε
  convert ContinuousWithinAt.const.closure_le _ _ (H x hx)
  · simp only [closure_Ioi, self_mem_Ici]
  exact (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `‖f a‖ ≤ δ`,
`∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then `‖f x‖` is bounded by `gronwallBound δ K ε (x - a)`
on `[a, b]`. -/
theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

/-- Let `f : [a, b] → E` be a differentiable function such that `f a = 0`
and `‖f'(x)‖ ≤ K ‖f(x)‖` for some constant `K`. Then `f = 0` on `[a, b]`. -/
theorem eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right {f f' : ℝ → E} {K a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a = 0) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖) :
    ∀ x ∈ Set.Icc a b, f x = 0 := by
  intro x hx
  apply norm_le_zero_iff.mp
  calc ‖f x‖
    _ ≤ gronwallBound 0 K 0 (x - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hf hf' (by simp [ha]) (by simpa using bound) _ hx
    _ = 0 := by rw [gronwallBound_ε0_δ0]

variable {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g f' g' : ℝ → E} {a b t₀ : ℝ} {εf εg δ : ℝ}

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) := by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))
  have := (hv t ht).dist_le_mul _ (hfs t ht) _ (hgs t ht)
  grind [dist_eq_norm]

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_approx_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) := by
  have f_bound : ∀ t ∈ Ico a b, dist (v t (f t)) (v t (f t)) ≤ 0 := by intros; rw [dist_self]
  have g_bound : ∀ t ∈ Ico a b, dist (v t (g t)) (v t (g t)) ≤ 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha

/-- There exists only one solution of an ODE $\dot x=v(t, x)$ in a set `s ⊆ ℝ × E` with
a given initial value provided that the RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`.

This version shows uniqueness in a closed interval `Icc a b`, where `a` is the initial time. -/
theorem ODE_solution_unique_of_mem_Icc_right
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

/-- A time-reversed version of `ODE_solution_unique_of_mem_Icc_right`. Uniqueness is shown in a
closed interval `Icc a b`, where `b` is the "initial" time. -/
theorem ODE_solution_unique_of_mem_Icc_left
    (hv : ∀ t ∈ Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioc a b, HasDerivWithinAt f (v t (f t)) (Iic t) t)
    (hfs : ∀ t ∈ Ioc a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioc a b, HasDerivWithinAt g (v t (g t)) (Iic t) t)
    (hgs : ∀ t ∈ Ioc a b, g t ∈ s t)
    (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  have hv' : ∀ t ∈ Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t ∈ Ioc a b := by
      push _ ∈ _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht ↦ ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht ↦ ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt3 (t : ℝ) : MapsTo Neg.neg (Ici t) (Iic (-t)) :=
    fun _ ht' ↦ mem_Iic.mpr <| neg_le_neg ht'
  suffices EqOn (f ∘ Neg.neg) (g ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at this
    convert this
    simp
  apply ODE_solution_unique_of_mem_Icc_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hgs _ (hmt2 ht)) (by simp [hb])
  · intro t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp
  · intro t ht
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp

/-- A version of `ODE_solution_unique_of_mem_Icc_right` for uniqueness in a closed interval whose
interior contains the initial time. -/
theorem ODE_solution_unique_of_mem_Icc
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ ⊆ Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq
  · have hss : Ico t₀ b ⊆ Ioo a b := Ico_subset_Ioo_left ht.1
    exact ODE_solution_unique_of_mem_Icc_right (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq

/-- A version of `ODE_solution_unique_of_mem_Icc` for uniqueness in an open interval. -/
theorem ODE_solution_unique_of_mem_Ioo
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t'' ht'' ↦ hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hf _ <| hss ht'').1)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ioc_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hg _ <| hss ht'').1)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ioc_subset_Icc_self ht'').2) heq
      ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t' ⊆ Ioo a b :=
      fun _ ht'' ↦ ⟨lt_of_lt_of_le ht.1 ht''.1, lt_of_le_of_lt ht''.2 ht'.2⟩
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t'' ht'' ↦ hv t'' ((Ico_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hf _ <| hss ht'').1)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hf _ <| hss <| Ico_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' ↦ (hg _ <| hss ht'').1)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' ↦ (hg _ <| hss <| Ico_subset_Icc_self ht'').2) heq
      ⟨h, le_rfl⟩

/-- Local uniqueness of ODE solutions. -/
theorem ODE_solution_unique_of_eventually
    (hv : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t))
    (hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and (hf.and hg))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo (fun _ ht ↦ (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_self hε)
    (fun _ ht ↦ (h _ ht).2.1) (fun _ ht ↦ (h _ ht).2.2) heq

/-- There exists only one solution of an ODE $\dot x=v(t, x)$ with
a given initial value provided that the RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ univ := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha

/-- There exists only one global solution to an ODE $\dot x=v(t, x)$ with a given initial value
provided that the RHS is Lipschitz continuous. -/
theorem ODE_solution_unique_univ
    (hv : ∀ t, LipschitzOnWith K (v t) (s t))
    (hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f = g := by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : ∃ A B, t ∈ Set.Ioo A B ∧ t₀ ∈ Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    grind
  exact ODE_solution_unique_of_mem_Ioo
    (fun t _ => hv t) Ht₀ (fun t _ => hf t) (fun t _ => hg t) heq Ht
