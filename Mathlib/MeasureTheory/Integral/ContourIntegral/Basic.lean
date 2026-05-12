module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

@[expose] public noncomputable section

open AffineMap MeasureTheory
open scoped unitInterval Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : ℂ}

def ContourIntegrable (f : ℂ → E) (γ : Path a b) :=
  CurveIntegrable (.toSpanSingleton ℂ ∘ f) γ

/-- TODO -/
def contourIntegral (f : ℂ → E) (γ : Path a b) : E :=
  ∫ᶜ x in γ, .toSpanSingleton ℂ (f x)

@[inherit_doc contourIntegral]
notation3 "∫ꟲ "(...)" in " γ ", "r:67:(scoped f => contourIntegral f γ) => r

theorem contourIntegral_of_not_completeSpace (h : ¬CompleteSpace E)
    (f : ℂ → E) (γ : Path a b) : ∫ꟲ x in γ, f x = 0 := by
  rw [contourIntegral, curveIntegral_of_not_completeSpace h]

theorem contourIntegral_eq_intervalIntegral_derivWithin_smul (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ, f x = ∫ t in 0..1, derivWithin γ.extend I t • f (γ.extend t) := by
  simp [contourIntegral, curveIntegral_def, curveIntegralFun_def]

theorem contourIntegral_eq_intervalIntegral_deriv_smul (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ, f x = ∫ t in 0..1, deriv γ.extend t • f (γ.extend t) := by
  simp [contourIntegral, curveIntegral_eq_intervalIntegral_deriv]


/-!
### Operations on paths
-/

section PathOperations

variable {c d : ℂ} {f : ℂ → E} {γ γab : Path a b} {γbc : Path b c} {t : ℝ}

@[simp]
theorem contourIntegral_refl (f : ℂ → E) (a : ℂ) : ∫ꟲ x in .refl a, f x = 0 := by
  simp [contourIntegral]

@[simp]
theorem ContourIntegrable.refl (f : ℂ → E) (a : ℂ) : ContourIntegrable f (.refl a) :=
  CurveIntegrable.refl ..

@[simp]
theorem contourIntegral_cast (f : ℂ → E) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ꟲ x in γ.cast hc hd, f x = ∫ꟲ x in γ, f x := by
  simp [contourIntegral]

@[simp]
theorem contourIntegrable_cast_iff (hc : c = a) (hd : d = b) :
    ContourIntegrable f (γ.cast hc hd) ↔ ContourIntegrable f γ := by
  simp [ContourIntegrable]

protected alias ⟨_, ContourIntegrable.cast⟩ := curveIntegrable_cast_iff

protected theorem ContourIntegrable.symm (h : ContourIntegrable f γ) :
    ContourIntegrable f γ.symm :=
  CurveIntegrable.symm h

@[simp]
theorem contourIntegrable_symm : ContourIntegrable f γ.symm ↔ ContourIntegrable f γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem contourIntegral_symm (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ.symm, f x = -∫ꟲ x in γ, f x := by
  simp [contourIntegral]

protected theorem ContourIntegrable.trans (h₁ : ContourIntegrable f γab)
    (h₂ : ContourIntegrable f γbc) :
    ContourIntegrable f (γab.trans γbc) :=
  CurveIntegrable.trans h₁ h₂

theorem contourIntegral_trans (h₁ : ContourIntegrable f γab) (h₂ : ContourIntegrable f γbc) :
    ∫ꟲ x in γab.trans γbc, f x = (∫ꟲ x in γab, f x) + ∫ꟲ x in γbc, f x :=
  curveIntegral_trans h₁ h₂

theorem contourIntegrable_segment :
    ContourIntegrable f (.segment a b) ↔
      a = b ∨ IntervalIntegrable (fun t ↦ f (lineMap a b t)) volume 0 1 := by
  simp [ContourIntegrable, curveIntegrable_segment, sub_eq_zero, @eq_comm _ a]

theorem contourIntegral_segment (f : ℂ → E) (a b : ℂ) :
    ∫ꟲ x in .segment a b, f x = (b - a) • ∫ t in 0..1, f (lineMap a b t) := by
  simp [contourIntegral, curveIntegral_segment]

@[simp]
theorem contourIntegral_segment_const [CompleteSpace E] (a b : ℂ) (y : E) :
    ∫ꟲ _ in .segment a b, y = (b - a) • y := by
  simp [contourIntegral_segment]

/-- If `‖f z‖ ≤ C` at all points of the segment `[a -[ℝ] b]`,
then the contour integral `∫ꟲ x in .segment a b, f x` has norm at most `C * ‖b - a‖`. -/
theorem norm_contourIntegral_segment_le {C : ℝ} (h : ∀ z ∈ [a -[ℝ] b], ‖f z‖ ≤ C) :
    ‖∫ꟲ x in .segment a b, f x‖ ≤ C * ‖b - a‖ :=
  norm_curveIntegral_segment_le <| by simpa

/-- If a function `f` is continuous on a set `s`,
then it is contour integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.contourIntegrable_of_contDiffOn {s : Set ℂ}
    (hf : ContinuousOn f s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    ContourIntegrable f γ := by
  refine ContinuousOn.curveIntegrable_of_contDiffOn ?_ hγ hγs
  exact ContinuousLinearMap.toSpanSingletonCLE.continuous.comp_continuousOn hf

end PathOperations

/-!
### Algebraic operations on the function
-/

section Algebra

variable {f f₁ f₂ : ℂ → E} {γ : Path a b} {t : ℝ}

@[to_fun]
protected theorem ContourIntegrable.add (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ContourIntegrable (f₁ + f₂) γ := by
  simpa [ContourIntegrable] using CurveIntegrable.add h₁ h₂

theorem contourIntegral_add (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    contourIntegral (f₁ + f₂) γ = ∫ꟲ x in γ, f₁ x + ∫ꟲ x in γ, f₂ x := by
  simpa [contourIntegral, ContinuousLinearMap.toSpanSingleton_add] using curveIntegral_add h₁ h₂

theorem contourIntegral_fun_add (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ∫ꟲ x in γ, (f₁ x + f₂ x) = ∫ꟲ x in γ, f₁ x + ∫ꟲ x in γ, f₂ x :=
  contourIntegral_add h₁ h₂

@[to_fun]
theorem ContourIntegrable.zero : ContourIntegrable (0 : ℂ → E) γ := by
  simp [ContourIntegrable]

@[simp]
theorem contourIntegral_zero : contourIntegral (0 : ℂ → E) γ = 0 := by simp [contourIntegral]

@[simp]
theorem contourIntegral_fun_zero : ∫ꟲ _ in γ, (0 : E) = 0 := contourIntegral_zero

-- TODO: add `ContinuousLinearMap.toSpanSingleton_neg`
@[to_fun]
theorem ContourIntegrable.neg (h : ContourIntegrable f γ) : ContourIntegrable (-f) γ := by
  simpa [ContourIntegrable, Function.comp_def, ContinuousLinearMap.toSpanSingleton_neg]
    using CurveIntegrable.neg h

@[simp]
theorem contourIntegrable_neg_iff : ContourIntegrable (-f) γ ↔ ContourIntegrable f γ :=
  ⟨fun h ↦ by simpa using h.neg, .neg⟩

@[simp]
theorem contourIntegrable_fun_neg_iff : ContourIntegrable (-f ·) γ ↔ ContourIntegrable f γ :=
  contourIntegrable_neg_iff

@[simp]
theorem contourIntegral_neg : contourIntegral (-f) γ = -∫ꟲ x in γ, f x := by
  simp [contourIntegral]

@[simp]
theorem contourIntegral_fun_neg : ∫ꟲ x in γ, -f x = -∫ꟲ x in γ, f x := contourIntegral_neg

protected theorem ContourIntegrable.sub (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ContourIntegrable (f₁ - f₂) γ :=
  sub_eq_add_neg f₁ f₂ ▸ h₁.add h₂.neg

theorem contourIntegral_sub (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    contourIntegral (f₁ - f₂) γ = ∫ꟲ x in γ, f₁ x - ∫ꟲ x in γ, f₂ x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, contourIntegral_add h₁ h₂.neg, contourIntegral_neg]

theorem contourIntegral_fun_sub (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ∫ꟲ x in γ, (f₁ x - f₂ x) = ∫ꟲ x in γ, f₁ x - ∫ꟲ x in γ, f₂ x :=
  contourIntegral_sub h₁ h₂


section RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [NormedSpace 𝕝 E]
  [LinearMap.CompatibleSMul E F 𝕝 𝕜]

@[simp]
theorem contourIntegralFun_restrictScalars :
    contourIntegralFun (fun t ↦ (f t).restrictScalars 𝕝) γ = contourIntegralFun f γ := by
  ext
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  simp [contourIntegralFun_def]

@[simp]
theorem contourIntegrable_restrictScalars_iff :
    ContourIntegrable (fun t ↦ (f t).restrictScalars 𝕝) γ ↔ ContourIntegrable f γ := by
  simp [ContourIntegrable]

@[simp]
theorem contourIntegral_restrictScalars :
    ∫ꟲ x in γ, (f x).restrictScalars 𝕝 = ∫ꟲ x in γ, f x := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [contourIntegral_def]

end RestrictScalars

variable {𝕝 : Type*} [RCLike 𝕝] [NormedSpace 𝕝 F] [SMulCommClass 𝕜 𝕝 F] {c : 𝕝}

@[simp]
theorem contourIntegralFun_smul : contourIntegralFun (c • f) γ = c • contourIntegralFun f γ := by
  ext
  simp [contourIntegralFun]

theorem ContourIntegrable.smul (h : ContourIntegrable f γ) :
    ContourIntegrable (c • f) γ := by
  simpa [ContourIntegrable] using IntervalIntegrable.smul h c

@[simp]
theorem contourIntegrable_smul_iff : ContourIntegrable (c • f) γ ↔ c = 0 ∨ ContourIntegrable f γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [ContourIntegrable.zero]
  · simp only [hc, false_or]
    refine ⟨fun h ↦ ?_, .smul⟩
    simpa [hc] using h.smul (c := c⁻¹)

@[simp]
theorem contourIntegral_smul : contourIntegral (c • f) γ = c • contourIntegral f γ := by
  letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  simp [contourIntegral_def, intervalIntegral.integral_smul]

@[simp]
theorem contourIntegral_fun_smul : ∫ꟲ x in γ, c • f x = c • ∫ꟲ x in γ, f x := contourIntegral_smul

end Algebra

section FDeriv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {s : Set E} {f : ℂ → E}

/-!
### Derivative of the curve integral w.r.t. the right endpoint

In this section we prove that the integral of `f` along `[a -[ℝ] b]`, as a function of `b`,
has derivative `f a` at `b = a`.
We provide several versions of this theorem, for `HasFDerivWithinAt` and `HasFDerivAt`,
as well as for continuity near a point and for continuity on the whole set or space.

Note that we take the derivative at the left endpoint of the segment.
Similar facts about the derivative at a different point are true
provided that `f` is a closed 1-form (formalization WIP, see #24019).
-/

/-- The integral of `f` along `[a -[ℝ] b]`, as a function of `b`, has derivative `f a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `f` is continuous within a convex set `s`
in a neighborhood of `a` within `s`. -/
theorem HasFDerivWithinAt.contourIntegral_segment_source' (hs : Convex ℝ s)
    (hf : ∀ᶠ x in 𝓝[s] a, ContinuousWithinAt f s x) (ha : a ∈ s) :
    HasFDerivWithinAt (∫ꟲ x in .segment a ·, f x) (f a) s a := by
  /- Given `ε > 0`, take a number `δ > 0` such that `f` is continuous on `ball a δ ∩ s`
  and `‖f z - f a‖ ≤ ε` on this set.
  Then for `b ∈ ball a δ ∩ s`, we have
  `‖(∫ꟲ x in .segment a b, f x) - f a (b - a)‖
    = ‖(∫ꟲ x in .segment a b, f x) - ∫ꟲ x in .segment a b, f a‖
    ≤ ∫ x in 0..1, ‖f x - f a‖ * ‖b - a‖
    ≤ ε * ‖b - a‖`
  -/
  simp only [hasFDerivWithinAt_iff_isLittleO, Path.segment_same, contourIntegral_refl, sub_zero,
    Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0,
      ball a δ ∩ s ⊆ {z | ContinuousWithinAt f s z ∧ dist (f z) (f a) ≤ ε} := by
    rw [← Metric.mem_nhdsWithin_iff, setOf_and, inter_mem_iff]
    exact ⟨hf, (hf.self_of_nhdsWithin ha).eventually <| closedBall_mem_nhds _ hε⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have hsub : [a -[ℝ] b] ⊆ ball a δ ∩ s :=
    ((convex_ball _ _).inter hs).segment_subset (by simp [*]) (by simp [*])
  rw [← contourIntegral_segment_const, ← contourIntegral_fun_sub]
  · refine norm_contourIntegral_segment_le fun z hz ↦ ?_
    simpa [dist_eq_norm] using (hδ (hsub hz)).2
  · rw [contourIntegrable_segment]
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t ht ↦ ?_
    refine ((hδ ?_).1.eval_const _).comp AffineMap.lineMap_continuous.continuousWithinAt ?_
    · exact hsub <| lineMap_mem_segment ℝ a b ht
    · rw [mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      exact hs.segment_subset ha hbs
  · rw [contourIntegrable_segment]
    exact intervalIntegrable_const

/-- The integral of `f` along `[a -[ℝ] b]`, as a function of `b`, has derivative `f a` at `b = a`.
This is a `HasFDerivWithinAt` version assuming that `f` is continuous on `s`. -/
theorem HasFDerivWithinAt.contourIntegral_segment_source (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (ha : a ∈ s) : HasFDerivWithinAt (∫ꟲ x in .segment a ·, f x) (f a) s a :=
  .contourIntegral_segment_source' hs (mem_of_superset self_mem_nhdsWithin hf) ha

/-- The integral of `f` along `[a -[ℝ] b]`, as a function of `b`, has derivative `f a` at `b = a`.
This is a `HasFDerivAt` version assuming that `f` is continuous in a neighborhood of `a`. -/
theorem HasFDerivAt.contourIntegral_segment_source' (hf : ∀ᶠ z in 𝓝 a, ContinuousAt f z) :
    HasFDerivAt (∫ꟲ x in .segment a ·, f x) (f a) a :=
  HasFDerivWithinAt.contourIntegral_segment_source' convex_univ
    (by simpa only [nhdsWithin_univ, continuousWithinAt_univ]) (mem_univ _) |>.hasFDerivAt_of_univ

/-- The integral of `f` along `[a -[ℝ] b]`, as a function of `b`, has derivative `f a` at `b = a`.
This is a `HasFDerivAt` version assuming that `f` is continuous on the whole space. -/
theorem HasFDerivAt.contourIntegral_segment_source (hf : Continuous f) :
    HasFDerivAt (∫ꟲ x in .segment a ·, f x) (f a) a :=
  .contourIntegral_segment_source' <| .of_forall fun _ ↦ hf.continuousAt

end FDeriv
