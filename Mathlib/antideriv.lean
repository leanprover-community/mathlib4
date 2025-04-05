import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Set Function MeasureTheory Metric
open scoped Topology Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem Convex.exists_hasFDerivWithin_of_symmetric {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s)
    {f' : E → E →L[ℝ] F} {f'' : E → E →L[ℝ] E →L[ℝ] F}
    (hf' : ∀ x ∈ s, HasFDerivAt f' (f'' x) x)
    (hf''_symm : ∀ x ∈ s, ∀ u v, f'' x u v = f'' x v u) (hf''_cont : ContinuousOn f'' s) :
    ∃ f : E → F, ∀ x ∈ s, HasFDerivAt f (f' x) x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · wlog ha₀ : a = 0 generalizing s f' f'' a
    · rcases @this _ (hs.vadd (-a)) (hso.vadd (-a)) (f' <| a + ·) (f'' <| a + ·)
        (forall_mem_image.2 fun x hx ↦ by simp [hasFDerivAt_comp_add_left, hf' x hx])
        (forall_mem_image.2 fun x hx u v ↦ by simpa using hf''_symm x hx u v)
        (hf''_cont.comp (by fun_prop) (by simp [MapsTo, mem_vadd_set])) 0 ⟨a, ha, by simp⟩ rfl
        with ⟨f, hf⟩
      use (f <| -a + ·)
      simpa [hasFDerivAt_comp_add_left, mem_vadd_set] using hf
    subst a
    set f : E → F := fun x ↦ ∫ t in (0)..1, f' (t • x) x
    refine ⟨f, fun y hy ↦ ?_⟩
    have hts : ∀ t ∈ [[(0 : ℝ), 1]], t • y ∈ s := fun t ht ↦
      hs.smul_mem_of_zero_mem ha hy <| by rwa [uIcc_of_le zero_le_one] at ht
    set F' : ℝ → E →L[ℝ] F := fun t ↦ f' (t • y) + t • f'' (t • y) y with hF'
    obtain ⟨ε, hε_pos, hεs⟩ : ∃ ε : ℝ, 0 < ε ∧ ball y ε ⊆ s := by
      exact mem_nhds_iff.mp (hso.mem_nhds hy)
    have hdF' : ∀ t ∈ [[0, 1]], HasDerivAt (fun t : ℝ ↦ t • f' (t • y)) (F' t) t := by
      intro t ht
      rw [hF']
      have := (hf' _ (hts t ht)).comp_hasDerivAt_of_eq t ((hasDerivAt_id t).smul_const y) rfl
      simpa [add_comm] using (hasDerivAt_id t).smul this
    have Hintegrable : ∀ x ∈ s, IntervalIntegrable (fun t ↦ f' (t • x) x) volume 0 1 := by
      intro x hx
      apply ContinuousOn.intervalIntegrable
      intro t ht
      replace ht : t • x ∈ s := by
        rw [uIcc_of_le zero_le_one] at ht
        exact hs.smul_mem_of_zero_mem ha hx ht
      exact (hf' (t • x) ht).continuousAt.comp_of_eq
        (continuousAt_id.smul continuousAt_const) rfl |>.eval_const x |>.continuousWithinAt
    have HintegrableF' : IntervalIntegrable F' volume 0 1 := sorry
    have Hint : ∫ t in (0)..1, F' t = f' y := by
      simp [intervalIntegral.integral_eq_sub_of_hasDerivAt hdF' HintegrableF']
    rw [← Hint]
    apply (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip' hε_pos _ _ _ _ _ _).2
    · sorry -- bound
    · exact fun x hx ↦ (Hintegrable x (hεs hx)).def'.1
    · exact Hintegrable y hy
    · exact HintegrableF'.def'.1
    · refine .of_forall fun t ht x hx ↦ ?_
      sorry
    · sorry
    · refine .of_forall fun t ht ↦ ?_
      convert (hf' (t • y) (hts _ (uIoc_subset_uIcc ht))).comp y
        ((hasFDerivAt_id y).const_smul t) |>.clm_apply (hasFDerivAt_id y) using 1
      ext z
      simp [F', hf''_symm (t • y) (hts _ (uIoc_subset_uIcc ht))]
      
      
