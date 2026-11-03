import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Basic

open Complex Filter Set

theorem riemannZeta_meromorphicAt_one : MeromorphicAt riemannZeta 1 := by
  refine ⟨2, ?_⟩
  simp only [smul_eq_mul]
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact ((differentiableAt_id.sub_const 1).pow 2).mul (differentiableAt_riemannZeta hz)
  · have h1 : Tendsto (fun z : Complex => z - 1) (nhdsWithin 1 (Set.compl {1})) (nhds 0) := by
      have hc : ContinuousAt (fun z : Complex => z - 1) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun z : Complex => (z - 1) ^ 2 * riemannZeta z)
        (nhdsWithin 1 (Set.compl {1})) (nhds 0) := by
      have hm := h1.mul riemannZeta_residue_one
      simpa [pow_two, mul_assoc] using hm
    have hf1 : (fun z : Complex => (z - 1) ^ 2 * riemannZeta z) 1 = 0 := by
      show ((1 : Complex) - 1) ^ 2 * riemannZeta 1 = 0
      rw [sub_self, zero_pow (by norm_num), zero_mul]
    have huniv : (insert (1 : Complex) (Set.compl {1})) = Set.univ := by
      ext x
      by_cases h : x = 1
      · simp [h]
      · simp [h]; exact h
    change Tendsto (fun z : Complex => (z - 1) ^ 2 * riemannZeta z) (nhds 1)
      (nhds ((fun z : Complex => (z - 1) ^ 2 * riemannZeta z) 1))
    rw [hf1]
    rw [← nhdsWithin_univ, ← huniv, nhdsWithin_insert, tendsto_sup]
    refine ⟨?_, h3⟩
    rw [← hf1]
    have hpure : Tendsto (fun z : Complex => (z - 1) ^ 2 * riemannZeta z) (pure 1)
        (pure ((fun z : Complex => (z - 1) ^ 2 * riemannZeta z) 1)) := by
      exact tendsto_pure.mpr (by simp : ∀ᶠ x in pure (1 : Complex), (fun z : Complex => (z - 1) ^ 2 * riemannZeta z) x = (fun z : Complex => (z - 1) ^ 2 * riemannZeta z) 1)
    exact hpure.mono_right (by simp)
