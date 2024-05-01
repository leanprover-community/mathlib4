import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Separation
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Linarith

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section PerfectlyNormal

/-- A topological space `X` is a *perfectly normal space* if for each closed subset `h`,
there exists a continuous function `f : X → ℝ` with `f ⁻¹' {0} = h`. -/
class PerfectlyNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  perfectly_normal :
    ∀ ⦃h : Set X⦄, IsClosed h → ∃ f : X → ℝ, Continuous f ∧ f ⁻¹' {0} = h

export PerfectlyNormalSpace (perfectly_normal)

theorem perfectly_normal_function [PerfectlyNormalSpace X] {h : Set X} (h_closed : IsClosed h) :
  ∃ f : X → ℝ, Continuous f ∧ f ⁻¹' {0} = h := PerfectlyNormalSpace.perfectly_normal h_closed

theorem perfectly_normal_iff_closed_pair (X : Type u) [TopologicalSpace X] :
    PerfectlyNormalSpace X ↔ ∀ h k : Set X, IsClosed h → IsClosed k →
    Disjoint h k → ∃ f : X → ℝ, Continuous f ∧ f ⁻¹' {0} = h ∧ f ⁻¹' {1} = k := by
  constructor
  · intro _ h k h_closed k_closed hk_dis
    rw [Set.disjoint_iff] at hk_dis
    rcases perfectly_normal_function h_closed with ⟨f_h, f_h_cont, f_h_zero⟩
    rcases perfectly_normal_function k_closed with ⟨f_k, f_k_cont, f_k_zero⟩
    use fun x => |f_h x| / (|f_h x| + |f_k x|)
    constructor
    · apply (continuous_abs.comp f_h_cont).div
        ((continuous_abs.comp f_h_cont).add (continuous_abs.comp f_k_cont))
      simp
      intro x
      by_contra zerosum
      have : f_h x = 0 ∧ f_k x = 0 := abs_add_abs_eq_zero.mp zerosum
      have : x ∈ h ∩ k := by
        rw [← f_h_zero,← f_k_zero]
        simpa
      exact hk_dis this
    constructor
    · ext x
      simp
      constructor
      · by_cases fhxz : f_h x = 0
        · intro _
          rw [← f_h_zero]
          exact fhxz
        · rintro (fhxz₂|zerosum)
          · by_contra; apply fhxz; exact fhxz₂
          · rw [← f_h_zero]
            exact (abs_add_abs_eq_zero.mp zerosum).1
      · intro xh
        left
        rwa [← f_h_zero] at xh
    · ext x
      simp
      constructor
      · intro hyp
        apply eq_of_div_eq_one at hyp
        have : |f_k x| = 0 := by linarith
        have : f_k x = 0 := by rwa [← abs_eq_zero]
        rwa [← f_k_zero]
      · intro hyp
        have : x ∉ h := by
          by_contra xh
          exact hk_dis ⟨xh, hyp⟩
        rw [← f_k_zero] at hyp
        simp at hyp
        rw [hyp]
        have : |f_h x| ≠ 0 := by
          rw [← f_h_zero] at this
          simp at this
          rwa [← abs_eq_zero] at this
        simp
        apply div_self this
  · intro hyp
    constructor
    intro h hcl
    have : ∃ f : X → ℝ, Continuous f ∧ f ⁻¹' {0} = h ∧ f ⁻¹' {1} = ∅ := by
      apply hyp h ∅
      · exact hcl
      · simp
      · simp
    rcases this with ⟨f, _, _, _⟩
    use f

end PerfectlyNormal
