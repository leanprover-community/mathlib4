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
    Disjoint h k → ∃ f : X → ℝ, f ⁻¹' {0} = h ∧ f ⁻¹' {1} = k := by
  constructor
  · intro _ h k h_closed k_closed hk_dis
    rcases perfectly_normal_function h_closed with ⟨f_h, f_h_zero⟩
    rcases perfectly_normal_function k_closed with ⟨f_k, f_k_zero⟩
    use fun x => |f_h x| / (|f_h x| + |f_k x|)
    constructor
    · ext x
      simp
      constructor
      · by_cases fhxz : f_h x = 0
        · intro _
          rw [← f_h_zero.2]
          exact fhxz
        · rintro (nah|fhxfkx)
          · by_contra; apply fhxz; exact nah
          · replace fhxz : 0 < |f_h x| := abs_pos.mpr fhxz
            have : 0 ≤ |f_k x| := by apply abs_nonneg
            linarith
      · intro xh
        left
        rw [← f_h_zero.2] at xh
        exact xh
    · ext x
      simp
      sorry
      -- constructor
      -- · intro hyp
      --   rw [mul_inv_eq_one] at hyp
      --   replace hyp : |f_h x| = |f_h x| + |f_k x| := sorry
      --   replace hyp : |f_k x| = 0 := sorry
      --   rw [← f_k_zero]
      -- · rw [← f_k_zero]
  · intro hyp
    constructor
    intro h hcl
    have : ∃ f : X → ℝ, f ⁻¹' {0} = h ∧ f ⁻¹' {1} = ∅ := by
      apply hyp h ∅
      exact hcl
      simp
      simp
    rcases this with ⟨f, fand⟩
    use f
    sorry
    -- exact fand.1






end PerfectlyNormal
