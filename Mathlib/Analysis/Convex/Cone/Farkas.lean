import Mathlib.Analysis.Convex.Cone.Caratheodory
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ProperMap

open ContinuousLinearMap Filter Set Matrix

variable {m n : Type*}
variable [Fintype m] [Fintype n]
variable (A : (EuclideanSpace ℝ m) →L[ℝ] (EuclideanSpace ℝ n))

/-

New strategy:

First work purely in (n → ℝ) and don't even worry about cones.
Show that A '' Set.ici 0 is closed using Caratheodory.

Use this to define the closed PointedCone in (n → ℝ)

Then use continuousLinearEquiv to send the closed, PointedCone in (n → ℝ) to closed, PointedCone in Euclidean ℝ n.

Finally, work with hyperplane_separation for PointedCone to show Farkas lemma.

-/

namespace EuclideanSpace

/-
Need to define module structures on ProperCones for any of this to work.
-/

noncomputable def positive (n) [Fintype n] : ProperCone ℝ (EuclideanSpace ℝ n) where
  carrier := (EuclideanSpace.equiv n ℝ).symm '' Set.Ici 0
  add_mem' := by
    simp only [PiLp.continuousLinearEquiv_symm_apply, Set.mem_image_equiv, Equiv.symm_symm,
      Set.mem_Ici, WithLp.equiv_add]
    rintro a b ha hb
    exact add_nonneg ha hb
  zero_mem' := by simp
  smul_mem' := by
    simp only [PiLp.continuousLinearEquiv_symm_apply, Set.mem_image_equiv, Equiv.symm_symm,
      Set.mem_Ici, WithLp.equiv_smul, Subtype.forall, Nonneg.mk_smul]
    rintro a ha x hx
    exact smul_nonneg ha hx
  isClosed' := by
    apply IsProperMap.isClosedMap <|
      Homeomorph.isProperMap (EuclideanSpace.equiv n ℝ).symm.toHomeomorph
    exact isClosed_Ici

@[simp]
theorem mem_positive {x : EuclideanSpace ℝ n} :
    x ∈ positive n ↔ 0 ≤ (EuclideanSpace.equiv n ℝ) x := by
  change x ∈ (EuclideanSpace.equiv n ℝ).symm '' Set.Ici 0 ↔ 0 ≤ (equiv n ℝ) x
  aesop


@[simp]
theorem mem_positive_dual [DecidableEq n] {x : EuclideanSpace ℝ n} :
    x ∈ (positive n).dual ↔ (0 : n → ℝ) ≤ x := by
  rw [ProperCone.mem_dual]
  constructor
  · rintro h i
    let xi' := (EuclideanSpace.equiv n ℝ).symm <| LinearMap.stdBasis ℝ (fun _ => ℝ) i 1
    have : xi' ∈ positive n := by
      simp_rw [PiLp.continuousLinearEquiv_symm_apply, mem_positive,
        PiLp.continuousLinearEquiv_apply, Equiv.apply_symm_apply]
      unfold LinearMap.stdBasis
      rintro _
      simp only [Pi.zero_apply, LinearMap.coe_single, Pi.single, Function.update, eq_rec_constant,
        dite_eq_ite]
      exact ite_nonneg zero_le_one (by rfl)
    specialize h this
    simpa using h
  · rintro x hx₁ hx₂
    rw [mem_positive] at hx₂
    exact Finset.sum_nonneg <| fun i _ => mul_nonneg (by aesop) (by aesop)

end EuclideanSpace


theorem extracted (b : EuclideanSpace ℝ n) :
    ((∃ x, A x = b ∧ (0 : m → ℝ) ≤ x) ↔ b ∈ ProperCone.map A (EuclideanSpace.positive m)) := by
  -- unfold ProperCone.map
  rw [ProperCone.mem_map]
  rw [PointedCone.mem_closure]
  -- rw [PointedCone.closure]
  -- extract_goal
  sorry


theorem farkas_lemma [DecidableEq m]
    (b : EuclideanSpace ℝ n) :
      (∃ x, A x = b ∧ (0 : m → ℝ) ≤ x) ↔
        ¬(∃ y, (0 : m → ℝ) ≤ adjoint A y ∧ ⟪y, b⟫_ℝ < 0) := by
  push_neg
  set K := EuclideanSpace.positive m with hK
  have := @ProperCone.hyperplane_separation _ _ _ _ _ _ _ _ K A b
  rw [hK] at this
  convert this
  rw [extracted]
  rw [EuclideanSpace.mem_positive_dual] -- single `rw` does not work!
