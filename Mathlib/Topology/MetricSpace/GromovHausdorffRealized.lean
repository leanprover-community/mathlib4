/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.gromov_hausdorff_realized
! leanprover-community/mathlib commit 0c1f285a9f6e608ae2bdffa3f993eafb01eba829
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Gluing
import Mathbin.Topology.MetricSpace.HausdorffDistance
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# The Gromov-Hausdorff distance is realized

In this file, we construct of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces.

Given two nonempty compact metric spaces `X` and `Y`, we define `optimal_GH_coupling X Y` as a
compact metric space, together with two isometric embeddings `optimal_GH_injl` and `optimal_GH_injr`
respectively of `X` and `Y` into `optimal_GH_coupling X Y`. The main property of the optimal
coupling is that the Hausdorff distance between `X` and `Y` in `optimal_GH_coupling X Y` is smaller
than the corresponding distance in any other coupling. We do not prove completely this fact in this
file, but we show a good enough approximation of this fact in `Hausdorff_dist_optimal_le_HD`, that
will suffice to obtain the full statement once the Gromov-Hausdorff distance is properly defined,
in `Hausdorff_dist_optimal`.

The key point in the construction is that the set of possible distances coming from isometric
embeddings of `X` and `Y` in metric spaces is a set of equicontinuous functions. By Arzela-Ascoli,
it is compact, and one can find such a distance which is minimal. This distance defines a premetric
space structure on `X ⊕ Y`. The corresponding metric quotient is `optimal_GH_coupling X Y`.
-/


noncomputable section

open Classical Topology NNReal

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotient

open BoundedContinuousFunction

open Sum (inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GromovHausdorffRealized

/- This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
`X ⊕ Y` of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/
section Definitions

variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

@[reducible]
private def prod_space_fun : Type _ :=
  Sum X Y × Sum X Y → ℝ
#align Gromov_Hausdorff.prod_space_fun Gromov_Hausdorff.prod_space_fun

@[reducible]
private def Cb : Type _ :=
  BoundedContinuousFunction (Sum X Y × Sum X Y) ℝ
#align Gromov_Hausdorff.Cb Gromov_Hausdorff.Cb

private def max_var : ℝ≥0 :=
  2 * ⟨diam (univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (univ : Set Y), diam_nonneg⟩
#align Gromov_Hausdorff.max_var Gromov_Hausdorff.max_var

private theorem one_le_max_var : 1 ≤ maxVar X Y :=
  calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by simp
    _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by
      apply_rules [add_le_add, mul_le_mul_of_nonneg_left, diam_nonneg] <;> norm_num
    
#align Gromov_Hausdorff.one_le_max_var Gromov_Hausdorff.one_le_max_var

/-- The set of functions on `X ⊕ Y` that are candidates distances to realize the
minimum of the Hausdorff distances between `X` and `Y` in a coupling -/
def candidates : Set (ProdSpaceFun X Y) :=
  { f |
    (((((∀ x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧
              ∀ x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
            ∀ x y, f (x, y) = f (y, x)) ∧
          ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)) ∧
        ∀ x, f (x, x) = 0) ∧
      ∀ x y, f (x, y) ≤ maxVar X Y }
#align Gromov_Hausdorff.candidates GromovHausdorff.candidates

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
private def candidates_b : Set (Cb X Y) :=
  { f : Cb X Y | (f : _ → ℝ) ∈ candidates X Y }
#align Gromov_Hausdorff.candidates_b Gromov_Hausdorff.candidates_b

end Definitions

--section
section Constructions

variable {X : Type u} {Y : Type v} [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y] {f : ProdSpaceFun X Y} {x y z t : Sum X Y}

attribute [local instance 10] inhabited_of_nonempty'

private theorem max_var_bound : dist x y ≤ maxVar X Y :=
  calc
    dist x y ≤ diam (univ : Set (Sum X Y)) :=
      dist_le_diam_of_mem bounded_of_compactSpace (mem_univ _) (mem_univ _)
    _ = diam (range inl ∪ range inr : Set (Sum X Y)) := by rw [range_inl_union_range_inr]
    _ ≤
        diam (range inl : Set (Sum X Y)) + dist (inl default) (inr default) +
          diam (range inr : Set (Sum X Y)) :=
      (diam_union (mem_range_self _) (mem_range_self _))
    _ =
        diam (univ : Set X) + (dist default default + 1 + dist default default) +
          diam (univ : Set Y) :=
      by
      rw [isometry_inl.diam_range, isometry_inr.diam_range]
      rfl
    _ = 1 * diam (univ : Set X) + 1 + 1 * diam (univ : Set Y) := by simp
    _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) :=
      by
      apply_rules [add_le_add, mul_le_mul_of_nonneg_right, diam_nonneg, le_refl]
      norm_num; norm_num
    
#align Gromov_Hausdorff.max_var_bound Gromov_Hausdorff.max_var_bound

private theorem candidates_symm (fA : f ∈ candidates X Y) : f (x, y) = f (y, x) :=
  fA.1.1.1.2 x y
#align Gromov_Hausdorff.candidates_symm Gromov_Hausdorff.candidates_symm

private theorem candidates_triangle (fA : f ∈ candidates X Y) : f (x, z) ≤ f (x, y) + f (y, z) :=
  fA.1.1.2 x y z
#align Gromov_Hausdorff.candidates_triangle Gromov_Hausdorff.candidates_triangle

private theorem candidates_refl (fA : f ∈ candidates X Y) : f (x, x) = 0 :=
  fA.1.2 x
#align Gromov_Hausdorff.candidates_refl Gromov_Hausdorff.candidates_refl

private theorem candidates_nonneg (fA : f ∈ candidates X Y) : 0 ≤ f (x, y) :=
  by
  have : 0 ≤ 2 * f (x, y) :=
    calc
      0 = f (x, x) := (candidates_refl fA).symm
      _ ≤ f (x, y) + f (y, x) := (candidates_triangle fA)
      _ = f (x, y) + f (x, y) := by rw [candidates_symm fA]
      _ = 2 * f (x, y) := by ring
      
  · linarith
#align Gromov_Hausdorff.candidates_nonneg Gromov_Hausdorff.candidates_nonneg

private theorem candidates_dist_inl (fA : f ∈ candidates X Y) (x y : X) :
    f (inl x, inl y) = dist x y :=
  fA.1.1.1.1.1 x y
#align Gromov_Hausdorff.candidates_dist_inl Gromov_Hausdorff.candidates_dist_inl

private theorem candidates_dist_inr (fA : f ∈ candidates X Y) (x y : Y) :
    f (inr x, inr y) = dist x y :=
  fA.1.1.1.1.2 x y
#align Gromov_Hausdorff.candidates_dist_inr Gromov_Hausdorff.candidates_dist_inr

private theorem candidates_le_max_var (fA : f ∈ candidates X Y) : f (x, y) ≤ maxVar X Y :=
  fA.2 x y
#align Gromov_Hausdorff.candidates_le_max_var Gromov_Hausdorff.candidates_le_max_var

/-- candidates are bounded by `max_var X Y` -/
private theorem candidates_dist_bound (fA : f ∈ candidates X Y) :
    ∀ {x y : Sum X Y}, f (x, y) ≤ maxVar X Y * dist x y
  | inl x, inl y =>
    calc
      f (inl x, inl y) = dist x y := candidates_dist_inl fA x y
      _ = dist (inl x) (inl y) := by
        rw [@sum.dist_eq X Y]
        rfl
      _ = 1 * dist (inl x) (inl y) := by simp
      _ ≤ maxVar X Y * dist (inl x) (inl y) :=
        mul_le_mul_of_nonneg_right (one_le_maxVar X Y) dist_nonneg
      
  | inl x, inr y =>
    calc
      f (inl x, inr y) ≤ maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) :=
        mul_le_mul_of_nonneg_left Sum.one_le_dist_inl_inr (le_trans zero_le_one (one_le_maxVar X Y))
      
  | inr x, inl y =>
    calc
      f (inr x, inl y) ≤ maxVar X Y := candidates_le_maxVar fA
      _ = maxVar X Y * 1 := by simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) :=
        mul_le_mul_of_nonneg_left Sum.one_le_dist_inl_inr (le_trans zero_le_one (one_le_maxVar X Y))
      
  | inr x, inr y =>
    calc
      f (inr x, inr y) = dist x y := candidates_dist_inr fA x y
      _ = dist (inr x) (inr y) := by
        rw [@sum.dist_eq X Y]
        rfl
      _ = 1 * dist (inr x) (inr y) := by simp
      _ ≤ maxVar X Y * dist (inr x) (inr y) :=
        mul_le_mul_of_nonneg_right (one_le_maxVar X Y) dist_nonneg
      
#align Gromov_Hausdorff.candidates_dist_bound Gromov_Hausdorff.candidates_dist_bound

/-- Technical lemma to prove that candidates are Lipschitz -/
private theorem candidates_lipschitz_aux (fA : f ∈ candidates X Y) :
    f (x, y) - f (z, t) ≤ 2 * maxVar X Y * dist (x, y) (z, t) :=
  calc
    f (x, y) - f (z, t) ≤ f (x, t) + f (t, y) - f (z, t) :=
      sub_le_sub_right (candidates_triangle fA) _
    _ ≤ f (x, z) + f (z, t) + f (t, y) - f (z, t) :=
      (sub_le_sub_right (add_le_add_right (candidates_triangle fA) _) _)
    _ = f (x, z) + f (t, y) := by simp [sub_eq_add_neg, add_assoc]
    _ ≤ maxVar X Y * dist x z + maxVar X Y * dist t y :=
      (add_le_add (candidates_dist_bound fA) (candidates_dist_bound fA))
    _ ≤ maxVar X Y * max (dist x z) (dist t y) + maxVar X Y * max (dist x z) (dist t y) :=
      by
      apply add_le_add
      apply
        mul_le_mul_of_nonneg_left (le_max_left (dist x z) (dist t y))
          (zero_le_one.trans (one_le_max_var X Y))
      apply
        mul_le_mul_of_nonneg_left (le_max_right (dist x z) (dist t y))
          (zero_le_one.trans (one_le_max_var X Y))
    _ = 2 * maxVar X Y * max (dist x z) (dist y t) :=
      by
      simp [dist_comm]
      ring
    _ = 2 * maxVar X Y * dist (x, y) (z, t) := by rfl
    
#align Gromov_Hausdorff.candidates_lipschitz_aux Gromov_Hausdorff.candidates_lipschitz_aux

/-- Candidates are Lipschitz -/
private theorem candidates_lipschitz (fA : f ∈ candidates X Y) : LipschitzWith (2 * maxVar X Y) f :=
  by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq, abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA
#align Gromov_Hausdorff.candidates_lipschitz Gromov_Hausdorff.candidates_lipschitz

/-- candidates give rise to elements of bounded_continuous_functions -/
def candidatesBOfCandidates (f : ProdSpaceFun X Y) (fA : f ∈ candidates X Y) : Cb X Y :=
  BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).Continuous⟩
#align Gromov_Hausdorff.candidates_b_of_candidates GromovHausdorff.candidatesBOfCandidates

theorem candidatesBOfCandidates_mem (f : ProdSpaceFun X Y) (fA : f ∈ candidates X Y) :
    candidatesBOfCandidates f fA ∈ candidatesB X Y :=
  fA
#align Gromov_Hausdorff.candidates_b_of_candidates_mem GromovHausdorff.candidatesBOfCandidates_mem

/-- The distance on `X ⊕ Y` is a candidate -/
private theorem dist_mem_candidates :
    (fun p : Sum X Y × Sum X Y => dist p.1 p.2) ∈ candidates X Y :=
  by
  simp only [candidates, dist_comm, forall_const, and_true_iff, add_comm, eq_self_iff_true,
    and_self_iff, Sum.forall, Set.mem_setOf_eq, dist_self]
  repeat'
    first
      |constructor|exact fun a y z =>
        dist_triangle_left _ _ _|exact fun x y => by rfl|exact fun x y => max_var_bound
#align Gromov_Hausdorff.dist_mem_candidates Gromov_Hausdorff.dist_mem_candidates

/-- The distance on `X ⊕ Y` as a candidate -/
def candidatesBDist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Inhabited X]
    [MetricSpace Y] [CompactSpace Y] [Inhabited Y] : Cb X Y :=
  candidatesBOfCandidates _ dist_mem_candidates
#align Gromov_Hausdorff.candidates_b_dist GromovHausdorff.candidatesBDist

theorem candidatesBDist_mem_candidatesB : candidatesBDist X Y ∈ candidatesB X Y :=
  candidatesBOfCandidates_mem _ _
#align Gromov_Hausdorff.candidates_b_dist_mem_candidates_b GromovHausdorff.candidatesBDist_mem_candidatesB

private theorem candidates_b_nonempty : (candidatesB X Y).Nonempty :=
  ⟨_, candidatesBDist_mem_candidatesB⟩
#align Gromov_Hausdorff.candidates_b_nonempty Gromov_Hausdorff.candidates_b_nonempty

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y z) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and
equicontinuous. Equicontinuity follows from the Lipschitz control, we check closedness. -/
private theorem closed_candidates_b : IsClosed (candidatesB X Y) :=
  by
  have I1 : ∀ x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    isClosed_eq continuous_eval_const continuous_const
  have I2 : ∀ x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    isClosed_eq continuous_eval_const continuous_const
  have I3 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) = f (y, x) } := fun x y =>
    isClosed_eq continuous_eval_const continuous_eval_const
  have I4 : ∀ x y z, IsClosed { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) } := fun x y z =>
    isClosed_le continuous_eval_const (continuous_eval_const.add continuous_eval_const)
  have I5 : ∀ x, IsClosed { f : Cb X Y | f (x, x) = 0 } := fun x =>
    isClosed_eq continuous_eval_const continuous_const
  have I6 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) ≤ max_var X Y } := fun x y =>
    isClosed_le continuous_eval_const continuous_const
  have :
    candidates_b X Y =
      (((((⋂ (x) (y), { f : Cb X Y | f (@inl X Y x, @inl X Y y) = dist x y }) ∩
                ⋂ (x) (y), { f : Cb X Y | f (@inr X Y x, @inr X Y y) = dist x y }) ∩
              ⋂ (x) (y), { f : Cb X Y | f (x, y) = f (y, x) }) ∩
            ⋂ (x) (y) (z), { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) }) ∩
          ⋂ x, { f : Cb X Y | f (x, x) = 0 }) ∩
        ⋂ (x) (y), { f : Cb X Y | f (x, y) ≤ max_var X Y } :=
    by
    ext
    simp only [candidates_b, candidates, mem_inter_iff, mem_Inter, mem_set_of_eq]
  rw [this]
  repeat'
    first
      |apply
        IsClosed.inter _
          _|apply
        isClosed_iInter
          _|apply I1 _ _|apply I2 _ _|apply I3 _ _|apply I4 _ _ _|apply I5 _|apply I6 _ _|intro x
#align Gromov_Hausdorff.closed_candidates_b Gromov_Hausdorff.closed_candidates_b

/-- Compactness of candidates (in bounded_continuous_functions) follows. -/
private theorem is_compact_candidates_b : IsCompact (candidatesB X Y) :=
  by
  refine'
    arzela_ascoli₂ (Icc 0 (max_var X Y)) is_compact_Icc (candidates_b X Y) closed_candidates_b _ _
  · rintro f ⟨x1, x2⟩ hf
    simp only [Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_max_var hf⟩
  · refine' equicontinuous_of_continuity_modulus (fun t => 2 * max_var X Y * t) _ _ _
    · have : tendsto (fun t : ℝ => 2 * (max_var X Y : ℝ) * t) (𝓝 0) (𝓝 (2 * max_var X Y * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this
    · rintro x y ⟨f, hf⟩
      exact (candidates_lipschitz hf).dist_le_mul _ _
#align Gromov_Hausdorff.is_compact_candidates_b Gromov_Hausdorff.is_compact_candidates_b

/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def hD (f : Cb X Y) :=
  max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))
#align Gromov_Hausdorff.HD GromovHausdorff.hD

/- We will show that HD is continuous on bounded_continuous_functions, to deduce that its
minimum on the compact set candidates_b is attained. Since it is defined in terms of
infimum and supremum on `ℝ`, which is only conditionnally complete, we will need all the time
to check that the defining sets are bounded below or above. This is done in the next few
technical lemmas -/
theorem HD_below_aux1 {f : Cb X Y} (C : ℝ) {x : X} :
    BddBelow (range fun y : Y => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).1
  ⟨cf + C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩
#align Gromov_Hausdorff.HD_below_aux1 GromovHausdorff.HD_below_aux1

private theorem HD_bound_aux1 (f : Cb X Y) (C : ℝ) :
    BddAbove (range fun x : X => ⨅ y, f (inl x, inr y) + C) :=
  by
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).2 with ⟨Cf, hCf⟩
  refine' ⟨Cf + C, forall_range_iff.2 fun x => _⟩
  calc
    (⨅ y, f (inl x, inr y) + C) ≤ f (inl x, inr default) + C := ciInf_le (HD_below_aux1 C) default
    _ ≤ Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
    
#align Gromov_Hausdorff.HD_bound_aux1 Gromov_Hausdorff.HD_bound_aux1

theorem HD_below_aux2 {f : Cb X Y} (C : ℝ) {y : Y} :
    BddBelow (range fun x : X => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).1
  ⟨cf + C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩
#align Gromov_Hausdorff.HD_below_aux2 GromovHausdorff.HD_below_aux2

private theorem HD_bound_aux2 (f : Cb X Y) (C : ℝ) :
    BddAbove (range fun y : Y => ⨅ x, f (inl x, inr y) + C) :=
  by
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).2 with ⟨Cf, hCf⟩
  refine' ⟨Cf + C, forall_range_iff.2 fun y => _⟩
  calc
    (⨅ x, f (inl x, inr y) + C) ≤ f (inl default, inr y) + C := ciInf_le (HD_below_aux2 C) default
    _ ≤ Cf + C := add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl
    
#align Gromov_Hausdorff.HD_bound_aux2 Gromov_Hausdorff.HD_bound_aux2

/-- Explicit bound on `HD (dist)`. This means that when looking for minimizers it will
be sufficient to look for functions with `HD(f)` bounded by this bound. -/
theorem hD_candidatesBDist_le :
    hD (candidatesBDist X Y) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
  by
  refine' max_le (ciSup_le fun x => _) (ciSup_le fun y => _)
  · have A :
      (⨅ y, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl x, inr default) :=
      ciInf_le (by simpa using HD_below_aux1 0) default
    have B : dist (inl x) (inr default) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl x) (inr (default : Y)) = dist x (default : X) + 1 + dist default default := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
          by
          apply add_le_add (add_le_add _ le_rfl)
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          any_goals exact OrderedAddCommMonoid.to_covariantClass_left ℝ
          any_goals exact OrderedAddCommMonoid.to_covariantClass_right ℝ
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
        
    exact le_trans A B
  · have A :
      (⨅ x, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl default, inr y) :=
      ciInf_le (by simpa using HD_below_aux2 0) default
    have B : dist (inl default) (inr y) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl (default : X)) (inr y) = dist default default + 1 + dist default y := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
          by
          apply add_le_add (add_le_add _ le_rfl)
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          any_goals exact OrderedAddCommMonoid.to_covariantClass_left ℝ
          any_goals exact OrderedAddCommMonoid.to_covariantClass_right ℝ
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
        
    exact le_trans A B
#align Gromov_Hausdorff.HD_candidates_b_dist_le GromovHausdorff.hD_candidatesBDist_le

/- To check that HD is continuous, we check that it is Lipschitz. As HD is a max, we
prove separately inequalities controlling the two terms (relying too heavily on copy-paste...) -/
private theorem HD_lipschitz_aux1 (f g : Cb X Y) :
    (⨆ x, ⨅ y, f (inl x, inr y)) ≤ (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g :=
  by
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 g.bounded_range).1 with ⟨cg, hcg⟩
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).1 with ⟨cf, hcf⟩
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ x, ⨅ y, f (inl x, inr y)) ≤ ⨆ x, ⨅ y, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux1 _ (dist f g)) fun x =>
      ciInf_mono ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ x, (⨅ y, g (inl x, inr y)) + dist f g = ⨅ y, g (inl x, inr y) + dist f g :=
    by
    intro x
    refine' Monotone.map_ciInf_of_continuousAt (continuous_at_id.add continuousAt_const) _ _
    · intro x y hx
      simpa
    · show BddBelow (range fun y : Y => g (inl x, inr y))
      exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
  have E2 : (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g = ⨆ x, (⨅ y, g (inl x, inr y)) + dist f g :=
    by
    refine' Monotone.map_ciSup_of_continuousAt (continuous_at_id.add continuousAt_const) _ _
    · intro x y hx
      simpa
    · simpa using HD_bound_aux1 _ 0
  -- deduce the result from the above two steps
  simpa [E2, E1, Function.comp]
#align Gromov_Hausdorff.HD_lipschitz_aux1 Gromov_Hausdorff.HD_lipschitz_aux1

private theorem HD_lipschitz_aux2 (f g : Cb X Y) :
    (⨆ y, ⨅ x, f (inl x, inr y)) ≤ (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g :=
  by
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 g.bounded_range).1 with ⟨cg, hcg⟩
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  rcases(Real.bounded_iff_bddBelow_bddAbove.1 f.bounded_range).1 with ⟨cf, hcf⟩
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ y, ⨅ x, f (inl x, inr y)) ≤ ⨆ y, ⨅ x, g (inl x, inr y) + dist f g :=
    ciSup_mono (HD_bound_aux2 _ (dist f g)) fun y =>
      ciInf_mono ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ y, (⨅ x, g (inl x, inr y)) + dist f g = ⨅ x, g (inl x, inr y) + dist f g :=
    by
    intro y
    refine' Monotone.map_ciInf_of_continuousAt (continuous_at_id.add continuousAt_const) _ _
    · intro x y hx
      simpa
    · show BddBelow (range fun x : X => g (inl x, inr y))
      exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
  have E2 : (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g = ⨆ y, (⨅ x, g (inl x, inr y)) + dist f g :=
    by
    refine' Monotone.map_ciSup_of_continuousAt (continuous_at_id.add continuousAt_const) _ _
    · intro x y hx
      simpa
    · simpa using HD_bound_aux2 _ 0
  -- deduce the result from the above two steps
  simpa [E2, E1]
#align Gromov_Hausdorff.HD_lipschitz_aux2 Gromov_Hausdorff.HD_lipschitz_aux2

private theorem HD_lipschitz_aux3 (f g : Cb X Y) : hD f ≤ hD g + dist f g :=
  max_le (le_trans (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_left _ _) _))
    (le_trans (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_right _ _) _))
#align Gromov_Hausdorff.HD_lipschitz_aux3 Gromov_Hausdorff.HD_lipschitz_aux3

/-- Conclude that HD, being Lipschitz, is continuous -/
private theorem HD_continuous : Continuous (hD : Cb X Y → ℝ) :=
  LipschitzWith.continuous (LipschitzWith.of_le_add hD_lipschitz_aux3)
#align Gromov_Hausdorff.HD_continuous Gromov_Hausdorff.HD_continuous

end Constructions

--section
section Consequences

variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

/- Now that we have proved that the set of candidates is compact, and that HD is continuous,
we can finally select a candidate minimizing HD. This will be the candidate realizing the
optimal coupling. -/
private theorem exists_minimizer : ∃ f ∈ candidatesB X Y, ∀ g ∈ candidatesB X Y, hD f ≤ hD g :=
  isCompact_candidatesB.exists_forall_le candidatesB_nonempty hD_continuous.ContinuousOn
#align Gromov_Hausdorff.exists_minimizer Gromov_Hausdorff.exists_minimizer

private def optimal_GH_dist : Cb X Y :=
  Classical.choose (exists_minimizer X Y)
#align Gromov_Hausdorff.optimal_GH_dist Gromov_Hausdorff.optimal_GH_dist

private theorem optimal_GH_dist_mem_candidates_b : optimalGHDist X Y ∈ candidatesB X Y := by
  cases Classical.choose_spec (exists_minimizer X Y) <;> assumption
#align Gromov_Hausdorff.optimal_GH_dist_mem_candidates_b Gromov_Hausdorff.optimal_GH_dist_mem_candidates_b

private theorem HD_optimal_GH_dist_le (g : Cb X Y) (hg : g ∈ candidatesB X Y) :
    hD (optimalGHDist X Y) ≤ hD g :=
  let ⟨Z1, Z2⟩ := Classical.choose_spec (exists_minimizer X Y)
  Z2 g hg
#align Gromov_Hausdorff.HD_optimal_GH_dist_le Gromov_Hausdorff.HD_optimal_GH_dist_le

/-- With the optimal candidate, construct a premetric space structure on `X ⊕ Y`, on which the
predistance is given by the candidate. Then, we will identify points at `0` predistance
to obtain a genuine metric space -/
def premetricOptimalGHDist : PseudoMetricSpace (Sum X Y)
    where
  dist p q := optimalGHDist X Y (p, q)
  dist_self x := candidates_refl (optimalGHDist_mem_candidatesB X Y)
  dist_comm x y := candidates_symm (optimalGHDist_mem_candidatesB X Y)
  dist_triangle x y z := candidates_triangle (optimalGHDist_mem_candidatesB X Y)
#align Gromov_Hausdorff.premetric_optimal_GH_dist GromovHausdorff.premetricOptimalGHDist

attribute [local instance] premetric_optimal_GH_dist

/-- A metric space which realizes the optimal coupling between `X` and `Y` -/
@[nolint has_nonempty_instance]
def OptimalGHCoupling : Type _ :=
  @UniformSpace.SeparationQuotient (Sum X Y) (premetricOptimalGHDist X Y).toUniformSpace deriving
  MetricSpace
#align Gromov_Hausdorff.optimal_GH_coupling GromovHausdorff.OptimalGHCoupling

/-- Injection of `X` in the optimal coupling between `X` and `Y` -/
def optimalGHInjl (x : X) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inl x)
#align Gromov_Hausdorff.optimal_GH_injl GromovHausdorff.optimalGHInjl

/-- The injection of `X` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimalGHInjl : Isometry (optimalGHInjl X Y) :=
  Isometry.of_dist_eq fun x y => candidates_dist_inl (optimalGHDist_mem_candidatesB X Y) _ _
#align Gromov_Hausdorff.isometry_optimal_GH_injl GromovHausdorff.isometry_optimalGHInjl

/-- Injection of `Y` in the optimal coupling between `X` and `Y` -/
def optimalGHInjr (y : Y) : OptimalGHCoupling X Y :=
  Quotient.mk'' (inr y)
#align Gromov_Hausdorff.optimal_GH_injr GromovHausdorff.optimalGHInjr

/-- The injection of `Y` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimalGHInjr : Isometry (optimalGHInjr X Y) :=
  Isometry.of_dist_eq fun x y => candidates_dist_inr (optimalGHDist_mem_candidatesB X Y) _ _
#align Gromov_Hausdorff.isometry_optimal_GH_injr GromovHausdorff.isometry_optimalGHInjr

/-- The optimal coupling between two compact spaces `X` and `Y` is still a compact space -/
instance compactSpace_optimalGHCoupling : CompactSpace (OptimalGHCoupling X Y) :=
  ⟨by
    rw [← range_quotient_mk']
    exact
      isCompact_range
        (continuous_sum_dom.2
          ⟨(isometry_optimal_GH_injl X Y).Continuous, (isometry_optimal_GH_injr X Y).Continuous⟩)⟩
#align Gromov_Hausdorff.compact_space_optimal_GH_coupling GromovHausdorff.compactSpace_optimalGHCoupling

/-- For any candidate `f`, `HD(f)` is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
theorem hausdorffDist_optimal_le_hD {f} (h : f ∈ candidatesB X Y) :
    hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤ hD f :=
  by
  refine' le_trans (le_of_forall_le_of_dense fun r hr => _) (HD_optimal_GH_dist_le X Y f h)
  have A : ∀ x ∈ range (optimal_GH_injl X Y), ∃ y ∈ range (optimal_GH_injr X Y), dist x y ≤ r :=
    by
    rintro _ ⟨z, rfl⟩
    have I1 : (⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_left _ _) hr
    have I2 :
      (⨅ y, optimal_GH_dist X Y (inl z, inr y)) ≤ ⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux1 _ 0) (mem_range_self _)
    have I : (⨅ y, optimal_GH_dist X Y (inl z, inr y)) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    exact ⟨optimal_GH_injr X Y z', mem_range_self _, le_of_lt hr'⟩
  refine' Hausdorff_dist_le_of_mem_dist _ A _
  · inhabit X
    rcases A _ (mem_range_self default) with ⟨y, -, hy⟩
    exact le_trans dist_nonneg hy
  · rintro _ ⟨z, rfl⟩
    have I1 : (⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y)) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    have I2 :
      (⨅ x, optimal_GH_dist X Y (inl x, inr z)) ≤ ⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y) :=
      le_csSup (by simpa using HD_bound_aux2 _ 0) (mem_range_self _)
    have I : (⨅ x, optimal_GH_dist X Y (inl x, inr z)) < r := lt_of_le_of_lt I2 I1
    rcases exists_lt_of_csInf_lt (range_nonempty _) I with ⟨r', ⟨z', rfl⟩, hr'⟩
    refine' ⟨optimal_GH_injl X Y z', mem_range_self _, le_of_lt _⟩
    rwa [dist_comm]
#align Gromov_Hausdorff.Hausdorff_dist_optimal_le_HD GromovHausdorff.hausdorffDist_optimal_le_hD

end Consequences

-- We are done with the construction of the optimal coupling
end GromovHausdorffRealized

end GromovHausdorff

