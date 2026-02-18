/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Incenter

/-!
# IMO 2024 Q4

Let `ABC` be a triangle with `AB < AC < BC`. Let the incentre and incircle of triangle `ABC` be
`I` and `ω`, respectively. Let `X` be the point on line `BC` different from `C` such that the
line through `X` parallel to `AC` is tangent to `ω`. Similarly, let `Y` be the point on line `BC`
different from `B` such that the line through `Y` parallel to `AB` is tangent to `ω`. Let `AI`
intersect the circumcircle of triangle `ABC` again at `P ≠ A`. Let `K` and `L` be the midpoints
of `AC` and `AB`, respectively.

Prove that `∠KIL + ∠YPX = 180°`.

We follow Solution 1 from the
[official solutions](https://www.imo2024.uk/s/IMO2024-solutions-updated.pdf), but work as much as
possible with oriented angles during the solution to limit the number of places where the argument
requires verifying that two angles have the same sign. We define `A'` to be the reflection of `A`
in `I`, or equivalently the image of `I` under a homothety at `A` with scale factor 2. By angle
chasing we show that `BPA'X` and `CYA'P` are cyclic. We then relate `∠KIL + ∠YPX` to the sum of
angles in triangle `A'CB`: the homothety gives `∠KIL = ∠CA'B`, while further angle chasing gives
`∠APX = ∠A'BC` and `∠YPA = ∠BCA'`.
-/

noncomputable section

open scoped Real
open Affine EuclideanGeometry Module


attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

namespace Imo2024Q4

/-- A configuration satisfying the conditions of the problem, but with weaker more symmetric
conditions on the side lengths to reduce duplication in the solution. -/
structure Imo2024q4Cfg where
  (A B C I X Y P K L : Pt)
  ω : Sphere Pt
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  AB_lt_BC : dist A B < dist B C
  AC_lt_BC : dist A C < dist B C
  incenter_eq_I : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).incenter = I
  incircle_eq_ω : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).insphere = ω
  X_mem_BC : X ∈ line[ℝ, B, C]
  X_ne_C : X ≠ C
  isTangent_mk'_X_parallel_AC : ω.IsTangent (AffineSubspace.mk' X line[ℝ, A, C].direction)
  Y_mem_BC : Y ∈ line[ℝ, B, C]
  Y_ne_B : Y ≠ B
  isTangent_mk'_Y_parallel_AB : ω.IsTangent (AffineSubspace.mk' Y line[ℝ, A, B].direction)
  P_mem_inter :
    P ∈ (line[ℝ, A, I] ∩ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere : Set Pt)
  P_ne_A : P ≠ A
  K_eq_midpoint_AC : K = midpoint ℝ A C
  L_eq_midpoint_AB : L = midpoint ℝ A B

/-- A default choice of orientation, for lemmas that need to pick one. -/
def someOrientation [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

variable {V Pt}

namespace Imo2024q4Cfg

variable (cfg : Imo2024q4Cfg V Pt)

/-- The configuration with `B` and `C` swapped. -/
def symm : Imo2024q4Cfg V Pt where
  A := cfg.A
  B := cfg.C
  C := cfg.B
  I := cfg.I
  X := cfg.Y
  Y := cfg.X
  P := cfg.P
  K := cfg.L
  L := cfg.K
  ω := cfg.ω
  affineIndependent_ABC := cfg.affineIndependent_ABC.comm_right
  AB_lt_BC := by
    convert cfg.AC_lt_BC using 1
    rw [dist_comm]
  AC_lt_BC := by
    convert cfg.AB_lt_BC using 1
    rw [dist_comm]
  incenter_eq_I := by
    convert cfg.incenter_eq_I using 1
    rw [← Affine.Simplex.incenter_reindex (e := (Equiv.swap (1 : Fin 3) 2))]
    convert rfl
    ext i
    fin_cases i <;> rfl
  incircle_eq_ω := by
    convert cfg.incircle_eq_ω using 1
    rw [← Affine.Simplex.insphere_reindex (e := (Equiv.swap (1 : Fin 3) 2))]
    convert rfl
    ext i
    fin_cases i <;> rfl
  X_mem_BC := by
    convert cfg.Y_mem_BC using 2
    grind
  X_ne_C := cfg.Y_ne_B
  isTangent_mk'_X_parallel_AC := cfg.isTangent_mk'_Y_parallel_AB
  Y_mem_BC := by
    convert cfg.X_mem_BC using 2
    grind
  Y_ne_B := cfg.X_ne_C
  isTangent_mk'_Y_parallel_AB := cfg.isTangent_mk'_X_parallel_AC
  P_mem_inter := by
    convert cfg.P_mem_inter using 2
    rw [← Affine.Simplex.circumsphere_reindex (e := (Equiv.swap (1 : Fin 3) 2))]
    convert rfl <;> ext i <;> fin_cases i <;> rfl
  P_ne_A := cfg.P_ne_A
  K_eq_midpoint_AC := cfg.L_eq_midpoint_AB
  L_eq_midpoint_AB := cfg.K_eq_midpoint_AC

/-- `ABC` as a `Triangle`. -/
def triangleABC : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_ABC⟩

/-- `A'` is the reflection of `A` in `I` (or various other equivalent descriptions). -/
def A' : Pt := AffineEquiv.pointReflection ℝ cfg.I cfg.A

lemma A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

lemma A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

lemma B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

lemma A_notMem_BC : cfg.A ∉ line[ℝ, cfg.B, cfg.C] := by
  intro h
  have h' := collinear_insert_of_mem_affineSpan_pair h
  rw [collinear_iff_not_affineIndependent_set] at h'
  exact h' cfg.triangleABC.independent

lemma A_mem_circumsphere : cfg.A ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 0

lemma B_mem_circumsphere : cfg.B ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 1

lemma C_mem_circumsphere : cfg.C ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 2

lemma P_mem_circumsphere : cfg.P ∈ cfg.triangleABC.circumsphere := cfg.P_mem_inter.2

lemma ω_eq_insphere : cfg.ω = cfg.triangleABC.insphere := cfg.incircle_eq_ω.symm

lemma collinear_XBC : Collinear ℝ {cfg.X, cfg.B, cfg.C} :=
  collinear_insert_of_mem_affineSpan_pair cfg.X_mem_BC

lemma collinear_CXB : Collinear ℝ {cfg.C, cfg.X, cfg.B} := by
  convert cfg.collinear_XBC using 1
  grind

lemma A'_mem_AI : cfg.A' ∈ line[ℝ, cfg.A, cfg.I] := by
  rw [A']
  convert AffineMap.lineMap_mem_affineSpan_pair (2 : ℝ) _ _
  simp [Equiv.pointReflection_apply, AffineMap.lineMap_apply, two_smul, add_vadd]

lemma A'_eq_homothety_A_2_I : cfg.A' = AffineMap.homothety cfg.A (2 : ℝ) cfg.I := by
  simp [A', AffineMap.homothety_apply, Equiv.pointReflection_apply, two_smul, add_vadd]

set_option backward.isDefEq.respectTransparency false in
lemma B_eq_homothety_A_2_L : cfg.B = AffineMap.homothety cfg.A (2 : ℝ) cfg.L := by
  simp [L_eq_midpoint_AB, midpoint, AffineMap.lineMap_apply]

lemma C_eq_homothety_A_2_K : cfg.C = AffineMap.homothety cfg.A (2 : ℝ) cfg.K :=
  cfg.symm.B_eq_homothety_A_2_L

lemma CB_eq_affineSpan_faceOpposite : line[ℝ, cfg.C, cfg.B] =
    affineSpan ℝ (Set.range (cfg.triangleABC.faceOpposite 0).points) := by
  congr
  have h0 : ({0}ᶜ : Set (Fin 3)) = {2, 1} := by ext i; fin_cases i <;> grind
  simp [Affine.Simplex.range_faceOpposite_points, h0, Set.image_insert_eq, triangleABC]

lemma sOppSide_CB_A_A' : line[ℝ, cfg.C, cfg.B].SOppSide cfg.A cfg.A' := by
  have hA :
    Finset.univ.affineCombination ℝ cfg.triangleABC.points
      (Finset.affineCombinationSingleWeights ℝ 0) = cfg.A :=
    Finset.affineCombination_affineCombinationSingleWeights _ _ _ (Finset.mem_univ 0)
  rw [A', ← hA, ← incenter_eq_I, Simplex.incenter_eq_affineCombination,
    AffineEquiv.pointReflection_apply, ← triangleABC, Finset.affineCombination_vsub,
    Finset.weightedVSub_vadd_affineCombination, cfg.CB_eq_affineSpan_faceOpposite]
  refine cfg.triangleABC.sOppSide_affineSpan_faceOpposite_of_pos_of_neg
    (Finset.sum_affineCombinationSingleWeights _ _ (Finset.mem_univ 0)) ?_ (by simp) ?_
  · simp [Finset.sum_add_distrib, cfg.triangleABC.excenterExists_empty.sum_excenterWeights_eq_one]
  · simp only [Pi.add_apply, Pi.sub_apply, Finset.affineCombinationSingleWeights_apply_self]
    linarith [cfg.triangleABC.excenterWeights_empty_lt_inv_two 0]

lemma P_eq_secondInter :
    cfg.P = cfg.triangleABC.circumsphere.secondInter cfg.A (cfg.I -ᵥ cfg.A) := by
  simpa [cfg.P_ne_A, cfg.P_mem_circumsphere] using
    cfg.triangleABC.circumsphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
      cfg.A_mem_circumsphere cfg.P_mem_inter.1

lemma sOppSide_CB_A_P : line[ℝ, cfg.C, cfg.B].SOppSide cfg.A cfg.P := by
  rw [P_eq_secondInter]
  convert cfg.triangleABC.circumsphere.sOppSide_faceOpposite_secondInter_of_mem_interior
    (sx := cfg.triangleABC) (i := 0) cfg.A_mem_circumsphere
    (fun j ↦ (cfg.triangleABC.dist_circumcenter_eq_circumradius j).le)
    cfg.triangleABC.incenter_mem_interior using 1
  · exact cfg.CB_eq_affineSpan_faceOpposite
  · convert rfl
    exact cfg.incenter_eq_I

lemma K_ne_I : cfg.K ≠ cfg.I := by
  have hI : cfg.I ∉ line[ℝ, cfg.A, cfg.C] := by
    rw [← cfg.incenter_eq_I]
    exact cfg.triangleABC.incenter_notMem_affineSpan_pair 0 2
  intro h
  rw [← h, K_eq_midpoint_AC, midpoint] at hI
  exact hI (AffineMap.lineMap_mem_affineSpan_pair _ _ _)

lemma L_ne_I : cfg.L ≠ cfg.I := cfg.symm.K_ne_I

lemma sbtw_A_I_P : Sbtw ℝ cfg.A cfg.I cfg.P := by
  rw [P_eq_secondInter, ← incenter_eq_I]
  exact cfg.triangleABC.circumsphere.sbtw_secondInter cfg.A_mem_circumsphere
    (cfg.triangleABC.dist_lt_of_mem_interior_of_strictConvexSpace
      cfg.triangleABC.incenter_mem_interior fun i ↦
        (cfg.triangleABC.dist_circumcenter_eq_circumradius _).le)

lemma PB_eq_PI : dist cfg.P cfg.B = dist cfg.P cfg.I := by
  rw [P_eq_secondInter, ← incenter_eq_I]
  exact cfg.triangleABC.dist_secondInter_point_eq_dist_secondInter_incenter (i₁ := 0) (i₂ := 1)
    (by decide)

lemma X_ne_A' : cfg.X ≠ cfg.A' :=
  fun h ↦ (h ▸ cfg.sOppSide_CB_A_A'.right_notMem) (Set.pair_comm _ _ ▸ cfg.X_mem_BC)

lemma line_BC_eq_line_CX : line[ℝ, cfg.B, cfg.C] = line[ℝ, cfg.C, cfg.X] := by
  rw [Set.pair_comm, eq_comm]
  exact affineSpan_pair_eq_of_right_mem_of_ne (Set.pair_comm _ _ ▸ cfg.X_mem_BC) cfg.X_ne_C

lemma cospherical_APCB : Cospherical ({cfg.A, cfg.P, cfg.C, cfg.B} : Set Pt) := by
  rw [cospherical_iff_exists_sphere]
  refine ⟨cfg.triangleABC.circumsphere, ?_⟩
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Metric.mem_sphere, ← mem_sphere]
  exact ⟨cfg.A_mem_circumsphere, cfg.P_mem_inter.2, cfg.C_mem_circumsphere, cfg.B_mem_circumsphere⟩

lemma P_ne_B : cfg.P ≠ cfg.B := by
  intro h
  apply cfg.sOppSide_CB_A_P.right_notMem
  rw [h]
  exact right_mem_affineSpan_pair _ _ _

lemma P_ne_C : cfg.P ≠ cfg.C := cfg.symm.P_ne_B

lemma B_notMem_AI : cfg.B ∉ line[ℝ, cfg.A, cfg.I] := by
  intro hB
  have hB' := ((cfg.triangleABC.circumsphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
    cfg.A_mem_circumsphere hB).2 cfg.B_mem_circumsphere).resolve_left cfg.A_ne_B.symm
  rw [← P_eq_secondInter, eq_comm] at hB'
  exact cfg.P_ne_B hB'

lemma X_ne_P : cfg.X ≠ cfg.P := by
  intro h
  have hl : cfg.P ∈ line[ℝ, cfg.B, cfg.C] := h ▸ cfg.X_mem_BC
  have hc := collinear_insert_of_mem_affineSpan_pair hl
  rw [collinear_iff_not_affineIndependent_set] at hc
  exact hc <| cfg.cospherical_APCB.affineIndependent_of_mem_of_ne (by grind) (by grind) (by grind)
    cfg.P_ne_B cfg.P_ne_C cfg.B_ne_C

lemma Y_ne_P : cfg.Y ≠ cfg.P := cfg.symm.X_ne_P

lemma B_ne_A' : cfg.B ≠ cfg.A' := by
  intro h
  apply cfg.B_notMem_AI
  rw [h]
  exact cfg.A'_mem_AI

lemma C_ne_A' : cfg.C ≠ cfg.A' := cfg.symm.B_ne_A'

lemma PAB_eq_BAC_div_two : ∠ cfg.P cfg.A cfg.B = ∠ cfg.B cfg.A cfg.C / 2 := by
  rw [angle_comm, ← angle_eq_angle_of_angle_eq_pi _ cfg.sbtw_A_I_P.angle₁₂₃_eq_pi,
    ← cfg.incenter_eq_I]
  exact cfg.triangleABC.angle_incenter_eq_angle_div_two (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide)
    (by decide) (by decide)

lemma ACB_lt_BAC : ∠ cfg.A cfg.C cfg.B < ∠ cfg.B cfg.A cfg.C := by
  rw [angle_comm, angle_lt_iff_dist_lt, dist_comm]
  · exact cfg.AB_lt_BC
  · rw [Set.insert_comm, ←affineIndependent_iff_not_collinear_set]
    exact cfg.affineIndependent_ABC

lemma CBA_lt_BAC : ∠ cfg.C cfg.B cfg.A < ∠ cfg.B cfg.A cfg.C := by
  nth_rw 2 [angle_comm]
  rw [angle_lt_iff_dist_lt, dist_comm cfg.C, dist_comm cfg.C]
  · exact cfg.AC_lt_BC
  · have hi := cfg.affineIndependent_ABC
    rw [affineIndependent_iff_not_collinear_set] at hi
    convert hi using 2
    grind

lemma pi_div_three_lt_BAC : π / 3 < ∠ cfg.B cfg.A cfg.C :=
  pi_div_three_lt_angle_of_le_of_le_of_ne cfg.ACB_lt_BAC.le cfg.CBA_lt_BAC.le
    (.inr (.inl cfg.CBA_lt_BAC.ne'))

lemma pi_div_six_lt_PAB : π / 6 < ∠ cfg.P cfg.A cfg.B := by
  rw [PAB_eq_BAC_div_two, lt_div_iff₀ (by norm_num)]
  convert cfg.pi_div_three_lt_BAC using 1
  ring

variable [hf2 : Fact (finrank ℝ V = 2)]

lemma circumradius_lt_PB : cfg.triangleABC.circumradius < dist cfg.P cfg.B := by
  have hc : Cospherical {cfg.A, cfg.B, cfg.C, cfg.P} := by
    refine ⟨cfg.triangleABC.circumcenter, cfg.triangleABC.circumradius, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, triangleABC, forall_eq_or_imp,
      forall_eq]
    exact ⟨cfg.A_mem_circumsphere, cfg.B_mem_circumsphere, cfg.C_mem_circumsphere,
      cfg.P_mem_circumsphere⟩
  have hi : AffineIndependent ℝ ![cfg.A, cfg.B, cfg.P] :=
    hc.affineIndependent_of_mem_of_ne (by grind) (by grind) (by grind) cfg.A_ne_B cfg.P_ne_A.symm
      cfg.P_ne_B.symm
  let ABP : Triangle ℝ Pt := ⟨_, hi⟩
  have hr : cfg.triangleABC.circumradius = ABP.circumradius := by
    refine circumradius_eq_of_cospherical hf2.out hc ?_ ?_
    · simp [triangleABC]
      grind
    · simp [ABP]
      grind
  rw [hr, ← ABP.dist_div_sin_angle_div_two_eq_circumradius (i₁ := 2) (i₂ := 0) (i₃ := 1)
        (by decide) (by decide) (by decide)]
  simp only [Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, ABP]
  rw [div_lt_iff₀ (by norm_num)]
  have hnc : ¬Collinear ℝ {cfg.P, cfg.A, cfg.B} := by
    rw [affineIndependent_iff_not_collinear_set] at hi
    convert hi using 2
    grind
  rw [div_lt_iff₀ (Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear hnc)
    (angle_lt_pi_of_not_collinear hnc)), mul_assoc]
  refine lt_mul_right (dist_pos.2 cfg.P_ne_B) ?_
  rw [← div_lt_iff₀' (by norm_num)]
  convert Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := π / 6) (by linarith [Real.pi_pos]) ?_
    cfg.pi_div_six_lt_PAB using 1
  · simp
  · rw [le_div_iff₀ (by norm_num), PAB_eq_BAC_div_two]
    simp [angle_le_pi]

lemma AI_lt_PI : dist cfg.A cfg.I < dist cfg.P cfg.I := by
  have hd := cfg.sbtw_A_I_P.wbtw.dist_add_dist
  rw [dist_comm cfg.I] at hd
  have hr : cfg.triangleABC.circumradius < dist cfg.P cfg.I := cfg.PB_eq_PI ▸ cfg.circumradius_lt_PB
  have h2 : dist cfg.A cfg.P ≤ 2 * cfg.triangleABC.circumradius := by
    rw [two_mul]
    nth_rw 1 [← cfg.triangleABC.dist_circumcenter_eq_circumradius 0]
    rw [Simplex.circumradius, ← mem_sphere'.1 cfg.P_mem_circumsphere]
    exact dist_triangle _ _ _
  linarith

lemma sbtw_A_A'_P : Sbtw ℝ cfg.A cfg.A' cfg.P := by
  have hs := cfg.sbtw_A_I_P
  rw [sbtw_iff_left_ne_and_right_mem_image_Ioi] at hs
  obtain ⟨hAI, r, hr, hP⟩ := hs
  suffices 2 < r by
    have hP' : cfg.P = AffineMap.lineMap cfg.A cfg.A' (r / 2) := by
      rw [← hP, A']
      simp [AffineMap.lineMap_apply, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [sbtw_iff_right_ne_and_left_mem_image_Ioi, hP', A']
    have hn : cfg.A ≠ (cfg.I -ᵥ cfg.A) +ᵥ cfg.I := by
      rw [← vsub_ne_zero, vsub_vadd_eq_vsub_sub, sub_eq_add_neg, neg_vsub_eq_vsub_rev, ← two_smul ℝ,
        ← incenter_eq_I]
      simpa using (cfg.triangleABC.incenter_ne_point 0).symm
    simp only [AffineEquiv.pointReflection_apply_eq_equivPointReflection_apply,
      Equiv.pointReflection_apply, ne_eq, AffineMap.lineMap_eq_right_iff, hn, false_or,
      AffineMap.lineMap_lineMap_left, AffineMap.lineMap_apply_one_sub, Set.mem_image, Set.mem_Ioi,
      hn.symm]
    refine ⟨by linarith, 1 - (1 - r / 2)⁻¹, ?_, by grind⟩
    rw [← sub_pos, sub_sub_cancel_left, Left.neg_pos_iff, inv_neg'']
    linarith
  have hAI := cfg.AI_lt_PI
  rw [← hP, dist_lineMap_right] at hAI
  simp_all only [ne_eq, Set.mem_Ioi, Real.norm_eq_abs, dist_pos, not_false_eq_true,
    lt_mul_iff_one_lt_left, gt_iff_lt]
  rw [abs_eq_neg_self.2 (by grind)] at hAI
  grind

lemma P_ne_A' : cfg.P ≠ cfg.A' := cfg.sbtw_A_A'_P.right_ne

lemma not_collinear_A'PB : ¬Collinear ℝ {cfg.A', cfg.P, cfg.B} := by
  intro h
  have hB : cfg.B ∈ line[ℝ, cfg.P, cfg.A'] :=
    h.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) cfg.P_ne_A'
  rw [affineSpan_pair_eq_of_mem_of_mem_of_ne cfg.P_mem_inter.1 cfg.A'_mem_AI cfg.P_ne_A'] at hB
  exact cfg.B_notMem_AI hB

lemma B_ne_X : cfg.B ≠ cfg.X := by
  intro h
  have ht : cfg.ω.tangentsFrom cfg.X = {line[ℝ, cfg.B, cfg.A], line[ℝ, cfg.B, cfg.C]} := by
    rw [ω_eq_insphere, ← h]
    exact cfg.triangleABC.tangentsFrom_insphere_eq_pair_affineSpan_pair (i₁ := 1) (i₂ := 0)
      (i₃ := 2) (by decide) (by decide) (by decide)
  have hX : AffineSubspace.mk' cfg.X line[ℝ, cfg.A, cfg.C].direction ∈
      cfg.ω.tangentsFrom cfg.X := by
    refine ⟨?_, AffineSubspace.self_mem_mk' _ _⟩
    rw [cfg.ω.mem_tangentSet_iff]
    obtain ⟨Q, hQ⟩ := cfg.isTangent_mk'_X_parallel_AC
    refine ⟨Q, hQ.mem_sphere, (hQ.eq_orthRadius_of_finrank_add_one_eq ?_ ?_).symm⟩
    · rw [ω_eq_insphere]
      exact cfg.triangleABC.inradius_pos.ne'
    · rw [AffineSubspace.direction_mk', direction_affineSpan, vectorSpan_pair, hf2.out,
        finrank_span_singleton (vsub_ne_zero.2 cfg.A_ne_C)]
  rw [ht, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with hX | hX <;> apply_fun AffineSubspace.direction at hX <;>
      simp_rw [AffineSubspace.direction_mk', direction_affineSpan] at hX
  · change vectorSpan ℝ {cfg.triangleABC.points 0, cfg.triangleABC.points 2} =
      vectorSpan ℝ {cfg.triangleABC.points 1, cfg.triangleABC.points 0} at hX
    rw [← Set.image_pair, ← Set.image_pair,
      cfg.triangleABC.independent.vectorSpan_image_eq_iff] at hX
    simp [Set.Subsingleton, Set.pair_eq_pair_iff] at hX
  · change vectorSpan ℝ {cfg.triangleABC.points 0, cfg.triangleABC.points 2} =
      vectorSpan ℝ {cfg.triangleABC.points 1, cfg.triangleABC.points 2} at hX
    rw [← Set.image_pair, ← Set.image_pair,
      cfg.triangleABC.independent.vectorSpan_image_eq_iff] at hX
    simp [Set.Subsingleton, Set.pair_eq_pair_iff] at hX

lemma A'X_eq_mk' :
    line[ℝ, cfg.A', cfg.X] = AffineSubspace.mk' cfg.X line[ℝ, cfg.A, cfg.C].direction := by
  have hX : cfg.X ∈ AffineSubspace.mk' cfg.X line[ℝ, cfg.A, cfg.C].direction :=
    AffineSubspace.self_mem_mk' _ _
  have hmap : AffineSubspace.mk' cfg.X line[ℝ, cfg.A, cfg.C].direction =
      line[ℝ, cfg.A, cfg.C].map (AffineEquiv.pointReflection ℝ cfg.I).toAffineMap := by
    have hAC : line[ℝ, cfg.A, cfg.C] =
      cfg.triangleABC.insphere.orthRadius (cfg.triangleABC.touchpoint ∅ 1) :=
        cfg.triangleABC.affineSpan_pair_eq_orthRadius_insphere (i₁ := 1) (i₂ := 0) (i₃ := 2)
          (by decide) (by decide) (by decide)
    have hpar : AffineSubspace.mk' cfg.X line[ℝ, cfg.A, cfg.C].direction ∥
        cfg.triangleABC.insphere.orthRadius (cfg.triangleABC.touchpoint ∅ 1) := by
      rw [← hAC, AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
      simp [← AffineSubspace.coe_eq_bot_iff, ← Set.not_nonempty_iff_eq_empty,
        AffineSubspace.mk'_nonempty]
    have ht' := cfg.ω_eq_insphere ▸ cfg.isTangent_mk'_X_parallel_AC
    have ht := ht'.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius hpar
      (cfg.triangleABC.touchpoint_mem_insphere _)
    rcases ht with ht | ht
    · rw [← hAC] at ht
      exfalso
      have hXAC : cfg.X ∈ line[ℝ, cfg.A, cfg.C] := ht ▸ AffineSubspace.self_mem_mk' _ _
      have hX₀₂ : cfg.X ∈ affineSpan ℝ (cfg.triangleABC.points '' {0, 2}) := by
        rw [Set.image_insert_eq, Set.image_singleton]
        exact hXAC
      have hX₁₂ : cfg.X ∈ affineSpan ℝ (cfg.triangleABC.points '' {1, 2}) := by
        rw [Set.image_insert_eq, Set.image_singleton]
        exact cfg.X_mem_BC
      apply cfg.X_ne_C
      have hi := (AffineSubspace.mem_inf_iff _ _ _).2 ⟨hX₀₂, hX₁₂⟩
      rw [cfg.triangleABC.independent.inf_affineSpan_eq_affineSpan_inter] at hi
      rw [← AffineSubspace.mem_affineSpan_singleton ℝ,
        show cfg.C = cfg.triangleABC.points 2 by rfl, ← Set.image_singleton]
      convert hi
      grind
    · rw [ht, hAC, Equiv.pointReflection_apply,
        ← AffineIsometryEquiv.pointReflection_apply (𝕜 := ℝ),
        ← cfg.triangleABC.insphere.orthRadius_map _ (by simp), ← cfg.incenter_eq_I]
      rfl
  simp_rw [hmap, AffineSubspace.map_span, Set.image_insert_eq, Set.image_singleton] at ⊢ hX
  exact affineSpan_pair_eq_of_right_mem_of_ne hX cfg.X_ne_A'

lemma AC_parallel_A'X : line[ℝ, cfg.A, cfg.C] ∥ line[ℝ, cfg.A', cfg.X] := by
  rw [A'X_eq_mk', AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
  simp [← AffineSubspace.coe_eq_bot_iff, ← Set.not_nonempty_iff_eq_empty,
    AffineSubspace.mk'_nonempty]

lemma AB_parallel_A'Y : line[ℝ, cfg.A, cfg.B] ∥ line[ℝ, cfg.A', cfg.Y] :=
  cfg.symm.AC_parallel_A'X

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

lemma two_zsmul_oangle_A'PB_eq_two_zsmul_oangle_A'XB :
    (2 : ℤ) • (∡ cfg.A' cfg.P cfg.B) = (2 : ℤ) • (∡ cfg.A' cfg.X cfg.B) := calc
  (2 : ℤ) • (∡ cfg.A' cfg.P cfg.B) = (2 : ℤ) • (∡ cfg.A cfg.P cfg.B) := by
    rw [cfg.sbtw_A_A'_P.symm.oangle_eq_left]
  _ = (2 : ℤ) • (∡ cfg.A cfg.C cfg.B) :=
    cfg.cospherical_APCB.two_zsmul_oangle_eq cfg.P_ne_A cfg.P_ne_B cfg.A_ne_C.symm cfg.B_ne_C.symm
  _ = (2 : ℤ) • (∡ cfg.A' cfg.X cfg.C) := two_zsmul_oangle_of_parallel cfg.AC_parallel_A'X
        (cfg.line_BC_eq_line_CX ▸ AffineSubspace.Parallel.refl _)
  _ = (2 : ℤ) • (∡ cfg.A' cfg.X cfg.B) :=
    cfg.collinear_CXB.two_zsmul_oangle_eq_right cfg.X_ne_C.symm cfg.B_ne_X

end Oriented

lemma cospherical_A'PBX : Cospherical ({cfg.A', cfg.P, cfg.B, cfg.X} : Set Pt) := by
  haveI := someOrientation V
  suffices Cospherical ({cfg.A', cfg.P, cfg.X, cfg.B} : Set Pt) by
    convert this using 1
    grind
  exact cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_A'PB_eq_two_zsmul_oangle_A'XB cfg.not_collinear_A'PB

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

lemma two_zsmul_oangle_APX_eq_two_zsmul_oangle_A'BC :
    (2 : ℤ) • (∡ cfg.A cfg.P cfg.X) = (2 : ℤ) • (∡ cfg.A' cfg.B cfg.C) := calc
  (2 : ℤ) • (∡ cfg.A cfg.P cfg.X) = (2 : ℤ) • (∡ cfg.A' cfg.P cfg.X):= by
    rw [cfg.sbtw_A_A'_P.symm.oangle_eq_left]
  _ = (2 : ℤ) • (∡ cfg.A' cfg.B cfg.X) := cfg.cospherical_A'PBX.two_zsmul_oangle_eq
    cfg.P_ne_A' cfg.X_ne_P.symm cfg.B_ne_A' cfg.B_ne_X
  _ = (2 : ℤ) • (∡ cfg.A' cfg.B cfg.C) :=
    cfg.collinear_XBC.two_zsmul_oangle_eq_right cfg.B_ne_X.symm cfg.B_ne_C.symm

lemma two_zsmul_oangle_YPA_eq_two_zsmul_oangle_BCA' :
    (2 : ℤ) • (∡ cfg.Y cfg.P cfg.A) = (2 : ℤ) • (∡ cfg.B cfg.C cfg.A') := by
  rw [oangle_rev cfg.A, oangle_rev cfg.A', smul_neg, smul_neg, neg_inj]
  exact cfg.symm.two_zsmul_oangle_APX_eq_two_zsmul_oangle_A'BC

lemma oangle_KIL_eq_oangle_CA'B : ∡ cfg.K cfg.I cfg.L = ∡ cfg.C cfg.A' cfg.B := by
  simp [A'_eq_homothety_A_2_I, B_eq_homothety_A_2_L, C_eq_homothety_A_2_K]

lemma oangle_KIL_sign_eq_oangle_YPX_sign :
    (∡ cfg.K cfg.I cfg.L).sign = (∡ cfg.Y cfg.P cfg.X).sign := calc
  (∡ cfg.K cfg.I cfg.L).sign = (∡ cfg.C cfg.A' cfg.B).sign := by rw [oangle_KIL_eq_oangle_CA'B]
  _ = (∡ cfg.B cfg.A cfg.C).sign := by
    rw [cfg.sOppSide_CB_A_A'.oangle_sign_eq_neg (left_mem_affineSpan_pair _ _ _)
      (right_mem_affineSpan_pair _ _ _), ← Real.Angle.sign_neg, ← oangle_rev]
  _ = (∡ cfg.Y cfg.A' cfg.X).sign := by
    rw [oangle_eq_of_parallel cfg.A_notMem_BC cfg.Y_mem_BC cfg.X_mem_BC
      (Set.pair_comm cfg.A _ ▸ Set.pair_comm cfg.A' _ ▸ cfg.AB_parallel_A'Y)
      (Set.pair_comm cfg.A _ ▸ Set.pair_comm cfg.A' _ ▸ cfg.AC_parallel_A'X)]
  _ = (∡ cfg.Y cfg.P cfg.X).sign :=
    (cfg.sOppSide_CB_A_P.symm.trans cfg.sOppSide_CB_A_A').oangle_sign_eq
      (Set.pair_comm _ _ ▸ cfg.Y_mem_BC) (Set.pair_comm _ _ ▸ cfg.X_mem_BC)

lemma oangle_KIL_sign_ne_zero : (∡ cfg.K cfg.I cfg.L).sign ≠ 0 := by
  rw [oangle_KIL_eq_oangle_CA'B, Real.Angle.sign_ne_zero_iff,
    oangle_ne_zero_and_ne_pi_iff_affineIndependent, affineIndependent_iff_not_collinear_set]
  intro hc
  have hc' : cfg.A' ∈ line[ℝ, cfg.C, cfg.B] :=
    hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) cfg.B_ne_C.symm
  exact cfg.sOppSide_CB_A_A'.right_notMem hc'

lemma two_zsmul_oangle_KIL_add_oangle_YPX_eq_zero :
    (2 : ℤ) • (∡ cfg.K cfg.I cfg.L + ∡ cfg.Y cfg.P cfg.X) = 0 := calc
  (2 : ℤ) • (∡ cfg.K cfg.I cfg.L + ∡ cfg.Y cfg.P cfg.X) =
    (2 : ℤ) • ∡ cfg.K cfg.I cfg.L + (2 : ℤ) • ∡ cfg.Y cfg.P cfg.X := smul_add _ _ _
  _ = (2 : ℤ) • ∡ cfg.C cfg.A' cfg.B + (2 : ℤ) • ∡ cfg.Y cfg.P cfg.X := by
    rw [oangle_KIL_eq_oangle_CA'B]
  _ = (2 : ℤ) • ∡ cfg.C cfg.A' cfg.B + (2 : ℤ) • (∡ cfg.Y cfg.P cfg.A + ∡ cfg.A cfg.P cfg.X) := by
    rw [oangle_add cfg.Y_ne_P cfg.P_ne_A.symm cfg.X_ne_P]
  _ = (2 : ℤ) • ∡ cfg.C cfg.A' cfg.B + (2 : ℤ) • ∡ cfg.B cfg.C cfg.A' +
        (2 : ℤ) • ∡ cfg.A' cfg.B cfg.C := by
    rw [smul_add, two_zsmul_oangle_APX_eq_two_zsmul_oangle_A'BC,
      two_zsmul_oangle_YPA_eq_two_zsmul_oangle_BCA', add_assoc]
  _ = (2 : ℤ) • (∡ cfg.C cfg.A' cfg.B + ∡ cfg.B cfg.C cfg.A' + ∡ cfg.A' cfg.B cfg.C) := by
    simp_rw [← smul_add]
  _ = 0 := by
    rw [add_comm (∡ cfg.C cfg.A' cfg.B), oangle_add_oangle_add_oangle_eq_pi cfg.B_ne_C.symm
      cfg.C_ne_A'.symm cfg.B_ne_A']
    simp

end Oriented

theorem result : ∠ cfg.K cfg.I cfg.L + ∠ cfg.Y cfg.P cfg.X = π := by
  haveI := someOrientation V
  rw [angle_eq_abs_oangle_toReal cfg.K_ne_I cfg.L_ne_I,
    angle_eq_abs_oangle_toReal cfg.Y_ne_P cfg.X_ne_P]
  exact Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
    cfg.two_zsmul_oangle_KIL_add_oangle_YPX_eq_zero cfg.oangle_KIL_sign_eq_oangle_YPX_sign
    cfg.oangle_KIL_sign_ne_zero

end Imo2024q4Cfg

end Imo2024Q4

open Imo2024Q4

theorem imo2024_q4 [Fact (finrank ℝ V = 2)] {A B C I X Y P K L : Pt} {ω : Sphere Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]) (AB_lt_AC : dist A B < dist A C)
    (AC_lt_BC : dist A C < dist B C)
    (incenter_eq_I : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).incenter = I)
    (incircle_eq_ω : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).insphere = ω)
    (X_mem_BC : X ∈ line[ℝ, B, C]) (X_ne_C : X ≠ C)
    (isTangent_mk'_X_parallel_AC : ω.IsTangent (AffineSubspace.mk' X line[ℝ, A, C].direction))
    (Y_mem_BC : Y ∈ line[ℝ, B, C]) (Y_ne_B : Y ≠ B)
    (isTangent_mk'_Y_parallel_AB : ω.IsTangent (AffineSubspace.mk' Y line[ℝ, A, B].direction))
    (P_mem_inter :
      P ∈ (line[ℝ, A, I] ∩ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere : Set Pt))
    (P_ne_A : P ≠ A) (K_eq_midpoint_AC : K = midpoint ℝ A C)
    (L_eq_midpoint_AB : L = midpoint ℝ A B) : ∠ K I L + ∠ Y P X = π :=
  (⟨A, B, C, I, X, Y, P, K, L, ω, affineIndependent_ABC, AB_lt_AC.trans AC_lt_BC, AC_lt_BC,
    incenter_eq_I, incircle_eq_ω, X_mem_BC, X_ne_C, isTangent_mk'_X_parallel_AC, Y_mem_BC, Y_ne_B,
    isTangent_mk'_Y_parallel_AB, P_mem_inter, P_ne_A, K_eq_midpoint_AC, L_eq_midpoint_AB⟩ :
   Imo2024q4Cfg V Pt).result
