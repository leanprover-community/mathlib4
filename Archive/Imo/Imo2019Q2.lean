/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module imo.imo2019_q2
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

/-!
# IMO 2019 Q2

In triangle `ABC`, point `A₁` lies on side `BC` and point `B₁` lies on side `AC`. Let `P` and
`Q` be points on segments `AA₁` and `BB₁`, respectively, such that `PQ` is parallel to `AB`.
Let `P₁` be a point on line `PB₁`, such that `B₁` lies strictly between `P` and `P₁`, and
`∠PP₁C = ∠BAC`. Similarly, let `Q₁` be a point on line `QA₁`, such that `A₁` lies strictly
between `Q` and `Q₁`, and `∠CQ₁Q = ∠CBA`.

Prove that points `P`, `Q`, `P₁`, and `Q₁` are concyclic.

We follow Solution 1 from the
[official solutions](https://www.imo2019.uk/wp-content/uploads/2018/07/solutions-r856.pdf).
Letting the rays `AA₁` and `BB₁` intersect the circumcircle of `ABC` at `A₂` and `B₂`
respectively, we show with an angle chase that `P`, `Q`, `A₂`, `B₂` are concyclic and let `ω` be
the circle through those points. We then show that `C`, `Q₁`, `A₂`, `A₁` are concyclic, and
then that `Q₁` lies on `ω`, and similarly that `P₁` lies on `ω`, so the required four points are
concyclic.

Note that most of the formal proof is actually proving nondegeneracy conditions needed for that
angle chase / concyclicity argument, where an informal solution doesn't discuss those conditions
at all. Also note that (as described in `geometry.euclidean.angle.oriented.basic`) the oriented
angles used are modulo `2 * π`, so parts of the angle chase that are only valid for angles modulo
`π` (as used in the informal solution) are represented as equalities of twice angles, which we write
as `(2 : ℤ) • ∡ _ _ _ = (2 : ℤ) • _ _ _`.
-/


library_note "IMO geometry formalization conventions"/--
We apply the following conventions for formalizing IMO geometry problems. A problem is assumed
to take place in the plane unless that is clearly not intended, so it is not required to prove
that the points are coplanar (whether or not that in fact follows from the other conditions).
Angles in problem statements are taken to be unoriented. A reference to an angle `∠XYZ` is taken
to imply that `X` and `Z` are not equal to `Y`, since choices of junk values play no role in
informal mathematics, and those implications are included as hypotheses for the problem whether
or not they follow from the other hypotheses. Similar, a reference to `XY` as a line is taken to
imply that `X` does not equal `Y` and that is included as a hypothesis, and a reference to `XY`
being parallel to something is considered a reference to it as a line. However, such an implicit
hypothesis about two points being different is included only once for any given two points (even
if it follows from more than one reference to a line or an angle), if `X ≠ Y` is included then
`Y ≠ X` is not included separately, and such hypotheses are not included in the case where there
is also a reference in the problem to a triangle including those two points, or to strict
betweenness of three points including those two. If betweenness is stated, it is taken to be
strict betweenness. However, segments and sides are taken to include their endpoints (unless
this makes a problem false), although those degenerate cases might not necessarily have been
considered when the problem was formulated and contestants might not have been expected to deal
with them. A reference to a point being on a side or a segment is expressed directly with `wbtw`
rather than more literally with `affine_segment`.
-/


open Affine Affine.Simplex EuclideanGeometry FiniteDimensional

open scoped Affine EuclideanGeometry Real

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

variable (V : Type _) (Pt : Type _)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt] [hd2 : Fact (finrank ℝ V = 2)]

namespace imo2019_q2

noncomputable section

/-- A configuration satisfying the conditions of the problem. We define this structure to avoid
passing many hypotheses around as we build up information about the configuration; the final
result for a statement of the problem not using this structure is then deduced from one in terms
of this structure. -/
@[nolint has_nonempty_instance]
structure Imo2019q2Cfg where
  (A b C a₁ b₁ P q p₁ q₁ : Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  wbtw_b_a₁_c : Wbtw ℝ B A₁ C
  wbtw_a_b₁_c : Wbtw ℝ A B₁ C
  wbtw_a_p_a₁ : Wbtw ℝ A P A₁
  wbtw_b_q_b₁ : Wbtw ℝ B Q B₁
  PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]
  -- A hypothesis implicit in the named line.
  p_ne_q : P ≠ Q
  sbtw_p_b₁_p₁ : Sbtw ℝ P B₁ P₁
  angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C
  -- A hypothesis implicit in the first named angle.
  c_ne_p₁ : C ≠ P₁
  sbtw_q_a₁_q₁ : Sbtw ℝ Q A₁ Q₁
  angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A
  -- A hypothesis implicit in the first named angle.
  c_ne_q₁ : C ≠ Q₁
#align imo2019_q2.imo2019q2_cfg Imo2019Q2.Imo2019q2Cfg

/-- A default choice of orientation, for lemmas that need to pick one. -/
def someOrientation : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩
#align imo2019_q2.some_orientation Imo2019Q2.someOrientation

variable {V Pt}

namespace Imo2019q2Cfg

variable (cfg : Imo2019q2Cfg V Pt)

/-- The configuration has symmetry, allowing results proved for one point to be applied for
another (where the informal solution says "similarly"). -/
def symm : Imo2019q2Cfg V Pt where
  A := cfg.b
  b := cfg.A
  C := cfg.C
  a₁ := cfg.b₁
  b₁ := cfg.a₁
  P := cfg.q
  q := cfg.P
  p₁ := cfg.q₁
  q₁ := cfg.p₁
  affineIndependent_ABC := by
    rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 1)]
    convert cfg.affine_independent_ABC using 1
    ext x
    fin_cases x <;> rfl
  wbtw_b_a₁_c := cfg.wbtw_a_b₁_c
  wbtw_a_b₁_c := cfg.wbtw_b_a₁_c
  wbtw_a_p_a₁ := cfg.wbtw_b_q_b₁
  wbtw_b_q_b₁ := cfg.wbtw_a_p_a₁
  PQ_parallel_AB := Set.pair_comm cfg.P cfg.q ▸ Set.pair_comm cfg.A cfg.b ▸ cfg.PQ_parallel_AB
  p_ne_q := cfg.p_ne_q.symm
  sbtw_p_b₁_p₁ := cfg.sbtw_q_a₁_q₁
  angle_PP₁C_eq_angle_BAC :=
    angle_comm cfg.C cfg.q₁ cfg.q ▸ angle_comm cfg.C cfg.b cfg.A ▸ cfg.angle_CQ₁Q_eq_angle_CBA
  c_ne_p₁ := cfg.c_ne_q₁
  sbtw_q_a₁_q₁ := cfg.sbtw_p_b₁_p₁
  angle_CQ₁Q_eq_angle_CBA :=
    angle_comm cfg.P cfg.p₁ cfg.C ▸ angle_comm cfg.b cfg.A cfg.C ▸ cfg.angle_PP₁C_eq_angle_BAC
  c_ne_q₁ := cfg.c_ne_p₁
#align imo2019_q2.imo2019q2_cfg.symm Imo2019Q2.Imo2019q2Cfg.symm

/-! ### Configuration properties that are obvious from the diagram, and construction of the
points `A₂` and `B₂` -/


theorem a_ne_b : cfg.A ≠ cfg.b :=
  cfg.affineIndependent_ABC.Injective.Ne (by decide : (0 : Fin 3) ≠ 1)
#align imo2019_q2.imo2019q2_cfg.A_ne_B Imo2019Q2.Imo2019q2Cfg.a_ne_b

theorem a_ne_c : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.Injective.Ne (by decide : (0 : Fin 3) ≠ 2)
#align imo2019_q2.imo2019q2_cfg.A_ne_C Imo2019Q2.Imo2019q2Cfg.a_ne_c

theorem b_ne_c : cfg.b ≠ cfg.C :=
  cfg.affineIndependent_ABC.Injective.Ne (by decide : (1 : Fin 3) ≠ 2)
#align imo2019_q2.imo2019q2_cfg.B_ne_C Imo2019Q2.Imo2019q2Cfg.b_ne_c

theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.b, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC
#align imo2019_q2.imo2019q2_cfg.not_collinear_ABC Imo2019Q2.Imo2019q2Cfg.not_collinear_ABC

/-- `ABC` as a `triangle`. -/
def triangleABC : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_ABC⟩
#align imo2019_q2.imo2019q2_cfg.triangle_ABC Imo2019Q2.Imo2019q2Cfg.triangleABC

theorem a_mem_circumsphere : cfg.A ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 0
#align imo2019_q2.imo2019q2_cfg.A_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.a_mem_circumsphere

theorem b_mem_circumsphere : cfg.b ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 1
#align imo2019_q2.imo2019q2_cfg.B_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.b_mem_circumsphere

theorem c_mem_circumsphere : cfg.C ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 2
#align imo2019_q2.imo2019q2_cfg.C_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.c_mem_circumsphere

theorem symm_triangleABC : cfg.symm.triangleABC = cfg.triangleABC.reindex (Equiv.swap 0 1) := by
  ext i; fin_cases i <;> rfl
#align imo2019_q2.imo2019q2_cfg.symm_triangle_ABC Imo2019Q2.Imo2019q2Cfg.symm_triangleABC

theorem symm_triangleABC_circumsphere :
    cfg.symm.triangleABC.circumsphere = cfg.triangleABC.circumsphere := by
  rw [symm_triangle_ABC, Affine.Simplex.circumsphere_reindex]
#align imo2019_q2.imo2019q2_cfg.symm_triangle_ABC_circumsphere Imo2019Q2.Imo2019q2Cfg.symm_triangleABC_circumsphere

/-- `A₂` is the second point of intersection of the ray `AA₁` with the circumcircle of `ABC`. -/
def a₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.A (cfg.a₁ -ᵥ cfg.A)
#align imo2019_q2.imo2019q2_cfg.A₂ Imo2019Q2.Imo2019q2Cfg.a₂

/-- `B₂` is the second point of intersection of the ray `BB₁` with the circumcircle of `ABC`. -/
def b₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.b (cfg.b₁ -ᵥ cfg.b)
#align imo2019_q2.imo2019q2_cfg.B₂ Imo2019Q2.Imo2019q2Cfg.b₂

theorem a₂_mem_circumsphere : cfg.a₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.a_mem_circumsphere
#align imo2019_q2.imo2019q2_cfg.A₂_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.a₂_mem_circumsphere

theorem b₂_mem_circumsphere : cfg.b₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.b_mem_circumsphere
#align imo2019_q2.imo2019q2_cfg.B₂_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.b₂_mem_circumsphere

theorem symm_a₂ : cfg.symm.a₂ = cfg.b₂ := by simp_rw [A₂, B₂, symm_triangle_ABC_circumsphere]; rfl
#align imo2019_q2.imo2019q2_cfg.symm_A₂ Imo2019Q2.Imo2019q2Cfg.symm_a₂

theorem QP_parallel_BA : line[ℝ, cfg.q, cfg.P] ∥ line[ℝ, cfg.b, cfg.A] := by
  rw [Set.pair_comm cfg.Q, Set.pair_comm cfg.B]; exact cfg.PQ_parallel_AB
#align imo2019_q2.imo2019q2_cfg.QP_parallel_BA Imo2019Q2.Imo2019q2Cfg.QP_parallel_BA

theorem a_ne_a₁ : cfg.A ≠ cfg.a₁ := by
  intro h
  have h' := cfg.not_collinear_ABC
  rw [h, Set.insert_comm] at h' 
  exact h' cfg.wbtw_B_A₁_C.collinear
#align imo2019_q2.imo2019q2_cfg.A_ne_A₁ Imo2019Q2.Imo2019q2Cfg.a_ne_a₁

theorem collinear_PAA₁A₂ : Collinear ℝ ({cfg.P, cfg.A, cfg.a₁, cfg.a₂} : Set Pt) := by
  rw [A₂,
    (cfg.triangle_ABC.circumsphere.second_inter_collinear cfg.A cfg.A₁).collinear_insert_iff_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_A₁,
    Set.insert_comm]
  exact cfg.wbtw_A_P_A₁.collinear
#align imo2019_q2.imo2019q2_cfg.collinear_PAA₁A₂ Imo2019Q2.Imo2019q2Cfg.collinear_PAA₁A₂

theorem a₁_ne_c : cfg.a₁ ≠ cfg.C := by
  intro h
  have hsbtw := cfg.sbtw_Q_A₁_Q₁
  rw [h] at hsbtw 
  have ha := hsbtw.angle₂₃₁_eq_zero
  rw [angle_CQ₁Q_eq_angle_CBA, angle_comm] at ha 
  exact (angle_ne_zero_of_not_collinear cfg.not_collinear_ABC) ha
#align imo2019_q2.imo2019q2_cfg.A₁_ne_C Imo2019Q2.Imo2019q2Cfg.a₁_ne_c

theorem b₁_ne_c : cfg.b₁ ≠ cfg.C :=
  cfg.symm.a₁_ne_c
#align imo2019_q2.imo2019q2_cfg.B₁_ne_C Imo2019Q2.Imo2019q2Cfg.b₁_ne_c

theorem q_not_mem_CB : cfg.q ∉ line[ℝ, cfg.C, cfg.b] := by
  intro hQ
  have hQA₁ : line[ℝ, cfg.Q, cfg.A₁] ≤ line[ℝ, cfg.C, cfg.B] :=
    affineSpan_pair_le_of_mem_of_mem hQ cfg.wbtw_B_A₁_C.symm.mem_affine_span
  have hQ₁ : cfg.Q₁ ∈ line[ℝ, cfg.C, cfg.B] := by
    rw [AffineSubspace.le_def'] at hQA₁ 
    exact hQA₁ _ cfg.sbtw_Q_A₁_Q₁.right_mem_affine_span
  have hc : Collinear ℝ ({cfg.C, cfg.Q₁, cfg.Q} : Set Pt) :=
    haveI hc' : Collinear ℝ ({cfg.B, cfg.C, cfg.Q₁, cfg.Q} : Set Pt) := by
      rw [Set.insert_comm cfg.B, Set.insert_comm cfg.B, Set.pair_comm, Set.insert_comm cfg.C,
        Set.insert_comm cfg.C]
      exact collinear_insert_insert_of_mem_affineSpan_pair hQ₁ hQ
    hc'.subset (Set.subset_insert _ _)
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, cfg.angle_CQ₁Q_eq_angle_CBA,
    or_iff_right cfg.C_ne_Q₁, or_iff_right cfg.sbtw_Q_A₁_Q₁.left_ne_right, angle_comm] at hc 
  exact cfg.not_collinear_ABC (hc.elim collinear_of_angle_eq_zero collinear_of_angle_eq_pi)
#align imo2019_q2.imo2019q2_cfg.Q_not_mem_CB Imo2019Q2.Imo2019q2Cfg.q_not_mem_CB

theorem q_ne_b : cfg.q ≠ cfg.b := by
  intro h
  have h' := cfg.Q_not_mem_CB
  rw [h] at h' 
  exact h' (right_mem_affineSpan_pair _ _ _)
#align imo2019_q2.imo2019q2_cfg.Q_ne_B Imo2019Q2.Imo2019q2Cfg.q_ne_b

theorem sOppSide_CB_q_q₁ : line[ℝ, cfg.C, cfg.b].SOppSide cfg.q cfg.q₁ :=
  cfg.sbtw_q_a₁_q₁.sOppSide_of_not_mem_of_mem cfg.q_not_mem_CB cfg.wbtw_b_a₁_c.symm.mem_affineSpan
#align imo2019_q2.imo2019q2_cfg.s_opp_side_CB_Q_Q₁ Imo2019Q2.Imo2019q2Cfg.sOppSide_CB_q_q₁

/-! ### Relate the orientations of different angles in the configuration -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem oangle_CQ₁Q_sign_eq_oangle_CBA_sign :
    (∡ cfg.C cfg.q₁ cfg.q).sign = (∡ cfg.C cfg.b cfg.A).sign := by
  rw [← cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right,
    cfg.s_opp_side_CB_Q_Q₁.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ cfg.C cfg.B)
      cfg.wbtw_B_A₁_C.symm.mem_affine_span,
    ← Real.Angle.sign_neg, ← oangle_rev,
    cfg.wbtw_B_A₁_C.oangle_sign_eq_of_ne_right cfg.Q cfg.A₁_ne_C, oangle_rotate_sign,
    cfg.wbtw_B_Q_B₁.oangle_eq_right cfg.Q_ne_B,
    cfg.wbtw_A_B₁_C.symm.oangle_sign_eq_of_ne_left cfg.B cfg.B₁_ne_C.symm]
#align imo2019_q2.imo2019q2_cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign Imo2019Q2.Imo2019q2Cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign

theorem oangle_CQ₁Q_eq_oangle_CBA : ∡ cfg.C cfg.q₁ cfg.q = ∡ cfg.C cfg.b cfg.A :=
  oangle_eq_of_angle_eq_of_sign_eq cfg.angle_CQ₁Q_eq_angle_CBA
    cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign
#align imo2019_q2.imo2019q2_cfg.oangle_CQ₁Q_eq_oangle_CBA Imo2019Q2.Imo2019q2Cfg.oangle_CQ₁Q_eq_oangle_CBA

end Oriented

/-! ### More obvious configuration properties -/


theorem a₁_ne_b : cfg.a₁ ≠ cfg.b := by
  intro h
  have hwbtw := cfg.wbtw_A_P_A₁
  rw [h] at hwbtw 
  have hPQ : line[ℝ, cfg.P, cfg.Q] = line[ℝ, cfg.A, cfg.B] := by
    rw [AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair _ _ _)
        hwbtw.mem_affine_span]
    exact cfg.PQ_parallel_AB.direction_eq
  haveI := some_orientation V
  have haQ : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A := by
    rw [Collinear.two_zsmul_oangle_eq_right _ cfg.A_ne_B cfg.Q_ne_B]
    rw [Set.pair_comm, Set.insert_comm]
    refine' collinear_insert_of_mem_affineSpan_pair _
    rw [← hPQ]
    exact right_mem_affineSpan_pair _ _ _
  have ha : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q := by
    rw [oangle_CQ₁Q_eq_oangle_CBA, haQ]
  have hn : ¬Collinear ℝ ({cfg.C, cfg.B, cfg.Q} : Set Pt) := by
    rw [collinear_iff_of_two_zsmul_oangle_eq haQ, Set.pair_comm, Set.insert_comm, Set.pair_comm]
    exact cfg.not_collinear_ABC
  have hc := cospherical_of_two_zsmul_oangle_eq_of_not_collinear ha hn
  have hBQ₁ : cfg.B ≠ cfg.Q₁ := by rw [← h]; exact cfg.sbtw_Q_A₁_Q₁.ne_right
  have hQQ₁ : cfg.Q ≠ cfg.Q₁ := cfg.sbtw_Q_A₁_Q₁.left_ne_right
  have hBQ₁Q : AffineIndependent ℝ ![cfg.B, cfg.Q₁, cfg.Q] :=
    hc.affine_independent_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      hBQ₁ cfg.Q_ne_B.symm hQQ₁.symm
  rw [affineIndependent_iff_not_collinear_set] at hBQ₁Q 
  refine' hBQ₁Q _
  rw [← h, Set.pair_comm, Set.insert_comm]
  exact cfg.sbtw_Q_A₁_Q₁.wbtw.collinear
#align imo2019_q2.imo2019q2_cfg.A₁_ne_B Imo2019Q2.Imo2019q2Cfg.a₁_ne_b

theorem sbtw_b_a₁_c : Sbtw ℝ cfg.b cfg.a₁ cfg.C :=
  ⟨cfg.wbtw_b_a₁_c, cfg.a₁_ne_b, cfg.a₁_ne_c⟩
#align imo2019_q2.imo2019q2_cfg.sbtw_B_A₁_C Imo2019Q2.Imo2019q2Cfg.sbtw_b_a₁_c

theorem sbtw_a_b₁_c : Sbtw ℝ cfg.A cfg.b₁ cfg.C :=
  cfg.symm.sbtw_b_a₁_c
#align imo2019_q2.imo2019q2_cfg.sbtw_A_B₁_C Imo2019Q2.Imo2019q2Cfg.sbtw_a_b₁_c

theorem sbtw_a_a₁_a₂ : Sbtw ℝ cfg.A cfg.a₁ cfg.a₂ := by
  refine' sphere.sbtw_second_inter cfg.A_mem_circumsphere _
  convert cfg.sbtw_B_A₁_C.dist_lt_max_dist _
  change _ = max (dist (cfg.triangle_ABC.points 1) _) (dist (cfg.triangle_ABC.points 2) _)
  simp_rw [circumsphere_center, circumsphere_radius, dist_circumcenter_eq_circumradius, max_self]
#align imo2019_q2.imo2019q2_cfg.sbtw_A_A₁_A₂ Imo2019Q2.Imo2019q2Cfg.sbtw_a_a₁_a₂

theorem sbtw_b_b₁_b₂ : Sbtw ℝ cfg.b cfg.b₁ cfg.b₂ := by rw [← cfg.symm_A₂];
  exact cfg.symm.sbtw_A_A₁_A₂
#align imo2019_q2.imo2019q2_cfg.sbtw_B_B₁_B₂ Imo2019Q2.Imo2019q2Cfg.sbtw_b_b₁_b₂

theorem a₂_ne_a : cfg.a₂ ≠ cfg.A :=
  cfg.sbtw_a_a₁_a₂.left_ne_right.symm
#align imo2019_q2.imo2019q2_cfg.A₂_ne_A Imo2019Q2.Imo2019q2Cfg.a₂_ne_a

theorem a₂_ne_p : cfg.a₂ ≠ cfg.P :=
  (cfg.sbtw_a_a₁_a₂.trans_wbtw_left_ne cfg.wbtw_a_p_a₁).symm
#align imo2019_q2.imo2019q2_cfg.A₂_ne_P Imo2019Q2.Imo2019q2Cfg.a₂_ne_p

theorem a₂_ne_b : cfg.a₂ ≠ cfg.b := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁ 
  refine' cfg.not_collinear_ABC _
  have hc : Collinear ℝ ({cfg.A, cfg.C, cfg.B, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affine_span
      cfg.sbtw_B_A₁_C.right_mem_affine_span
  refine' hc.subset _
  rw [Set.pair_comm _ cfg.A₁, Set.insert_comm _ cfg.A₁, Set.insert_comm _ cfg.A₁, Set.pair_comm]
  exact Set.subset_insert _ _
#align imo2019_q2.imo2019q2_cfg.A₂_ne_B Imo2019Q2.Imo2019q2Cfg.a₂_ne_b

theorem a₂_ne_c : cfg.a₂ ≠ cfg.C := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁ 
  refine' cfg.not_collinear_ABC _
  have hc : Collinear ℝ ({cfg.A, cfg.B, cfg.C, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affine_span
      cfg.sbtw_B_A₁_C.left_mem_affine_span
  refine' hc.subset (Set.insert_subset_insert (Set.insert_subset_insert _))
  rw [Set.singleton_subset_iff]
  exact Set.mem_insert _ _
#align imo2019_q2.imo2019q2_cfg.A₂_ne_C Imo2019Q2.Imo2019q2Cfg.a₂_ne_c

theorem b₂_ne_b : cfg.b₂ ≠ cfg.b := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_A
#align imo2019_q2.imo2019q2_cfg.B₂_ne_B Imo2019Q2.Imo2019q2Cfg.b₂_ne_b

theorem b₂_ne_q : cfg.b₂ ≠ cfg.q := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_P
#align imo2019_q2.imo2019q2_cfg.B₂_ne_Q Imo2019Q2.Imo2019q2Cfg.b₂_ne_q

theorem b₂_ne_a₂ : cfg.b₂ ≠ cfg.a₂ := by
  intro h
  have hA : Sbtw ℝ (cfg.triangle_ABC.points 1) cfg.A₁ (cfg.triangle_ABC.points 2) := cfg.sbtw_B_A₁_C
  have hB : Sbtw ℝ (cfg.triangle_ABC.points 0) cfg.B₁ (cfg.triangle_ABC.points 2) := cfg.sbtw_A_B₁_C
  have hA' : cfg.A₂ ∈ line[ℝ, cfg.triangle_ABC.points 0, cfg.A₁] :=
    sphere.second_inter_vsub_mem_affine_span _ _ _
  have hB' : cfg.A₂ ∈ line[ℝ, cfg.triangle_ABC.points 1, cfg.B₁] := by rw [← h];
    exact sphere.second_inter_vsub_mem_affine_span _ _ _
  exact
    (sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair (by decide) hA hB hA' hB').symm.not_rotate
      cfg.sbtw_A_A₁_A₂.wbtw
#align imo2019_q2.imo2019q2_cfg.B₂_ne_A₂ Imo2019Q2.Imo2019q2Cfg.b₂_ne_a₂

theorem wbtw_b_q_b₂ : Wbtw ℝ cfg.b cfg.q cfg.b₂ :=
  cfg.sbtw_b_b₁_b₂.Wbtw.trans_left cfg.wbtw_b_q_b₁
#align imo2019_q2.imo2019q2_cfg.wbtw_B_Q_B₂ Imo2019Q2.Imo2019q2Cfg.wbtw_b_q_b₂

/-! ### The first equality in the first angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ :
    (2 : ℤ) • ∡ cfg.q cfg.P cfg.a₂ = (2 : ℤ) • ∡ cfg.b cfg.A cfg.a₂ := by
  refine' two_zsmul_oangle_of_parallel cfg.QP_parallel_BA _
  convert AffineSubspace.Parallel.refl _ using 1
  rw [cfg.collinear_PAA₁A₂.affine_span_eq_of_ne
      (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A₂_ne_A,
    cfg.collinear_PAA₁A₂.affine_span_eq_of_ne
      (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      (Set.mem_insert _ _) cfg.A₂_ne_P]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂

end Oriented

/-! ### More obvious configuration properties -/


theorem not_collinear_QPA₂ : ¬Collinear ℝ ({cfg.q, cfg.P, cfg.a₂} : Set Pt) := by
  haveI := some_orientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂, ←
    affineIndependent_iff_not_collinear_set]
  have h : cospherical ({cfg.B, cfg.A, cfg.A₂} : Set Pt) := by
    refine' cfg.triangle_ABC.circumsphere.cospherical.subset _
    simp [Set.insert_subset_iff, cfg.A_mem_circumsphere, cfg.B_mem_circumsphere,
      cfg.A₂_mem_circumsphere]
  exact h.affine_independent_of_ne cfg.A_ne_B.symm cfg.A₂_ne_B.symm cfg.A₂_ne_A.symm
#align imo2019_q2.imo2019q2_cfg.not_collinear_QPA₂ Imo2019Q2.Imo2019q2Cfg.not_collinear_QPA₂

theorem q₁_ne_a₂ : cfg.q₁ ≠ cfg.a₂ := by
  intro h
  have h₁ := cfg.sbtw_Q_A₁_Q₁
  rw [h] at h₁ 
  refine' cfg.not_collinear_QPA₂ _
  have hA₂ := cfg.sbtw_A_A₁_A₂.right_mem_affine_span
  have hA₂A₁ : line[ℝ, cfg.A₂, cfg.A₁] ≤ line[ℝ, cfg.A, cfg.A₁] :=
    affineSpan_pair_le_of_left_mem hA₂
  have hQ : cfg.Q ∈ line[ℝ, cfg.A, cfg.A₁] := by
    rw [AffineSubspace.le_def'] at hA₂A₁ 
    exact hA₂A₁ _ h₁.left_mem_affine_span
  exact collinear_triple_of_mem_affineSpan_pair hQ cfg.wbtw_A_P_A₁.mem_affine_span hA₂
#align imo2019_q2.imo2019q2_cfg.Q₁_ne_A₂ Imo2019Q2.Imo2019q2Cfg.q₁_ne_a₂

theorem affineIndependent_QPA₂ : AffineIndependent ℝ ![cfg.q, cfg.P, cfg.a₂] :=
  affineIndependent_iff_not_collinear_set.2 cfg.not_collinear_QPA₂
#align imo2019_q2.imo2019q2_cfg.affine_independent_QPA₂ Imo2019Q2.Imo2019q2Cfg.affineIndependent_QPA₂

theorem affineIndependent_PQB₂ : AffineIndependent ℝ ![cfg.P, cfg.q, cfg.b₂] := by rw [← symm_A₂];
  exact cfg.symm.affine_independent_QPA₂
#align imo2019_q2.imo2019q2_cfg.affine_independent_PQB₂ Imo2019Q2.Imo2019q2Cfg.affineIndependent_PQB₂

/-- `QPA₂` as a `triangle`. -/
def triangleQPA₂ : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_QPA₂⟩
#align imo2019_q2.imo2019q2_cfg.triangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.triangleQPA₂

/-- `PQB₂` as a `triangle`. -/
def trianglePQB₂ : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_PQB₂⟩
#align imo2019_q2.imo2019q2_cfg.triangle_PQB₂ Imo2019Q2.Imo2019q2Cfg.trianglePQB₂

theorem symm_triangleQPA₂ : cfg.symm.triangleQPA₂ = cfg.trianglePQB₂ := by
  simp_rw [triangle_PQB₂, ← symm_A₂]; ext i; fin_cases i <;> rfl
#align imo2019_q2.imo2019q2_cfg.symm_triangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.symm_triangleQPA₂

/-- `ω` is the circle containing `Q`, `P` and `A₂`, which will be shown also to contain `B₂`,
`P₁` and `Q₁`. -/
def ω : Sphere Pt :=
  cfg.triangleQPA₂.circumsphere
#align imo2019_q2.imo2019q2_cfg.ω Imo2019Q2.Imo2019q2Cfg.ω

theorem p_mem_ω : cfg.P ∈ cfg.ω :=
  cfg.triangleQPA₂.mem_circumsphere 1
#align imo2019_q2.imo2019q2_cfg.P_mem_ω Imo2019Q2.Imo2019q2Cfg.p_mem_ω

theorem q_mem_ω : cfg.q ∈ cfg.ω :=
  cfg.triangleQPA₂.mem_circumsphere 0
#align imo2019_q2.imo2019q2_cfg.Q_mem_ω Imo2019Q2.Imo2019q2Cfg.q_mem_ω

/-! ### The rest of the first angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ :
    (2 : ℤ) • ∡ cfg.q cfg.P cfg.a₂ = (2 : ℤ) • ∡ cfg.q cfg.b₂ cfg.a₂ :=
  calc
    (2 : ℤ) • ∡ cfg.q cfg.P cfg.a₂ = (2 : ℤ) • ∡ cfg.b cfg.A cfg.a₂ :=
      cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂
    _ = (2 : ℤ) • ∡ cfg.b cfg.b₂ cfg.a₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.b_mem_circumsphere cfg.a_mem_circumsphere
        cfg.b₂_mem_circumsphere cfg.a₂_mem_circumsphere cfg.a_ne_b cfg.a₂_ne_a.symm cfg.b₂_ne_b
        cfg.b₂_ne_a₂)
    _ = (2 : ℤ) • ∡ cfg.q cfg.b₂ cfg.a₂ := by
      rw [cfg.wbtw_B_Q_B₂.symm.oangle_eq_left cfg.B₂_ne_Q.symm]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂

end Oriented

/-! ### Conclusions from that first angle chase -/


theorem cospherical_QPB₂A₂ : Cospherical ({cfg.q, cfg.P, cfg.b₂, cfg.a₂} : Set Pt) :=
  haveI := some_orientation V
  cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ cfg.not_collinear_QPA₂
#align imo2019_q2.imo2019q2_cfg.cospherical_QPB₂A₂ Imo2019Q2.Imo2019q2Cfg.cospherical_QPB₂A₂

theorem symm_ω_eq_trianglePQB₂_circumsphere : cfg.symm.ω = cfg.trianglePQB₂.circumsphere := by
  rw [ω, symm_triangle_QPA₂]
#align imo2019_q2.imo2019q2_cfg.symm_ω_eq_triangle_PQB₂_circumsphere Imo2019Q2.Imo2019q2Cfg.symm_ω_eq_trianglePQB₂_circumsphere

theorem symm_ω : cfg.symm.ω = cfg.ω := by
  rw [symm_ω_eq_triangle_PQB₂_circumsphere, ω]
  refine' circumsphere_eq_of_cospherical hd2.out cfg.cospherical_QPB₂A₂ _ _
  · simp only [triangle_PQB₂, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_emptyc_eq]
    rw [Set.insert_comm]
    refine' Set.insert_subset_insert (Set.insert_subset_insert _)
    simp
  · simp only [triangle_QPA₂, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_emptyc_eq]
    refine' Set.insert_subset_insert (Set.insert_subset_insert _)
    simp
#align imo2019_q2.imo2019q2_cfg.symm_ω Imo2019Q2.Imo2019q2Cfg.symm_ω

/-! ### The second angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA :
    (2 : ℤ) • ∡ cfg.C cfg.a₂ cfg.a₁ = (2 : ℤ) • ∡ cfg.C cfg.b cfg.A :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.a₂ cfg.a₁ = (2 : ℤ) • ∡ cfg.C cfg.a₂ cfg.A := by
      rw [cfg.sbtw_A_A₁_A₂.symm.oangle_eq_right]
    _ = (2 : ℤ) • ∡ cfg.C cfg.b cfg.A :=
      Sphere.two_zsmul_oangle_eq cfg.c_mem_circumsphere cfg.a₂_mem_circumsphere
        cfg.b_mem_circumsphere cfg.a_mem_circumsphere cfg.a₂_ne_c cfg.a₂_ne_a cfg.b_ne_c
        cfg.a_ne_b.symm
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA

theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ :
    (2 : ℤ) • ∡ cfg.C cfg.a₂ cfg.a₁ = (2 : ℤ) • ∡ cfg.C cfg.q₁ cfg.a₁ :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.a₂ cfg.a₁ = (2 : ℤ) • ∡ cfg.C cfg.b cfg.A :=
      cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA
    _ = (2 : ℤ) • ∡ cfg.C cfg.q₁ cfg.q := by rw [oangle_CQ₁Q_eq_oangle_CBA]
    _ = (2 : ℤ) • ∡ cfg.C cfg.q₁ cfg.a₁ := by rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁

end Oriented

/-! ### Conclusions from that second angle chase -/


theorem not_collinear_CA₂A₁ : ¬Collinear ℝ ({cfg.C, cfg.a₂, cfg.a₁} : Set Pt) := by
  haveI := some_orientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA,
    Set.pair_comm, Set.insert_comm, Set.pair_comm]
  exact cfg.not_collinear_ABC
#align imo2019_q2.imo2019q2_cfg.not_collinear_CA₂A₁ Imo2019Q2.Imo2019q2Cfg.not_collinear_CA₂A₁

theorem cospherical_A₁Q₁CA₂ : Cospherical ({cfg.a₁, cfg.q₁, cfg.C, cfg.a₂} : Set Pt) := by
  haveI := some_orientation V
  rw [Set.insert_comm cfg.Q₁, Set.insert_comm cfg.A₁, Set.pair_comm, Set.insert_comm cfg.A₁,
    Set.pair_comm]
  exact
    cospherical_of_two_zsmul_oangle_eq_of_not_collinear
      cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ cfg.not_collinear_CA₂A₁
#align imo2019_q2.imo2019q2_cfg.cospherical_A₁Q₁CA₂ Imo2019Q2.Imo2019q2Cfg.cospherical_A₁Q₁CA₂

/-! ### The third angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ :
    (2 : ℤ) • ∡ cfg.q cfg.q₁ cfg.a₂ = (2 : ℤ) • ∡ cfg.q cfg.P cfg.a₂ :=
  calc
    (2 : ℤ) • ∡ cfg.q cfg.q₁ cfg.a₂ = (2 : ℤ) • ∡ cfg.a₁ cfg.q₁ cfg.a₂ := by
      rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.a₁ cfg.C cfg.a₂ :=
      (cfg.cospherical_A₁Q₁CA₂.two_zsmul_oangle_eq cfg.sbtw_q_a₁_q₁.right_ne cfg.q₁_ne_a₂
        cfg.a₁_ne_c.symm cfg.a₂_ne_c.symm)
    _ = (2 : ℤ) • ∡ cfg.b cfg.C cfg.a₂ := by rw [cfg.sbtw_B_A₁_C.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.b cfg.A cfg.a₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.b_mem_circumsphere cfg.c_mem_circumsphere
        cfg.a_mem_circumsphere cfg.a₂_mem_circumsphere cfg.b_ne_c.symm cfg.a₂_ne_c.symm cfg.a_ne_b
        cfg.a₂_ne_a.symm)
    _ = (2 : ℤ) • ∡ cfg.q cfg.P cfg.a₂ := cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂.symm
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂

end Oriented

/-! ### Conclusions from that third angle chase -/


theorem q₁_mem_ω : cfg.q₁ ∈ cfg.ω :=
  haveI := some_orientation V
  Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) (by decide) cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂
#align imo2019_q2.imo2019q2_cfg.Q₁_mem_ω Imo2019Q2.Imo2019q2Cfg.q₁_mem_ω

theorem p₁_mem_ω : cfg.p₁ ∈ cfg.ω := by rw [← symm_ω]; exact cfg.symm.Q₁_mem_ω
#align imo2019_q2.imo2019q2_cfg.P₁_mem_ω Imo2019Q2.Imo2019q2Cfg.p₁_mem_ω

theorem result : Concyclic ({cfg.P, cfg.q, cfg.p₁, cfg.q₁} : Set Pt) := by
  refine' ⟨_, coplanar_of_fact_finrank_eq_two _⟩
  rw [cospherical_iff_exists_sphere]
  refine' ⟨cfg.ω, _⟩
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨cfg.P_mem_ω, cfg.Q_mem_ω, cfg.P₁_mem_ω, cfg.Q₁_mem_ω⟩
#align imo2019_q2.imo2019q2_cfg.result Imo2019Q2.Imo2019q2Cfg.result

end Imo2019q2Cfg

end imo2019_q2

open imo2019_q2

theorem imo2019_q2 (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
    (affine_independent_ABC : AffineIndependent ℝ ![A, B, C]) (wbtw_B_A₁_C : Wbtw ℝ B A₁ C)
    (wbtw_A_B₁_C : Wbtw ℝ A B₁ C) (wbtw_A_P_A₁ : Wbtw ℝ A P A₁) (wbtw_B_Q_B₁ : Wbtw ℝ B Q B₁)
    (PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]) (P_ne_Q : P ≠ Q)
    (sbtw_P_B₁_P₁ : Sbtw ℝ P B₁ P₁) (angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C)
    (C_ne_P₁ : C ≠ P₁) (sbtw_Q_A₁_Q₁ : Sbtw ℝ Q A₁ Q₁)
    (angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A) (C_ne_Q₁ : C ≠ Q₁) :
    Concyclic ({P, Q, P₁, Q₁} : Set Pt) :=
  (⟨A, B, C, A₁, B₁, P, Q, P₁, Q₁, affine_independent_ABC, wbtw_B_A₁_C, wbtw_A_B₁_C, wbtw_A_P_A₁,
        wbtw_B_Q_B₁, PQ_parallel_AB, P_ne_Q, sbtw_P_B₁_P₁, angle_PP₁C_eq_angle_BAC, C_ne_P₁,
        sbtw_Q_A₁_Q₁, angle_CQ₁Q_eq_angle_CBA, C_ne_Q₁⟩ :
      Imo2019q2Cfg V Pt).result
#align imo2019_q2 imo2019_q2

