/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

#align_import imo.imo2019_q2 from "leanprover-community/mathlib"@"308826471968962c6b59c7ff82a22757386603e3"

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
at all. Also note that (as described in `Geometry.Euclidean.Angle.Oriented.Basic`) the oriented
angles used are modulo `2 * π`, so parts of the angle chase that are only valid for angles modulo
`π` (as used in the informal solution) are represented as equalities of twice angles, which we write
as `(2 : ℤ) • ∡ _ _ _ = (2 : ℤ) • ∡ _ _ _`.
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
with them. A reference to a point being on a side or a segment is expressed directly with `Wbtw`
rather than more literally with `affineSegment`.
-/


open Affine Affine.Simplex EuclideanGeometry FiniteDimensional

open scoped Affine EuclideanGeometry Real

set_option linter.uppercaseLean3 false

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [hd2 : Fact (finrank ℝ V = 2)]

namespace Imo2019Q2

noncomputable section

/-- A configuration satisfying the conditions of the problem. We define this structure to avoid
passing many hypotheses around as we build up information about the configuration; the final
result for a statement of the problem not using this structure is then deduced from one in terms
of this structure. -/
structure Imo2019q2Cfg where
  (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  wbtw_B_A₁_C : Wbtw ℝ B A₁ C
  wbtw_A_B₁_C : Wbtw ℝ A B₁ C
  wbtw_A_P_A₁ : Wbtw ℝ A P A₁
  wbtw_B_Q_B₁ : Wbtw ℝ B Q B₁
  PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]
  -- A hypothesis implicit in the named line.
  P_ne_Q : P ≠ Q
  sbtw_P_B₁_P₁ : Sbtw ℝ P B₁ P₁
  angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C
  -- A hypothesis implicit in the first named angle.
  C_ne_P₁ : C ≠ P₁
  sbtw_Q_A₁_Q₁ : Sbtw ℝ Q A₁ Q₁
  angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A
  -- A hypothesis implicit in the first named angle.
  C_ne_Q₁ : C ≠ Q₁
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
  A := cfg.B
  B := cfg.A
  C := cfg.C
  A₁ := cfg.B₁
  B₁ := cfg.A₁
  P := cfg.Q
  Q := cfg.P
  P₁ := cfg.Q₁
  Q₁ := cfg.P₁
  affineIndependent_ABC := by
    rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 1)]
    convert cfg.affineIndependent_ABC using 1
    ext x
    fin_cases x <;> rfl
  wbtw_B_A₁_C := cfg.wbtw_A_B₁_C
  wbtw_A_B₁_C := cfg.wbtw_B_A₁_C
  wbtw_A_P_A₁ := cfg.wbtw_B_Q_B₁
  wbtw_B_Q_B₁ := cfg.wbtw_A_P_A₁
  PQ_parallel_AB := Set.pair_comm cfg.P cfg.Q ▸ Set.pair_comm cfg.A cfg.B ▸ cfg.PQ_parallel_AB
  P_ne_Q := cfg.P_ne_Q.symm
  sbtw_P_B₁_P₁ := cfg.sbtw_Q_A₁_Q₁
  angle_PP₁C_eq_angle_BAC :=
    angle_comm cfg.C cfg.Q₁ cfg.Q ▸ angle_comm cfg.C cfg.B cfg.A ▸ cfg.angle_CQ₁Q_eq_angle_CBA
  C_ne_P₁ := cfg.C_ne_Q₁
  sbtw_Q_A₁_Q₁ := cfg.sbtw_P_B₁_P₁
  angle_CQ₁Q_eq_angle_CBA :=
    angle_comm cfg.P cfg.P₁ cfg.C ▸ angle_comm cfg.B cfg.A cfg.C ▸ cfg.angle_PP₁C_eq_angle_BAC
  C_ne_Q₁ := cfg.C_ne_P₁
#align imo2019_q2.imo2019q2_cfg.symm Imo2019Q2.Imo2019q2Cfg.symm

/-! ### Configuration properties that are obvious from the diagram, and construction of the
points `A₂` and `B₂` -/


theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
#align imo2019_q2.imo2019q2_cfg.A_ne_B Imo2019Q2.Imo2019q2Cfg.A_ne_B

theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
#align imo2019_q2.imo2019q2_cfg.A_ne_C Imo2019Q2.Imo2019q2Cfg.A_ne_C

theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)
#align imo2019_q2.imo2019q2_cfg.B_ne_C Imo2019Q2.Imo2019q2Cfg.B_ne_C

theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC
#align imo2019_q2.imo2019q2_cfg.not_collinear_ABC Imo2019Q2.Imo2019q2Cfg.not_collinear_ABC

/-- `ABC` as a `Triangle`. -/
def triangleABC : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_ABC⟩
#align imo2019_q2.imo2019q2_cfg.triangle_ABC Imo2019Q2.Imo2019q2Cfg.triangleABC

theorem A_mem_circumsphere : cfg.A ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 0
#align imo2019_q2.imo2019q2_cfg.A_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.A_mem_circumsphere

theorem B_mem_circumsphere : cfg.B ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 1
#align imo2019_q2.imo2019q2_cfg.B_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.B_mem_circumsphere

theorem C_mem_circumsphere : cfg.C ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 2
#align imo2019_q2.imo2019q2_cfg.C_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.C_mem_circumsphere

theorem symm_triangleABC : cfg.symm.triangleABC = cfg.triangleABC.reindex (Equiv.swap 0 1) := by
  ext i; fin_cases i <;> rfl
#align imo2019_q2.imo2019q2_cfg.symm_triangle_ABC Imo2019Q2.Imo2019q2Cfg.symm_triangleABC

theorem symm_triangleABC_circumsphere :
    cfg.symm.triangleABC.circumsphere = cfg.triangleABC.circumsphere := by
  rw [symm_triangleABC, Affine.Simplex.circumsphere_reindex]
#align imo2019_q2.imo2019q2_cfg.symm_triangle_ABC_circumsphere Imo2019Q2.Imo2019q2Cfg.symm_triangleABC_circumsphere

/-- `A₂` is the second point of intersection of the ray `AA₁` with the circumcircle of `ABC`. -/
def A₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.A (cfg.A₁ -ᵥ cfg.A)
#align imo2019_q2.imo2019q2_cfg.A₂ Imo2019Q2.Imo2019q2Cfg.A₂

/-- `B₂` is the second point of intersection of the ray `BB₁` with the circumcircle of `ABC`. -/
def B₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.B (cfg.B₁ -ᵥ cfg.B)
#align imo2019_q2.imo2019q2_cfg.B₂ Imo2019Q2.Imo2019q2Cfg.B₂

theorem A₂_mem_circumsphere : cfg.A₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.A_mem_circumsphere
#align imo2019_q2.imo2019q2_cfg.A₂_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.A₂_mem_circumsphere

theorem B₂_mem_circumsphere : cfg.B₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.B_mem_circumsphere
#align imo2019_q2.imo2019q2_cfg.B₂_mem_circumsphere Imo2019Q2.Imo2019q2Cfg.B₂_mem_circumsphere

theorem symm_A₂ : cfg.symm.A₂ = cfg.B₂ := by simp_rw [A₂, B₂, symm_triangleABC_circumsphere]; rfl
#align imo2019_q2.imo2019q2_cfg.symm_A₂ Imo2019Q2.Imo2019q2Cfg.symm_A₂

theorem QP_parallel_BA : line[ℝ, cfg.Q, cfg.P] ∥ line[ℝ, cfg.B, cfg.A] := by
  rw [Set.pair_comm cfg.Q, Set.pair_comm cfg.B]; exact cfg.PQ_parallel_AB
#align imo2019_q2.imo2019q2_cfg.QP_parallel_BA Imo2019Q2.Imo2019q2Cfg.QP_parallel_BA

theorem A_ne_A₁ : cfg.A ≠ cfg.A₁ := by
  intro h
  have h' := cfg.not_collinear_ABC
  rw [h, Set.insert_comm] at h'
  exact h' cfg.wbtw_B_A₁_C.collinear
#align imo2019_q2.imo2019q2_cfg.A_ne_A₁ Imo2019Q2.Imo2019q2Cfg.A_ne_A₁

theorem collinear_PAA₁A₂ : Collinear ℝ ({cfg.P, cfg.A, cfg.A₁, cfg.A₂} : Set Pt) := by
  rw [A₂,
    (cfg.triangleABC.circumsphere.secondInter_collinear cfg.A cfg.A₁).collinear_insert_iff_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_A₁,
    Set.insert_comm]
  exact cfg.wbtw_A_P_A₁.collinear
#align imo2019_q2.imo2019q2_cfg.collinear_PAA₁A₂ Imo2019Q2.Imo2019q2Cfg.collinear_PAA₁A₂

theorem A₁_ne_C : cfg.A₁ ≠ cfg.C := by
  intro h
  have hsbtw := cfg.sbtw_Q_A₁_Q₁
  rw [h] at hsbtw
  have ha := hsbtw.angle₂₃₁_eq_zero
  rw [angle_CQ₁Q_eq_angle_CBA, angle_comm] at ha
  exact (angle_ne_zero_of_not_collinear cfg.not_collinear_ABC) ha
#align imo2019_q2.imo2019q2_cfg.A₁_ne_C Imo2019Q2.Imo2019q2Cfg.A₁_ne_C

theorem B₁_ne_C : cfg.B₁ ≠ cfg.C :=
  cfg.symm.A₁_ne_C
#align imo2019_q2.imo2019q2_cfg.B₁_ne_C Imo2019Q2.Imo2019q2Cfg.B₁_ne_C

theorem Q_not_mem_CB : cfg.Q ∉ line[ℝ, cfg.C, cfg.B] := by
  intro hQ
  have hQA₁ : line[ℝ, cfg.Q, cfg.A₁] ≤ line[ℝ, cfg.C, cfg.B] :=
    affineSpan_pair_le_of_mem_of_mem hQ cfg.wbtw_B_A₁_C.symm.mem_affineSpan
  have hQ₁ : cfg.Q₁ ∈ line[ℝ, cfg.C, cfg.B] := by
    rw [AffineSubspace.le_def'] at hQA₁
    exact hQA₁ _ cfg.sbtw_Q_A₁_Q₁.right_mem_affineSpan
  have hc : Collinear ℝ ({cfg.C, cfg.Q₁, cfg.Q} : Set Pt) :=
    haveI hc' : Collinear ℝ ({cfg.B, cfg.C, cfg.Q₁, cfg.Q} : Set Pt) := by
      rw [Set.insert_comm cfg.B, Set.insert_comm cfg.B, Set.pair_comm, Set.insert_comm cfg.C,
        Set.insert_comm cfg.C]
      exact collinear_insert_insert_of_mem_affineSpan_pair hQ₁ hQ
    hc'.subset (Set.subset_insert _ _)
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, cfg.angle_CQ₁Q_eq_angle_CBA,
    or_iff_right cfg.C_ne_Q₁, or_iff_right cfg.sbtw_Q_A₁_Q₁.left_ne_right, angle_comm] at hc
  exact cfg.not_collinear_ABC (hc.elim collinear_of_angle_eq_zero collinear_of_angle_eq_pi)
#align imo2019_q2.imo2019q2_cfg.Q_not_mem_CB Imo2019Q2.Imo2019q2Cfg.Q_not_mem_CB

theorem Q_ne_B : cfg.Q ≠ cfg.B := by
  intro h
  have h' := cfg.Q_not_mem_CB
  rw [h] at h'
  exact h' (right_mem_affineSpan_pair _ _ _)
#align imo2019_q2.imo2019q2_cfg.Q_ne_B Imo2019Q2.Imo2019q2Cfg.Q_ne_B

theorem sOppSide_CB_Q_Q₁ : line[ℝ, cfg.C, cfg.B].SOppSide cfg.Q cfg.Q₁ :=
  cfg.sbtw_Q_A₁_Q₁.sOppSide_of_not_mem_of_mem cfg.Q_not_mem_CB cfg.wbtw_B_A₁_C.symm.mem_affineSpan
#align imo2019_q2.imo2019q2_cfg.s_opp_side_CB_Q_Q₁ Imo2019Q2.Imo2019q2Cfg.sOppSide_CB_Q_Q₁

/-! ### Relate the orientations of different angles in the configuration -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem oangle_CQ₁Q_sign_eq_oangle_CBA_sign :
    (∡ cfg.C cfg.Q₁ cfg.Q).sign = (∡ cfg.C cfg.B cfg.A).sign := by
  rw [← cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right,
    cfg.sOppSide_CB_Q_Q₁.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ cfg.C cfg.B)
      cfg.wbtw_B_A₁_C.symm.mem_affineSpan,
    ← Real.Angle.sign_neg, ← oangle_rev,
    cfg.wbtw_B_A₁_C.oangle_sign_eq_of_ne_right cfg.Q cfg.A₁_ne_C, oangle_rotate_sign,
    cfg.wbtw_B_Q_B₁.oangle_eq_right cfg.Q_ne_B,
    cfg.wbtw_A_B₁_C.symm.oangle_sign_eq_of_ne_left cfg.B cfg.B₁_ne_C.symm]
#align imo2019_q2.imo2019q2_cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign Imo2019Q2.Imo2019q2Cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign

theorem oangle_CQ₁Q_eq_oangle_CBA : ∡ cfg.C cfg.Q₁ cfg.Q = ∡ cfg.C cfg.B cfg.A :=
  oangle_eq_of_angle_eq_of_sign_eq cfg.angle_CQ₁Q_eq_angle_CBA
    cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign
#align imo2019_q2.imo2019q2_cfg.oangle_CQ₁Q_eq_oangle_CBA Imo2019Q2.Imo2019q2Cfg.oangle_CQ₁Q_eq_oangle_CBA

end Oriented

/-! ### More obvious configuration properties -/


theorem A₁_ne_B : cfg.A₁ ≠ cfg.B := by
  intro h
  have hwbtw := cfg.wbtw_A_P_A₁
  rw [h] at hwbtw
  have hPQ : line[ℝ, cfg.P, cfg.Q] = line[ℝ, cfg.A, cfg.B] := by
    rw [AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair _ _ _)
      hwbtw.mem_affineSpan]
    exact cfg.PQ_parallel_AB.direction_eq
  haveI := someOrientation V
  have haQ : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A := by
    rw [Collinear.two_zsmul_oangle_eq_right _ cfg.A_ne_B cfg.Q_ne_B]
    rw [Set.pair_comm, Set.insert_comm]
    refine collinear_insert_of_mem_affineSpan_pair ?_
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
    hc.affineIndependent_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      hBQ₁ cfg.Q_ne_B.symm hQQ₁.symm
  rw [affineIndependent_iff_not_collinear_set] at hBQ₁Q
  refine hBQ₁Q ?_
  rw [← h, Set.pair_comm, Set.insert_comm]
  exact cfg.sbtw_Q_A₁_Q₁.wbtw.collinear
#align imo2019_q2.imo2019q2_cfg.A₁_ne_B Imo2019Q2.Imo2019q2Cfg.A₁_ne_B

theorem sbtw_B_A₁_C : Sbtw ℝ cfg.B cfg.A₁ cfg.C :=
  ⟨cfg.wbtw_B_A₁_C, cfg.A₁_ne_B, cfg.A₁_ne_C⟩
#align imo2019_q2.imo2019q2_cfg.sbtw_B_A₁_C Imo2019Q2.Imo2019q2Cfg.sbtw_B_A₁_C

theorem sbtw_A_B₁_C : Sbtw ℝ cfg.A cfg.B₁ cfg.C :=
  cfg.symm.sbtw_B_A₁_C
#align imo2019_q2.imo2019q2_cfg.sbtw_A_B₁_C Imo2019Q2.Imo2019q2Cfg.sbtw_A_B₁_C

theorem sbtw_A_A₁_A₂ : Sbtw ℝ cfg.A cfg.A₁ cfg.A₂ := by
  refine Sphere.sbtw_secondInter cfg.A_mem_circumsphere ?_
  convert cfg.sbtw_B_A₁_C.dist_lt_max_dist _
  change _ = max (dist (cfg.triangleABC.points 1) _) (dist (cfg.triangleABC.points 2) _)
  simp_rw [circumsphere_center, circumsphere_radius, dist_circumcenter_eq_circumradius, max_self]
#align imo2019_q2.imo2019q2_cfg.sbtw_A_A₁_A₂ Imo2019Q2.Imo2019q2Cfg.sbtw_A_A₁_A₂

theorem sbtw_B_B₁_B₂ : Sbtw ℝ cfg.B cfg.B₁ cfg.B₂ := by
  rw [← cfg.symm_A₂]; exact cfg.symm.sbtw_A_A₁_A₂
#align imo2019_q2.imo2019q2_cfg.sbtw_B_B₁_B₂ Imo2019Q2.Imo2019q2Cfg.sbtw_B_B₁_B₂

theorem A₂_ne_A : cfg.A₂ ≠ cfg.A :=
  cfg.sbtw_A_A₁_A₂.left_ne_right.symm
#align imo2019_q2.imo2019q2_cfg.A₂_ne_A Imo2019Q2.Imo2019q2Cfg.A₂_ne_A

theorem A₂_ne_P : cfg.A₂ ≠ cfg.P :=
  (cfg.sbtw_A_A₁_A₂.trans_wbtw_left_ne cfg.wbtw_A_P_A₁).symm
#align imo2019_q2.imo2019q2_cfg.A₂_ne_P Imo2019Q2.Imo2019q2Cfg.A₂_ne_P

theorem A₂_ne_B : cfg.A₂ ≠ cfg.B := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁
  refine cfg.not_collinear_ABC ?_
  have hc : Collinear ℝ ({cfg.A, cfg.C, cfg.B, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affineSpan
      cfg.sbtw_B_A₁_C.right_mem_affineSpan
  refine hc.subset ?_
  rw [Set.pair_comm _ cfg.A₁, Set.insert_comm _ cfg.A₁, Set.insert_comm _ cfg.A₁, Set.pair_comm]
  exact Set.subset_insert _ _
#align imo2019_q2.imo2019q2_cfg.A₂_ne_B Imo2019Q2.Imo2019q2Cfg.A₂_ne_B

theorem A₂_ne_C : cfg.A₂ ≠ cfg.C := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁
  refine cfg.not_collinear_ABC ?_
  have hc : Collinear ℝ ({cfg.A, cfg.B, cfg.C, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affineSpan
      cfg.sbtw_B_A₁_C.left_mem_affineSpan
  refine hc.subset (Set.insert_subset_insert (Set.insert_subset_insert ?_))
  rw [Set.singleton_subset_iff]
  exact Set.mem_insert _ _
#align imo2019_q2.imo2019q2_cfg.A₂_ne_C Imo2019Q2.Imo2019q2Cfg.A₂_ne_C

theorem B₂_ne_B : cfg.B₂ ≠ cfg.B := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_A
#align imo2019_q2.imo2019q2_cfg.B₂_ne_B Imo2019Q2.Imo2019q2Cfg.B₂_ne_B

theorem B₂_ne_Q : cfg.B₂ ≠ cfg.Q := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_P
#align imo2019_q2.imo2019q2_cfg.B₂_ne_Q Imo2019Q2.Imo2019q2Cfg.B₂_ne_Q

theorem B₂_ne_A₂ : cfg.B₂ ≠ cfg.A₂ := by
  intro h
  have hA : Sbtw ℝ (cfg.triangleABC.points 1) cfg.A₁ (cfg.triangleABC.points 2) := cfg.sbtw_B_A₁_C
  have hB : Sbtw ℝ (cfg.triangleABC.points 0) cfg.B₁ (cfg.triangleABC.points 2) := cfg.sbtw_A_B₁_C
  have hA' : cfg.A₂ ∈ line[ℝ, cfg.triangleABC.points 0, cfg.A₁] :=
    Sphere.secondInter_vsub_mem_affineSpan _ _ _
  have hB' : cfg.A₂ ∈ line[ℝ, cfg.triangleABC.points 1, cfg.B₁] := by
    rw [← h]; exact Sphere.secondInter_vsub_mem_affineSpan _ _ _
  exact (sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair (by decide) hA hB hA' hB').symm.not_rotate
    cfg.sbtw_A_A₁_A₂.wbtw
#align imo2019_q2.imo2019q2_cfg.B₂_ne_A₂ Imo2019Q2.Imo2019q2Cfg.B₂_ne_A₂

theorem wbtw_B_Q_B₂ : Wbtw ℝ cfg.B cfg.Q cfg.B₂ :=
  cfg.sbtw_B_B₁_B₂.wbtw.trans_left cfg.wbtw_B_Q_B₁
#align imo2019_q2.imo2019q2_cfg.wbtw_B_Q_B₂ Imo2019Q2.Imo2019q2Cfg.wbtw_B_Q_B₂

/-! ### The first equality in the first angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ := by
  refine two_zsmul_oangle_of_parallel cfg.QP_parallel_BA ?_
  convert AffineSubspace.Parallel.refl (k := ℝ) (P := Pt) _ using 1
  rw [cfg.collinear_PAA₁A₂.affineSpan_eq_of_ne (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A₂_ne_A,
      cfg.collinear_PAA₁A₂.affineSpan_eq_of_ne (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    (Set.mem_insert _ _) cfg.A₂_ne_P]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂

end Oriented

/-! ### More obvious configuration properties -/


theorem not_collinear_QPA₂ : ¬Collinear ℝ ({cfg.Q, cfg.P, cfg.A₂} : Set Pt) := by
  haveI := someOrientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂, ←
    affineIndependent_iff_not_collinear_set]
  have h : Cospherical ({cfg.B, cfg.A, cfg.A₂} : Set Pt) := by
    refine cfg.triangleABC.circumsphere.cospherical.subset ?_
    simp only [Set.insert_subset_iff, cfg.A_mem_circumsphere, cfg.B_mem_circumsphere,
      cfg.A₂_mem_circumsphere, Sphere.mem_coe, Set.singleton_subset_iff, and_true]
  exact h.affineIndependent_of_ne cfg.A_ne_B.symm cfg.A₂_ne_B.symm cfg.A₂_ne_A.symm
#align imo2019_q2.imo2019q2_cfg.not_collinear_QPA₂ Imo2019Q2.Imo2019q2Cfg.not_collinear_QPA₂

theorem Q₁_ne_A₂ : cfg.Q₁ ≠ cfg.A₂ := by
  intro h
  have h₁ := cfg.sbtw_Q_A₁_Q₁
  rw [h] at h₁
  refine cfg.not_collinear_QPA₂ ?_
  have hA₂ := cfg.sbtw_A_A₁_A₂.right_mem_affineSpan
  have hA₂A₁ : line[ℝ, cfg.A₂, cfg.A₁] ≤ line[ℝ, cfg.A, cfg.A₁] :=
    affineSpan_pair_le_of_left_mem hA₂
  have hQ : cfg.Q ∈ line[ℝ, cfg.A, cfg.A₁] := by
    rw [AffineSubspace.le_def'] at hA₂A₁
    exact hA₂A₁ _ h₁.left_mem_affineSpan
  exact collinear_triple_of_mem_affineSpan_pair hQ cfg.wbtw_A_P_A₁.mem_affineSpan hA₂
#align imo2019_q2.imo2019q2_cfg.Q₁_ne_A₂ Imo2019Q2.Imo2019q2Cfg.Q₁_ne_A₂

theorem affineIndependent_QPA₂ : AffineIndependent ℝ ![cfg.Q, cfg.P, cfg.A₂] :=
  affineIndependent_iff_not_collinear_set.2 cfg.not_collinear_QPA₂
#align imo2019_q2.imo2019q2_cfg.affine_independent_QPA₂ Imo2019Q2.Imo2019q2Cfg.affineIndependent_QPA₂

theorem affineIndependent_PQB₂ : AffineIndependent ℝ ![cfg.P, cfg.Q, cfg.B₂] := by
  rw [← symm_A₂]; exact cfg.symm.affineIndependent_QPA₂
#align imo2019_q2.imo2019q2_cfg.affine_independent_PQB₂ Imo2019Q2.Imo2019q2Cfg.affineIndependent_PQB₂

/-- `QPA₂` as a `Triangle`. -/
def triangleQPA₂ : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_QPA₂⟩
#align imo2019_q2.imo2019q2_cfg.triangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.triangleQPA₂

/-- `PQB₂` as a `Triangle`. -/
def trianglePQB₂ : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_PQB₂⟩
#align imo2019_q2.imo2019q2_cfg.triangle_PQB₂ Imo2019Q2.Imo2019q2Cfg.trianglePQB₂

theorem symm_triangleQPA₂ : cfg.symm.triangleQPA₂ = cfg.trianglePQB₂ := by
  simp_rw [trianglePQB₂, ← symm_A₂]; ext i; fin_cases i <;> rfl
#align imo2019_q2.imo2019q2_cfg.symm_triangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.symm_triangleQPA₂

/-- `ω` is the circle containing `Q`, `P` and `A₂`, which will be shown also to contain `B₂`,
`P₁` and `Q₁`. -/
def ω : Sphere Pt :=
  cfg.triangleQPA₂.circumsphere
#align imo2019_q2.imo2019q2_cfg.ω Imo2019Q2.Imo2019q2Cfg.ω

theorem P_mem_ω : cfg.P ∈ cfg.ω :=
  cfg.triangleQPA₂.mem_circumsphere 1
#align imo2019_q2.imo2019q2_cfg.P_mem_ω Imo2019Q2.Imo2019q2Cfg.P_mem_ω

theorem Q_mem_ω : cfg.Q ∈ cfg.ω :=
  cfg.triangleQPA₂.mem_circumsphere 0
#align imo2019_q2.imo2019q2_cfg.Q_mem_ω Imo2019Q2.Imo2019q2Cfg.Q_mem_ω

/-! ### The rest of the first angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ :=
  calc
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :=
      cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂
    _ = (2 : ℤ) • ∡ cfg.B cfg.B₂ cfg.A₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.A_mem_circumsphere
        cfg.B₂_mem_circumsphere cfg.A₂_mem_circumsphere cfg.A_ne_B cfg.A₂_ne_A.symm cfg.B₂_ne_B
        cfg.B₂_ne_A₂)
    _ = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ := by
      rw [cfg.wbtw_B_Q_B₂.symm.oangle_eq_left cfg.B₂_ne_Q.symm]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂

end Oriented

/-! ### Conclusions from that first angle chase -/


theorem cospherical_QPB₂A₂ : Cospherical ({cfg.Q, cfg.P, cfg.B₂, cfg.A₂} : Set Pt) :=
  haveI := someOrientation V
  cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ cfg.not_collinear_QPA₂
#align imo2019_q2.imo2019q2_cfg.cospherical_QPB₂A₂ Imo2019Q2.Imo2019q2Cfg.cospherical_QPB₂A₂

theorem symm_ω_eq_trianglePQB₂_circumsphere : cfg.symm.ω = cfg.trianglePQB₂.circumsphere := by
  rw [ω, symm_triangleQPA₂]
#align imo2019_q2.imo2019q2_cfg.symm_ω_eq_triangle_PQB₂_circumsphere Imo2019Q2.Imo2019q2Cfg.symm_ω_eq_trianglePQB₂_circumsphere

theorem symm_ω : cfg.symm.ω = cfg.ω := by
  rw [symm_ω_eq_trianglePQB₂_circumsphere, ω]
  refine circumsphere_eq_of_cospherical hd2.out cfg.cospherical_QPB₂A₂ ?_ ?_
  · simp only [trianglePQB₂, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_emptyc_eq]
    rw [Set.insert_comm]
    refine Set.insert_subset_insert (Set.insert_subset_insert ?_)
    simp
  · simp only [triangleQPA₂, Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_emptyc_eq]
    refine Set.insert_subset_insert (Set.insert_subset_insert ?_)
    simp
#align imo2019_q2.imo2019q2_cfg.symm_ω Imo2019Q2.Imo2019q2Cfg.symm_ω

/-! ### The second angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA :
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A := by
      rw [cfg.sbtw_A_A₁_A₂.symm.oangle_eq_right]
    _ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
      Sphere.two_zsmul_oangle_eq cfg.C_mem_circumsphere cfg.A₂_mem_circumsphere
        cfg.B_mem_circumsphere cfg.A_mem_circumsphere cfg.A₂_ne_C cfg.A₂_ne_A cfg.B_ne_C
        cfg.A_ne_B.symm
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA

theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ :
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
      cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA
    _ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q := by rw [oangle_CQ₁Q_eq_oangle_CBA]
    _ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ := by rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right]
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁

end Oriented

/-! ### Conclusions from that second angle chase -/


theorem not_collinear_CA₂A₁ : ¬Collinear ℝ ({cfg.C, cfg.A₂, cfg.A₁} : Set Pt) := by
  haveI := someOrientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA,
    Set.pair_comm, Set.insert_comm, Set.pair_comm]
  exact cfg.not_collinear_ABC
#align imo2019_q2.imo2019q2_cfg.not_collinear_CA₂A₁ Imo2019Q2.Imo2019q2Cfg.not_collinear_CA₂A₁

theorem cospherical_A₁Q₁CA₂ : Cospherical ({cfg.A₁, cfg.Q₁, cfg.C, cfg.A₂} : Set Pt) := by
  haveI := someOrientation V
  rw [Set.insert_comm cfg.Q₁, Set.insert_comm cfg.A₁, Set.pair_comm, Set.insert_comm cfg.A₁,
    Set.pair_comm]
  exact cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ cfg.not_collinear_CA₂A₁
#align imo2019_q2.imo2019q2_cfg.cospherical_A₁Q₁CA₂ Imo2019Q2.Imo2019q2Cfg.cospherical_A₁Q₁CA₂

/-! ### The third angle chase in the solution -/


section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

theorem two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ :=
  calc
    (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.A₁ cfg.Q₁ cfg.A₂ := by
      rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.A₁ cfg.C cfg.A₂ :=
      (cfg.cospherical_A₁Q₁CA₂.two_zsmul_oangle_eq cfg.sbtw_Q_A₁_Q₁.right_ne cfg.Q₁_ne_A₂
        cfg.A₁_ne_C.symm cfg.A₂_ne_C.symm)
    _ = (2 : ℤ) • ∡ cfg.B cfg.C cfg.A₂ := by rw [cfg.sbtw_B_A₁_C.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.C_mem_circumsphere
        cfg.A_mem_circumsphere cfg.A₂_mem_circumsphere cfg.B_ne_C.symm cfg.A₂_ne_C.symm cfg.A_ne_B
        cfg.A₂_ne_A.symm)
    _ = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ := cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂.symm
#align imo2019_q2.imo2019q2_cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ Imo2019Q2.Imo2019q2Cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂

end Oriented

/-! ### Conclusions from that third angle chase -/


theorem Q₁_mem_ω : cfg.Q₁ ∈ cfg.ω :=
  haveI := someOrientation V
  Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) (by decide) cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂
#align imo2019_q2.imo2019q2_cfg.Q₁_mem_ω Imo2019Q2.Imo2019q2Cfg.Q₁_mem_ω

theorem P₁_mem_ω : cfg.P₁ ∈ cfg.ω := by rw [← symm_ω]; exact cfg.symm.Q₁_mem_ω
#align imo2019_q2.imo2019q2_cfg.P₁_mem_ω Imo2019Q2.Imo2019q2Cfg.P₁_mem_ω

theorem result : Concyclic ({cfg.P, cfg.Q, cfg.P₁, cfg.Q₁} : Set Pt) := by
  refine ⟨?_, coplanar_of_fact_finrank_eq_two _⟩
  rw [cospherical_iff_exists_sphere]
  refine ⟨cfg.ω, ?_⟩
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨cfg.P_mem_ω, cfg.Q_mem_ω, cfg.P₁_mem_ω, cfg.Q₁_mem_ω⟩
#align imo2019_q2.imo2019q2_cfg.result Imo2019Q2.Imo2019q2Cfg.result

end Imo2019q2Cfg

end

end Imo2019Q2

open Imo2019Q2

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
