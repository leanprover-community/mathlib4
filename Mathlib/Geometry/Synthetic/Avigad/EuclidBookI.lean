/-
Copyright (c) 2023 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet
-/
import Mathlib.Geometry.Synthetic.Avigad.Tactics
import Mathlib.Tactic.WLOG

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we prove the Pythagorean theorem (Euclid I.47) using Avigad's axioms for synthetic
geometry.
-/

variable [I : IncidenceGeometry] {a a1 a2 b b1 b2 c d e f g h i j k l m n o p q s x y :
  IncidenceGeometry.Point} {L M N O P Q R S T U W V X : IncidenceGeometry.Line}
  {α β : IncidenceGeometry.Circle} {r : ℝ}
namespace IncidenceGeometry

-------------------------------------------------- new  API ----------------------------------------
theorem ne_23_of_B (Babc : B a b c) : b ≠ c := (ne_12_of_B $ B_symm Babc).symm

theorem online_of_line L : ∃ a, OnLine a L := by
  rcases more_pts ∅ Set.finite_empty with ⟨a, -⟩
  exact Classical.by_cases (fun aL => by use a)
    (fun aL => by rcases diffSide_of_not_onLine aL with ⟨b, -, abL⟩; rcases line_of_pts a b with
      ⟨M, aM, bM⟩; rcases pt_of_linesInter (lines_inter_of_not_sameSide aM bM abL) with
      ⟨c, cL, -⟩; exact ⟨c, cL⟩)

theorem online_ne_of_line L : ∃ a b, a ≠ b ∧ OnLine  a L ∧ OnLine  b L := by
  rcases online_of_line L with ⟨a, aL⟩; rcases more_pts {a} (Set.finite_singleton a) with ⟨b, hb⟩;
  rcases circle_of_ne $ ne_of_mem_of_not_mem (Set.mem_singleton a) hb with ⟨α, acen, -⟩;
  rcases pts_of_lineCircleInter (lineCircleInter_of_inside_onLine aL
  (inside_circle_of_center acen)) with ⟨c, d, cd, cL, dL, -, -⟩; exact ⟨c, d, cd, cL, dL⟩

theorem online_ne_of_point_line a L : ∃ b, a ≠ b ∧ OnLine b L := by
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  by_cases c = a; use b; rw[h] at bc; exact ⟨bc.symm, bL⟩
  use c; exact ⟨Ne.symm h, cL⟩

lemma len_pos_of_nq (ab : a ≠ b) : 0 < length a b :=
  (Ne.symm (not_imp_not.mpr length_eq_zero_iff.mp ab)).le_iff_lt.mp (length_nonneg a b)

theorem ne_of_ne_len (ab : a ≠ b) (ab_cd : length a b = length c d) : c ≠ d :=
  fun ac => by linarith[length_eq_zero_iff.mpr ac, len_pos_of_nq ab]

theorem ne_of_ne_len' (cd : c ≠ d) (ab_cd : length a b = length c d) : a ≠ b :=
  ne_of_ne_len cd (ab_cd.symm)

theorem length_sum_perm_of_B (Babc : B a b c) : 0 < length a b ∧ 0 < length b c ∧
    0 < length a c ∧ length a b + length b c = length a c := by
  splitAll; exact len_pos_of_nq $ ne_12_of_B Babc; exact len_pos_of_nq $ ne_23_of_B Babc
  exact len_pos_of_nq $ ne_13_of_B Babc; exact length_sum_of_B Babc

theorem not_online_of_line L : ∃ a, ¬OnLine a L := by
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  rcases circle_of_ne bc with ⟨α, bα, cα⟩
  rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩
  rcases pts_of_circlesInter (circlesInter_of_inside_on_circle cα bβ (inside_circle_of_center
     bα) (inside_circle_of_center cβ)) with ⟨a, -, -, aα, aβ, -, -⟩
  have bc_ba := (on_circle_iff_length_eq bα cα).mpr aα
  have cb_ca := (on_circle_iff_length_eq cβ bβ).mpr aβ
  refine ⟨a, fun aL => (by push_neg; splitAll; all_goals exact (fun Bet =>
    by linarith[length_sum_perm_of_B Bet]) : ¬ (B b c a ∨ B c b a ∨ B b a c)) $
    B_of_three_onLine_ne bc (ne_of_ne_len bc bc_ba) (ne_of_ne_len bc.symm cb_ca) bL cL aL⟩

theorem online_of_circlesinter (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (αβ : CirclesInter α β) : ∃ c L, OnLine a L ∧ OnLine b L ∧ OnCircle c α ∧
    OnCircle c β ∧ ¬OnLine c L := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases not_online_of_line L with ⟨d, dL⟩;
  rcases pt_sameSide_of_circlesInter aL bL dL aα bβ αβ with ⟨c, cdL, cα, cβ⟩;
  exact ⟨c, L, aL, bL, cα, cβ, not_onLine_of_sameSide cdL⟩

theorem not_sameSide_symm (abL : ¬SameSide a b L) : ¬SameSide b a L := fun baL =>
  abL (sameSide_symm baL)

lemma DiffSide_symm (abL : DiffSide a b L) : DiffSide b a L :=
  ⟨abL.2.1, abL.1, (not_sameSide_symm abL.2.2)⟩

theorem DiffSide_of_sameside_DiffSide (abL : SameSide a b L) (acL : DiffSide a c L) :
    DiffSide b c L := by
by_contra h; unfold DiffSide at h; push_neg at h; exact acL.2.2
 (sameSide_trans (sameSide_symm abL) (h (not_onLine_of_sameSide (sameSide_symm abL)) acL.2.1))

theorem sameside_of_DiffSide_DiffSide (abL : DiffSide a b L) (acL : DiffSide a c L) :
    SameSide b c L := (or_iff_right acL.2.2).mp
  (sameSide_or_of_diffSide abL.1 abL.2.1 acL.2.1 abL.2.2)

theorem DiffSide_of_circlesinter (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (αβ : CirclesInter α β) : ∃ c d L, OnLine a L ∧ OnLine b L ∧ OnCircle c α ∧
    OnCircle c β ∧ OnCircle d α ∧ OnCircle d β ∧ DiffSide c d L := by
rcases online_of_circlesinter aα bβ αβ with ⟨c, L, aL, bL, cα, cβ, cL⟩;
rcases diffSide_of_not_onLine cL with ⟨e, eL, ceL⟩; rcases pt_sameSide_of_circlesInter aL bL eL
 aα bβ αβ with ⟨d, deL, dα, dβ⟩; exact ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, DiffSide_symm
 (DiffSide_of_sameside_DiffSide (sameSide_symm deL) ⟨eL, cL, not_sameSide_symm ceL⟩)⟩

theorem online_of_col_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (col_abc : Colinear a b c) : OnLine c L :=
by rcases col_abc with ⟨L, aM, bM, cM⟩; rwa [line_unique_of_pts ab aM bM aL bL] at cM

theorem Triangle_of_ne_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (cL : ¬OnLine c L) :
    Triangle a b c := fun col => by exact cL (online_of_col_online ab aL bL col)

theorem online_3_of_Triangle (aL : OnLine a L) (bL : OnLine b L) (tri_abc : Triangle a b c) :
    ¬OnLine c L := fun cL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_1_of_Triangle (bL : OnLine b L) (cL : OnLine c L) (tri_abc : Triangle a b c) :
    ¬OnLine a L := fun aL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_2_of_Triangle (aL : OnLine a L) (cL : OnLine c L) (tri_abc : Triangle a b c) :
    ¬OnLine b L := fun bL => tri_abc ⟨L, aL, bL, cL⟩

theorem EqTri_of_length_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (cL : ¬OnLine c L)
    (ab_ac : length a b = length a c) (bc_ba : length b c = length b a) : EqTri a b c :=
⟨Triangle_of_ne_online ab aL bL cL, by perma, by linperm, by linperm⟩

theorem B_circ_of_ne (ab : a ≠ b) (bc : b ≠ c) : ∃ d α, B a b d ∧
    CenterCircle b α ∧ OnCircle c α ∧ OnCircle d α := by
rcases circle_of_ne bc with ⟨α, bα, cα⟩; rcases pt_oncircle_of_inside_ne ab
 (inside_circle_of_center bα) with ⟨d, Babd, dα⟩; exact ⟨d, α, Babd, bα, cα, dα⟩

theorem online_of_eq (ab : a = b) (aL : OnLine a L) : OnLine b L := by rwa [ab] at aL

theorem online_of_eq' (ab : a = b) (bL : OnLine b L) : OnLine a L := by rwa [ab.symm] at bL

theorem ne_12_of_tri (tri: Triangle a b c) : a ≠ b :=
  fun ac => by rcases line_of_pts a c with ⟨L, aL, cL⟩; exact tri ⟨L, aL, online_of_eq ac aL, cL⟩

theorem ne_21_of_tri (tri : Triangle a b c) : b ≠ a := Ne.symm $ ne_12_of_tri tri

theorem ne_23_of_tri (tri: Triangle a b c) : b ≠ c :=
  fun bc => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq bc bL⟩

theorem ne_32_of_tri (tri : Triangle a b c) : c ≠ b := fun cb => (ne_23_of_tri tri) cb.symm

theorem ne_13_of_tri (tri : Triangle a b c) : a ≠ c :=
  fun ac => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq ac aL⟩

theorem ne_31_of_tri (tri : Triangle a b c) : c ≠ a := fun ca => (ne_13_of_tri tri) ca.symm

theorem incirc_of_lt (aα : CenterCircle a α) (bα : OnCircle b α)
    (ac_ab : length a c < length a b) : InCircle c α := (in_circle_iff_length_lt aα bα).mp ac_ab

theorem B_circ_out_of_B (ab : a ≠ b) (Bacd : B a c d) (ab_ac : length a b = length a c) :
    ∃ e α, B a b e ∧ CenterCircle a α ∧ OnCircle d α ∧ OnCircle e α := by
  rcases circle_of_ne (ne_13_of_B Bacd) with ⟨α, aα, dα⟩;
  rcases pt_oncircle_of_inside_ne ab (incirc_of_lt aα dα (by linarith[length_sum_perm_of_B Bacd] :
  length a b < length a d)) with ⟨e, Babe, eα⟩; exact ⟨e, α, Babe, aα, dα, eα⟩

theorem length_eq_of_oncircle (aα : CenterCircle a α) (bα : OnCircle b α) (cα : OnCircle c α) :
    length a b = length a c := (on_circle_iff_length_eq aα bα).mpr cα

theorem on_circle_of_oncircle_length (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_ac : length a b ≠ length a c) : ¬OnCircle c α :=
  fun cα => ab_ac (length_eq_of_oncircle aα bα cα)

theorem incircle_of_on_circle_length (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_ac : length a b ≤ length a c) : ¬InCircle c α :=
fun c_in_α => by linarith[(in_circle_iff_length_lt aα bα).mpr c_in_α]

theorem length_eq_of_B_B (Bdbe: B d b e) (Bdaf : B d a f) (da_db : length d a = length d b)
    (de_df : length d e = length d f):
length a f = length b e := by linarith[length_sum_perm_of_B Bdbe, length_sum_perm_of_B Bdaf]

theorem B_oncircle_of_inside_outside (a_in_α : InCircle a α) (b_out_α : OutCircle b α) :
    ∃ c, B a c b ∧ OnCircle c α := pt_on_circle_of_inside_outside b_out_α.1 a_in_α b_out_α.2

theorem OutCircle_of_lt (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_lt_ac : length a b < length a c) : OutCircle c α := ⟨on_circle_of_oncircle_length aα bα
  (by linarith), incircle_of_on_circle_length aα bα (by linarith)⟩

theorem sss (ab_de : length a b = length d e) (bc_ef : length b c = length e f)
    (ac_df : length a c = length d f) : angle a b c = angle d e f ∧ angle b a c = angle e d f
    ∧ angle a c b = angle d f e := ⟨(SAS_iff_SSS (by linperm) bc_ef).mpr ac_df,
  (SAS_iff_SSS ab_de ac_df).mpr bc_ef, (SAS_iff_SSS (by linperm) (by linperm)).mpr ab_de⟩

theorem sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
    (Abac : angle b a c = angle e d f) : length b c = length e f ∧ angle a b c = angle d e f ∧
    angle a c b = angle d f e := ⟨(SAS_iff_SSS ab_de ac_df).1 Abac, (sss ab_de ((SAS_iff_SSS ab_de
  ac_df).1 Abac) ac_df).1, (sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).2.2⟩

theorem tri132_of_tri123 (tri_abc : Triangle a b c) : Triangle a c b :=
  fun col => by unfold Colinear at col; simp_rw [And.comm] at col; exact tri_abc col

theorem tri231_of_tri123 (tri_abc : Triangle a b c) : Triangle b c a :=
  fun col => by rcases col with ⟨L, bL, cL, aL⟩; exact tri_abc ⟨L, aL, bL, cL⟩

theorem tri312 (tri_abc : Triangle a b c) : Triangle c a b :=
  tri231_of_tri123 $ tri231_of_tri123 $ tri_abc

theorem tri213 (tri_abc : Triangle a b c) : Triangle b a c :=
  tri132_of_tri123 $ tri231_of_tri123 $ tri_abc

theorem tri321 (tri_abc : Triangle a b c) : Triangle c b a := tri132_of_tri123 $ tri312 tri_abc

theorem area_eq_of_sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
    (Abac_Aedf : angle b a c = angle e d f) : area a b c = area d e f :=
  area_eq_of_SSS ab_de ac_df (sas ab_de ac_df Abac_Aedf).1

theorem angle_extension_of_B (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩;
  refine angle_extension ((ne_12_of_B Babb1).symm) ((ne_13_of_B Babb1).symm) ac.symm ac.symm aL bL
    (onLine_3_of_B Babb1 aL bL) aM cM cM (not_B_of_B Babb1) $ fun Bcac => (ne_13_of_B Bcac) rfl

theorem area_add_of_B (Babc : B a b c) (tri_dac : Triangle d a c) :
    area d a b + area d c b = area d a c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; have cL := onLine_3_of_B Babc aL bL
exact (area_add_iff_B (ne_12_of_B Babc) (ne_23_of_B Babc) (Ne.symm (ne_13_of_B Babc)) aL bL cL
  (online_1_of_Triangle aL cL tri_dac)).mp Babc

theorem area_add_of_B_offline (Babc : B a b c) (aL : OnLine a L) (cL : OnLine c L)
    (dL : ¬OnLine d L) : area d a b + area d c b = area d a c :=
area_add_of_B Babc $ by perma[Triangle_of_ne_online (ne_13_of_B Babc) aL cL dL]

theorem col_of_area_zero_ne (ab : a ≠ b) (area_abc : area a b c = 0) : Colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact ⟨L, aL, bL, (area_zero_iff_onLine ab aL bL).mp area_abc⟩

theorem col_132_of_col (col_123 : Colinear a b c) : Colinear a c b := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, bL⟩

theorem col_213_of_col (col_123 : Colinear a b c) : Colinear b a c := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, bL, aL, cL⟩

theorem col_312 (col : Colinear a b c) : Colinear c a b := by
  rcases col with ⟨L, aL, bL, cL⟩; exact ⟨L, cL, aL, bL⟩

theorem col_134_of_col_123_col_124 (ab : a ≠ b) (col_123 : Colinear a b c)
    (col_124 : Colinear a b d) : Colinear a c d := by
rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, online_of_col_online ab aL bL col_124⟩

theorem tri_143_of_tri_col (ad : a ≠ d) (tri_abc : Triangle a b c) (col_abd : Colinear a b d) :
    Triangle a d c := fun col_adc => by rcases col_abd with ⟨L, aL, bL, dL⟩; exact tri_abc
                                          ⟨L, aL, bL, online_of_col_online ad aL dL col_adc⟩

theorem col_of_B (Babc : B a b c) : Colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact ⟨L, aL, bL, onLine_3_of_B Babc aL bL⟩

theorem pt_inter_of_not_sameside (abL : ¬SameSide a b L) :
    ∃ c M, OnLine a M ∧ OnLine b M ∧ OnLine c M ∧ OnLine c L := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases pt_of_linesInter $ lines_inter_of_not_sameSide
    aM bM abL with ⟨c, cL, cM⟩; refine ⟨c, M, aM, bM, cM, cL⟩

theorem ne_of_DiffSide (abL : DiffSide a b L) : a ≠ b :=
  fun ab => by rw [ab] at abL; exact abL.2.2 $ sameSide_rfl_of_not_onLine abL.1

theorem ne_of_online (aL : OnLine a L) (bL : ¬OnLine b L) : a ≠ b :=
  fun ab => by rw [ab] at aL; exact bL aL

theorem ne_of_online' (aL : OnLine a L) (bL : ¬OnLine b L) : b ≠ a :=
  fun ab => by rw [←ab] at aL; exact bL aL

theorem ne_line_of_online (bM : OnLine b M) (bL : ¬OnLine b L) : L ≠ M :=
  fun LM => by rw [←LM] at bM; exact bL bM

theorem ne_line_of_online' (bM : OnLine b M) (bL : ¬OnLine b L) : M ≠ L :=
  Ne.symm $ ne_line_of_online bM bL

theorem pt_B_of_DiffSide (abL : DiffSide a b L) : ∃ c, OnLine c L ∧ B a c b := by
  rcases pt_inter_of_not_sameside abL.2.2 with ⟨c, M, aM, bM, cM, cL⟩
  refine ⟨c, cL, B_of_onLine_inter (Ne.symm $ ne_of_online cL abL.1) (ne_of_online cL abL.2.1)
    (ne_of_DiffSide abL) (Ne.symm $ ne_line_of_online bM abL.2.1) aM cM bM cL abL.2.2⟩

theorem B_of_three_col_ne (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (col_abc : Colinear a b c) :
    B a b c ∨ B b a c ∨ B a c b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact B_of_three_onLine_ne ab ac bc aL bL cL

theorem B_of_length_eq_col (ab : a ≠ b) (ac : a ≠ c) (col_abc : Colinear a b c)
    (ab_cb : length a b = length c b) : B a b c := by
  rcases B_of_three_col_ne ab ac (ne_of_ne_len ab $ by linperm) col_abc
    with Babc | Bet | Bet; exact Babc; repeat {linperm[length_sum_perm_of_B Bet]}

theorem length_zero_of_eq (ab : a = b) : length a b = 0 := (length_eq_zero_iff).mpr ab

theorem eq_of_length_zero (ab_0 : length a b = 0) : a = b := (length_eq_zero_iff).mp ab_0

theorem ne_of_Triangle_length_eq (tri_abc : Triangle a b c) (bd_cd : length b d = length c d) :
    b ≠ d := fun bd => ne_23_of_tri tri_abc $ bd.trans (eq_of_length_zero $ bd_cd.symm.trans $
      length_zero_of_eq bd).symm

theorem angle_extension_of_B' (ac : a ≠ c) (Babb1 : B a b b1) : angle c a b = angle c a b1 :=
  by perma[angle_extension_of_B ac Babb1]

theorem online_of_B_online (Babc : B a b c) (aL : OnLine a L) (cL : ¬OnLine c L) : ¬OnLine b L :=
  fun bL => cL (onLine_3_of_B Babc aL bL)

theorem online_of_B_online' (Babc : B a b c) (bL : OnLine b L) (cL : ¬OnLine c L) : ¬OnLine a L :=
  fun aL => cL (onLine_3_of_B Babc aL bL)

theorem online_of_B_online'' (Babc : B a b c) (aL : OnLine a L) (bL : ¬OnLine b L) : ¬OnLine c L :=
  fun cL => bL (onLine_2_of_B Babc aL cL)

theorem sameside_of_B_online_3 (Babc : B a b c) (aL : OnLine a L) (cL : ¬OnLine c L) :
    SameSide b c L := sameSide_of_B_not_onLine_2 Babc aL $ online_of_B_online Babc aL cL

theorem ne_of_sameside (bL : OnLine b L) (acL : SameSide a c L) : a ≠ b :=
  (ne_of_online bL (not_onLine_of_sameSide acL)).symm

theorem ne_of_sameside' (cL : OnLine c L) (abL : SameSide a b L) : c ≠ a :=
  ne_of_online cL $ not_onLine_of_sameSide abL

theorem tri_of_B_B_tri (Babd : B a b d) (Bace : B a c e) (tri_abc : Triangle a b c) :
    Triangle a d e := tri132_of_tri123 $ tri_143_of_tri_col (ne_13_of_B Bace) (tri132_of_tri123 $
  tri_143_of_tri_col (ne_13_of_B Babd) tri_abc $ col_of_B Babd) $ col_of_B Bace

theorem ne_21_of_B (Babc : B a b c) : b ≠ a := Ne.symm $ ne_12_of_B Babc

theorem ne_32_of_B (Babc : B a b c) : c ≠ b := Ne.symm $ ne_23_of_B Babc

theorem ne_31_of_B (Babc : B a b c) : c ≠ a := Ne.symm $ ne_13_of_B Babc

theorem sameSide_or_of_diffSide' (cL : ¬OnLine c L) (abL : DiffSide a b L) :
    SameSide a c L ∨ SameSide b c L := sameSide_or_of_diffSide abL.1 abL.2.1 cL abL.2.2

theorem rightangle_of_angle_eq (Babc : B a b c) (aL : OnLine a L) (cL : OnLine c L)
    (dL : ¬OnLine d L) (dba_dbc : angle d b a = angle d b c) :
    angle d b a = rightangle ∧ angle d b c = rightangle := by
  have ang := (angle_eq_iff_rightangle aL cL dL Babc).mp $ by perma[dba_dbc]
  exact ⟨by perma[ang], by linperm⟩

theorem diffSide_of_not_onLine' (aL : ¬OnLine a L) : ∃ b, DiffSide a b L := by
  rcases diffSide_of_not_onLine aL with ⟨b, bL, abL⟩; exact ⟨b, aL, bL, abL⟩

theorem pts_line_circle_of_not_sameside (aα : CenterCircle a α) (bα : OnCircle b α)
    (abL : ¬SameSide a b L) : ∃ c d, c ≠ d ∧
    OnLine c L ∧ OnLine d L ∧ OnCircle c α ∧ OnCircle d α :=
  pts_of_lineCircleInter $ lineCircleInter_of_not_sameSide abL
  (by right; exact inside_circle_of_center aα) $ by left; exact bα

theorem B_or_B_of_B_B (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
    B b c d ∨ B b d c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases B_of_three_onLine_ne (ne_23_of_B Babc) (ne_23_of_B Babd) cd bL
    (onLine_3_of_B Babc aL bL) (onLine_3_of_B Babd aL bL) with Bet | Bet | Bet
  left; exact Bet; exfalso; exact (not_B324_of_B123_B124 Babc Babd) Bet; right; exact Bet

theorem angle_extension_of_B_B (be : b ≠ e) (Babc : B a b c) (Babd : B a b d) :
    angle e b d = angle e b c := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_B_B cd Babc Babd with Bet | Bet; symm
  perma[angle_extension_of_B be Bet]; perma[angle_extension_of_B be Bet]

theorem online_of_sameside_inter (ab : a ≠ b) (aL : OnLine a L) (aM : OnLine a M) (bL : OnLine b L)
    (cM : OnLine c M) (cdL : SameSide c d L) : ¬OnLine b M :=
  fun bM => (not_onLine_of_sameSide cdL) (by rwa [line_unique_of_pts ab aM bM aL bL] at cM)

theorem DiffSide_of_sameside_sameside (aL : OnLine a L) (aM : OnLine a M) (aN : OnLine a N)
    (bL : OnLine b L) (cM : OnLine c M) (dN : OnLine d N) (dcL : SameSide d c L)
    (bcN : SameSide b c N) : DiffSide b d M :=
  ⟨online_of_sameside_inter (ne_of_sameside' aN bcN) aL aM bL cM $ sameSide_symm dcL,
  online_of_sameside_inter (ne_of_sameside' aL dcL) aN aM dN cM $ sameSide_symm bcN,
  not_sameSide_of_sameSide_sameSide aL aM aN bL cM dN (sameSide_symm dcL) bcN⟩

theorem angle_add_of_sameside (aL : OnLine a L) (bL : OnLine b L) (aM : OnLine a M)
    (cM : OnLine c M) (cdL : SameSide c d L) (bdM : SameSide b d M) :
    angle b a c = angle d a b + angle d a c := by
  linarith[angle_symm b a d, (angle_add_iff_sameSide (ne_of_sameside' aM bdM) (ne_of_sameside'
    aL cdL) aL bL aM cM (not_onLine_of_sameSide $ sameSide_symm bdM) (not_onLine_of_sameSide $
    sameSide_symm cdL) $ ne_line_of_online cM $ not_onLine_of_sameSide cdL).mpr ⟨bdM, cdL⟩]

theorem offline_of_B_offline (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bN : OnLine b N)
    (dN : OnLine d N) (dL : ¬OnLine d L) : ¬OnLine a N :=
  online_3_of_Triangle bN dN (tri231_of_tri123 $ Triangle_of_ne_online (ne_12_of_B Babc) aL bL dL)

theorem DiffSide_of_B_offline (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bN : OnLine b N)
    (dN : OnLine d N) (dL : ¬OnLine d L) : DiffSide a c N :=
  ⟨offline_of_B_offline Babc aL bL bN dN dL, offline_of_B_offline (B_symm Babc)
  (onLine_3_of_B Babc aL bL) bL bN dN dL, not_sameSide13_of_B123_onLine2 Babc bN⟩

theorem DiffSide_of_B_offline'' (Babc : B a b c) (aN : ¬OnLine a N) (bN : OnLine b N) :
    DiffSide a c N :=
  ⟨aN, fun cN => aN $ onLine_3_of_B (B_symm Babc) cN bN, not_sameSide13_of_B123_onLine2 Babc bN⟩

theorem sameside_of_B_sameside_sameside (Babc : B a b c) (bL : OnLine b L) (bM : OnLine b M)
    (bN : OnLine b N) (aL : OnLine a L) (eM : OnLine e M) (dN : OnLine d N) (edL : SameSide e d L)
    (cdM : SameSide c d M) : SameSide a e N :=
  sameside_of_DiffSide_DiffSide (DiffSide_symm $ DiffSide_of_B_offline Babc aL bL bN dN $
  not_onLine_of_sameSide $ sameSide_symm edL) (DiffSide_of_sameside_sameside bL bN bM
  (onLine_3_of_B Babc aL bL) dN eM edL cdM)

theorem B_or_B_of_sameside (bc : b ≠ c) (aL : OnLine a L) (col : Colinear a b c)
    (bcL : SameSide b c L) : B a b c ∨ B a c b := by
  rcases B_of_three_col_ne (ne_of_sameside' aL bcL) (ne_of_sameside' aL $ sameSide_symm bcL)
    bc col with Bet | Bet | Bet
  left; exact Bet; exfalso; exact not_sameSide13_of_B123_onLine2 Bet aL $ bcL; right; exact Bet

theorem angle_extension_of_sameside (ab : a ≠ b) (bL : OnLine b L)
    (col : Colinear b c d) (cdL : SameSide c d L) : angle c b a = angle d b a := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_sameside cd bL col cdL with Bet | Bet; symm
  repeat exact symm $ angle_extension_of_B (Ne.symm ab) Bet

theorem sameside_of_B_DiffSide_sameside (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (bM : OnLine b M) (eM : OnLine e M) (dM : ¬OnLine d M) (edL : SameSide e d L)
    (cdM : ¬SameSide c d M) : SameSide a d M :=
   sameSide_symm $ sameside_of_DiffSide_DiffSide ⟨offline_of_B_offline
    (B_symm Babc) (onLine_3_of_B Babc aL bL) bL bM eM $ not_onLine_of_sameSide edL, dM, cdM⟩ $
    DiffSide_symm $ DiffSide_of_B_offline Babc aL bL bM eM $ not_onLine_of_sameSide edL

theorem offline_of_online_offline (bc : b ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (bM : OnLine b M) (cM : OnLine c M) (aM : ¬OnLine a M) : ¬OnLine c L :=
  online_2_of_Triangle aL bL $ tri321 $ Triangle_of_ne_online bc bM cM aM

theorem offline_of_ne_online_offline (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (aM : OnLine a M) (cM : OnLine c M) (cL : ¬OnLine c L) : ¬OnLine b M :=
  fun bM => cL (by rwa[←line_unique_of_pts ab aL bL aM bM] at cM)

theorem online_of_angle_zero (ab : a ≠ b) (ac : a ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (bac_0 : angle  b a c = 0) : OnLine c L ∧ ¬B b a c :=
  (angle_zero_iff_onLine ab ac aL bL).mpr bac_0

theorem B_of_col_DiffSide (col_abc : Colinear a b c) (bL : OnLine b L)
    (acL : DiffSide a c L) : B a b c := by
  rcases col_abc with ⟨M, aM, bM, cM⟩; exact B_of_onLine_inter (ne_of_online' bL acL.1)
    (ne_of_online bL acL.2.1) (ne_of_DiffSide acL) (ne_line_of_online' aM acL.1) aM bM cM bL acL.2.2

theorem B_of_col_sameside (bL : OnLine b L) (acL : SameSide a c L) :
    ¬B a b c := fun Babc => not_sameSide13_of_B123_onLine2 Babc bL $ acL

theorem angle_zero_of_online (ab : a ≠ b) (ac : a ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (cL : OnLine c L) (Bbac : ¬B b a c) : angle b a c = 0 :=
  (angle_zero_iff_onLine ab ac aL bL).mp ⟨cL, Bbac⟩

theorem sameside_of_B_DiffSide (Babc : B a b c) (bL : OnLine b L) (aeL : DiffSide a e L) :
    SameSide e c L := sameside_of_DiffSide_DiffSide aeL $ DiffSide_of_B_offline'' Babc aeL.1 bL
/-- Lemma for I.14 that handles some casework. If one angle is contained in another and are equal
      then a sub-angle is zero -/
lemma angle_zero_of_lt_eq (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (dcL : SameSide d c L)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a d with ⟨M, aM, dM⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  by_cases bcM : SameSide b c M
  · linarith[angle_add_of_sameside aL bL aM dM dcL bcM, angle_symm c a b]
  by_cases cM : OnLine c M
  · exact angle_zero_of_online (ne_of_sameside' aL $ sameSide_symm dcL) (ne_of_sameside' aL dcL)
      aM cM dM (B_of_col_sameside aL $ sameSide_symm dcL)
  · linarith[angle_symm b a d, angle_add_of_sameside aL bL aN cN (sameSide_symm dcL) $
      sameSide_of_sameSide_not_sameSide ab aL aM aN bL dM cN cM dcL bcM, angle_symm d a c]

theorem angle_zero_of_lt_eq_B (ab : a ≠ b) (Bbcd : B b c d) (tri_bad : Triangle b a d)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact angle_zero_of_lt_eq ab aL bL (sameSide_symm $
    sameside_of_B_online_3 Bbcd bL (online_3_of_Triangle bL aL tri_bad)) bad_bac

theorem ne_of_col_tri (col_abc : Colinear a b c) (tri_acd : Triangle d a c) : d ≠ b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact ne_of_online' bL $ online_1_of_Triangle aL cL tri_acd

theorem ne_of_col_tri' (col_abc : Colinear a b c) (tri_acd : Triangle d a c) : b ≠ d :=
  Ne.symm $ ne_of_col_tri col_abc tri_acd

theorem tri_of_B_tri (Babc : B a b c) (tri_acd : Triangle d a c) : Triangle d b c :=
  tri321 $ tri_143_of_tri_col (ne_32_of_B Babc) (tri321 tri_acd) $ col_312 $ col_of_B Babc

theorem DiffSide_of_B_offline' (Babc : B a b c) (bL : OnLine b L) (aL : ¬OnLine a L) :
    DiffSide a c L :=
  ⟨aL, fun cL => aL $ onLine_3_of_B (B_symm Babc) cL bL, not_sameSide13_of_B123_onLine2 Babc bL⟩

theorem tri_of_B_B_base_tri (Bade : B a d e) (Bbdc : B b d c) (tri_abc : Triangle a b c) :
    Triangle a e b := tri_143_of_tri_col (ne_13_of_B Bade) (tri_of_B_tri (B_symm Bbdc) $
  tri132_of_tri123 tri_abc) (col_of_B Bade)

theorem offline_of_B_B_tri (Bade : B a d e) (Bbdc : B b d c) (aL : OnLine a L) (bL : OnLine b L)
    (tri_abc : Triangle a b c) : ¬OnLine e L :=
  fun eL => tri_of_B_B_base_tri Bade Bbdc tri_abc $ ⟨L, aL, eL, bL⟩

theorem nonzero_angle_of_offline (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (cL : ¬OnLine c L) : angle c a b ≠ 0 :=
  fun bac_0 => cL ((angle_zero_iff_onLine ab (ne_of_online aL cL) aL bL).mpr (by perma[bac_0])).1

theorem zero_lt_angle_of_offline (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (cL : ¬OnLine c L) : 0 < angle c a b :=
  lt_of_le_of_ne (angle_nonneg c a b) $ Ne.symm $ nonzero_angle_of_offline ab aL bL cL

theorem zero_lt_angle_of_tri (tri_abc : Triangle a b c) : 0 < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL
    bL (online_3_of_Triangle aL bL tri_abc)

theorem sameside_of_B_B (Babc : B a b c) (Bade : B a d e) (bL : OnLine b L) (dL : OnLine d L)
    (aL : ¬OnLine a L) : SameSide c e L :=
  sameside_of_DiffSide_DiffSide (DiffSide_of_B_offline' Babc bL aL) $ DiffSide_of_B_offline'
    Bade dL aL

theorem angle_lt_of_B_tri (Bcdb : B c d b) (tri_abc : Triangle a b c) :
    angle c a d < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩
  have ang_split := angle_add_of_sameside aM cM aL bL (sameSide_symm $ sameside_of_B_online_3 Bcdb
    cM (online_2_of_Triangle aM cM tri_abc)) $ sameSide_symm $ sameside_of_B_online_3 (B_symm Bcdb)
    bL $ online_3_of_Triangle aL bL tri_abc
  linarith[angle_symm d a c, zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL bL (fun dL =>
    (online_3_of_Triangle aL bL tri_abc) $ onLine_3_of_B (B_symm Bcdb) bL dL)]

theorem ne_of_oncircle (aα : OnCircle a α) (bα : ¬OnCircle b α) : a ≠ b :=
  fun ab => bα $ by rwa [ab] at aα

theorem B_or_B_of_circ_pt (ab : a ≠ b) (aα : CenterCircle a α) (bα : ¬OnCircle b α):
    ∃ c, (B a c b ∨ B a b c) ∧ OnCircle c α := by
  rcases pt_oncircle_of_inside_ne ab.symm $ inside_circle_of_center aα with ⟨d, Bbad, -⟩
  rcases pt_oncircle_of_inside_ne (ne_32_of_B Bbad) $ inside_circle_of_center aα with ⟨c, Bdac, cα⟩
  exact ⟨c, B_or_B_of_B_B (ne_of_oncircle cα bα) Bdac $ B_symm Bbad, cα⟩

theorem in_circle_of_lt_lt (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (cα : OnCircle c α) (dβ : OnCircle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : ∃ e, OnCircle e α ∧ InCircle e β := by
  by_cases bα : OnCircle b α; exact ⟨b, bα, inside_circle_of_center bβ⟩
  rcases B_or_B_of_circ_pt (mt length_eq_zero_iff.mpr $ by linarith[abs_lt.mp lt_cen]) aα bα with
   ⟨e, Bet, eα⟩
  rcases Bet with Bet | Bet
  repeat exact
    ⟨e, eα, incirc_of_lt bβ dβ $ by linarith[length_sum_of_B Bet, length_eq_of_oncircle aα cα eα,
                            abs_lt.mp lt_cen, length_symm e b]⟩

theorem circint_of_lt_lt (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (cα : OnCircle c α) (dβ : OnCircle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : CirclesInter α β := by
  rcases in_circle_of_lt_lt aα bβ cα dβ lt_cen cen_lt with ⟨e, eα, eβ⟩
  rcases in_circle_of_lt_lt bβ aα dβ cα (by rw[abs_lt]; constructor; repeat
    linperm[abs_lt.mp lt_cen]) $ by linperm with ⟨f, fβ, fα⟩
  exact circlesInter_of_inside_on_circle eα fβ fα eβ

theorem ang_2_nonzero_of_tri (tri_abc : Triangle a b c) : angle b a c ≠ 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; linarith[zero_lt_angle_of_offline (ne_12_of_tri
    tri_abc) aL bL (online_3_of_Triangle aL bL tri_abc), angle_symm b a c]

theorem not_B_symm (Babc : ¬B a b c) : ¬B c b a := fun Bet => Babc $ B_symm Bet

theorem ang_121_zero_of_ne (ab : a ≠ b) : angle a b a = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact angle_zero_of_online ab.symm ab.symm bL aL aL $ fun Baba => ne_13_of_B Baba rfl

theorem ne_23_of_sa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf ab_de
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_12_of_tri tri_abc) ab_de).symm,
    zero_lt_angle_of_tri tri_abc]

theorem ne_23_of_sa' (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_13_of_tri tri_abc) ac_df).symm,
    zero_lt_angle_of_tri tri_abc]

theorem not_B_of_tri_ang (tri_abc : Triangle a b c) (ef : e ≠ f) (de : d ≠ e)
    (abc_def : angle a b c = angle d e f) : ¬B e d f := by
  intro Bedf; rcases col_of_B Bedf with ⟨L, eL, dL, fL⟩
  linperm [angle_zero_of_online de.symm ef eL dL fL $ not_B_of_B Bedf, zero_lt_angle_of_tri $
    tri213 tri_abc]

theorem Triangle_of_asa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    Triangle d e f := by
  intro col_def
  have df := ne_23_of_sa (tri213 tri_abc) (by linperm) abc_def
  have de := ne_of_ne_len (ne_12_of_tri tri_abc) ab_de
  rcases B_of_three_col_ne de df (ne_23_of_sa tri_abc ab_de bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa tri_abc ab_de bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem Triangle_of_saa (de : d ≠ e) (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    Triangle d e f := by
  intro col_def
  have df := ne_of_ne_len (ne_13_of_tri tri_abc) ac_df
  rcases B_of_three_col_ne de df (ne_23_of_sa' tri_abc ac_df bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa' tri_abc ac_df bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem offline_of_online_inter (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (aL : ¬OnLine a L) (dL : ¬OnLine d L)
    (eM : OnLine e M) (eN : OnLine e N) : ¬OnLine e L :=
  offline_of_online_offline (ne_of_online' eM $ offline_of_online_offline bc aM bM bL cL aL) bL cL
    cN eN $ offline_of_online_offline bc.symm dN cN cL bL dL

theorem Para_symm (ParaMN : Para M N) : Para N M := fun e => by have := ParaMN e; tauto

theorem offline_of_Para (aM : OnLine a M) (ParaMN : Para M N) : ¬OnLine a N := by
  have := ParaMN a; tauto

theorem offline_of_Para' (aN : OnLine a N) (ParaMN : Para M N) : ¬OnLine a M := by
  have := ParaMN a; tauto

theorem ne_of_Para (aM : OnLine a M) (bN : OnLine b N) (ParaMN : Para M N) : a ≠ b :=
  ne_of_online aM $ offline_of_Para' bN ParaMN

theorem ne_of_Para' (aM : OnLine a M) (bN : OnLine b N) (ParaMN : Para M N) : b ≠ a :=
  ne_of_online' aM $ offline_of_Para' bN ParaMN

theorem not_Para_of_inter (aM : OnLine a M) (aN : OnLine a N) : ¬Para M N := by
  intro ParaMN; have := ParaMN a; tauto

theorem DiffSide_of_B_sameside (Bcad : B c a d) (aL : OnLine a L) (ceL : SameSide c e L) :
    DiffSide d e L :=
  DiffSide_symm $ DiffSide_of_sameside_DiffSide ceL $ DiffSide_of_B_offline' Bcad aL $
    not_onLine_of_sameSide ceL

theorem pt_of_online_not_sameside (aL : OnLine a L) (bL : OnLine b L) (abM : ¬SameSide a b M) :
    ∃ c, OnLine c M ∧ OnLine c L := pt_of_linesInter $ lines_inter_of_not_sameSide aL bL abM

theorem sameside_of_Para_online (aM : OnLine a M) (bM : OnLine b M) (ParaMN : Para M N) :
    SameSide a b N := by
  by_contra abO; rcases pt_of_online_not_sameside aM bM abO with ⟨c, cN, cM⟩
  exact not_Para_of_inter cM cN ParaMN

theorem sameside_of_Para_online' (aN : OnLine a N) (bN : OnLine b N) (ParaMN : Para M N) :
    SameSide a b M := sameside_of_Para_online aN bN (Para_symm ParaMN)

theorem tri124_of_Paragram (pgram : Paragram a b c d M N O P) : Triangle a b d := by
  have ⟨aM, bM, bN, cN, _, dO, _, aP, ParaMO, ParaNP⟩ := pgram
  exact Triangle_of_ne_online (ne_of_sameside' aP $ sameside_of_Para_online
    bN cN ParaNP) aM bM $ offline_of_Para dO $ Para_symm ParaMO

theorem sameside_of_sameside_DiffSide (aL : OnLine a L) (aM : OnLine a M) (aN : OnLine a N)
    (bL : OnLine b L) (cM : OnLine c M) (dN : OnLine d N) (cdL : SameSide c d L)
    (bdM : DiffSide b d M) : SameSide b c N :=
  sameSide_of_sameSide_not_sameSide (ne_of_online aM bdM.1) aL aM aN bL cM dN bdM.2.1 cdL bdM.2.2

theorem sameside_of_quad (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M) (cM : OnLine c M)
    (cN : OnLine c N) (dN : OnLine d N) (dO : OnLine d O) (aO : OnLine a O) (abN : SameSide a b N)
    (cdL : SameSide c d L) (adM : SameSide a d M) : SameSide b c O := by
  rcases line_of_pts b d with ⟨P, bP, dP⟩
  perma[sameside_of_sameside_DiffSide dN dP dO cN bP aO (by perma) $
    by perma[DiffSide_of_sameside_sameside bL bP bM aL dP cM cdL adM]]

theorem DiffSide_of_Paragram (bL : OnLine b L) (dL : OnLine d L)
    (pgram : Paragram a b c d M N O P) : DiffSide a c L := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  exact DiffSide_of_sameside_sameside bM bL bN aM dL cN (sameside_of_Para_online' cO dO ParaMO)
    (sameside_of_Para_online' aP dP ParaNP)

theorem offline_of_col_offline (bc : b ≠ c) (col_abc : Colinear a b c) (bL : OnLine b L)
    (aL : ¬OnLine a L) : ¬OnLine c L :=
  fun cL => aL $ online_of_col_online bc bL cL (by perma[col_abc])

theorem B_of_col_offline (bc : b ≠ c) (col_abc : Colinear a b c) (bL : OnLine b L)
    (aL : ¬OnLine a L) (acL : ¬SameSide a c L) : B a b c :=
  B_of_col_DiffSide col_abc bL ⟨aL, offline_of_col_offline bc col_abc bL aL, acL⟩

theorem tri_of_sameside (bc : b ≠ c) (bL : OnLine b L) (cL : OnLine c L) (adL : SameSide a d L) :
    Triangle a b c := tri312 $ Triangle_of_ne_online bc bL cL $ not_onLine_of_sameSide adL

theorem B_diagonal_of_quad (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M)
    (cM : OnLine c M) (cN : OnLine c N) (dN : OnLine d N) (abN : SameSide a b N)
    (cdL : SameSide c d L) (adM : SameSide a d M) : ∃ e P O, B b e d ∧ B a e c ∧ OnLine a P ∧
    OnLine c P ∧ OnLine b O ∧ OnLine d O ∧ OnLine e P ∧ OnLine e O ∧
    DiffSide b d P ∧ DiffSide a c O := by
  rcases line_of_pts b d with ⟨O, bO, dO⟩; rcases line_of_pts a c with ⟨P, aP, cP⟩
  rcases line_of_pts a d with ⟨Q, aQ, dQ⟩
  have acO := DiffSide_of_sameside_sameside bL bO bM aL dO cM cdL adM
  have bdP := DiffSide_of_sameside_sameside aL aP aQ bL cP dQ (by perma) $
    sameside_of_quad aL bL bM cM cN dN dQ aQ abN cdL adM
  rcases pt_of_online_not_sameside aP cP acO.2.2 with ⟨e, eO, eP⟩
  exact ⟨e, P, O, B_of_col_DiffSide ⟨O, bO, eO, dO⟩ eP bdP,
    B_of_col_DiffSide ⟨P, aP, eP, cP⟩ eO acO, aP, cP, bO, dO, eP, eO, bdP, acO⟩

theorem quad_area_comm (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M) (cM : OnLine c M)
    (cN : OnLine c N) (dN : OnLine d N) (abN : SameSide a b N) (cdL : SameSide c d L)
    (adM : SameSide a d M) : area a b d + area b c d = area a b c + area a c d := by
  rcases B_diagonal_of_quad aL bL bM cM cN dN abN cdL adM with
    ⟨e, P, O, Bbed, Baec, aP, cP, bO, dO, eP, eO, bdP, acO⟩
  linperm[area_add_of_B_offline Bbed bO dO acO.1, area_add_of_B_offline Bbed bO dO acO.2.1,
    area_add_of_B_offline Baec aP cP bdP.1, area_add_of_B_offline Baec aP cP bdP.2.1]

theorem Paragram_area_comm (pgram : Paragram a b c d M N O P) :
    area a b d + area b c d = area a b c + area a c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  exact quad_area_comm aM bM bN cN cO dO (sameside_of_Para_online aM bM ParaMO)
    (sameside_of_Para_online' cO dO ParaMO) $ sameside_of_Para_online' aP dP ParaNP

theorem sameside_of_not_B (bc : b ≠ c) (Babc : ¬B a b c) (bL : OnLine b L) (aL : ¬OnLine a L)
    (col_abc : Colinear a b c) : SameSide a c L := by
  by_contra acL; exact Babc $ B_of_col_offline bc col_abc bL aL acL

theorem DiffSide_of_DiffSide_Para (aO : OnLine a O) (bO : OnLine b O) (afM : DiffSide a f M)
    (ParaMO : Para M O) : DiffSide b f M :=
  DiffSide_of_sameside_DiffSide (sameside_of_Para_online' aO bO ParaMO) afM

theorem DiffSide_of_B_Para (Badf : B a d f) (aL : OnLine a L) (dL : OnLine d L)
    (dM : OnLine d M) (cM : OnLine c M) (cN : OnLine c N) (ParaLN : Para L N) : DiffSide a f M :=
  DiffSide_of_B_offline Badf aL dL dM cM $ offline_of_Para' cN ParaLN

theorem DiffSide_of_B_pgram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O) :
    DiffSide b f M := by
  have ⟨aL, dL, dM, cM, cN, _, bO, aO, ParaLN, ParaMO⟩ := pgram1
  exact DiffSide_of_DiffSide_Para aO bO (DiffSide_of_B_Para Badf aL dL dM cM cN ParaLN) ParaMO

theorem sameside_of_B_pgram_pgram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : SameSide b d P := by
  have ⟨_, dL, dM, cM, cN, bN, _, _, ParaLN, _⟩ := pgram1
  exact sameside_of_sameside_DiffSide cN cM pgram2.2.2.2.1 bN dM pgram2.2.2.1
    (sameside_of_Para_online dL pgram2.2.1 ParaLN) $ DiffSide_of_B_pgram Badf pgram1

theorem sameside_of_B_prgram_pgram_trans (Badf : B a d f)
    (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q) : SameSide d e P := by
  have ⟨_, _, _, _, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  exact sameSide_trans (sameside_of_B_pgram_pgram Badf pgram1 pgram2) $
    sameside_of_Para_online' bQ eQ ParaPQ

theorem sameside_of_B_prgram_pgram_trans' (Badf : B a d f)
    (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q) : SameSide a e P :=
  sameSide_trans (sameSide_of_B_not_onLine_2 (B_symm Badf) pgram2.2.2.1
    (not_onLine_of_sameSide $ by perma[sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2])) $
    sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2

theorem sameside_of_sameside_Para (aN : OnLine a N) (bN : OnLine b N) (acM : SameSide a c M)
    (ParaMN : Para M N) : SameSide b c M :=
  sameSide_trans (sameside_of_Para_online' aN bN ParaMN) acM

theorem DiffSide_of_sameside_Paragram (fL : OnLine f L) (cP : OnLine c P) (fP : OnLine f P)
    (afM : SameSide a f M) (pgram : Paragram a b c d L M N O) : DiffSide b d P := by
have ⟨_, bL, bM, cM, cN, dN, dO, aO, ParaLN, ParaMO⟩ := pgram
exact DiffSide_of_sameside_sameside cM cP cN bM fP dN (sameside_of_sameside_Para aO dO afM ParaMO)
  (sameside_of_Para_online bL fL ParaLN)

theorem DiffSide_of_sameside_2_Paragram (afM : SameSide a f M) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : DiffSide e d P := by
  have ⟨_, fL, fP, cP, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  exact DiffSide_of_sameside_DiffSide (sameside_of_Para_online' bQ eQ ParaPQ)
    (by perma[DiffSide_of_sameside_Paragram fL cP fP afM pgram1])

theorem B_of_B_2_Paragram (df : d ≠ f) (Badf : ¬B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : B e f d := by
  have ⟨aL, dL, dM, _, _, _, _, aO, _, ParaMO⟩ := pgram1; have ⟨eL, fL, fP, _, _, _, _, _, _, _⟩ :=
    pgram2; exact B_of_col_DiffSide ⟨L, eL, fL, dL⟩ fP $ DiffSide_of_sameside_2_Paragram
    (sameside_of_not_B df Badf dM (offline_of_Para' aO ParaMO) ⟨L, aL, dL, fL⟩) pgram1 pgram2

theorem sameside_of_B_Para (Bfea : B f e a) (fP : OnLine f P) (eQ : OnLine e Q) (bQ : OnLine b Q)
    (ParaPQ : Para P Q) : SameSide a b P := sameSide_trans (sameSide_of_B_not_onLine_2 Bfea fP $
  offline_of_Para' eQ ParaPQ) $ sameside_of_Para_online' eQ bQ ParaPQ

theorem sameside_online_of_DiffSide (dM : OnLine d M) (aM : OnLine a M) (aL : OnLine a L)
    (cdL : DiffSide c d L) : ∃ b, OnLine b M ∧ SameSide b c L := by
  rcases circle_of_ne (ne_of_online aL cdL.2.1) with ⟨α, acen, _⟩
  rcases pt_oncircle_of_inside_ne (ne_of_online aL cdL.2.1).symm (inside_circle_of_center acen)
    with ⟨b, Bdab, _⟩
  exact ⟨b, onLine_3_of_B Bdab dM aM, by perma[sameside_of_B_DiffSide Bdab aL (DiffSide_symm cdL)]⟩

theorem sameside_of_offline (bL : OnLine b L) (cL : ¬OnLine c L) (bM : ¬OnLine b M)
    (eL : OnLine e L) (eM : OnLine e M) : ∃ d, OnLine d M ∧ SameSide d c L := by
  rcases online_ne_of_line M with ⟨a, d, ad, aM, dM⟩
  wlog dL : ¬OnLine d L generalizing a d L; exact this bL cL eL d a ad.symm dM aM $
    offline_of_online_offline ad.symm bL (of_not_not dL) dM aM bM
  by_cases dcL : SameSide d c L; exact ⟨d, dM, dcL⟩
  exact sameside_online_of_DiffSide dM eM eL ⟨cL, dL, not_sameSide_symm dcL⟩

theorem angle_add_of_B (Bbcd : B b c d) (bL : OnLine b L) (cL : OnLine c L) (aL : ¬OnLine a L) :
    angle d a b = angle c a d + angle c a b := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases line_of_pts a d with ⟨N, aN, dN⟩
  exact angle_add_of_sameside aN dN aM bM (sameSide_symm $ sameside_of_B_online_3 (B_symm Bbcd) dN
    $ offline_of_online_offline (ne_13_of_B Bbcd).symm aN dN (onLine_3_of_B Bbcd bL cL) bL aL)
    (sameSide_symm $ sameside_of_B_online_3 Bbcd bM $ offline_of_online_offline (ne_13_of_B Bbcd)
    aM bM bL (onLine_3_of_B Bbcd bL cL) aL)

theorem online_of_ne_ne (ac : a ≠ c) (LM : L ≠ M) (aL : OnLine a L) (cL : OnLine c L)
    (cM : OnLine c M) : ¬OnLine a M := fun aM => LM $ line_unique_of_pts ac aL cL aM cM

theorem sameside_of_B_sameside (Bbcd : B b c d) (dL : OnLine d L) (bL : ¬OnLine b L)
    (abL : SameSide a b L) : SameSide a c L :=
  sameSide_trans (sameSide_symm abL) $ sameSide_symm $ sameside_of_B_online_3 (B_symm Bbcd) dL bL

theorem quad_add_of_quad (Babc : B a b c) (Bdef : B d e f) (aL : OnLine a L) (bL : OnLine b L)
    (cM : OnLine c M) (fM : OnLine f M) (dN : OnLine d N) (eN : OnLine e N) (acN : SameSide a c N)
    (feL : SameSide f e L) (adM : SameSide a d M) :
    area a c f + area a f d = area a b e + area a e d + area b c e + area f e c := by
  rcases B_diagonal_of_quad aL (onLine_3_of_B Babc aL bL) cM fM (onLine_3_of_B Bdef dN eN) eN acN
    feL $ sameside_of_B_sameside Bdef fM (not_onLine_of_sameSide $ sameSide_symm adM) adM
    with ⟨g, P, O, Bcge, Bagf, aP, fP, cO, eO, gP, gO, ceP, afO⟩
  linperm[area_add_of_B_offline Bagf aP fP ceP.1, area_add_of_B_offline Bdef dN
    (onLine_3_of_B Bdef dN eN) (not_onLine_of_sameSide acN), area_add_of_B_offline Bagf aP fP
    ceP.2.1, area_add_of_B_offline Bcge cO eO afO.2.1, area_add_of_B_offline Bcge cO eO afO.1,
    area_add_of_B_offline Babc aL (onLine_3_of_B Babc aL bL)
    (not_onLine_of_sameSide (by perma[feL]))]

theorem B_of_sq (Bbxc : B b x c) (xX : OnLine x X) (lX : OnLine l X) (lP : OnLine l P)
    (ParaQX : Para Q X) (ParaOX : Para O X) (pgram : Paragram b c d e L O P Q) : B e l d := by
  have ⟨_, _, cO, dO, dP, eP, eQ, bQ, _, _⟩ := pgram
  exact B_of_col_DiffSide ⟨P, eP, lP, dP⟩ lX $ DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameside_of_Para_online cO dO ParaOX) $ DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameSide_symm $ sameside_of_Para_online eQ bQ ParaQX) $ DiffSide_of_B_offline' Bbxc xX $
    offline_of_Para bQ ParaQX

theorem sameside_of_pyth (Beld : B e l d) (aX : OnLine a X) (lX : OnLine l X)
    (pgram : Paragram b c d e L O P Q) (ParaQX : Para Q X) : SameSide a c Q := by
  have ⟨_, _, cO, dO, _, _, eQ, _, _, ParaOQ⟩ := pgram
  exact sameSide_trans (sameSide_trans (sameside_of_B_online_3 Beld eQ $ offline_of_Para dO ParaOQ)
    $ sameSide_symm $ sameside_of_Para_online' aX lX ParaQX) $ sameSide_symm $
    sameside_of_Para_online cO dO ParaOQ

theorem tri_tri_B_B_of_int (bL : OnLine b L) (cL : OnLine c L) (aM : OnLine a M) (cM : OnLine c M)
    (aN : OnLine a N) (bN : OnLine b N) (adL : SameSide a d L) (bdM : SameSide b d M)
    (cdN : SameSide c d N) : ∃ e, B a e c ∧ B b d e ∧ Triangle a b e ∧ Triangle c d e := by
rcases line_of_pts b d with ⟨P, bP, dP⟩
rcases line_of_pts c d with ⟨O, cO, dO⟩
have caP := DiffSide_of_sameside_sameside bL bP bN cL dP aN adL cdN
rcases pt_B_of_DiffSide caP with ⟨e, eP, Bcea⟩
have beO := DiffSide_of_sameside_sameside cL cO cM bL dO (onLine_2_of_B Bcea cM aM)
  (by perma[sameSide_trans adL $
    by perma[sameside_of_B_online_3 Bcea cL $ not_onLine_of_sameSide adL]]) bdM
have Bbde := B_of_col_DiffSide ⟨P, bP, dP, eP⟩ dO beO
exact ⟨e, B_symm Bcea, B_of_col_DiffSide ⟨P, bP, dP, eP⟩ dO beO,
  by perma[Triangle_of_ne_online (ne_13_of_B Bbde) bP eP caP.2.1],
  by perma[Triangle_of_ne_online (ne_23_of_B Bbde) dP eP caP.1]⟩

theorem line_circle_inter_sameside_of_offline (aL : OnLine a L) (aM : OnLine a M) (cM : OnLine c M)
    (cL : ¬OnLine c L) (aα : CenterCircle a α) :
    ∃ d, OnLine d M ∧ SameSide c d L ∧ OnCircle d α := by
rcases pts_of_lineCircleInter $ lineCircleInter_of_inside_onLine aM (inside_circle_of_center aα)
  with ⟨d, e, de, dM, eM, dα, eα⟩
have Bdae := B_of_lineCircleInter de aM dM eM dα eα (inside_circle_of_center aα)
have dL : ¬OnLine d L := --turn into API
  fun dL => cL (by rwa[line_unique_of_pts de dM eM dL (onLine_3_of_B Bdae dL aL)] at cM)
rcases sameSide_or_of_diffSide' cL (DiffSide_of_B_offline'' Bdae dL aL) with dcL | ecL
exact ⟨d, dM, by perma[dcL], dα⟩; exact ⟨e, eM, by perma[ecL], eα⟩

/--Euclid I.2, generalization-/
theorem len_eq_of_sameside (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (aL : ¬OnLine a L) :
    ∃ d, OnLine d L ∧ SameSide c d M ∧ length a b = length b d := by
rcases circle_of_ne $ ne_of_online bL aL with ⟨α, bα, aα⟩
rcases line_circle_inter_sameside_of_offline bM bL cL
  (offline_of_ne_online_offline bc bL cL bM aM aL) bα with ⟨d, dL, cdM, dα⟩
exact ⟨d, dL, cdM, by perma[length_eq_of_oncircle bα aα dα]⟩

theorem offLine_of_angle_lt (ad : a ≠ d) (dL : OnLine d L) (cN : OnLine c N) (dN : OnLine d N)
    (bcL : SameSide b c L) (adb_lt_adc : angle a d b < angle a d c) : ¬OnLine b N := by
  rcases line_of_pts d b with ⟨M, dM, bM⟩
  intro bN; rw[line_unique_of_pts (ne_of_sameside dL bcL) bN dN bM dM] at cN
  linperm[angle_extension_of_sameside ad dL ⟨M, dM, bM, cN⟩ bcL]

theorem sameside_of_B_not_online_3 (Babc : B a b c) (aL : OnLine a L) (cL : ¬OnLine c L) :
    SameSide b c L := sameSide_of_B_not_onLine_2 Babc aL $ online_of_B_online Babc aL cL

theorem sameside_of_sameside_sameside (dL : OnLine d L) (dM : OnLine d M) (dN : OnLine d N)
    (cN : OnLine c N) (eN : OnLine e N) (ceM : SameSide c e M) (bcL : SameSide b c L) :
    SameSide c e L := by
  by_cases ce : c = e; rw[←ce]; exact sameSide_rfl_of_not_onLine $ not_onLine_of_sameSide $
    sameSide_symm bcL
  rcases B_or_B_of_sameside ce dM ⟨N, dN, cN, eN⟩ ceM with Bet | Bet
  exact sameSide_of_B_not_onLine_2 Bet dL $ not_onLine_of_sameSide $ sameSide_symm bcL
  perma[sameside_of_B_not_online_3 Bet dL $ not_onLine_of_sameSide $ sameSide_symm bcL]

theorem DiffSide_of_angle_lt (ad : a ≠ d) (dL : OnLine d L) (dM : OnLine d M) (dN : OnLine d N)
    (aL : OnLine a L) (bM : OnLine b M) (cN : OnLine c N) (aM : ¬OnLine a M)
    (bcL : SameSide b c L) (adb_lt_adc : angle a d b < angle a d c) : DiffSide a c M := by
  by_cases acM : SameSide a c M;
    linperm[angle_add_of_sameside dL aL dM bM bcL acM, angle_nonneg c d b]
  exact ⟨aM, offline_of_online_offline (ne_of_sameside dL $ sameSide_symm bcL).symm bM dM dN cN $
    offLine_of_angle_lt ad dL cN dN bcL adb_lt_adc, acM⟩ --golf?

theorem online_sameside_DiffSide_len_ang_tri_of_ang_lt (tri_def : Triangle d e f)
    (dL : OnLine d L) (eL : OnLine e L) (hM : OnLine h M) (dM : OnLine d M) (dN : OnLine d N)
    (fN : OnLine f N) (hfL : SameSide h f L) (edf_edh : angle e d f < angle e d h) :
    ∃ g, OnLine g M ∧ ¬OnLine f M ∧ SameSide h g L ∧ length f d = length d g ∧
    angle h d e = angle g d e ∧ 0 < angle d g e ∧ Triangle g d f ∧ DiffSide e g N := by
  have fM := offLine_of_angle_lt (ne_21_of_tri tri_def) dL hM dM (sameSide_symm hfL) $ by linperm
  rcases len_eq_of_sameside (ne_of_sameside' dL hfL) fN dN dM hM fM with ⟨g, gM, hgN, fd_dg⟩
  have hgL := sameside_of_sameside_sameside dL dN dM hM gM hgN $ sameSide_symm hfL
  have tri_gdf := Triangle_of_ne_online (ne_of_sameside dN $ sameSide_symm hgN) gM dM fM
  have hde_gde := angle_extension_of_sameside (ne_21_of_tri tri_def) dL ⟨M, dM, hM, gM⟩ hgL
  exact ⟨g, gM, fM, hgL, fd_dg, hde_gde, zero_lt_angle_of_tri $ tri321 $ Triangle_of_ne_online
    (ne_12_of_tri tri_def) dL eL $ not_onLine_of_sameSide $ sameSide_symm hgL, tri_gdf,
    DiffSide_of_angle_lt (ne_21_of_tri tri_def) dL dN dM eL fN gM (online_2_of_Triangle dN fN
    tri_def) (sameSide_symm $ sameSide_trans hgL hfL) $ by linperm⟩

theorem sameside_of_not_sameside_Para (bc : b ≠ c) (eh : e ≠ h) (eL : OnLine e L) (eR : OnLine e R)
    (eS : OnLine e S) (hL : OnLine h L) (cR : OnLine c R) (bS : OnLine b S) (bN : OnLine b N)
    (cN : OnLine c N) (bhR : ¬SameSide b h R) (ParaLN : Para L N) : SameSide c h S :=
sameSide_symm $ sameside_of_sameside_DiffSide eL eR eS hL cR bS (sameside_of_Para_online' cN bN
    ParaLN) ⟨offline_of_online_offline eh cR eR eL hL (offline_of_Para' cN ParaLN),
    offline_of_online_offline bc.symm eR cR cN bN (offline_of_Para eL ParaLN), not_sameSide_symm
    bhR⟩

theorem not_Para (ParaLM : ¬Para L M) : ∃ a, OnLine a L ∧ OnLine a M := by
  unfold Para at ParaLM; push_neg at ParaLM; exact ParaLM

/-- area of a Triangle cannot equal the area of its subTriangle -/
lemma tri_sum_contra (bO : OnLine b O) (dO : OnLine d O) (eO : OnLine e O) (cO : ¬OnLine c O)
    (ar: area b c d = area b c e) : ¬B b e d := by
  intro Bbed; apply cO; apply (area_zero_iff_onLine (ne_32_of_B Bbed) dO eO).mp
  linperm [(area_add_iff_B (ne_12_of_B Bbed) (ne_23_of_B Bbed) (ne_31_of_B Bbed) bO eO dO cO).mp
      Bbed]

theorem ne_of_Para_Para (ab : a ≠ b) (aM : OnLine a M) (aN : OnLine a N) (bN : OnLine b N)
    (cM : OnLine c M) (ParaLM : Para L M) (ParaLN : ¬Para L N) : b ≠ c := fun bc => ParaLN (by rwa
  [line_unique_of_pts ab aM (by rwa[←bc] at cM) aN bN] at ParaLM)

theorem B_of_B_Para (Bakc : B a k c) (col_aeb : Colinear a e b) (bM : OnLine b M) (cM : OnLine c M)
    (eN : OnLine e N) (kN : OnLine k N) (aN : ¬OnLine a N) (ParaMN : Para M N) : B a e b :=
  B_of_col_DiffSide col_aeb eN $ DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameside_of_Para_online cM bM ParaMN) (DiffSide_symm $ DiffSide_of_B_offline' Bakc kN aN)

theorem not_B_of_sameside (abL : SameSide a b L) (cL : OnLine c L) : ¬B a c b :=
  fun Bacb => (DiffSide_of_B_offline' Bacb cL (not_onLine_of_sameSide abL)).2.2 abL

theorem B_of_B_Para_Para (Babc : B a b c) (aL : OnLine a L) (aM : OnLine a M) (bO : OnLine b O)
    (cP : OnLine c P) (dM : OnLine d M) (dO : OnLine d O) (eM : OnLine e M) (eP : OnLine e P)
    (ParaPO : Para P O) (ParaPL : Para P L) (ParaOL : Para O L) : B e d a := by
  have Bead := not_B_of_sameside (sameSide_symm (sameSide_trans (sameside_of_Para_online bO dO
    ParaOL) (sameSide_trans (sameSide_symm (sameside_of_B_not_online_3 Babc aL (offline_of_Para cP
    ParaPL))) (sameside_of_Para_online cP eP ParaPL)))) aL
  have := B_or_B_of_sameside (ne_of_Para dO aL ParaOL).symm eP ⟨M, eM, aM, dM⟩ (sameSide_trans
    (sameside_of_B_not_online_3 (B_symm Babc) cP (offline_of_Para' aL ParaPL))
    (sameside_of_Para_online' bO dO ParaPO)); tauto

theorem DiffSide_of_B_Para_Para (Bfgh : B f g h) (bL : OnLine b L) (hQ : OnLine h Q)
    (hM : OnLine h M) (hS : OnLine h S) (gP : OnLine g P) (fR : OnLine f R) (bS : OnLine b S)
    (bP : OnLine b P) (kS : OnLine k S) (kR : OnLine k R) (ParaPR : Para P R) (ParaMR : Para M R)
    (ParaPM : Para P M) (ParaQL : Para Q L) : DiffSide h k L := DiffSide_of_B_offline'
  (B_symm $ B_of_B_Para_Para (B_symm Bfgh) hM hS gP fR bS bP kS kR (Para_symm ParaPR)
    (Para_symm ParaMR) ParaPM) bL (offline_of_Para hQ ParaQL)

theorem DiffSide_of_B_B_Para (Babe : B a b e) (Bfgh : B f g h) (aL : OnLine a L) (bL : OnLine b L)
    (hS : OnLine h S) (bS : OnLine b S) (bP : OnLine b P) (gP : OnLine g P) (eR : OnLine e R)
    (fR : OnLine f R) (fQ : OnLine f Q) (gQ : OnLine g Q) (ParaPR : Para P R) (ParaQL : Para Q L) :
    DiffSide a g S := DiffSide_of_sameside_sameside bL bS bP aL hS gP (sameside_of_Para_online
  gQ (onLine_3_of_B Bfgh fQ gQ) ParaQL) $ sameside_of_DiffSide_DiffSide
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' eR fR ParaPR) $
    DiffSide_of_B_offline' (B_symm Babe) bP (offline_of_Para' eR ParaPR)) $ DiffSide_of_B_offline'
    Bfgh gP (offline_of_Para' fR ParaPR)

theorem B_of_B_B_Para (Babe : B a b e) (Bfgh : B f g h) (aL : OnLine a L) (bL : OnLine b L)
    (hM : OnLine h M) (hS : OnLine h S) (hQ : OnLine h Q) (bS : OnLine b S) (bP : OnLine b P)
    (gP : OnLine g P) (eR : OnLine e R) (fR : OnLine f R) (fQ : OnLine f Q) (kS : OnLine k S)
    (kR : OnLine k R) (ParaPR : Para P R) (ParaQL : Para Q L) (ParaPM : Para P M)
    (ParaMR : Para M R) : B f e k := B_of_col_DiffSide ⟨R, fR, eR, kR⟩ (onLine_3_of_B Babe aL bL)
  $ DiffSide_of_sameside_DiffSide (sameside_of_Para_online hQ fQ ParaQL) $ DiffSide_of_B_Para_Para
    Bfgh bL hQ hM hS gP fR bS bP kS kR ParaPR ParaMR ParaPM ParaQL
 ---------------------------------------- Book I Refactored ---------------------------------------
/-- Euclid I.1, construction of two equilateral Triangles -/
theorem iseqtri_iseqtri_DiffSide_of_ne (ab : a ≠ b) : ∃ c d L, OnLine a L ∧
    OnLine b L ∧ DiffSide c d L ∧ EqTri a b c ∧ EqTri a b d := by
rcases circle_of_ne ab with ⟨α, aα, bα⟩
rcases circle_of_ne (Ne.symm ab) with ⟨β, bβ, aβ⟩
rcases DiffSide_of_circlesinter aα bβ (circlesInter_of_inside_on_circle bα aβ
  (inside_circle_of_center aα) (inside_circle_of_center bβ)) with
  ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩
have ab_ac := (on_circle_iff_length_eq aα bα).mpr cα
have bc_ba := (on_circle_iff_length_eq bβ cβ).mpr aβ
have ab_ad := (on_circle_iff_length_eq aα bα).mpr dα
have bd_ba := (on_circle_iff_length_eq bβ dβ).mpr aβ
exact ⟨c, d, L, aL, bL, cdL, EqTri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
  EqTri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩

/-- Euclid I.1, construction of an equilateral Triangle on the sameside of a point -/
theorem iseqtri_sameside_of_ne (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (dL : ¬OnLine d L):
    ∃ c, ¬OnLine c L ∧ SameSide c d L ∧ EqTri a b c := by
  rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c1, c2, M, aM, bM, c1c2M, eqtri1, eqtri2⟩
  rcases sameSide_or_of_diffSide' dL (by rwa [line_unique_of_pts ab aM bM aL bL] at c1c2M)
    with c1dL | c2dL
  refine ⟨c1, not_onLine_of_sameSide c1dL, c1dL, eqtri1⟩
  refine ⟨c2, not_onLine_of_sameSide c2dL, c2dL, eqtri2⟩

/-- Euclid I.1, construction of a single equilateral Triangle -/
theorem iseqtri_of_ne (ab : a ≠ b) : ∃ c, EqTri a b c :=
  by rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c, -, -, -, -, -, eqtri, -⟩; exact ⟨c, eqtri⟩

/-- Euclid I.2, collapsing compass -/
theorem length_eq_of_ne (a : Point) (bc : b ≠ c) : ∃ f, length a f = length b c := by
  by_cases ab : a = b; rw [ab]; exact ⟨c, rfl⟩
  rcases iseqtri_of_ne ab with ⟨d, eqtri⟩
  rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩
  rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩
  have be_bc := (length_eq_of_oncircle bα cα eα).symm
  have de_df := length_eq_of_oncircle dβ eβ fβ
  have af_be := length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 de_df
  exact ⟨f, af_be.trans be_bc⟩

/-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne (ab : a ≠ b) (bc : b ≠ c) : ∃ d, B a b d ∧ length b c = length b d := by
  rcases B_circ_of_ne ab bc with ⟨d, α, Babd, bα, cα, dα⟩;
  exact ⟨d, Babd, length_eq_of_oncircle bα cα dα⟩

/-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne_four (ab : a ≠ b) (cd : c ≠ d) :
    ∃ f, B a b f ∧ length c d = length b f := by
rcases length_eq_of_ne b cd with ⟨e, be_cd⟩
rcases length_eq_B_of_ne ab (ne_of_ne_len' cd be_cd) with ⟨f, Babf, be_bf⟩
exact ⟨f, Babf, by linarith⟩

/-- Euclid I.2, generalization -/
theorem length_eq_of_sameside (aL : OnLine a L) (bL : ¬OnLine b L) (aM : ¬OnLine a M)
    (dL : OnLine d L) (dM : OnLine d M) : ∃ e, OnLine e M ∧ DiffSide e b L ∧
    length e d = length a b := by
  rcases sameside_of_offline aL bL aM dL dM with ⟨f, fM, fbL⟩
  rcases length_eq_B_of_ne_four (ne_of_sameside dL fbL) (ne_of_online aL bL) with ⟨e, Bfde, ab_de⟩
  exact ⟨e, onLine_3_of_B Bfde fM dM, DiffSide_of_B_sameside Bfde dL fbL, by perma[ab_de.symm]⟩

/-- Euclid I.2, generalization -/
theorem length_eq_of_sameside' (aL : OnLine a L) (bL : ¬OnLine b L) (aM : ¬OnLine a M)
    (dL : OnLine d L) (dM : OnLine d M) : ∃ e, OnLine e M ∧ SameSide e b L ∧
    length e d = length a b := by
  rcases length_eq_of_sameside aL bL aM dL dM with ⟨e, eM, ebL, _⟩
  rcases length_eq_B_of_ne_four (ne_of_online' dL ebL.1) (ne_of_online aL bL) with
    ⟨f, Bedf, ab_df⟩
  exact ⟨f, onLine_3_of_B Bedf eM dM, by perma[sameside_of_B_DiffSide Bedf dL ebL],
    by perma[ab_df.symm]⟩

/-- Euclid I.3, Moving a smaller segment on top of a larger one -/
theorem B_length_eq_of_ne_lt (cd : c ≠ d) (cd_lt_ab : length c d < length a b) :
    ∃ f, B a f b ∧ length a f = length c d := by
rcases length_eq_of_ne a cd with ⟨e, ae_cd⟩
rcases circle_of_ne (ne_of_ne_len' cd ae_cd) with ⟨α, aα, eα⟩
rcases B_oncircle_of_inside_outside (inside_circle_of_center aα)
  (OutCircle_of_lt aα eα (by rwa [← ae_cd] at cd_lt_ab)) with ⟨f, Bafb, fα⟩
have ae_af := length_eq_of_oncircle aα eα fα
exact ⟨f, Bafb, by linarith⟩

/-- Euclid I.5, (part 1), isosceles Triangles have equal angles -/
theorem angle_eq_of_iso (iso_abc : IsoTri a b c) : angle a b c = angle a c b :=
  (sas (iso_abc).2 (iso_abc).2.symm $ by perm).2.2.symm

/-- Euclid I.6, a Triangle with equal angles is isosceles -/
theorem iso_of_angle_eq (tri_abc : Triangle a b c) (abc_eq_acb : angle a b c = angle a c b) :
    length a b = length a c := by
by_contra ab_ac
wlog ab_le_ac : length a b ≤ length a c generalizing b c; exact this (by perma) abc_eq_acb.symm
  (Ne.symm ab_ac) $ by linarith
rcases B_length_eq_of_ne_lt (ne_12_of_tri tri_abc)
  (by perma[Ne.lt_of_le ab_ac ab_le_ac] : length a b < length c a) with ⟨d, Bcda, cd_ab⟩
have ar_cdb_eq_bac : area c d b = area b a c := area_eq_of_sas (by linperm) (by perm) $
  (angle_extension_of_B (ne_32_of_tri tri_abc) Bcda).trans abc_eq_acb.symm
have split_ar_bca := area_add_of_B Bcda (tri231_of_tri123 tri_abc)
have ar_abd_zero : area a b d = 0 := by linperm
have col_abd := col_132_of_col $ col_of_area_zero_ne (ne_12_of_tri tri_abc) ar_abd_zero
exact tri_abc $ col_134_of_col_123_col_124 (ne_32_of_B Bcda) col_abd (col_of_B $ B_symm Bcda)

/-- Euclid I.10, bisecting a segment -/
theorem bisect_segment (ab : a ≠ b) : ∃ e, B a e b ∧ length a e = length b e := by
  rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c, d, L, aL, bL, cdL, eqtri_abc, eqtri_abd⟩
  rcases pt_B_of_DiffSide cdL with ⟨e, eL, Bced⟩
  have acd_bcd : angle a c d = angle b c d := (sss (by perma[eqtri_abc.2.2.2]) rfl $
    by perma[eqtri_abd.2.2.2]).1
  have ae_be : length a e = length b e := (sas eqtri_abc.2.2.2 rfl $ by
    linperm[angle_extension_of_B (Ne.symm $ ne_13_of_tri eqtri_abc.1) Bced,
    angle_extension_of_B (Ne.symm $ ne_23_of_tri eqtri_abc.1) Bced]).1
  refine ⟨e, B_of_length_eq_col (ne_of_Triangle_length_eq
    (tri312 eqtri_abc.1) ae_be) ab ⟨L, aL, eL, bL⟩ ae_be, ae_be⟩

/-- Euclid I.9 lemma, bisecting an angle in an isosceles Triangle -/
theorem bisect_angle_iso (aL : OnLine a L) (bL : OnLine b L) (aM : OnLine a M) (cM : OnLine c M)
    (iso_abc : IsoTri a b c) : ∃ d, angle b a d = angle c a d ∧ SameSide d b M ∧
    SameSide d c L := by
  rcases bisect_segment (ne_23_of_tri iso_abc.1) with ⟨d, Bbdc, bd_cd⟩
  have bad_cad : angle b a d = angle c a d := (sss bd_cd rfl $ by perma[iso_abc.2]).2.2
  refine ⟨d, bad_cad, sameside_of_B_online_3 (B_symm Bbdc) cM $ online_2_of_Triangle aM cM
    iso_abc.1, sameside_of_B_online_3 Bbdc bL $ online_3_of_Triangle aL bL iso_abc.1⟩

/-- Euclid I.9 lemma, bisecting an angle -/
theorem bisect_angle (aL : OnLine a L) (bL : OnLine b L) (aM : OnLine a M) (cM : OnLine c M)
    (tri_abc : Triangle a b c) : ∃ f, angle b a f = angle c a f ∧ SameSide f b M ∧
    SameSide f c L := by
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_abc) (ne_13_of_tri tri_abc) with ⟨d, Babd, ac_bd⟩
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_12_of_tri tri_abc) with ⟨e, Bace, ab_ce⟩
  rcases bisect_angle_iso aL (onLine_3_of_B Babd aL bL) aM (onLine_3_of_B Bace aM cM)
    ⟨tri_of_B_B_tri Babd Bace tri_abc, by linarith[length_sum_of_B Babd, length_sum_of_B Bace]⟩
    with ⟨f, daf_eaf, fdM, feL⟩
  refine ⟨f, by linarith[angle_extension_of_B (ne_of_sameside' aL feL) Babd,
    angle_extension_of_B (ne_of_sameside' aL feL) Bace], sameSide_trans (sameSide_symm fdM) $
    sameSide_symm $ sameSide_of_B_not_onLine_2 Babd aM (online_2_of_Triangle aM cM tri_abc),
    sameSide_trans (sameSide_symm feL) $ sameSide_symm $ sameSide_of_B_not_onLine_2 Bace aL
    (online_3_of_Triangle aL bL tri_abc)⟩

/-- Euclid I.11, Obtaining perpendicular angles from a point on a line -/
theorem perpendicular_of_online (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (fL : ¬OnLine f L) :
    ∃ e, SameSide e f L ∧ angle e b a = rightangle ∧ angle e b c = rightangle := by
  rcases length_eq_B_of_ne (ne_12_of_B Babc) (ne_21_of_B Babc) with ⟨d, Babd, ba_bd⟩
  rcases iseqtri_sameside_of_ne (ne_13_of_B Babd) aL (onLine_3_of_B Babd aL bL) fL
    with ⟨e, eL, efL, eqtri⟩
  have eba_ebd : angle e b a = angle e b d := (sss rfl eqtri.2.2.2 ba_bd).2.1
  have rightangles : angle e b a = rightangle ∧ angle e b c = rightangle :=
    rightangle_of_angle_eq Babc aL (onLine_3_of_B Babc aL bL) eL $ eba_ebd.trans
    $ angle_extension_of_B_B (ne_of_online bL eL) Babc Babd
  refine ⟨e, efL, rightangles⟩

/-- Euclid I.11, Obtaining a perpendicular angle from a point on a line -/
theorem perpendicular_of_online' (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (fL : ¬OnLine f L) : ∃ c, SameSide c f L ∧ angle a b c = rightangle := by
  rcases length_eq_B_of_ne ab ab.symm with ⟨d, Babd, _⟩
  rcases perpendicular_of_online Babd aL bL fL with ⟨c, cfL, right, _⟩
  exact ⟨c, cfL, by perma[right]⟩

/-- Euclid I.12, Obtaining perpendicular angles from a point off a line -/
theorem perpendicular_of_not_online (aL : ¬OnLine a L) : ∃ c d e, B c e d ∧ OnLine c L ∧ OnLine d L
    ∧ OnLine e L ∧ angle a e c = rightangle ∧ angle a e d = rightangle := by
  rcases diffSide_of_not_onLine' aL with ⟨b, abL⟩
  rcases circle_of_ne (ne_of_DiffSide abL) with ⟨α, aα, bα⟩
  rcases pts_line_circle_of_not_sameside aα bα abL.2.2 with ⟨c, d, cd, cL, dL, cα, dα⟩
  rcases bisect_segment cd with ⟨e, Bced, ce_de⟩
  have aec_aed : angle a e c = angle a e d := (sss (length_eq_of_oncircle aα cα dα) ce_de rfl).2.2
  have rightangles : angle a e c = rightangle ∧ angle a e d = rightangle :=
    rightangle_of_angle_eq Bced cL dL aL aec_aed
  refine ⟨c, d, e, Bced, cL, dL, onLine_2_of_B Bced cL dL, rightangles⟩

/-- Euclid I.13, A generalization of I.11. Instead of requiring the angles to be perpendicular,
  they can be arbitrary -/
theorem two_right_of_flat_angle (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (dL : ¬OnLine d L) : angle d b a + angle d b c = 2 * rightangle := by
  rcases line_of_pts b d with ⟨N, bN, dN⟩
  rcases perpendicular_of_online Babc aL bL dL with ⟨e, edL, eba_ra, ebc_ra⟩
  rcases line_of_pts e b with ⟨M, eM, bM⟩
  by_cases dM : OnLine d M; linarith[angle_extension_of_sameside (ne_12_of_B Babc) bL
    ⟨M, bM, eM, dM⟩ edL, angle_extension_of_sameside (ne_32_of_B Babc) bL ⟨M, bM, eM, dM⟩ edL]
  wlog cdM : SameSide c d M generalizing a c; linarith[this (B_symm Babc) (onLine_3_of_B Babc aL
    bL) ebc_ra eba_ra $ sameside_of_B_DiffSide_sameside Babc aL bL bM eM dM edL cdM]
  have ebc_add : angle d b c = angle e b c - angle d b e :=
    by linarith[angle_add_of_sameside bM eM bL (onLine_3_of_B Babc aL bL) cdM edL]
  have dba_add : angle d b a = angle e b d + angle e b a := angle_add_of_sameside bN dN bL aL
    (sameside_of_B_sameside_sameside Babc bL bM bN aL eM dN edL cdM) (sameSide_symm edL)
  linperm

/-- Euclid I.14, the converse of I.13. If angles add to two right angles then you have betweeness-/
theorem flat_of_two_right_angle (bd : b ≠ d) (bL : OnLine b L) (dL : OnLine d L)
    (acL : DiffSide a c L) (two_ra : angle d b a + angle d b c = 2 * rightangle) : B a b c := by
  rcases line_of_pts a b with ⟨N, aN, bN⟩
  rcases length_eq_B_of_ne (ne_of_online' bL acL.1) bd with ⟨e, Babe, -⟩
  have : angle d b a + angle d b e = 2 * rightangle := two_right_of_flat_angle Babe aN bN $
    offline_of_online_offline bd aN bN bL dL acL.1
  have ebc_0 : angle e b c = 0 := angle_zero_of_lt_eq bd bL dL
    (sameside_of_B_DiffSide Babe bL acL) (by linarith)
  have cN := online_of_angle_zero (ne_23_of_B Babe) (ne_of_online bL acL.2.1)
      bN (onLine_3_of_B Babe aN bN) ebc_0
  exact B_of_col_DiffSide ⟨N, aN, bN, cN.1⟩ bL acL

/-- Euclid I.15, vertical angles are equal-/
theorem vertical_angle (Babc : B a b c) (Bdbe : B d b e) (aL : OnLine a L) (bL : OnLine b L)
    (dL : ¬OnLine d L) : angle a b d = angle c b e := by
  rcases line_of_pts d b with ⟨M, dM, bM⟩
  have dba_dbc : angle d b a + angle d b c = 2 * rightangle := two_right_of_flat_angle Babc aL bL dL
  have cbd_cbe : angle c b d + angle c b e = 2 * rightangle := two_right_of_flat_angle Bdbe dM bM $
    offline_of_online_offline (ne_23_of_B Babc) dM bM bL (onLine_3_of_B Babc aL bL) dL
  linperm

/-- Euclid I.15, vertical angles are equal-/
theorem vertical_angle' (Babc : B a b c) (Bdbe : B d b e) (col_abd : ¬Colinear a b d) :
    angle a b d = angle c b e := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact vertical_angle Babc Bdbe aL bL $ online_3_of_Triangle aL bL col_abd

/-- Euclid I.16, external angles are greater than interior angles-/
theorem internal_lt_external (Babc : B a b c) (tri_abd : Triangle a b d) :
    angle b d a < angle d b c := by
  rcases bisect_segment (ne_23_of_tri tri_abd) with ⟨e, Bbed, be_de⟩
  rcases col_of_B Bbed with ⟨L, bL, eL, dL⟩
  rcases col_of_B Babc with ⟨M, aM, bM, cM⟩
  rcases length_eq_B_of_ne (ne_of_col_tri ⟨L, bL, eL, dL⟩ tri_abd) (ne_of_col_tri' ⟨L, bL, eL, dL⟩
    tri_abd) with ⟨f, Baef, ea_ef⟩
  have aed_feb : angle a e d = angle f e b := vertical_angle' Baef (B_symm Bbed) $ tri_of_B_tri
    Bbed tri_abd
  have eda_ebf : angle e d a = angle e b f := (sas ea_ef (by perm; exact be_de.symm) aed_feb).2.2
  have ebc_split : angle e b c = angle f b e + angle f b c := angle_add_of_sameside bL eL bM cM
    (sameside_of_B_B Babc Baef bL eL $ online_1_of_Triangle bL dL tri_abd) $ sameside_of_B_online_3
    Baef aM $ offline_of_B_B_tri Baef Bbed aM bM tri_abd
  linperm[zero_lt_angle_of_offline (ne_23_of_B Babc) bM cM $ offline_of_B_B_tri Baef Bbed aM bM
    tri_abd, angle_extension_of_B (ne_23_of_B Babc) Bbed, angle_extension_of_B (ne_31_of_tri
    tri_abd) (B_symm Bbed)]

/-- Euclid I.16, external angles are greater than interior angles-/
theorem internal_lt_external' (Babc : B a b c) (tri_abd : Triangle a b d) :
    angle b a d < angle d b c := by
  rcases length_eq_B_of_ne (ne_32_of_tri tri_abd) (ne_23_of_tri tri_abd) with ⟨e, Bdbe, -⟩
  have : angle b a d < angle a b e := internal_lt_external Bdbe (by perma)
  have : angle e b a = angle d b c := vertical_angle' (B_symm Bdbe) Babc $ tri213 $
    tri_143_of_tri_col (ne_23_of_B Bdbe) (by perma) $ col_213_of_col $ col_of_B Bdbe
  linperm

/-- Euclid I.17, Any two angles of a Triangle sum to less than two right angles-/
theorem two_ang_lt_two_right_of_tri (tri_abc : Triangle a b c) :
    angle a b c + angle a c b < 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_32_of_tri tri_abc) (ne_23_of_tri tri_abc) with ⟨d, Bcbd, _⟩
  rcases line_of_pts c b with ⟨L, cL, bL⟩
  have bca_lt_abd := internal_lt_external' Bcbd $ tri321 tri_abc
  have cbd_split := two_right_of_flat_angle Bcbd cL bL (online_1_of_Triangle bL cL tri_abc)
  linperm

/-- Euclid I.17 corollary, An obtuse angle in a Triangle is bigger than the other two angles-/
theorem ang_lt_obtuse_of_tri (tri_abc : Triangle a b c) (right_lt_abc : rightangle < angle a b c) :
    angle b a c < angle a b c ∧ angle a c b < angle a b c := by
  have abc_acb_ra := two_ang_lt_two_right_of_tri tri_abc
  have cba_cab_ra := two_ang_lt_two_right_of_tri $ tri321 tri_abc
  exact ⟨by linperm, by linperm⟩

/-- Euclid I.18, Opposite larger sides you have larger angles in a Triangle-/
theorem ang_lt_of_len_lt (tri_abc : Triangle a b c) (len_lt : length c a < length c b) :
    angle c b a < angle c a b := by
  rcases B_length_eq_of_ne_lt (ne_31_of_tri tri_abc) len_lt with ⟨d, Bcdb, cd_ca⟩
  have : angle d b a < angle a d c := internal_lt_external' (B_symm Bcdb) $ tri321 $ tri_of_B_tri
    Bcdb $ tri132_of_tri123 tri_abc
  have : angle c a d = angle c d a := angle_eq_of_iso ⟨tri312 $ tri_of_B_tri (B_symm Bcdb) tri_abc,
    cd_ca.symm⟩
  have : angle c a d < angle c a b := angle_lt_of_B_tri Bcdb tri_abc
  linarith[angle_extension_of_B (ne_21_of_tri tri_abc) $ B_symm Bcdb, angle_symm c d a]

/--Euclid I.19, larger angles correspond to larger opposide sides in a Triangle-/
theorem len_lt_of_ang_lt (tri_abc : Triangle a b c) (ang_lt : angle c b a < angle c a b) :
    length c a < length c b := by
  push_contra cb_le_ca at cb_le_ca
  by_cases cb_ca : length c b = length c a
  · linarith[angle_eq_of_iso ⟨by perma, cb_ca.symm⟩]
  linarith[ang_lt_of_len_lt (by perma) $ lt_of_le_of_ne cb_le_ca cb_ca]

/--Euclid I.20, a Triangle inequality-/
theorem len_lt_of_tri' (tri_abc : Triangle a b c) : length a b < length a c + length b c := by
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_23_of_tri tri_abc) with ⟨d, Bacd, bc_cd⟩
  have : angle d b c < angle d b a := angle_lt_of_B_tri (B_symm Bacd) $ tri312 $ tri_143_of_tri_col
    (ne_13_of_B Bacd) (by perma) $ col_of_B Bacd
  have : angle c d b = angle c b d := angle_eq_of_iso ⟨tri_143_of_tri_col (ne_23_of_B Bacd)
    (by perma) $ col_213_of_col $ col_of_B Bacd, by perma[bc_cd.symm]⟩
  have : length a b < length a d := len_lt_of_ang_lt (tri321 $ tri_143_of_tri_col (ne_13_of_B Bacd)
    (tri132_of_tri123 tri_abc) $ col_of_B Bacd) $
    by linarith[angle_symm c b d, angle_symm d b a, angle_extension_of_B (ne_of_col_tri'
    (col_132_of_col $ col_of_B Bacd) $ tri213 tri_abc) $ B_symm Bacd]
  have : length a c + length c d = length a d := length_sum_of_B Bacd
  linarith

/--Euclid I.20, the Triangle inequalities-/
theorem len_lt_of_tri (tri_abc : Triangle a b c) : length a b < length a c + length b c ∧
    length b c < length b a + length c a ∧ length c a < length c b + length a b :=
  ⟨len_lt_of_tri' tri_abc, len_lt_of_tri' $ by perma, len_lt_of_tri' $ by perma⟩

/--Euclid I.21, with one Triangle in another and sharing a base, the sum of the other two sides of
   the outer Triangle is larger than that for the inner Triangle, and the top angle of the outer
   Triangle is smaller than that of the interior Triangle-/
theorem angle_len_leq_of_tri_in_out (bL : OnLine b L) (cL : OnLine c L) (aM : OnLine a M)
    (cM : OnLine c M) (aN : OnLine a N) (bN : OnLine b N) (adL : SameSide a d L)
    (bdM : SameSide b d M) (cdN : SameSide c d N) :
    length b d + length c d < length a b + length a c ∧ angle b a c < angle b d c := by
rcases tri_tri_B_B_of_int bL cL aM cM aN bN adL bdM cdN with ⟨e, Baec, Bbde, tri_abe, tri_cde⟩
have be_lt_ba_ea := (len_lt_of_tri tri_abe).2.1
have cd_lt_ce_de := (len_lt_of_tri tri_cde).1
have ac_split := length_sum_of_B Baec
have be_split := length_sum_of_B Bbde
have dec_lt_cdb := internal_lt_external' (B_symm Bbde) (tri321 tri_cde)
have eab_lt_bec := internal_lt_external' Baec (tri132_of_tri123 tri_abe)
exact ⟨by linperm, by linperm[angle_extension_of_B (ne_23_of_B Baec) (B_symm Bbde),
  angle_extension_of_B (ne_of_sameside bL adL) Baec]⟩

/--Euclid I.22, making a Triangle with prescribed lengths-/
theorem Triangle_of_ineq (aL : OnLine a L) (bL : OnLine b L) (fL : ¬OnLine f L)
    (ab_lt_a1a2_b1b2 : length a b < length a1 a2 + length b1 b2)
    (a1a2_lt_ab_b1b2 : length a1 a2 < length a b + length b1 b2)
    (b1b2_lt_a1a2_ab : length b1 b2 < length a1 a2 + length a b) :
    ∃ e, length a e = length a1 a2 ∧ length b e = length b1 b2 ∧ SameSide e f L := by
  rcases length_eq_B_of_ne_four (Ne.symm (fun n => by linarith[length_zero_of_eq n] : a ≠ b))
    ((fun n => by linarith[length_zero_of_eq n] : a1 ≠ a2)) with ⟨c, Bbac, a1a2_ac⟩
  rcases length_eq_B_of_ne_four (fun n => by linarith[length_zero_of_eq n] : a ≠ b)
    ((fun n => by linarith[length_zero_of_eq n] : b1 ≠ b2)) with ⟨d, Babd, b1b2_bd⟩
  rcases circle_of_ne $ ne_23_of_B Bbac with ⟨α, aα, cα⟩
  rcases circle_of_ne $ ne_23_of_B Babd with ⟨β, bβ, dβ⟩
  rcases pt_sameSide_of_circlesInter aL bL fL aα bβ $ circint_of_lt_lt aα bβ cα dβ
    (by apply abs_lt.mpr; exact ⟨by linarith, by linarith⟩) $ by linarith with ⟨e, efL, eα, eβ⟩
  have : length a c = length a e := length_eq_of_oncircle aα cα eα
  have : length b d = length b e := length_eq_of_oncircle bβ dβ eβ
  exact ⟨e, by linarith, by linarith, efL⟩

/--Euclid I.22, corollary, if you are copying a triangle-/
theorem triangle_copy (tri_def : Triangle d e f) (aL : OnLine a L) (bL : OnLine b L)
    (gL : ¬OnLine g L) (ab_de : length a b = length d e) :
    ∃ c, length a c = length d f ∧ length b c = length e f ∧ SameSide c g L :=
  Triangle_of_ineq aL bL gL (by linarith[len_lt_of_tri tri_def] : length a b < length d f +
    length e f) (by linperm[len_lt_of_tri tri_def]) (by linperm[len_lt_of_tri tri_def])

/--Euclid I.23, copying an angle-/
theorem angle_copy (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (jL : ¬OnLine j L)
    (tri_cde : Triangle c d e) : ∃ h, angle h a b = angle e c d ∧ SameSide h j L := by
  rcases length_eq_B_of_ne_four ab (ne_12_of_tri tri_cde) with ⟨g, Babg, cd_bg⟩
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_cde) ab with ⟨f, Bcdf, ab_df⟩
  have cf_ag : length c f = length a g := by linarith[length_sum_of_B Babg, length_sum_of_B Bcdf]
  have ⟨cf_lt_ce_ef, _, _⟩ := len_lt_of_tri $ tri_143_of_tri_col (ne_13_of_B
    Bcdf) tri_cde $ col_of_B Bcdf; perm only [length] at *
  rcases Triangle_of_ineq aL (onLine_3_of_B Babg aL bL) jL (by rwa [cf_ag] at cf_lt_ce_ef) (by
    linarith) $ by linarith with ⟨h, ah_ce, gh_ef, hjL⟩
  have : angle h a g = angle e c f := (sss ah_ce (by perma[gh_ef]) cf_ag.symm).2.1
  exact ⟨h, by linarith[angle_extension_of_B' (ne_of_sameside' aL hjL) Babg, angle_extension_of_B'
                (ne_13_of_tri tri_cde) Bcdf], hjL⟩

/--Euclid I.23, copying an angle-/
theorem angle_copy' (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (jL : ¬OnLine j L)
    (tri_cde : Triangle c d e) : ∃ h, angle h a b = angle e c d ∧ DiffSide h j L := by
  rcases diffSide_of_not_onLine jL with ⟨f, fL, jfL⟩
  rcases angle_copy ab aL bL fL tri_cde with ⟨h, hab_ecd, hfL⟩
  refine ⟨h, hab_ecd, DiffSide_of_sameside_DiffSide (sameSide_symm hfL) $ DiffSide_symm
    ⟨jL, fL, jfL⟩⟩

theorem sameside_of_len_lt_tri (dN : OnLine d N) (fN : OnLine f N) (fO : OnLine f O)
    (gO : OnLine g O) (tri_def : Triangle d e f) (tri_gdf : Triangle g d f) (egN : DiffSide e g N)
    (ab_le_ac : length d e ≤ length d f) (tri_fge : ¬Colinear f g e)
    (dgf_dfg : angle d g f = angle d f g) : SameSide d e O := by
  by_contra deO
  rcases pt_B_of_DiffSide ⟨online_2_of_Triangle gO fO tri_gdf, online_3_of_Triangle fO gO
    tri_fge, deO⟩ with ⟨x, xO, Bdxe⟩
  have xgN := DiffSide_of_sameside_DiffSide (sameSide_symm $ sameside_of_B_not_online_3 Bdxe dN
    (online_2_of_Triangle dN fN tri_def)) egN
  have tri_xfd := Triangle_of_ne_online (ne_12_of_B $ B_of_col_DiffSide ⟨O, xO, fO, gO⟩ fN xgN)
    xO fO $ online_2_of_Triangle gO fO tri_gdf
  have dfg_lt_ra := two_ang_lt_two_right_of_tri $ tri213 tri_gdf
  have gfx_split := two_right_of_flat_angle (B_of_col_DiffSide ⟨O, xO, fO, gO⟩ fN xgN) xO fO $
    online_2_of_Triangle gO fO tri_gdf
  have fxd_xfd := (ang_lt_obtuse_of_tri tri_xfd (by linperm)).1
  have df_dx := len_lt_of_ang_lt (tri213 tri_xfd) $ by linperm
  linperm[len_pos_of_nq (ne_23_of_B Bdxe), length_sum_of_B Bdxe]

/--Euclid I.24, If two Triangles have two congruent sides, and the included angle of one is bigger
   than the other then the opposite side is also bigger than that of the other Triangle-/
theorem opp_lt_of_ss_lt (tri_abc : Triangle a b c) (tri_def : Triangle d e f)
    (ab_de : length a b = length d e) (ac_df : length a c = length d f)
    (edf_lt_bac : angle e d f < angle b a c) : length e f < length b c := by
  wlog ab_le_ac : length a b ≤ length a c generalizing b c e f; perma[this (by perma) (by perma)
    ac_df ab_de (by perma) $ by linperm]
  rcases line_of_pts d e with ⟨L, dL, eL⟩
  rcases line_of_pts d f with ⟨N, dN, fN⟩
  rcases line_of_pts f e with ⟨P, fP, eP⟩
  rcases angle_copy (ne_12_of_tri tri_def) dL eL (online_3_of_Triangle dL eL tri_def) tri_abc
    with ⟨h, hde_cab, hfL⟩
  rcases line_of_pts d h with ⟨M, dM, hM⟩
  rcases online_sameside_DiffSide_len_ang_tri_of_ang_lt tri_def dL eL hM dM dN fN hfL (by linperm)
    with ⟨g, gM, fM, hgL, fd_dg, hde_gde, nn_dge, tri_gdf, egN⟩
  rcases line_of_pts f g with ⟨O, fO, gO⟩
  have dgf_dfg := angle_eq_of_iso ⟨tri213 tri_gdf, by linperm⟩
  have bc_eg := (sas ab_de (by linperm : length a c = length d g) $ by linperm).1
  by_cases tri_fge : Colinear f g e; linperm[length_sum_of_B $ B_of_col_DiffSide (by perma
    [tri_fge]) fN egN, len_pos_of_nq (ne_of_online gM fM)]
  have gfe_split := angle_add_of_sameside fO gO fP eP (sameSide_symm $ sameside_of_len_lt_tri dN fN
    fO gO tri_def tri_gdf egN (by linarith) tri_fge dgf_dfg) $ sameside_of_sameside_DiffSide fO fN
    fP gO dN eP (sameside_of_len_lt_tri dN fN fO gO tri_def tri_gdf egN (by linarith) tri_fge
    dgf_dfg) $ DiffSide_symm egN
  have dgf_split := angle_add_of_sameside gM dM gO fO (sameSide_symm $
    sameside_of_sameside_DiffSide dL dN dM eL fN gM (sameSide_symm $ sameSide_trans hgL hfL) egN) $
    sameside_of_len_lt_tri dN fN fO gO tri_def tri_gdf egN (by linarith) tri_fge dgf_dfg
  have ef_eg := len_lt_of_ang_lt tri_fge (by linperm[zero_lt_angle_of_tri $ tri321 tri_def])
  rwa[bc_eg]

/--Euclid I.25, the converse of I.24-/
theorem ang_lt_of_ss_lt (tri_abc : Triangle a b c) (tri_def : Triangle d e f)
    (ab_de : length a b = length d e) (ac_df : length a c = length d f)
    (ef_bc : length e f < length b c) : angle e d f < angle b a c := by
  by_cases edf_bac : angle e d f = angle b a c;
  have bc_ef := (sas ab_de ac_df edf_bac.symm).1; linperm
  by_cases bac_edf : angle b a c < angle e d f;
  have bc_lt_ef := opp_lt_of_ss_lt tri_def tri_abc ab_de.symm ac_df.symm bac_edf; linperm
  push_neg at bac_edf; exact Ne.lt_of_le edf_bac bac_edf

/--Euclid I.26, if two Triangles have two corresponding angles equal and the included sides equal,
   then they are congruent-/
theorem asa' (tri_abc : Triangle a b c) (tri_def : Triangle d e f) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e := by
  wlog df_le_ac : length d f ≤ length a c generalizing a b c d e f; have' := this tri_def tri_abc
    ab_de.symm bac_edf.symm abc_def.symm (by linarith); tauto
  by_cases ac_df : length a c = length d f; have := sas ab_de ac_df bac_edf; tauto
  rcases B_length_eq_of_ne_lt (ne_13_of_tri tri_def) $ Ne.lt_of_le (Ne.symm ac_df) df_le_ac
    with ⟨g, Bagc, ag_df⟩
  have : angle a b g = angle d e f :=
    (sas ag_df ab_de $ by linperm[angle_extension_of_B' (ne_12_of_tri tri_abc) Bagc]).2.2
  exfalso; exact ang_2_nonzero_of_tri (tri_of_B_tri Bagc $ tri213 tri_abc) $ angle_zero_of_lt_eq_B
    (ne_21_of_tri tri_abc) Bagc tri_abc $ by linarith

/--Euclid I.26, if two Triangles have two corresponding angles equal and the included sides equal,
   then they are congruent-/
theorem asa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  asa' tri_abc (Triangle_of_asa tri_abc ab_de bac_edf abc_def) ab_de bac_edf abc_def

/--Euclid I.26, if two Triangles have two corresponding angles equal and a non-included side equal,
   then they are congruent-/
theorem saa' (tri_abc : Triangle a b c) (tri_def : Triangle d e f) (ac_df : length a c =
    length d f) (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a b = length d e ∧ length b c = length e f ∧ angle a c b = angle d f e := by
  wlog de_le_ab : length d e ≤ length a b generalizing a b c d e f; have := this tri_def tri_abc
     ac_df.symm bac_edf.symm abc_def.symm (by linarith); tauto
  by_cases ab_de : length a b = length d e; have := sas ab_de ac_df bac_edf; tauto
  rcases B_length_eq_of_ne_lt (ne_12_of_tri tri_def) $ Ne.lt_of_le (Ne.symm ab_de) de_le_ab
    with ⟨g, Bagb, ag_de⟩
  have : angle c g a = angle d e f :=
    by perma[(sas ag_de ac_df $ by linarith[angle_extension_of_B (ne_13_of_tri tri_abc) Bagb]).2.1]
  have : angle g b c < angle c g a := internal_lt_external' (B_symm Bagb) $
    tri_143_of_tri_col (ne_32_of_B Bagb) (tri213 tri_abc) $ by perma[col_of_B Bagb]
  linarith[angle_extension_of_B (ne_23_of_tri tri_abc) (B_symm Bagb)]

/--Euclid I.26, if two Triangles have two corresponding angles equal and a non-included side equal,
   then they are congruent-/
theorem saa (de : d ≠ e) (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a b = length d e ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  saa' tri_abc (Triangle_of_saa de tri_abc ac_df bac_edf abc_def) ac_df bac_edf abc_def

/--Euclid I.27, if the alternate angles are equal, then the lines it formed from are Parallel-/
theorem Para_of_ang_eq (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : DiffSide a d L)
    (cba_bcd : angle c b a = angle b c d) : Para M N := by
  intro e; push_contra eMN at eMN
  wlog aeL : SameSide a e L generalizing a b c d e M N; exact this bc.symm dN cN cL bL bM aM (by
    perma) (by linperm) e (by tauto) $ sameside_of_DiffSide_DiffSide adL ⟨adL.1,
    offline_of_online_inter bc aM bM bL cL cN dN adL.1 adL.2.1 eMN.1 eMN.2, aeL⟩
  have : angle c b e < angle b c d := internal_lt_external (B_of_col_DiffSide ⟨N, eMN.2, cN, dN⟩ cL
    $ DiffSide_of_sameside_DiffSide aeL adL) $ by perma[Triangle_of_ne_online bc bL cL $
                not_onLine_of_sameSide $ sameSide_symm aeL]
  linperm[angle_extension_of_sameside bc.symm bL ⟨M, bM, aM, eMN.1⟩ aeL]

/--Euclid I.28 part 1, If the exterior angle is equal to the internal and opposite angle then we
    have parallel Lines-/
theorem para_of_ext_ang_eq (Bebc : B e b c) (bM : OnLine b M) (fM : OnLine f M)
    (bL : OnLine b L) (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (fdL : SameSide f d L)
    (ebf_bcd : angle e b f = angle b c d) : Para M N := by
  rcases length_eq_B_of_ne (ne_of_sameside bL fdL) $ ne_of_sameside' bL fdL with ⟨a, Bfba, _⟩
  have ebf_cba := vertical_angle Bebc Bfba (onLine_3_of_B (B_symm Bebc) cL bL) bL
    $ online_of_B_online' Bfba bL (DiffSide_of_B_sameside Bfba bL fdL).1
  exact Para_of_ang_eq (ne_23_of_B Bebc) (onLine_3_of_B Bfba fM bM) bM bL cL cN dN
    (DiffSide_of_B_sameside Bfba bL fdL) $ by linperm

/--Euclid I.28 part 2, If the sum of the interior angles is equal to two right angles then we have
    parallel Lines-/
theorem para_of_int_ang_sum (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : SameSide a d L)
    (abc_bcd : angle a b c + angle b c d = 2 * rightangle) : Para M N := by
  rcases length_eq_B_of_ne (ne_of_sameside bL adL) $ ne_of_sameside' bL adL with ⟨e, Babe, _⟩
  have abe_split := two_right_of_flat_angle Babe aM bM $ online_3_of_Triangle aM bM $
    tri_of_sameside bc bL cL adL
  exact Para_of_ang_eq bc (onLine_3_of_B Babe aM bM) bM bL cL cN dN
    (DiffSide_of_B_sameside Babe bL adL) $ by linperm

/--Euclid I.29, basic properties of alternate, exterior, and interior angles with Parallel lines-/
theorem alternate_eq_of_Para (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : DiffSide a d L)
    (ParaMN : Para M N) : angle a b c = angle b c d := by
  wlog bcd_lt_abc : angle b c d < angle a b c generalizing a b c d M N; by_cases angle a b c =
    angle b c d; exact h; push_neg at bcd_lt_abc; linperm[this dN cN cL bL bM aM (by perma)
    (Para_symm ParaMN) $ by linperm[lt_of_le_of_ne bcd_lt_abc h]]
  rcases length_eq_B_of_ne (ne_of_online' bL adL.1) (ne_of_online bL adL.1) with ⟨e, Babe, -⟩
  have : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_Para' cN ParaMN
  have : angle c b e + angle b c d < 2 * rightangle := by perm at *; linarith
  rcases unparallel_postulate (ne_of_Para bM cN ParaMN) (onLine_3_of_B Babe aM bM) bM bL cL cN dN
    (sameSide_symm $ sameside_of_B_DiffSide Babe bL adL) (by perma) with ⟨f, fM, fN, -⟩
  exfalso; exact not_Para_of_inter fM fN ParaMN

/--Euclid I.29, basic properties of alternate, exterior, and interior angles with Parallel lines-/
theorem interior_rightangles_of_Para (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : SameSide a d L)
    (ParaMN : Para M N) : angle a b c + angle b c d = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_of_sameside bL adL) (ne_of_sameside' bL adL) with ⟨e, Babe, -⟩
  have ras : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_Para' cN ParaMN
  have : angle e b c = angle b c d := alternate_eq_of_Para (onLine_3_of_B Babe aM bM) bM bL cL
    cN dN (DiffSide_of_B_sameside Babe bL adL) ParaMN
  linperm

/--Euclid I.29, corresponding angles are equal-/
theorem correspond_of_Para (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M)
    (dM : OnLine d M) (cN : OnLine c N) (eN : OnLine e N) (deL : SameSide d e L)
    (ParaMN : Para M N) : angle a b d = angle b c e := by
  have : angle a b d + angle d b c = 2 * rightangle :=
    by perma[two_right_of_flat_angle Babc aL bL (not_onLine_of_sameSide deL)]
  have : angle d b c + angle b c e = 2 * rightangle :=
    interior_rightangles_of_Para dM bM bL (onLine_3_of_B Babc aL bL) cN eN deL ParaMN
  linarith

theorem right_of_Para_right (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L) (cL : OnLine c L)
    (cN : OnLine c N) (dN : OnLine d N) (aL : ¬OnLine a L) (dL : ¬OnLine d L)
    (bcd : angle b c d = rightangle) (ParaMN : Para M N) : angle a b c = rightangle := by
  by_cases adL : SameSide a d L
  linperm[interior_rightangles_of_Para aM bM bL cL cN dN adL ParaMN]
  linperm[alternate_eq_of_Para aM bM bL cL cN dN ⟨aL, dL, adL⟩ ParaMN]

/--Euclid I.30, transitivity of Parallel lines-/
theorem Para_trans (MN : M ≠ N) (ParaLM : Para L M) (ParaLN : Para L N) : Para M N := by
  intro x; push_contra int at int
  rcases perpendicular_of_not_online (offline_of_Para' int.1 ParaLM)
    with ⟨c, d, y, Bcyd, cL, dL, yL, xyc, xyd⟩
  rcases line_of_pts x y with ⟨O, xO, yO⟩
  rcases online_ne_of_point_line x M with ⟨a, xa, aM⟩
  rcases sameside_of_offline yO (offline_of_online_offline xa yO xO int.1 aM
    $ offline_of_Para yL ParaLM) (offline_of_Para yL ParaLN) xO int.2 with ⟨b, bN, baO⟩
  wlog yaN : SameSide y a N generalizing x y a b c d N M O; exact this MN.symm ParaLN ParaLM x
    ⟨int.2, int.1⟩ c d y Bcyd cL dL yL xyc xyd O xO yO b (ne_of_sameside xO baO).symm bN a aM
    (by perma[baO]) $ sameside_of_sameside_DiffSide xO int.2 int.1 yO bN aM baO ⟨offline_of_Para
    yL ParaLN, offline_of_online_offline xa bN int.2 int.1 aM $ online_of_ne_ne
    (ne_of_sameside xO baO) MN.symm bN int.2 int.1, yaN⟩
  have split := angle_add_of_sameside int.2 bN xO yO yaN baO
  have axy := right_of_Para_right aM int.1 xO yO yL cL (not_onLine_of_sameSide $ sameSide_symm baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_Para' int.1 ParaLM)) xyc
    (Para_symm ParaLM)
  have bxy := right_of_Para_right bN int.2 xO yO yL cL (not_onLine_of_sameSide baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_Para' int.1 ParaLM)) xyc
    (Para_symm ParaLN)
  linarith[zero_lt_angle_of_tri $ Triangle_of_ne_online (ne_of_sameside xO baO).symm int.2 bN
    (not_onLine_of_sameSide $ sameSide_symm yaN)]

/--Euclid I.30, a corollary, a contrapositive of sorts of I.30-/
theorem lines_inter_of_para (LM : L ≠ M) (aL : OnLine a L) (aM : OnLine a M) (paraMN : Para M N) :
    ∃ b, OnLine b L ∧ OnLine b N := by
  by_cases paraLN : Para L N; have := Para_trans LM (Para_symm paraLN) (Para_symm paraMN) a; tauto
  unfold Para at paraLN; push_neg at paraLN; exact paraLN

/--Euclid I.31, through a point off a line there exists a Parallel line-/
theorem Para_of_offline (aM : ¬OnLine a M) : ∃ N, OnLine a N ∧ Para M N := by
  rcases online_ne_of_line M with ⟨b, c, bc, bM, cM⟩
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases angle_copy' (ne_of_online' bM aM) aL bL (offline_of_online_offline bc aL bL bM cM aM)
    (Triangle_of_ne_online bc bM cM aM) with ⟨d, bad_abc, cdL⟩; perm at *
  rcases line_of_pts a d with ⟨N, aN, dN⟩
  refine ⟨N, aN, Para_of_ang_eq (ne_of_online bM aM) cM bM bL aL aN dN cdL bad_abc.symm⟩

/--Euclid I.32, the exterior angle equals the sum of the other two angles and the sum of all three
  interior angles adds to two right angles-/
theorem ext_int_sum_of_tri (Bbcd : B b c d) (tri_abc : Triangle a b c) : angle a c d = angle b a c +
    angle a b c ∧ angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  rcases line_of_pts c d with ⟨O, cO, dO⟩
  rcases Para_of_offline (online_3_of_Triangle aL bL tri_abc) with ⟨M, cM, ParaLM⟩
  rcases length_eq_of_sameside aN (online_2_of_Triangle aN cN tri_abc) (offline_of_Para aL ParaLM)
    cN cM with ⟨e, eM, ebN, _⟩
  have bac_ace := alternate_eq_of_Para bL aL aN cN cM eM (by perma[ebN]) ParaLM
  have dce_cba := correspond_of_Para (B_symm Bbcd) dO cO cM eM bL aL (sameside_of_sameside_DiffSide
    cM cN cO eM aN (onLine_3_of_B (B_symm Bbcd) dO cO) (sameside_of_Para_online aL bL ParaLM) ebN)
    (by perma[ParaLM])
  have acd_split := angle_add_of_sameside cN aN cO dO
    (by perma[sameside_of_B_DiffSide Bbcd cN (by perma[ebN])]) (by perma
    [(sameside_of_sameside_DiffSide cM cN cO eM aN (onLine_3_of_B (B_symm Bbcd) dO cO)
    (sameside_of_Para_online aL bL ParaLM) ebN)])
  have flat_sum := two_right_of_flat_angle Bbcd (onLine_3_of_B (B_symm Bbcd) dO cO) cO
    (online_1_of_Triangle (onLine_3_of_B (B_symm Bbcd) dO cO) cO tri_abc)
  exact ⟨by linperm, by linperm⟩

theorem sum_two_right_of_tri (tri_abc : Triangle a b c) :
    angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_23_of_tri tri_abc) (ne_32_of_tri tri_abc) with ⟨d, Bbcd, _⟩
  exact (ext_int_sum_of_tri Bbcd tri_abc).2

/-- Euclid I.33, Parallel lines with pair of points with same length make a Parallelogram -/
theorem pgram_of_Para_len_eq (aL : OnLine a L) (bL : OnLine b L) (bO : OnLine b O)
    (dO : OnLine d O) (dM : OnLine d M) (cM : OnLine c M) (cN : OnLine c N) (aN : OnLine a N)
    (bP : OnLine b P) (cP : OnLine c P) (aPd : DiffSide a d P) (ParaLM : Para L M)
    (ab_cd : length a b = length c d) : Paragram a b d c L O M N := by
  have abc_bcd := alternate_eq_of_Para aL bL bP cP cM dM aPd ParaLM
  obtain ⟨-, -, bca_cbd⟩ := sas (by perma : length b a = length c d) (length_symm b c) (by perma)
  exact ⟨aL, bL, bO, dO, dM, cM, cN, aN, ParaLM, Para_symm $
    Para_of_ang_eq (ne_of_Para' bL cM ParaLM) aN cN cP bP bO dO aPd bca_cbd⟩

/--Euclid I.34, basic length, angle, and area properties of Paralellograms-/
theorem len_ang_area_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    length a b = length c d ∧ angle b a d = angle b c d ∧ area a b d = area b c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  rcases line_of_pts b d with ⟨L, bL, dL⟩
  have abd_bdc : angle a b d = angle b d c := alternate_eq_of_Para aM bM bL dL
    dO cO (DiffSide_of_Paragram bL dL pgram) ParaMO
  have adb_dbc : angle a d b = angle d b c := alternate_eq_of_Para aP dP dL bL bN cN
    (DiffSide_of_Paragram bL dL pgram) $ Para_symm ParaNP; perm at adb_dbc
  have ⟨ba_dc, da_bc, bad_dcb⟩ := asa (by perma[tri124_of_Paragram pgram])
    (length_symm b d) (by perma : angle d b a = angle b d c) (by perma)
  have : area b a d = area d c b := area_eq_of_SSS ba_dc (length_symm b d) (by linperm[da_bc])
  perm at *; exact ⟨ba_dc, bad_dcb, this⟩

/--Euclid I.34, basic length properties of Paralellograms-/
theorem len_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    length a b = length c d := (len_ang_area_eq_of_Parallelogram pgram).1

/--Euclid I.34, basic length properties of Paralellograms-/
theorem len_eq_of_Parallelogram' (pgram : Paragram a b c d M N O P) :
    length a d = length c b := by
    have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram; exact len_eq_of_Parallelogram
      ⟨aP, dP, dO, cO, cN, bN, bM, aM, Para_symm ParaNP, Para_symm ParaMO⟩

/--Euclid I.34, basic area properties of Paralellograms-/
theorem area_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    area a b d = area b c d := (len_ang_area_eq_of_Parallelogram pgram).2.2

lemma B_sameside_of_2_Paragram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : B f e a ∧ SameSide d e P := by
  have ad_cb := len_eq_of_Parallelogram pgram1; have ef_cb := len_eq_of_Parallelogram pgram2
  rcases B_or_B_of_sameside (fun ae => by rw [←ae] at ef_cb; linarith[length_sum_perm_of_B Badf])
    pgram2.2.2.1 ⟨L, pgram2.2.1, pgram1.1, pgram2.1⟩ $ sameside_of_B_prgram_pgram_trans' Badf
    pgram1 pgram2 with Bet | Bet
  linperm[length_sum_perm_of_B Bet, length_sum_perm_of_B Badf]
  exact ⟨Bet, sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2⟩

/--Euclid I.35, Parallelograms sharing two Parallels have the same area-/
theorem area_eq_of_Paragram (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q):
    area a d b + area d b c = area e f b + area f b c := by
  wlog Badf : B a d f generalizing a b c d e f L M N O P Q; by_cases df : d = f; rw [←df] at pgram2
    ⊢; linperm [(len_ang_area_eq_of_Parallelogram pgram1).2.2, (len_ang_area_eq_of_Parallelogram
    pgram2).2.2]; exact (this pgram2 pgram1 $ B_of_B_2_Paragram df Badf pgram1 pgram2).symm
  have ⟨Bfea, deP⟩ := B_sameside_of_2_Paragram Badf pgram1 pgram2
  have ⟨aL, dL, dM, cM, cN, bN, bO, aO, ParaLN, ParaMO⟩ := pgram1
  have ⟨eL, fL, fP, cP, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  have fdc_dab := correspond_of_Para (B_symm Badf) fL dL dM cM aO bO
    (sameside_of_Para_online' cN bN ParaLN) ParaMO
  have aeb_efc := correspond_of_Para (B_symm Bfea) aL eL eQ bQ fP cP
    (sameside_of_Para_online' bN cN ParaLN) $ Para_symm ParaPQ
  have dc_ab : length d c = length a b := by linperm[len_eq_of_Parallelogram' pgram1]
  have ae_df := (saa (ne_32_of_B Bfea) (tri_of_sameside (ne_of_Para fL cN ParaLN) fP cP deP) dc_ab
    (fdc_dab.trans (angle_extension_of_sameside (ne_of_Para' aL bN ParaLN) aO ⟨L, aL, dL, eL⟩ $
    by perma[(B_sameside_of_2_Paragram Bfea ⟨fL, eL, eQ, bQ, bN, cN, cP, fP, ParaLN, Para_symm
    ParaPQ⟩ ⟨dL, aL, aO, bO, bN, cN, cM, dM, ParaLN, Para_symm ParaMO⟩).2])) (aeb_efc.trans $
    angle_extension_of_sameside (ne_of_Para' fL cN ParaLN) fP ⟨L, fL, eL, dL⟩ $ by
    perma[deP]).symm).1.symm
  have ab_cd := len_eq_of_Parallelogram' pgram1; have eb_cf := len_eq_of_Parallelogram' pgram2
  have aeb_dfc := area_eq_of_SSS ae_df (by perma : length a b = length d c) $ by perma[eb_cf]
  have ar1 := Paragram_area_comm pgram1
  have ar2 := quad_area_comm aL fL fP cP cN bN (sameside_of_Para_online aL fL ParaLN)
    (sameside_of_Para_online' cN bN ParaLN) $ sameside_of_B_Para Bfea fP eQ bQ ParaPQ
  have ar3 := area_add_of_B_offline Badf aL fL $ offline_of_Para' cN ParaLN
  have ar4 := area_add_of_B_offline Bfea fL aL $ offline_of_Para' bN ParaLN
  linperm

/--Euclid I.36, generalization of I.35 to parallelograms with a distance-/
theorem area_eq_of_far_Paragram (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e h g f L P N Q) (bc_fg : length b c = length f g) :
    area a d b + area d b c = area f g e + area g e h := by
  have ⟨aL, dL, dM, cM, cN, bN, bO, aO, paraLN, paraMO⟩ := pgram1
  have ⟨eL, hL, hP, gP, gN, fN, fQ, eQ, _, paraPQ⟩ := pgram2
  rcases line_of_pts e c with ⟨R, eR, cR⟩
  wlog bhR : SameSide b h R generalizing a b c d M O R; rcases line_of_pts b e with ⟨S, bS, eS⟩
  have quad_comm := Paragram_area_comm pgram1
  have key := this ⟨dL, aL, aO, bO, bN, cN, cM, dM, paraLN, Para_symm paraMO⟩ (by linperm) dL aL aO
    bO bN cN cM dM (Para_symm paraMO) S eS bS $ sameside_of_not_sameside_Para (ne_of_Para' cM bO
    paraMO) (ne_of_Para' hP eQ paraPQ) eL eR eS hL cR bS bN cN bhR paraLN; perm at *;
    rw[quad_comm,key]
  rcases line_of_pts b h with ⟨T, bT, hT⟩
  rcases B_diagonal_of_quad hL eL eR cR cN bN (sameside_of_Para_online hL eL paraLN)
    (sameside_of_Para_online' cN bN paraLN) (sameSide_symm bhR)
    with ⟨_, _, S, _, _, _, _, eS, bS, _, _, _, hcS⟩
  have eh_gf := len_eq_of_Parallelogram pgram2
  have ⟨hL, eL, eR, cR, cN, bN, bT, hT, _, paraRT⟩ :=
    pgram_of_Para_len_eq hL eL eR cR cN bN bT hT eS bS hcS paraLN (by linperm)
  have pgram3_pgram1 := area_eq_of_Paragram ⟨hL, eL, eR, cR, cN, bN, bT, hT, paraLN, paraRT⟩ pgram1
  have pgram3_pgram2 := area_eq_of_Paragram ⟨cN, bN, bT, hT, hL, eL, eR, cR, Para_symm paraLN,
    Para_symm paraRT⟩ ⟨fN, gN, gP, hP, hL, eL, eQ, fQ, Para_symm paraLN, paraPQ⟩
  linperm

/--Proof of the construction of the Parallelogram from the Triangle in I.37, used twice so worth
    having as its own lemma-/
lemma Paragram_of_tri_Para (bc : b ≠ c) (bM : OnLine b M) (cM : OnLine c M) (aN : OnLine a N)
    (ParaMN : Para M N) : ∃ d L O, Paragram d a c b N L M O := by
  rcases line_of_pts a c with ⟨L, aL, cL⟩
  rcases line_of_pts a b with ⟨P, aP, bP⟩
  rcases length_eq_of_sameside bP (online_3_of_Triangle aP bP
    (by perma[Triangle_of_ne_online bc bM cM $ offline_of_Para' aN ParaMN]))
    (offline_of_Para bM ParaMN) aP aN with ⟨d, dN, dcP, da_bc⟩
  rcases line_of_pts d b with ⟨O, dO, bO⟩
  exact ⟨d, L, O, pgram_of_Para_len_eq dN aN aL cL cM bM bO dO aP bP dcP (by perma) da_bc⟩

/--Euclid I.37, Triangles sharing two Parallels have the same area-/
theorem area_eq_of_tri (aL : OnLine a L) (dL : OnLine d L) (bM : OnLine b M) (cM : OnLine c M)
    (ParaLM : Para L M) : area a b c = area d b c := by
  by_cases bc : b = c; rw [bc]; linperm[degenerate_area c a, degenerate_area c d]
  rcases Paragram_of_tri_Para bc bM cM aL (by perma[ParaLM]) with ⟨e, N, O, pgram1⟩
  rcases Paragram_of_tri_Para bc bM cM dL (by perma[ParaLM]) with ⟨f, P, Q, pgram2⟩
  have pgram_eq := area_eq_of_Paragram pgram1 pgram2
  have half_pgram1 := area_eq_of_Parallelogram pgram1
  have half_pgram2 := area_eq_of_Parallelogram pgram2
  linperm

/--Euclid I.38, the analog of I.35 for Triangles-/
theorem area_eq_of_tri_far (aL : OnLine a L) (dL : OnLine d L) (bM : OnLine b M) (cM : OnLine c M)
    (eM : OnLine e M) (fM : OnLine f M) (bc_ef : length b c = length e f) (paraLM : Para L M) :
    area a b c = area d e f := by
  by_cases ef : e = f; rw[ef, eq_of_length_zero (by rwa[length_zero_of_eq ef] at bc_ef :
    length b c = 0)]; linperm[degenerate_area c a, degenerate_area f d]
  rcases Paragram_of_tri_Para (ne_of_ne_len ef bc_ef.symm) bM cM aL (Para_symm paraLM)
    with ⟨g, N, O, pgram1⟩
  rcases Paragram_of_tri_Para ef eM fM dL (Para_symm paraLM) with ⟨h, P, Q, pgram2⟩
  have pgram_eq := area_eq_of_far_Paragram pgram1 pgram2 bc_ef
  have half_pgram1 := area_eq_of_Parallelogram pgram1
  have half_pgram2 := area_eq_of_Parallelogram pgram2
  linperm[Paragram_area_comm pgram2]

/--Euclid I.40, equal area Triangles on the same side must be on the same parallels-/
theorem para_of_tri_sameside_area_far (ad : a ≠ d) (tri_abc : Triangle a b c)
    (tri_def : Triangle d e f) (bL : OnLine b L) (cL : OnLine c L) (eL : OnLine e L)
    (fL : OnLine f L) (aM : OnLine a M) (dM : OnLine d M) (adL : SameSide a d L)
    (bc_ef : length b c = length e f) (eq_tri : area a b c = area d e f) : Para L M := by
  by_contra paraLM
  rcases line_of_pts e d with ⟨O, eO, dO⟩
  rcases Para_of_offline $ online_1_of_Triangle bL cL tri_abc with ⟨N, aN, paraLN⟩
  rcases lines_inter_of_para (ne_line_of_online dO $ online_1_of_Triangle eL
    fL tri_def).symm eO eL paraLN with ⟨g, gO, gN⟩
  have abc_gef := area_eq_of_tri_far aN gN bL cL eL fL bc_ef $ Para_symm paraLN
  by_cases Begd : B e g d; exact tri_sum_contra eO dO gO (online_3_of_Triangle dO eO tri_def)
    (by linperm) Begd
  by_cases Bedg : B e d g; exact tri_sum_contra eO gO dO (online_3_of_Triangle dO eO tri_def)
    (by linperm) Bedg
  have := B_or_B_of_sameside (ne_of_Para_Para ad aN aM dM gN paraLN paraLM) eL ⟨O, eO, dO, gO⟩
    (sameSide_trans adL $ sameside_of_Para_online' aN gN paraLN); tauto

/--Euclid I.39, equal area Triangles on the same side must be on the same parallels-/
theorem para_of_tri_sameside_area (ad : a ≠ d) (tri_abc : Triangle a b c) (tri_dbc : Triangle d b c)
    (bL : OnLine b L) (cL : OnLine c L) (aM : OnLine a M) (dM : OnLine d M) (adL : SameSide a d L)
    (eq_tri : area a b c = area b c d) : Para L M :=
  para_of_tri_sameside_area_far ad tri_abc tri_dbc bL cL bL cL aM dM adL rfl (by linperm)

/--Euclid I.41, if a Parallelogram shares the same Parallels as a
  Triangle and the same base, then the Parallelogram has twice the area of the Triangle-/
theorem twice_pgram_of_tri  (eL : OnLine e L) (pgram : Paragram a b c d L M N O) :
    area a b d + area b c d = 2 * area c d e := by
  have ⟨_, _, _, _, cN, dN, _, _, ParaLM, _⟩ := pgram
  have pgram_eq := area_eq_of_Parallelogram pgram
  have tri_eq := area_eq_of_tri pgram.2.1 eL cN dN ParaLM
  linperm

/--Euclid I.42, to construct a parallelogram with the area of a given Triangle and with a given
  angle-/
theorem pgram_of_angle_tri (hi : h ≠ i) (tri_abc : Triangle a b c) (tri_def : Triangle d e f)
    (hL : OnLine h L) (iL : OnLine i L) (nL : ¬OnLine n L) : ∃ j l m M N O,
    B h i j ∧ Paragram m l i j N M L O ∧ area j i l + area l m j = area a b c ∧ SameSide n l L ∧
    angle l i j = angle d e f := by
  rcases bisect_segment (ne_23_of_tri tri_abc) with ⟨g, Bbgc, bg_cg⟩
  rcases length_eq_B_of_ne_four hi (ne_12_of_B Bbgc) with ⟨j, Bhij, bg_ij⟩
  rcases triangle_copy (tri321 $ tri_of_B_tri (B_symm Bbgc) (tri132_of_tri123 tri_abc)) iL
    (onLine_3_of_B Bhij hL iL) nL bg_ij.symm with ⟨k, ik_ba, jk_ga, knL⟩
  rcases Para_of_offline (not_onLine_of_sameSide knL) with ⟨N, kN, paraLN⟩
  rcases angle_copy (ne_23_of_B Bhij) iL (onLine_3_of_B Bhij hL iL) (not_onLine_of_sameSide knL)
    (tri231_of_tri123 tri_def) with ⟨o, oij_def, okL⟩
  rcases line_of_pts i o with ⟨M', iM', oM'⟩
  rcases lines_inter_of_para (ne_line_of_online oM' (not_onLine_of_sameSide okL)).symm iM' iL paraLN
    with ⟨l, lM', lN⟩
  rcases Paragram_of_tri_Para (ne_32_of_B Bhij) (onLine_3_of_B Bhij hL iL) iL lN paraLN
    with ⟨m, M, O, pgram⟩; have ⟨_, lN, lM, iM, iL, _⟩ := pgram
  rcases line_of_pts b c with ⟨Q, bQ, cQ⟩
  rcases Para_of_offline (online_1_of_Triangle bQ cQ tri_abc) with ⟨R, aR, paraQR⟩
  have abg_acg := area_eq_of_tri_far aR aR bQ (onLine_2_of_B Bbgc bQ cQ) cQ
    (onLine_2_of_B Bbgc bQ cQ) bg_cg (Para_symm paraQR)
  have para_split := twice_pgram_of_tri kN pgram
  have bga_ijk := area_eq_of_SSS bg_ij ik_ba.symm jk_ga.symm
  have abc_split := area_add_of_B_offline Bbgc bQ cQ (online_1_of_Triangle bQ cQ tri_abc)
  exact ⟨j, l, m, M, N, O, Bhij, pgram, by linperm, sameSide_trans knL (sameside_of_Para_online' kN
    lN paraLN), by linperm[angle_extension_of_sameside (ne_32_of_B Bhij) iL ⟨M, iM, (by rwa
      [line_unique_of_pts (ne_of_Para iL lN paraLN) iM lM iM' lM'] : OnLine o M), lM⟩
                    (sameSide_symm $ sameSide_trans (sameside_of_Para_online' kN lN paraLN) okL)]⟩

/--Euclid I.43, complementary parallelograms accross the diameter of a parallelogram are equal-/
theorem pgram_complement_eq (Bakc : B a k c) (hM : OnLine h M) (hQ : OnLine h Q) (fN : OnLine f N)
    (fP : OnLine f P) (pgram1 : Paragram d a b c O L M N) (pgram2 : Paragram g a e k O L P Q) :
    area k d g + area k d f = area k b e + area k b h := by
  have ⟨dO, _, _, bL, bM, cM, cN, dN, paraOM, paraLN⟩ := pgram1
  have ⟨gO, aO, aL, eL, eP, kP, kQ, gQ, paraOP, paraLQ⟩ := pgram2
  have paraPM := Para_trans (ne_line_of_online cM (DiffSide_of_B_offline' Bakc kP
    (offline_of_Para aO paraOP)).2.1) paraOP paraOM
  have paraQN := Para_trans (ne_line_of_online kQ $ not_onLine_of_sameSide $
    sameside_of_B_not_online_3 (B_symm Bakc) cN (offline_of_Para aL paraLN)).symm paraLQ paraLN
  have dac_abc := area_eq_of_Parallelogram pgram1
  have gak_aek := area_eq_of_Parallelogram pgram2
  have fkc_khc := area_eq_of_Parallelogram ⟨fP, kP, kQ, hQ, hM, cM, cN, fN, paraPM, paraQN⟩
  have kab_split := area_add_of_B_offline (B_of_B_Para Bakc ⟨L, aL, eL, bL⟩ bM cM eP kP
    (offline_of_Para aO paraOP) (Para_symm paraPM)) aL bL (offline_of_Para' kQ paraLQ)
  have kcb_split := area_add_of_B_offline (B_of_B_Para (B_symm Bakc) ⟨M, cM, hM, bM⟩ bL aL hQ kQ
    (offline_of_Para' cN paraQN) paraLQ) cM bM (offline_of_Para kP paraPM)
  have kad_split := area_add_of_B_offline (B_of_B_Para Bakc ⟨O, aO, gO, dO⟩ dN cN gQ kQ
    (offline_of_Para aL paraLQ) (Para_symm paraQN)) aO dO (offline_of_Para' kP paraOP)
  have kcd_split := area_add_of_B_offline (B_of_B_Para (B_symm Bakc) ⟨N, cN, fN, dN⟩ dO aO fP kP
    (offline_of_Para' cM paraPM) paraOP) cN dN (offline_of_Para kQ paraQN)
  have bac_split := area_add_of_B Bakc $ tri132_of_tri123 $ Triangle_of_ne_online
    (ne_of_Para bL cN paraLN) bM cM (offline_of_Para aO paraOM)
  have dca_split := area_add_of_B (B_symm Bakc) $ tri132_of_tri123 $ Triangle_of_ne_online
    (ne_of_Para dN aL $ Para_symm paraLN) dO aO (offline_of_Para' cM paraOM)
  linperm

theorem lines_inter_of_pgram (Babe : B a b e) (Bfgh : B f g h) (pgram1 : Paragram f g b e Q P L R)
    (pgram2 : Paragram a b g h L P Q M) (bS : OnLine b S) (hS : OnLine h S) (paraMR : Para M R) :
    ∃ k, OnLine k S ∧ OnLine k R ∧ B h b k ∧ ¬OnLine k Q := by
  have ⟨fQ, _, _, _, _, _, eR, fR, paraQL, paraPR⟩ := pgram1
  have ⟨aL, bL, bP, gP, _, hQ, hM, _, _, paraPM⟩ := pgram2
  rcases lines_inter_of_para (ne_line_of_online bS (offline_of_Para bP paraPM)).symm hS hM paraMR
    with ⟨k, kS, kR⟩
  exact ⟨k, kS, kR, B_symm $ B_of_B_Para_Para (B_symm Bfgh) hM hS gP fR bS bP kS kR (Para_symm
    paraPR) (Para_symm paraMR) paraPM, online_2_of_Triangle fQ hQ $ Triangle_of_ne_online
    (ne_13_of_B $ B_of_B_B_Para Babe Bfgh aL bL hM hS hQ bS bP gP eR fR fQ kS kR paraPR paraQL
    paraPM paraMR) fR kR (offline_of_Para hM paraMR)⟩

theorem lines_inter_of_pgram' (Babe : B a b e) (Bfgh : B f g h) (pgram1 : Paragram f g b e Q P L R)
    (pgram2 : Paragram a b g h L P Q M) (bS : OnLine b S) (hS : OnLine h S) (kS : OnLine k S)
    (kR : OnLine k R) (kN : OnLine k N) (paraMR : Para M R) (paraLN : Para L N) (paraQN : Para Q N):
    ∃ m, OnLine m P ∧ OnLine m N ∧ B g b m := by
  have ⟨fQ, gQ, _, _, _, eL, eR, fR, paraQL, paraPR⟩ := pgram1
  have ⟨aL, bL, bP, gP, _, hQ, hM, _, _, paraPM⟩ := pgram2
  rcases lines_inter_of_para (ne_line_of_online hQ (offline_of_Para' hM paraPM)) gP gQ paraQN
    with ⟨m, mP, mN⟩
  exact ⟨m, mP, mN, B_of_sq (B_of_B_B_Para Babe Bfgh aL bL hM hS hQ bS bP gP eR fR
    fQ kS kR paraPR paraQL paraPM paraMR) eL bL bP paraQL (Para_symm paraLN) ⟨fR, kR, kN, mN, mP,
    gP, gQ, fQ, Para_symm paraPR, Para_symm paraQN⟩⟩

/--Euclid I.44, make a parallelogram on a segment with a prescribed area and angle-/
theorem pgram_seg_of_tri_ang (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (tri_nop : Triangle n o p) (tri_qrs : Triangle q j s) (iL : ¬OnLine i L) :
    ∃ l m M N O, Paragram a b m l L M N O ∧ area l b a + area l b m = area n o p ∧
    angle a b m = angle q j s ∧ DiffSide m i L := by
  rcases pgram_of_angle_tri ab tri_nop tri_qrs aL bL iL with ⟨e, g, f, P, Q, R, Babe, pgram1,
    pgram_tri, igL, gbe_qjs⟩; have ⟨fQ, gQ, gP, bP, bL, eL, eR, fR, paraQL, paraPR⟩ := pgram1
  rcases length_eq_B_of_ne_four (ne_of_Para gP fR paraPR).symm ab with ⟨h, Bfgh, ab_gh⟩
  rcases line_of_pts h a with ⟨M, hM, aM⟩
  rcases line_of_pts h b with ⟨S, hS, bS⟩
  have pgram2 := pgram_of_Para_len_eq aL bL bP gP gQ (onLine_3_of_B Bfgh fQ gQ) hM aM bS hS
    (DiffSide_of_B_B_Para Babe Bfgh aL bL hS bS bP gP eR fR fQ gQ paraPR paraQL)
    (Para_symm paraQL) (by linperm); have ⟨aL, bL, bP, gP, gQ, hQ, hM, aM, _, paraPM⟩ := pgram2
  have paraMR := Para_trans (ne_line_of_online aM $ not_onLine_of_sameSide $ sameSide_symm $
    sameSide_of_B_not_onLine_2 (B_symm Babe) eR (offline_of_Para bP paraPR)).symm paraPM paraPR
  rcases lines_inter_of_pgram Babe Bfgh pgram1 pgram2 bS hS paraMR with ⟨k, kS, kR, Bhbk, kQ⟩
  rcases Para_of_offline kQ with ⟨N, kN, paraQN⟩
  rcases lines_inter_of_para (ne_line_of_online gQ (offline_of_Para gP paraPM)) hM hQ paraQN
    with ⟨l, lM, lN⟩
  have paraLN := Para_trans (ne_line_of_online kN (DiffSide_of_B_Para_Para Bfgh bL hQ hM hS gP fR
    bS bP kS kR paraPR paraMR paraPM paraQL).2.1) paraQL paraQN
  rcases lines_inter_of_pgram' Babe Bfgh pgram1 pgram2 bS hS kS kR kN paraMR paraLN paraQN
    with ⟨m, mP, mN, Bgbm⟩
  have pgram_pgram := pgram_complement_eq Bhbk eR eL mN mP ⟨lM, hM, hQ, fQ, fR, kR,
     kN, lN, paraMR, paraQN⟩ ⟨aM, hM, hQ, gQ, gP, bP, bL, aL, Para_symm paraPM, paraQL⟩
  have gbe_mba := vertical_angle Bgbm (B_symm Babe) gP bP (offline_of_Para' eR paraPR)
  exact ⟨l, m, P, N, M, ⟨aL, bL, bP, mP, mN, lN, lM, aM, paraLN, paraPM⟩, by
    linperm[Paragram_area_comm pgram1], by linperm, DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameSide_symm igL) $ DiffSide_of_B_offline' Bgbm bL (offline_of_Para gQ paraQL)⟩

/--Euclid I.45, from a quadrilateral contructing a parallelogram with its area-/
theorem pgram_of_quad (nf : n ≠ f) (tri_abd : Triangle a b d) (tri_cbd : Triangle c b d)
    (tri_eij : Triangle e i j) (nL : OnLine n L) (fL : OnLine f L) (pL : ¬OnLine p L) :
    ∃ k m l M N O, B n f k ∧ Paragram f k m l L M N O ∧ area f m k + area f m l = area a b d +
    area c b d ∧ angle k f l = angle e i j ∧ SameSide l p L := by
  rcases pgram_of_angle_tri nf tri_abd tri_eij nL fL pL with ⟨k, g, h, O, P, M, Bnfk, pgram1,
    abd_pgram, pgL, gfk_eij⟩; have ⟨hP, gP, gO, fO, fL, kL, kM, hM, paraPL, paraOM⟩ := pgram1
  rcases pgram_seg_of_tri_ang (ne_of_Para' gO hM paraOM) hP gP tri_cbd tri_eij
    (offline_of_Para' fL paraPL) with ⟨m, l, O', N, M', pgram2, cbd_pgram, hgm_eij, lfP⟩
  have ⟨hP, gP, gO', lO', lN, mN, mM', hM', paraPN, paraOM'⟩ := pgram2
  have kfgh_right := interior_rightangles_of_Para kL fL fO gO gP hP
    (sameside_of_Para_online' kM hM paraOM) (Para_symm paraPL)
  have Blgf := flat_of_two_right_angle (ne_of_Para gO hM paraOM) gP hP lfP (by linperm)
  have mghl_right := interior_rightangles_of_Para mM' hM' hP gP gO' lO'
    (sameside_of_Para_online' mN lN paraPN) (Para_symm paraOM')
  have khg_hgl := alternate_eq_of_Para kM hM hP gP gO (onLine_3_of_B (B_symm Blgf) fO gO)
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' fL kL paraPL) (DiffSide_symm lfP))
    (Para_symm paraOM)
  have Bkhm := flat_of_two_right_angle (ne_of_Para gO hM paraOM).symm hP gP
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' fL kL paraPL) (DiffSide_symm
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' lN mN paraPN) lfP))) (by linperm)
  have paraLN := Para_trans (ne_line_of_online lN $ online_of_B_online'' (B_symm Blgf) fL
    (offline_of_Para gP paraPL)) paraPL paraPN
  have pgram_split := quad_add_of_quad (B_symm Blgf) Bkhm fO gO lN mN kM hM
    (sameside_of_Para_online fO (onLine_3_of_B (B_symm Blgf) fO gO) paraOM)
    (sameside_of_Para_online' (onLine_3_of_B Bkhm kM hM) hM paraOM)
    (sameside_of_Para_online fL kL paraLN)
  exact ⟨k, m, l, M, N, O, Bnfk, ⟨fL, kL, kM, onLine_3_of_B Bkhm kM hM, mN, lN, onLine_3_of_B
    (B_symm Blgf) fO gO, fO, paraLN, Para_symm paraOM⟩, by
    linperm[Paragram_area_comm pgram1, Paragram_area_comm pgram2], by
    linperm[angle_extension_of_B (ne_of_Para fO kM $ Para_symm paraOM) (B_symm Blgf)],
      sameSide_trans (sameside_of_B_online_3 (B_symm Blgf) fL (online_of_B_online'' (B_symm Blgf)
      fL (offline_of_Para gP paraPL))) (sameSide_symm pgL)⟩

/--Euclid I.46, constructing a Square out of a segment-/
theorem Square_of_len (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (fL : ¬OnLine f L) :
    ∃ c d M N O, Paragram a c d b N M O L ∧ Square a c d b ∧ DiffSide c f L := by
  rcases perpendicular_of_online' ab.symm bL aL fL with ⟨e, efL, bae⟩
  rcases length_eq_B_of_ne (ne_of_sameside aL efL) ab with ⟨c, Beac, ab_ac⟩
  rcases Para_of_offline $ online_of_B_online' (B_symm Beac) aL $ not_onLine_of_sameSide efL
    with ⟨M, cM, ParaLM⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  rcases length_eq_of_sameside' aN (offline_of_ne_online_offline ab aL bL aN cN $
    offline_of_Para' cM ParaLM) (offline_of_Para aL ParaLM) cN cM with ⟨d, dM, dbN, dc_ab⟩
  rcases line_of_pts b d with ⟨O, bO, dO⟩
  rcases line_of_pts b c with ⟨P, bP, cP⟩
  have abc_bcd := alternate_eq_of_Para aL bL bP cP cM dM
    (by perma[DiffSide_of_sameside_sameside cM cP cN dM bP aN (sameside_of_Para_online aL bL
    ParaLM) dbN]) ParaLM
  have ⟨ac_db, bac_cdb, bca_cbd⟩ := sas (by linperm : length b a = length c d)
    (length_symm b c) $ by perma[abc_bcd]
  have bac := two_right_of_flat_angle Beac (onLine_3_of_B (B_symm Beac) cN aN) aN $
    offline_of_ne_online_offline ab aL bL aN cN $ offline_of_Para' cM ParaLM
  have acd := correspond_of_Para Beac (onLine_3_of_B (B_symm Beac) cN aN) aN aL bL cM dM
    (by perma[dbN]) ParaLM
  have bdc := interior_rightangles_of_Para aL bL bO dO dM cM
    (sameside_of_sameside_DiffSide bL bP bO aL cP dO (sameside_of_Para_online' cM dM ParaLM) $
    by perma[DiffSide_of_sameside_sameside cM cP cN dM bP aN
        (sameside_of_Para_online aL bL ParaLM) dbN]) ParaLM
  refine ⟨c, d, M, N, O, ⟨aN, cN, cM, dM, dO, bO, bL, aL, Para_of_ang_eq (ne_of_Para' bL cM ParaLM)
    aN cN cP bP bO dO
    (by perma[DiffSide_of_sameside_sameside cM cP cN dM bP aN (sameside_of_Para_online
    aL bL ParaLM) dbN]) bca_cbd, Para_symm ParaLM⟩, by splitAll; repeat linperm,
    DiffSide_of_B_sameside Beac aL efL⟩

lemma right_of_online_right (bd : b ≠ d) (tri_abc : Triangle a b c) (bL : OnLine b L) (cL :
    OnLine c L) (dL : OnLine d L) (abd : angle a b d = rightangle) : angle a b c = rightangle := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩
  by_cases cdM : SameSide c d M;
    linperm[angle_extension_of_sameside (ne_12_of_tri tri_abc) bM ⟨L, bL, cL, dL⟩ cdM]
  linperm[two_right_of_flat_angle (B_of_col_DiffSide ⟨L, cL, bL, dL⟩ bM ⟨online_3_of_Triangle aM
    bM tri_abc, offline_of_online_offline bd aM bM bL dL $ online_1_of_Triangle bL cL tri_abc,
    cdM⟩) cL bL (online_1_of_Triangle bL cL tri_abc)]

lemma ne_of_perp_ineq (Bxdy : B x d y) (tri_abc : Triangle a b c) (bL : OnLine b L)
    (cL : OnLine c L) (xL : OnLine x L) (cab_le_ra : rightangle ≤ angle c a b)
    (ady : angle a d y = rightangle) : b ≠ d := by
  intro bd; rw[←bd] at Bxdy ady
  linperm[right_of_online_right (ne_23_of_B Bxdy) tri_abc bL cL (onLine_3_of_B Bxdy xL bL) ady,
    sum_two_right_of_tri tri_abc, (zero_lt_angle_of_tri (by perma[tri_abc]) : 0 < angle b c a)]

lemma not_B_of_right_le_right (tri_abc : Triangle a b c) (col_bcd : Colinear b c d)
    (adb : angle a d b = rightangle) (cab_le_ra : rightangle ≤ angle c a b) : ¬B d b c := by
  intro Bdbc; rcases col_bcd with ⟨L, bL, cL, dL⟩
  have split := angle_add_of_B Bdbc dL bL (online_1_of_Triangle bL cL tri_abc)
  have sum_three := sum_two_right_of_tri (Triangle_of_ne_online (ne_13_of_B Bdbc) dL cL
    (online_1_of_Triangle bL cL tri_abc))
  linperm[angle_nonneg b a d, (zero_lt_angle_of_tri (by
    perma[Triangle_of_ne_online (ne_13_of_B Bdbc) dL cL (online_1_of_Triangle bL cL tri_abc)]) :
    0 < angle d c a), angle_extension_of_B (ne_of_online dL $ online_1_of_Triangle bL cL
    tri_abc) Bdbc]

lemma inter_sq_of_perp (Bbxc : B b x c) (aX : OnLine a X) (xX : OnLine x X)
    (pgram1 : Paragram b c d e L O P Q) (adL : DiffSide a d L) : ∃ l, OnLine l X ∧ OnLine l P := by
  have ⟨bL, cL, _, _, _, _, _, _, ParaLP, _⟩ := pgram1
  by_cases ParaXP : Para X P; have := onLine_2_of_B Bbxc bL cL; have := Para_trans
    (ne_line_of_online aX adL.1) (Para_symm ParaLP) (Para_symm ParaXP) x; tauto
  unfold Para at ParaXP; push_neg at ParaXP; exact ParaXP

/--A big enough angle has its perpendicular on a Triangle side-/
lemma right_B_of_le_right (tri_abc : Triangle a b c) (cab_le_ra : rightangle ≤ angle c a b) :
    ∃ d, angle a d b = rightangle ∧ angle a d c = rightangle ∧ B b d c := by
  rcases line_of_pts b c with ⟨L, bL, cL⟩
  rcases perpendicular_of_not_online (online_1_of_Triangle bL cL tri_abc) with
    ⟨x, y, d, Bxdy, xL, _, dL, adx, ady⟩
  have adb := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[Triangle_of_ne_online (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady) bL dL
          (online_1_of_Triangle bL cL tri_abc)] : Triangle a d b) dL bL xL adx
  have adc := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[Triangle_of_ne_online (ne_of_perp_ineq Bxdy (by perma[tri_abc] : Triangle a c b)
    cL bL xL (by perma[cab_le_ra]) ady) cL dL (online_1_of_Triangle bL cL tri_abc)] : Triangle
     a d c) dL cL xL adx
  have := B_of_three_col_ne (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady).symm
    (ne_of_perp_ineq Bxdy (by perma[tri_abc] : Triangle a c b) cL bL xL (by perma[cab_le_ra])
    ady).symm (ne_23_of_tri tri_abc) ⟨L, dL, bL, cL⟩
  have := not_B_of_right_le_right tri_abc ⟨L, bL, cL, dL⟩ adb cab_le_ra
  have := not_B_of_right_le_right (by perma[tri_abc] : Triangle a c b) ⟨L, cL, bL, dL⟩ adc
    (by perma[cab_le_ra])
  tauto

/--Euclid I.47, the construction of the Squares for the Pythagorean theorem-/
theorem pythagoras_construct (tri_abc : Triangle a b c) : ∃ d e f g h k L M N O P Q R S T U V W,
    Square c d e b ∧ Square a g f b ∧ Square a h k c ∧ Paragram b c d e L O P Q ∧
    Paragram g a b f T N R S ∧ Paragram h a c k U M W V ∧ DiffSide a d L ∧
    DiffSide b h M ∧ DiffSide c g N := by
  rcases line_of_pts b c with ⟨L, bL, cL⟩
  rcases line_of_pts a c with ⟨M, aM, cM⟩
  rcases line_of_pts a b with ⟨N, aN, bN⟩
  rcases Square_of_len (ne_32_of_tri tri_abc) cL bL (online_1_of_Triangle bL cL tri_abc) with
    ⟨d, e, P, O, Q, ⟨cO, dO, dP, eP, eQ, bQ, bL, cL, ParaOQ, ParaPL⟩, sq1, daL⟩
  rcases Square_of_len (ne_12_of_tri tri_abc) aN bN (online_3_of_Triangle aN bN tri_abc) with
    ⟨g, f, S, T, R, ⟨aT, gT, gS, fS, fR, bR, bN, aN, ParaTR, ParaSN⟩, sq2, gcN⟩
  rcases Square_of_len (ne_13_of_tri tri_abc) aM cM (online_2_of_Triangle aM cM tri_abc) with
    ⟨h, k, V, U, W, ⟨aU, hU, hV, kV, kW, cW, cM, aM, ParaUW, ParaVM⟩, sq3, hbM⟩
  exact ⟨d, e, f, g, h, k, L, M, N, O, P, Q, R, S, T, U, V, W, sq1, sq2, sq3, ⟨bL, cL, cO, dO, dP,
    eP, eQ, bQ, Para_symm ParaPL, ParaOQ⟩, ⟨gT, aT, aN, bN, bR, fR, fS, gS, ParaTR, Para_symm
    ParaSN⟩, ⟨hU, aU, aM, cM, cW, kW, kV, hV, ParaUW, Para_symm ParaVM⟩, by perma[daL], by perma
    [hbM], by perma[gcN]⟩

/--Euclid I.47, the Pythagorean theorem-/
theorem pythagoras (tri_abc : Triangle a b c) (ang : angle c a b = rightangle)
    (sq1 : Square c d e b) (sq2 : Square a g f b) (sq3 : Square a h k c)
    (pgram1 : Paragram b c d e L O P Q) (pgram2 : Paragram g a b f T N R S)
    (pgram3 : Paragram h a c k U M W V) (adL : DiffSide a d L) (bhM : DiffSide b h M)
    (cgN : DiffSide c g N) :
    area b c d + area b d e = area a b f + area a g f + area a h k + area a c k := by
  unfold Square at sq1 sq2 sq3
  have ⟨bL, cL, cO, dO, dP, eP, eQ, bQ, ParaLP, ParaOQ⟩ := pgram1
  have ⟨gT, aT, aN, bN, bR, fR, fS, gS, ParaTR, ParaNS⟩ := pgram2
  have ⟨hU, aU, aM, cM, cW, kW, kV, hV, ParaUW, ParaMV⟩ := pgram3
  have Bcag := flat_of_two_right_angle (ne_12_of_tri tri_abc) aN bN cgN (by linperm)
  have Bbah := flat_of_two_right_angle (ne_13_of_tri tri_abc) aM cM bhM (by linperm)
  rcases right_B_of_le_right tri_abc (by linarith) with ⟨x, axb, axc, Bbxc⟩
  rcases line_of_pts a x with ⟨X, aX, xX⟩
  rcases inter_sq_of_perp Bbxc aX xX pgram1 adL with ⟨l, lX, lP⟩
  have ParaQX := Para_of_ang_eq (ne_12_of_B Bbxc) eQ bQ bL (onLine_2_of_B Bbxc bL cL) xX aX
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' dP eP ParaLP) (DiffSide_symm adL))
    (by linperm[angle_extension_of_B (ne_of_Para bL eP ParaLP) Bbxc])
  have ParaOX := Para_of_ang_eq (ne_32_of_B Bbxc) dO cO cL (onLine_2_of_B Bbxc bL cL) xX aX
    (DiffSide_symm adL) (by linperm[angle_extension_of_B (ne_of_Para cL dP ParaLP) $ B_symm Bbxc])
  have Beld := B_of_sq Bbxc xX lX lP ParaQX ParaOX pgram1
  have fbc_split := angle_add_of_sameside bR fR bL cL (sameSide_symm $ sameside_of_Para_online aT
    (onLine_3_of_B (B_symm Bcag) gT aT) ParaTR) $ sameside_of_sameside_DiffSide bR bN bL fR aN cL
    (sameside_of_Para_online aT (onLine_3_of_B (B_symm Bcag) gT aT) ParaTR) $
    DiffSide_of_sameside_DiffSide (sameSide_symm $ sameside_of_Para_online' fS gS ParaNS) $
    DiffSide_symm cgN
  have abe_split := angle_add_of_sameside bN aN bQ eQ (sameside_of_sameside_DiffSide bQ bL bN eQ cL
    aN (sameSide_symm $ sameside_of_pyth Beld aX lX pgram1 ParaQX) $ DiffSide_of_sameside_DiffSide
    (sameside_of_Para_online' dP eP ParaLP) $ DiffSide_symm adL) $ sameside_of_pyth Beld aX lX
    pgram1 ParaQX
  have bck_split := angle_add_of_sameside cL bL cW kW (sameside_of_sameside_DiffSide cW cM cL kW aM
    bL (sameside_of_Para_online aU (onLine_3_of_B (B_symm Bbah) hU aU) ParaUW) $
    DiffSide_of_sameside_DiffSide (sameside_of_Para_online' hV kV ParaMV) $ DiffSide_symm bhM)
    (sameSide_symm $ sameside_of_Para_online aU (onLine_3_of_B (B_symm Bbah) hU aU) ParaUW)
  have acd_split := angle_add_of_sameside cM aM cO dO (sameside_of_sameside_DiffSide cO cL cM dO bL
    aM (sameSide_symm $ sameside_of_pyth (B_symm Beld) aX lX ⟨cL, bL, bQ, eQ, eP, dP, dO, cO,
    ParaLP, Para_symm ParaOQ⟩ ParaOX) $ DiffSide_symm adL) $ sameside_of_pyth (B_symm Beld) aX lX
    ⟨cL, bL, bQ, eQ, eP, dP, dO, cO, ParaLP, Para_symm ParaOQ⟩ ParaOX
  have ⟨ae_fc, _, _⟩ := sas (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) $ by linperm
  have tri1_eq := area_eq_of_SSS (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) ae_fc
  have ⟨ad_kb, _, _⟩ := sas (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) $ by linperm
  have tri2_eq := area_eq_of_SSS (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) ad_kb
  have tri_req1 := twice_pgram_of_tri aX
    ⟨xX, lX, lP, eP, eQ, bQ, bL, onLine_2_of_B Bbxc bL cL, Para_symm ParaQX, Para_symm ParaLP⟩
  have tri_req2 := twice_pgram_of_tri (onLine_3_of_B (B_symm Bcag) gT aT) pgram2
  have tri_req3 := twice_pgram_of_tri aX
    ⟨lX, xX, onLine_2_of_B Bbxc bL cL, cL, cO, dO, dP, lP, Para_symm ParaOX, ParaLP⟩
  have tri_req4 := twice_pgram_of_tri (onLine_3_of_B (B_symm Bbah) hU aU) pgram3
  have sq_split := quad_add_of_quad Bbxc Beld bL (onLine_2_of_B Bbxc bL cL) cO dO eP lP
    (sameside_of_Para_online bL cL ParaLP) (sameside_of_Para_online' dP lP ParaLP)
    $ sameside_of_Para_online' bQ eQ ParaOQ
  have right_half := quad_area_comm (onLine_2_of_B Bbxc bL cL) cL cO dO dP lP
    (sameside_of_Para_online (onLine_2_of_B Bbxc bL cL) cL ParaLP)
    (sameside_of_Para_online' dP lP ParaLP) $ sameside_of_Para_online' xX lX ParaOX
  linperm
