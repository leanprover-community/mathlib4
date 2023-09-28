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

variable [i : IncidenceGeometry] {a a1 a2 b b1 b2 c d e f g h j k l x y :
  IncidenceGeometry.Point} {L M N O P Q R S T U W V X : IncidenceGeometry.Line}
  {α β : IncidenceGeometry.Circle} {r : ℝ}
open IncidenceGeometry

-------------------------------------------------- new  API ----------------------------------------
theorem online_of_line (L : Line) : ∃ a, online a L := by
  rcases more_pts ∅ Set.finite_empty with ⟨a, -⟩
  exact Classical.by_cases (fun aL => by use a)
    (fun aL => by rcases diffside_of_not_online aL with ⟨b, -, abL⟩; rcases line_of_pts a b with
      ⟨M, aM, bM⟩; rcases pt_of_lines_inter (lines_inter_of_not_sameside aM bM abL) with
      ⟨c, cL, -⟩; exact ⟨c, cL⟩)

theorem online_ne_of_line (L : Line) : ∃ a b, a ≠ b ∧ online a L ∧ online b L := by
  rcases online_of_line L with ⟨a, aL⟩; rcases more_pts {a} (Set.finite_singleton a) with ⟨b, hb⟩;
  rcases circle_of_ne $ ne_of_mem_of_not_mem (Set.mem_singleton a) hb with ⟨α, acen, -⟩;
  rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online aL
  (inside_circle_of_center acen)) with ⟨c, d, cd, cL, dL, -, -⟩; exact ⟨c, d, cd, cL, dL⟩

theorem online_ne_of_point_line (a : Point) (L : Line) : ∃ b, a ≠ b ∧ online b L := by
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  by_cases c = a; use b; rw[h] at bc; exact ⟨bc.symm, bL⟩
  use c; exact ⟨Ne.symm h, cL⟩

lemma len_pos_of_nq (ab : a ≠ b) : 0 < length a b :=
  (Ne.symm (not_imp_not.mpr length_eq_zero_iff.mp ab)).le_iff_lt.mp (length_nonneg a b)

theorem ne_of_ne_len (ab : a ≠ b) (ab_cd : length a b = length c d) : c ≠ d :=
  fun ac => by linarith[length_eq_zero_iff.mpr ac, len_pos_of_nq ab]

theorem ne_of_ne_len' (cd : c ≠ d) (ab_cd : length a b = length c d) : a ≠ b :=
  ne_of_ne_len cd (ab_cd.symm)

theorem length_sum_perm_of_B (Babc : B a b c) : 0 < length a b ∧ 0 < length b a ∧ 0 < length b c
    ∧ 0 < length c b ∧ 0 < length a c ∧ 0 < length c a ∧ length a b + length b c = length a c ∧
    length b a + length b c = length a c ∧ length b a + length c b = length a c ∧
    length b a + length b c = length c a ∧ length b a + length c b = length c a ∧
    length a b + length c b = length a c ∧ length a b + length b c = length c a ∧
    length a b + length c b = length c a := by
  perm; splitAll; repeat exact len_pos_of_nq $ ne_12_of_B Babc
  repeat exact len_pos_of_nq $ ne_23_of_B Babc; repeat exact len_pos_of_nq $ ne_13_of_B Babc
  repeat exact length_sum_of_B Babc

theorem length_perm_of_3pts (a b c : Point) : length a b = length b a ∧ length a c = length c a ∧
  length b c = length c b := by perm; tauto

theorem not_online_of_line (L : Line) : ∃ a, ¬online a L := by
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  rcases circle_of_ne bc with ⟨α, bα, cα⟩
  rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩
  rcases pts_of_circles_inter (circles_inter_of_inside_on_circle cα bβ (inside_circle_of_center
     bα) (inside_circle_of_center cβ)) with ⟨a, -, -, aα, aβ, -, -⟩
  have bc_ba := (on_circle_iff_length_eq bα cα).mpr aα
  have cb_ca := (on_circle_iff_length_eq cβ bβ).mpr aβ
  refine ⟨a, fun aL => (by push_neg; splitAll; all_goals exact (fun Bet =>
    by linarith[length_sum_perm_of_B Bet]) : ¬ (B b c a ∨ B c b a ∨ B b a c)) $
    B_of_three_online_ne bc (ne_of_ne_len bc bc_ba) (ne_of_ne_len bc.symm cb_ca) bL cL aL⟩

theorem online_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ c L, online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ ¬online c L := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases not_online_of_line L with ⟨d, dL⟩;
  rcases pt_sameside_of_circles_inter aL bL dL aα bβ αβ with ⟨c, cdL, cα, cβ⟩;
  exact ⟨c, L, aL, bL, cα, cβ, not_online_of_sameside cdL⟩

theorem not_sameside_symm (abL : ¬sameside a b L) : ¬sameside b a L := fun baL =>
  abL (sameside_symm baL)

lemma diffside_symm (abL : diffside a b L) : diffside b a L :=
  ⟨abL.2.1, abL.1, (not_sameside_symm abL.2.2)⟩

theorem diffside_of_sameside_diffside (abL : sameside a b L) (acL : diffside a c L) :
  diffside b c L := by
by_contra h; unfold diffside at h; push_neg at h; exact acL.2.2
 (sameside_trans (sameside_symm abL) (h (not_online_of_sameside (sameside_symm abL)) acL.2.1))

theorem sameside_of_diffside_diffside (abL : diffside a b L) (acL : diffside a c L) :
  sameside b c L := (or_iff_right acL.2.2).mp
  (sameside_or_of_diffside abL.1 abL.2.1 acL.2.1 abL.2.2)

theorem diffside_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ c d L, online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ on_circle d α ∧ on_circle d β ∧ diffside c d L := by
rcases online_of_circles_inter aα bβ αβ with ⟨c, L, aL, bL, cα, cβ, cL⟩;
rcases diffside_of_not_online cL with ⟨e, eL, ceL⟩; rcases pt_sameside_of_circles_inter aL bL eL
 aα bβ αβ with ⟨d, deL, dα, dβ⟩; exact ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, diffside_symm
 (diffside_of_sameside_diffside (sameside_symm deL) ⟨eL, cL, not_sameside_symm ceL⟩)⟩

theorem online_of_col_online (ab : a ≠ b) (aL : online a L) (bL : online b L)
  (col_abc : colinear a b c) : online c L :=
by rcases col_abc with ⟨L, aM, bM, cM⟩; rwa [line_unique_of_pts ab aM bM aL bL] at cM

theorem triangle_of_ne_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L) :
  triangle a b c := fun col => by exact cL (online_of_col_online ab aL bL col)

theorem online_3_of_triangle (aL : online a L) (bL : online b L) (tri_abc : triangle a b c) :
  ¬online c L := fun cL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_1_of_triangle (bL : online b L) (cL : online c L) (tri_abc : triangle a b c) :
  ¬online a L := fun aL => tri_abc ⟨L, aL, bL, cL⟩

theorem online_2_of_triangle (aL : online a L) (cL : online c L) (tri_abc : triangle a b c) :
  ¬online b L := fun bL => tri_abc ⟨L, aL, bL, cL⟩

theorem eq_tri_of_length_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L)
  (ab_ac : length a b = length a c) (bc_ba : length b c = length b a) : eq_tri a b c :=
⟨triangle_of_ne_online ab aL bL cL, by perma, by linperm, by linperm⟩

theorem B_circ_of_ne (ab : a ≠ b) (bc : b ≠ c) : ∃ d α, B a b d ∧
  center_circle b α ∧ on_circle c α ∧ on_circle d α := by
rcases circle_of_ne bc with ⟨α, bα, cα⟩; rcases pt_oncircle_of_inside_ne ab
 (inside_circle_of_center bα) with ⟨d, Babd, dα⟩; exact ⟨d, α, Babd, bα, cα, dα⟩

theorem online_of_eq (ab : a = b) (aL : online a L) : online b L := by rwa [ab] at aL

theorem online_of_eq' (ab : a = b) (bL : online b L) : online a L := by rwa [ab.symm] at bL

theorem ne_12_of_tri (tri: triangle a b c) : a ≠ b :=
  fun ac => by rcases line_of_pts a c with ⟨L, aL, cL⟩; exact tri ⟨L, aL, online_of_eq ac aL, cL⟩

theorem ne_21_of_tri (tri : triangle a b c) : b ≠ a := Ne.symm $ ne_12_of_tri tri

theorem ne_23_of_tri (tri: triangle a b c) : b ≠ c :=
  fun bc => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq bc bL⟩

theorem ne_32_of_tri (tri : triangle a b c) : c ≠ b := fun cb => (ne_23_of_tri tri) cb.symm

theorem ne_13_of_tri (tri : triangle a b c) : a ≠ c :=
  fun ac => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq ac aL⟩

theorem ne_31_of_tri (tri : triangle a b c) : c ≠ a := fun ca => (ne_13_of_tri tri) ca.symm

theorem incirc_of_lt (aα : center_circle a α) (bα : on_circle b α)
  (ac_ab : length a c < length a b) : in_circle c α := (in_circle_iff_length_lt aα bα).mp ac_ab

theorem B_circ_out_of_B (ab : a ≠ b) (Bacd : B a c d) (ab_ac : length a b = length a c) :
    ∃ e α, B a b e ∧ center_circle a α ∧ on_circle d α ∧ on_circle e α := by
  rcases circle_of_ne (ne_13_of_B Bacd) with ⟨α, aα, dα⟩;
  rcases pt_oncircle_of_inside_ne ab (incirc_of_lt aα dα (by linarith[length_sum_perm_of_B Bacd] :
  length a b < length a d)) with ⟨e, Babe, eα⟩; exact ⟨e, α, Babe, aα, dα, eα⟩

theorem length_eq_of_oncircle (aα : center_circle a α) (bα : on_circle b α) (cα : on_circle c α) :
   length a b = length a c := (on_circle_iff_length_eq aα bα).mpr cα

theorem on_circle_of_oncircle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≠ length a c) : ¬on_circle c α :=
fun cα => ab_ac (length_eq_of_oncircle aα bα cα)

theorem incircle_of_on_circle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≤ length a c) : ¬in_circle c α :=
fun c_in_α => by linarith[(in_circle_iff_length_lt aα bα).mpr c_in_α]

theorem length_eq_of_B_B (Bdbe: B d b e) (Bdaf : B d a f) (da_db : length d a = length d b)
  (de_df : length d e = length d f):
length a f = length b e := by linarith[length_sum_perm_of_B Bdbe, length_sum_perm_of_B Bdaf]

theorem B_oncircle_of_inside_outside (a_in_α : in_circle a α) (b_out_α : out_circle b α) :
  ∃ c, B a c b ∧ on_circle c α :=
pt_on_circle_of_inside_outside b_out_α.1 a_in_α b_out_α.2

theorem out_circle_of_lt (aα : center_circle a α) (bα : on_circle b α)
    (ab_lt_ac : length a b < length a c) : out_circle c α := ⟨on_circle_of_oncircle_length aα bα
  (by linarith), incircle_of_on_circle_length aα bα (by linarith)⟩

theorem sss (ab_de : length a b = length d e) (bc_ef : length b c = length e f)
(ac_df : length a c = length d f) : angle a b c = angle d e f ∧ angle b a c = angle e d f
  ∧ angle a c b = angle d f e :=
⟨(SAS_iff_SSS (by linperm) bc_ef).mpr ac_df,
(SAS_iff_SSS ab_de ac_df).mpr bc_ef, (SAS_iff_SSS (by linperm) (by linperm)).mpr ab_de⟩

theorem sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
(Abac : angle b a c = angle e d f) : length b c = length e f ∧ angle a b c = angle d e f ∧
  angle a c b = angle d f e :=
⟨(SAS_iff_SSS ab_de ac_df).1 Abac, (sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).1,
(sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).2.2⟩

theorem tri132_of_tri123 (tri_abc : triangle a b c) : triangle a c b :=
  fun col => by unfold colinear at col; simp_rw [And.comm] at col; exact tri_abc col

theorem tri231_of_tri123 (tri_abc : triangle a b c) : triangle b c a :=
  fun col => by rcases col with ⟨L, bL, cL, aL⟩; exact tri_abc ⟨L, aL, bL, cL⟩

theorem tri312 (tri_abc : triangle a b c) : triangle c a b :=
  tri231_of_tri123 $ tri231_of_tri123 $ tri_abc

theorem tri213 (tri_abc : triangle a b c) : triangle b a c :=
  tri132_of_tri123 $ tri231_of_tri123 $ tri_abc

theorem tri321 (tri_abc : triangle a b c) : triangle c b a := tri132_of_tri123 $ tri312 tri_abc

theorem area_eq_of_sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
  (Abac_Aedf : angle b a c = angle e d f) : area a b c = area d e f :=
area_eq_of_SSS ab_de ac_df (sas ab_de ac_df Abac_Aedf).1

theorem angle_extension_of_B (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩;
  refine angle_extension ((ne_12_of_B Babb1).symm) ((ne_13_of_B Babb1).symm) ac.symm ac.symm aL bL
    (online_3_of_B Babb1 aL bL) aM cM cM (not_B_of_B Babb1) $ fun Bcac => (ne_13_of_B Bcac) rfl

theorem area_add_of_B (Babc : B a b c) (tri_dac : triangle d a c) :
  area d a b + area d c b = area d a c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; have cL := online_3_of_B Babc aL bL
exact (area_add_iff_B (ne_12_of_B Babc) (ne_23_of_B Babc) (Ne.symm (ne_13_of_B Babc)) aL bL cL
  (online_1_of_triangle aL cL tri_dac)).mp Babc

theorem area_add_of_B_offline (Babc : B a b c) (aL : online a L) (cL : online c L)
  (dL : ¬online d L) : area d a b + area d c b = area d a c :=
area_add_of_B Babc $ by perma[triangle_of_ne_online (ne_13_of_B Babc) aL cL dL]

theorem col_of_area_zero_ne (ab : a ≠ b) (area_abc : area a b c = 0) : colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact ⟨L, aL, bL, (area_zero_iff_online ab aL bL).mp area_abc⟩

theorem col_132_of_col (col_123 : colinear a b c) : colinear a c b := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, bL⟩

theorem col_213_of_col (col_123 : colinear a b c) : colinear b a c := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, bL, aL, cL⟩

theorem col_312 (col : colinear a b c) : colinear c a b := by
  rcases col with ⟨L, aL, bL, cL⟩; exact ⟨L, cL, aL, bL⟩

theorem col_134_of_col_123_col_124 (ab : a ≠ b) (col_123 : colinear a b c)
  (col_124 : colinear a b d) : colinear a c d := by
rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, online_of_col_online ab aL bL col_124⟩

theorem tri_143_of_tri_col (ad : a ≠ d) (tri_abc : triangle a b c) (col_abd : colinear a b d) :
  triangle a d c := fun col_adc => by rcases col_abd with ⟨L, aL, bL, dL⟩; exact tri_abc
                                        ⟨L, aL, bL, online_of_col_online ad aL dL col_adc⟩

theorem col_of_B (Babc : B a b c) : colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact ⟨L, aL, bL, online_3_of_B Babc aL bL⟩

theorem pt_inter_of_not_sameside (abL : ¬sameside a b L) :
    ∃ c M, online a M ∧ online b M ∧ online c M ∧ online c L := by
   rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases pt_of_lines_inter $ lines_inter_of_not_sameside
    aM bM abL with ⟨c, cL, cM⟩; refine ⟨c, M, aM, bM, cM, cL⟩

theorem ne_of_diffside (abL : diffside a b L) : a ≠ b :=
  fun ab => by rw [ab] at abL; exact abL.2.2 $ sameside_rfl_of_not_online abL.1

theorem ne_of_online (aL : online a L) (bL : ¬online b L) : a ≠ b :=
  fun ab => by rw [ab] at aL; exact bL aL

theorem ne_of_online' (aL : online a L) (bL : ¬online b L) : b ≠ a :=
  fun ab => by rw [←ab] at aL; exact bL aL

theorem ne_line_of_online (bM : online b M) (bL : ¬online b L) : L ≠ M :=
  fun LM => by rw [←LM] at bM; exact bL bM

theorem ne_line_of_online' (bM : online b M) (bL : ¬online b L) : M ≠ L :=
  Ne.symm $ ne_line_of_online bM bL

theorem pt_B_of_diffside (abL : diffside a b L) : ∃ c, online c L ∧ B a c b := by
  rcases pt_inter_of_not_sameside abL.2.2 with ⟨c, M, aM, bM, cM, cL⟩
  refine ⟨c, cL, B_of_online_inter (Ne.symm $ ne_of_online cL abL.1) (ne_of_online cL abL.2.1)
    (ne_of_diffside abL) (Ne.symm $ ne_line_of_online bM abL.2.1) aM cM bM cL abL.2.2⟩

theorem B_of_three_col_ne (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (col_abc : colinear a b c) :
    B a b c ∨ B b a c ∨ B a c b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact B_of_three_online_ne ab ac bc aL bL cL

theorem B_of_length_eq_col (ab : a ≠ b) (ac : a ≠ c) (col_abc : colinear a b c)
    (ab_cb : length a b = length c b) : B a b c := by
  rcases B_of_three_col_ne ab ac (ne_of_ne_len ab $ by linperm) col_abc
    with Babc | Bet | Bet; exact Babc; repeat {linarith [length_sum_perm_of_B Bet]}

theorem length_zero_of_eq (ab : a = b) : length a b = 0 := (length_eq_zero_iff).mpr ab

theorem eq_of_length_zero (ab_0 : length a b = 0) : a = b := (length_eq_zero_iff).mp ab_0

theorem ne_of_triangle_length_eq (tri_abc : triangle a b c) (bd_cd : length b d = length c d) :
    b ≠ d := fun bd => ne_23_of_tri tri_abc $ bd.trans (eq_of_length_zero $ bd_cd.symm.trans $
      length_zero_of_eq bd).symm

theorem len_21_of_len (ab_r : length a b = r) : length b a = r := by perma

theorem len_43_of_len (ab_r : r = length a b) : r = length b a := by perma

theorem len_2143_of_len (ab_cd : length a b = length c d) : length b a = length d c := by perma

theorem ang_321_of_ang (abc_r : angle a b c = r) : angle c b a = r := by perma

theorem ang_654_of_ang (abc_r : r = angle a b c) : r = angle c b a := by perma

theorem ang_654321_of_ang (abc_def : angle a b c = angle d e f) : angle c b a = angle f e d :=
  by perma

theorem angle_extension_of_B' (ac : a ≠ c) (Babb1 : B a b b1) : angle c a b = angle c a b1 :=
  ang_654321_of_ang $ angle_extension_of_B ac Babb1

theorem online_of_B_online (Babc : B a b c) (aL : online a L) (cL : ¬online c L) : ¬online b L :=
  fun bL => cL (online_3_of_B Babc aL bL)

theorem online_of_B_online' (Babc : B a b c) (bL : online b L) (cL : ¬online c L) : ¬online a L :=
  fun aL => cL (online_3_of_B Babc aL bL)

theorem sameside_of_B_online_3 (Babc : B a b c) (aL : online a L) (cL : ¬online c L) :
    sameside b c L := sameside_of_B_not_online_2 Babc aL $ online_of_B_online Babc aL cL

theorem ne_of_sameside (bL : online b L) (acL : sameside a c L) : a ≠ b :=
  (ne_of_online bL (not_online_of_sameside acL)).symm

theorem ne_of_sameside' (cL : online c L) (abL : sameside a b L) : c ≠ a :=
  ne_of_online cL $ not_online_of_sameside abL

theorem tri_of_B_B_tri (Babd : B a b d) (Bace : B a c e) (tri_abc : triangle a b c) :
    triangle a d e := tri132_of_tri123 $ tri_143_of_tri_col (ne_13_of_B Bace) (tri132_of_tri123 $
  tri_143_of_tri_col (ne_13_of_B Babd) tri_abc $ col_of_B Babd) $ col_of_B Bace

theorem ne_21_of_B (Babc : B a b c) : b ≠ a := Ne.symm $ ne_12_of_B Babc

theorem ne_32_of_B (Babc : B a b c) : c ≠ b := Ne.symm $ ne_23_of_B Babc

theorem sameside_or_of_diffside' (cL : ¬online c L) (abL : diffside a b L) :
    sameside a c L ∨ sameside b c L := sameside_or_of_diffside abL.1 abL.2.1 cL abL.2.2

theorem rightangle_of_angle_eq (Babc : B a b c) (aL : online a L) (cL : online c L)
    (dL : ¬online d L) (dba_dbc : angle d b a = angle d b c) :
    angle d b a = rightangle ∧ angle d b c = rightangle := by
  have ang := ang_321_of_ang $ (angle_eq_iff_rightangle aL cL dL Babc).mp $ ang_321_of_ang dba_dbc
  exact ⟨ang, dba_dbc.symm.trans ang⟩

theorem diffside_of_not_online' (aL : ¬online a L) : ∃ b, diffside a b L := by
  rcases diffside_of_not_online aL with ⟨b, bL, abL⟩; exact ⟨b, aL, bL, abL⟩

theorem pts_line_circle_of_not_sameside (aα : center_circle a α) (bα : on_circle b α)
    (abL : ¬sameside a b L) : ∃ c d, c ≠ d ∧
    online c L ∧ online d L ∧ on_circle c α ∧ on_circle d α :=
  pts_of_line_circle_inter $ line_circle_inter_of_not_sameside abL
  (by right; exact inside_circle_of_center aα) $ by left; exact bα

theorem B_or_B_of_B_B (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
    B b c d ∨ B b d c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases B_of_three_online_ne (ne_23_of_B Babc) (ne_23_of_B Babd) cd bL
    (online_3_of_B Babc aL bL) (online_3_of_B Babd aL bL) with Bet | Bet | Bet
  left; exact Bet; exfalso; exact (not_B324_of_B123_B124 Babc Babd) Bet; right; exact Bet

theorem angle_extension_of_B_B (be : b ≠ e) (Babc : B a b c) (Babd : B a b d) :
    angle e b d = angle e b c := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_B_B cd Babc Babd with Bet | Bet; symm
  repeat exact ang_654321_of_ang $ angle_extension_of_B be Bet

theorem online_of_sameside_inter (ab : a ≠ b) (aL : online a L) (aM : online a M) (bL : online b L)
    (cM : online c M) (cdL : sameside c d L) : ¬online b M :=
  fun bM => (not_online_of_sameside cdL) (by rwa [line_unique_of_pts ab aM bM aL bL] at cM)

theorem diffside_of_sameside_sameside (aL : online a L) (aM : online a M) (aN : online a N)
    (bL : online b L) (cM : online c M) (dN : online d N) (dcL : sameside d c L)
    (bcN : sameside b c N) : diffside b d M :=
  ⟨online_of_sameside_inter (ne_of_sameside' aN bcN) aL aM bL cM $ sameside_symm dcL,
  online_of_sameside_inter (ne_of_sameside' aL dcL) aN aM dN cM $ sameside_symm bcN,
  not_sameside_of_sameside_sameside aL aM aN bL cM dN (sameside_symm dcL) bcN⟩

theorem angle_add_of_sameside (aL : online a L) (bL : online b L) (aM : online a M)
    (cM : online c M) (cdL : sameside c d L) (bdM : sameside b d M) :
    angle b a c = angle d a b + angle d a c := by
  linarith[angle_symm b a d, (angle_add_iff_sameside (ne_of_sameside' aM bdM) (ne_of_sameside'
    aL cdL) aL bL aM cM (not_online_of_sameside $ sameside_symm bdM) (not_online_of_sameside $
    sameside_symm cdL) $ ne_line_of_online cM $ not_online_of_sameside cdL).mpr ⟨bdM, cdL⟩]

theorem offline_of_B_offline (Babc : B a b c) (aL : online a L) (bL : online b L) (bN : online b N)
    (dN : online d N) (dL : ¬online d L) : ¬online a N :=
  online_3_of_triangle bN dN (tri231_of_tri123 $ triangle_of_ne_online (ne_12_of_B Babc) aL bL dL)

theorem diffside_of_B_offline (Babc : B a b c) (aL : online a L) (bL : online b L) (bN : online b N)
    (dN : online d N) (dL : ¬online d L) : diffside a c N :=
  ⟨offline_of_B_offline Babc aL bL bN dN dL, offline_of_B_offline (B_symm Babc)
  (online_3_of_B Babc aL bL) bL bN dN dL, not_sameside13_of_B123_online2 Babc bN⟩

theorem diffside_of_B_offline'' (Babc : B a b c) (aN : ¬online a N) (bN : online b N) :
    diffside a c N :=
  ⟨aN, fun cN => aN $ online_3_of_B (B_symm Babc) cN bN, not_sameside13_of_B123_online2 Babc bN⟩

theorem sameside_of_B_sameside_sameside (Babc : B a b c) (bL : online b L) (bM : online b M)
    (bN : online b N) (aL : online a L) (eM : online e M) (dN : online d N) (edL : sameside e d L)
    (cdM : sameside c d M) : sameside a e N :=
  sameside_of_diffside_diffside (diffside_symm $ diffside_of_B_offline Babc aL bL bN dN $
  not_online_of_sameside $ sameside_symm edL) (diffside_of_sameside_sameside bL bN bM
  (online_3_of_B Babc aL bL) dN eM edL cdM)

theorem B_or_B_of_sameside (bc : b ≠ c) (aL : online a L) (col : colinear a b c)
    (bcL : sameside b c L) : B a b c ∨ B a c b := by
  rcases B_of_three_col_ne (ne_of_sameside' aL bcL) (ne_of_sameside' aL $ sameside_symm bcL)
    bc col with Bet | Bet | Bet
  left; exact Bet; exfalso; exact not_sameside13_of_B123_online2 Bet aL $ bcL; right; exact Bet

theorem angle_extension_of_sameside (ab : a ≠ b) (bL : online b L)
    (col : colinear b c d) (cdL : sameside c d L) : angle c b a = angle d b a := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_sameside cd bL col cdL with Bet | Bet; symm
  repeat exact symm $ angle_extension_of_B (Ne.symm ab) Bet

theorem sameside_of_B_diffside_sameside (Babc : B a b c) (aL : online a L) (bL : online b L)
    (bM : online b M) (eM : online e M) (dM : ¬online d M) (edL : sameside e d L)
    (cdM : ¬sameside c d M) : sameside a d M :=
   sameside_symm $ sameside_of_diffside_diffside ⟨offline_of_B_offline
    (B_symm Babc) (online_3_of_B Babc aL bL) bL bM eM $ not_online_of_sameside edL, dM, cdM⟩ $
    diffside_symm $ diffside_of_B_offline Babc aL bL bM eM $ not_online_of_sameside edL

theorem offline_of_online_offline (bc : b ≠ c) (aL : online a L) (bL : online b L)
    (bM : online b M) (cM : online c M) (aM : ¬online a M) : ¬online c L :=
  online_2_of_triangle aL bL $ tri321 $ triangle_of_ne_online bc bM cM aM

theorem offline_of_ne_online_offline (ab : a ≠ b) (aL : online a L) (bL : online b L)
    (aM : online a M) (cM : online c M) (cL : ¬online c L) : ¬online b M :=
  fun bM => cL (by rwa[←line_unique_of_pts ab aL bL aM bM] at cM)

theorem online_of_angle_zero (ab : a ≠ b) (ac : a ≠ c) (aL : online a L) (bL : online b L)
    (bac_0 : angle  b a c = 0) : online c L ∧ ¬B b a c :=
  (angle_zero_iff_online ab ac aL bL).mpr bac_0

theorem B_of_col_diffside (col_abc : colinear a b c) (bL : online b L)
    (acL : diffside a c L) : B a b c := by
  rcases col_abc with ⟨M, aM, bM, cM⟩; exact B_of_online_inter (ne_of_online' bL acL.1)
    (ne_of_online bL acL.2.1) (ne_of_diffside acL) (ne_line_of_online' aM acL.1) aM bM cM bL
    acL.2.2

theorem B_of_col_sameside (bL : online b L) (acL : sameside a c L) :
    ¬B a b c := fun Babc => not_sameside13_of_B123_online2 Babc bL $ acL

theorem angle_zero_of_online (ab : a ≠ b) (ac : a ≠ c) (aL : online a L) (bL : online b L)
    (cL : online c L) (Bbac : ¬B b a c) : angle b a c = 0 :=
  (angle_zero_iff_online ab ac aL bL).mp ⟨cL, Bbac⟩

theorem sameside_of_B_diffside (Babc : B a b c) (bL : online b L) (aeL : diffside a e L) :
    sameside e c L :=
  sameside_of_diffside_diffside aeL $ diffside_of_B_offline'' Babc aeL.1 bL

/-- Lemma for I.14 that handles some casework. If one angle is contained in another and are equal
      then a sub-angle is zero -/
lemma angle_zero_of_lt_eq (ab : a ≠ b) (aL : online a L) (bL : online b L) (dcL : sameside d c L)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a d with ⟨M, aM, dM⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  by_cases bcM : sameside b c M
  · linarith[angle_add_of_sameside aL bL aM dM dcL bcM, angle_symm c a b]
  by_cases cM : online c M
  · exact angle_zero_of_online (ne_of_sameside' aL $ sameside_symm dcL) (ne_of_sameside' aL dcL)
      aM cM dM (B_of_col_sameside aL $ sameside_symm dcL)
  · linarith[angle_symm b a d, angle_add_of_sameside aL bL aN cN (sameside_symm dcL) $
      sameside_of_sameside_not_sameside ab aL aM aN bL dM cN cM dcL bcM, angle_symm d a c]

theorem angle_zero_of_lt_eq_B (ab : a ≠ b) (Bbcd : B b c d) (tri_bad : triangle b a d)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact angle_zero_of_lt_eq ab aL bL (sameside_symm $
    sameside_of_B_online_3 Bbcd bL (online_3_of_triangle bL aL tri_bad)) bad_bac

theorem ne_of_col_tri (col_abc : colinear a b c) (tri_acd : triangle d a c) : d ≠ b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact ne_of_online' bL $ online_1_of_triangle aL cL tri_acd

theorem ne_of_col_tri' (col_abc : colinear a b c) (tri_acd : triangle d a c) : b ≠ d :=
  Ne.symm $ ne_of_col_tri col_abc tri_acd

theorem tri_of_B_tri (Babc : B a b c) (tri_acd : triangle d a c) : triangle d b c :=
  tri321 $ tri_143_of_tri_col (ne_32_of_B Babc) (tri321 tri_acd) $ col_312 $ col_of_B Babc

theorem diffside_of_B_offline' (Babc : B a b c) (bL : online b L) (aL : ¬online a L) :
    diffside a c L :=
  ⟨aL, fun cL => aL $ online_3_of_B (B_symm Babc) cL bL, not_sameside13_of_B123_online2 Babc bL⟩

theorem tri_of_B_B_base_tri (Bade : B a d e) (Bbdc : B b d c) (tri_abc : triangle a b c) :
    triangle a e b :=
  tri_143_of_tri_col (ne_13_of_B Bade) (tri_of_B_tri (B_symm Bbdc) $ tri132_of_tri123 tri_abc)
    (col_of_B Bade)

theorem offline_of_B_B_tri (Bade : B a d e) (Bbdc : B b d c) (aL : online a L) (bL : online b L)
    (tri_abc : triangle a b c) : ¬online e L :=
  fun eL => tri_of_B_B_base_tri Bade Bbdc tri_abc $ ⟨L, aL, eL, bL⟩

theorem nonzero_angle_of_offline (ab : a ≠ b) (aL : online a L) (bL : online b L)
    (cL : ¬online c L) : angle c a b ≠ 0 :=
  fun bac_0 => cL ((angle_zero_iff_online ab (ne_of_online aL cL) aL bL).mpr (ang_321_of_ang
    bac_0)).1

theorem zero_lt_angle_of_offline (ab : a ≠ b) (aL : online a L) (bL : online b L)
    (cL : ¬online c L) : 0 < angle c a b :=
  lt_of_le_of_ne (angle_nonneg c a b) $ Ne.symm $ nonzero_angle_of_offline ab aL bL cL

theorem zero_lt_angle_of_tri (tri_abc : triangle a b c) : 0 < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL
    bL (online_3_of_triangle aL bL tri_abc)

theorem sameside_of_B_B (Babc : B a b c) (Bade : B a d e) (bL : online b L) (dL : online d L)
    (aL : ¬online a L) : sameside c e L :=
   sameside_of_diffside_diffside (diffside_of_B_offline' Babc bL aL) $ diffside_of_B_offline'
    Bade dL aL

theorem angle_lt_of_B_tri (Bcdb : B c d b) (tri_abc : triangle a b c) :
    angle c a d < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩
  have ang_split := angle_add_of_sameside aM cM aL bL (sameside_symm $ sameside_of_B_online_3 Bcdb
    cM (online_2_of_triangle aM cM tri_abc)) $ sameside_symm $ sameside_of_B_online_3 (B_symm Bcdb)
    bL $ online_3_of_triangle aL bL tri_abc
  linarith[angle_symm d a c, zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL bL (fun dL =>
    (online_3_of_triangle aL bL tri_abc) $ online_3_of_B (B_symm Bcdb) bL dL)]

theorem ne_of_oncircle (aα : on_circle a α) (bα : ¬on_circle b α) : a ≠ b :=
  fun ab => bα $ by rwa [ab] at aα

theorem B_or_B_of_circ_pt (ab : a ≠ b) (aα : center_circle a α) (bα : ¬on_circle b α):
    ∃ c, (B a c b ∨ B a b c) ∧ on_circle c α := by
  rcases pt_oncircle_of_inside_ne ab.symm $ inside_circle_of_center aα with ⟨d, Bbad, -⟩
  rcases pt_oncircle_of_inside_ne (ne_32_of_B Bbad) $ inside_circle_of_center aα with ⟨c, Bdac, cα⟩
  exact ⟨c, B_or_B_of_B_B (ne_of_oncircle cα bα) Bdac $ B_symm Bbad, cα⟩

theorem in_circle_of_lt_lt (aα : center_circle a α) (bβ : center_circle b β)
    (cα : on_circle c α) (dβ : on_circle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : ∃ e, on_circle e α ∧ in_circle e β := by
  by_cases bα : on_circle b α; exact ⟨b, bα, inside_circle_of_center bβ⟩
  rcases B_or_B_of_circ_pt (mt length_eq_zero_iff.mpr $ by linarith[abs_lt.mp lt_cen]) aα bα with
   ⟨e, Bet, eα⟩
  rcases Bet with Bet | Bet
  repeat exact
    ⟨e, eα, incirc_of_lt bβ dβ $ by linarith[length_sum_of_B Bet, length_eq_of_oncircle aα cα eα,
                            abs_lt.mp lt_cen, length_symm e b]⟩

theorem circint_of_lt_lt (aα : center_circle a α) (bβ : center_circle b β)
    (cα : on_circle c α) (dβ : on_circle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : circles_inter α β := by
  rcases in_circle_of_lt_lt aα bβ cα dβ lt_cen cen_lt with ⟨e, eα, eβ⟩
  rcases in_circle_of_lt_lt bβ aα dβ cα (by rw[abs_lt]; constructor; repeat
    linperm[abs_lt.mp lt_cen]) $ by linperm with ⟨f, fβ, fα⟩
  exact circles_inter_of_inside_on_circle eα fβ fα eβ

theorem ang_2_nonzero_of_tri (tri_abc : triangle a b c) : angle b a c ≠ 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; linarith[zero_lt_angle_of_offline (ne_12_of_tri
    tri_abc) aL bL (online_3_of_triangle aL bL tri_abc), angle_symm b a c]

theorem not_B_symm (Babc : ¬B a b c) : ¬B c b a := fun Bet => Babc $ B_symm Bet

theorem ang_121_zero_of_ne (ab : a ≠ b) : angle a b a = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact angle_zero_of_online ab.symm ab.symm bL aL aL $ fun Baba => ne_13_of_B Baba rfl

theorem ne_23_of_sa (tri_abc : triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf ab_de
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_12_of_tri tri_abc) ab_de).symm,
    zero_lt_angle_of_tri tri_abc]

theorem ne_23_of_sa' (tri_abc : triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_13_of_tri tri_abc) ac_df).symm,
    zero_lt_angle_of_tri tri_abc]

theorem not_B_of_tri_ang (tri_abc : triangle a b c) (ef : e ≠ f) (de : d ≠ e)
    (abc_def : angle a b c = angle d e f) : ¬B e d f := by
  intro Bedf; rcases col_of_B Bedf with ⟨L, eL, dL, fL⟩
  linperm [angle_zero_of_online de.symm ef eL dL fL $ not_B_of_B Bedf, zero_lt_angle_of_tri $
    tri213 tri_abc]

theorem triangle_of_asa (tri_abc : triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    triangle d e f := by
  intro col_def
  have df := ne_23_of_sa (tri213 tri_abc) (by linperm) abc_def
  have de := ne_of_ne_len (ne_12_of_tri tri_abc) ab_de
  rcases B_of_three_col_ne de df (ne_23_of_sa tri_abc ab_de bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa tri_abc ab_de bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem triangle_of_saa (de : d ≠ e) (tri_abc : triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    triangle d e f := by
  intro col_def
  have df := ne_of_ne_len (ne_13_of_tri tri_abc) ac_df
  rcases B_of_three_col_ne de df (ne_23_of_sa' tri_abc ac_df bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa' tri_abc ac_df bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem offline_of_online_inter (bc : b ≠ c) (aM : online a M) (bM : online b M) (bL : online b L)
    (cL : online c L) (cN : online c N) (dN : online d N) (aL : ¬online a L) (dL : ¬online d L)
    (eM : online e M) (eN : online e N) : ¬online e L :=
  offline_of_online_offline (ne_of_online' eM $ offline_of_online_offline bc aM bM bL cL aL) bL cL
    cN eN $ offline_of_online_offline bc.symm dN cN cL bL dL

theorem para_symm (paraMN : para M N) : para N M := fun e => by have := paraMN e; tauto

theorem offline_of_para (aM : online a M) (paraMN : para M N) : ¬online a N := by
  have := paraMN a; tauto

theorem offline_of_para' (aN : online a N) (paraMN : para M N) : ¬online a M := by
  have := paraMN a; tauto

theorem ne_of_para (aM : online a M) (bN : online b N) (paraMN : para M N) : a ≠ b :=
  ne_of_online aM $ offline_of_para' bN paraMN

theorem ne_of_para' (aM : online a M) (bN : online b N) (paraMN : para M N) : b ≠ a :=
  ne_of_online' aM $ offline_of_para' bN paraMN

theorem not_para_of_inter (aM : online a M) (aN : online a N) : ¬para M N := by
  intro paraMN; have := paraMN a; tauto

theorem diffside_of_B_sameside (Bcad : B c a d) (aL : online a L) (ceL : sameside c e L) :
    diffside d e L :=
  diffside_symm $ diffside_of_sameside_diffside ceL $ diffside_of_B_offline' Bcad aL $
    not_online_of_sameside ceL

theorem pt_of_online_not_sameside (aL : online a L) (bL : online b L) (abM : ¬sameside a b M) :
    ∃ c, online c M ∧ online c L :=
pt_of_lines_inter $ lines_inter_of_not_sameside aL bL abM

theorem sameside_of_para_online (aM : online a M) (bM : online b M) (paraMN : para M N) :
    sameside a b N := by
  by_contra abO; rcases pt_of_online_not_sameside aM bM abO with ⟨c, cN, cM⟩
  exact not_para_of_inter cM cN paraMN

theorem sameside_of_para_online' (aN : online a N) (bN : online b N) (paraMN : para M N) :
    sameside a b M := sameside_of_para_online aN bN (para_symm paraMN)

theorem tri124_of_paragram (pgram : paragram a b c d M N O P) : triangle a b d := by
  have ⟨aM, bM, bN, cN, _, dO, _, aP, paraMO, paraNP⟩ := pgram
  exact triangle_of_ne_online (ne_of_sameside' aP $ sameside_of_para_online
    bN cN paraNP) aM bM $ offline_of_para dO $ para_symm paraMO

theorem sameside_of_sameside_diffside (aL : online a L) (aM : online a M) (aN : online a N)
    (bL : online b L) (cM : online c M) (dN : online d N) (cdL : sameside c d L)
    (bdM : diffside b d M) : sameside b c N :=
  sameside_of_sameside_not_sameside (ne_of_online aM bdM.1) aL aM aN bL cM dN bdM.2.1 cdL bdM.2.2

theorem sameside_of_quad (aL : online a L) (bL : online b L) (bM : online b M) (cM : online c M)
    (cN : online c N) (dN : online d N) (dO : online d O) (aO : online a O) (abN : sameside a b N)
    (cdL : sameside c d L) (adM : sameside a d M) : sameside b c O := by
  rcases line_of_pts b d with ⟨P, bP, dP⟩
  perma[sameside_of_sameside_diffside dN dP dO cN bP aO (by perma) $
    by perma[diffside_of_sameside_sameside bL bP bM aL dP cM cdL adM]]

theorem diffside_of_paragram (bL : online b L) (dL : online d L)
    (pgram : paragram a b c d M N O P) : diffside a c L := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, paraMO, paraNP⟩ := pgram
  exact diffside_of_sameside_sameside bM bL bN aM dL cN (sameside_of_para_online' cO dO paraMO)
    (sameside_of_para_online' aP dP paraNP)

theorem offline_of_col_offline (bc : b ≠ c) (col_abc : colinear a b c) (bL : online b L)
    (aL : ¬online a L) : ¬online c L :=
  fun cL => aL $ online_of_col_online bc bL cL (by perma[col_abc])

theorem B_of_col_offline (bc : b ≠ c) (col_abc : colinear a b c) (bL : online b L)
    (aL : ¬online a L) (acL : ¬sameside a c L) : B a b c :=
  B_of_col_diffside col_abc bL ⟨aL, offline_of_col_offline bc col_abc bL aL, acL⟩

theorem tri_of_sameside (bc : b ≠ c) (bL : online b L) (cL : online c L) (adL : sameside a d L) :
    triangle a b c := tri312 $ triangle_of_ne_online bc bL cL $ not_online_of_sameside adL

theorem B_diagonal_of_quad (aL : online a L) (bL : online b L) (bM : online b M)
    (cM : online c M) (cN : online c N) (dN : online d N) (abN : sameside a b N)
    (cdL : sameside c d L) (adM : sameside a d M) : ∃ e P O, B b e d ∧ B a e c ∧ online a P ∧
    online c P ∧ online b O ∧ online d O ∧ online e P ∧ online e O ∧
    diffside b d P ∧ diffside a c O := by
  rcases line_of_pts b d with ⟨O, bO, dO⟩; rcases line_of_pts a c with ⟨P, aP, cP⟩
  rcases line_of_pts a d with ⟨Q, aQ, dQ⟩
  have acO := diffside_of_sameside_sameside bL bO bM aL dO cM cdL adM
  have bdP := diffside_of_sameside_sameside aL aP aQ bL cP dQ (by perma) $
    sameside_of_quad aL bL bM cM cN dN dQ aQ abN cdL adM
  rcases pt_of_online_not_sameside aP cP acO.2.2 with ⟨e, eO, eP⟩
  exact ⟨e, P, O, B_of_col_diffside ⟨O, bO, eO, dO⟩ eP bdP,
    B_of_col_diffside ⟨P, aP, eP, cP⟩ eO acO, aP, cP, bO, dO, eP, eO, bdP, acO⟩

theorem quad_area_comm (aL : online a L) (bL : online b L) (bM : online b M) (cM : online c M)
    (cN : online c N) (dN : online d N) (abN : sameside a b N) (cdL : sameside c d L)
    (adM : sameside a d M) : area a b d + area b c d = area a b c + area a c d := by
  rcases B_diagonal_of_quad aL bL bM cM cN dN abN cdL adM with
    ⟨e, P, O, Bbed, Baec, aP, cP, bO, dO, eP, eO, bdP, acO⟩
  linperm[area_add_of_B_offline Bbed bO dO acO.1, area_add_of_B_offline Bbed bO dO acO.2.1,
    area_add_of_B_offline Baec aP cP bdP.1, area_add_of_B_offline Baec aP cP bdP.2.1]

theorem paragram_area_comm (pgram : paragram a b c d M N O P) :
    area a b d + area b c d = area a b c + area a c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, paraMO, paraNP⟩ := pgram
  exact quad_area_comm aM bM bN cN cO dO (sameside_of_para_online aM bM paraMO)
    (sameside_of_para_online' cO dO paraMO) $ sameside_of_para_online' aP dP paraNP

theorem sameside_of_not_B (bc : b ≠ c) (Babc : ¬B a b c) (bL : online b L) (aL : ¬online a L)
    (col_abc : colinear a b c) : sameside a c L := by
  by_contra acL; exact Babc $ B_of_col_offline bc col_abc bL aL acL

theorem diffside_of_diffside_para (aO : online a O) (bO : online b O) (afM : diffside a f M)
    (paraMO : para M O) : diffside b f M :=
  diffside_of_sameside_diffside (sameside_of_para_online' aO bO paraMO) afM

theorem diffside_of_B_para (Badf : B a d f) (aL : online a L) (dL : online d L)
    (dM : online d M) (cM : online c M) (cN : online c N) (paraLN : para L N) : diffside a f M :=
  diffside_of_B_offline Badf aL dL dM cM $ offline_of_para' cN paraLN

theorem diffside_of_B_pgram (Badf : B a d f) (pgram1 : paragram a d c b L M N O) :
    diffside b f M := by
  have ⟨aL, dL, dM, cM, cN, _, bO, aO, paraLN, paraMO⟩ := pgram1
  exact diffside_of_diffside_para aO bO (diffside_of_B_para Badf aL dL dM cM cN paraLN) paraMO

theorem sameside_of_B_pgram_pgram (Badf : B a d f) (pgram1 : paragram a d c b L M N O)
    (pgram2 : paragram e f c b L P N Q) : sameside b d P := by
  have ⟨_, dL, dM, cM, cN, bN, _, _, paraLN, _⟩ := pgram1
  exact sameside_of_sameside_diffside cN cM pgram2.2.2.2.1 bN dM pgram2.2.2.1
    (sameside_of_para_online dL pgram2.2.1 paraLN) $ diffside_of_B_pgram Badf pgram1

theorem sameside_of_B_prgram_pgram_trans (Badf : B a d f)
    (pgram1 : paragram a d c b L M N O) (pgram2 : paragram e f c b L P N Q) : sameside d e P := by
  have ⟨_, _, _, _, _, _, bQ, eQ, _, paraPQ⟩ := pgram2
  exact sameside_trans (sameside_of_B_pgram_pgram Badf pgram1 pgram2) $
    sameside_of_para_online' bQ eQ paraPQ

theorem sameside_of_B_prgram_pgram_trans' (Badf : B a d f)
    (pgram1 : paragram a d c b L M N O) (pgram2 : paragram e f c b L P N Q) : sameside a e P :=
  sameside_trans (sameside_of_B_not_online_2 (B_symm Badf) pgram2.2.2.1
    (not_online_of_sameside $ by perma[sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2])) $
    sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2

theorem sameside_of_sameside_para (aN : online a N) (bN : online b N) (acM : sameside a c M)
    (paraMN : para M N) : sameside b c M :=
  sameside_trans (sameside_of_para_online' aN bN paraMN) acM

theorem diffside_of_sameside_paragram (fL : online f L) (cP : online c P) (fP : online f P)
  (afM : sameside a f M) (pgram : paragram a b c d L M N O) : diffside b d P := by
have ⟨_, bL, bM, cM, cN, dN, dO, aO, paraLN, paraMO⟩ := pgram
exact diffside_of_sameside_sameside cM cP cN bM fP dN (sameside_of_sameside_para aO dO afM paraMO)
  (sameside_of_para_online bL fL paraLN)

theorem diffside_of_sameside_2_paragram (afM : sameside a f M) (pgram1 : paragram a d c b L M N O)
    (pgram2 : paragram e f c b L P N Q) : diffside e d P := by
  have ⟨_, fL, fP, cP, _, _, bQ, eQ, _, paraPQ⟩ := pgram2
  exact diffside_of_sameside_diffside (sameside_of_para_online' bQ eQ paraPQ)
    (by perma[diffside_of_sameside_paragram fL cP fP afM pgram1])

theorem B_of_B_2_paragram (df : d ≠ f) (Badf : ¬B a d f) (pgram1 : paragram a d c b L M N O)
    (pgram2 : paragram e f c b L P N Q) : B e f d := by
  have ⟨aL, dL, dM, _, _, _, _, aO, _, paraMO⟩ := pgram1; have ⟨eL, fL, fP, _, _, _, _, _, _, _⟩ :=
    pgram2; exact B_of_col_diffside ⟨L, eL, fL, dL⟩ fP $ diffside_of_sameside_2_paragram
    (sameside_of_not_B df Badf dM (offline_of_para' aO paraMO) ⟨L, aL, dL, fL⟩) pgram1 pgram2

theorem sameside_of_B_para (Bfea : B f e a) (fP : online f P) (eQ : online e Q) (bQ : online b Q)
   (paraPQ : para P Q) : sameside a b P := sameside_trans (sameside_of_B_not_online_2 Bfea fP $
   offline_of_para' eQ paraPQ) $ sameside_of_para_online' eQ bQ paraPQ

theorem sameside_online_of_diffside (dM : online d M) (aM : online a M) (aL : online a L)
    (cdL : diffside c d L) : ∃ b, online b M ∧ sameside b c L := by
  rcases circle_of_ne (ne_of_online aL cdL.2.1) with ⟨α, acen, _⟩
  rcases pt_oncircle_of_inside_ne (ne_of_online aL cdL.2.1).symm (inside_circle_of_center acen)
    with ⟨b, Bdab, _⟩
  exact ⟨b, online_3_of_B Bdab dM aM, by perma[sameside_of_B_diffside Bdab aL (diffside_symm cdL)]⟩

theorem sameside_of_offline (bL : online b L) (cL : ¬online c L) (bM : ¬online b M)
    (eL : online e L) (eM : online e M) : ∃ d, online d M ∧ sameside d c L := by
  rcases online_ne_of_line M with ⟨a, d, ad, aM, dM⟩
  wlog dL : ¬online d L generalizing a d L; exact this bL cL eL d a ad.symm dM aM $
    offline_of_online_offline ad.symm bL (of_not_not dL) dM aM bM
  by_cases dcL : sameside d c L; exact ⟨d, dM, dcL⟩
  exact sameside_online_of_diffside dM eM eL ⟨cL, dL, not_sameside_symm dcL⟩

theorem angle_add_of_B (Bbcd : B b c d) (bL : online b L) (cL : online c L) (aL : ¬online a L) :
    angle d a b = angle c a d + angle c a b := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases line_of_pts a d with ⟨N, aN, dN⟩
  exact angle_add_of_sameside aN dN aM bM (sameside_symm $ sameside_of_B_online_3 (B_symm Bbcd) dN
    $ offline_of_online_offline (ne_13_of_B Bbcd).symm aN dN (online_3_of_B Bbcd bL cL) bL aL)
    (sameside_symm $ sameside_of_B_online_3 Bbcd bM $ offline_of_online_offline (ne_13_of_B Bbcd)
    aM bM bL (online_3_of_B Bbcd bL cL) aL)

theorem online_of_ne_ne (ac : a ≠ c) (LM : L ≠ M) (aL : online a L) (cL : online c L)
    (cM : online c M) : ¬online a M := fun aM => LM $ line_unique_of_pts ac aL cL aM cM

theorem sameside_of_B_sameside (Bbcd : B b c d) (dL : online d L) (bL : ¬online b L)
    (abL : sameside a b L) : sameside a c L :=
  sameside_trans (sameside_symm abL) $ sameside_symm $ sameside_of_B_online_3 (B_symm Bbcd) dL bL

theorem quad_add_of_quad (Babc : B a b c) (Bdef : B d e f) (aL : online a L) (bL : online b L)
    (cM : online c M) (fM : online f M) (dN : online d N) (eN : online e N) (acN : sameside a c N)
    (feL : sameside f e L) (adM : sameside a d M) :
    area a c f + area a f d = area a b e + area a e d + area b c e + area f e c := by
  rcases B_diagonal_of_quad aL (online_3_of_B Babc aL bL) cM fM (online_3_of_B Bdef dN eN) eN acN
    feL $ sameside_of_B_sameside Bdef fM (not_online_of_sameside $ sameside_symm adM) adM
    with ⟨g, P, O, Bcge, Bagf, aP, fP, cO, eO, gP, gO, ceP, afO⟩
  linperm[area_add_of_B_offline Bagf aP fP ceP.1, area_add_of_B_offline Bdef dN
    (online_3_of_B Bdef dN eN) (not_online_of_sameside acN), area_add_of_B_offline Bagf aP fP
    ceP.2.1, area_add_of_B_offline Bcge cO eO afO.2.1, area_add_of_B_offline Bcge cO eO afO.1,
    area_add_of_B_offline Babc aL (online_3_of_B Babc aL bL)
    (not_online_of_sameside (by perma[feL]))]

theorem B_of_sq (Bbxc : B b x c) (xX : online x X) (lX : online l X) (lP : online l P)
    (paraQX : para Q X) (paraOX : para O X) (pgram : paragram b c d e L O P Q) : B e l d := by
  have ⟨_, _, cO, dO, dP, eP, eQ, bQ, _, _⟩ := pgram
  exact B_of_col_diffside ⟨P, eP, lP, dP⟩ lX $ diffside_symm $ diffside_of_sameside_diffside
    (sameside_of_para_online cO dO paraOX) $ diffside_symm $ diffside_of_sameside_diffside
    (sameside_symm $ sameside_of_para_online eQ bQ paraQX) $ diffside_of_B_offline' Bbxc xX $
    offline_of_para bQ paraQX

theorem sameside_of_pyth (Beld : B e l d) (aX : online a X) (lX : online l X)
    (pgram : paragram b c d e L O P Q) (paraQX : para Q X) : sameside a c Q := by
  have ⟨_, _, cO, dO, _, _, eQ, _, _, paraOQ⟩ := pgram
  exact sameside_trans (sameside_trans (sameside_of_B_online_3 Beld eQ $ offline_of_para dO paraOQ)
    $ sameside_symm $ sameside_of_para_online' aX lX paraQX) $ sameside_symm $
    sameside_of_para_online cO dO paraOQ
 ---------------------------------------- Book I Refactored ---------------------------------------
/-- Euclid I.1, construction of two equilateral triangles -/
theorem iseqtri_iseqtri_diffside_of_ne (ab : a ≠ b) : ∃ c d L, online a L ∧
  online b L ∧ diffside c d L ∧ eq_tri a b c ∧ eq_tri a b d := by
rcases circle_of_ne ab with ⟨α, aα, bα⟩
rcases circle_of_ne (Ne.symm ab) with ⟨β, bβ, aβ⟩
rcases diffside_of_circles_inter aα bβ (circles_inter_of_inside_on_circle bα aβ
  (inside_circle_of_center aα) (inside_circle_of_center bβ)) with
  ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩
have ab_ac := (on_circle_iff_length_eq aα bα).mpr cα
have bc_ba := (on_circle_iff_length_eq bβ cβ).mpr aβ
have ab_ad := (on_circle_iff_length_eq aα bα).mpr dα
have bd_ba := (on_circle_iff_length_eq bβ dβ).mpr aβ
exact ⟨c, d, L, aL, bL, cdL, eq_tri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
  eq_tri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩

/-- Euclid I.1, construction of an equilateral triangle on the sameside of a point -/
theorem iseqtri_sameside_of_ne (ab : a ≠ b) (aL : online a L) (bL : online b L) (dL : ¬online d L):
  ∃ c, ¬online c L ∧ sameside c d L ∧ eq_tri a b c := by
  rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c1, c2, M, aM, bM, c1c2M, eqtri1, eqtri2⟩
  rcases sameside_or_of_diffside' dL (by rwa [line_unique_of_pts ab aM bM aL bL] at c1c2M)
    with c1dL | c2dL
  refine ⟨c1, not_online_of_sameside c1dL, c1dL, eqtri1⟩
  refine ⟨c2, not_online_of_sameside c2dL, c2dL, eqtri2⟩

/-- Euclid I.1, construction of a single equilateral triangle -/
theorem iseqtri_of_ne (ab : a ≠ b) : ∃ c, eq_tri a b c :=
  by rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c, -, -, -, -, -, eqtri, -⟩; exact ⟨c, eqtri⟩

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
theorem length_eq_of_sameside (aL : online a L) (bL : ¬online b L) (aM : ¬online a M)
    (dL : online d L) (dM : online d M) : ∃ e, online e M ∧ diffside e b L ∧
    length e d = length a b := by
  rcases sameside_of_offline aL bL aM dL dM with ⟨f, fM, fbL⟩
  rcases length_eq_B_of_ne_four (ne_of_sameside dL fbL) (ne_of_online aL bL) with ⟨e, Bfde, ab_de⟩
  exact ⟨e, online_3_of_B Bfde fM dM, diffside_of_B_sameside Bfde dL fbL, by perma[ab_de.symm]⟩

/-- Euclid I.2, generalization -/
theorem length_eq_of_sameside' (aL : online a L) (bL : ¬online b L) (aM : ¬online a M)
    (dL : online d L) (dM : online d M) : ∃ e, online e M ∧ sameside e b L ∧
    length e d = length a b := by
  rcases length_eq_of_sameside aL bL aM dL dM with ⟨e, eM, ebL, _⟩
  rcases length_eq_B_of_ne_four (ne_of_online' dL ebL.1) (ne_of_online aL bL) with
    ⟨f, Bedf, ab_df⟩
  exact ⟨f, online_3_of_B Bedf eM dM, by perma[sameside_of_B_diffside Bedf dL ebL],
    by perma[ab_df.symm]⟩

/-- Euclid I.3, Moving a smaller segment on top of a larger one -/
theorem B_length_eq_of_ne_lt (cd : c ≠ d) (cd_lt_ab : length c d < length a b) :
  ∃ f, B a f b ∧ length a f = length c d := by
rcases length_eq_of_ne a cd with ⟨e, ae_cd⟩
rcases circle_of_ne (ne_of_ne_len' cd ae_cd) with ⟨α, aα, eα⟩
rcases B_oncircle_of_inside_outside (inside_circle_of_center aα)
  (out_circle_of_lt aα eα (by rwa [← ae_cd] at cd_lt_ab)) with ⟨f, Bafb, fα⟩
have ae_af := length_eq_of_oncircle aα eα fα
exact ⟨f, Bafb, by linarith⟩

/-- Euclid I.5, (part 1), isosceles triangles have equal angles -/
theorem angle_eq_of_iso (iso_abc : iso_tri a b c) : angle a b c = angle a c b :=
  (sas (iso_abc).2 (iso_abc).2.symm $ by perm).2.2.symm

/-- Euclid I.6, a triangle with equal angles is isosceles -/
theorem iso_of_angle_eq (tri_abc : triangle a b c) (abc_eq_acb : angle a b c = angle a c b) :
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
  rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c, d, L, aL, bL, cdL, eqtri_abc, eqtri_abd⟩
  rcases pt_B_of_diffside cdL with ⟨e, eL, Bced⟩
  have acd_bcd : angle a c d = angle b c d := (sss (len_2143_of_len eqtri_abc.2.2.2) rfl $
    len_2143_of_len eqtri_abd.2.2.2).1
  have ae_be : length a e = length b e := (sas eqtri_abc.2.2.2 rfl $ by
    linarith [ang_654321_of_ang $ angle_extension_of_B (Ne.symm $ ne_13_of_tri eqtri_abc.1) Bced,
    ang_654321_of_ang $ angle_extension_of_B (Ne.symm $ ne_23_of_tri eqtri_abc.1) Bced]).1
  refine ⟨e, B_of_length_eq_col (ne_of_triangle_length_eq
    (tri312 eqtri_abc.1) ae_be) ab ⟨L, aL, eL, bL⟩ ae_be, ae_be⟩

/-- Euclid I.9 lemma, bisecting an angle in an isosceles triangle -/
theorem bisect_angle_iso (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M)
    (iso_abc : iso_tri a b c) : ∃ d, angle b a d = angle c a d ∧ sameside d b M ∧
    sameside d c L := by
  rcases bisect_segment (ne_23_of_tri iso_abc.1) with ⟨d, Bbdc, bd_cd⟩
  have bad_cad : angle b a d = angle c a d := (sss bd_cd rfl $ len_2143_of_len iso_abc.2).2.2
  refine ⟨d, bad_cad, sameside_of_B_online_3 (B_symm Bbdc) cM $ online_2_of_triangle aM cM
    iso_abc.1, sameside_of_B_online_3 Bbdc bL $ online_3_of_triangle aL bL iso_abc.1⟩

/-- Euclid I.9 lemma, bisecting an angle -/
theorem bisect_angle (aL : online a L) (bL : online b L) (aM : online a M) (cM : online c M)
    (tri_abc : triangle a b c) : ∃ f, angle b a f = angle c a f ∧ sameside f b M ∧
    sameside f c L := by
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_abc) (ne_13_of_tri tri_abc) with ⟨d, Babd, ac_bd⟩
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_12_of_tri tri_abc) with ⟨e, Bace, ab_ce⟩
  rcases bisect_angle_iso aL (online_3_of_B Babd aL bL) aM (online_3_of_B Bace aM cM)
    ⟨tri_of_B_B_tri Babd Bace tri_abc, by linarith[length_sum_of_B Babd, length_sum_of_B Bace]⟩
    with ⟨f, daf_eaf, fdM, feL⟩
  refine ⟨f, by linarith[angle_extension_of_B (ne_of_sameside' aL feL) Babd,
    angle_extension_of_B (ne_of_sameside' aL feL) Bace], sameside_trans (sameside_symm fdM) $
    sameside_symm $ sameside_of_B_not_online_2 Babd aM (online_2_of_triangle aM cM tri_abc),
    sameside_trans (sameside_symm feL) $ sameside_symm $ sameside_of_B_not_online_2 Bace aL
    (online_3_of_triangle aL bL tri_abc)⟩

/-- Euclid I.11, Obtaining perpendicular angles from a point on a line -/
theorem perpendicular_of_online (Babc : B a b c) (aL : online a L) (bL : online b L)
    (fL : ¬online f L) :
    ∃ e, sameside e f L ∧ angle e b a = rightangle ∧ angle e b c = rightangle := by
  rcases length_eq_B_of_ne (ne_12_of_B Babc) (ne_21_of_B Babc) with ⟨d, Babd, ba_bd⟩
  rcases iseqtri_sameside_of_ne (ne_13_of_B Babd) aL (online_3_of_B Babd aL bL) fL
    with ⟨e, eL, efL, eqtri⟩
  have eba_ebd : angle e b a = angle e b d := (sss rfl eqtri.2.2.2 ba_bd).2.1
  have rightangles : angle e b a = rightangle ∧ angle e b c = rightangle :=
    rightangle_of_angle_eq Babc aL (online_3_of_B Babc aL bL) eL $ eba_ebd.trans
    $ angle_extension_of_B_B (ne_of_online bL eL) Babc Babd
  refine ⟨e, efL, rightangles⟩

/-- Euclid I.11, Obtaining a perpendicular angle from a point on a line -/
theorem perpendicular_of_online' (ab : a ≠ b) (aL : online a L) (bL : online b L)
    (fL : ¬online f L) : ∃ c, sameside c f L ∧ angle a b c = rightangle := by
  rcases length_eq_B_of_ne ab ab.symm with ⟨d, Babd, _⟩
  rcases perpendicular_of_online Babd aL bL fL with ⟨c, cfL, right, _⟩
  exact ⟨c, cfL, by perma[right]⟩

/-- Euclid I.12, Obtaining perpendicular angles from a point off a line -/
theorem perpendicular_of_not_online (aL : ¬online a L) : ∃ c d e, B c e d ∧ online c L ∧ online d L
    ∧ online e L ∧ angle a e c = rightangle ∧ angle a e d = rightangle := by
  rcases diffside_of_not_online' aL with ⟨b, abL⟩
  rcases circle_of_ne (ne_of_diffside abL) with ⟨α, aα, bα⟩
  rcases pts_line_circle_of_not_sameside aα bα abL.2.2 with ⟨c, d, cd, cL, dL, cα, dα⟩
  rcases bisect_segment cd with ⟨e, Bced, ce_de⟩
  have aec_aed : angle a e c = angle a e d := (sss (length_eq_of_oncircle aα cα dα) ce_de rfl).2.2
  have rightangles : angle a e c = rightangle ∧ angle a e d = rightangle :=
    rightangle_of_angle_eq Bced cL dL aL aec_aed
  refine ⟨c, d, e, Bced, cL, dL, online_2_of_B Bced cL dL, rightangles⟩

/-- Euclid I.13, A generalization of I.11. Instead of requiring the angles to be perpendicular,
  they can be arbitrary -/
theorem two_right_of_flat_angle (Babc : B a b c) (aL : online a L) (bL : online b L)
    (dL : ¬online d L) : angle d b a + angle d b c = 2 * rightangle := by
  rcases line_of_pts b d with ⟨N, bN, dN⟩
  rcases perpendicular_of_online Babc aL bL dL with ⟨e, edL, eba_ra, ebc_ra⟩
  rcases line_of_pts e b with ⟨M, eM, bM⟩
  by_cases dM : online d M; linarith[angle_extension_of_sameside (ne_12_of_B Babc) bL
    ⟨M, bM, eM, dM⟩ edL, angle_extension_of_sameside (ne_32_of_B Babc) bL ⟨M, bM, eM, dM⟩ edL]
  wlog cdM : sameside c d M generalizing a c; linarith[this (B_symm Babc) (online_3_of_B Babc aL
    bL) ebc_ra eba_ra $ sameside_of_B_diffside_sameside Babc aL bL bM eM dM edL cdM]
  have ebc_add : angle d b c = angle e b c - angle d b e :=
    by linarith[angle_add_of_sameside bM eM bL (online_3_of_B Babc aL bL) cdM edL]
  have dba_add : angle d b a = angle e b d + angle e b a := angle_add_of_sameside bN dN bL aL
    (sameside_of_B_sameside_sameside Babc bL bM bN aL eM dN edL cdM) (sameside_symm edL)
  linperm

/-- Euclid I.14, the converse of I.13. If angles add to two right angles then you have betweeness-/
theorem flat_of_two_right_angle (bd : b ≠ d) (bL : online b L) (dL : online d L)
    (acL : diffside a c L) (two_ra : angle d b a + angle d b c = 2 * rightangle) : B a b c := by
  rcases line_of_pts a b with ⟨N, aN, bN⟩
  rcases length_eq_B_of_ne (ne_of_online' bL acL.1) bd with ⟨e, Babe, -⟩
  have : angle d b a + angle d b e = 2 * rightangle := two_right_of_flat_angle Babe aN bN $
    offline_of_online_offline bd aN bN bL dL acL.1
  have ebc_0 : angle e b c = 0 := angle_zero_of_lt_eq bd bL dL
    (sameside_of_B_diffside Babe bL acL) (by linarith)
  have cN := online_of_angle_zero (ne_23_of_B Babe) (ne_of_online bL acL.2.1)
      bN (online_3_of_B Babe aN bN) ebc_0
  exact B_of_col_diffside ⟨N, aN, bN, cN.1⟩ bL acL

/-- Euclid I.15, vertical angles are equal-/
theorem vertical_angle (Babc : B a b c) (Bdbe : B d b e) (aL : online a L) (bL : online b L)
    (dL : ¬online d L) : angle a b d = angle c b e := by
  rcases line_of_pts d b with ⟨M, dM, bM⟩
  have dba_dbc : angle d b a + angle d b c = 2 * rightangle := two_right_of_flat_angle Babc aL bL dL
  have cbd_cbe : angle c b d + angle c b e = 2 * rightangle := two_right_of_flat_angle Bdbe dM bM $
    offline_of_online_offline (ne_23_of_B Babc) dM bM bL (online_3_of_B Babc aL bL) dL
  linperm

/-- Euclid I.15, vertical angles are equal-/
theorem vertical_angle' (Babc : B a b c) (Bdbe : B d b e) (col_abd : ¬colinear a b d) :
    angle a b d = angle c b e := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact vertical_angle Babc Bdbe aL bL $ online_3_of_triangle aL bL col_abd

/-- Euclid I.16, external angles are greater than interior angles-/
theorem internal_lt_external (Babc : B a b c) (tri_abd : triangle a b d) :
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
    (sameside_of_B_B Babc Baef bL eL $ online_1_of_triangle bL dL tri_abd) $ sameside_of_B_online_3
    Baef aM $ offline_of_B_B_tri Baef Bbed aM bM tri_abd
  linperm[zero_lt_angle_of_offline (ne_23_of_B Babc) bM cM $ offline_of_B_B_tri Baef Bbed aM bM
    tri_abd, angle_extension_of_B (ne_23_of_B Babc) Bbed, angle_extension_of_B (ne_31_of_tri
    tri_abd) (B_symm Bbed)]

/-- Euclid I.16, external angles are greater than interior angles-/
theorem internal_lt_external' (Babc : B a b c) (tri_abd : triangle a b d) :
    angle b a d < angle d b c := by
  rcases length_eq_B_of_ne (ne_32_of_tri tri_abd) (ne_23_of_tri tri_abd) with ⟨e, Bdbe, -⟩
  have : angle b a d < angle a b e := internal_lt_external Bdbe (by perma)
  have : angle e b a = angle d b c := vertical_angle' (B_symm Bdbe) Babc $ tri213 $
    tri_143_of_tri_col (ne_23_of_B Bdbe) (by perma) $ col_213_of_col $ col_of_B Bdbe
  linperm

/-- Euclid I.18, Opposite larger sides you have larger angles in a triangle-/
theorem ang_lt_of_len_lt (tri_abc : triangle a b c) (len_lt : length c a < length c b) :
    angle c b a < angle c a b := by
  rcases B_length_eq_of_ne_lt (ne_31_of_tri tri_abc) len_lt with ⟨d, Bcdb, cd_ca⟩
  have : angle d b a < angle a d c := internal_lt_external' (B_symm Bcdb) $ tri321 $ tri_of_B_tri
    Bcdb $ tri132_of_tri123 tri_abc
  have : angle c a d = angle c d a := angle_eq_of_iso ⟨tri312 $ tri_of_B_tri (B_symm Bcdb) tri_abc,
    cd_ca.symm⟩
  have : angle c a d < angle c a b := angle_lt_of_B_tri Bcdb tri_abc
  linarith[angle_extension_of_B (ne_21_of_tri tri_abc) $ B_symm Bcdb, angle_symm c d a]

/--Euclid I.19, larger angles correspond to larger opposide sides in a triangle-/
theorem len_lt_of_ang_lt (tri_abc : triangle a b c) (ang_lt : angle c b a < angle c a b) :
    length c a < length c b := by
  push_contra cb_le_ca at cb_le_ca
  by_cases cb_ca : length c b = length c a
  · linarith[angle_eq_of_iso ⟨by perma, cb_ca.symm⟩]
  linarith[ang_lt_of_len_lt (by perma) $ lt_of_le_of_ne cb_le_ca cb_ca]

/--Euclid I.20, a triangle inequality-/
theorem len_lt_of_tri' (tri_abc : triangle a b c) : length a b < length a c + length b c := by
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_23_of_tri tri_abc) with ⟨d, Bacd, bc_cd⟩
  have : angle d b c < angle d b a := angle_lt_of_B_tri (B_symm Bacd) $ tri312 $ tri_143_of_tri_col
    (ne_13_of_B Bacd) (by perma) $ col_of_B Bacd
  have : angle c d b = angle c b d := angle_eq_of_iso ⟨tri_143_of_tri_col (ne_23_of_B Bacd)
    (by perma) $ col_213_of_col $ col_of_B Bacd, len_43_of_len bc_cd.symm⟩
  have : length a b < length a d := len_lt_of_ang_lt (tri321 $ tri_143_of_tri_col (ne_13_of_B Bacd)
    (tri132_of_tri123 tri_abc) $ col_of_B Bacd) $
    by linarith[angle_symm c b d, angle_symm d b a, angle_extension_of_B (ne_of_col_tri'
    (col_132_of_col $ col_of_B Bacd) $ tri213 tri_abc) $ B_symm Bacd]
  have : length a c + length c d = length a d := length_sum_of_B Bacd
  linarith

/--Euclid I.20, the triangle inequalities-/
theorem len_lt_of_tri (tri_abc : triangle a b c) : length a b < length a c + length b c ∧
    length b c < length b a + length c a ∧ length c a < length c b + length a b :=
  ⟨len_lt_of_tri' tri_abc, len_lt_of_tri' $ by perma, len_lt_of_tri' $ by perma⟩

/--Euclid I.22, making a triangle with prescribed lengths-/
theorem triangle_of_ineq (aL : online a L) (bL : online b L) (fL : ¬online f L)
    (ab_lt_a1a2_b1b2 : length a b < length a1 a2 + length b1 b2)
    (a1a2_lt_ab_b1b2 : length a1 a2 < length a b + length b1 b2)
    (b1b2_lt_a1a2_ab : length b1 b2 < length a1 a2 + length a b) :
    ∃ e, length a e = length a1 a2 ∧ length b e = length b1 b2 ∧ sameside e f L := by
  rcases length_eq_B_of_ne_four (Ne.symm (fun n => by linarith[length_zero_of_eq n] : a ≠ b))
    ((fun n => by linarith[length_zero_of_eq n] : a1 ≠ a2)) with ⟨c, Bbac, a1a2_ac⟩
  rcases length_eq_B_of_ne_four (fun n => by linarith[length_zero_of_eq n] : a ≠ b)
    ((fun n => by linarith[length_zero_of_eq n] : b1 ≠ b2)) with ⟨d, Babd, b1b2_bd⟩
  rcases circle_of_ne $ ne_23_of_B Bbac with ⟨α, aα, cα⟩
  rcases circle_of_ne $ ne_23_of_B Babd with ⟨β, bβ, dβ⟩
  rcases pt_sameside_of_circles_inter aL bL fL aα bβ $ circint_of_lt_lt aα bβ cα dβ
    (by apply abs_lt.mpr; exact ⟨by linarith, by linarith⟩) $ by linarith with ⟨e, efL, eα, eβ⟩
  have : length a c = length a e := length_eq_of_oncircle aα cα eα
  have : length b d = length b e := length_eq_of_oncircle bβ dβ eβ
  exact ⟨e, by linarith, by linarith, efL⟩

/--Euclid I.23, copying an angle-/
theorem angle_copy (ab : a ≠ b) (aL : online a L) (bL : online b L) (jL : ¬online j L)
    (tri_cde : triangle c d e) : ∃ h, angle h a b = angle e c d ∧ sameside h j L := by
  rcases length_eq_B_of_ne_four ab (ne_12_of_tri tri_cde) with ⟨g, Babg, cd_bg⟩
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_cde) ab with ⟨f, Bcdf, ab_df⟩
  have cf_ag : length c f = length a g := by linarith[length_sum_of_B Babg, length_sum_of_B Bcdf]
  have ⟨cf_lt_ce_ef, _, _⟩ := len_lt_of_tri $ tri_143_of_tri_col (ne_13_of_B
    Bcdf) tri_cde $ col_of_B Bcdf; perm only [length] at *
  rcases triangle_of_ineq aL (online_3_of_B Babg aL bL) jL (by rwa [cf_ag] at cf_lt_ce_ef) (by
    linarith) $ by linarith with ⟨h, ah_ce, gh_ef, hjL⟩
  have : angle h a g = angle e c f := (sss ah_ce (len_21_of_len gh_ef) cf_ag.symm).2.1
  exact ⟨h, by linarith[angle_extension_of_B' (ne_of_sameside' aL hjL) Babg, angle_extension_of_B'
                (ne_13_of_tri tri_cde) Bcdf], hjL⟩

/--Euclid I.23, copying an angle-/
theorem angle_copy' (ab : a ≠ b) (aL : online a L) (bL : online b L) (jL : ¬online j L)
    (tri_cde : triangle c d e) : ∃ h, angle h a b = angle e c d ∧ diffside h j L := by
  rcases diffside_of_not_online jL with ⟨f, fL, jfL⟩
  rcases angle_copy ab aL bL fL tri_cde with ⟨h, hab_ecd, hfL⟩
  refine ⟨h, hab_ecd, diffside_of_sameside_diffside (sameside_symm hfL) $ diffside_symm
    ⟨jL, fL, jfL⟩⟩

/--Euclid I.26, if two triangles have two corresponding angles equal and the included sides equal,
   then they are congruent-/
theorem asa' (tri_abc : triangle a b c) (tri_def : triangle d e f) (ab_de : length a b = length d e)
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

/--Euclid I.26, if two triangles have two corresponding angles equal and the included sides equal,
   then they are congruent-/
theorem asa (tri_abc : triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  asa' tri_abc (triangle_of_asa tri_abc ab_de bac_edf abc_def) ab_de bac_edf abc_def

/--Euclid I.26, if two triangles have two corresponding angles equal and a non-included side equal,
   then they are congruent-/
theorem saa' (tri_abc : triangle a b c) (tri_def : triangle d e f) (ac_df : length a c =
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

/--Euclid I.26, if two triangles have two corresponding angles equal and a non-included side equal,
   then they are congruent-/
theorem saa (de : d ≠ e) (tri_abc : triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a b = length d e ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  saa' tri_abc (triangle_of_saa de tri_abc ac_df bac_edf abc_def) ac_df bac_edf abc_def

/--Euclid I.27, if the alternate angles are equal, then the lines it formed from are parallel-/
theorem para_of_ang_eq (bc : b ≠ c) (aM : online a M) (bM : online b M) (bL : online b L)
    (cL : online c L) (cN : online c N) (dN : online d N) (adL : diffside a d L)
    (cba_bcd : angle c b a = angle b c d) : para M N := by
  intro e; push_contra eMN at eMN
  wlog aeL : sameside a e L generalizing a b c d e M N; exact this bc.symm dN cN cL bL bM aM (by
    perma) (by linperm) e (by tauto) $ sameside_of_diffside_diffside adL ⟨adL.1,
    offline_of_online_inter bc aM bM bL cL cN dN adL.1 adL.2.1 eMN.1 eMN.2, aeL⟩
  have : angle c b e < angle b c d := internal_lt_external (B_of_col_diffside ⟨N, eMN.2, cN, dN⟩ cL
    $ diffside_of_sameside_diffside aeL adL) $ by perma[triangle_of_ne_online bc bL cL $
                not_online_of_sameside $ sameside_symm aeL]
  linperm[angle_extension_of_sameside bc.symm bL ⟨M, bM, aM, eMN.1⟩ aeL]

/--Euclid I.29, basic properties of alternate, exterior, and interior angles with parallel lines-/
theorem alternate_eq_of_para (aM : online a M) (bM : online b M) (bL : online b L)
    (cL : online c L) (cN : online c N) (dN : online d N) (adL : diffside a d L)
    (paraMN : para M N) : angle a b c = angle b c d := by
  wlog bcd_lt_abc : angle b c d < angle a b c generalizing a b c d M N; by_cases angle a b c =
    angle b c d; exact h; push_neg at bcd_lt_abc; linperm[this dN cN cL bL bM aM (by perma)
    (para_symm paraMN) $ by linperm[lt_of_le_of_ne bcd_lt_abc h]]
  rcases length_eq_B_of_ne (ne_of_online' bL adL.1) (ne_of_online bL adL.1) with ⟨e, Babe, -⟩
  have : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_para' cN paraMN
  have : angle c b e + angle b c d < 2 * rightangle := by perm at *; linarith
  rcases unparallel_postulate (ne_of_para bM cN paraMN) (online_3_of_B Babe aM bM) bM bL cL cN dN
    (sameside_symm $ sameside_of_B_diffside Babe bL adL) (by perma) with ⟨f, fM, fN, -⟩
  exfalso; exact not_para_of_inter fM fN paraMN

/--Euclid I.29, basic properties of alternate, exterior, and interior angles with parallel lines-/
theorem interior_rightangles_of_para (aM : online a M) (bM : online b M) (bL : online b L)
    (cL : online c L) (cN : online c N) (dN : online d N) (adL : sameside a d L)
    (paraMN : para M N) : angle a b c + angle b c d = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_of_sameside bL adL) (ne_of_sameside' bL adL) with ⟨e, Babe, -⟩
  have ras : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_para' cN paraMN
  have : angle e b c = angle b c d := alternate_eq_of_para (online_3_of_B Babe aM bM) bM bL cL
    cN dN (diffside_of_B_sameside Babe bL adL) paraMN
  perm at *; linarith

/--Euclid I.29, corresponding angles are equal-/
theorem correspond_of_para (Babc : B a b c) (aL : online a L) (bL : online b L) (bM : online b M)
    (dM : online d M) (cN : online c N) (eN : online e N) (deL : sameside d e L)
    (paraMN : para M N) : angle a b d = angle b c e := by
  have : angle a b d + angle d b c = 2 * rightangle :=
    by perma[two_right_of_flat_angle Babc aL bL (not_online_of_sameside deL)]
  have : angle d b c + angle b c e = 2 * rightangle :=
    interior_rightangles_of_para dM bM bL (online_3_of_B Babc aL bL) cN eN deL paraMN
  linarith

theorem right_of_para_right (aM : online a M) (bM : online b M) (bL : online b L) (cL : online c L)
    (cN : online c N) (dN : online d N) (aL : ¬online a L) (dL : ¬online d L)
    (bcd : angle b c d = rightangle) (paraMN : para M N) : angle a b c = rightangle := by
  by_cases adL : sameside a d L
  linperm[interior_rightangles_of_para aM bM bL cL cN dN adL paraMN]
  linperm[alternate_eq_of_para aM bM bL cL cN dN ⟨aL, dL, adL⟩ paraMN]

/--Euclid I.30, transitivity of parallel lines-/
theorem para_trans (MN : M ≠ N) (paraLM : para L M) (paraLN : para L N) : para M N := by
  intro x; push_contra int at int
  rcases perpendicular_of_not_online (offline_of_para' int.1 paraLM)
    with ⟨c, d, y, Bcyd, cL, dL, yL, xyc, xyd⟩
  rcases line_of_pts x y with ⟨O, xO, yO⟩
  rcases online_ne_of_point_line x M with ⟨a, xa, aM⟩
  rcases sameside_of_offline yO (offline_of_online_offline xa yO xO int.1 aM
    $ offline_of_para yL paraLM) (offline_of_para yL paraLN) xO int.2 with ⟨b, bN, baO⟩
  wlog yaN : sameside y a N generalizing x y a b c d N M O; exact this MN.symm paraLN paraLM x
    ⟨int.2, int.1⟩ c d y Bcyd cL dL yL xyc xyd O xO yO b (ne_of_sameside xO baO).symm bN a aM
    (by perma[baO]) $ sameside_of_sameside_diffside xO int.2 int.1 yO bN aM baO ⟨offline_of_para
    yL paraLN, offline_of_online_offline xa bN int.2 int.1 aM $ online_of_ne_ne
    (ne_of_sameside xO baO) MN.symm bN int.2 int.1, yaN⟩
  have split := angle_add_of_sameside int.2 bN xO yO yaN baO
  have axy := right_of_para_right aM int.1 xO yO yL cL (not_online_of_sameside $ sameside_symm baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_para' int.1 paraLM)) xyc
    (para_symm paraLM)
  have bxy := right_of_para_right bN int.2 xO yO yL cL (not_online_of_sameside baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_para' int.1 paraLM)) xyc
    (para_symm paraLN)
  linarith[zero_lt_angle_of_tri $ triangle_of_ne_online (ne_of_sameside xO baO).symm int.2 bN
    (not_online_of_sameside $ sameside_symm yaN)]

/--Euclid I.31, through a point off a line there exists a parallel line-/
theorem para_of_offline (aM : ¬online a M) : ∃ N, online a N ∧ para M N := by
  rcases online_ne_of_line M with ⟨b, c, bc, bM, cM⟩
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases angle_copy' (ne_of_online' bM aM) aL bL (offline_of_online_offline bc aL bL bM cM aM)
    (triangle_of_ne_online bc bM cM aM) with ⟨d, bad_abc, cdL⟩; perm at *
  rcases line_of_pts a d with ⟨N, aN, dN⟩
  refine ⟨N, aN, para_of_ang_eq (ne_of_online bM aM) cM bM bL aL aN dN cdL bad_abc.symm⟩

/--Euclid I.32, the exterior angle equals the sum of the other two angles and the sum of all three
  interior angles adds to two right angles-/
theorem ext_int_sum_of_tri (Bbcd : B b c d) (tri_abc : triangle a b c) : angle a c d = angle b a c +
    angle a b c ∧ angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  rcases line_of_pts c d with ⟨O, cO, dO⟩
  rcases para_of_offline (online_3_of_triangle aL bL tri_abc) with ⟨M, cM, paraLM⟩
  rcases length_eq_of_sameside aN (online_2_of_triangle aN cN tri_abc) (offline_of_para aL paraLM)
    cN cM with ⟨e, eM, ebN, _⟩
  have bac_ace := alternate_eq_of_para bL aL aN cN cM eM (by perma[ebN]) paraLM
  have dce_cba := correspond_of_para (B_symm Bbcd) dO cO cM eM bL aL (sameside_of_sameside_diffside
    cM cN cO eM aN (online_3_of_B (B_symm Bbcd) dO cO) (sameside_of_para_online aL bL paraLM) ebN)
    (by perma[paraLM])
  have acd_split := angle_add_of_sameside cN aN cO dO
    (by perma[sameside_of_B_diffside Bbcd cN (by perma[ebN])]) (by perma
    [(sameside_of_sameside_diffside cM cN cO eM aN (online_3_of_B (B_symm Bbcd) dO cO)
    (sameside_of_para_online aL bL paraLM) ebN)])
  have flat_sum := two_right_of_flat_angle Bbcd (online_3_of_B (B_symm Bbcd) dO cO) cO
    (online_1_of_triangle (online_3_of_B (B_symm Bbcd) dO cO) cO tri_abc)
  exact ⟨by linperm, by linperm⟩

theorem sum_two_right_of_tri (tri_abc : triangle a b c) :
    angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_23_of_tri tri_abc) (ne_32_of_tri tri_abc) with ⟨d, Bbcd, _⟩
  exact (ext_int_sum_of_tri Bbcd tri_abc).2

/-- Euclid I.33, parallel lines with pair of points with same length make a parallelogram -/
theorem pgram_of_para_len_eq (aL : online a L) (bL : online b L) (bO : online b O)
    (dO : online d O) (dM : online d M) (cM : online c M) (cN : online c N) (aN : online a N)
    (bP : online b P) (cP : online c P) (aPd : diffside a d P) (paraLM : para L M)
    (ab_cd : length a b = length c d) : paragram a b d c L O M N := by
  have abc_bcd := alternate_eq_of_para aL bL bP cP cM dM aPd paraLM
  obtain ⟨-, -, bca_cbd⟩ := sas (by perma : length b a = length c d) (length_symm b c) (by perma)
  exact ⟨aL, bL, bO, dO, dM, cM, cN, aN, paraLM, para_symm $
    para_of_ang_eq (ne_of_para' bL cM paraLM) aN cN cP bP bO dO aPd bca_cbd⟩

/--Euclid I.34, basic length, angle, and area properties of paralellograms-/
theorem len_ang_area_eq_of_parallelogram (pgram : paragram a b c d M N O P) :
    length a b = length c d ∧ angle b a d = angle b c d ∧ area a b d = area b c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, paraMO, paraNP⟩ := pgram
  rcases line_of_pts b d with ⟨L, bL, dL⟩
  have abd_bdc : angle a b d = angle b d c := alternate_eq_of_para aM bM bL dL
    dO cO (diffside_of_paragram bL dL pgram) paraMO
  have adb_dbc : angle a d b = angle d b c := alternate_eq_of_para aP dP dL bL bN cN
    (diffside_of_paragram bL dL pgram) $ para_symm paraNP; perm at adb_dbc
  have ⟨ba_dc, da_bc, bad_dcb⟩ := asa (by perma[tri124_of_paragram pgram])
    (length_symm b d) (by perma : angle d b a = angle b d c) (by perma)
  have : area b a d = area d c b := area_eq_of_SSS ba_dc (length_symm b d) (by linperm[da_bc])
  perm at *; exact ⟨ba_dc, bad_dcb, this⟩

/--Euclid I.34, basic length properties of paralellograms-/
theorem len_eq_of_parallelogram (pgram : paragram a b c d M N O P) :
    length a b = length c d := (len_ang_area_eq_of_parallelogram pgram).1

/--Euclid I.34, basic length properties of paralellograms-/
theorem len_eq_of_parallelogram' (pgram : paragram a b c d M N O P) :
    length a d = length c b := by
    have ⟨aM, bM, bN, cN, cO, dO, dP, aP, paraMO, paraNP⟩ := pgram; exact len_eq_of_parallelogram
      ⟨aP, dP, dO, cO, cN, bN, bM, aM, para_symm paraNP, para_symm paraMO⟩

/--Euclid I.34, basic area properties of paralellograms-/
theorem area_eq_of_parallelogram (pgram : paragram a b c d M N O P) :
    area a b d = area b c d := (len_ang_area_eq_of_parallelogram pgram).2.2

lemma B_sameside_of_2_paragram (Badf : B a d f) (pgram1 : paragram a d c b L M N O)
    (pgram2 : paragram e f c b L P N Q) : B f e a ∧ sameside d e P := by
  have ad_cb := len_eq_of_parallelogram pgram1; have ef_cb := len_eq_of_parallelogram pgram2
  rcases B_or_B_of_sameside (fun ae => by rw [←ae] at ef_cb; linarith[length_sum_perm_of_B Badf])
    pgram2.2.2.1 ⟨L, pgram2.2.1, pgram1.1, pgram2.1⟩ $ sameside_of_B_prgram_pgram_trans' Badf
    pgram1 pgram2 with Bet | Bet
  linarith[length_sum_perm_of_B Bet, length_sum_perm_of_B Badf]
  exact ⟨Bet, sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2⟩

/--Euclid I.35, parallelograms sharing two parallels have the same area-/
theorem area_eq_of_paragram (pgram1 : paragram a d c b L M N O) (pgram2 : paragram e f c b L P N Q):
    area a d b + area d b c = area e f b + area f b c := by
  wlog Badf : B a d f generalizing a b c d e f L M N O P Q; by_cases df : d = f; rw [←df] at pgram2
    ⊢; linperm [(len_ang_area_eq_of_parallelogram pgram1).2.2, (len_ang_area_eq_of_parallelogram
    pgram2).2.2]; exact (this pgram2 pgram1 $ B_of_B_2_paragram df Badf pgram1 pgram2).symm
  have ⟨Bfea, deP⟩ := B_sameside_of_2_paragram Badf pgram1 pgram2
  have ⟨aL, dL, dM, cM, cN, bN, bO, aO, paraLN, paraMO⟩ := pgram1
  have ⟨eL, fL, fP, cP, _, _, bQ, eQ, _, paraPQ⟩ := pgram2
  have fdc_dab := correspond_of_para (B_symm Badf) fL dL dM cM aO bO
    (sameside_of_para_online' cN bN paraLN) paraMO
  have aeb_efc := correspond_of_para (B_symm Bfea) aL eL eQ bQ fP cP
    (sameside_of_para_online' bN cN paraLN) $ para_symm paraPQ
  have dc_ab : length d c = length a b := by linperm[len_eq_of_parallelogram' pgram1]
  have ae_df := (saa (ne_32_of_B Bfea) (tri_of_sameside (ne_of_para fL cN paraLN) fP cP deP) dc_ab
    (fdc_dab.trans (angle_extension_of_sameside (ne_of_para' aL bN paraLN) aO ⟨L, aL, dL, eL⟩ $
    by perma[(B_sameside_of_2_paragram Bfea ⟨fL, eL, eQ, bQ, bN, cN, cP, fP, paraLN, para_symm
    paraPQ⟩ ⟨dL, aL, aO, bO, bN, cN, cM, dM, paraLN, para_symm paraMO⟩).2])) (aeb_efc.trans $
    angle_extension_of_sameside (ne_of_para' fL cN paraLN) fP ⟨L, fL, eL, dL⟩ $ by
    perma[deP]).symm).1.symm
  have ab_cd := len_eq_of_parallelogram' pgram1; have eb_cf := len_eq_of_parallelogram' pgram2
  have aeb_dfc := area_eq_of_SSS ae_df (by perma : length a b = length d c) $ by perma[eb_cf]
  have ar1 := paragram_area_comm pgram1
  have ar2 := quad_area_comm aL fL fP cP cN bN (sameside_of_para_online aL fL paraLN)
    (sameside_of_para_online' cN bN paraLN) $ sameside_of_B_para Bfea fP eQ bQ paraPQ
  have ar3 := area_add_of_B_offline Badf aL fL $ offline_of_para' cN paraLN
  have ar4 := area_add_of_B_offline Bfea fL aL $ offline_of_para' bN paraLN
  linperm

/--Proof of the construction of the parallelogram from the triangle in I.37, used twice so worth
    having as its own lemma-/
lemma paragram_of_tri_para (bc : b ≠ c) (bM : online b M) (cM : online c M) (aN : online a N)
    (paraMN : para M N) : ∃ d L O, paragram d a c b N L M O := by
  rcases line_of_pts a c with ⟨L, aL, cL⟩
  rcases line_of_pts a b with ⟨P, aP, bP⟩
  rcases length_eq_of_sameside bP (online_3_of_triangle aP bP
    (by perma[triangle_of_ne_online bc bM cM $ offline_of_para' aN paraMN]))
    (offline_of_para bM paraMN) aP aN with ⟨d, dN, dcP, da_bc⟩
  rcases line_of_pts d b with ⟨O, dO, bO⟩
  exact ⟨d, L, O, pgram_of_para_len_eq dN aN aL cL cM bM bO dO aP bP dcP (by perma) da_bc⟩

/--Euclid I.37, triangles sharing two parallels have the same area-/
theorem area_eq_of_tri (aL : online a L) (dL : online d L) (bM : online b M) (cM : online c M)
    (paraLM : para L M) : area a b c = area d b c := by
  by_cases bc : b = c; rw [bc]; linperm[degenerate_area c a, degenerate_area c d]
  rcases paragram_of_tri_para bc bM cM aL (by perma[paraLM]) with ⟨e, N, O, pgram1⟩
  rcases paragram_of_tri_para bc bM cM dL (by perma[paraLM]) with ⟨f, P, Q, pgram2⟩
  have pgram_eq := area_eq_of_paragram pgram1 pgram2
  have half_pgram1 := area_eq_of_parallelogram pgram1
  have half_pgram2 := area_eq_of_parallelogram pgram2
  linperm

/--Euclid I.41, if a parallelogram shares the same parallels as a
  triangle and the same base, then the parallelogram has twice the area of the triangle-/
theorem twice_pgram_of_tri  (eL : online e L) (pgram : paragram a b c d L M N O) :
    area a b d + area b c d = 2 * area c d e := by
  have ⟨_, _, _, _, cN, dN, _, _, paraLM, _⟩ := pgram
  have pgram_eq := area_eq_of_parallelogram pgram
  have tri_eq := area_eq_of_tri pgram.2.1 eL cN dN paraLM
  linperm

/--Euclid I.46, constructing a square out of a segment-/
theorem square_of_len (ab : a ≠ b) (aL : online a L) (bL : online b L) (fL : ¬online f L) :
    ∃ c d M N O, paragram a c d b N M O L ∧ square a c d b ∧ diffside c f L := by
  rcases perpendicular_of_online' ab.symm bL aL fL with ⟨e, efL, bae⟩
  rcases length_eq_B_of_ne (ne_of_sameside aL efL) ab with ⟨c, Beac, ab_ac⟩
  rcases para_of_offline $ online_of_B_online' (B_symm Beac) aL $ not_online_of_sameside efL
    with ⟨M, cM, paraLM⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  rcases length_eq_of_sameside' aN (offline_of_ne_online_offline ab aL bL aN cN $
    offline_of_para' cM paraLM) (offline_of_para aL paraLM) cN cM with ⟨d, dM, dbN, dc_ab⟩
  rcases line_of_pts b d with ⟨O, bO, dO⟩
  rcases line_of_pts b c with ⟨P, bP, cP⟩
  have abc_bcd := alternate_eq_of_para aL bL bP cP cM dM
    (by perma[diffside_of_sameside_sameside cM cP cN dM bP aN (sameside_of_para_online aL bL
    paraLM) dbN]) paraLM
  have ⟨ac_db, bac_cdb, bca_cbd⟩ := sas (by linperm : length b a = length c d)
    (length_symm b c) $ by perma[abc_bcd]
  have bac := two_right_of_flat_angle Beac (online_3_of_B (B_symm Beac) cN aN) aN $
    offline_of_ne_online_offline ab aL bL aN cN $ offline_of_para' cM paraLM
  have acd := correspond_of_para Beac (online_3_of_B (B_symm Beac) cN aN) aN aL bL cM dM
    (by perma[dbN]) paraLM
  have bdc := interior_rightangles_of_para aL bL bO dO dM cM
    (sameside_of_sameside_diffside bL bP bO aL cP dO (sameside_of_para_online' cM dM paraLM) $
    by perma[diffside_of_sameside_sameside cM cP cN dM bP aN
        (sameside_of_para_online aL bL paraLM) dbN]) paraLM
  refine ⟨c, d, M, N, O, ⟨aN, cN, cM, dM, dO, bO, bL, aL, para_of_ang_eq (ne_of_para' bL cM paraLM)
    aN cN cP bP bO dO
    (by perma[diffside_of_sameside_sameside cM cP cN dM bP aN (sameside_of_para_online
    aL bL paraLM) dbN]) bca_cbd, para_symm paraLM⟩, by splitAll; repeat linperm,
    diffside_of_B_sameside Beac aL efL⟩

lemma right_of_online_right (bd : b ≠ d) (tri_abc : triangle a b c) (bL : online b L) (cL :
    online c L) (dL : online d L) (abd : angle a b d = rightangle) : angle a b c = rightangle := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩
  by_cases cdM : sameside c d M;
    linperm[angle_extension_of_sameside (ne_12_of_tri tri_abc) bM ⟨L, bL, cL, dL⟩ cdM]
  linperm[two_right_of_flat_angle (B_of_col_diffside ⟨L, cL, bL, dL⟩ bM ⟨online_3_of_triangle aM
    bM tri_abc, offline_of_online_offline bd aM bM bL dL $ online_1_of_triangle bL cL tri_abc,
    cdM⟩) cL bL (online_1_of_triangle bL cL tri_abc)]

lemma ne_of_perp_ineq (Bxdy : B x d y) (tri_abc : triangle a b c) (bL : online b L)
    (cL : online c L) (xL : online x L) (cab_le_ra : rightangle ≤ angle c a b)
    (ady : angle a d y = rightangle) : b ≠ d := by
  intro bd; rw[←bd] at Bxdy ady
  linperm[right_of_online_right (ne_23_of_B Bxdy) tri_abc bL cL (online_3_of_B Bxdy xL bL) ady,
    sum_two_right_of_tri tri_abc, (zero_lt_angle_of_tri (by perma[tri_abc]) : 0 < angle b c a)]

lemma not_B_of_right_le_right (tri_abc : triangle a b c) (col_bcd : colinear b c d)
    (adb : angle a d b = rightangle) (cab_le_ra : rightangle ≤ angle c a b) : ¬B d b c := by
  intro Bdbc; rcases col_bcd with ⟨L, bL, cL, dL⟩
  have split := angle_add_of_B Bdbc dL bL (online_1_of_triangle bL cL tri_abc)
  have sum_three := sum_two_right_of_tri (triangle_of_ne_online (ne_13_of_B Bdbc) dL cL
    (online_1_of_triangle bL cL tri_abc))
  linperm[angle_nonneg b a d, (zero_lt_angle_of_tri (by
    perma[triangle_of_ne_online (ne_13_of_B Bdbc) dL cL (online_1_of_triangle bL cL tri_abc)]) :
    0 < angle d c a), angle_extension_of_B (ne_of_online dL $ online_1_of_triangle bL cL
    tri_abc) Bdbc]

lemma inter_sq_of_perp (Bbxc : B b x c) (aX : online a X) (xX : online x X)
    (pgram1 : paragram b c d e L O P Q) (adL : diffside a d L) : ∃ l, online l X ∧ online l P := by
  have ⟨bL, cL, _, _, _, _, _, _, paraLP, _⟩ := pgram1
  by_cases paraXP : para X P; have := online_2_of_B Bbxc bL cL; have := para_trans
    (ne_line_of_online aX adL.1) (para_symm paraLP) (para_symm paraXP) x; tauto
  unfold para at paraXP; push_neg at paraXP; exact paraXP

/--A big enough angle has its perpendicular on a triangle side-/
lemma right_B_of_le_right (tri_abc : triangle a b c) (cab_le_ra : rightangle ≤ angle c a b) :
    ∃ d, angle a d b = rightangle ∧ angle a d c = rightangle ∧ B b d c := by
  rcases line_of_pts b c with ⟨L, bL, cL⟩
  rcases perpendicular_of_not_online (online_1_of_triangle bL cL tri_abc) with
    ⟨x, y, d, Bxdy, xL, _, dL, adx, ady⟩
  have adb := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[triangle_of_ne_online (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady) bL dL
          (online_1_of_triangle bL cL tri_abc)] : triangle a d b) dL bL xL adx
  have adc := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[triangle_of_ne_online (ne_of_perp_ineq Bxdy (by perma[tri_abc] : triangle a c b)
    cL bL xL (by perma[cab_le_ra]) ady) cL dL (online_1_of_triangle bL cL tri_abc)] : triangle
     a d c) dL cL xL adx
  have := B_of_three_col_ne (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady).symm
    (ne_of_perp_ineq Bxdy (by perma[tri_abc] : triangle a c b) cL bL xL (by perma[cab_le_ra])
    ady).symm (ne_23_of_tri tri_abc) ⟨L, dL, bL, cL⟩
  have := not_B_of_right_le_right tri_abc ⟨L, bL, cL, dL⟩ adb cab_le_ra
  have := not_B_of_right_le_right (by perma[tri_abc] : triangle a c b) ⟨L, cL, bL, dL⟩ adc
    (by perma[cab_le_ra])
  tauto

/--Euclid I.47, the construction of the squares for the Pythagorean theorem-/
theorem pythagoras_construct (tri_abc : triangle a b c) : ∃ d e f g h k L M N O P Q R S T U V W,
    square c d e b ∧ square a g f b ∧ square a h k c ∧ paragram b c d e L O P Q ∧
    paragram g a b f T N R S ∧ paragram h a c k U M W V ∧ diffside a d L ∧
    diffside b h M ∧ diffside c g N := by
  rcases line_of_pts b c with ⟨L, bL, cL⟩
  rcases line_of_pts a c with ⟨M, aM, cM⟩
  rcases line_of_pts a b with ⟨N, aN, bN⟩
  rcases square_of_len (ne_32_of_tri tri_abc) cL bL (online_1_of_triangle bL cL tri_abc) with
    ⟨d, e, P, O, Q, ⟨cO, dO, dP, eP, eQ, bQ, bL, cL, paraOQ, paraPL⟩, sq1, daL⟩
  rcases square_of_len (ne_12_of_tri tri_abc) aN bN (online_3_of_triangle aN bN tri_abc) with
    ⟨g, f, S, T, R, ⟨aT, gT, gS, fS, fR, bR, bN, aN, paraTR, paraSN⟩, sq2, gcN⟩
  rcases square_of_len (ne_13_of_tri tri_abc) aM cM (online_2_of_triangle aM cM tri_abc) with
    ⟨h, k, V, U, W, ⟨aU, hU, hV, kV, kW, cW, cM, aM, paraUW, paraVM⟩, sq3, hbM⟩
  exact ⟨d, e, f, g, h, k, L, M, N, O, P, Q, R, S, T, U, V, W, sq1, sq2, sq3, ⟨bL, cL, cO, dO, dP,
    eP, eQ, bQ, para_symm paraPL, paraOQ⟩, ⟨gT, aT, aN, bN, bR, fR, fS, gS, paraTR, para_symm
    paraSN⟩, ⟨hU, aU, aM, cM, cW, kW, kV, hV, paraUW, para_symm paraVM⟩, by perma[daL], by perma
    [hbM], by perma[gcN]⟩

/--Euclid I.47, the Pythagorean theorem-/
theorem pythagoras (tri_abc : triangle a b c) (ang : angle c a b = rightangle)
    (sq1 : square c d e b) (sq2 : square a g f b) (sq3 : square a h k c)
    (pgram1 : paragram b c d e L O P Q) (pgram2 : paragram g a b f T N R S)
    (pgram3 : paragram h a c k U M W V) (adL : diffside a d L) (bhM : diffside b h M)
    (cgN : diffside c g N) :
    area b c d + area b d e = area a b f + area a g f + area a h k + area a c k := by
  unfold square at sq1 sq2 sq3
  have ⟨bL, cL, cO, dO, dP, eP, eQ, bQ, paraLP, paraOQ⟩ := pgram1
  have ⟨gT, aT, aN, bN, bR, fR, fS, gS, paraTR, paraNS⟩ := pgram2
  have ⟨hU, aU, aM, cM, cW, kW, kV, hV, paraUW, paraMV⟩ := pgram3
  have Bcag := flat_of_two_right_angle (ne_12_of_tri tri_abc) aN bN cgN (by linperm)
  have Bbah := flat_of_two_right_angle (ne_13_of_tri tri_abc) aM cM bhM (by linperm)
  rcases right_B_of_le_right tri_abc (by linarith) with ⟨x, axb, axc, Bbxc⟩
  rcases line_of_pts a x with ⟨X, aX, xX⟩
  rcases inter_sq_of_perp Bbxc aX xX pgram1 adL with ⟨l, lX, lP⟩
  have paraQX := para_of_ang_eq (ne_12_of_B Bbxc) eQ bQ bL (online_2_of_B Bbxc bL cL) xX aX
    (diffside_of_sameside_diffside (sameside_of_para_online' dP eP paraLP) (diffside_symm adL))
    (by linperm[angle_extension_of_B (ne_of_para bL eP paraLP) Bbxc])
  have paraOX := para_of_ang_eq (ne_32_of_B Bbxc) dO cO cL (online_2_of_B Bbxc bL cL) xX aX
    (diffside_symm adL) (by linperm[angle_extension_of_B (ne_of_para cL dP paraLP) $ B_symm Bbxc])
  have Beld := B_of_sq Bbxc xX lX lP paraQX paraOX pgram1
  have fbc_split := angle_add_of_sameside bR fR bL cL (sameside_symm $ sameside_of_para_online aT
    (online_3_of_B (B_symm Bcag) gT aT) paraTR) $ sameside_of_sameside_diffside bR bN bL fR aN cL
    (sameside_of_para_online aT (online_3_of_B (B_symm Bcag) gT aT) paraTR) $
    diffside_of_sameside_diffside (sameside_symm $ sameside_of_para_online' fS gS paraNS) $
    diffside_symm cgN
  have abe_split := angle_add_of_sameside bN aN bQ eQ (sameside_of_sameside_diffside bQ bL bN eQ cL
    aN (sameside_symm $ sameside_of_pyth Beld aX lX pgram1 paraQX) $ diffside_of_sameside_diffside
    (sameside_of_para_online' dP eP paraLP) $ diffside_symm adL) $ sameside_of_pyth Beld aX lX
    pgram1 paraQX
  have bck_split := angle_add_of_sameside cL bL cW kW (sameside_of_sameside_diffside cW cM cL kW aM
    bL (sameside_of_para_online aU (online_3_of_B (B_symm Bbah) hU aU) paraUW) $
    diffside_of_sameside_diffside (sameside_of_para_online' hV kV paraMV) $ diffside_symm bhM)
    (sameside_symm $ sameside_of_para_online aU (online_3_of_B (B_symm Bbah) hU aU) paraUW)
  have acd_split := angle_add_of_sameside cM aM cO dO (sameside_of_sameside_diffside cO cL cM dO bL
    aM (sameside_symm $ sameside_of_pyth (B_symm Beld) aX lX ⟨cL, bL, bQ, eQ, eP, dP, dO, cO,
    paraLP, para_symm paraOQ⟩ paraOX) $ diffside_symm adL) $ sameside_of_pyth (B_symm Beld) aX lX
    ⟨cL, bL, bQ, eQ, eP, dP, dO, cO, paraLP, para_symm paraOQ⟩ paraOX
  have ⟨ae_fc, _, _⟩ := sas (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) $ by linperm
  have tri1_eq := area_eq_of_SSS (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) ae_fc
  have ⟨ad_kb, _, _⟩ := sas (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) $ by linperm
  have tri2_eq := area_eq_of_SSS (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) ad_kb
  have tri_req1 := twice_pgram_of_tri aX
    ⟨xX, lX, lP, eP, eQ, bQ, bL, online_2_of_B Bbxc bL cL, para_symm paraQX, para_symm paraLP⟩
  have tri_req2 := twice_pgram_of_tri (online_3_of_B (B_symm Bcag) gT aT) pgram2
  have tri_req3 := twice_pgram_of_tri aX
    ⟨lX, xX, online_2_of_B Bbxc bL cL, cL, cO, dO, dP, lP, para_symm paraOX, paraLP⟩
  have tri_req4 := twice_pgram_of_tri (online_3_of_B (B_symm Bbah) hU aU) pgram3
  have sq_split := quad_add_of_quad Bbxc Beld bL (online_2_of_B Bbxc bL cL) cO dO eP lP
    (sameside_of_para_online bL cL paraLP) (sameside_of_para_online' dP lP paraLP)
    $ sameside_of_para_online' bQ eQ paraOQ
  have right_half := quad_area_comm (online_2_of_B Bbxc bL cL) cL cO dO dP lP
    (sameside_of_para_online (online_2_of_B Bbxc bL cL) cL paraLP)
    (sameside_of_para_online' dP lP paraLP) $ sameside_of_para_online' xX lX paraOX
  linperm
