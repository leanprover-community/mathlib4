/-
Copyright (c) 2023 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite

/-!
Axioms of synthetic geometry
-/

universe u1 u2 u3

/-- `incidence_geometry` represents geometry in the Euclidean sense, with primitives for points
lines and circles-/
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(center_circle : point → circle → Prop)
(on_circle : point → circle → Prop)
(in_circle : point → circle → Prop)
(lines_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circles_inter : circle → circle → Prop)
(length : point → point → ℝ)
(angle : point → point → point → ℝ)
(rightangle : ℝ)
(area : point → point → point → ℝ)

(more_pts : ∀ (S : Set point), S.Finite → ∃ (a : point), a ∉ S)
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
(diffside_of_not_online : ∀ {L : line}, ∀ {a : point}, ¬online a L →
    ∃ (b : point), ¬online b L ∧ ¬sameside a b L)
(line_of_pts : ∀ (a b : point), ∃ (L :line), online a L ∧ online b L)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ on_circle b α)
(pt_of_lines_inter : ∀ {L M : line}, lines_inter L M →
  ∃ (a : point), online a L ∧ online a M)
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point),  a ≠ b ∧ online a L ∧ online b L ∧ on_circle a α ∧ on_circle b α )
(pt_on_circle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  ¬on_circle c α →in_circle b α → ¬in_circle c α →
  ∃ (a : point), B b a c ∧ on_circle a α)
(pt_oncircle_of_inside_ne : ∀ {a b : point}, ∀ {α : circle}, a ≠ b → in_circle b α →
  ∃ (c : point), B a b c ∧ on_circle c α)
(pts_of_circles_inter : ∀ {α β : circle}, circles_inter α β →
  ∃ (a b : point), a≠ b∧ on_circle a α ∧ on_circle a β ∧ on_circle b α ∧ on_circle b β )
(pt_sameside_of_circles_inter : ∀ {b c d : point}, ∀ {L : line}, ∀ {α β : circle},
  online c L → online d L →¬online b L  → center_circle c α → center_circle d β →circles_inter α β
  →  ∃ (a : point), sameside a b L∧ on_circle a α ∧  on_circle a β )
(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, center_circle a α → center_circle b α →
  a = b)
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, center_circle a α → in_circle a α)
(not_on_circle_of_inside : ∀ {a : point}, ∀ {α : circle}, in_circle a α → ¬on_circle a α)
(B_symm : ∀ {a b c : point}, B a b c → B c b a )
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L →  B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)
(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L →
  sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L →
  ¬online c L → ¬sameside a b L → sameside a c L ∨ sameside b c L)
(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L →
  sameside a b L)
(sameside_of_B_not_online_2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L
  → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L →
  ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, a ≠ b → b ≠ c → a ≠ c → L ≠ M →
  online a L → online b L → online c L → online b M → ¬sameside a c M → B a b c)
(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L →
  online a M → online a N → online b L → online c M → online d N → sameside c d L →
  sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, a≠ b → online a L →
  online a M → online a N → online b L → online c M → online d N → ¬online d M → sameside c d L →
  ¬sameside b d M → sameside b c N)
(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle },b ≠ c → online a L →
  online b L → online c L → on_circle b α → on_circle c α → in_circle a α →   B b a c)
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {L : line}, ∀ {α β : circle},  c ≠ d →
  α ≠ β →  online a L → online b L  → on_circle c α → on_circle c β → on_circle d α →
  on_circle d β → center_circle a α → center_circle b β → circles_inter α β → ¬sameside c d L)
(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, online a M → online b M →
  ¬sameside a b L → lines_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle},
  ¬sameside a b L → on_circle a α ∨ in_circle a α→ on_circle b α ∨ in_circle b α →
  line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, online a L →
  in_circle a α →  line_circle_inter L α)
(circles_inter_of_inside_on_circle : ∀ {a b : point}, ∀ {α β : circle}, on_circle b α →
  on_circle a β → in_circle a α →  in_circle b β → circles_inter α β)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_symm : ∀ (a b : point), length a b = length b a)
(angle_symm : ∀ (a b c : point), angle a b c = angle c b a)
(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(area_nonneg : ∀ (a b c : point), 0 ≤ area a b c)
(degenerate_area : ∀ (a b : point), area a a b = 0)
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 →
  length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1)
(length_sum_of_B : ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(on_circle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle},  center_circle a α →
  on_circle b α → (length a b = length a c ↔ on_circle c α))
(in_circle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α →
  (length a c < length a b ↔ in_circle c α))
(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L →
  online b L → (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, a ≠ b → a ≠ c → online a L →
  online b L → online a M → online c M → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L →
  ¬online d L → B a c b → (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a →
  online a L → online b L → online b1 L → online a M → online c M → online c1 M →
  ¬B b a b1 → ¬B c a c1 → angle b a c = angle b1 a1 c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line}, b ≠ c → online a L → online b L →
  online b M → online c M → online c N → online d N →  sameside a d M → angle a b c +
  angle b c d < 2 * rightangle → ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)
(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L →
  online b L → online c L → ¬online d L → (B a b c ↔ area d a b + area d c b = area d a c))
(SAS_iff_SSS : ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f)) --Euclid Prop 4,8

variable [i : incidence_geometry]
open incidence_geometry
-------------------------------------------------- Definitions -----------------------------------
def diffside (a b : point) (L : line) := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L
--3/28/23
def out_circle (a : point) (α : circle) := ¬on_circle a α ∧ ¬in_circle a α

def colinear (a b c : point) := ∃ L : line, online a L ∧ online b L ∧ online c L

def triangle (a b c : point) := ¬colinear a b c

def eq_tri (a b c : point) := triangle a b c ∧ length a b = length a c ∧ length b a = length b c
  ∧ length c a = length c b

def iso_tri (a b c : point) := triangle a b c ∧ length a b = length a c

def para (M N : line) := ∀ e, ¬online e M ∨ ¬online e N

def paragram (a b c d : point) (L M N O : line) := online a L ∧ online b L ∧ online b M ∧
    online c M ∧ online c N ∧ online d N ∧ online d O ∧ online a O ∧ para L N ∧ para M O

def square (a b c d : point) := length a b = length b c ∧ length a b = length c d ∧
    length a b = length d a ∧ angle a b c = rightangle ∧ angle b c d = rightangle ∧
    angle c d a = rightangle ∧ angle d a b = rightangle
