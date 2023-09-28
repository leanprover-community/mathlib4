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

/-! Universes for points lines and circles-/
universe u

/-- `IncidenceGeometry` represents geometry in the Euclidean sense, with primitives for points
lines and circles-/
class IncidenceGeometry :=
/--Points in the plane-/
(Point : Type u)
/--Lines in the plane-/
(Line : Type u)
/--Circles in the plane-/
(Circle : Type u)

/--A Point being on a line-/
(online : Point → Line → Prop)
/--Two points being on the sameside of a line-/
(sameside : Point → Point → Line → Prop)
/--Three points being in a row-/
(B : Point → Point → Point → Prop)
/--A point being the center of a center-/
(center_circle : Point → Circle → Prop)
/--A point being on a circle-/
(on_circle : Point → Circle → Prop)
/--A point being inside a circle-/
(in_circle : Point → Circle → Prop)
/--That two lines intersect-/
(lines_inter : Line → Line → Prop)
/--A line and a circle intersect-/
(line_circle_inter : Line → Circle → Prop)
/--Two circles intersect-/
(circles_inter : Circle → Circle → Prop)
/--The distance between two points-/
(length : Point → Point → ℝ)
/--The angle made between three points-/
(angle : Point → Point → Point → ℝ)
/--The constant dedicated to the right angle-/
(rightangle : ℝ)
/--The area made by three points-/
(area : Point → Point → Point → ℝ)

/--From a set of points getting one additional one-/
(more_pts : ∀ (S : Set Point), S.Finite → ∃ (a : Point), a ∉ S)
/--Interpolating a segment by an arbitrary amount-/
(pt_B_of_ne : ∀ {b c : Point}, b ≠ c → ∃ (a : Point), B b a c)
/--Extending a segment by an arbitrary amount-/
(pt_extension_of_ne : ∀ {b c : Point}, b ≠ c → ∃ (a : Point), B b c a)
/--Obtaining a point opposite a line and point-/
(diffside_of_not_online : ∀ {L : Line}, ∀ {a : Point}, ¬online a L →
    ∃ (b : Point), ¬online b L ∧ ¬sameside a b L)
/--Get a line from two points-/
(line_of_pts : ∀ (a b : Point), ∃ (L : Line), online a L ∧ online b L)
/--Getting a circle with center and point on it-/
(circle_of_ne : ∀ {a b : Point}, a ≠ b → ∃ (α : Circle), center_circle a α ∧ on_circle b α)
/--If lines intersect then this gives you the point of intersection-/
(pt_of_lines_inter : ∀ {L M : Line}, lines_inter L M →
  ∃ (a : Point), online a L ∧ online a M)
/--Gives you the points of intersection when a circle and line intersect-/
(pts_of_line_circle_inter : ∀ {L : Line}, ∀ {α : Circle}, line_circle_inter L α →
  ∃ (a b : Point),  a ≠ b ∧ online a L ∧ online b L ∧ on_circle a α ∧ on_circle b α )
/--Getting points on circles-/
(pt_on_circle_of_inside_outside : ∀ {b c : Point}, ∀ {α : Circle},
  ¬on_circle c α → in_circle b α → ¬in_circle c α →
  ∃ (a : Point), B b a c ∧ on_circle a α)
/--Getting points on circles-/
(pt_oncircle_of_inside_ne : ∀ {a b : Point}, ∀ {α : Circle}, a ≠ b → in_circle b α →
  ∃ (c : Point), B a b c ∧ on_circle c α)
/--Getting points of intersection of two circles-/
(pts_of_circles_inter : ∀ {α β : Circle}, circles_inter α β →
  ∃ (a b : Point), a ≠ b ∧ on_circle a α ∧ on_circle a β ∧ on_circle b α ∧ on_circle b β)
/--Obtaining a specific point of intersection between a line and a circle-/
(pt_sameside_of_circles_inter : ∀ {b c d : Point}, ∀ {L : Line}, ∀ {α β : Circle},
  online c L → online d L → ¬online b L  → center_circle c α → center_circle d β → circles_inter α β
  → ∃ (a : Point), sameside a b L ∧ on_circle a α ∧  on_circle a β)
/--Condition to remark that two points uniquely determine a line-/
(line_unique_of_pts : ∀ {a b : Point}, ∀ {L M : Line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
/--The center of a circle is unique-/
(center_circle_unique : ∀ {a b : Point}, ∀ {α : Circle}, center_circle a α → center_circle b α →
  a = b)
/--The center of a circle is inside the circle-/
(inside_circle_of_center : ∀ {a : Point}, ∀ {α : Circle}, center_circle a α → in_circle a α)
/--If a point is on a circle then it is not inside-/
(not_on_circle_of_inside : ∀ {a : Point}, ∀ {α : Circle}, in_circle a α → ¬on_circle a α)
/--Symmetry of Betweeness-/
(B_symm : ∀ {a b c : Point}, B a b c → B c b a)
/--B is strict-/
(ne_12_of_B : ∀ {a b c : Point}, B a b c → a ≠ b)
/--B is strict-/
(ne_13_of_B : ∀ {a b c : Point}, B a b c → a ≠ c)
/--B is strict-/
(ne_23_of_B : ∀ {a b c : Point}, B a b c → b ≠ c)
/--If you are between then the other configurations are impossible-/
(not_B_of_B : ∀ {a b c : Point}, B a b c → ¬B b a c)
/--From two points being on a line the B forces the third point-/
(online_3_of_B : ∀ {a b c : Point}, ∀ {L : Line}, B a b c → online a L → online b L → online c L)
/--From two points being on a line the B forces the third point-/
(online_2_of_B : ∀ {a b c : Point}, ∀ {L : Line}, B a b c → online a L → online c L → online b L)
/--Deducing betweeness from four points on a line-/
(B124_of_B134_B123 : ∀ {a b c d : Point}, B a b c → B a d b → B a d c)
/--Deducing betweeness from four points on a line-/
(B124_of_B123_B234 : ∀ {a b c d : Point}, B a b c → B b c d → B a b d)
/--If three distict points are on a line then they are between in some way-/
(B_of_three_online_ne : ∀ {a b c : Point}, ∀ {L : Line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L →  B a b c ∨ B b a c ∨ B a c b)
/--Conditions for not B given four points on a line-/
(not_B324_of_B123_B124 : ∀ {a b c d : Point}, B a b c → B a b d → ¬B c b d)
/--Sameside is reflective-/
(sameside_rfl_of_not_online : ∀ {a : Point}, ∀ {L : Line}, ¬online a L → sameside a a L)
/--Sameside is symmetric-/
(sameside_symm : ∀ {a b : Point}, ∀ {L : Line}, sameside a b L → sameside b a L)
/--Being on the sameside of a line implies you are not on the line-/
(not_online_of_sameside : ∀ {a b : Point}, ∀ {L : Line}, sameside a b L → ¬online a L)
/--Sameside is transitive-/
(sameside_trans : ∀ {a b c : Point}, ∀ {L : Line}, sameside a b L → sameside a c L →
  sameside b c L)
/--If you are not on a line and two points are on opposite sides then you are on the same side as
one of the points-/
(sameside_or_of_diffside : ∀ {a b c : Point}, ∀ {L : Line}, ¬online a L → ¬online b L →
  ¬online c L → ¬sameside a b L → sameside a c L ∨ sameside b c L)
/--Relations between sidedness and betweeness-/
(sameside12_of_B123_sameside13 : ∀ {a b c : Point}, ∀ {L : Line}, B a b c → sameside a c L →
  sameside a b L)
/--Relations between sidedness and betweeness-/
(sameside_of_B_not_online_2 : ∀ {a b c : Point}, ∀ {L : Line}, B a b c → online a L → ¬online b L
  → sameside b c L)
/--Relations between sidedness and betweeness-/
(not_sameside13_of_B123_online2 : ∀ {a b c : Point}, ∀ {L : Line}, B a b c → online b L →
  ¬sameside a c L)
/--Relations between sidedness and betweeness-/
(B_of_online_inter : ∀ {a b c : Point}, ∀ {L M : Line}, a ≠ b → b ≠ c → a ≠ c → L ≠ M →
  online a L → online b L → online c L → online b M → ¬sameside a c M → B a b c)
/--Deducing sidedness from three lines intersecting-/
(not_sameside_of_sameside_sameside : ∀ {a b c d : Point}, ∀ {L M N : Line}, online a L →
  online a M → online a N → online b L → online c M → online d N → sameside c d L →
  sameside b c N → ¬sameside b d M)
/--Deducing sidedness from three lines intersecting-/
(sameside_of_sameside_not_sameside : ∀ {a b c d : Point}, ∀ {L M N : Line}, a≠ b → online a L →
  online a M → online a N → online b L → online c M → online d N → ¬online d M → sameside c d L →
  ¬sameside b d M → sameside b c N)
/--Points of intersection of a line and circle-/
(B_of_line_circle_inter : ∀ {a b c : Point}, ∀ {L : Line}, ∀ {α : Circle}, b ≠ c → online a L →
  online b L → online c L → on_circle b α → on_circle c α → in_circle a α → B b a c)
/--The points of intersection of circles are on opposite sides the line that joins the centers-/
(not_sameside_of_circle_inter : ∀ {a b c d : Point}, ∀ {L : Line}, ∀ {α β : Circle},  c ≠ d →
  α ≠ β →  online a L → online b L  → on_circle c α → on_circle c β → on_circle d α →
  on_circle d β → center_circle a α → center_circle b β → circles_inter α β → ¬sameside c d L)
/--Condition for lines intersecting-/
(lines_inter_of_not_sameside : ∀ {a b : Point}, ∀ {L M : Line}, online a M → online b M →
  ¬sameside a b L → lines_inter L M)
/--Condition for line circle intersection-/
(line_circle_inter_of_not_sameside : ∀ {a b : Point}, ∀ {L : Line}, ∀ {α : Circle},
  ¬sameside a b L → on_circle a α ∨ in_circle a α→ on_circle b α ∨ in_circle b α →
  line_circle_inter L α)
/--Condition for line circle intersection-/
(line_circle_inter_of_inside_online : ∀ {a : Point}, ∀ {L : Line}, ∀ {α : Circle}, online a L →
  in_circle a α →  line_circle_inter L α)
/--Condition for circle circle intersection-/
(circles_inter_of_inside_on_circle : ∀ {a b : Point}, ∀ {α β : Circle}, on_circle b α →
  on_circle a β → in_circle a α →  in_circle b β → circles_inter α β)
/--A length is zero iff the points are equal-/
(length_eq_zero_iff : ∀ {a b : Point}, length a b = 0 ↔ a = b)
/--Length is symmetric-/
(length_symm : ∀ (a b : Point), length a b = length b a)
/--Angles are symmetric across the middle point-/
(angle_symm : ∀ (a b c : Point), angle a b c = angle c b a)
/--Angles are nonnegative-/
(angle_nonneg : ∀ (a b c : Point), 0 ≤ angle a b c)
/--Lengths are nonnegative-/
(length_nonneg : ∀ (a b : Point), 0 ≤ length a b)
/--Areas are nonnegative-/
(area_nonneg : ∀ (a b c : Point), 0 ≤ area a b c)
/--Degenerate areas are zero-/
(degenerate_area : ∀ (a b : Point), area a a b = 0)
/--Area is completely symmetric-/
(area_invariant : ∀ (a b c : Point), area a b c = area c a b ∧ area a b c = area a c b)
/--If SSS is satisfied then triangles have equal area-/
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : Point}, length a b = length a1 b1 →
  length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1)
/--Given betweeness the lengths of segments add as expected-/
(length_sum_of_B : ∀ {a b c : Point}, B a b c → length a b + length b c = length a c)
/--Points on a circle have the same distance from the radius-/
(on_circle_iff_length_eq : ∀ {a b c : Point}, ∀ {α : Circle},  center_circle a α →
  on_circle b α → (length a b = length a c ↔ on_circle c α))
/--A point on a circle has a greater distance from the center than a point inside the circle-/
(in_circle_iff_length_lt : ∀ {a b c : Point}, ∀ {α : Circle}, center_circle a α → on_circle b α →
  (length a c < length a b ↔ in_circle c α))
/--One kind of degenerate angle is zero-/
(angle_zero_iff_online : ∀ {a b c : Point}, ∀ {L : Line}, a ≠ b → a ≠ c → online a L →
  online b L → (online c L ∧ ¬B b a c ↔ angle b a c = 0))
/--Conditions for a split angle to add as expected-/
(angle_add_iff_sameside : ∀ {a b c d : Point}, ∀ {L M : Line}, a ≠ b → a ≠ c → online a L →
  online b L → online a M → online c M → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
/--Betweeness forces equal angles across the middle to be right angles-/
(angle_eq_iff_rightangle : ∀ {a b c d : Point}, ∀ {L : Line}, online a L → online b L →
  ¬online d L → B a c b → (angle a c d = angle d c b ↔ angle a c d = rightangle))
/--A condition to extend angles in a predictable way-/
(angle_extension : ∀ {a b c a1 b1 c1 : Point}, ∀ {L M : Line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a →
  online a L → online b L → online b1 L → online a M → online c M → online c1 M →
  ¬B b a b1 → ¬B c a c1 → angle b a c = angle b1 a1 c1)
/--The unparallel postulate-/
(unparallel_postulate : ∀ {a b c d : Point}, ∀ {L M N : Line}, b ≠ c → online a L → online b L →
  online b M → online c M → online c N → online d N →  sameside a d M → angle a b c +
  angle b c d < 2 * rightangle → ∃ (e : Point), online e L ∧ online e N ∧ sameside e a M)
/--Areas of degenerate triangles equal zero-/
(area_zero_iff_online : ∀ {a b c : Point}, ∀ {L : Line}, a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
/--Areas adding on a triangle given a betweeness condition-/
(area_add_iff_B : ∀ {a b c d : Point}, ∀ {L : Line}, a ≠ b → b ≠ c → c ≠ a → online a L →
  online b L → online c L → ¬online d L → (B a b c ↔ area d a b + area d c b = area d a c))
/--SAS is equivalent to SSS-/
(SAS_iff_SSS : ∀ {a b c d e f : Point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f))

variable [i : IncidenceGeometry]
open IncidenceGeometry
-------------------------------------------------- Definitions -----------------------------------
/--Points being on different sides of a line-/
def diffside (a b : Point) (L : Line) := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L
/--A point being outside a circle-/
def out_circle (a : Point) (α : Circle) := ¬on_circle a α ∧ ¬in_circle a α
/--Points being colinear-/
def colinear (a b c : Point) := ∃ L : Line, online a L ∧ online b L ∧ online c L
/--Definition of a triangle-/
def triangle (a b c : Point) := ¬colinear a b c
/--Definition of an equilateral triangle-/
def eq_tri (a b c : Point) := triangle a b c ∧ length a b = length a c ∧ length b a = length b c
  ∧ length c a = length c b
/--Definition of an isosoles triangle-/
def iso_tri (a b c : Point) := triangle a b c ∧ length a b = length a c
/--Definition of parallel-/
def para (M N : Line) := ∀ e, ¬online e M ∨ ¬online e N
/--Definition of parallelogram-/
def paragram (a b c d : Point) (L M N O : Line) := online a L ∧ online b L ∧ online b M ∧
    online c M ∧ online c N ∧ online d N ∧ online d O ∧ online a O ∧ para L N ∧ para M O
/--Definition of a square-/
def square (a b c d : Point) := length a b = length b c ∧ length a b = length c d ∧
    length a b = length d a ∧ angle a b c = rightangle ∧ angle b c d = rightangle ∧
    angle c d a = rightangle ∧ angle d a b = rightangle
