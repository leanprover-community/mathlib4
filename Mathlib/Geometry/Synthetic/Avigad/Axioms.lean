/-
Copyright (c) 2023 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finite.Defs

/-!
Axioms of synthetic geometry
-/

/-! Universes for points lines and circles. -/
universe u

/-- `IncidenceGeometry` represents geometry in the Euclidean sense, with primitives for points
lines and circles. -/
class IncidenceGeometry where
    /-- Points in the plane. -/
    Point : Type u
    /-- Lines in the plane. -/
    Line : Type u
    /-- Circles in the plane. -/
    Circle : Type u
    /-- A Point being on a line. -/
    OnLine : Point → Line → Prop
    /-- Two points being on the sameside of a line. -/
    SameSide : Point → Point → Line → Prop
    /-- Three points being in a row. -/
    B : Point → Point → Point → Prop
    /-- A point being the center of a center. -/
    CenterCircle : Point → Circle → Prop
    /-- A point being on a circle. -/
    OnCircle : Point → Circle → Prop
    /-- A point being inside a circle. -/
    InCircle : Point → Circle → Prop
    /-- That two lines intersect. -/
    LinesInter : Line → Line → Prop
    /-- A line and a circle intersect. -/
    LineCircleInter : Line → Circle → Prop
    /-- Two circles intersect. -/
    CirclesInter : Circle → Circle → Prop
    /-- The distance between two points. -/
    length : Point → Point → ℝ
    /-- The angle made between three points. -/
    angle : Point → Point → Point → ℝ
    /-- The constant dedicated to the right angle. -/
    rightangle : ℝ
    /-- The area made by three points. -/
    area : Point → Point → Point → ℝ
    /-- From a set of points getting one additional one. -/
    more_pts : ∀ (S : Set Point), S.Finite → ∃ a, a ∉ S
    /-- Interpolating a segment by an arbitrary amount. -/
    pt_B_of_ne : ∀ {b c}, b ≠ c → ∃ a, B b a c
    /-- Extending a segment by an arbitrary amount. -/
    pt_extension_of_ne : ∀ {b c}, b ≠ c → ∃ a, B b c a
    /-- Obtaining a point opposite a line and point. -/
    diffSide_of_not_onLine : ∀ {L a}, ¬OnLine a L → ∃ b, ¬OnLine b L ∧ ¬SameSide a b L
    /-- Get a line from two points. -/
    line_of_pts : ∀ a b, ∃ L, OnLine a L ∧ OnLine b L
    /-- Getting a circle with center and point on it. -/
    circle_of_ne : ∀ {a b}, a ≠ b → ∃ α, CenterCircle a α ∧ OnCircle b α
    /-- If lines intersect then this gives you the point of intersection. -/
    pt_of_linesInter : ∀ {L M}, LinesInter L M → ∃ a, OnLine a L ∧ OnLine a M
    /-- Gives you the points of intersection when a circle and line intersect. -/
    pts_of_lineCircleInter : ∀ {L α}, LineCircleInter L α →
      ∃ a b, a ≠ b ∧ OnLine a L ∧ OnLine b L ∧ OnCircle a α ∧ OnCircle b α
    /-- Getting points on circles. -/
    pt_on_circle_of_inside_outside : ∀ {b c α}, ¬OnCircle c α → InCircle b α → ¬InCircle c α →
      ∃ a, B b a c ∧ OnCircle a α
    /-- Getting points on circles. -/
    pt_oncircle_of_inside_ne : ∀ {a b α}, a ≠ b → InCircle b α → ∃ c, B a b c ∧ OnCircle c α
    /-- Getting points of intersection of two circles. -/
    pts_of_circlesInter : ∀ {α β}, CirclesInter α β →
      ∃ a b, a ≠ b ∧ OnCircle a α ∧ OnCircle a β ∧ OnCircle b α ∧ OnCircle b β
    /-- Obtaining a specific point of intersection between a line and a circle. -/
    pt_sameSide_of_circlesInter : ∀ {b c d L α β}, OnLine c L → OnLine d L → ¬OnLine b L →
      CenterCircle c α → CenterCircle d β → CirclesInter α β → ∃ a, SameSide a b L ∧ OnCircle a α ∧
      OnCircle a β
    /-- Condition to remark that two points uniquely determine a line. -/
    line_unique_of_pts : ∀ {a b L M}, a ≠ b → OnLine a L → OnLine b L → OnLine a M → OnLine b M →
      L = M
    /-- The center of a circle is unique. -/
    centerCircle_unique : ∀ {a b α}, CenterCircle a α → CenterCircle b α → a = b
    /-- The center of a circle is inside the circle. -/
    inside_circle_of_center : ∀ {a α}, CenterCircle a α → InCircle a α
    /-- If a point is on a circle then it is not inside. -/
    not_on_circle_of_inside : ∀ {a α}, InCircle a α → ¬OnCircle a α
    /-- Symmetry of Betweeness. -/
    B_symm : ∀ {a b c}, B a b c → B c b a
    /-- B is strict. -/
    ne_12_of_B : ∀ {a b c}, B a b c → a ≠ b
    /-- B is strict. -/
    ne_13_of_B : ∀ {a b c}, B a b c → a ≠ c
    /-- If you are between then the other configurations are impossible. -/
    not_B_of_B : ∀ {a b c}, B a b c → ¬B b a c
    /-- From two points being on a line the B forces the third point. -/
    onLine_3_of_B : ∀ {a b c L}, B a b c → OnLine a L → OnLine b L → OnLine c L
    /-- From two points being on a line the B forces the third point. -/
    onLine_2_of_B : ∀ {a b c L}, B a b c → OnLine a L → OnLine c L → OnLine b L
    /-- Deducing betweeness from four points on a line. -/
    B124_of_B134_B123 : ∀ {a b c d}, B a b c → B a d b → B a d c
    /-- Deducing betweeness from four points on a line. -/
    B124_of_B123_B234 : ∀ {a b c d}, B a b c → B b c d → B a b d
    /-- If three distict points are on a line then they are between in some way. -/
    B_of_three_onLine_ne : ∀ {a b c L}, a ≠ b → a ≠ c → b ≠ c → OnLine a L → OnLine b L →
      OnLine c L → B a b c ∨ B b a c ∨ B a c b
    /-- Conditions for not B given four points on a line. -/
    not_B324_of_B123_B124 : ∀ {a b c d}, B a b c → B a b d → ¬B c b d
    /-- Sameside is reflective. -/
    sameSide_rfl_of_not_onLine : ∀ {a L}, ¬OnLine a L → SameSide a a L
    /-- Sameside is symmetric. -/
    sameSide_symm : ∀ {a b L}, SameSide a b L → SameSide b a L
    /-- Being on the sameside of a line implies you are not on the line. -/
    not_onLine_of_sameSide : ∀ {a b L}, SameSide a b L → ¬OnLine a L
    /-- Sameside is transitive. -/
    sameSide_trans : ∀ {a b c L}, SameSide a b L → SameSide a c L → SameSide b c L
    /-- If you are not on a line and two points are on opposite sides then you are on the same side
    as one of the points. -/
    sameSide_or_of_diffSide : ∀ {a b c L}, ¬OnLine a L → ¬OnLine b L → ¬OnLine c L →
      ¬SameSide a b L → SameSide a c L ∨ SameSide b c L
    /-- Relations between sidedness and betweeness. -/
    sameSide12_of_B123_sameSide13 : ∀ {a b c L}, B a b c → SameSide a c L → SameSide a b L
    /-- Relations between sidedness and betweeness. -/
    sameSide_of_B_not_onLine_2 : ∀ {a b c L}, B a b c → OnLine a L → ¬OnLine b L → SameSide b c L
    /-- Relations between sidedness and betweeness. -/
    not_sameSide13_of_B123_onLine2 : ∀ {a b c L}, B a b c → OnLine b L → ¬SameSide a c L
    /-- Relations between sidedness and betweeness. -/
    B_of_onLine_inter : ∀ {a b c L M}, a ≠ b → b ≠ c → a ≠ c → L ≠ M →
      OnLine a L → OnLine b L → OnLine c L → OnLine b M → ¬SameSide a c M → B a b c
    /-- Deducing sidedness from three lines intersecting. -/
    not_sameSide_of_sameSide_sameSide : ∀ {a b c d L M N}, OnLine a L → OnLine a M → OnLine a N →
      OnLine b L → OnLine c M → OnLine d N → SameSide c d L → SameSide b c N → ¬SameSide b d M
    /-- Deducing sidedness from three lines intersecting. -/
    sameSide_of_sameSide_not_sameSide : ∀ {a b c d L M N}, a ≠ b → OnLine a L → OnLine a M →
      OnLine a N → OnLine b L → OnLine c M → OnLine d N → ¬OnLine d M → SameSide c d L →
      ¬SameSide b d M → SameSide b c N
    /-- Points of intersection of a line and circle. -/
    B_of_lineCircleInter : ∀ {a b c L α}, b ≠ c → OnLine a L →
      OnLine b L → OnLine c L → OnCircle b α → OnCircle c α → InCircle a α → B b a c
    /-- The points of intersection of circles are on opposite sides the line that joins the centers.
    -/
    not_sameSide_of_circle_inter : ∀ {a b c d L α β},  c ≠ d → α ≠ β →  OnLine a L → OnLine b L →
      OnCircle c α → OnCircle c β → OnCircle d α → OnCircle d β → CenterCircle a α →
      CenterCircle b β → CirclesInter α β → ¬SameSide c d L
    /-- Condition for lines intersecting. -/
    lines_inter_of_not_sameSide : ∀ {a b L M}, OnLine a M → OnLine b M → ¬SameSide a b L →
      LinesInter L M
    /-- Condition for line circle intersection. -/
    lineCircleInter_of_not_sameSide : ∀ {a b L α}, ¬SameSide a b L → OnCircle a α ∨ InCircle a α →
      OnCircle b α ∨ InCircle b α → LineCircleInter L α
    /-- Condition for line circle intersection. -/
    lineCircleInter_of_inside_onLine : ∀ {a L α}, OnLine a L → InCircle a α → LineCircleInter L α
    /-- Condition for circle circle intersection. -/
    circlesInter_of_inside_on_circle : ∀ {a b α β}, OnCircle b α → OnCircle a β → InCircle a α →
      InCircle b β → CirclesInter α β
    /-- A length is zero iff the points are equal. -/
    length_eq_zero_iff : ∀ {a b}, length a b = 0 ↔ a = b
    /-- Length is symmetric. -/
    length_symm : ∀ a b, length a b = length b a
    /-- Angles are symmetric across the middle point. -/
    angle_symm : ∀ a b c, angle a b c = angle c b a
    /-- Angles are nonnegative. -/
    angle_nonneg : ∀ a b c, 0 ≤ angle a b c
    /-- Lengths are nonnegative. -/
    length_nonneg : ∀ a b, 0 ≤ length a b
    /-- Areas are nonnegative. -/
    area_nonneg : ∀ a b c, 0 ≤ area a b c
    /-- Degenerate areas are zero. -/
    degenerate_area : ∀ a b, area a a b = 0
    /-- Area is completely symmetric. -/
    area_invariant_cycle : ∀ a b c, area a b c = area c a b
    /-- Area is completely symmetric. -/
    area_invariant_flip : ∀ a b c, area a b c = area a c b
    /-- If SSS is satisfied then triangles have equal area. -/
    area_eq_of_SSS : ∀ {a b c a1 b1 c1}, length a b = length a1 b1 →
      length a c = length a1 c1 → length b c = length b1 c1 → area a b c = area a1 b1 c1
    /-- Given betweeness the lengths of segments add as expected. -/
    length_sum_of_B : ∀ {a b c}, B a b c → length a b + length b c = length a c
    /-- Points on a circle have the same distance from the radius. -/
    on_circle_iff_length_eq : ∀ {a b c α}, CenterCircle a α → OnCircle b α →
      (length a b = length a c ↔ OnCircle c α)
    /-- A point on a circle has a greater distance from the center than a point inside the circle.
    -/
    in_circle_iff_length_lt : ∀ {a b c α}, CenterCircle a α → OnCircle b α →
      (length a c < length a b ↔ InCircle c α)
    /-- One kind of degenerate angle is zero. -/
    angle_zero_iff_onLine : ∀ {a b c L}, a ≠ b → a ≠ c → OnLine a L → OnLine b L →
      (OnLine c L ∧ ¬B b a c ↔ angle b a c = 0)
    /-- Conditions for a split angle to add as expected. -/
    angle_add_iff_sameSide : ∀ {a b c d L M}, a ≠ b → a ≠ c → OnLine a L →
      OnLine b L → OnLine a M → OnLine c M → ¬OnLine d M → ¬OnLine d L → L ≠ M →
      (angle b a c = angle b a d + angle d a c ↔ SameSide b d M ∧ SameSide c d L)
    /-- Betweeness forces equal angles across the middle to be right angles. -/
    angle_eq_iff_rightangle : ∀ {a b c d L}, OnLine a L → OnLine b L → ¬OnLine d L → B a c b →
      (angle a c d = angle d c b ↔ angle a c d = rightangle)
    /-- A condition to extend angles in a predictable way. -/
    angle_extension : ∀ {a b c a1 b1 c1 L M}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → OnLine a L →
      OnLine b L → OnLine b1 L → OnLine a M → OnLine c M → OnLine c1 M → ¬B b a b1 → ¬B c a c1 →
      angle b a c = angle b1 a1 c1
    /-- The unparallel postulate. -/
    unparallel_postulate : ∀ {a b c d L M N}, b ≠ c → OnLine a L → OnLine b L →
      OnLine b M → OnLine c M → OnLine c N → OnLine d N →  SameSide a d M → angle a b c +
      angle b c d < 2 * rightangle → ∃ e, OnLine e L ∧ OnLine e N ∧ SameSide e a M
    /-- Areas of degenerate triangles equal zero. -/
    area_zero_iff_onLine : ∀ {a b c L}, a ≠ b → OnLine a L → OnLine b L →
      (area a b c = 0 ↔ OnLine c L)
    /-- Areas adding on a triangle given a betweeness condition. -/
    area_add_iff_B : ∀ {a b c d L}, a ≠ b → b ≠ c → c ≠ a → OnLine a L →
      OnLine b L → OnLine c L → ¬OnLine d L → (B a b c ↔ area d a b + area d c b = area d a c)
    /-- SAS is equivalent to SSS. -/
    SAS_iff_SSS : ∀ {a b c d e f}, length a b = length d e → length a c = length d f →
      (angle b a c = angle e d f ↔ length b c = length e f)

variable [i : IncidenceGeometry]
namespace IncidenceGeometry
-------------------------------------------------- Definitions -----------------------------------
/-- Points being on different sides of a line. -/
def DiffSide (a b : Point) (L : Line) : Prop := ¬OnLine a L ∧ ¬OnLine b L ∧ ¬SameSide a b L

/-- A point being outside a circle. -/
def OutCircle (a : Point) (α : Circle) : Prop := ¬OnCircle a α ∧ ¬InCircle a α

/-- Points being colinear. -/
def Colinear (a b c : Point) : Prop := ∃ L : Line, OnLine a L ∧ OnLine b L ∧ OnLine c L

/-- Definition of a triangle. -/
def Triangle (a b c : Point) : Prop := ¬Colinear a b c

/-- Definition of an equilateral triangle. -/
def EqTri (a b c : Point) : Prop := Triangle a b c ∧ length a b = length a c ∧
  length b a = length b c ∧ length c a = length c b

/-- Definition of an isosoles triangle. -/
def IsoTri (a b c : Point) : Prop := Triangle a b c ∧ length a b = length a c

/-- Definition of parallel. -/
def Para (M N : Line) : Prop := ∀ e, ¬OnLine e M ∨ ¬OnLine e N

/-- Definition of parallelogram. -/
def Paragram (a b c d : Point) (L M N O : Line) : Prop := OnLine a L ∧ OnLine b L ∧ OnLine b M ∧
    OnLine c M ∧ OnLine c N ∧ OnLine d N ∧ OnLine d O ∧ OnLine a O ∧ Para L N ∧ Para M O

/-- Definition of a square. -/
def Square (a b c d : Point) : Prop := length a b = length b c ∧ length a b = length c d ∧
    length a b = length d a ∧ angle a b c = rightangle ∧ angle b c d = rightangle ∧
    angle c d a = rightangle ∧ angle d a b = rightangle

end IncidenceGeometry
