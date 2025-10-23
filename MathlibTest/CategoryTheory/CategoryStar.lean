import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

section

variable (C : Type*) [Category* C]

universe u
variable (D : Type u) [Category* D]

variable (E : Type 3) [Category* E]

def fooC := C ⥤ C
def fooD := D ⥤ D
def fooE := E ⥤ E
def fooCDE := C ⥤ D ⥤ E

/--
info: fooC.{v_1, u_1} (C : Type u_1) [Category.{v_1, u_1} C] : Type (max v_1 u_1)
-/
#guard_msgs (info) in
#check fooC

/--
info: fooD.{v_2, u} (D : Type u) [Category.{v_2, u} D] : Type (max v_2 u)
-/
#guard_msgs (info) in
#check fooD

/--
info: fooE.{v_3} (E : Type 3) [Category.{v_3, 3} E] : Type (max v_3 3)
-/
#guard_msgs (info) in
#check fooE

/--
info: fooCDE.{v_2, u, v_1, u_1, v_3} (C : Type u_1) [Category.{v_1, u_1} C] (D : Type u) [Category.{v_2, u} D] (E : Type 3)
  [Category.{v_3, 3} E] : Type (max v_1 (max u v_3) u_1 (max (max 3 u) v_3) v_2)
-/
#guard_msgs (info) in
#check fooCDE

end

section

variable (C D : Type*) [Category* (C × D)]

def foo := (C × D) ⥤ (C × D)

/--
info: foo.{v_1, u_1, u_2} (C : Type u_1) (D : Type u_2) [Category.{v_1, max u_1 u_2} (C × D)] : Type (max v_1 u_2 u_1)
-/
#guard_msgs (info) in
#check foo



universe u₁ u₂

variable (E : Sort (imax (u₁ + 1) (u₂ + 1))) [Category* E]
variable (F : Sort (max (u₁ + 1) (u₂ + 1))) [Category* F]

def barE := E ⥤ E
def barF := F ⥤ F

/--
info: barE.{v_2, u₁, u₂} (E : Type (max u₁ u₂)) [Category.{v_2, max u₁ u₂} E] : Type (max v_2 u₁ u₂)
-/
#guard_msgs (info) in
#check barE

/--
info: barF.{v_3, u₁, u₂} (F : Type (max u₁ u₂)) [Category.{v_3, max u₁ u₂} F] : Type (max v_3 u₁ u₂)
-/
#guard_msgs (info) in
#check barF

end

section

variable (C1 : Type*) [Category* C1] (C2 : Type*) [Category* C2]

universe a b

variable [Category* (Type a)] [Category (Type b)]

universe c

variable [Category* (Type c)]

def Big := Type a ⥤ Type b ⥤ C1 ⥤ C2 ⥤ Type c

/--
info: Big.{v_3, a, b, v_4, c, v_1, u_1, v_2, u_2, u_3} (C1 : Type u_1) [Category.{v_1, u_1} C1] (C2 : Type u_2)
  [Category.{v_2, u_2} C2] [Category.{v_3, a + 1} (Type a)] [Category.{u_3, b + 1} (Type b)]
  [Category.{v_4, c + 1} (Type c)] :
  Type
    (max v_3 (max (max (max (b + 1) u_1) u_2) v_4) (a + 1)
        (max (max (max (max (max (max (max (max (c + 1) u_2) v_4) v_2) u_1) u_2 v_4) v_1) (b + 1)) (max u_1 u_2) v_4)
        u_3)
-/
#guard_msgs (info) in
#check Big

end

section

variable [Category* (Type _)]

variable (C : Type _) [Category* C]

/--
error: Type mismatch
  D
has type
  Sort u_1
of sort `Type u_1` but is expected to have type
  Type ?u.772
of sort `Type (?u.772 + 1)`
-/
#guard_msgs (error) in
variable (D : Sort*) [Category* D]

/--
error: stuck at solving universe constraint
  max u_1 (u_2+1) =?= ?u.948+1
while trying to unify
  Sort (max u_1 (u_2 + 1)) : Type (max u_1 (u_2 + 1))
with
  Type ?u.948 : Type (?u.948 + 1)
-/
#guard_msgs (error) in
variable (E : Sort*) (F : Type*) [Category* (E → F)]

/--
error: stuck at solving universe constraint
  imax (u_2+1) u_1 =?= ?u.973+1
while trying to unify
  Sort (imax (u_2 + 1) u_1) : Type (imax (u_2 + 1) u_1)
with
  Type ?u.973 : Type (?u.973 + 1)
-/
#guard_msgs (error) in
variable (E : Sort*) (F : Type*) [Category* (F → E)]

end
