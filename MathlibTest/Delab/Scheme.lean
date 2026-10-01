import Mathlib.AlgebraicGeometry.Restrict

universe u

open AlgebraicGeometry

variable (X : Scheme.{u}) (x : X) in
/-- info: x : ↥X -/
#guard_msgs in
#check x

variable (R : CommRingCat.{u}) (x : Spec R) in
/-- info: x : ↥(Spec R) -/
#guard_msgs in
#check x

variable (X : Scheme.{u}) (U : X.Opens) (x : U.toScheme) in
/-- info: x : ↥↑U -/
#guard_msgs in
#check x

variable (X : Scheme.{u}) (U : X.Opens) (x : U) in
/-- info: x : ↥U -/
#guard_msgs in
#check x

variable (X Y : Scheme.{u}) (f : X ⟶ Y) in
/-- info: f : X ⟶ Y -/
#guard_msgs in
#check f

variable (X Y : Scheme.{u}) (f : X ⟶ Y) in
/-- info: ⇑f : ↥X → ↥Y -/
#guard_msgs in
#check (f : X → Y)

variable (X Y : Scheme.{u}) (f : X ⟶ Y) (x : X) in
/-- info: f x : ↥Y -/
#guard_msgs in
#check f x

variable (X Y : Scheme.{u}) (f : X ⟶ Y) (U : Y.Opens) (x : f ⁻¹ᵁ U) in
/-- info: (f ∣_ U) x : ↥↑U -/
#guard_msgs in
#check (f ∣_ U) x
