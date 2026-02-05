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
