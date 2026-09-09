import Mathlib

universe u

variable (R : Type u) [Semiring R]
/-- info: ↧R : SemiRingCat -/
#guard_msgs in
#check SemiRingCat.of R

variable (R : Type u) [CommSemiring R]
/-- info: ↧R : CommSemiRingCat -/
#guard_msgs in
#check CommSemiRingCat.of R

variable (R : Type u) [Ring R] in
/-- info: ↧R : RingCat -/
#guard_msgs in
#check RingCat.of R

variable (R : Type u) [CommRing R] in
/-- info: ↧R : CommRingCat -/
#guard_msgs in
#check CommRingCat.of R

variable (X : Type u) [TopologicalSpace X] in
/-- info: ↧X : TopCat -/
#guard_msgs in
#check TopCat.of X

variable (X : Type u) [TopologicalSpace X] in
/-- info: ↧X : TopCat -/
#guard_msgs in
#check TopCat.of X

variable (X : Type u) [Fintype X] in
/-- info: ↧X : FintypeCat -/
#guard_msgs in
#check FintypeCat.of X

variable (R : Type u) [TopologicalSpace R] [CommRing R] [IsTopologicalRing R] in
/-- info: ↧R : TopCommRingCat -/
#guard_msgs in
#check TopCommRingCat.of R
