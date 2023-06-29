import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Bitvec.ConstantLemmas
import Mathlib.Data.Bitvec.Tactic
import Mathlib.Data.Vector.MapLemmas



namespace Bitvec
  open Bitvec (not)
  variable (x y z : Bitvec n)

  /-!
    How do the operations interact with constant patterns `000000...` and `11111....`, and what
    happens if we supply the same argument twice
  -/
  @[simp] theorem or_self         : x.or x = x                      := by ext; simp
  @[simp] theorem or_not_self     : x.or (not x) = (allOnes n)      := by ext; simp
  @[simp] theorem not_or_self     : (not x).or x = (allOnes n)      := by ext; simp
  @[simp] theorem or_zeroes       : x.or 0 = x                      := by ext; simp
  @[simp] theorem or_ones         : x.or (allOnes n) = (allOnes n)  := by ext; simp

  @[simp] theorem and_self        : x.and x = x                     := by ext; simp
  @[simp] theorem and_not_self    : x.and (not x) = 0               := by ext; simp
  @[simp] theorem not_and_self    : (not x).and x = 0               := by ext; simp
  @[simp] theorem and_zeroes      : x.and 0 = 0                     := by ext; simp
  @[simp] theorem and_ones        : x.and (allOnes n) = x           := by ext; simp

  @[simp] theorem xor_self        : x.xor x = 0                     := by ext; simp
  @[simp] theorem xor_not_self    : x.xor (not x) = (allOnes n)     := by ext; simp
  @[simp] theorem not_xor_self    : (not x).xor x = (allOnes n)     := by ext; simp
  @[simp] theorem xor_zeroes      : x.xor 0 = x                     := by ext; simp
  @[simp] theorem xor_ones        : x.xor (allOnes n) = x.not       := by ext; simp



  /-!
    Associativity and Commutativity
  -/
  theorem or_comm     : x.or y = y.or x                   := by ext; simp; apply Bool.or_comm
  theorem or_assoc    : (x.or y).or z = x.or (y.or z)     := by ext; simp; apply Bool.or_assoc

  theorem and_comm    : x.and y = y.and x                 := by ext; simp; apply Bool.and_comm
  theorem and_assoc   : (x.and y).and z = x.and (y.and z) := by ext; simp; apply Bool.and_assoc

  theorem xor_comm    : x.xor y = y.xor x                 := by ext; simp; apply Bool.xor_comm
  theorem xor_assoc   : (x.xor y).xor z = x.xor (y.xor z) := by ext; simp -- Bool.xor_assoc is `@[simp]`, is that OK/safe?



  /-!
    Distributivity
  -/
  theorem and_or_distrib_left : x.and (y.or z) = (x.and y).or (x.and z) := by
    ext; simp; apply Bool.and_or_distrib_left

  theorem and_or_distrib_right : (x.or y).and z = (x.and z).or (y.and z) := by
    ext; simp; apply Bool.and_or_distrib_right

  theorem and_xor_distrib_left : x.and (y.xor z) = (x.and y).xor (x.and z) := by
    ext; simp; apply Bool.and_xor_distrib_left

  theorem and_xor_distrib_right : (x.xor y).and z = (x.and z).xor (y.and z) := by
    ext; simp; apply Bool.and_xor_distrib_right

  theorem or_and_distrib_left : x.or (y.and z) = (x.or y).and (x.or z) := by
    ext; simp; apply Bool.or_and_distrib_left

  theorem or_and_distrib_right : (x.and y).or z = (x.or z).and (y.or z) := by
    ext; simp; apply Bool.or_and_distrib_right



  /--
    De Morgan's laws for bitvectors
  -/
  @[simp]
  theorem not_and : not (x.and y) = (not x).or (not y) := by
    ext; simp

  @[simp]
  theorem not_or  : not (x.or y) = (not x).and (not y) := by
    ext; simp

end Bitvec
