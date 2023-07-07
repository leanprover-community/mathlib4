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
  @[simp] theorem or_self         : x ||| x = x                     := by ext; simp
  @[simp] theorem or_not_self     : x ||| (~~~x) = (allOnes n)      := by ext; simp
  @[simp] theorem not_or_self     : (~~~x) ||| x = (allOnes n)      := by ext; simp
  @[simp] theorem or_zeroes       : x ||| 0 = x                     := by ext; simp
  @[simp] theorem or_ones         : x ||| (allOnes n) = (allOnes n) := by ext; simp

  @[simp] theorem and_self        : x &&& x = x                     := by ext; simp
  @[simp] theorem and_not_self    : x &&& (~~~x) = 0                := by ext; simp
  @[simp] theorem not_and_self    : (~~~x) &&& x = 0                := by ext; simp
  @[simp] theorem and_zeroes      : x &&& 0 = 0                     := by ext; simp
  @[simp] theorem and_ones        : x &&& (allOnes n) = x           := by ext; simp

  @[simp] theorem xor_self        : x ^^^ x = 0                     := by ext; simp
  @[simp] theorem xor_not_self    : x ^^^ (~~~x) = (allOnes n)      := by ext; simp
  @[simp] theorem not_xor_self    : (~~~x) ^^^ x = (allOnes n)      := by ext; simp
  @[simp] theorem xor_zeroes      : x ^^^ 0 = x                     := by ext; simp
  @[simp] theorem xor_ones        : x ^^^ (allOnes n) = ~~~x        := by ext; simp



  /-!
    Associativity and Commutativity
  -/
  theorem or_comm     : x ||| y = y ||| x                   := by ext; simp; apply Bool.or_comm
  theorem or_assoc    : (x ||| y) ||| z = x ||| (y ||| z)   := by ext; simp; apply Bool.or_assoc

  theorem and_comm    : x &&& y = y &&& x                   := by ext; simp; apply Bool.and_comm
  theorem and_assoc   : (x &&& y) &&& z = x &&& (y &&& z)   := by ext; simp; apply Bool.and_assoc

  theorem xor_comm    : x ^^^ y = y ^^^ x                   := by ext; simp; apply Bool.xor_comm
  theorem xor_assoc   : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z)   := by ext; simp -- Bool.xor_assoc is `@[simp]`, is that OK/safe?



  /-!
    Distributivity
  -/
  theorem and_or_distrib_left : x &&& (y ||| z) = (x &&& y) ||| (x &&& z) := by
    ext; simp; apply Bool.and_or_distrib_left

  theorem and_or_distrib_right : (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
    ext; simp; apply Bool.and_or_distrib_right

  theorem and_xor_distrib_left : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) := by
    ext; simp; apply Bool.and_xor_distrib_left

  theorem and_xor_distrib_right : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) := by
    ext; simp; apply Bool.and_xor_distrib_right

  theorem or_and_distrib_left : x ||| (y &&& z) = (x ||| y) &&& (x ||| z) := by
    ext; simp; apply Bool.or_and_distrib_left

  theorem or_and_distrib_right : (x &&& y) ||| z = (x ||| z) &&& (y ||| z) := by
    ext; simp; apply Bool.or_and_distrib_right



  /--
    De Morgan's laws for bitvectors
  -/
  @[simp]
  theorem not_and :  ~~~(x &&& y) = (~~~x) ||| (~~~y) := by
    ext; simp

  @[simp]
  theorem not_or  :  ~~~(x ||| y) = (~~~x) &&& (~~~y) := by
    ext; simp



  /-!
    Shifts
  -/

  -- @[simp]
  -- theorem shl_succ (x : Bitvec n) :
  --     (x <<< (@Bitvec.ofNat n <| m + 1)) = (x.snoc false |>.tail) := by
  --   simp[(· <<< ·), ShiftLeft.shiftLeft, Bitvec.shl]
  --   sorry



  -- theorem shl_eq_mapAccumr :
  --     x <<< y
  --     = (Vector.mapAccumr (fun b s =>
  --         (s.snoc b |>.tail, (s.snoc b).head)
  --       ) x (Vector.replicate (y.toNat) false)).snd := by
  --   conv_lhs => {rw[←ofNat_toNat y]}
  --   induction y.toNat
  --   . simp
  --     have : Vector.replicate 0 false = Vector.nil := rfl
  --     rw[this]
  --     simp
  --     clear z shl_eq_mapAccumr y
  --     induction x using Vector.inductionOn
  --     . rfl
  --     . simp; congr
  --   next ih =>
  --     simp
  --     clear z shl_eq_mapAccumr y
  --     induction x using Vector.revInductionOn
  --     . rfl
  --     . simp_all

end Bitvec
