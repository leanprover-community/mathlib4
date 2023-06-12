import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas


/-!
  Some theorems & defintions I needed along the way, but which should find their home elsewhere
-/
section ShouldMove

/--
  The bitwise complement, i.e., take the complement of each bit
-/
def Bitvec.compl : Bitvec n → Bitvec n :=
  Vector.map not

instance : Complement (Bitvec n) := ⟨Bitvec.compl⟩



@[simp]
theorem Bitvec.get_map : get (Vector.map f v) i = f (get v i) := by
  simp only [get, Vector.get_map]

@[simp]
theorem Bitvec.get_map₂ : get (Vector.map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  simp only [get, Vector.get_map₂]

end ShouldMove








namespace Bitvec

variable {width : Nat}

section Constants

  /-- The bitvector of all zeroes: `0000..`  -/
  abbrev zeroes : Bitvec width
    := 0

  /-- The bitvector of all ones: `1111..`  -/
  def ones : Bitvec width
    := Vector.replicate width true

  @[simp]
  theorem get_replicate_val_eq_val : get (Vector.replicate width val) i = val := by
    induction width
    case zero =>
      exact Fin.elim0 i
    case succ n ih =>
      cases i using Fin.cases
      case H0 => rfl
      case Hs => apply ih

  /-- Every bit in `zeroes` is `0`/`false` -/
  @[simp]
  theorem get_zeroes_eq_false : get zeroes i = false := get_replicate_val_eq_val

  /-- Every bit in `ones` is `1`/`true` -/
  @[simp]
  theorem get_ones_eq_true : get ones i = true := get_replicate_val_eq_val


  /-- The all-ones bit pattern is also spelled `-1` -/
  @[simp]
  theorem get_minus_one : get (-1 : Bitvec width) i = true := by
    simp[OfNat.ofNat, Neg.neg, Bitvec.neg, One.one]
    sorry

  @[simp]
  theorem minus_one_eq_ones : (-1 : Bitvec width) = ones := by
    ext i; rw[get_ones_eq_true]; exact get_minus_one

end Constants


section Bitwise
  variable (x y z : Bitvec width)

  /-!
    First, we show that these bitwise operations are indeed just determined bit-by-bit, by showing
    how they interact with `get`
  -/

  @[simp]
  theorem get_or : get (x.or y) i = (get x i || get y i) := by
    simp only [Bitvec.or, get_map₂]

  @[simp]
  theorem get_and : get (x.and y) i = (get x i && get y i) := by
    simp only [Bitvec.and, get_map₂]

  @[simp]
  theorem get_xor : get (x.xor y) i = xor (get x i) (get y i) := by
    simp only [Bitvec.xor, get_map₂]

  @[simp]
  theorem get_compl : get (x.compl) i = not (get x i) := by
    simp only [Bitvec.compl, get_map]


  /-!
    How do the operations interact with constant patterns `000000...` and `11111....`, and what
    happens if we supply the same argument twice
  -/
  @[simp] theorem or_self         : x.or x = x                    := by ext; simp
  @[simp] theorem or_compl_self   : x.or (compl x) = ones         := by ext; simp
  @[simp] theorem compl_or_self   : (compl x).or x = ones         := by ext; simp
  @[simp] theorem or_zeroes       : x.or 0 = x                    := by ext; simp
  @[simp] theorem or_ones         : x.or ones = ones              := by ext; simp

  @[simp] theorem and_self        : x.and x = x                   := by ext; simp
  @[simp] theorem and_compl_self  : x.and (compl x) = 0           := by ext; simp
  @[simp] theorem compl_and_self  : (compl x).and x = 0           := by ext; simp
  @[simp] theorem and_zeroes      : x.and 0 = 0                   := by ext; simp
  @[simp] theorem and_ones        : x.and ones = x                := by ext; simp

  @[simp] theorem xor_self        : x.xor x = 0                   := by ext; simp
  @[simp] theorem xor_compl_self  : x.xor (compl x) = ones        := by ext; simp
  @[simp] theorem compl_xor_self  : (compl x).xor x = ones        := by ext; simp
  @[simp] theorem xor_zeroes      : x.xor 0 = x                   := by ext; simp
  @[simp] theorem xor_ones        : x.xor ones = x.compl          := by ext; simp


  theorem not_zeroes              : compl (@ones width) = zeroes  := by ext; simp
  theorem not_ones                : compl (@zeroes width) = ones  := by ext; simp



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
  theorem not_and : compl (x.and y) = (compl x).or (compl y) := by
    ext; simp

  @[simp]
  theorem not_or  : compl (x.or y) = (compl x).and (compl y) := by
    ext; simp





end Bitwise


end Bitvec
