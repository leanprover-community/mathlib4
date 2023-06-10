import Mathlib.Data.Bitvec.Basic
import Mathlib.Data.Bitvec.Core


/-!
  Some theorems & defintions I needed along the way, but which should find their home elsewhere
-/
section ShouldMove

theorem Vector.replicate.unfold : Vector.replicate (n+1) val = val ::ᵥ (Vector.replicate n val) :=
  rfl

@[simp]
theorem Vector.map.unfold_cons : Vector.map f (hd ::ᵥ tl) = f hd ::ᵥ (Vector.map f tl) :=
  rfl

@[simp]
theorem Vector.map₂.unfold_cons : Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂)
                                  = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
theorem Vector.get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) :
    Vector.get (Vector.map₂ f v₁ v₂) i = f (Vector.get v₁ i) (Vector.get v₂ i) := by
  induction n
  case zero =>
    exact Fin.elim0 i
  case succ n ih =>
    cases v₁ using Vector.cases with | cons x_hd x_tl =>
    cases v₂ using Vector.cases with | cons y_hd y_tl =>
    simp only [Vector.map₂.unfold_cons]
    cases i using Fin.cases
    . simp only [get_zero, head_cons]
    . simp only [get_cons_succ, ih]

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
      case Hs =>
        simp[Vector.replicate.unfold]
        apply ih

  /-- Every bit in `zeroes` is `0`/`false` -/
  @[simp]
  theorem get_zeroes_eq_false : get zeroes i = false := get_replicate_val_eq_val

  /-- Every bit in `ones` is `1`/`true` -/
  @[simp]
  theorem get_ones_eq_true : get ones i = true := get_replicate_val_eq_val

  /-- The all-ones bit pattern is also spelled `-1` -/
  @[simp]
  theorem get_minus_one : get (-1 : Bitvec width) i = true := by
    sorry

  @[simp]
  theorem minus_one_eq_ones : (-1 : Bitvec width) = ones := by
    ext i; rw[get_ones_eq_true]; exact get_minus_one

end Constants


section Bitwise
  variable (x y : Bitvec width)

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
  @[simp] theorem x_or_x_eq_x             : x.or x = x            := by ext; simp
  @[simp] theorem x_or_not_x_eq_ones      : x.or x.compl = ones   := by ext; simp
  @[simp] theorem x_or_zeroes_eq_x        : x.or 0 = x            := by ext; simp
  @[simp] theorem x_or_ones_eq_ones       : x.or ones = ones      := by ext; simp

  @[simp] theorem x_and_x_eq_x            : x.and x = x           := by ext; simp
  @[simp] theorem x_and_zeroes_eq_zeroes  : x.and 0 = 0           := by ext; simp
  @[simp] theorem x_and_ones_eq_x         : x.and ones = x        := by ext; simp

  @[simp] theorem x_xor_x_eq_0            : x.xor x = 0           := by ext; simp
  @[simp] theorem x_xor_zeroes_eq_x       : x.xor 0 = x           := by ext; simp
  @[simp] theorem x_xor_ones_eq_not_x     : x.xor ones = x.compl  := by ext; simp


  theorem not_zeroes_eq_ones              : (@ones width).compl = zeroes := by ext; simp
  theorem not_ones_eq_zeroes              : (@zeroes width).compl = ones := by ext; simp



  /-!
    Associativity, Commutativity
  -/
  theorem or_comm     : x.or y = y.or x                   := by ext; simp; apply Bool.or_comm
  theorem or_assoc    : (x.or y).or z = x.or (y.or z)     := by ext; simp; apply Bool.or_assoc

  theorem and_comm    : x.and y = y.and x                 := by ext; simp; apply Bool.and_comm
  theorem and_assoc   : (x.and y).and z = x.and (y.and z) := by ext; simp; apply Bool.and_assoc

  theorem xor_comm    : x.xor y = y.xor x                 := by ext; simp; apply Bool.xor_comm
  theorem xor_assoc   : (x.xor y).xor z = x.xor (y.xor z) := by ext; simp -- Bool.xor_assoc is `@[simp]`, is that OK/safe?


end Bitwise


end Bitvec
