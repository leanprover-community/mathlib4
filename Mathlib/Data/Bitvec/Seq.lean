import Mathlib.Data.Bitvec.Basic

namespace Bitvec
abbrev Seq := Nat → Bool -- TODO: find a better name

namespace Seq

def ofBitvecFun {w : Nat} (x : Bitvec.Fun w) : Seq :=
  fun n => if h : n < w
    then x ⟨n, h⟩
    else false

def toBitvecFun {w : Nat} (x : Seq) : Bitvec.Fun w :=
  fun ⟨n, _⟩ => x n

theorem toBitvecFun_ofBitvecFun {w : Nat} {x : Fun w} :
 Seq.toBitvecFun (Seq.ofBitvecFun x) = x := by
 funext x
 simp [Seq.toBitvecFun, Seq.ofBitvecFun]

theorem ofBitvecFun_toBitvecFun_eq_width {w : Nat} {x : Seq} :
 ∀ i : Fin w, Seq.ofBitvecFun (@Seq.toBitvecFun w x) i = x i := by
 intro i
 simp [Seq.toBitvecFun, Seq.ofBitvecFun]

def zeroSeq : Nat → Bool := fun _ => false

def oneSeq : Nat → Bool := fun n => n == 0

def negOneSeq : Nat → Bool := fun _ => true

def andSeq : ∀ (_ _ : Nat → Bool), Nat → Bool := fun x y n => x n && y n

def orSeq : ∀ (_ _ : Nat → Bool), Nat → Bool := fun x y n => x n || y n

def xorSeq : ∀ (_ _ : Nat → Bool), Nat → Bool := fun x y n => xor (x n) (y n)

def notSeq : ∀ (_ : Nat → Bool), Nat → Bool := fun x n => !(x n)

def lsSeq (s : Nat → Bool) : Nat → Bool
  | 0 => false
  | (n+1) => s n

def addSeqAux (x y : Nat → Bool) : Nat → Bool × Bool
  | 0 => (_root_.xor (x 0) (y 0), x 0 && y 0)
  | n+1 =>
    let carry := (addSeqAux x y n).2
    let a := x (n + 1)
    let b := y (n + 1)
    (_root_.xor a (_root_.xor b carry), (a && b) || (b && carry) || (a && carry))

def addSeq (x y : Nat → Bool) : Nat → Bool :=
  fun n => (addSeqAux x y n).1

def subSeqAux (x y : Nat → Bool) : Nat → Bool × Bool
  | 0 => (_root_.xor (x 0) (y 0), !(x 0) && y 0)
  | n+1 =>
    let borrow := (subSeqAux x y n).2
    let a := x (n + 1)
    let b := y (n + 1)
    (_root_.xor a (_root_.xor b borrow), !a && b || ((!(_root_.xor a b)) && borrow))

def subSeq (x y : Nat → Bool) : Nat → Bool :=
  fun n => (subSeqAux x y n).1

def negSeqAux (x : Nat → Bool) : Nat → Bool × Bool
  | 0 => (x 0, !(x 0))
  | n+1 =>
    let borrow := (negSeqAux x n).2
    let a := x (n + 1)
    (_root_.xor (!a) borrow, !a && borrow)

def negSeq (x : Nat → Bool) : Nat → Bool :=
  fun n => (negSeqAux x n).1

def incrSeqAux (x : Nat → Bool) : Nat → Bool × Bool
  | 0 => (!(x 0), x 0)
  | n+1 =>
    let carry := (incrSeqAux x n).2
    let a := x (n + 1)
    (_root_.xor a carry, a && carry)

def incrSeq (x : Nat → Bool) : Nat → Bool :=
  fun n => (incrSeqAux x n).1

def decrSeqAux (x : Nat → Bool) : Nat → Bool × Bool
  | 0 => (!(x 0), !(x 0))
  | (n+1) =>
    let borrow := (decrSeqAux x n).2
    let a := x (n + 1)
    (_root_.xor a borrow, !a && borrow)

def decrSeq (x : Nat → Bool) : Nat → Bool :=
  fun n => (decrSeqAux x n).1

instance : Add Seq := ⟨addSeq⟩
instance : Sub Seq := ⟨subSeq⟩
instance : Neg Seq := ⟨negSeq⟩
instance : Xor Seq := ⟨xorSeq⟩
instance : Zero Seq := ⟨zeroSeq⟩
instance : One Seq := ⟨oneSeq⟩
instance : Inhabited Seq := ⟨zeroSeq⟩

def ofBitvec {w : Nat} (x : Bitvec w) : Seq := ofBitvecFun $ Bitvec.toFun x

@[reducible]
def toBitvec {w : Nat} (x : Seq) : Bitvec w := Bitvec.ofFun $ toBitvecFun x

-- def toBitvec_eq_bit {w : Nat} [NeZero w] (x : Seq) (n : Fin w) : (toBitvec x)[n] = x n.1 := by
--   simp [toBitvec, toBitvecFun, Bitvec.ofFun, Bitvec.toFun]

/- needs ofFun_toFun in bitvec
theorem toBitvec_ofBitvec {w : Nat} (x : Seq) :
  ∀ i : Fin w, ofBitvec (@toBitvec w x) i = x i := by
  simp [toBitvec, ofBitvec]
  intro i
  rw [ofFun_toFun, ofBitvecFun_toBitvecFun_eq_width]

theorem toBitvec_add_hom {x y : Seq} {w : Nat} : @toBitvec w x + @Seq.toBitvec w y = @Seq.toBitvec w (x + y) := by
  simp [toBitvec, toBitvecFun, addSeq, Bitvec.ofFun, Bitvec.add, Add.add, ofFun]
  sorry
-/

end Seq
end Bitvec
