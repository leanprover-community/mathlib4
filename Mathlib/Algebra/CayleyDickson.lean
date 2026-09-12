/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The Cayley–Dickson construction

Given a (possibly non-associative) ring `A` with a star operation, the Cayley–Dickson
construction produces the algebra `CayleyDickson A` of pairs of elements of `A`,
multiplied by

`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`,

with the star operation `star ⟨a, b⟩ = ⟨star a, -b⟩`. Iterating the construction starting
from the quaternions produces the octonions, the sedenions, the trigintaduonions, and so
on; see `Mathlib/Algebra/Octonion.lean`.

The construction preserves `NonAssocRing` and `StarRing`, but not associativity, so the
tower can be iterated indefinitely inside these classes.

The doubling unit `ℓ = ⟨0, 1⟩` satisfies `ℓ * ℓ = -1` and, crucially,
`ℓ * (ℓ * x) = -x` (`CayleyDickson.unit_mul_unit_mul`) *at every level of the tower* —
the proof only uses that `star` is an involution on `A`. Consequently left multiplication
by `ℓ` is a complex structure on every Cayley–Dickson algebra (even the non-alternative
ones with zero divisors, such as the sedenions), which is what the hypercomplex
(octonion, sedenion, …) Fourier transform needs; this is used in a follow-up PR to derive
Plancherel's theorem for these transforms from the vector-valued `L²` Fourier theory.

## Main definitions

* `CayleyDickson A`: the Cayley–Dickson double of `A`.
* `CayleyDickson.unit`: the doubling unit `ℓ`.

## TODO

* alternativity of the double of an associative star ring, the multiplicative norm for
  composition algebras.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002)

-/

@[expose] public section

/-- The Cayley–Dickson double of `A`: pairs of elements of `A` with the multiplication
`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`. -/
@[ext]
structure CayleyDickson (A : Type*) where
  /-- The first component. -/
  fst : A
  /-- The second component. -/
  snd : A

namespace CayleyDickson

variable {A S : Type*}

/-! ### The additive and module structure, componentwise -/

section AddGroup

variable [AddCommGroup A]

instance : Zero (CayleyDickson A) := ⟨⟨0, 0⟩⟩
instance : Add (CayleyDickson A) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (CayleyDickson A) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (CayleyDickson A) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance [SMul S A] : SMul S (CayleyDickson A) :=
  ⟨fun s x => ⟨s • x.fst, s • x.snd⟩⟩

@[simp] theorem zero_fst : (0 : CayleyDickson A).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : CayleyDickson A).snd = 0 := rfl
@[simp] theorem add_fst (x y : CayleyDickson A) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem add_snd (x y : CayleyDickson A) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem neg_fst (x : CayleyDickson A) : (-x).fst = -x.fst := rfl
@[simp] theorem neg_snd (x : CayleyDickson A) : (-x).snd = -x.snd := rfl
@[simp] theorem sub_fst (x y : CayleyDickson A) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem sub_snd (x y : CayleyDickson A) : (x - y).snd = x.snd - y.snd := rfl
omit [AddCommGroup A] in
@[simp] theorem smul_fst [SMul S A] (s : S) (x : CayleyDickson A) :
    (s • x).fst = s • x.fst := rfl

omit [AddCommGroup A] in
@[simp] theorem smul_snd [SMul S A] (s : S) (x : CayleyDickson A) :
    (s • x).snd = s • x.snd := rfl

/-- The underlying pair of a Cayley–Dickson number. -/
def toProd (x : CayleyDickson A) : A × A := (x.fst, x.snd)

omit [AddCommGroup A] in
theorem toProd_injective : Function.Injective (toProd (A := A)) := fun x y h => by
  cases x
  cases y
  simpa [toProd, Prod.ext_iff] using h

instance : AddCommGroup (CayleyDickson A) :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- `toProd` as an additive monoid homomorphism. -/
def toProdHom : CayleyDickson A →+ A × A where
  toFun := toProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule [Semiring S] [Module S A] : Module S (CayleyDickson A) :=
  toProd_injective.module S toProdHom fun _ _ => rfl

variable (S) in
/-- `toProd` as a linear equivalence. -/
@[simps apply]
def toProdLinearEquiv [Semiring S] [Module S A] : CayleyDickson A ≃ₗ[S] A × A where
  toFun := toProd
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [Semiring S] [Module S A] [Module.Finite S A] :
    Module.Finite S (CayleyDickson A) :=
  Module.Finite.equiv (toProdLinearEquiv S).symm

end AddGroup

/-! ### The multiplicative and star structure -/

section Ring

variable [NonUnitalNonAssocRing A] [StarRing A]

instance : Mul (CayleyDickson A) :=
  ⟨fun x y => ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩⟩

theorem mul_def (x y : CayleyDickson A) :
    x * y = ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩ :=
  rfl

@[simp] theorem mul_fst (x y : CayleyDickson A) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem mul_snd (x y : CayleyDickson A) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

instance : NonUnitalNonAssocRing (CayleyDickson A) where
  left_distrib _ _ _ := by
    ext <;> simp [mul_add, add_mul, star_add, sub_eq_add_neg] <;> abel
  right_distrib _ _ _ := by
    ext <;> simp [mul_add, add_mul, sub_eq_add_neg] <;> abel
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

instance : Star (CayleyDickson A) := ⟨fun x => ⟨star x.fst, -x.snd⟩⟩

@[simp] theorem star_fst (x : CayleyDickson A) : (star x).fst = star x.fst := rfl
@[simp] theorem star_snd (x : CayleyDickson A) : (star x).snd = -x.snd := rfl

instance : StarRing (CayleyDickson A) where
  star_involutive _ := by ext <;> simp
  star_add _ _ := by ext <;> simp [add_comm]
  star_mul _ _ := by ext <;> simp [star_mul, sub_eq_add_neg]

instance [Monoid S] [DistribMulAction S A] [Star S] [TrivialStar S] [StarModule S A] :
    StarModule S (CayleyDickson A) :=
  ⟨fun s x => by ext <;> simp [star_smul, star_trivial, smul_neg]⟩

theorem smul_mul_assoc' [Monoid S] [DistribMulAction S A] [SMulCommClass S A A]
    [IsScalarTower S A A] (s : S) (x y : CayleyDickson A) :
    (s • x) * y = s • (x * y) := by
  ext <;> simp [smul_sub, smul_add, mul_smul_comm, smul_mul_assoc]

theorem mul_smul_comm' [Monoid S] [Star S] [TrivialStar S] [DistribMulAction S A]
    [StarModule S A] [SMulCommClass S A A] [IsScalarTower S A A] (s : S)
    (x y : CayleyDickson A) : x * (s • y) = s • (x * y) := by
  have hstar : ∀ a : A, star (s • a) = s • star a := fun a => by
    rw [star_smul, star_trivial]
  ext <;> simp [hstar, smul_sub, smul_add, mul_smul_comm, smul_mul_assoc]

/-- The self-action compatibility propagates up the Cayley–Dickson tower. -/
instance [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [IsScalarTower S A A] :
    IsScalarTower S (CayleyDickson A) (CayleyDickson A) :=
  ⟨fun s x y => smul_mul_assoc' s x y⟩

/-- The self-action compatibility propagates up the Cayley–Dickson tower. -/
instance [Monoid S] [Star S] [TrivialStar S] [DistribMulAction S A] [StarModule S A]
    [SMulCommClass S A A] [IsScalarTower S A A] :
    SMulCommClass S (CayleyDickson A) (CayleyDickson A) :=
  ⟨fun s x y => (mul_smul_comm' s x y).symm⟩

end Ring

section Unital

variable [NonAssocRing A]

instance : One (CayleyDickson A) := ⟨⟨1, 0⟩⟩

@[simp] theorem one_fst : (1 : CayleyDickson A).fst = 1 := rfl
@[simp] theorem one_snd : (1 : CayleyDickson A).snd = 0 := rfl

instance : NatCast (CayleyDickson A) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (CayleyDickson A) := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem natCast_fst (n : ℕ) : (n : CayleyDickson A).fst = n := rfl
@[simp] theorem natCast_snd (n : ℕ) : (n : CayleyDickson A).snd = 0 := rfl
@[simp] theorem intCast_fst (n : ℤ) : (n : CayleyDickson A).fst = n := rfl
@[simp] theorem intCast_snd (n : ℤ) : (n : CayleyDickson A).snd = 0 := rfl

variable [StarRing A]

instance : NonAssocRing (CayleyDickson A) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  natCast_zero := by ext <;> simp
  natCast_succ _ := by ext <;> simp
  intCast_ofNat _ := by ext <;> simp
  intCast_negSucc _ := by ext <;> simp [Int.negSucc_eq]

/-! ### The doubling unit -/

variable (A) in
/-- The Cayley–Dickson doubling unit `ℓ = ⟨0, 1⟩`. -/
def unit : CayleyDickson A := ⟨0, 1⟩

omit [StarRing A] in
@[simp] theorem unit_fst : (unit A).fst = 0 := rfl

omit [StarRing A] in
@[simp] theorem unit_snd : (unit A).snd = 1 := rfl

@[simp] theorem unit_mul_unit : unit A * unit A = -1 := by
  ext <;> simp

theorem unit_mul (x : CayleyDickson A) : unit A * x = ⟨-star x.snd, star x.fst⟩ := by
  ext <;> simp

/-- The left alternative law at the doubling unit: `ℓ * (ℓ * x) = (ℓ * ℓ) * x = -x`.
This holds at *every* level of the Cayley–Dickson tower — the proof uses only that
`star` is an involution — even when the algebra is not alternative (e.g. the
sedenions). Left multiplication by `ℓ` is therefore always a complex structure. -/
@[simp] theorem unit_mul_unit_mul (x : CayleyDickson A) : unit A * (unit A * x) = -x := by
  ext <;> simp

end Unital

end CayleyDickson
