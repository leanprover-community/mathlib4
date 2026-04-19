/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.StructurePolynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `Mathlib/RingTheory/WittVector/Basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : 𝕎 R` is an infinite sequence `ℕ → R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `Mathlib/RingTheory/WittVector/StructurePolynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a “carrying” operation.

## Main definitions

* `WittVector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `WittVector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


noncomputable section

/-- `WittVector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of `ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `WittVector p R` is a ring of characteristic `0`.
The canonical example is `WittVector p (ZMod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`. -/
@[informal "ring of Witt vectors"]
@[informal "ring of Witt vectors"]
structure WittVector (p : ℕ) (R : Type*) where mk' ::
  /-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

  This concept does not have a standard name in the literature.
  -/
  coeff : ℕ → R

/-- Construct a Witt vector `mk p x : 𝕎 R` from a sequence `x` of elements of `R`.

This is preferred over `WittVector.mk'` because it has `p` explicit.
-/
def WittVector.mk (p : ℕ) {R : Type*} (coeff : ℕ → R) : WittVector p R := mk' coeff

variable {p : ℕ}

/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/
local notation "𝕎" => WittVector p -- type as `\bbW`

namespace WittVector

variable {R : Type*}

@[ext]
theorem ext {x y : 𝕎 R} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [funext_iff, h]

theorem coeff_surjective (n : ℕ) :
    Function.Surjective (fun (x : 𝕎 R) ↦ x.coeff n) :=
  fun x ↦ ⟨(mk p fun _ ↦ x), rfl⟩

variable (p)

@[simp]
theorem coeff_mk (x : ℕ → R) : (mk p x).coeff = x :=
  rfl

/- These instances are not needed for the rest of the development,
but it is interesting to establish early on that `WittVector p` is a lawful functor. -/
instance : Functor (WittVector p) where
  map f v := mk p (f ∘ v.coeff)
  mapConst a _ := mk p fun _ => a

instance : LawfulFunctor (WittVector p) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

variable [hp : Fact p.Prime] [CommRing R]

open MvPolynomial

section RingOperations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def wittZero : ℕ → MvPolynomial (Fin 0 × ℕ) ℤ :=
  wittStructureInt p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def wittOne : ℕ → MvPolynomial (Fin 0 × ℕ) ℤ :=
  wittStructureInt p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def wittAdd : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 + X 1)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittNSMul (n : ℕ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittZSMul (n : ℤ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
def wittSub : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 - X 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def wittMul : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 * X 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def wittNeg : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (-X 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittPow (n : ℕ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (X 0 ^ n)

variable {p}


/-- An auxiliary definition used in `WittVector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `ℕ`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
def peval {k : ℕ} (φ : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → R) : R :=
  aeval (Function.uncurry x) φ

/-- Let `φ` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `ℕ`, and let `xᵢ` be a Witt vector for `0 ≤ i < k`.

`eval φ x` evaluates `φ` mapping the variable `X_(i, n)` to the `n`th coefficient of `xᵢ`.

Instantiating `φ` with certain polynomials defined in
`Mathlib/RingTheory/WittVector/StructurePolynomial.lean` establishes the
ring operations on `𝕎 R`. For example, `WittVector.wittAdd` is such a `φ` with `k = 2`;
evaluating this at `(x₀, x₁)` gives us the sum of two Witt vectors `x₀ + x₁`.
-/
def eval {k : ℕ} (φ : ℕ → MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → 𝕎 R) : 𝕎 R :=
  mk p fun n => peval (φ n) fun i => (x i).coeff

instance : Zero (𝕎 R) :=
  ⟨eval (wittZero p) ![]⟩

instance : Inhabited (𝕎 R) :=
  ⟨0⟩

instance : One (𝕎 R) :=
  ⟨eval (wittOne p) ![]⟩

instance : Add (𝕎 R) :=
  ⟨fun x y => eval (wittAdd p) ![x, y]⟩

instance : Sub (𝕎 R) :=
  ⟨fun x y => eval (wittSub p) ![x, y]⟩

instance hasNatScalar : SMul ℕ (𝕎 R) :=
  ⟨fun n x => eval (wittNSMul p n) ![x]⟩

instance hasIntScalar : SMul ℤ (𝕎 R) :=
  ⟨fun n x => eval (wittZSMul p n) ![x]⟩

instance : Mul (𝕎 R) :=
  ⟨fun x y => eval (wittMul p) ![x, y]⟩

instance : Neg (𝕎 R) :=
  ⟨fun x => eval (wittNeg p) ![x]⟩

instance hasNatPow : Pow (𝕎 R) ℕ :=
  ⟨fun x n => eval (wittPow p n) ![x]⟩

instance : NatCast (𝕎 R) :=
  ⟨Nat.unaryCast⟩

instance : IntCast (𝕎 R) :=
  ⟨Int.castDef⟩

end RingOperations

section WittStructureSimplifications

@[simp]
theorem wittZero_eq_zero (n : ℕ) : wittZero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittZero, wittStructureRat, bind₁, aeval_zero', constantCoeff_xInTermsOfW, map_zero,
    map_wittStructureInt]

@[simp]
theorem wittOne_zero_eq_one : wittOne p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittOne, wittStructureRat, xInTermsOfW_zero, map_one, bind₁_X_right,
    map_wittStructureInt]

@[simp]
theorem wittOne_pos_eq_zero (n : ℕ) (hn : 0 < n) : wittOne p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittOne, wittStructureRat, map_zero, map_one, map_wittStructureInt]
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [xInTermsOfW_eq]
  simp only [map_mul, map_sub, map_sum, map_pow, bind₁_X_right,
    bind₁_C_right]
  rw [sub_mul, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [one_mul, pow_zero]
    simp only [one_pow, one_mul, xInTermsOfW_zero, sub_self, bind₁_X_right]
  · intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zero hi0), zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero]
  · grind

@[simp]
theorem wittAdd_zero : wittAdd p 0 = X (0, 0) + X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittAdd, wittStructureRat, map_add, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
theorem wittSub_zero : wittSub p 0 = X (0, 0) - X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittSub, wittStructureRat, map_sub, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
theorem wittMul_zero : wittMul p 0 = X (0, 0) * X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittMul, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_mul, bind₁_X_right, map_wittStructureInt]

@[simp]
theorem wittNeg_zero : wittNeg p 0 = -X (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittNeg, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_neg, bind₁_X_right, map_wittStructureInt]

@[simp]
theorem constantCoeff_wittAdd (n : ℕ) : constantCoeff (wittAdd p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [add_zero, map_add, constantCoeff_X]

@[simp]
theorem constantCoeff_wittSub (n : ℕ) : constantCoeff (wittSub p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [sub_zero, map_sub, constantCoeff_X]

@[simp]
theorem constantCoeff_wittMul (n : ℕ) : constantCoeff (wittMul p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [mul_zero, map_mul, constantCoeff_X]

@[simp]
theorem constantCoeff_wittNeg (n : ℕ) : constantCoeff (wittNeg p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [neg_zero, map_neg, constantCoeff_X]

@[simp]
theorem constantCoeff_wittNSMul (m : ℕ) (n : ℕ) : constantCoeff (wittNSMul p m n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_nsmul, constantCoeff_X]

@[simp]
theorem constantCoeff_wittZSMul (z : ℤ) (n : ℕ) : constantCoeff (wittZSMul p z n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_zsmul, constantCoeff_X]

end WittStructureSimplifications

section Coeff

variable (R)

@[simp]
theorem zero_coeff (n : ℕ) : (0 : 𝕎 R).coeff n = 0 :=
  show (aeval _ (wittZero p n) : R) = 0 by simp only [wittZero_eq_zero, map_zero]

@[simp]
theorem one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1 :=
  show (aeval _ (wittOne p 0) : R) = 1 by simp only [wittOne_zero_eq_one, map_one]

@[simp]
theorem one_coeff_eq_of_pos (n : ℕ) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0 :=
  show (aeval _ (wittOne p n) : R) = 0 by simp only [hn, wittOne_pos_eq_zero, map_zero]

variable {p R}

@[simp]
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 2) :
    (![x, y] i).coeff = ![x.coeff, y.coeff] i := by fin_cases i <;> simp

theorem add_coeff (x y : 𝕎 R) (n : ℕ) :
    (x + y).coeff n = peval (wittAdd p n) ![x.coeff, y.coeff] := by
  simp [(· + ·), Add.add, eval]

theorem sub_coeff (x y : 𝕎 R) (n : ℕ) :
    (x - y).coeff n = peval (wittSub p n) ![x.coeff, y.coeff] := by
  simp [(· - ·), Sub.sub, eval]

theorem mul_coeff (x y : 𝕎 R) (n : ℕ) :
    (x * y).coeff n = peval (wittMul p n) ![x.coeff, y.coeff] := by
  simp [(· * ·), Mul.mul, eval]

theorem neg_coeff (x : 𝕎 R) (n : ℕ) : (-x).coeff n = peval (wittNeg p n) ![x.coeff] := by
  simp [Neg.neg, eval, Matrix.cons_fin_one]

theorem nsmul_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) :
    (m • x).coeff n = peval (wittNSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

theorem zsmul_coeff (m : ℤ) (x : 𝕎 R) (n : ℕ) :
    (m • x).coeff n = peval (wittZSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

theorem pow_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) :
    (x ^ m).coeff n = peval (wittPow p m n) ![x.coeff] := by
  simp [(· ^ ·), Pow.pow, eval, Matrix.cons_fin_one]

theorem add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [add_coeff, peval, Function.uncurry]

theorem mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [mul_coeff, peval, Function.uncurry]

end Coeff

theorem wittAdd_vars (n : ℕ) : (wittAdd p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittSub_vars (n : ℕ) : (wittSub p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittMul_vars (n : ℕ) : (wittMul p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittNeg_vars (n : ℕ) : (wittNeg p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittNSMul_vars (m : ℕ) (n : ℕ) :
    (wittNSMul p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittZSMul_vars (m : ℤ) (n : ℕ) :
    (wittZSMul p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

theorem wittPow_vars (m : ℕ) (n : ℕ) : (wittPow p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

end WittVector
