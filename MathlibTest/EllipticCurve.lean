import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Test for kernel reduction of elliptic curve `nsmul`

In `addOrderOf_basepoint`, the `rfl` tests that the kernel is able to reduce the `nsmul`
operation on an elliptic curve to check an equality. `nsmul` on elliptic curves implements
multiplication by doubling and should be relatively fast.
-/

open WeierstrassCurve Affine Point

instance : Fact (Nat.Prime 29) := by decide
instance : Fact (Nat.Prime 37) := by decide

/- A tiny example curve from Example 3.5,
D. Hankerson, A. Menezes, S. Vanstone, Guide to Elliptic Curve Cryptography, Springer, 2004 -/
abbrev curve : Affine (ZMod 29) := ⟨0, 0, 0, 4, 20⟩

def basepoint : curve.Point :=
  .some (x := 1) (y := 5) <| by
    rw [nonsingular_iff, equation_iff]
    decide

set_option maxRecDepth 300 in
theorem addOrderOf_basepoint : addOrderOf basepoint = 37 := by
  apply addOrderOf_eq_prime
  · rfl
  · simp [basepoint]
