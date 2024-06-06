/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Algebra.Module.Opposites

#align_import linear_algebra.clifford_algebra.conjugation from "leanprover-community/mathlib"@"34020e531ebc4e8aac6d449d9eecbcd1508ea8d0"

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `CliffordAlgebra.involute`: the grade involution, negating each basis vector
* `CliffordAlgebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `CliffordAlgebra.involute_involutive`
* `CliffordAlgebra.reverse_involutive`
* `CliffordAlgebra.reverse_involute_commute`
* `CliffordAlgebra.involute_mem_evenOdd_iff`
* `CliffordAlgebra.reverse_mem_evenOdd_iff`

-/


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

section Involute

/-- Grade involution, inverting the sign of each basis vector. -/
def involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩
#align clifford_algebra.involute CliffordAlgebra.involute

@[simp]
theorem involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  lift_ι_apply _ _ m
#align clifford_algebra.involute_ι CliffordAlgebra.involute_ι

@[simp]
theorem involute_comp_involute : involute.comp involute = AlgHom.id R (CliffordAlgebra Q) := by
  ext; simp
#align clifford_algebra.involute_comp_involute CliffordAlgebra.involute_comp_involute

theorem involute_involutive : Function.Involutive (involute : _ → CliffordAlgebra Q) :=
  AlgHom.congr_fun involute_comp_involute
#align clifford_algebra.involute_involutive CliffordAlgebra.involute_involutive

@[simp]
theorem involute_involute : ∀ a : CliffordAlgebra Q, involute (involute a) = a :=
  involute_involutive
#align clifford_algebra.involute_involute CliffordAlgebra.involute_involute

/-- `CliffordAlgebra.involute` as an `AlgEquiv`. -/
@[simps!]
def involuteEquiv : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom involute involute (AlgHom.ext <| involute_involute)
    (AlgHom.ext <| involute_involute)
#align clifford_algebra.involute_equiv CliffordAlgebra.involuteEquiv

end Involute

section Reverse

open MulOpposite

/-- `CliffordAlgebra.reverse` as an `AlgHom` to the opposite algebra -/
def reverseOp : CliffordAlgebra Q →ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  CliffordAlgebra.lift Q
    ⟨(MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ ι Q, fun m => unop_injective <| by simp⟩

@[simp]
theorem reverseOp_ι (m : M) : reverseOp (ι Q m) = op (ι Q m) := lift_ι_apply _ _ _

/-- `CliffordAlgebra.reverseEquiv` as an `AlgEquiv` to the opposite algebra -/
@[simps! apply]
def reverseOpEquiv : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.unop.injective <| hom_ext <| LinearMap.ext fun _ => by simp)
    (hom_ext <| LinearMap.ext fun _ => by simp)

@[simp]
theorem reverseOpEquiv_opComm :
    AlgEquiv.opComm (reverseOpEquiv (Q := Q)) = reverseOpEquiv.symm := rfl

/-- Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature. -/
def reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (opLinearEquiv R).symm.toLinearMap.comp reverseOp.toLinearMap
#align clifford_algebra.reverse CliffordAlgebra.reverse

@[simp] theorem unop_reverseOp (x : CliffordAlgebra Q) : (reverseOp x).unop = reverse x := rfl

@[simp] theorem op_reverse (x : CliffordAlgebra Q) : op (reverse x) = reverseOp x := rfl

@[simp]
theorem reverse_ι (m : M) : reverse (ι Q m) = ι Q m := by simp [reverse]
#align clifford_algebra.reverse_ι CliffordAlgebra.reverse_ι

@[simp]
theorem reverse.commutes (r : R) :
    reverse (algebraMap R (CliffordAlgebra Q) r) = algebraMap R _ r :=
  op_injective <| reverseOp.commutes r
#align clifford_algebra.reverse.commutes CliffordAlgebra.reverse.commutes

@[simp]
theorem reverse.map_one : reverse (1 : CliffordAlgebra Q) = 1 :=
  op_injective reverseOp.map_one
#align clifford_algebra.reverse.map_one CliffordAlgebra.reverse.map_one

@[simp]
theorem reverse.map_mul (a b : CliffordAlgebra Q) :
    reverse (a * b) = reverse b * reverse a :=
  op_injective (reverseOp.map_mul a b)
#align clifford_algebra.reverse.map_mul CliffordAlgebra.reverse.map_mul

@[simp]
theorem reverse_involutive : Function.Involutive (reverse (Q := Q)) :=
  AlgHom.congr_fun reverseOpEquiv.symm_comp
#align clifford_algebra.reverse_involutive CliffordAlgebra.reverse_involutive

@[simp]
theorem reverse_comp_reverse :
    reverse.comp reverse = (LinearMap.id : _ →ₗ[R] CliffordAlgebra Q) :=
  LinearMap.ext reverse_involutive

@[simp]
theorem reverse_reverse : ∀ a : CliffordAlgebra Q, reverse (reverse a) = a :=
  reverse_involutive
#align clifford_algebra.reverse_reverse CliffordAlgebra.reverse_reverse

/-- `CliffordAlgebra.reverse` as a `LinearEquiv`. -/
@[simps!]
def reverseEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  LinearEquiv.ofInvolutive reverse reverse_involutive
#align clifford_algebra.reverse_equiv CliffordAlgebra.reverseEquiv

theorem reverse_comp_involute :
    reverse.comp involute.toLinearMap =
      (involute.toLinearMap.comp reverse : _ →ₗ[R] CliffordAlgebra Q) := by
  ext x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  induction x using CliffordAlgebra.induction with
  | algebraMap => simp
  | ι => simp
  | mul a b ha hb => simp only [ha, hb, reverse.map_mul, AlgHom.map_mul]
  | add a b ha hb => simp only [ha, hb, reverse.map_add, AlgHom.map_add]
#align clifford_algebra.reverse_comp_involute CliffordAlgebra.reverse_comp_involute

/-- `CliffordAlgebra.reverse` and `CliffordAlgebra.involute` commute. Note that the composition
is sometimes referred to as the "clifford conjugate". -/
theorem reverse_involute_commute : Function.Commute (reverse (Q := Q)) involute :=
  LinearMap.congr_fun reverse_comp_involute
#align clifford_algebra.reverse_involute_commute CliffordAlgebra.reverse_involute_commute

theorem reverse_involute :
    ∀ a : CliffordAlgebra Q, reverse (involute a) = involute (reverse a) :=
  reverse_involute_commute
#align clifford_algebra.reverse_involute CliffordAlgebra.reverse_involute

end Reverse

/-!
### Statements about conjugations of products of lists
-/


section List

/-- Taking the reverse of the product a list of $n$ vectors lifted via `ι` is equivalent to
taking the product of the reverse of that list. -/
theorem reverse_prod_map_ι :
    ∀ l : List M, reverse (l.map <| ι Q).prod = (l.map <| ι Q).reverse.prod
  | [] => by simp
  | x::xs => by simp [reverse_prod_map_ι xs]
#align clifford_algebra.reverse_prod_map_ι CliffordAlgebra.reverse_prod_map_ι

/-- Taking the involute of the product a list of $n$ vectors lifted via `ι` is equivalent to
premultiplying by ${-1}^n$. -/
theorem involute_prod_map_ι :
    ∀ l : List M, involute (l.map <| ι Q).prod = (-1 : R) ^ l.length • (l.map <| ι Q).prod
  | [] => by simp
  | x::xs => by simp [pow_succ, involute_prod_map_ι xs]
#align clifford_algebra.involute_prod_map_ι CliffordAlgebra.involute_prod_map_ι

end List

/-!
### Statements about `Submodule.map` and `Submodule.comap`
-/


section Submodule

variable (Q)

section Involute

theorem submodule_map_involute_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      p.comap (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap :=
  Submodule.map_equiv_eq_comap_symm involuteEquiv.toLinearEquiv _
#align clifford_algebra.submodule_map_involute_eq_comap CliffordAlgebra.submodule_map_involute_eq_comap

@[simp]
theorem ι_range_map_involute :
    (ι Q).range.map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_neg _)
#align clifford_algebra.ι_range_map_involute CliffordAlgebra.ι_range_map_involute

@[simp]
theorem ι_range_comap_involute :
    (ι Q).range.comap (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) := by
  rw [← submodule_map_involute_eq_comap, ι_range_map_involute]
#align clifford_algebra.ι_range_comap_involute CliffordAlgebra.ι_range_comap_involute

@[simp]
theorem evenOdd_map_involute (n : ZMod 2) :
    (evenOdd Q n).map (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_involute]
#align clifford_algebra.even_odd_map_involute CliffordAlgebra.evenOdd_map_involute

@[simp]
theorem evenOdd_comap_involute (n : ZMod 2) :
    (evenOdd Q n).comap (involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  rw [← submodule_map_involute_eq_comap, evenOdd_map_involute]
#align clifford_algebra.even_odd_comap_involute CliffordAlgebra.evenOdd_comap_involute

end Involute

section Reverse

theorem submodule_map_reverse_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) :=
  Submodule.map_equiv_eq_comap_symm (reverseEquiv : _ ≃ₗ[R] _) _
#align clifford_algebra.submodule_map_reverse_eq_comap CliffordAlgebra.submodule_map_reverse_eq_comap

@[simp]
theorem ι_range_map_reverse :
    (ι Q).range.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [reverse, reverseOp, Submodule.map_comp, ι_range_map_lift, LinearMap.range_comp,
    ← Submodule.map_comp]
  exact Submodule.map_id _
#align clifford_algebra.ι_range_map_reverse CliffordAlgebra.ι_range_map_reverse

@[simp]
theorem ι_range_comap_reverse :
    (ι Q).range.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [← submodule_map_reverse_eq_comap, ι_range_map_reverse]
#align clifford_algebra.ι_range_comap_reverse CliffordAlgebra.ι_range_comap_reverse

/-- Like `Submodule.map_mul`, but with the multiplication reversed. -/
theorem submodule_map_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      q.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) *
        p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul]
#align clifford_algebra.submodule_map_mul_reverse CliffordAlgebra.submodule_map_mul_reverse

theorem submodule_comap_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      q.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) *
        p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_mul_reverse]
#align clifford_algebra.submodule_comap_mul_reverse CliffordAlgebra.submodule_comap_mul_reverse

/-- Like `Submodule.map_pow` -/
theorem submodule_map_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : ℕ) :
    (p ^ n).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow]
#align clifford_algebra.submodule_map_pow_reverse CliffordAlgebra.submodule_map_pow_reverse

theorem submodule_comap_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : ℕ) :
    (p ^ n).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_pow_reverse]
#align clifford_algebra.submodule_comap_pow_reverse CliffordAlgebra.submodule_comap_pow_reverse

@[simp]
theorem evenOdd_map_reverse (n : ZMod 2) :
    (evenOdd Q n).map (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, submodule_map_pow_reverse, ι_range_map_reverse]
#align clifford_algebra.even_odd_map_reverse CliffordAlgebra.evenOdd_map_reverse

@[simp]
theorem evenOdd_comap_reverse (n : ZMod 2) :
    (evenOdd Q n).comap (reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  rw [← submodule_map_reverse_eq_comap, evenOdd_map_reverse]
#align clifford_algebra.even_odd_comap_reverse CliffordAlgebra.evenOdd_comap_reverse

end Reverse

@[simp]
theorem involute_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    involute x ∈ evenOdd Q n ↔ x ∈ evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_involute Q n) x
#align clifford_algebra.involute_mem_even_odd_iff CliffordAlgebra.involute_mem_evenOdd_iff

@[simp]
theorem reverse_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    reverse x ∈ evenOdd Q n ↔ x ∈ evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_reverse Q n) x
#align clifford_algebra.reverse_mem_even_odd_iff CliffordAlgebra.reverse_mem_evenOdd_iff

end Submodule

/-!
### Related properties of the even and odd submodules

TODO: show that these are `iff`s when `Invertible (2 : R)`.
-/


theorem involute_eq_of_mem_even {x : CliffordAlgebra Q} (h : x ∈ evenOdd Q 0) : involute x = x := by
  induction x, h using even_induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | add x y _hx _hy ihx ihy =>
    rw [map_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul, map_mul, involute_ι, involute_ι, ihx, neg_mul_neg]
#align clifford_algebra.involute_eq_of_mem_even CliffordAlgebra.involute_eq_of_mem_even

theorem involute_eq_of_mem_odd {x : CliffordAlgebra Q} (h : x ∈ evenOdd Q 1) : involute x = -x := by
  induction x, h using odd_induction with
  | ι m => exact involute_ι _
  | add x y _hx _hy ihx ihy =>
    rw [map_add, ihx, ihy, neg_add]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul, map_mul, involute_ι, involute_ι, ihx, neg_mul_neg, mul_neg]
#align clifford_algebra.involute_eq_of_mem_odd CliffordAlgebra.involute_eq_of_mem_odd

end CliffordAlgebra
