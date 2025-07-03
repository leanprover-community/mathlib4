/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `n`th symmetric tensor power of `M` as the `TensorPower` quotiented by the relation
that the `tprod` of `n` elements is equal to the `tprod` of the same elements permuted by a
permutation of `Fin n`. We denote this space by `Sym[R]^n M`, and the canonical multilinear map
from `M ^ n` to `Sym[R]^n M` by `⨂ₛ[R] i, f i`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogneous (multivariate) polynomials of degree `n`.

-/

suppress_compilation

universe u v

open TensorProduct Equiv

variable (R : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ)

/-- The relation on the `n`ᵗʰ tensor power of `M` that two tensors are equal if they are related by
a permutation of `Fin n`. -/
inductive SymmetricPower.Rel : ⨂[R]^n M → ⨂[R]^n M → Prop
  | perm : (e : Perm (Fin n)) → (f : Fin n → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/-- The symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `n`ᵗʰ tensor power by the relation that two tensors are equal
if they are related by a permutation of `Fin n`. -/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R M n)).Quotient

@[inherit_doc] scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => SymmetricPower R M n

namespace SymmetricPower

instance : AddCommMonoid (Sym[R]^n M) := AddCon.addCommMonoid _

instance (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    AddCommGroup (Sym[R]^n M) := AddCon.addCommGroup _

variable {R M n} in
lemma smul (r : R) (x y : ⨂[R]^n M) (h : addConGen (Rel R M n) x y) :
    addConGen (Rel R M n) (r • x) (r • y) := by
  induction h with
  | of x y h => cases h with
    | perm e f => cases n with
      | zero => convert (addConGen (Rel R M 0)).refl _
      | succ n =>
          convert AddConGen.Rel.of _ _ (Rel.perm (R := R) e (Function.update f 0 (r • f 0)))
          · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
          · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
              ← Function.update_comp_equiv, Function.update_eq_self]; rfl
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add => rw [smul_add, smul_add]; apply AddCon.add <;> assumption

variable {R} in
/-- Scalar multiplication by `r : R`. Use `•` instead. -/
def smul' (r : R) : Sym[R]^n M →+ Sym[R]^n M :=
  AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h ↦ Quotient.sound (smul r x y h))

instance module : Module R (Sym[R]^n M) where
  smul r x := smul' M n r x
  one_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| one_smul R x
  mul_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| mul_smul r s x
  smul_zero r := congr_arg _ <| smul_zero r
  smul_add r x y := AddCon.induction_on₂ x y <| fun x y ↦ congr_arg _ <| smul_add r x y
  add_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| add_smul r s x
  zero_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| zero_smul R x

/-- The canonical map from the `n`ᵗʰ tensor power to the `n`ᵗʰ symmetric tensor power. -/
def mk : ⨂[R]^n M →ₗ[R] Sym[R]^n M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M n} in
/-- The multilinear map that takes `n` elements of `M` and returns their symmetric tensor product.
Denoted `⨂ₛ[R] i, f i`. -/
def tprod : MultilinearMap R (fun _ : Fin n ↦ M) Sym[R]^n M :=
  (mk R M n).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R M n} in
@[simp] lemma tprod_equiv (e : Perm (Fin n)) (f : Fin n → M) :
    (⨂ₛ[R] i, f (e i)) = ⨂ₛ[R] i, f i :=
  Eq.symm <| Quot.sound <| AddConGen.Rel.of _ _ <| Rel.perm e f

variable {R M n} in
@[simp] lemma domDomCongr_tprod (e : Perm (Fin n)) :
    (tprod R (M := M) (n := n)).domDomCongr e = tprod R :=
  MultilinearMap.ext <| tprod_equiv e

theorem range_mk : LinearMap.range (mk R M n) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor product. -/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (M := M) (n := n))) = ⊤ := by
  rw [tprod, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

end SymmetricPower
