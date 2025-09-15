/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `ι`-indexed symmetric tensor power of `M` as the `PiTensorProduct` quotiented by
the relation that the `tprod` of `ι` elements is equal to the `tprod` of the same elements permuted
by a permutation of `ι`. We denote this space by `Sym[R] ι M`, and the canonical multilinear map
from `ι → M` to `Sym[R] ι M` by `⨂ₛ[R] i, f i`. We also reserve the notation `Sym[R]^n M` for the
`n`th symmetric tensor power of `M`, which is the symmetric tensor power indexed by `Fin n`.

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

variable (R ι : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (s : ι → M)

/-- The relation on the `ι`-indexed tensor power of `M` where two tensors are equal
if they are related by a permutation of `ι`. -/
inductive SymmetricPower.Rel : (⨂[R] _, M) → (⨂[R] _, M) → Prop
  | perm : (e : Perm ι) → (f : ι → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/-- The `ι`-indexed symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `ι`-indexed tensor power of `M` by the relation that two tensors are equal
if they are related by a permutation of `ι`. -/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R ι M)).Quotient

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

/-- The `n`th symmetric tensor power of a semimodule `M` over a commutative semiring `R` -/
scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => Sym[R] (Fin n) M

namespace SymmetricPower

instance : AddCommMonoid (Sym[R] ι M) := AddCon.addCommMonoid _

instance (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (Sym[R] ι M) := AddCon.addCommGroup _

variable {R ι M} in
lemma smul (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι M) (r • x) (r • y) := by
  induction h with
  | of x y h => cases h with
    | perm e f =>
      apply isEmpty_or_nonempty ι |>.elim <;> intro h
      · convert addConGen (Rel R ι M) |>.refl _
      · let i := Nonempty.some h
        classical
        convert AddConGen.Rel.of _ _ <| SymmetricPower.Rel.perm (R := R) (ι := ι) e
          <| Function.update f i (r • f i)
        · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
        · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
              ← Function.update_comp_equiv, Function.update_eq_self]; rfl
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add => rw [smul_add, smul_add]; apply AddCon.add <;> assumption

variable {R} in
/-- Scalar multiplication by `r : R`. Use `•` instead. -/
def smul' (r : R) : Sym[R] ι M →+ Sym[R] ι M :=
  AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h ↦ Quotient.sound (smul r x y h))

instance module : Module R (Sym[R] ι M) where
  smul r x := smul' ι M r x
  one_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| one_smul R x
  mul_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| mul_smul r s x
  smul_zero r := congr_arg _ <| smul_zero r
  smul_add r x y := AddCon.induction_on₂ x y <| fun x y ↦ congr_arg _ <| smul_add r x y
  add_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| add_smul r s x
  zero_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| zero_smul R x

/-- The canonical map from the `ι`-indexed tensor power to the symmetric tensor power. -/
def mk : (⨂[R] (_ : ι), M) →ₗ[R] Sym[R] ι M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M ι} in
/-- The multilinear map that takes `ι`-indexed elements of `M` and
returns their symmetric tensor power. Denoted `⨂ₛ[R] i, f i`. -/
def tprod : MultilinearMap R (fun _ : ι ↦ M) Sym[R] ι M :=
  (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R ι M} in
@[simp] lemma tprod_equiv (e : Perm ι) (f : ι → M) :
    (⨂ₛ[R] i, f (e i)) = ⨂ₛ[R] i, f i :=
  Eq.symm <| Quot.sound <| AddConGen.Rel.of _ _ <| Rel.perm e f

variable {R M n} in
@[simp] lemma domDomCongr_tprod (e : Perm ι) :
    (tprod R (ι := ι) (M := M)).domDomCongr e = tprod R :=
  MultilinearMap.ext <| tprod_equiv e

theorem range_mk : LinearMap.range (mk R ι M) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor power. -/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤ := by
  rw [tprod, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

end SymmetricPower
