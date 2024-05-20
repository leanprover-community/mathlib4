/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Dual

#align_import linear_algebra.clifford_algebra.contraction from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Contraction in Clifford Algebras

This file contains some of the results from [grinberg_clifford_2016][].
The key result is `CliffordAlgebra.equivExterior`.

## Main definitions

* `CliffordAlgebra.contractLeft`: contract a multivector by a `Module.Dual R M` on the left.
* `CliffordAlgebra.contractRight`: contract a multivector by a `Module.Dual R M` on the right.
* `CliffordAlgebra.changeForm`: convert between two algebras of different quadratic form, sending
  vectors to vectors. The difference of the quadratic forms must be a bilinear form.
* `CliffordAlgebra.equivExterior`: in characteristic not-two, the `CliffordAlgebra Q` is
  isomorphic as a module to the exterior algebra.

## Implementation notes

This file somewhat follows [grinberg_clifford_2016][], although we are missing some of the induction
principles needed to prove many of the results. Here, we avoid the quotient-based approach described
in [grinberg_clifford_2016][], instead directly constructing our objects using the universal
property.

Note that [grinberg_clifford_2016][] concludes that its contents are not novel, and are in fact just
a rehash of parts of [bourbaki2007][]; we should at some point consider swapping our references to
refer to the latter.

Within this file, we use the local notation
* `x ⌊ d` for `contractRight x d`
* `d ⌋ x` for `contractLeft d x`

-/

open LinearMap (BilinForm)

universe u1 u2 u3

variable {R : Type u1} [CommRing R]
variable {M : Type u2} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section contractLeft

variable (d d' : Module.Dual R M)

/-- Auxiliary construction for `CliffordAlgebra.contractLeft` -/
@[simps!]
def contractLeftAux (d : Module.Dual R M) :
    M →ₗ[R] CliffordAlgebra Q × CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)
#align clifford_algebra.contract_left_aux CliffordAlgebra.contractLeftAux

theorem contractLeftAux_contractLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) :
    contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)) = Q v • fx := by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← sub_add, mul_smul_comm, sub_self,
    zero_add]
#align clifford_algebra.contract_left_aux_contract_left_aux CliffordAlgebra.contractLeftAux_contractLeftAux

variable {Q}

/-- Contract an element of the clifford algebra with an element `d : Module.Dual R M` from the left.

Note that $v ⌋ x$ is spelt `contractLeft (Q.associated v) x`.

This includes [grinberg_clifford_2016][] Theorem 10.75 -/
def contractLeft : Module.Dual R M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun d := foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      dsimp only
      rw [LinearMap.add_apply]
      induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
      · simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      · rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [sub_add_sub_comm, mul_add, LinearMap.add_apply, add_smul]
  map_smul' c d :=
    LinearMap.ext fun x => by
      dsimp only
      rw [LinearMap.smul_apply, RingHom.id_apply]
      induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
      · simp_rw [foldr'_algebraMap, smul_zero]
      · rw [map_add, map_add, smul_add, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [LinearMap.smul_apply, smul_assoc, mul_smul_comm, smul_sub]
#align clifford_algebra.contract_left CliffordAlgebra.contractLeft

/-- Contract an element of the clifford algebra with an element `d : Module.Dual R M` from the
right.

Note that $x ⌊ v$ is spelt `contractRight x (Q.associated v)`.

This includes [grinberg_clifford_2016][] Theorem 16.75 -/
def contractRight : CliffordAlgebra Q →ₗ[R] Module.Dual R M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)
#align clifford_algebra.contract_right CliffordAlgebra.contractRight

theorem contractRight_eq (x : CliffordAlgebra Q) :
    contractRight (Q := Q) x d = reverse (contractLeft (R := R) (M := M) d <| reverse x) :=
  rfl
#align clifford_algebra.contract_right_eq CliffordAlgebra.contractRight_eq

local infixl:70 "⌋" => contractLeft (R := R) (M := M)

local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)

-- Porting note: Lean needs to be reminded of this instance otherwise the statement of the
-- next result times out
instance : SMul R (CliffordAlgebra Q) := inferInstance

/-- This is [grinberg_clifford_2016][] Theorem 6  -/
theorem contractLeft_ι_mul (a : M) (b : CliffordAlgebra Q) :
    d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b) := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine foldr'_ι_mul _ _ ?_ _ _ _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
#align clifford_algebra.contract_left_ι_mul CliffordAlgebra.contractLeft_ι_mul

/-- This is [grinberg_clifford_2016][] Theorem 12  -/
theorem contractRight_mul_ι (a : M) (b : CliffordAlgebra Q) :
    b * ι Q a⌊d = d a • b - b⌊d * ι Q a := by
  rw [contractRight_eq, reverse.map_mul, reverse_ι, contractLeft_ι_mul, map_sub, map_smul,
    reverse_reverse, reverse.map_mul, reverse_ι, contractRight_eq]
#align clifford_algebra.contract_right_mul_ι CliffordAlgebra.contractRight_mul_ι

theorem contractLeft_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    d⌋(algebraMap _ _ r * b) = algebraMap _ _ r * (d⌋b) := by
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
#align clifford_algebra.contract_left_algebra_map_mul CliffordAlgebra.contractLeft_algebraMap_mul

theorem contractLeft_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    d⌋(a * algebraMap _ _ r) = d⌋a * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractLeft_algebraMap_mul, Algebra.commutes]
#align clifford_algebra.contract_left_mul_algebra_map CliffordAlgebra.contractLeft_mul_algebraMap

theorem contractRight_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    algebraMap _ _ r * b⌊d = algebraMap _ _ r * (b⌊d) := by
  rw [← Algebra.smul_def, LinearMap.map_smul₂, Algebra.smul_def]
#align clifford_algebra.contract_right_algebra_map_mul CliffordAlgebra.contractRight_algebraMap_mul

theorem contractRight_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    a * algebraMap _ _ r⌊d = a⌊d * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractRight_algebraMap_mul, Algebra.commutes]
#align clifford_algebra.contract_right_mul_algebra_map CliffordAlgebra.contractRight_mul_algebraMap

variable (Q)

@[simp]
theorem contractLeft_ι (x : M) : d⌋ι Q x = algebraMap R _ (d x) := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine (foldr'_ι _ _ ?_ _ _).trans <| by
    simp_rw [contractLeftAux_apply_apply, mul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one]
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
#align clifford_algebra.contract_left_ι CliffordAlgebra.contractLeft_ι

@[simp]
theorem contractRight_ι (x : M) : ι Q x⌊d = algebraMap R _ (d x) := by
  rw [contractRight_eq, reverse_ι, contractLeft_ι, reverse.commutes]
#align clifford_algebra.contract_right_ι CliffordAlgebra.contractRight_ι

@[simp]
theorem contractLeft_algebraMap (r : R) : d⌋algebraMap R (CliffordAlgebra Q) r = 0 := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine (foldr'_algebraMap _ _ ?_ _ _).trans <| smul_zero _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx
#align clifford_algebra.contract_left_algebra_map CliffordAlgebra.contractLeft_algebraMap

@[simp]
theorem contractRight_algebraMap (r : R) : algebraMap R (CliffordAlgebra Q) r⌊d = 0 := by
  rw [contractRight_eq, reverse.commutes, contractLeft_algebraMap, map_zero]
#align clifford_algebra.contract_right_algebra_map CliffordAlgebra.contractRight_algebraMap

@[simp]
theorem contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0 := by
  simpa only [map_one] using contractLeft_algebraMap Q d 1
#align clifford_algebra.contract_left_one CliffordAlgebra.contractLeft_one

@[simp]
theorem contractRight_one : (1 : CliffordAlgebra Q)⌊d = 0 := by
  simpa only [map_one] using contractRight_algebraMap Q d 1
#align clifford_algebra.contract_right_one CliffordAlgebra.contractRight_one

variable {Q}

/-- This is [grinberg_clifford_2016][] Theorem 7 -/
theorem contractLeft_contractLeft (x : CliffordAlgebra Q) : d⌋(d⌋x) = 0 := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [contractLeft_algebraMap, map_zero]
  · rw [map_add, map_add, hx, hy, add_zero]
  · rw [contractLeft_ι_mul, map_sub, contractLeft_ι_mul, hx, LinearMap.map_smul,
      mul_zero, sub_zero, sub_self]
#align clifford_algebra.contract_left_contract_left CliffordAlgebra.contractLeft_contractLeft

/-- This is [grinberg_clifford_2016][] Theorem 13 -/
theorem contractRight_contractRight (x : CliffordAlgebra Q) : x⌊d⌊d = 0 := by
  rw [contractRight_eq, contractRight_eq, reverse_reverse, contractLeft_contractLeft, map_zero]
#align clifford_algebra.contract_right_contract_right CliffordAlgebra.contractRight_contractRight

/-- This is [grinberg_clifford_2016][] Theorem 8 -/
theorem contractLeft_comm (x : CliffordAlgebra Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x)) := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  · rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  · simp only [contractLeft_ι_mul, map_sub, LinearMap.map_smul]
    rw [neg_sub, sub_sub_eq_add_sub, hx, mul_neg, ← sub_eq_add_neg]
#align clifford_algebra.contract_left_comm CliffordAlgebra.contractLeft_comm

/-- This is [grinberg_clifford_2016][] Theorem 14 -/
theorem contractRight_comm (x : CliffordAlgebra Q) : x⌊d⌊d' = -(x⌊d'⌊d) := by
  rw [contractRight_eq, contractRight_eq, contractRight_eq, contractRight_eq, reverse_reverse,
    reverse_reverse, contractLeft_comm, map_neg]
#align clifford_algebra.contract_right_comm CliffordAlgebra.contractRight_comm

/- TODO:
lemma contractRight_contractLeft (x : CliffordAlgebra Q) : (d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d') :=
-/
end contractLeft

local infixl:70 "⌋" => contractLeft

local infixl:70 "⌊" => contractRight

/-- Auxiliary construction for `CliffordAlgebra.changeForm` -/
@[simps!]
def changeFormAux (B : BilinForm R M) : M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B
#align clifford_algebra.change_form_aux CliffordAlgebra.changeFormAux

theorem changeFormAux_changeFormAux (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q) :
    changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x := by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, map_sub, contractLeft_ι_mul, ← sub_add, sub_sub_sub_comm,
    ← Algebra.smul_def, sub_self, sub_zero, contractLeft_contractLeft, add_zero, sub_smul]
#align clifford_algebra.change_form_aux_change_form_aux CliffordAlgebra.changeFormAux_changeFormAux

variable {Q}
variable {Q' Q'' : QuadraticForm R M} {B B' : BilinForm R M}
variable (h : B.toQuadraticForm = Q' - Q) (h' : B'.toQuadraticForm = Q'' - Q')

/-- Convert between two algebras of different quadratic form, sending vector to vectors, scalars to
scalars, and adjusting products by a contraction term.

This is $\lambda_B$ from [bourbaki2007][] $9 Lemma 2. -/
def changeForm (h : B.toQuadraticForm = Q' - Q) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q' :=
  foldr Q (changeFormAux Q' B)
    (fun m x =>
      (changeFormAux_changeFormAux Q' B m x).trans <| by
        dsimp only [← BilinForm.toQuadraticForm_apply]
        rw [h, QuadraticForm.sub_apply, sub_sub_cancel])
    1
#align clifford_algebra.change_form CliffordAlgebra.changeForm

/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
theorem changeForm.zero_proof : (0 : BilinForm R M).toQuadraticForm = Q - Q :=
  (sub_self _).symm
#align clifford_algebra.change_form.zero_proof CliffordAlgebra.changeForm.zero_proof

/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
theorem changeForm.add_proof : (B + B').toQuadraticForm = Q'' - Q :=
  (congr_arg₂ (· + ·) h h').trans <| sub_add_sub_cancel' _ _ _
#align clifford_algebra.change_form.add_proof CliffordAlgebra.changeForm.add_proof

/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
theorem changeForm.neg_proof : (-B).toQuadraticForm = Q - Q' :=
  (congr_arg Neg.neg h).trans <| neg_sub _ _
#align clifford_algebra.change_form.neg_proof CliffordAlgebra.changeForm.neg_proof

theorem changeForm.associated_neg_proof [Invertible (2 : R)] :
    (QuadraticForm.associated (R := R) (M := M) (-Q)).toQuadraticForm = 0 - Q := by
  simp [QuadraticForm.toQuadraticForm_associated]
#align clifford_algebra.change_form.associated_neg_proof CliffordAlgebra.changeForm.associated_neg_proof

@[simp]
theorem changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r :=
  (foldr_algebraMap _ _ _ _ _).trans <| Eq.symm <| Algebra.algebraMap_eq_smul_one r
#align clifford_algebra.change_form_algebra_map CliffordAlgebra.changeForm_algebraMap

@[simp]
theorem changeForm_one : changeForm h (1 : CliffordAlgebra Q) = 1 := by
  simpa using changeForm_algebraMap h (1 : R)
#align clifford_algebra.change_form_one CliffordAlgebra.changeForm_one

@[simp]
theorem changeForm_ι (m : M) : changeForm h (ι (M := M) Q m) = ι (M := M) Q' m :=
  (foldr_ι _ _ _ _ _).trans <|
    Eq.symm <| by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]
#align clifford_algebra.change_form_ι CliffordAlgebra.changeForm_ι

theorem changeForm_ι_mul (m : M) (x : CliffordAlgebra Q) :
    changeForm h (ι (M := M) Q m * x) = ι (M := M) Q' m * changeForm h x
    - contractLeft (Q := Q') (B m) (changeForm h x) :=
-- Porting note: original statement
--    - BilinForm.toLin B m⌋changeForm h x :=
  (foldr_mul _ _ _ _ _ _).trans <| by rw [foldr_ι]; rfl
#align clifford_algebra.change_form_ι_mul CliffordAlgebra.changeForm_ι_mul

theorem changeForm_ι_mul_ι (m₁ m₂ : M) :
    changeForm h (ι Q m₁ * ι Q m₂) = ι Q' m₁ * ι Q' m₂ - algebraMap _ _ (B m₁ m₂) := by
  rw [changeForm_ι_mul, changeForm_ι, contractLeft_ι]
#align clifford_algebra.change_form_ι_mul_ι CliffordAlgebra.changeForm_ι_mul_ι

/-- Theorem 23 of [grinberg_clifford_2016][] -/
theorem changeForm_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    -- Porting note: original statement
    --    changeForm h (d⌋x) = d⌋changeForm h x := by
    changeForm h (contractLeft (Q := Q) d x) = contractLeft (Q := Q') d (changeForm h x) := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  · rw [map_add, map_add, map_add, map_add, hx, hy]
  · simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, LinearMap.map_smul]
    rw [← hx, contractLeft_comm, ← sub_add, sub_neg_eq_add, ← hx]
#align clifford_algebra.change_form_contract_left CliffordAlgebra.changeForm_contractLeft

theorem changeForm_self_apply (x : CliffordAlgebra Q) : changeForm (Q' := Q)
    changeForm.zero_proof x = x := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [changeForm_algebraMap]
  · rw [map_add, hx, hy]
  · rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]
#align clifford_algebra.change_form_self_apply CliffordAlgebra.changeForm_self_apply

@[simp]
theorem changeForm_self :
    changeForm changeForm.zero_proof = (LinearMap.id : CliffordAlgebra Q →ₗ[R] _) :=
  LinearMap.ext <| changeForm_self_apply
#align clifford_algebra.change_form_self CliffordAlgebra.changeForm_self

/-- This is [bourbaki2007][] $9 Lemma 3. -/
theorem changeForm_changeForm (x : CliffordAlgebra Q) :
    changeForm h' (changeForm h x) = changeForm (changeForm.add_proof h h') x := by
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [changeForm_algebraMap]
  · rw [map_add, map_add, map_add, hx, hy]
  · rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_add, LinearMap.add_apply, changeForm_contractLeft, hx,
      add_comm (_ : CliffordAlgebra Q'')]
#align clifford_algebra.change_form_change_form CliffordAlgebra.changeForm_changeForm

theorem changeForm_comp_changeForm :
    (changeForm h').comp (changeForm h) = changeForm (changeForm.add_proof h h') :=
  LinearMap.ext <| changeForm_changeForm _ h'
#align clifford_algebra.change_form_comp_change_form CliffordAlgebra.changeForm_comp_changeForm

/-- Any two algebras whose quadratic forms differ by a bilinear form are isomorphic as modules.

This is $\bar \lambda_B$ from [bourbaki2007][] $9 Proposition 3. -/
@[simps apply]
def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
      dsimp only
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(add_neg_self B), changeForm_self_apply]
    right_inv := fun x => by
      dsimp only
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(add_left_neg B), changeForm_self_apply] }
#align clifford_algebra.change_form_equiv CliffordAlgebra.changeFormEquiv

@[simp]
theorem changeFormEquiv_symm :
    (changeFormEquiv h).symm = changeFormEquiv (changeForm.neg_proof h) :=
  LinearEquiv.ext fun _ => rfl
#align clifford_algebra.change_form_equiv_symm CliffordAlgebra.changeFormEquiv_symm

variable (Q)

/-- The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use. -/
@[simp]
def equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  changeFormEquiv changeForm.associated_neg_proof
#align clifford_algebra.equiv_exterior CliffordAlgebra.equivExterior

/-- A `CliffordAlgebra` over a nontrivial ring is nontrivial, in characteristic not two. -/
instance [Nontrivial R] [Invertible (2 : R)] :
    Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial

end CliffordAlgebra
