/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.basic
! leanprover-community/mathlib commit 9556784a5b84697562e9c6acb40500d4a82e675a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Counit
import Mathbin.Data.MvPolynomial.Invertible
import Mathbin.RingTheory.WittVector.Defs

/-!
# Witt vectors

This file verifies that the ring operations on `witt_vector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `witt_vector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `witt_vector.ghost_component n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `witt_vector.ghost_map`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `witt_vector.comm_ring`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/


noncomputable section

open MvPolynomial Function

open scoped BigOperators

variable {p : ℕ} {R S T : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S] [CommRing T]

variable {α : Type _} {β : Type _}

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
open scoped Witt

namespace WittVector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `witt_vector.map f`. -/
def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)
#align witt_vector.map_fun WittVector.mapFun

namespace MapFun

theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) := fun x y h =>
  ext fun n => hf (congr_arg (fun x => coeff x n) h : _)
#align witt_vector.map_fun.injective WittVector.mapFun.injective

theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.choose <| hf <| x.coeff n, by ext n; dsimp [map_fun];
    rw [Classical.choose_spec (hf (x.coeff n))]⟩
#align witt_vector.map_fun.surjective WittVector.mapFun.surjective

variable (f : R →+* S) (x y : 𝕎 R)

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
unsafe def map_fun_tac : tactic Unit :=
  sorry
#align witt_vector.map_fun.map_fun_tac witt_vector.map_fun.map_fun_tac

include hp

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
-- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on.
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.zero WittVector.mapFun.zero

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem one : mapFun f (1 : 𝕎 R) = 1 := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.one WittVector.mapFun.one

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.add WittVector.mapFun.add

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.sub WittVector.mapFun.sub

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.mul WittVector.mapFun.mul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem neg : mapFun f (-x) = -mapFun f x := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.neg WittVector.mapFun.neg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem nsmul (n : ℕ) : mapFun f (n • x) = n • mapFun f x := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.nsmul WittVector.mapFun.nsmul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem zsmul (z : ℤ) : mapFun f (z • x) = z • mapFun f x := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.zsmul WittVector.mapFun.zsmul

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic witt_vector.map_fun.map_fun_tac -/
theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by
  run_tac
    map_fun_tac
#align witt_vector.map_fun.pow WittVector.mapFun.pow

theorem nat_cast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = coe n by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl
#align witt_vector.map_fun.nat_cast WittVector.mapFun.nat_cast

theorem int_cast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = coe n by
    cases n <;> simp [*, Int.castDef, add, one, neg, zero, nat_cast] <;> rfl
#align witt_vector.map_fun.int_cast WittVector.mapFun.int_cast

end MapFun

end WittVector

section Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- An auxiliary tactic for proving that `ghost_fun` respects the ring operations. -/
unsafe def tactic.interactive.ghost_fun_tac (φ fn : parse parser.pexpr) : tactic Unit := do
  let fn ← to_expr `(($(fn) : Fin _ → ℕ → R))
  let q(Fin $(k) → _ → _) ← infer_type fn
  sorry
  sorry
  to_expr `(congr_fun (congr_arg (@peval R _ $(k)) (wittStructureInt_prop p $(φ) n)) $(fn)) >>=
      note `this none
  sorry
#align tactic.interactive.ghost_fun_tac tactic.interactive.ghost_fun_tac

end Tactic

namespace WittVector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghost_fun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section GhostFun

include hp

-- The following lemmas are not `@[simp]` because they will be bundled in `ghost_map` later on.
variable (x y : 𝕎 R)

omit hp

@[local simp]
theorem matrix_vecEmpty_coeff {R} (i j) :
    @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩
#align witt_vector.matrix_vec_empty_coeff WittVector.matrix_vecEmpty_coeff

include hp

private theorem ghost_fun_zero : ghostFun (0 : 𝕎 R) = 0 := by ghost_fun_tac 0, ![]

private theorem ghost_fun_one : ghostFun (1 : 𝕎 R) = 1 := by ghost_fun_tac 1, ![]

private theorem ghost_fun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_nat_cast (i : ℕ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;>
      simp [*, Nat.unaryCast, ghost_fun_zero, ghost_fun_one, ghost_fun_add, -Pi.coe_nat]

private theorem ghost_fun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_neg : ghostFun (-x) = -ghostFun x := by ghost_fun_tac -X 0, ![x.coeff]

private theorem ghost_fun_int_cast (i : ℤ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghost_fun_nat_cast, ghost_fun_neg, -Pi.coe_nat, -Pi.coe_int]

private theorem ghost_fun_nsmul (m : ℕ) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • X 0, ![x.coeff]

private theorem ghost_fun_zsmul (m : ℤ) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • X 0, ![x.coeff]

private theorem ghost_fun_pow (m : ℕ) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]

end GhostFun

variable (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `witt_vector.ghost_equiv` we upgrade this to an isomorphism of rings. -/
private def ghost_equiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R)
    where
  toFun := ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this 
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_wittPolynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_xInTermsOfW_wittPolynomial p R n
    apply_fun aeval x at this 
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_wittPolynomial]

include hp

@[local instance]
private def comm_ring_aux₁ : CommRing (𝕎 (MvPolynomial R ℚ)) :=
  letI : CommRing (MvPolynomial R ℚ) := MvPolynomial.commRing
  (ghost_equiv' p (MvPolynomial R ℚ)).Injective.CommRing ghost_fun ghost_fun_zero ghost_fun_one
    ghost_fun_add ghost_fun_mul ghost_fun_neg ghost_fun_sub ghost_fun_nsmul ghost_fun_zsmul
    ghost_fun_pow ghost_fun_nat_cast ghost_fun_int_cast

@[local instance]
private def comm_ring_aux₂ : CommRing (𝕎 (MvPolynomial R ℤ)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).CommRing _
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.nat_cast _) (mapFun.int_cast _)

attribute [reducible] comm_ring_aux₂

/-- The commutative ring structure on `𝕎 R`. -/
instance : CommRing (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).CommRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.nat_cast _) (mapFun.int_cast _)

variable {p R}

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
noncomputable def map (f : R →+* S) : 𝕎 R →+* 𝕎 S
    where
  toFun := mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f
#align witt_vector.map WittVector.map

theorem map_injective (f : R →+* S) (hf : Injective f) : Injective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.injective f hf
#align witt_vector.map_injective WittVector.map_injective

theorem map_surjective (f : R →+* S) (hf : Surjective f) : Surjective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.surjective f hf
#align witt_vector.map_surjective WittVector.map_surjective

@[simp]
theorem map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) : (map f x).coeff n = f (x.coeff n) :=
  rfl
#align witt_vector.map_coeff WittVector.map_coeff

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghostMap : 𝕎 R →+* ℕ → R where
  toFun := ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul
#align witt_vector.ghost_map WittVector.ghostMap

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghostComponent (n : ℕ) : 𝕎 R →+* R :=
  (Pi.evalRingHom _ n).comp ghostMap
#align witt_vector.ghost_component WittVector.ghostComponent

theorem ghostComponent_apply (n : ℕ) (x : 𝕎 R) : ghostComponent n x = aeval x.coeff (W_ ℤ n) :=
  rfl
#align witt_vector.ghost_component_apply WittVector.ghostComponent_apply

@[simp]
theorem ghostMap_apply (x : 𝕎 R) (n : ℕ) : ghostMap x n = ghostComponent n x :=
  rfl
#align witt_vector.ghost_map_apply WittVector.ghostMap_apply

section Invertible

variable (p R) [Invertible (p : R)]

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghostEquiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghostMap : 𝕎 R →+* ℕ → R), ghostEquiv' p R with }
#align witt_vector.ghost_equiv WittVector.ghostEquiv

@[simp]
theorem ghostEquiv_coe : (ghostEquiv p R : 𝕎 R →+* ℕ → R) = ghostMap :=
  rfl
#align witt_vector.ghost_equiv_coe WittVector.ghostEquiv_coe

theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R → ℕ → R) :=
  (ghostEquiv p R).Bijective
#align witt_vector.ghost_map.bijective_of_invertible WittVector.ghostMap.bijective_of_invertible

end Invertible

/-- `witt_vector.coeff x 0` as a `ring_hom` -/
@[simps]
noncomputable def constantCoeff : 𝕎 R →+* R
    where
  toFun x := x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero
#align witt_vector.constant_coeff WittVector.constantCoeff

instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial

end WittVector

