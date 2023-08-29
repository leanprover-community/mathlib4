/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Data.MvPolynomial.Counit
import Mathlib.Data.MvPolynomial.Invertible
import Mathlib.RingTheory.WittVector.Defs

#align_import ring_theory.witt_vector.basic from "leanprover-community/mathlib"@"9556784a5b84697562e9c6acb40500d4a82e675a"

/-!
# Witt vectors

This file verifies that the ring operations on `WittVector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `WittVector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `WittVector.ghostComponent n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `WittVector.ghostMap`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `WittVector.CommRing`: the ring structure induced by the ghost components.

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

variable {p : ℕ} {R S T : Type*} [hp : Fact p.Prime] [CommRing R] [CommRing S] [CommRing T]

variable {α : Type*} {β : Type*}

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p
local notation "W_" => wittPolynomial p

-- type as `\bbW`
open scoped Witt

namespace WittVector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `WittVector.map f`. -/
def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)
#align witt_vector.map_fun WittVector.mapFun

namespace mapFun

-- porting note: switched the proof to tactic mode. I think that `ext` was the issue.
theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) := by
  intros _ _ h
  -- ⊢ a₁✝ = a₂✝
  ext p
  -- ⊢ coeff a₁✝ p = coeff a₂✝ p
  exact hf (congr_arg (fun x => coeff x p) h : _)
  -- 🎉 no goals
#align witt_vector.map_fun.injective WittVector.mapFun.injective

theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.choose <| hf <| x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩
       -- ⊢ coeff (mapFun f (mk p fun n => Classical.choose (_ : ∃ a, f a = coeff x n))) …
              -- 🎉 no goals
#align witt_vector.map_fun.surjective WittVector.mapFun.surjective

-- porting note: using `(x y : 𝕎 R)` instead of `(x y : WittVector p R)` produced sorries.
variable (f : R →+* S) (x y : WittVector p R)

/-- Auxiliary tactic for showing that `mapFun` respects the ring operations. -/
--  porting note: a very crude port.
macro "map_fun_tac" : tactic => `(tactic| (
  ext n
  simp only [mapFun, mk, comp_apply, zero_coeff, map_zero,
    -- porting note: the lemmas on the next line do not have the `simp` tag in mathlib4
    add_coeff, sub_coeff, mul_coeff, neg_coeff, nsmul_coeff, zsmul_coeff, pow_coeff,
    peval, map_aeval, algebraMap_int_eq, coe_eval₂Hom] <;>
  try { cases n <;> simp <;> done } <;>  -- porting note: this line solves `one`
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl <;>
  ext ⟨i, k⟩ <;>
    fin_cases i <;> rfl ))

--  and until `pow`.
-- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on.
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by map_fun_tac
                                            -- 🎉 no goals
#align witt_vector.map_fun.zero WittVector.mapFun.zero

theorem one : mapFun f (1 : 𝕎 R) = 1 := by map_fun_tac
                                           -- 🎉 no goals
#align witt_vector.map_fun.one WittVector.mapFun.one

theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac
                                                               -- 🎉 no goals
#align witt_vector.map_fun.add WittVector.mapFun.add

theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac
                                                               -- 🎉 no goals
#align witt_vector.map_fun.sub WittVector.mapFun.sub

theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac
                                                               -- 🎉 no goals
#align witt_vector.map_fun.mul WittVector.mapFun.mul

theorem neg : mapFun f (-x) = -mapFun f x := by map_fun_tac
                                                -- 🎉 no goals
#align witt_vector.map_fun.neg WittVector.mapFun.neg

theorem nsmul (n : ℕ) : mapFun f (n • x) = n • mapFun f x := by map_fun_tac
                                                                -- 🎉 no goals
#align witt_vector.map_fun.nsmul WittVector.mapFun.nsmul

theorem zsmul (z : ℤ) : mapFun f (z • x) = z • mapFun f x := by map_fun_tac
                                                                -- 🎉 no goals
#align witt_vector.map_fun.zsmul WittVector.mapFun.zsmul

theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac
                                                              -- 🎉 no goals
#align witt_vector.map_fun.pow WittVector.mapFun.pow

theorem nat_cast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl
    -- ⊢ mapFun (↑f) (Nat.unaryCast Nat.zero) = ↑Nat.zero
                    -- ⊢ 0 = ↑0
                    -- ⊢ ↑n✝ + 1 = ↑(Nat.succ n✝)
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align witt_vector.map_fun.nat_cast WittVector.mapFun.nat_cast

theorem int_cast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, add, one, neg, zero, nat_cast] <;> rfl
    -- ⊢ mapFun (↑f) (Int.castDef (Int.ofNat a✝)) = ↑(Int.ofNat a✝)
                -- ⊢ ↑a✝ = ↑↑a✝
                -- ⊢ -↑(a✝ + 1) = ↑(Int.negSucc a✝)
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align witt_vector.map_fun.int_cast WittVector.mapFun.int_cast

end mapFun

end WittVector

namespace WittVector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `WittVector.ghostMap`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghostFun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section Tactic
open Lean Elab Tactic

--  porting note: removed mathport output related to meta code.
--  I do not know what to do with `#align`
/-- An auxiliary tactic for proving that `ghostFun` respects the ring operations. -/
elab "ghost_fun_tac" φ:term "," fn:term : tactic => do
  evalTactic (← `(tactic| (
  ext n
  have := congr_fun (congr_arg (@peval R _ _) (wittStructureInt_prop p $φ n)) $fn
  simp only [wittZero, OfNat.ofNat, Zero.zero, wittOne, One.one,
    HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, Neg.neg, HMul.hMul, Mul.mul,HPow.hPow, Pow.pow,
    wittNSMul, wittZSMul, HSMul.hSMul, SMul.smul]
  simpa [WittVector.ghostFun, aeval_rename, aeval_bind₁, comp, uncurry, peval, eval] using this
  )))

end Tactic

section GhostFun

variable (x y : WittVector p R)

-- The following lemmas are not `@[simp]` because they will be bundled in `ghostMap` later on.

@[local simp]
theorem matrix_vecEmpty_coeff {R} (i j) :
    @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩
  -- 🎉 no goals
#align witt_vector.matrix_vec_empty_coeff WittVector.matrix_vecEmpty_coeff

private theorem ghostFun_zero : ghostFun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, ![]
  -- 🎉 no goals

private theorem ghostFun_one : ghostFun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, ![]
  -- 🎉 no goals

private theorem ghostFun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]
  -- 🎉 no goals

private theorem ghostFun_nat_cast (i : ℕ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;>
    -- ⊢ WittVector.ghostFun (Nat.unaryCast Nat.zero) = ↑Nat.zero
      simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add, -Pi.coe_nat]
      -- 🎉 no goals
      -- 🎉 no goals

private theorem ghostFun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]
  -- 🎉 no goals

private theorem ghostFun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]
  -- 🎉 no goals

private theorem ghostFun_neg : ghostFun (-x) = -ghostFun x := by ghost_fun_tac -X 0, ![x.coeff]
                                                                 -- 🎉 no goals

private theorem ghostFun_int_cast (i : ℤ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_nat_cast, ghostFun_neg, -Pi.coe_nat, -Pi.coe_int]
    -- ⊢ WittVector.ghostFun (Int.castDef (Int.ofNat a✝)) = ↑(Int.ofNat a✝)
                -- 🎉 no goals
                -- 🎉 no goals

private theorem ghostFun_nsmul (m : ℕ) : ghostFun (m • x) = m • ghostFun x := by
  --  porting note: I had to add the explicit type ascription.
  --  This could very well be due to my poor tactic writing!
  ghost_fun_tac m • (X 0 : MvPolynomial _ ℤ), ![x.coeff]
  -- 🎉 no goals

private theorem ghostFun_zsmul (m : ℤ) : ghostFun (m • x) = m • ghostFun x := by
  --  porting note: I had to add the explicit type ascription.
  --  This could very well be due to my poor tactic writing!
  ghost_fun_tac m • (X 0 : MvPolynomial _ ℤ), ![x.coeff]
  -- 🎉 no goals

private theorem ghostFun_pow (m : ℕ) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]
  -- 🎉 no goals

end GhostFun

variable (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `WittVector.ghostEquiv` we upgrade this to an isomorphism of rings. -/
private def ghostEquiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R) where
  toFun := ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    -- ⊢ (fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) (WittVector.ghostFun …
    ext n
    -- ⊢ coeff ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) (WittVector.g …
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    -- ⊢ coeff ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) (WittVector.g …
    apply_fun aeval x.coeff at this
    -- ⊢ coeff ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) (WittVector.g …
    simpa only [aeval_bind₁, aeval_X, ghostFun, aeval_wittPolynomial]
    -- 🎉 no goals
  right_inv := by
    intro x
    -- ⊢ WittVector.ghostFun ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) …
    ext n
    -- ⊢ WittVector.ghostFun ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) …
    have := bind₁_xInTermsOfW_wittPolynomial p R n
    -- ⊢ WittVector.ghostFun ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) …
    apply_fun aeval x at this
    -- ⊢ WittVector.ghostFun ((fun x => mk p fun n => ↑(aeval x) (xInTermsOfW p R n)) …
    simpa only [aeval_bind₁, aeval_X, ghostFun, aeval_wittPolynomial]
    -- 🎉 no goals

@[local instance]
private def comm_ring_aux₁ : CommRing (𝕎 (MvPolynomial R ℚ)) :=
  -- Porting note: no longer needed?
  -- letI : CommRing (MvPolynomial R ℚ) := MvPolynomial.commRing
  (ghostEquiv' p (MvPolynomial R ℚ)).injective.commRing ghostFun ghostFun_zero ghostFun_one
    ghostFun_add ghostFun_mul ghostFun_neg ghostFun_sub ghostFun_nsmul ghostFun_zsmul
    ghostFun_pow ghostFun_nat_cast ghostFun_int_cast

@[local instance]
private def comm_ring_aux₂ : CommRing (𝕎 (MvPolynomial R ℤ)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).commRing _
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.nat_cast _) (mapFun.int_cast _)

attribute [reducible] comm_ring_aux₂

/-- The commutative ring structure on `𝕎 R`. -/
instance : CommRing (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.nat_cast _) (mapFun.int_cast _)

variable {p R}

/-- `WittVector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
noncomputable def map (f : R →+* S) : 𝕎 R →+* 𝕎 S where
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

/-- `WittVector.ghostMap` is a ring homomorphism that maps each Witt vector
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

variable (p R)
variable [Invertible (p : R)]

/-- `WittVector.ghostMap` is a ring isomorphism when `p` is invertible in `R`. -/
def ghostEquiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghostMap : 𝕎 R →+* ℕ → R), ghostEquiv' p R with }
#align witt_vector.ghost_equiv WittVector.ghostEquiv

@[simp]
theorem ghostEquiv_coe : (ghostEquiv p R : 𝕎 R →+* ℕ → R) = ghostMap :=
  rfl
#align witt_vector.ghost_equiv_coe WittVector.ghostEquiv_coe

theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R → ℕ → R) :=
  (ghostEquiv p R).bijective
#align witt_vector.ghost_map.bijective_of_invertible WittVector.ghostMap.bijective_of_invertible

end Invertible

/-- `WittVector.coeff x 0` as a `RingHom` -/
@[simps]
noncomputable def constantCoeff : 𝕎 R →+* R where
  toFun x := x.coeff 0
  map_zero' := by simp
                  -- 🎉 no goals
                 -- 🎉 no goals
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero
#align witt_vector.constant_coeff WittVector.constantCoeff

instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial

end WittVector
