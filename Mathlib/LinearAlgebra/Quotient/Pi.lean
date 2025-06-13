/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodule quotients and direct sums

This file contains some results on the quotient of a module by a direct sum of submodules,
and the direct sum of quotients of modules by submodules.

# Main definitions

* `Submodule.piQuotientLift`: create a map out of the direct sum of quotients
* `Submodule.quotientPiLift`: create a map out of the quotient of a direct sum
* `Submodule.quotientPi`: the quotient of a direct sum is the direct sum of quotients.

-/


namespace Submodule

open LinearMap

variable {ι R : Type*} [CommRing R]
variable {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {Ns : ι → Type*} [∀ i, AddCommGroup (Ns i)] [∀ i, Module R (Ns i)]

/-- Lift a family of maps to the direct sum of quotients. -/
def piQuotientLift [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i)) (q : Submodule R N)
    (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) : (∀ i, Ms i ⧸ p i) →ₗ[R] N ⧸ q :=
  lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)

@[simp]
theorem piQuotientLift_mk [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i))
    (q : Submodule R N) (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : ∀ i, Ms i) :
    (piQuotientLift p q f hf fun i => Quotient.mk (x i)) = Quotient.mk (lsum _ _ R f x) := by
  rw [piQuotientLift, lsum_apply, sum_apply, ← mkQ_apply, lsum_apply, sum_apply, _root_.map_sum]
  simp only [coe_proj, mapQ_apply, mkQ_apply, comp_apply]

@[simp]
theorem piQuotientLift_single [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i))
    (q : Submodule R N) (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i)
    (x : Ms i ⧸ p i) : piQuotientLift p q f hf (Pi.single i x) = mapQ _ _ (f i) (hf i) x := by
  simp_rw [piQuotientLift, lsum_apply, sum_apply, comp_apply, proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro j - hj
    rw [Pi.single_eq_of_ne hj, map_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

/-- Lift a family of maps to a quotient of direct sums. -/
def quotientPiLift (p : ∀ i, Submodule R (Ms i)) (f : ∀ i, Ms i →ₗ[R] Ns i)
    (hf : ∀ i, p i ≤ ker (f i)) : (∀ i, Ms i) ⧸ pi Set.univ p →ₗ[R] ∀ i, Ns i :=
  (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
    mem_ker.mpr <| by
      ext i
      simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))

@[simp]
theorem quotientPiLift_mk (p : ∀ i, Submodule R (Ms i)) (f : ∀ i, Ms i →ₗ[R] Ns i)
    (hf : ∀ i, p i ≤ ker (f i)) (x : ∀ i, Ms i) :
    quotientPiLift p f hf (Quotient.mk x) = fun i => f i (x i) :=
  rfl

namespace quotientPi_aux

variable (p : ∀ i, Submodule R (Ms i))

@[simp]
def toFun : ((∀ i, Ms i) ⧸ pi Set.univ p) → ∀ i, Ms i ⧸ p i :=
  quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge

theorem map_add (x y : ((i : ι) → Ms i) ⧸ pi Set.univ p) :
    toFun p (x + y) = toFun p x + toFun p y :=
  LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y

theorem map_smul (r : R) (x : ((i : ι) → Ms i) ⧸ pi Set.univ p) :
    toFun p (r • x) = (RingHom.id R r) • toFun p x :=
  LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x

variable [Fintype ι] [DecidableEq ι]

@[simp]
def invFun : (∀ i, Ms i ⧸ p i) → (∀ i, Ms i) ⧸ pi Set.univ p :=
  piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p

theorem left_inv : Function.LeftInverse (invFun p) (toFun p) := fun x =>
  Submodule.Quotient.induction_on _ x fun x' => by
    dsimp only [toFun, invFun]
    rw [quotientPiLift_mk p, funext fun i => (mkQ_apply (p i) (x' i)), piQuotientLift_mk p,
      lsum_single, id_apply]

theorem right_inv : Function.RightInverse (invFun p) (toFun p) := by
  dsimp only [toFun, invFun]
  rw [Function.rightInverse_iff_comp, ← coe_comp, ← @id_coe R]
  refine congr_arg _ (pi_ext fun i x => Submodule.Quotient.induction_on _ x fun x' =>
    funext fun j => ?_)
  rw [comp_apply, piQuotientLift_single, mapQ_apply,
    quotientPiLift_mk, id_apply]
  by_cases hij : i = j <;> simp only [mkQ_apply, coe_single]
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hij), Quotient.mk_zero]

end quotientPi_aux

open quotientPi_aux in
/-- The quotient of a direct sum is the direct sum of quotients. -/
@[simps!]
def quotientPi [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i)) :
    ((∀ i, Ms i) ⧸ pi Set.univ p) ≃ₗ[R] ∀ i, Ms i ⧸ p i where
  toFun := toFun p
  invFun := invFun p
  map_add' := map_add p
  map_smul' := quotientPi_aux.map_smul p
  left_inv := left_inv p
  right_inv := right_inv p

end Submodule
