/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

#align_import linear_algebra.exterior_algebra.of_alternating from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Extending an alternating map to the exterior algebra

## Main definitions

* `ExteriorAlgebra.liftAlternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `ExteriorAlgebra.liftAlternatingEquiv`: the above as a linear equivalence

## Main results

* `ExteriorAlgebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/


variable {R M N N' : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
variable [Module R M] [Module R N] [Module R N']

-- This instance can't be found where it's needed if we don't remind lean that it exists.
instance AlternatingMap.instModuleAddCommGroup {ι : Type*} :
    Module R (M [⋀^ι]→ₗ[R] N) := by
  infer_instance
#align alternating_map.module_add_comm_group AlternatingMap.instModuleAddCommGroup

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def liftAlternating : (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R] ExteriorAlgebra R M →ₗ[R] N := by
  suffices
    (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R]
      ExteriorAlgebra R M →ₗ[R] ∀ i, M [⋀^Fin i]→ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlgebra.foldl _ ?_ ?_
  · refine
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => ?_) (fun c m f => ?_)
        (fun m f₁ f₂ => ?_) fun c m f => ?_
    all_goals
      ext i : 1
      simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, AlternatingMap.curryLeft_add,
        AlternatingMap.curryLeft_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    dsimp only [LinearMap.mk₂_apply, QuadraticForm.coeFn_zero, Pi.zero_apply]
    simp only [Nat.succ_eq_add_one, AlternatingMap.curryLeft_same, Pi.zero_apply, zero_smul]
    rfl
#align exterior_algebra.lift_alternating ExteriorAlgebra.liftAlternating

@[simp]
theorem liftAlternating_ι (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (m : M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m) = f 1 ![m] := by
  dsimp [liftAlternating]
  rw [foldl_ι, LinearMap.mk₂_apply, AlternatingMap.curryLeft_apply_apply]
  congr
  -- Porting note: In Lean 3, `congr` could use the `[Subsingleton (Fin 0 → M)]` instance to finish
  -- the proof. Here, the instance can be synthesized but `congr` does not use it so the following
  -- line is provided.
  rw [Matrix.zero_empty]
#align exterior_algebra.lift_alternating_ι ExteriorAlgebra.liftAlternating_ι

theorem liftAlternating_ι_mul (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (m : M)
    (x : ExteriorAlgebra R M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m * x) =
    liftAlternating (R := R) (M := M) (N := N) (fun i => (f i.succ).curryLeft m) x := by
  dsimp [liftAlternating]
  rw [foldl_mul, foldl_ι]
  rfl
#align exterior_algebra.lift_alternating_ι_mul ExteriorAlgebra.liftAlternating_ι_mul

@[simp]
theorem liftAlternating_one (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    liftAlternating (R := R) (M := M) (N := N) f (1 : ExteriorAlgebra R M) = f 0 0 := by
  dsimp [liftAlternating]
  rw [foldl_one]
#align exterior_algebra.lift_alternating_one ExteriorAlgebra.liftAlternating_one

@[simp]
theorem liftAlternating_algebraMap (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (r : R) :
    liftAlternating (R := R) (M := M) (N := N) f (algebraMap _ (ExteriorAlgebra R M) r) =
    r • f 0 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, liftAlternating_one]
#align exterior_algebra.lift_alternating_algebra_map ExteriorAlgebra.liftAlternating_algebraMap

@[simp]
theorem liftAlternating_apply_ιMulti {n : ℕ} (f : ∀ i, M [⋀^Fin i]→ₗ[R] N)
    (v : Fin n → M) : liftAlternating (R := R) (M := M) (N := N) f (ιMulti R n v) = f n v := by
  rw [ιMulti_apply]
  -- Porting note: `v` is generalized automatically so it was removed from the next line
  induction' n with n ih generalizing f
  · -- Porting note: Lean does not automatically synthesize the instance
    -- `[Subsingleton (Fin 0 → M)]` which is needed for `Subsingleton.elim 0 v` on line 114.
    letI : Subsingleton (Fin 0 → M) := by infer_instance
    rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
  · rw [List.ofFn_succ, List.prod_cons, liftAlternating_ι_mul, ih,
      AlternatingMap.curryLeft_apply_apply]
    congr
    exact Matrix.cons_head_tail _
#align exterior_algebra.lift_alternating_apply_ι_multi ExteriorAlgebra.liftAlternating_apply_ιMulti

@[simp]
theorem liftAlternating_comp_ιMulti {n : ℕ} (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N) f).compAlternatingMap (ιMulti R n) = f n :=
  AlternatingMap.ext <| liftAlternating_apply_ιMulti f
#align exterior_algebra.lift_alternating_comp_ι_multi ExteriorAlgebra.liftAlternating_comp_ιMulti

@[simp]
theorem liftAlternating_comp (g : N →ₗ[R] N') (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N') fun i => g.compAlternatingMap (f i)) =
    g ∘ₗ liftAlternating (R := R) (M := M) (N := N) f := by
  ext v
  rw [LinearMap.comp_apply]
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx generalizing f
  · rw [liftAlternating_algebraMap, liftAlternating_algebraMap, map_smul,
      LinearMap.compAlternatingMap_apply]
  · rw [map_add, map_add, map_add, hx, hy]
  · rw [liftAlternating_ι_mul, liftAlternating_ι_mul, ← hx]
    simp_rw [AlternatingMap.curryLeft_compAlternatingMap]
#align exterior_algebra.lift_alternating_comp ExteriorAlgebra.liftAlternating_comp

@[simp]
theorem liftAlternating_ιMulti :
    liftAlternating (R := R) (M := M) (N := ExteriorAlgebra R M) (ιMulti R) =
    (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  ext v
  dsimp
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx
  · rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  · rw [map_add, hx, hy]
  · simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlternating_comp,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, hx]
#align exterior_algebra.lift_alternating_ι_multi ExteriorAlgebra.liftAlternating_ιMulti

/-- `ExteriorAlgebra.liftAlternating` is an equivalence. -/
@[simps apply symm_apply]
def liftAlternatingEquiv : (∀ i, M [⋀^Fin i]→ₗ[R] N) ≃ₗ[R] ExteriorAlgebra R M →ₗ[R] N where
  toFun := liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv f := funext fun i => liftAlternating_comp_ιMulti _
  right_inv F :=
    (liftAlternating_comp _ _).trans <| by rw [liftAlternating_ιMulti, LinearMap.comp_id]
#align exterior_algebra.lift_alternating_equiv ExteriorAlgebra.liftAlternatingEquiv

/-- To show that two linear maps from the exterior algebra agree, it suffices to show they agree on
the exterior powers.

See note [partially-applied ext lemmas] -/
@[ext]
theorem lhom_ext ⦃f g : ExteriorAlgebra R M →ₗ[R] N⦄
    (h : ∀ i, f.compAlternatingMap (ιMulti R i) = g.compAlternatingMap (ιMulti R i)) : f = g :=
  liftAlternatingEquiv.symm.injective <| funext h
#align exterior_algebra.lhom_ext ExteriorAlgebra.lhom_ext

end ExteriorAlgebra
