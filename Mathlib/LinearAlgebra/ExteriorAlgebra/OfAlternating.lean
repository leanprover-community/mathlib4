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
    Module R (AlternatingMap R M N ι) := by
  infer_instance
  -- 🎉 no goals
#align alternating_map.module_add_comm_group AlternatingMap.instModuleAddCommGroup

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def liftAlternating : (∀ i, AlternatingMap R M N (Fin i)) →ₗ[R] ExteriorAlgebra R M →ₗ[R] N := by
  suffices
    (∀ i, AlternatingMap R M N (Fin i)) →ₗ[R]
      ExteriorAlgebra R M →ₗ[R] ∀ i, AlternatingMap R M N (Fin i) by
    refine' LinearMap.compr₂ this _
    refine' (LinearEquiv.toLinearMap _).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine' CliffordAlgebra.foldl _ _ _
  -- ⊢ M →ₗ[R] ((i : ℕ) → AlternatingMap R M N (Fin i)) →ₗ[R] (i : ℕ) → Alternating …
  · refine'
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => _) (fun c m f => _)
        (fun m f₁ f₂ => _) fun c m f => _
    all_goals
      ext i : 1
      simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, AlternatingMap.curryLeft_add,
        AlternatingMap.curryLeft_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    -- ⊢ ↑(↑(LinearMap.mk₂ R (fun m f i => ↑(AlternatingMap.curryLeft (f (Nat.succ i) …
    dsimp only [LinearMap.mk₂_apply, QuadraticForm.coeFn_zero, Pi.zero_apply]
    -- ⊢ (fun i => ↑(AlternatingMap.curryLeft (↑(AlternatingMap.curryLeft (x (Nat.suc …
    simp_rw [zero_smul]
    -- ⊢ (fun i => ↑(AlternatingMap.curryLeft (↑(AlternatingMap.curryLeft (x (Nat.suc …
    ext i : 1
    -- ⊢ ↑(AlternatingMap.curryLeft (↑(AlternatingMap.curryLeft (x (Nat.succ (Nat.suc …
    exact AlternatingMap.curryLeft_same _ _
    -- 🎉 no goals
#align exterior_algebra.lift_alternating ExteriorAlgebra.liftAlternating

@[simp]
theorem liftAlternating_ι (f : ∀ i, AlternatingMap R M N (Fin i)) (m : M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m) = f 1 ![m] := by
  dsimp [liftAlternating]
  -- ⊢ ↑(↑(↑(foldl 0 (LinearMap.mk₂ R (fun m f i => ↑(AlternatingMap.curryLeft (f ( …
  rw [foldl_ι, LinearMap.mk₂_apply, AlternatingMap.curryLeft_apply_apply]
  -- ⊢ ↑(f (Nat.succ 0)) (Matrix.vecCons m 0) = ↑(f 1) ![m]
  congr
  -- ⊢ Matrix.vecCons m 0 = ![m]
  -- porting note: In Lean 3, `congr` could use the `[Subsingleton (Fin 0 → M)]` instance to finish
  -- the proof. Here, the instance can be synthesized but `congr` does not use it so the following
  -- line is provided.
  rw [Matrix.zero_empty]
  -- 🎉 no goals
#align exterior_algebra.lift_alternating_ι ExteriorAlgebra.liftAlternating_ι

theorem liftAlternating_ι_mul (f : ∀ i, AlternatingMap R M N (Fin i)) (m : M)
    (x : ExteriorAlgebra R M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m * x) =
    liftAlternating (R := R) (M := M) (N := N) (fun i => (f i.succ).curryLeft m) x := by
  dsimp [liftAlternating]
  -- ⊢ ↑(↑(↑(foldl 0 (LinearMap.mk₂ R (fun m f i => ↑(AlternatingMap.curryLeft (f ( …
  rw [foldl_mul, foldl_ι]
  -- ⊢ ↑(↑(↑(foldl 0 (LinearMap.mk₂ R (fun m f i => ↑(AlternatingMap.curryLeft (f ( …
  rfl
  -- 🎉 no goals
#align exterior_algebra.lift_alternating_ι_mul ExteriorAlgebra.liftAlternating_ι_mul

@[simp]
theorem liftAlternating_one (f : ∀ i, AlternatingMap R M N (Fin i)) :
    liftAlternating (R := R) (M := M) (N := N) f (1 : ExteriorAlgebra R M) = f 0 0 := by
  dsimp [liftAlternating]
  -- ⊢ ↑(↑(↑(foldl 0 (LinearMap.mk₂ R (fun m f i => ↑(AlternatingMap.curryLeft (f ( …
  rw [foldl_one]
  -- 🎉 no goals
#align exterior_algebra.lift_alternating_one ExteriorAlgebra.liftAlternating_one

@[simp]
theorem liftAlternating_algebraMap (f : ∀ i, AlternatingMap R M N (Fin i)) (r : R) :
    liftAlternating (R := R) (M := M) (N := N) f (algebraMap _ (ExteriorAlgebra R M) r) =
    r • f 0 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, liftAlternating_one]
  -- 🎉 no goals
#align exterior_algebra.lift_alternating_algebra_map ExteriorAlgebra.liftAlternating_algebraMap

@[simp]
theorem liftAlternating_apply_ιMulti {n : ℕ} (f : ∀ i, AlternatingMap R M N (Fin i))
    (v : Fin n → M) : liftAlternating (R := R) (M := M) (N := N) f (ιMulti R n v) = f n v := by
  rw [ιMulti_apply]
  -- ⊢ ↑(↑liftAlternating f) (List.prod (List.ofFn fun i => ↑(ι R) (v i))) = ↑(f n) v
  -- porting note: `v` is generalized automatically so it was removed from the next line
  induction' n with n ih generalizing f
  -- ⊢ ↑(↑liftAlternating f) (List.prod (List.ofFn fun i => ↑(ι R) (v i))) = ↑(f Na …
  · -- porting note: Lean does not automatically synthesize the instance
    -- `[Subsingleton (Fin 0 → M)]` which is needed for `Subsingleton.elim 0 v` on line 114.
    letI : Subsingleton (Fin 0 → M) := by infer_instance
    -- ⊢ ↑(↑liftAlternating f) (List.prod (List.ofFn fun i => ↑(ι R) (v i))) = ↑(f Na …
    rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
    -- 🎉 no goals
  · rw [List.ofFn_succ, List.prod_cons, liftAlternating_ι_mul, ih,
      AlternatingMap.curryLeft_apply_apply]
    congr
    -- ⊢ (Matrix.vecCons (v 0) fun i => v (Fin.succ i)) = v
    exact Matrix.cons_head_tail _
    -- 🎉 no goals
#align exterior_algebra.lift_alternating_apply_ι_multi ExteriorAlgebra.liftAlternating_apply_ιMulti

@[simp]
theorem liftAlternating_comp_ιMulti {n : ℕ} (f : ∀ i, AlternatingMap R M N (Fin i)) :
    (liftAlternating (R := R) (M := M) (N := N) f).compAlternatingMap (ιMulti R n) = f n :=
  AlternatingMap.ext <| liftAlternating_apply_ιMulti f
#align exterior_algebra.lift_alternating_comp_ι_multi ExteriorAlgebra.liftAlternating_comp_ιMulti

@[simp]
theorem liftAlternating_comp (g : N →ₗ[R] N') (f : ∀ i, AlternatingMap R M N (Fin i)) :
    (liftAlternating (R := R) (M := M) (N := N') fun i => g.compAlternatingMap (f i)) =
    g ∘ₗ liftAlternating (R := R) (M := M) (N := N) f := by
  ext v
  -- ⊢ ↑(↑liftAlternating fun i => ↑(LinearMap.compAlternatingMap g) (f i)) v = ↑(L …
  rw [LinearMap.comp_apply]
  -- ⊢ ↑(↑liftAlternating fun i => ↑(LinearMap.compAlternatingMap g) (f i)) v = ↑g  …
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx generalizing f
  · rw [liftAlternating_algebraMap, liftAlternating_algebraMap, map_smul,
      LinearMap.compAlternatingMap_apply]
  · rw [map_add, map_add, map_add, hx, hy]
    -- 🎉 no goals
  · rw [liftAlternating_ι_mul, liftAlternating_ι_mul, ← hx]
    -- ⊢ ↑(↑liftAlternating fun i => ↑(AlternatingMap.curryLeft (↑(LinearMap.compAlte …
    simp_rw [AlternatingMap.curryLeft_compAlternatingMap]
    -- 🎉 no goals
#align exterior_algebra.lift_alternating_comp ExteriorAlgebra.liftAlternating_comp

@[simp]
theorem liftAlternating_ιMulti :
    liftAlternating (R := R) (M := M) (N := ExteriorAlgebra R M) (ιMulti R) =
    (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  ext v
  -- ⊢ ↑(↑liftAlternating (ιMulti R)) v = ↑LinearMap.id v
  dsimp
  -- ⊢ ↑(↑liftAlternating (ιMulti R)) v = v
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx
  · rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
    -- 🎉 no goals
  · rw [map_add, hx, hy]
    -- 🎉 no goals
  · simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlternating_comp,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, hx]
#align exterior_algebra.lift_alternating_ι_multi ExteriorAlgebra.liftAlternating_ιMulti

/-- `ExteriorAlgebra.liftAlternating` is an equivalence. -/
@[simps apply symm_apply]
def liftAlternatingEquiv : (∀ i, AlternatingMap R M N (Fin i)) ≃ₗ[R] ExteriorAlgebra R M →ₗ[R] N
    where
  toFun := liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv f := funext fun i => liftAlternating_comp_ιMulti _
  right_inv F :=
    (liftAlternating_comp _ _).trans <| by rw [liftAlternating_ιMulti, LinearMap.comp_id]
                                           -- 🎉 no goals
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
