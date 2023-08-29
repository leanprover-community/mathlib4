/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

#align_import linear_algebra.clifford_algebra.fold from "leanprover-community/mathlib"@"446eb51ce0a90f8385f260d2b52e760e2004246b"

/-!
# Recursive computation rules for the Clifford algebra

This file provides API for a special case `CliffordAlgebra.foldr` of the universal property
`CliffordAlgebra.lift` with `A = Module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `CliffordAlgebra.foldl`, implemented via
`CliffordAlgebra.reverse`

## Main definitions

* `CliffordAlgebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `CliffordAlgebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `CliffordAlgebra.right_induction`: an induction rule that adds generators from the right.
* `CliffordAlgebra.left_induction`: an induction rule that adds generators from the left.
-/


universe u1 u2 u3

variable {R M N : Type*}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section Foldr

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip
#align clifford_algebra.foldr CliffordAlgebra.foldr

@[simp]
theorem foldr_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldr Q f hf n (ι Q m) = f m n :=
  LinearMap.congr_fun (lift_ι_apply _ _ _) n
#align clifford_algebra.foldr_ι CliffordAlgebra.foldr_ι

@[simp]
theorem foldr_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldr Q f hf n (algebraMap R _ r) = r • n :=
  LinearMap.congr_fun (AlgHom.commutes _ r) n
#align clifford_algebra.foldr_algebra_map CliffordAlgebra.foldr_algebraMap

@[simp]
theorem foldr_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldr Q f hf n 1 = n :=
  LinearMap.congr_fun (AlgHom.map_one _) n
#align clifford_algebra.foldr_one CliffordAlgebra.foldr_one

@[simp]
theorem foldr_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
  LinearMap.congr_fun (AlgHom.map_mul _ _ _) n
#align clifford_algebra.foldr_mul CliffordAlgebra.foldr_mul

/-- This lemma demonstrates the origin of the `foldr` name. -/
theorem foldr_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldr Q f hf n (l.map <| ι Q).prod = List.foldr (fun m n => f m n) n l := by
  induction' l with hd tl ih
  -- ⊢ ↑(↑(foldr Q f hf) n) (List.prod (List.map ↑(ι Q) [])) = List.foldr (fun m n  …
  · rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
    -- 🎉 no goals
  · rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]
    -- 🎉 no goals
#align clifford_algebra.foldr_prod_map_ι CliffordAlgebra.foldr_prod_map_ι

end Foldr

section Foldl

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldl Q f hf n (ι Q m * x) = f m (foldl Q f hf n x)`.

For example, `foldl f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldl (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.compl₂ (foldr Q f hf) reverse
#align clifford_algebra.foldl CliffordAlgebra.foldl

@[simp]
theorem foldl_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldl Q f hf n (reverse x) = foldr Q f hf n x :=
  FunLike.congr_arg (foldr Q f hf n) <| reverse_reverse _
#align clifford_algebra.foldl_reverse CliffordAlgebra.foldl_reverse

@[simp]
theorem foldr_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldr Q f hf n (reverse x) = foldl Q f hf n x :=
  rfl
#align clifford_algebra.foldr_reverse CliffordAlgebra.foldr_reverse

@[simp]
theorem foldl_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldl Q f hf n (ι Q m) = f m n := by
  rw [← foldr_reverse, reverse_ι, foldr_ι]
  -- 🎉 no goals
#align clifford_algebra.foldl_ι CliffordAlgebra.foldl_ι

@[simp]
theorem foldl_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldl Q f hf n (algebraMap R _ r) = r • n := by
  rw [← foldr_reverse, reverse.commutes, foldr_algebraMap]
  -- 🎉 no goals
#align clifford_algebra.foldl_algebra_map CliffordAlgebra.foldl_algebraMap

@[simp]
theorem foldl_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldl Q f hf n 1 = n := by
  rw [← foldr_reverse, reverse.map_one, foldr_one]
  -- 🎉 no goals
#align clifford_algebra.foldl_one CliffordAlgebra.foldl_one

@[simp]
theorem foldl_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b := by
  rw [← foldr_reverse, ← foldr_reverse, ← foldr_reverse, reverse.map_mul, foldr_mul]
  -- 🎉 no goals
#align clifford_algebra.foldl_mul CliffordAlgebra.foldl_mul

/-- This lemma demonstrates the origin of the `foldl` name. -/
theorem foldl_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldl Q f hf n (l.map <| ι Q).prod = List.foldl (fun m n => f n m) n l := by
  rw [← foldr_reverse, reverse_prod_map_ι, ← List.map_reverse, foldr_prod_map_ι, List.foldr_reverse]
  -- 🎉 no goals
#align clifford_algebra.foldl_prod_map_ι CliffordAlgebra.foldl_prod_map_ι

end Foldl

theorem right_induction {P : CliffordAlgebra Q → Prop} (hr : ∀ r : R, P (algebraMap _ _ r))
    (h_add : ∀ x y, P x → P y → P (x + y)) (h_ι_mul : ∀ m x, P x → P (x * ι Q m)) : ∀ x, P x := by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `CliffordAlgebra.induction`, but going via the grading seems easier. -/
  intro x
  -- ⊢ P x
  have : x ∈ ⊤ := Submodule.mem_top (R := R)
  -- ⊢ P x
  rw [← iSup_ι_range_eq_top] at this
  -- ⊢ P x
  induction this using Submodule.iSup_induction' with -- _ this (fun i x hx => ?_) _ h_add
  | hp i x hx =>
    induction hx using Submodule.pow_induction_on_right' with
    | hr r => exact hr r
    | hadd _x _y _i _ _ ihx ihy => exact h_add _ _ ihx ihy
    | hmul _i x _hx px m hm =>
      obtain ⟨m, rfl⟩ := hm
      exact h_ι_mul _ _ px
  | h0 => simpa only [map_zero] using hr 0
  | hadd _x _y _ _ ihx ihy =>
    exact h_add _ _ ihx ihy
#align clifford_algebra.right_induction CliffordAlgebra.right_induction

theorem left_induction {P : CliffordAlgebra Q → Prop} (hr : ∀ r : R, P (algebraMap _ _ r))
    (h_add : ∀ x y, P x → P y → P (x + y)) (h_mul_ι : ∀ x m, P x → P (ι Q m * x)) : ∀ x, P x := by
  refine' reverse_involutive.surjective.forall.2 _
  -- ⊢ ∀ (x : CliffordAlgebra Q), P (↑reverse x)
  intro x
  -- ⊢ P (↑reverse x)
  induction' x using CliffordAlgebra.right_induction with r x y hx hy m x hx
  · simpa only [reverse.commutes] using hr r
    -- 🎉 no goals
  · simpa only [map_add] using h_add _ _ hx hy
    -- 🎉 no goals
  · simpa only [reverse.map_mul, reverse_ι] using h_mul_ι _ _ hx
    -- 🎉 no goals
#align clifford_algebra.left_induction CliffordAlgebra.left_induction

/-! ### Versions with extra state -/


/-- Auxiliary definition for `CliffordAlgebra.foldr'` -/
def foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) :
    M →ₗ[R] Module.End R (CliffordAlgebra Q × N) := by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  -- ⊢ M →ₗ[R] Module.End R (CliffordAlgebra Q × N)
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  -- ⊢ M →ₗ[R] Module.End R (CliffordAlgebra Q × N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearMap.congr_fun (f.map_add _ _) x)
      map_smul' := fun c v =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_smul _ _) x)
            (LinearMap.congr_fun (f.map_smul _ _) x) }
#align clifford_algebra.foldr'_aux CliffordAlgebra.foldr'Aux

theorem foldr'Aux_apply_apply (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    foldr'Aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) :=
  rfl
#align clifford_algebra.foldr'_aux_apply_apply CliffordAlgebra.foldr'Aux_apply_apply

theorem foldr'Aux_foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (v : M) (x_fx) :
    foldr'Aux Q f v (foldr'Aux Q f v x_fx) = Q v • x_fx := by
  cases' x_fx with x fx
  -- ⊢ ↑(↑(foldr'Aux Q f) v) (↑(↑(foldr'Aux Q f) v) (x, fx)) = ↑Q v • (x, fx)
  simp only [foldr'Aux_apply_apply]
  -- ⊢ (↑(ι Q) v * (↑(ι Q) v * x), ↑(↑f v) (↑(ι Q) v * x, ↑(↑f v) (x, fx))) = ↑Q v  …
  rw [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, hf, Prod.smul_mk]
  -- 🎉 no goals
#align clifford_algebra.foldr'_aux_foldr'_aux CliffordAlgebra.foldr'Aux_foldr'Aux

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `CliffordAlgebra.foldr`, but with an extra `x` argument.
Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
def foldr' (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n : N) : CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)
#align clifford_algebra.foldr' CliffordAlgebra.foldr'

theorem foldr'_algebraMap (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
    foldr' Q f hf n (algebraMap R _ r) = r • n :=
  congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)
#align clifford_algebra.foldr'_algebra_map CliffordAlgebra.foldr'_algebraMap

theorem foldr'_ι (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
    foldr' Q f hf n (ι Q m) = f m (1, n) :=
  congr_arg Prod.snd (foldr_ι _ _ _ _ _)
#align clifford_algebra.foldr'_ι CliffordAlgebra.foldr'_ι

theorem foldr'_ι_mul (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
    foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) := by
  dsimp [foldr']
  -- ⊢ (↑(↑(foldr Q (foldr'Aux Q f) (_ : ∀ (v : M) (x_fx : CliffordAlgebra Q × N),  …
  rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply]
  -- ⊢ (↑(ι Q) m * (↑(↑(foldr Q (foldr'Aux Q f) (_ : ∀ (v : M) (x_fx : CliffordAlge …
  refine' congr_arg (f m) (Prod.mk.eta.symm.trans _)
  -- ⊢ ((↑(↑(foldr Q (foldr'Aux Q f) (_ : ∀ (v : M) (x_fx : CliffordAlgebra Q × N), …
  congr 1
  -- ⊢ (↑(↑(foldr Q (foldr'Aux Q f) (_ : ∀ (v : M) (x_fx : CliffordAlgebra Q × N),  …
  induction' x using CliffordAlgebra.left_induction with r x y hx hy m x hx
  · simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
    -- 🎉 no goals
  · rw [map_add, Prod.fst_add, hx, hy]
    -- 🎉 no goals
  · rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply, hx]
    -- 🎉 no goals
#align clifford_algebra.foldr'_ι_mul CliffordAlgebra.foldr'_ι_mul

end CliffordAlgebra
