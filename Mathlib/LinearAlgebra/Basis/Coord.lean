/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Coordinates of vectors with respect to a basis.

## Main definitions

* `Basis.coord`: `b.coord i x` is the `i`-th coordinate of a vector `x` with respect to the basis
  `b`.
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace Basis

variable (b : Basis ι R M)

section Coord

variable (i : ι)

/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps!]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr

theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun _ => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)

@[simp]
theorem coe_sumCoords : (b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id :=
  rfl

@[simp high]
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.coord i := by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coeFn_sum]

@[simp]
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
  ⟨b.coord i m, by simp⟩

theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) :
    b.coord i (b.repr.symm f) = f i := by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]

theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

variable (e : ι ≃ ι')

@[simp]
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

theorem coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι → R) :
    b.coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

end Coord

variable {v : ι → M} {x y : M}

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

variable {hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

end Mk

end Basis

end Module
