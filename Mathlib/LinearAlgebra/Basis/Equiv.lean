/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis.Constr

/-!
# Equivalence of modules given equivalence of bases

Two modules over the same ring with equivalent index types are linearly equivalent.
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

section Equiv

variable (i : ι)
variable {M'' : Type*} (b' : Basis ι' R M') (e : ι ≃ ι')
variable [AddCommMonoid M''] [Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]

@[simp]
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp

@[simp]
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]
theorem equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext' fun i => by simp

@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.equiv b' e) = b'.reindex e.symm := by
  ext i
  simp

section CommSemiring

variable {R M M' : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (b : Basis ι R M) (b' : Basis ι' R M')
variable [SMulCommClass R R M']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }

@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _

@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _

theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]

end CommSemiring

end Equiv

end Basis

end Module
