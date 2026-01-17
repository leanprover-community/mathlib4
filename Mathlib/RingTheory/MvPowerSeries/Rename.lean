/-
Copyright (c) 2025 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Andrew Yang
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series under an embedding,
which modifies the set of variables.

This file is patterned after `MvPolynomials/rename.lean`

## Main declarations

* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`

## Notation

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `x : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPowerSeries σ R`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p q : MvPowerSeries σ R`

-/

@[expose] public section


noncomputable section

open Finset Finsupp

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]
variable (f : σ ↪ τ)

namespace MvPowerSeries

/-- Rename all the variables in a multivariable power series by an embedding, as a function. -/
def renameFun (p : MvPowerSeries σ R) : MvPowerSeries τ R := Function.extend (embDomain f) p 0

@[simp]
theorem coeff_embDomain_renameFun (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    (renameFun f p).coeff (embDomain f x)  = p.coeff x :=
  ((embDomain_injective f).factorsThrough _).extend_apply _ _

theorem coeff_renameFun_eq_zero_of_notMem_range_embDomain (p : MvPowerSeries σ R) {x : τ →₀ ℕ}
    (h : x ∉ Set.range (embDomain f)) : (renameFun f p).coeff x = 0 := by
  rw [renameFun, coeff, LinearMap.proj, LinearMap.coe_mk, AddHom.coe_mk, Function.eval,
    Function.extend, dite_cond_eq_false (by grind), Pi.zero_apply]

theorem renameFun_monomial (x) (r : R) :
    renameFun f (monomial x r) = monomial (embDomain f x) r := by
  classical
  ext y; by_cases h : y ∈ Set.range (embDomain f)
  · rcases h with ⟨a, rfl⟩
    simp [coeff_monomial]
  · rw [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h, coeff_monomial,
      if_neg (by grind)]

theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x; by_cases h : x ∈ Set.range (embDomain f)
  · rcases h with ⟨y, rfl⟩
    simp [coeff_mul, ← antidiagonal_image_prodMap_embDomain, sum_image
      (Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective f,
        embDomain_injective f⟩))]
  rw [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h, eq_comm, coeff_mul]
  refine sum_eq_zero fun i i_in ↦ ?_
  rw [mem_antidiagonal] at i_in
  obtain (h' | h') : i.1 ∉ Set.range (embDomain f) ∨ i.2 ∉ Set.range (embDomain f) := by
    revert h; contrapose!
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨u + v, by simpa [hu, hv]⟩
  · rw [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h', zero_mul]
  rw [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h', mul_zero]

/-- Rename all the variables in a multivariable power series by an embedding, as an `AlgHom`. -/
@[simps] def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R := {
  toFun := renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; rw [renameFun, Function.extend_zero]
  map_add' _ _ := by
    simp only [renameFun]
    nth_rw 1 [← add_zero (0 : (τ →₀ ℕ) → R), Function.extend_add]
  commutes' := renameFun_monomial f 0
}

@[simp]
theorem rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r := renameFun_monomial f 0 r

@[simp]
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using renameFun_monomial f (single i 1) 1

theorem map_rename (F : R →+* S) (p : MvPowerSeries σ R) :
    map F (rename f p) = rename f (map F p) := by
  ext x
  by_cases h : x ∈ Set.range (embDomain f)
  · rcases h with ⟨_, rfl⟩
    simp
  simp [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h]

@[simp]
theorem rename_rename (g : τ ↪ α) (p : MvPowerSeries σ R) :
    rename g (rename f p) = rename (f.trans g) p := by
  ext x
  by_cases h : x ∈ Set.range (embDomain g)
  · rcases h with ⟨y, rfl⟩
    simp only [rename_apply, coeff_embDomain_renameFun]
    by_cases h' : y ∈ Set.range (embDomain f)
    · rcases h' with ⟨_, rfl⟩
      simp [← embDomain_comp]
    rw [coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h',
      coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _
        (show embDomain g y ∉ Set.range (embDomain (f.trans g)) by
          rintro ⟨_, _⟩; grind [embDomain_comp, embDomain_inj])]
  rw [rename_apply, coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _ h,
    rename_apply, coeff_renameFun_eq_zero_of_notMem_range_embDomain _ _
      (show x ∉ Set.range (embDomain (f.trans g)) by
        rintro ⟨_, _⟩; grind [embDomain_comp, embDomain_inj])]

lemma rename_comp_rename (g : τ ↪ α) :
    (rename (R := R) g).comp (rename f) = rename (f.trans g) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
theorem rename_id : rename (Function.Embedding.refl _) = AlgHom.id R (MvPowerSeries σ R) :=
  AlgHom.ext fun p ↦ by simp [renameFun]

lemma rename_id_apply (p : MvPowerSeries σ R) :
    rename (Function.Embedding.refl _) p = p := by simp

theorem rename_monomial (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  simpa [embDomain_eq_mapDomain] using renameFun_monomial f d r

@[simp]
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename f p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, rename_apply,
    show (0 : τ →₀ ℕ) = embDomain f 0 by simp, coeff_embDomain_renameFun]

theorem rename_injective : Function.Injective (rename (R := R) f) := by
  intro _ _ h; ext x
  simp only [rename_apply, MvPowerSeries.ext_iff] at h
  simpa using h (embDomain f x)

/-- Given an embedding `f : σ ↪ τ`, `MvPowerSeries.killComplFun f` is the function from
  `R[[τ]]` to `R[[σ]]` that is left inverse to `rename f : R[[σ]] → R[[τ]]` and sends the
  variables in the complement of the range of `f` to `0`. -/
def killComplFun (p : MvPowerSeries τ R) : MvPowerSeries σ R := fun x ↦ coeff (embDomain f x) p

theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
  coeff x (killComplFun f p) = coeff (embDomain f x) p := rfl

@[simp] theorem killComplFun_monomial_embDomain (x) (r : R) :
    killComplFun f (monomial (embDomain f x) r) = monomial x r := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]

theorem killComplFun_monomial_eq_zero_of_notMem_range_embDomain {x} (r : R)
    (h : x ∉ Set.range (embDomain f)) : killComplFun f (monomial x r) = 0 := by
  classical
  ext; simp only [coeff_killComplFun, coeff_monomial, coeff_zero, ite_eq_right_iff]
  grind

theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun f (p * q) = killComplFun f p * killComplFun f q := by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← antidiagonal_image_prodMap_embDomain, sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective f,
      embDomain_injective f⟩)))]

/-- The `AlgHom` version of `killComplFun`. -/
@[simps] def killCompl : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R := {
  toFun := killComplFun f
  map_one' := by simpa using killComplFun_monomial_embDomain f 0 1
  map_mul' := killComplFun_mul f
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using killComplFun_monomial_embDomain f 0
}

lemma killCompl_C (r : R) : killCompl f (C r) = C r := by
  simpa using killComplFun_monomial_embDomain f 0 r

theorem killCompl_X (i : σ) : killCompl (R := R) f (X (f i)) = X i := by
  classical
  ext
  simp [coeff_killComplFun, coeff_X, ← embDomain_single]

theorem killCompl_X_eq_zero_of_notMem_range {t} (h : t ∉ Set.range f) :
    killCompl (R := R) f (X t) = 0 := by
  classical
  ext y
  rw [killCompl_apply, coeff_killComplFun, coeff_X, coeff_zero, ite_eq_right_iff,
    Finsupp.ext_iff]
  intro h'; specialize h' t
  simp [embDomain_notin_range _ _ _ h] at h'

theorem killCompl_comp_rename : (killCompl f).comp (rename f) = AlgHom.id R _ := by
  ext; simp [coeff_killComplFun]

@[simp]
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl f (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename f) p

variable (R)

/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R := {
  rename e with
  invFun := rename e.symm
  left_inv _ := by simp [-rename_apply]
  right_inv _ := by simp [-rename_apply]
}

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl

@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e.toEmbedding f.toEmbedding)

end MvPowerSeries
