/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series under an injective map,
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

noncomputable section

open MvPowerSeries Finset Finsupp Classical

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]
variable {f : σ → τ} (hf : f.Injective)

namespace MvPowerSeries

def renameFun (p : MvPowerSeries σ R) : MvPowerSeries τ R :=
  fun x ↦ if SetLike.coe x.support ⊆ Set.range f then
    coeff (x.comapDomain f hf.injOn) p else 0

theorem coeff_renameFun (p : MvPowerSeries σ R) (x : τ →₀ ℕ) :
    coeff x (renameFun hf p) = if SetLike.coe x.support ⊆ Set.range f then
      coeff (x.comapDomain f hf.injOn) p else 0 := rfl

theorem renameFun_zero : renameFun hf (0 : MvPowerSeries σ R) = 0 := by
  simp [MvPowerSeries.ext_iff, coeff_renameFun]

theorem renameFun_one : renameFun hf (1 : MvPowerSeries σ R) = 1 := by
  simp only [MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def, SetLike.mem_coe,
    mem_support_iff, ne_eq, Set.mem_range, coeff_one, Finsupp.ext_iff, comapDomain_apply,
    Finsupp.coe_zero, Pi.ofNat_apply]
  intro; split_ifs
  all_goals grind only

theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun hf (p * q) = renameFun hf p * renameFun hf q := by
  ext x
  simp only [coeff_renameFun, coeff_mul, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite,
    sum_const_zero, add_zero, filter_filter]
  split_ifs with h
  · have : filter (fun x ↦ SetLike.coe x.2.support ⊆ Set.range f ∧
      SetLike.coe x.1.support ⊆ Set.range f) (antidiagonal x) = antidiagonal x := by
      simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
        Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add,
        Pi.add_apply, and_iff_left_iff_imp, Prod.forall] at h ⊢
      grind only
    rw [this]
    replace this : antidiagonal (comapDomain f x hf.injOn) = image (fun (x, y) ↦
      (comapDomain f x hf.injOn, comapDomain f y hf.injOn)) (antidiagonal x) := by
      simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
        Finset.ext_iff, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply,
        comapDomain_apply, mem_image, Prod.exists, Prod.forall, Prod.mk.injEq] at h ⊢
      refine fun a b ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
      · use mapDomain f a, mapDomain f b
        simp only [mapDomain_apply hf, implies_true, and_self, and_true]
        intro t
        by_cases! h'' : x t = 0
        · simp only [h'', Nat.add_eq_zero_iff]
          constructor; all_goals
          rw [← notMem_support_iff, mapDomain_support_of_injective hf]
          simp only [mem_image, mem_support_iff, ne_eq, not_exists, not_and]
          grind only
        obtain ⟨s, hs⟩ := h _ h''
        simp [← hs, mapDomain_apply hf, h' s]
      grind only
    rw [this, sum_image]
    · simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range, Set.InjOn,
        mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply, Prod.mk.injEq,
        comapDomain_apply, and_imp, Prod.forall] at h ⊢
      grind only
  have : filter (fun x ↦ SetLike.coe x.2.support ⊆ Set.range f ∧
    SetLike.coe x.1.support ⊆ Set.range f) (antidiagonal x) = ∅ := by
    simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
      not_forall, not_exists, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.ext_iff,
      Finsupp.coe_add, Pi.add_apply, notMem_empty, iff_false, not_and, Prod.forall] at h ⊢
    grind only
  simp [this]

theorem renameFun_add (p g : MvPowerSeries σ R) : renameFun hf (p + g) =
    renameFun hf p + renameFun hf g := by
  simp only [MvPowerSeries.ext_iff, coeff_renameFun, map_add]
  intro; split
  · rfl
  simp

theorem renameFun_commutes (r : R) : renameFun hf ((algebraMap R (MvPowerSeries σ R)) r) =
    (algebraMap R (MvPowerSeries τ R)) r := by
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.ext_iff,
    coeff_renameFun, Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
    coeff_C, Finsupp.ext_iff, comapDomain_apply, Finsupp.coe_zero, Pi.zero_apply]
  grind only

/-- Rename all the variables in a multivariable power series by an injective map. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R := {
  toFun := renameFun hf
  map_one' := renameFun_one hf
  map_mul' := renameFun_mul hf
  map_zero' := renameFun_zero hf
  map_add' := renameFun_add hf
  commutes' := renameFun_commutes hf
}

theorem rename_apply {p : MvPowerSeries σ R} : rename hf p = renameFun hf p := rfl

theorem rename_C (r : R) : rename hf (C r : MvPowerSeries σ R) = C r := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def, SetLike.mem_coe,
    mem_support_iff, ne_eq, Set.mem_range, coeff_C, Finsupp.ext_iff, comapDomain_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  intro; split_ifs
  all_goals grind only

@[simp]
theorem rename_X (i : σ) : rename hf (X i : MvPowerSeries σ R) = X (f i) := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def,
    SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range, coeff_X, Finsupp.ext_iff,
    comapDomain_apply, single_apply]
  intro; split_ifs
  all_goals grind only

theorem map_rename (F : R →+* S) (p : MvPowerSeries σ R) :
    map F (rename hf p) = rename hf (map F p) := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_map, coeff_renameFun, Set.subset_def,
    SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range]
  intro; split_ifs
  all_goals simp

@[simp]
theorem rename_rename {g : τ → α} (hg : g.Injective) (p : MvPowerSeries σ R) :
    rename hg (rename hf p) = rename (hg.comp hf) p := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def, SetLike.mem_coe,
    mem_support_iff, ne_eq, Set.mem_range, comapDomain_support, coe_preimage, Set.mem_preimage,
    Function.comp_apply]
  intro; split_ifs
  · congr
    simp [Finsupp.ext_iff]
  all_goals grind only

lemma rename_comp_rename {g : τ → α} (hg : g.Injective) :
    (rename (R := R) hg).comp (rename hf) = rename (hg.comp hf) :=
  AlgHom.ext fun p ↦ rename_rename hf hg p

@[simp]
theorem rename_id : rename (Function.injective_id) = AlgHom.id R (MvPowerSeries σ R) := by
  ext p x
  simp only [rename_apply, coeff_renameFun, Set.range_id, Set.subset_univ, ↓reduceIte,
    AlgHom.coe_id, id_eq]
  congr
  simp [Finsupp.ext_iff]

lemma rename_id_apply (p : MvPowerSeries σ R) :
    rename (Function.injective_id) p = p := by simp

theorem rename_monomial (d : σ →₀ ℕ) (r : R) :
    rename hf (monomial d r) = monomial (d.mapDomain f) r := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def, SetLike.mem_coe,
    mem_support_iff, ne_eq, Set.mem_range, coeff_monomial, Finsupp.ext_iff, comapDomain_apply]
  intro x; split_ifs with h1 _ h2 _ h3
  any_goals rfl
  · rw [not_forall] at h2
    rcases h2 with ⟨t, ht⟩
    rw [← ne_eq] at ht; symm at ht
    by_cases! h : x t ≠ 0
    · grind [mapDomain_apply hf]
    rw [h, ← mem_support_iff, mapDomain_support_of_injective hf] at ht
    grind only [= mem_image, = mem_support_iff]
  · grind only [mapDomain_apply hf]
  · simp only [not_forall, exists_prop, not_exists] at h1
    rcases h1 with ⟨t, ht, _⟩
    rw [h3 t, ← ne_eq, ← mem_support_iff, mapDomain_support_of_injective hf] at ht
    grind only [= mem_image]

@[simp]
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename hf p) = constantCoeff p := by
  rw [rename_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_renameFun]
  simp

theorem rename_injective : Function.Injective (rename (R := R) hf) := by
  intro _ _ h; ext x
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun] at h
  simpa [mapDomain_support_of_injective hf, comapDomain_mapDomain f hf] using h (mapDomain f x)

variable (f)

def killComplFun (p : MvPowerSeries τ R) : MvPowerSeries σ R := fun x ↦ coeff (mapDomain f x) p

theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
  coeff x (killComplFun f p) = coeff (mapDomain f x) p := rfl

theorem killComplFun_zero : killComplFun f (0 : MvPowerSeries τ R) = 0 := by
  simp [MvPowerSeries.ext_iff, coeff_killComplFun]

include hf in
theorem killComplFun_one : killComplFun f (1 : MvPowerSeries τ R) = 1 := by
  simp only [MvPowerSeries.ext_iff, coeff_killComplFun, coeff_one, Finsupp.ext_iff,
    Finsupp.coe_zero, Pi.zero_apply]
  intro x; split_ifs with h1 h2
  any_goals rfl
  · rw [not_forall] at h2
    rcases h2 with ⟨s, _⟩
    specialize h1 (f s)
    grind only [mapDomain_apply hf]
  rw [not_forall] at h1
  rcases h1 with ⟨_, h⟩
  rw [← ne_eq, ← mem_support_iff, mapDomain_support_of_injective hf] at h
  grind only [= mem_image, = mem_support_iff]

include hf in
theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun f (p * q) = killComplFun f p * killComplFun f q := by
  simp only [MvPowerSeries.ext_iff, coeff_killComplFun, coeff_mul]
  intro x
  let e : (σ →₀ ℕ) × (σ →₀ ℕ) → (τ →₀ ℕ) × (τ →₀ ℕ) := fun (a, b) ↦
    (mapDomain f a, mapDomain f b)
  have img_e : antidiagonal (mapDomain f x) = image e (antidiagonal x) := by
    simp only [Finset.ext_iff, mem_antidiagonal, mem_image, Prod.exists, Prod.forall,
      Prod.mk.injEq, e]
    refine fun a b ↦ ⟨fun h ↦ ?_, fun ⟨a', b', h1, h2, h3⟩ ↦ ?_⟩
    · use comapDomain f a hf.injOn, comapDomain f b hf.injOn
      have : mapDomain f (comapDomain f a hf.injOn) = a ∧
        mapDomain f (comapDomain f b hf.injOn) = b := by
        constructor; all_goals
        apply mapDomain_comapDomain f hf
        simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range]
        intro t _
        simp only [Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply] at h
        specialize h t
        replace h : (mapDomain f x) t ≠ 0 := by omega
        rw [← mem_support_iff, mapDomain_support_of_injective hf] at h
        grind only [= mem_image]
      refine ⟨mapDomain_injective hf ?_, this.left, this.right⟩
      simp [mapDomain_add, ← h, this]
    rw [← h2, ← h3, ← mapDomain_add, h1]
  rw [img_e, sum_image]
  · apply Function.Injective.injOn
    simp only [Function.Injective, Prod.mk.injEq, and_imp, Prod.forall, e]
    grind only [!mapDomain_injective hf]

include hf in
theorem killComplFun_commutes (r : R) :
    killComplFun f ((algebraMap R (MvPowerSeries τ R)) r) =
      (algebraMap R (MvPowerSeries σ R)) r := by
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.ext_iff,
    coeff_killComplFun, coeff_C, Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]
  intro x; split_ifs with h1 h2
  any_goals rfl
  · rw [not_forall] at h2
    rcases h2 with ⟨s, _⟩
    specialize h1 (f s)
    grind only [mapDomain_apply hf]
  rw [not_forall] at h1
  rcases h1 with ⟨_, h⟩
  rw [← ne_eq, ← mem_support_iff, mapDomain_support_of_injective hf] at h
  grind only [= mem_image, = mem_support_iff]

variable {f}
/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `MvPowerSeries.killCompl hf` is the `AlgHom` from `R[[τ]]` to `R[[σ]]` that is left inverse to
  `rename hf : R[[σ]] → R[[τ]]` and sends the variables in the complement of the range of `f` to `0`. -/
def killCompl : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R := {
  toFun := killComplFun f
  map_one' := killComplFun_one f hf
  map_mul' := killComplFun_mul f hf
  map_zero' := killComplFun_zero f
  map_add' := by simp [MvPowerSeries.ext_iff, coeff_killComplFun]
  commutes' := killComplFun_commutes f hf
}

theorem killCompl_apply (p : MvPowerSeries τ R) :
    killCompl hf p = killComplFun f p := rfl

theorem killCompl_C (r : R) : killCompl hf (C r) = C r := by
  simp only [killCompl_apply, MvPowerSeries.ext_iff, coeff_killComplFun, coeff_C, Finsupp.ext_iff,
    Finsupp.coe_zero, Pi.zero_apply]
  intro x; split_ifs with h1 h2
  any_goals rfl
  · rw [not_forall] at h2
    rcases h2 with ⟨s, _⟩
    grind only [h1 (f s), mapDomain_apply hf]
  rw [not_forall] at h1
  rcases h1 with ⟨t, ht⟩
  rw [← ne_eq, ← mem_support_iff, mapDomain_support_of_injective hf] at ht
  grind only [= mem_image, = mem_support_iff]

theorem killCompl_X (t : τ) : killCompl (R := R) hf (X t) = if h : t ∈ Set.range f then
    X ((Equiv.ofInjective f hf).symm ⟨t, h⟩) else 0 := by
  simp only [killCompl_apply, Set.mem_range, MvPowerSeries.ext_iff, coeff_killComplFun, coeff_X,
    Finsupp.ext_iff, single_apply]
  intro x; split_ifs with h1 h2 h3
  · rcases h2 with ⟨s, hs⟩
    simp only [← hs, Equiv.ofInjective_symm_apply, coeff_X, Finsupp.ext_iff, single_apply,
      left_eq_ite_iff, not_forall, forall_exists_index]
    intro s' hs'
    split_ifs at hs' with h
    · grind only [h1 (f s), mapDomain_apply hf]
    specialize h1 (f s')
    rw [ite_cond_eq_false, mapDomain_apply hf] at h1
    contradiction
    · grind only
  · replace h1 : (mapDomain f x) t ≠ 0 := by
      specialize h1 t
      simp only [↓reduceIte] at h1
      simp [h1]
    rw [← mem_support_iff, mapDomain_support_of_injective hf] at h1
    grind only [= mem_image]
  · rcases h3 with ⟨s, hs⟩
    simp only [← hs, Equiv.ofInjective_symm_apply, coeff_X, Finsupp.ext_iff, single_apply,
      right_eq_ite_iff]
    rw [not_forall] at h1
    rcases h1 with ⟨_, h1⟩
    intro h; exfalso
    revert h1
    simp only [imp_false, Decidable.not_not]
    split_ifs
    · grind only [mapDomain_apply hf]
    rw [← notMem_support_iff, mapDomain_support_of_injective hf]
    grind only [= mem_image, = mem_support_iff]
  simp

theorem killCompl_comp_rename : (killCompl hf).comp (rename hf) = AlgHom.id R _ := by
  ext p x
  simp only [AlgHom.coe_comp, Function.comp_apply, rename_apply, killCompl_apply,
    coeff_killComplFun, coeff_renameFun, Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq,
    Set.mem_range, AlgHom.coe_id, id_eq]
  split_ifs with h
  · rw [comapDomain_mapDomain f hf]
  simp only [not_forall, exists_prop, not_exists] at h
  rcases h with ⟨_, h, _⟩
  rw [← ne_eq, ← mem_support_iff, mapDomain_support_of_injective hf] at h
  grind only [= mem_image]

@[simp]
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl hf (rename hf p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p

variable (R)

/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R := {
  rename e.injective with
  invFun := rename e.symm.injective
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
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
  AlgEquiv.ext (rename_rename e.injective f.injective)

variable {R}

@[simp]
theorem coeff_rename_mapDomain (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    (rename hf p).coeff (x.mapDomain f) = p.coeff x := by
  simp [← coeff_killComplFun, ← killCompl_apply hf]

@[simp]
theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    (rename f.injective φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [embDomain_eq_mapDomain f, coeff_rename_mapDomain f.injective]
