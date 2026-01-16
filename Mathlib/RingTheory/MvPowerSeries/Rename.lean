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

This file is patterned after `MvPolynomial/Rename.lean`

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
    coeff (embDomain f x) (renameFun f p) = coeff x p :=
  ((embDomain_injective f).factorsThrough _).extend_apply _ _

open Classical in
theorem coeff_renameFun (p : MvPowerSeries σ R) (x : τ →₀ ℕ) :
    coeff x (renameFun f p) = if ↑x.support ⊆ Set.range f then
      coeff (x.comapDomain f f.injective.injOn) p else 0 := by
  split_ifs with h
  · obtain ⟨y, hy⟩ := mem_range_embDomain_iff.mpr h
    simp [← hy]
  rw [← mem_range_embDomain_iff, Set.mem_range] at h
  exact Function.extend_apply' p (0 : (τ →₀ ℕ) → R) x h

theorem renameFun_monomial (x) (r : R) :
    renameFun f (monomial x r) = monomial (embDomain f x) r := by
  classical
  ext y; rw [coeff_monomial]
  split_ifs with h
  · simp [h]
  rw [coeff_renameFun, ← mem_range_embDomain_iff, Set.mem_range, ite_eq_right_iff,
    forall_exists_index]
  grind only [!comapDomain_embDomain, coeff_monomial]

theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite,
    sum_const_zero, add_zero, filter_filter]
  split_ifs with h
  · simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range] at h
    have : ∀ x_1 ∈ antidiagonal x, ↑x_1.2.support ⊆ Set.range f ∧ ↑x_1.1.support ⊆
      Set.range f := by
      simp only [mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply, Set.subset_def,
        SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range, Prod.forall]
      grind only
    rw [filter_true_of_mem this]
    replace this : antidiagonal (comapDomain f x f.injective.injOn) = image (fun (x, y) ↦
      (comapDomain f x f.injective.injOn, comapDomain f y f.injective.injOn)) (antidiagonal x) := by
      simp only [Finset.ext_iff, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply,
        comapDomain_apply, mem_image, Prod.exists, Prod.forall, Prod.mk.injEq] at h ⊢
      refine fun a b ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
      · use mapDomain f a, mapDomain f b
        simp only [mapDomain_apply f.injective, implies_true, and_self, and_true]
        intro t; by_cases! h'' : x t = 0
        · rw [h'', Nat.add_eq_zero_iff]
          constructor; all_goals
          rw [← notMem_support_iff, mapDomain_support_of_injective f.injective]
          grind only [= mem_image, = mem_support_iff]
        obtain ⟨s, hs⟩ := h _ h''
        simp [← hs, mapDomain_apply f.injective, h' s]
      grind only
    rw [this, sum_image]
    · simp only [Set.InjOn, SetLike.mem_coe, mem_antidiagonal, Finsupp.ext_iff, Finsupp.coe_add,
        Pi.add_apply, Prod.mk.injEq, comapDomain_apply, and_imp, Prod.forall]
      grind only
  have : filter (fun x ↦ ↑x.2.support ⊆ Set.range f ∧ ↑x.1.support ⊆ Set.range f)
    (antidiagonal x) = ∅ := by
    simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range,
      not_forall, not_exists, Finset.ext_iff, mem_filter, mem_antidiagonal, Finsupp.ext_iff,
      Finsupp.coe_add, Pi.add_apply, notMem_empty, iff_false, not_and, Prod.forall] at h ⊢
    grind only
  rw [this, sum_empty]

/-- Rename all the variables in a multivariable power series by an embedding, as an `AlgHom`. -/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R := {
  toFun := renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by
    dsimp only [renameFun]
    nth_rw 1 [← add_zero (0 : (τ →₀ ℕ) → R), Function.extend_add]
  commutes' := renameFun_monomial f 0
}

theorem rename_apply {p : MvPowerSeries σ R} : rename f p = renameFun f p := rfl

@[simp]
theorem rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r := renameFun_monomial f 0 r

@[simp]
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using renameFun_monomial f (single i 1) 1

theorem map_rename (F : R →+* S) (p : MvPowerSeries σ R) :
    map F (rename f p) = rename f (map F p) := by
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_map, coeff_renameFun, Set.subset_def,
    SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range]
  intro; split_ifs
  all_goals simp

@[simp]
theorem rename_rename (g : τ ↪ α) (p : MvPowerSeries σ R) :
    rename g (rename f p) = rename (f.trans g) p := by
  classical
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun, Set.subset_def, SetLike.mem_coe,
    mem_support_iff, ne_eq, Set.mem_range, comapDomain_support, coe_preimage, Set.mem_preimage,
    Function.Embedding.trans_apply]
  intro; split_ifs
  · congr
    ext; simp
  all_goals grind

lemma rename_comp_rename (g : τ ↪ α) :
    (rename (R := R) g).comp (rename f) = rename (f.trans g) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
theorem rename_id : rename (Function.Embedding.refl _) = AlgHom.id R (MvPowerSeries σ R) :=
  AlgHom.ext fun p ↦ by simp [rename_apply, renameFun]

lemma rename_id_apply (p : MvPowerSeries σ R) :
    rename (Function.Embedding.refl _) p = p := by simp

theorem rename_monomial (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  simpa [embDomain_eq_mapDomain] using renameFun_monomial f d r

@[simp]
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename f p) = constantCoeff p := by
  rw [rename_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_renameFun]
  simp

theorem rename_injective : Function.Injective (rename (R := R) f) := by
  classical
  intro _ _ h; ext x
  simp only [rename_apply, MvPowerSeries.ext_iff, coeff_renameFun] at h
  simpa [mapDomain_support_of_injective f.injective, comapDomain_mapDomain f f.injective]
    using h (mapDomain f x)

/-- Given an embedding `f : σ ↪ τ`, `MvPowerSeries.killComplFun f` is the function from
  `R[[τ]]` to `R[[σ]]` that is left inverse to `rename f : R[[σ]] → R[[τ]]` and sends the
  variables in the complement of the range of `f` to `0`. -/
def killComplFun (p : MvPowerSeries τ R) : MvPowerSeries σ R := fun x ↦ coeff (embDomain f x) p

theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
  coeff x (killComplFun f p) = coeff (embDomain f x) p := rfl

open Classical in
theorem killComplFun_monomial (x) (r : R) : killComplFun f (monomial x r) =
    if x ∈ Set.range (embDomain f) then monomial (comapDomain f x f.injective.injOn) r else 0 := by
  classical
  ext y; split_ifs with h
  · simp only [coeff_killComplFun, coeff_monomial]
    congr; refine eq_iff_iff.mpr ⟨fun _ ↦ ?_, fun h' ↦ ?_⟩
    · rwa [← (embDomain_injective f).eq_iff, embDomain_comapDomain]
      · rw [← mem_range_embDomain_iff]
        use y
    rw [h', embDomain_comapDomain ((mem_range_embDomain_iff).mp h)]
  grind only [coeff_killComplFun, !coeff_zero, = Set.mem_range, coeff_monomial]

theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun f (p * q) = killComplFun f p * killComplFun f q := by
  classical
  ext x; simp only [coeff_killComplFun, coeff_mul]
  let e : (σ →₀ ℕ) × (σ →₀ ℕ) → (τ →₀ ℕ) × (τ →₀ ℕ) := fun (a, b) ↦
    (embDomain f a, embDomain f b)
  have img_e : antidiagonal (embDomain f x) = image e (antidiagonal x) := by
    simp only [Finset.ext_iff, mem_antidiagonal, mem_image, Prod.exists, Prod.forall,
      Prod.mk.injEq, e]
    refine fun a b ↦ ⟨fun h ↦ ?_, fun ⟨a', b', h1, h2, h3⟩ ↦ ?_⟩
    · use comapDomain f a f.injective.injOn, comapDomain f b f.injective.injOn
      have : embDomain f (comapDomain f a f.injective.injOn) = a ∧
        embDomain f (comapDomain f b f.injective.injOn) = b := by
        constructor; all_goals
        rw [embDomain_comapDomain]
        simp only [Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq, Set.mem_range]
        intro t _
        simp only [Finsupp.ext_iff, Finsupp.coe_add, Pi.add_apply] at h
        replace h : (embDomain f x) t ≠ 0 := by
          specialize h t; lia
        rw [← mem_support_iff, support_embDomain] at h
        grind only [= mem_map]
      refine ⟨embDomain_injective f ?_, this.left, this.right⟩
      rw [embDomain_add, ← h, this.left, this.right]
    rw [← h2, ← h3, ← embDomain_add, h1]
  rw [img_e, sum_image]
  · apply Function.Injective.injOn
    simp only [Function.Injective, Prod.mk.injEq, and_imp, Prod.forall, e]
    grind only [!embDomain_injective f]

/-- The `AlgHom` version of `killComplFun`. -/
def killCompl : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R := {
  toFun := killComplFun f
  map_one' := by simpa using killComplFun_monomial f 0 1
  map_mul' := killComplFun_mul f
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using killComplFun_monomial f 0
}

lemma killCompl_apply (p : MvPowerSeries τ R) :
    killCompl f p = killComplFun f p := by rfl

lemma killCompl_C (r : R) : killCompl f (C r) = C r := by
  simpa using killComplFun_monomial f 0 r

open Classical in
theorem killCompl_X (t : τ) : killCompl (R := R) f (X t) = if h : t ∈ Set.range f then
    X ((Equiv.ofInjective f f.injective).symm ⟨t, h⟩) else 0 := by
  rw [killCompl_apply]
  convert killComplFun_monomial f (single t 1) (1 : R)
  split_ifs with h1 h2 h3
  · set s := ((Equiv.ofInjective f f.injective).symm ⟨t, h1⟩) with hs
    simp only [← Equiv.symm_apply_eq, Equiv.symm_symm, Equiv.ofInjective_apply,
      Subtype.mk.injEq] at hs
    simp [← hs, X_def]
  · rw [mem_range_embDomain_iff, support_single_ne_zero] at h2
    · grind only [= Set.subset_def, = mem_coe, = mem_singleton]
    simp
  · rw [mem_range_embDomain_iff, support_single_ne_zero] at h3
    · grind only [= Set.subset_def, = mem_coe, = mem_singleton]
    simp
  rfl

theorem killCompl_comp_rename : (killCompl f).comp (rename f) = AlgHom.id R _ := by
  classical
  ext p x
  simp only [AlgHom.coe_comp, Function.comp_apply, rename_apply, killCompl_apply,
    coeff_killComplFun, coeff_renameFun, Set.subset_def, SetLike.mem_coe, mem_support_iff, ne_eq,
    Set.mem_range, AlgHom.coe_id, id_eq]
  split_ifs with h
  · rw [comapDomain_embDomain f]
  simp only [not_forall, exists_prop, not_exists] at h
  rcases h with ⟨_, h, _⟩
  rw [← ne_eq, ← mem_support_iff, support_embDomain] at h
  grind only [= mem_map]

@[simp]
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl f (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename f) p

variable (R)

/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R := {
  rename e with
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp
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
