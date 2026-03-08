/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series
under a map with finite fibers, which modifies the set of variables.

This file is patterned after `Mathlib/Algebra/MvPolynomial/Rename.lean`.

## Main declarations

* `Filter.TendstoCofinite.mapDomain`
* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`
* `MvPowerSeries.killCompl`

-/

@[expose] public section

noncomputable section

open Finsupp Filter

variable {σ τ γ R M : Type*} (f : σ → τ) (g : τ → γ) [AddCommMonoid M] [TendstoCofinite f]

namespace Filter.TendstoCofinite

/-- Given `f : σ → τ` with `Filter.TendstoCofinite f` and `v : σ → M`,
`Filter.TendstoCofinite.mapDomain f v : τ → M` is the function whose value at `b : τ` is
the sum of `v x` over all `x` such that `f x = b`. -/
def mapDomain (v : σ → M) : τ → M := fun i ↦ (finite_preimage_singleton f i).toFinset.sum v

@[simp]
lemma mapDomain_add (u v : σ → M) : mapDomain f (u + v) = mapDomain f u + mapDomain f v := by
  ext; simp [mapDomain, Finset.sum_add_distrib]

@[simp]
lemma mapDomain_smul [DistribSMul R M] (r : R) (v : σ → M) :
    mapDomain f (r • v) = r • (mapDomain f v) := by ext; simp [mapDomain, Finset.smul_sum]

theorem mapDomain_eq_zero (v : σ → M) {i : τ} (h' : i ∉ Set.range f) : mapDomain f v i = 0 := by
  rw [← Set.preimage_singleton_eq_empty] at h'
  simp [mapDomain, Set.Finite.toFinset, h']

end Filter.TendstoCofinite

open TendstoCofinite

@[instance]
theorem Finsupp.mapDomain_tendstoCofinite : TendstoCofinite (mapDomain (M := ℕ) f) := by
  classical
  refine (tendstoCofinite_iff_finite_preimage_singleton _).mpr fun x ↦ ?_
  let s := Finset.sup x.support (fun t ↦ (finite_preimage_singleton f t).toFinset)
  let e : s ↪ σ := Function.Embedding.subtype (fun u ↦ u ∈ s)
  refine Set.Finite.subset (Set.Finite.image (embDomain e) <|
    finite_of_degree_le (σ := s) (degree x)) ?_
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_setOf_eq]
  refine fun y hy ↦ ⟨y.comapDomain e e.injective.injOn, ?_, embDomain_comapDomain ?_⟩
  · rw [← hy, degree_mapDomain_eq]
    exact degree_comapDomain_le ..
  suffices y.support ⊆ s by simpa [e]
  simpa [← hy, mapDomain, sum, Finset.subset_iff, single_apply, s] using
    fun i hi ↦ ⟨i, by simp [hi]⟩

namespace MvPowerSeries

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

section rename

/-- Implementation detail for `rename`. Use `MvPowerSeries.rename` instead. -/
def renameFun [TendstoCofinite f] : MvPowerSeries σ R → MvPowerSeries τ R :=
  mapDomain (Finsupp.mapDomain f)

private lemma coeff_renameFun {p : MvPowerSeries σ R} {x : τ →₀ ℕ} : (renameFun f p).coeff x =
    (finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum (p.coeff ·) := rfl

private lemma renameFun_monomial (x : σ →₀ ℕ) (r : R) :
    renameFun f (monomial x r) = monomial (mapDomain f x) r := by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]

private theorem renameFunAux [DecidableEq σ] (x : τ →₀ ℕ) :
    {p : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) | (p.1).mapDomain f = x ∧
      p.2 ∈ Finset.antidiagonal p.1}.Finite := by
  apply Set.Finite.subset
    (s := ↑((finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y ↦ Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

private theorem renameFunAux' [DecidableEq τ] (x : τ →₀ ℕ) :
    {p : ((τ →₀ ℕ) × (τ →₀ ℕ)) × (σ →₀ ℕ) × (σ →₀ ℕ) | p.1 ∈ Finset.antidiagonal x
      ∧ p.2 ∈ (finite_preimage_singleton (Finsupp.mapDomain f) p.1.1).toFinset ×ˢ
    (finite_preimage_singleton (Finsupp.mapDomain f) p.1.2).toFinset}.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q ↦ Finset.product {q}
    ((finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind

private theorem renameFunAuxImage [DecidableEq σ] [DecidableEq τ] (x : τ →₀ ℕ) :
      (renameFunAux' f x).toFinset.image (fun (_, b) ↦ (b.1 + b.2, b)) =
    (renameFunAux f x).toFinset := by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]

open Finset in
private theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp),
    ← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp),
    ← renameFunAuxImage f x, sum_image fun _ ↦ by simp; grind]

/-- Rename all the variables in a multivariable power series by a function with finite fibers. -/
@[no_expose]
def rename [TendstoCofinite f] : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R where
  toFun := renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by ext; simp [coeff_renameFun, Finset.sum_add_distrib]
  commutes' := renameFun_monomial f 0

theorem coeff_rename (p : MvPowerSeries σ R) (x : τ →₀ ℕ) : coeff x (rename f p) =
    (finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum (p.coeff ·) := by rfl

theorem rename_monomial (x : σ →₀ ℕ) (r : R) : rename f (monomial x r) =
    monomial (mapDomain f x) r := renameFun_monomial f ..

@[simp]
theorem coeff_embDomain_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    coeff (embDomain e x) (rename e p) = p.coeff x := by
  rw [coeff_rename, Finset.sum_eq_single x _ (by simp [← embDomain_eq_mapDomain])]
  simpa using fun _ h h' ↦ by simp [← embDomain_eq_mapDomain, embDomain_inj, h'] at h

theorem coeff_rename_eq_zero (p : MvPowerSeries σ R) (x : τ →₀ ℕ)
    (h' : x ∉ Set.range (Finsupp.mapDomain f)) : (rename f p).coeff x = 0 := by
  simp [coeff_rename, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr h']

@[simp]
theorem rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r := rename_monomial f 0 r

@[simp]
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using rename_monomial f (single i 1) 1

theorem map_rename (F : R →+* S) (p : MvPowerSeries σ R) :
    map F (rename f p) = rename f (map F p) := by
  ext; simp [coeff_rename]

@[simp]
theorem rename_rename [TendstoCofinite g] (p : MvPowerSeries σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  classical
  ext y; simp only [coeff_rename]
  rw [← Finset.sum_finset_product' ((finite_preimage_singleton
    (Finsupp.mapDomain (g ∘ f)) y).toFinset.image (fun u ↦ (Finsupp.mapDomain f u, u))) _ _
      (by simp; grind [mapDomain_comp]), Finset.sum_image (by simp)]

lemma rename_comp_rename [TendstoCofinite g] :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
theorem rename_id : rename id = AlgHom.id R (MvPowerSeries σ R) := by
  ext _ y
  simpa [coeff_rename] using Finset.sum_eq_single y (by simp) (by simp)

@[simp]
lemma rename_id_apply (p : MvPowerSeries σ R) : rename id p = p := by simp

@[simp]
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename f p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_rename, Finset.sum_eq_single 0 (by simp [mapDomain_apply_eq_zero_iff]) (by simp)]

theorem rename_injective (e : σ ↪ τ) : Function.Injective (rename (R := R) e) := by
  intro _ _ h; ext x
  simpa using MvPowerSeries.ext_iff.mp h (embDomain e x)

variable (R) in
/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R where
  __ := rename e
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl := AlgEquiv.ext (by simp)

@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm := rfl

@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ γ) : (renameEquiv R e).trans (renameEquiv R f) =
    renameEquiv R (e.trans f) := AlgEquiv.ext (rename_rename e f)

end rename

section killCompl

variable {e : σ ↪ τ}

/-- Implementation detail for `killCompl`. Use `MvPowerSeries.killCompl` instead. -/
def killComplFun (e : σ ↪ τ) (p : MvPowerSeries τ R) : MvPowerSeries σ R :=
  fun x ↦ coeff (embDomain e x) p

private theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
    coeff x (killComplFun e p) = coeff (embDomain e x) p := rfl

private theorem killComplFun_monomial_embDomain (x : σ →₀ ℕ) (r : R) :
    killComplFun e (monomial (embDomain e x) r) = monomial x r := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]

private theorem killComplFun_monomial_eq_zero {x : τ →₀ ℕ} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killComplFun e (monomial x r) = 0 := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial]
  grind

private theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun e (p * q) = killComplFun e p * killComplFun e q := by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← image_prodMap_embDomain_antidiagonal, Finset.sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective e,
      embDomain_injective e⟩)))]

/-- Given an embedding `e : σ ↪ τ`, `MvPowerSeries.killComplFun e` is the function from
`R[[τ]]` to `R[[σ]]` that is left inverse to `rename e.injective.fiberFinite : R[[σ]] → R[[τ]]`
and sends the variables in the complement of the range of `e` to `0`. -/
@[no_expose]
def killCompl (e : σ ↪ τ) : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R where
  toFun := killComplFun e
  map_one' := by simpa using killComplFun_monomial_embDomain 0 1
  map_mul' := killComplFun_mul
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using killComplFun_monomial_embDomain 0

lemma coeff_killCompl (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
    coeff x (killCompl e p) = coeff (embDomain e x) p := by rfl

lemma killCompl_monomial_embDomain (x : σ →₀ ℕ) (r : R) :
    killCompl e (monomial (embDomain e x) r) = monomial x r :=
  killComplFun_monomial_embDomain x r

lemma killCompl_monomial_eq_zero {x : τ →₀ ℕ} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killCompl e (monomial x r) = 0 :=
  killComplFun_monomial_eq_zero r h

@[simp]
lemma killCompl_C (r : R) : killCompl e (C r) = C r := by
  simpa using killCompl_monomial_embDomain 0 r

@[simp]
theorem killCompl_X (i : σ) : killCompl (R := R) e (X (e i)) = X i := by
  classical
  ext; simp [coeff_X, coeff_killCompl, ← embDomain_single]

theorem killCompl_X_eq_zero {t : τ} (h : t ∉ Set.range e) :
    killCompl (R := R) e (X t) = 0 := by
  replace h : single t 1 ∉ Set.range (embDomain e) := by
    rwa [mem_range_embDomain_iff, support_single_ne_zero _ (by simp), Finset.coe_singleton,
      Set.singleton_subset_iff]
  simpa using killCompl_monomial_eq_zero (1 : R) h

theorem killCompl_comp_rename : (killCompl e).comp (rename e) = AlgHom.id R _ := by
  ext; simp [coeff_killCompl]

@[simp]
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl e (rename e p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename) p

end killCompl

end MvPowerSeries
