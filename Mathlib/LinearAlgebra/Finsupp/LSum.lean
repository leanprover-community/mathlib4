/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic.ApplyFun

/-!
# Sums as a linear map

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

## Main definitions

* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section SMul

variable {α : Type*} {β : Type*} {R R₂ : Type*} {M M₂ : Type*}

theorem smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α →₀ β} {c : R} {h : α → β → M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum

@[simp]
theorem sum_smul_index_semilinearMap' [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R₂ M₂] {σ : R →+* R₂} {v : α →₀ M} {c : R} {h : α → M →ₛₗ[σ] M₂} :
    ((c • v).sum fun a => h a) = σ c • v.sum fun a => h a := by
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  · simp only [map_smulₛₗ]
  · intro i
    exact (h i).map_zero

theorem sum_smul_index_linearMap' [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
    [Module R M₂] {v : α →₀ M} {c : R} {h : α → M →ₗ[R] M₂} :
    ((c • v).sum fun a => h a) = c • v.sum fun a => h a :=
  sum_smul_index_semilinearMap'

end SMul

variable {α : Type*} {M N P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]

variable {σ : R →+* R₂} {σ_inv : R₂ →+* R}

section CompatibleSMul

variable (R S M N ι : Type*)
variable [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]

instance _root_.LinearMap.CompatibleSMul.finsupp_dom [SMulZeroClass R M] [DistribSMul R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul (ι →₀ M) N R S where
  map_smul f r m := by
    conv_rhs => rw [← sum_single m, map_finsuppSum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsuppSum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m

instance _root_.LinearMap.CompatibleSMul.finsupp_cod [SMul R M] [SMulZeroClass R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι →₀ N) R S where
  map_smul f r m := by ext i; apply ((lapply i).comp f).map_smul_of_tower

end CompatibleSMul

section LSum

variable (S)
variable [Module S N] [SMulCommClass R₂ S N]

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `Finsupp.sum`. This is an upgraded version of `Finsupp.liftAddHom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
def lsum : (α → M →ₛₗ[σ] N) ≃ₗ[S] (α →₀ M) →ₛₗ[σ] N where
  toFun F :=
    { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
    ext x y
    simp
  map_add' F G := by
    ext x y
    simp
  map_smul' F G := by
    ext x y
    simp

@[simp]
theorem coe_lsum (f : α → M →ₛₗ[σ] N) : (lsum S f : (α →₀ M) → N) = fun d => d.sum fun i => f i :=
  rfl

theorem lsum_apply (f : α → M →ₛₗ[σ] N) (l : α →₀ M) : Finsupp.lsum S f l = l.sum fun b => f b :=
  rfl

theorem lsum_single (f : α → M →ₛₗ[σ] N) (i : α) (m : M) :
    Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero

@[simp] theorem lsum_comp_lsingle (f : α → M →ₛₗ[σ] N) (i : α) :
    Finsupp.lsum S f ∘ₛₗ lsingle i = f i := by ext; simp

theorem lsum_symm_apply (f : (α →₀ M) →ₛₗ[σ] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl

end LSum

section

variable (M) (R) (X : Type*) (S)
variable [Module S M] [SMulCommClass R S M]

/-- A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
noncomputable def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R ℕ M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[ℕ] _).toAddEquiv

@[simp]
theorem lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1) :=
  rfl

@[simp]
theorem lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun x r => r • f x :=
  rfl

/-- Given compatible `S` and `R`-module structures on `M` and a type `X`, the set of functions
`X → M` is `S`-linearly equivalent to the `R`-linear maps from the free `R`-module
on `X` to `M`. -/
noncomputable def llift : (X → M) ≃ₗ[S] (X →₀ R) →ₗ[R] M :=
  { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }

@[simp]
theorem llift_apply (f : X → M) (x : X →₀ R) : llift M R S X f x = lift M R X f x :=
  rfl

@[simp]
theorem llift_symm_apply (f : (X →₀ R) →ₗ[R] M) (x : X) :
    (llift M R S X).symm f x = f (single x 1) :=
  rfl

end

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `Finsupp.domCongr` as a `LinearEquiv`.
See also `LinearMap.funCongrLeft` for the case of arbitrary functions. -/
protected def domLCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv <| by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using (lmapDomain M R e).map_smul

@[simp]
theorem domLCongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl

@[simp]
theorem domLCongr_refl : Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext fun _ => equivMapDomain_refl _

theorem domLCongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
    (Finsupp.domLCongr f).trans (Finsupp.domLCongr f₂) =
      (Finsupp.domLCongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

@[simp]
theorem domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) :
    ((Finsupp.domLCongr f).symm : (_ →₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm :=
  LinearEquiv.ext fun _ => rfl

theorem domLCongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m := by
  simp

section Equiv

variable [RingHomInvPair σ σ_inv] [RingHomInvPair σ_inv σ]

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) : (ι →₀ M) ≃ₛₗ[σ] κ →₀ N :=
  (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)

@[simp]
theorem lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M) :
    lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m) := by simp [lcongr]

@[simp]
theorem lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι →₀ M) (k : κ) :
    lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
  rfl

theorem lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (n : N) :
    (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) := by
  apply_fun (lcongr e₁ e₂ : (ι →₀ M) → (κ →₀ N)) using (lcongr e₁ e₂).injective
  simp

@[simp]
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) :
    (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm := by
  ext
  rfl

end Equiv

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

protected theorem Submodule.finsuppSum_mem {ι β : Type*} [Zero β] (S : Submodule R M) (f : ι →₀ β)
    (g : ι → β → M) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
  AddSubmonoidClass.finsuppSum_mem S f g h

@[deprecated (since := "2025-04-06")] alias Submodule.finsupp_sum_mem := Submodule.finsuppSum_mem

end

namespace LinearMap

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFunOnFintypeSurjective`
/-- A surjective linear map to finitely supported functions has a splitting. -/
def splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose

theorem splittingOfFinsuppSurjective_splits (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id := by
  ext x
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index, one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]

theorem leftInverse_splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    LeftInverse f (splittingOfFinsuppSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g

theorem splittingOfFinsuppSurjective_injective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    Injective (splittingOfFinsuppSurjective f s) :=
  (leftInverse_splittingOfFinsuppSurjective f s).injective

end LinearMap

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R →+* R₂}
variable [Module R M] [Module R₂ M₂]
variable {γ : Type*} [Zero γ]

section Finsupp

theorem coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
theorem finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Finsupp

end AddCommMonoid

end LinearMap

namespace Submodule

variable {S : Type*} [Semiring S] [Module R S] [SMulCommClass R R S]

section
variable [SMulCommClass R S S]

/-- If `M` and `N` are submodules of an `R`-algebra `S`, `m : ι → M` is a family of elements, then
there is an `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }` to the sum of `m_i * n_i`.
This is used in the definition of linearly disjointness. -/
def mulLeftMap {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι → M) :
    (ι →₀ N) →ₗ[R] S := Finsupp.lsum R fun i ↦ (m i).1 • N.subtype

theorem mulLeftMap_apply {M N : Submodule R S} {ι : Type*} (m : ι → M) (n : ι →₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) ↦ (m i).1 * n.1 := rfl

@[simp]
theorem mulLeftMap_apply_single {M N : Submodule R S} {ι : Type*} (m : ι → M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap]

end

variable [IsScalarTower R S S]

/-- If `M` and `N` are submodules of an `R`-algebra `S`, `n : ι → N` is a family of elements, then
there is an `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }` to the sum of `m_i * n_i`.
This is used in the definition of linearly disjointness. -/
def mulRightMap (M : Submodule R S) {N : Submodule R S} {ι : Type*} (n : ι → N) :
    (ι →₀ M) →ₗ[R] S := Finsupp.lsum R fun i ↦ MulOpposite.op (n i).1 • M.subtype

theorem mulRightMap_apply {M N : Submodule R S} {ι : Type*} (n : ι → N) (m : ι →₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) ↦ m.1 * (n i).1 := rfl

@[simp]
theorem mulRightMap_apply_single {M N : Submodule R S} {ι : Type*} (n : ι → N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap]

theorem mulLeftMap_eq_mulRightMap_of_commute [SMulCommClass R S S]
    {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι → M)
    (hc : ∀ (i : ι) (n : N), Commute (m i).1 n.1) : mulLeftMap N m = mulRightMap N m := by
  ext i n; simp [(hc i n).eq]

theorem mulLeftMap_eq_mulRightMap {S : Type*} [CommSemiring S] [Module R S] [SMulCommClass R R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {M : Submodule R S} (N : Submodule R S)
    {ι : Type*} (m : ι → M) : mulLeftMap N m = mulRightMap N m :=
  mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ ↦ mul_comm _ _

end Submodule
