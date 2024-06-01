/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Basis

#align_import algebra.direct_sum.module from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`DirectSum.toModule.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`.  There is a canonical linear map from this direct sum to `M` (`DirectSum.coeLinearMap`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`.  The property is defined more generally
elsewhere as `DirectSum.IsInternal`, but its basic consequences on `Submodule`s are established
in this file.

-/


universe u v w u₁

namespace DirectSum

open DirectSum

section General

variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

instance : Module R (⨁ i, M i) :=
  DFinsupp.module

instance {S : Type*} [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    SMulCommClass R S (⨁ i, M i) :=
  DFinsupp.smulCommClass

instance {S : Type*} [Semiring S] [SMul R S] [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
  DFinsupp.isScalarTower

instance [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
  DFinsupp.isCentralScalar

theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  DFinsupp.smul_apply _ _ _
#align direct_sum.smul_apply DirectSum.smul_apply

variable (R ι M)

/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i :=
  DFinsupp.lmk
#align direct_sum.lmk DirectSum.lmk

/-- Inclusion of each component into the direct sum. -/
def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i :=
  DFinsupp.lsingle
#align direct_sum.lof DirectSum.lof

theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := rfl
#align direct_sum.lof_eq_of DirectSum.lof_eq_of

variable {ι M}

theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b := rfl
#align direct_sum.single_eq_lof DirectSum.single_eq_lof

/-- Scalar multiplication commutes with direct sums. -/
theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
  (lmk R ι M s).map_smul c x
#align direct_sum.mk_smul DirectSum.mk_smul

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
  (lof R ι M i).map_smul c x
#align direct_sum.of_smul DirectSum.of_smul

variable {R}

theorem support_smul [∀ (i : ι) (x : M i), Decidable (x ≠ 0)] (c : R) (v : ⨁ i, M i) :
    (c • v).support ⊆ v.support :=
  DFinsupp.support_smul _ _
#align direct_sum.support_smul DirectSum.support_smul

variable {N : Type u₁} [AddCommMonoid N] [Module R N]
variable (φ : ∀ i, M i →ₗ[R] N)
variable (R ι N)

/-- The linear map constructed using the universal property of the coproduct. -/
def toModule : (⨁ i, M i) →ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum ℕ) φ
#align direct_sum.to_module DirectSum.toModule

/-- Coproducts in the categories of modules and additive monoids commute with the forgetful functor
from modules to additive monoids. -/
theorem coe_toModule_eq_coe_toAddMonoid :
    (toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i ↦ (φ i).toAddMonoidHom := rfl
#align direct_sum.coe_to_module_eq_coe_to_add_monoid DirectSum.coe_toModule_eq_coe_toAddMonoid

variable {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp]
theorem toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x :=
  toAddMonoid_of (fun i ↦ (φ i).toAddMonoidHom) i x
#align direct_sum.to_module_lof DirectSum.toModule_lof

variable (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i ↦ ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f
#align direct_sum.to_module.unique DirectSum.toModule.unique

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
    (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
  DFinsupp.lhom_ext' H
#align direct_sum.linear_map_ext DirectSum.linearMap_ext

/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map. -/
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i ↦ lof R T (fun i : Subtype T ↦ M i) ⟨i, H i.prop⟩
#align direct_sum.lset_to_set DirectSum.lsetToSet

variable (ι M)

/-- Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `∀ i, M i`. -/
@[simps apply]
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  { DFinsupp.equivFunOnFintype with
    toFun := (↑)
    map_add' := fun f g ↦ by
      ext
      rw [add_apply, Pi.add_apply]
    map_smul' := fun c f ↦ by
      simp_rw [RingHom.id_apply]
      rw [DFinsupp.coe_smul] }
#align direct_sum.linear_equiv_fun_on_fintype DirectSum.linearEquivFunOnFintype

variable {ι M}

@[simp]
theorem linearEquivFunOnFintype_lof [Fintype ι] [DecidableEq ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  ext a
  change (DFinsupp.equivFunOnFintype (lof R ι M i m)) a = _
  convert _root_.congr_fun (DFinsupp.equivFunOnFintype_single i m) a
#align direct_sum.linear_equiv_fun_on_fintype_lof DirectSum.linearEquivFunOnFintype_lof

@[simp]
theorem linearEquivFunOnFintype_symm_single [Fintype ι] [DecidableEq ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m := by
  change (DFinsupp.equivFunOnFintype.symm (Pi.single i m)) = _
  rw [DFinsupp.equivFunOnFintype_symm_single i m]
  rfl
#align direct_sum.linear_equiv_fun_on_fintype_symm_single DirectSum.linearEquivFunOnFintype_symm_single

@[simp]
theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (linearEquivFunOnFintype R ι M).symm f = f := by
  simp [linearEquivFunOnFintype]
#align direct_sum.linear_equiv_fun_on_fintype_symm_coe DirectSum.linearEquivFunOnFintype_symm_coe

/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
protected def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ ↦ LinearMap.id with }
#align direct_sum.lid DirectSum.lid

variable (ι M)

/-- The projection map onto one component, as a linear map. -/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  DFinsupp.lapply i
#align direct_sum.component DirectSum.component

variable {ι M}

theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f := rfl
#align direct_sum.apply_eq_component DirectSum.apply_eq_component

@[ext]
theorem ext {f g : ⨁ i, M i} (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
  DFinsupp.ext h
#align direct_sum.ext DirectSum.ext

theorem ext_iff {f g : ⨁ i, M i} : f = g ↔ ∀ i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ ↦ by rw [h], ext R⟩
#align direct_sum.ext_iff DirectSum.ext_iff

@[simp]
theorem lof_apply (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
  DFinsupp.single_eq_same
#align direct_sum.lof_apply DirectSum.lof_apply

@[simp]
theorem component.lof_self (i : ι) (b : M i) : component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b
#align direct_sum.component.lof_self DirectSum.component.lof_self

theorem component.of (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 :=
  DFinsupp.single_apply
#align direct_sum.component.of DirectSum.component.of

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum is linear. -/
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  { equivCongrLeft h with map_smul' := DFinsupp.comapDomain'_smul h.invFun h.right_inv }
#align direct_sum.lequiv_congr_left DirectSum.lequivCongrLeft

@[simp]
theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    lequivCongrLeft R h f k = f (h.symm k) :=
  equivCongrLeft_apply _ _ _
#align direct_sum.lequiv_congr_left_apply DirectSum.lequivCongrLeft_apply

end CongrLeft

section Sigma

variable {α : ι → Type*} {δ : ∀ i, α i → Type w}
variable [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

/-- `curry` as a linear map. -/
def sigmaLcurry : (⨁ i : Σi, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r ↦ by convert DFinsupp.sigmaCurry_smul (δ := δ) r }
#align direct_sum.sigma_lcurry DirectSum.sigmaLcurry

@[simp]
theorem sigmaLcurry_apply (f : ⨁ i : Σ_, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaLcurry R f i j = f ⟨i, j⟩ :=
  sigmaCurry_apply f i j
#align direct_sum.sigma_lcurry_apply DirectSum.sigmaLcurry_apply

-- Porting note: marked noncomputable
/-- `uncurry` as a linear map. -/
noncomputable def sigmaLuncurry [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σ_, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }
#align direct_sum.sigma_luncurry DirectSum.sigmaLuncurry

@[simp]
theorem sigmaLuncurry_apply [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)]
    (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigmaUncurry_apply f i j
#align direct_sum.sigma_luncurry_apply DirectSum.sigmaLuncurry_apply

/-- `curryEquiv` as a linear equiv. -/
def sigmaLcurryEquiv [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ i : Σ_, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurryEquiv, sigmaLcurry R with }
#align direct_sum.sigma_lcurry_equiv DirectSum.sigmaLcurryEquiv

end Sigma

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)] [∀ i, Module R (α i)]

/-- Linear isomorphism obtained by separating the term of index `none` of a direct sum over
`Option ι`. -/
@[simps]
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }
#align direct_sum.lequiv_prod_direct_sum DirectSum.lequivProdDirectSum

end Option

end General

section Submodule

section Semiring

variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι → Submodule R M)

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `Submodule R M`
indexed by `ι`. This is `DirectSum.coeAddMonoidHom` as a `LinearMap`. -/
def coeLinearMap : (⨁ i, A i) →ₗ[R] M :=
  toModule R ι M fun i ↦ (A i).subtype
#align direct_sum.coe_linear_map DirectSum.coeLinearMap

@[simp]
theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i ↦ A i) i x) = x :=
  -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i ↦ ((A i).subtype : A i →+ M)) i x
#align direct_sum.coe_linear_map_of DirectSum.coeLinearMap_of

variable {A}

@[simp]
theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = x := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_same]

@[simp]
theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_of_ne _ i j _ hij]

theorem IsInternal.ofBijective_coeLinearMap_of_mem (h : IsInternal A)
    {i : ι} {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_same ⟨x, hx⟩

theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 :=
  h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

/-- If a direct sum of submodules is internal then the submodules span the module. -/
theorem IsInternal.submodule_iSup_eq_top (h : IsInternal A) : iSup A = ⊤ := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.range_eq_top]
  exact Function.Bijective.surjective h
#align direct_sum.is_internal.submodule_supr_eq_top DirectSum.IsInternal.submodule_iSup_eq_top

/-- If a direct sum of submodules is internal then the submodules are independent. -/
theorem IsInternal.submodule_independent (h : IsInternal A) : CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_lsum_injective _ h.injective
#align direct_sum.is_internal.submodule_independent DirectSum.IsInternal.submodule_independent

/-- Given an internal direct sum decomposition of a module `M`, and a basis for each of the
components of the direct sum, the disjoint union of these bases is a basis for `M`. -/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σi, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm
#align direct_sum.is_internal.collected_basis DirectSum.IsInternal.collectedBasis

@[simp]
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σi, α i ↦ ↑(v a.1 a.2) := by
  funext a
  -- Porting note: was
  -- simp only [IsInternal.collectedBasis, toModule, coeLinearMap, Basis.coe_ofRepr,
  --   Basis.repr_symm_apply, DFinsupp.lsum_apply_apply, DFinsupp.mapRange.linearEquiv_apply,
  --   DFinsupp.mapRange.linearEquiv_symm, DFinsupp.mapRange_single, Finsupp.total_single,
  --   LinearEquiv.ofBijective_apply, LinearEquiv.symm_symm, LinearEquiv.symm_trans_apply, one_smul,
  --   sigmaFinsuppAddEquivDFinsupp_apply, sigmaFinsuppEquivDFinsupp_single,
  --   sigmaFinsuppLequivDFinsupp_apply]
  -- convert DFinsupp.sumAddHom_single (fun i ↦ (A i).subtype.toAddMonoidHom) a.1 (v a.1 a.2)
  simp only [IsInternal.collectedBasis, coeLinearMap, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, sigmaFinsuppLequivDFinsupp_apply,
    sigmaFinsuppEquivDFinsupp_single, LinearEquiv.ofBijective_apply,
    sigmaFinsuppAddEquivDFinsupp_apply]
  rw [DFinsupp.mapRange.linearEquiv_symm]
  erw [DFinsupp.mapRange.linearEquiv_apply]
  simp only [DFinsupp.mapRange_single, Basis.repr_symm_apply, Finsupp.total_single, one_smul,
    toModule]
  erw [DFinsupp.lsum_single]
  simp only [Submodule.coeSubtype]
#align direct_sum.is_internal.collected_basis_coe DirectSum.IsInternal.collectedBasis_coe

theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) (a : Σi, α i) : h.collectedBasis v a ∈ A a.1 := by simp
#align direct_sum.is_internal.collected_basis_mem DirectSum.IsInternal.collectedBasis_mem

theorem IsInternal.collectedBasis_repr_of_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i : ι} {a : α i} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨i, a⟩ = (v i).repr ⟨x, hx⟩ a := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i ≠ j) {a : α j} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

/-- When indexed by only two distinct elements, `DirectSum.IsInternal` implies
the two submodules are complementary. Over a `Ring R`, this is true as an iff, as
`DirectSum.isInternal_submodule_iff_isCompl`. -/
theorem IsInternal.isCompl {A : ι → Submodule R M} {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_independent.pairwiseDisjoint hij,
    codisjoint_iff.mpr <| Eq.symm <| hi.submodule_iSup_eq_top.symm.trans <| by
      rw [← sSup_pair, iSup, ← Set.image_univ, h, Set.image_insert_eq, Set.image_singleton]⟩
#align direct_sum.is_internal.is_compl DirectSum.IsInternal.isCompl

end Semiring

section Ring

variable {R : Type u} [Ring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Note that this is not generally true for `[Semiring R]`; see
`CompleteLattice.Independent.dfinsupp_lsum_injective` for details. -/
theorem isInternal_submodule_of_independent_of_iSup_eq_top {A : ι → Submodule R M}
    (hi : CompleteLattice.Independent A) (hs : iSup A = ⊤) : IsInternal A :=
  ⟨hi.dfinsupp_lsum_injective,
    -- Note: #8386 had to specify value of `f`
    (LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1 <|
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩
#align direct_sum.is_internal_submodule_of_independent_of_supr_eq_top DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top

/-- `iff` version of `DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top`,
`DirectSum.IsInternal.submodule_independent`, and `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
theorem isInternal_submodule_iff_independent_and_iSup_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ CompleteLattice.Independent A ∧ iSup A = ⊤ :=
  ⟨fun i ↦ ⟨i.submodule_independent, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_independent_of_iSup_eq_top⟩
#align direct_sum.is_internal_submodule_iff_independent_and_supr_eq_top DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

/-- If a collection of submodules has just two indices, `i` and `j`, then
`DirectSum.IsInternal` is equivalent to `isCompl`. -/
theorem isInternal_submodule_iff_isCompl (A : ι → Submodule R M) {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : ∀ k, k = i ∨ k = j := fun k ↦ by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_independent_and_iSup_eq_top, iSup, ← Set.image_univ, h,
    Set.image_insert_eq, Set.image_singleton, sSup_pair, CompleteLattice.independent_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ ↦ ⟨hd, codisjoint_iff.mpr ht⟩, fun ⟨hd, ht⟩ ↦ ⟨hd, ht.eq_top⟩⟩
#align direct_sum.is_internal_submodule_iff_is_compl DirectSum.isInternal_submodule_iff_isCompl

@[simp]
theorem isInternal_ne_bot_iff {A : ι → Submodule R M} :
    IsInternal (fun i : {i // A i ≠ ⊥} ↦ A i) ↔ IsInternal A := by
  simp only [isInternal_submodule_iff_independent_and_iSup_eq_top]
  exact Iff.and CompleteLattice.independent_ne_bot_iff_independent <| by simp

lemma isInternal_biSup_submodule_of_independent {A : ι → Submodule R M} (s : Set ι)
    (h : CompleteLattice.Independent <| fun i : s ↦ A i) :
    IsInternal <| fun (i : s) ↦ (A i).comap (⨆ i ∈ s, A i).subtype := by
  refine (isInternal_submodule_iff_independent_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i ∈ s, A i
  have hp : ∀ i ∈ s, A i ≤ p := fun i hi ↦ le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s ↦ (A i).comap p.subtype) = fun i ↦ ⟨A i, hp i i.property⟩ by
    rw [← CompleteLattice.independent_map_orderIso_iff e, this]
    exact CompleteLattice.independent_of_independent_coe_Iic_comp h
  ext i m
  change m ∈ ((A i).comap p.subtype).map p.subtype ↔ _
  rw [Submodule.map_comap_subtype, inf_of_le_right (hp i i.property)]

/-! Now copy the lemmas for subgroup and submonoids. -/


theorem IsInternal.addSubmonoid_independent {M : Type*} [AddCommMonoid M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_sumAddHom_injective _ h.injective
#align direct_sum.is_internal.add_submonoid_independent DirectSum.IsInternal.addSubmonoid_independent

theorem IsInternal.addSubgroup_independent {M : Type*} [AddCommGroup M] {A : ι → AddSubgroup M}
    (h : IsInternal A) : CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_sumAddHom_injective' _ h.injective
#align direct_sum.is_internal.add_subgroup_independent DirectSum.IsInternal.addSubgroup_independent

end Ring

end Submodule

end DirectSum
