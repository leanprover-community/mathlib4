/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

! This file was ported from Lean 3 source module linear_algebra.dfinsupp
! leanprover-community/mathlib commit a148d797a1094ab554ad4183a4ad6f130358ef64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finsupp.ToDfinsupp
import Mathlib.LinearAlgebra.Basis

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Data.Dfinsupp`.

In this file we define `LinearMap` versions of various maps:

* `Dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `Dfinsupp.single a` as a linear map;

* `Dfinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `Dfinsupp.single a` as a linear map;

* `Dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `Dfinsupp.lsum`: `Dfinsupp.sum` or `Dfinsupp.liftAddHom` as a `LinearMap`;

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

variable {ι : Type _} {R : Type _} {S : Type _} {M : ι → Type _} {N : Type _}

variable [dec_ι : DecidableEq ι]

namespace Dfinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [AddCommMonoid N] [Module R N]

/-- `Dfinsupp.mk` as a `LinearMap`. -/
def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x
#align dfinsupp.lmk Dfinsupp.lmk

/-- `Dfinsupp.single` as a `LinearMap` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { Dfinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }
#align dfinsupp.lsingle Dfinsupp.lsingle

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
#align dfinsupp.lhom_ext Dfinsupp.lhom_ext

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext 1100]
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)
#align dfinsupp.lhom_ext' Dfinsupp.lhom_ext'

/-- Interpret `fun (f : Π₀ i, M i) ↦ f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i
#align dfinsupp.lapply Dfinsupp.lapply

@[simp]
theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl
#align dfinsupp.lmk_apply Dfinsupp.lmk_apply

@[simp]
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) →ₗ[R] _) x = single i x :=
  rfl
#align dfinsupp.lsingle_apply Dfinsupp.lsingle_apply

@[simp]
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) →ₗ[R] _) f = f i :=
  rfl
#align dfinsupp.lapply_apply Dfinsupp.lapply_apply

section Lsum

-- Porting note: Unclear how true these docstrings are in lean 4
/-- Typeclass inference can't find `Dfinsupp.addCommMonoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`Dfinsupp.moduleOfLinearMap`. -/
instance addCommMonoidOfLinearMap : AddCommMonoid (Π₀ i : ι, M i →ₗ[R] N) :=
  inferInstance
#align dfinsupp.add_comm_monoid_of_linear_map Dfinsupp.addCommMonoidOfLinearMap

/-- Typeclass inference can't find `Dfinsupp.module` without help for this case.
This is needed to define `Dfinsupp.lsum` below.

The cause seems to be an inability to unify the `∀ i, AddCommMonoid (M i →ₗ[R] N)` instance that
we have with the `∀ i, Zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`Dfinsupp` type. -/
instance moduleOfLinearMap [Semiring S] [Module S N] [SMulCommClass R S N] :
    Module S (Π₀ i : ι, M i →ₗ[R] N) :=
  Dfinsupp.module
#align dfinsupp.module_of_linear_map Dfinsupp.moduleOfLinearMap

variable (S)


instance {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) (M₂ : Type _)
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] :
    EquivLike (LinearEquiv σ M M₂) M M₂ :=
  inferInstance

/- Porting note: In every application of lsum that follows, the argument M needs to be explicitly
supplied, lean does not manage to gather that information itself -/
/-- The `Dfinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      -- Porting note: needed to (β := M) hint below
      map_add' := (Dfinsupp.liftAddHom (β := M) (fun (i : ι) => (F i).toAddMonoidHom)).map_add
      map_smul' := fun c f => by
        dsimp
        apply Dfinsupp.induction f
        · rw [smul_zero, AddMonoidHom.map_zero, smul_zero]
        · intro a b f _ _ hf
          rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, smul_add, hf, ← single_smul,
            sumAddHom_single, sumAddHom_single, LinearMap.toAddMonoidHom_coe,
            LinearMap.map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    simp
  right_inv F := by
    refine Dfinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_add' F G := by
    refine Dfinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_smul' c F := by
    refine Dfinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
#align dfinsupp.lsum Dfinsupp.lsum

/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sumAddHom`
with `Dfinsupp.lsum_apply_apply`. -/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : ∀ i, M i →ₗ[R] N) (i)
    (x : M i) : lsum S (M := M) F (single i x) = F i x := by
  simp
#align dfinsupp.lsum_single Dfinsupp.lsum_single

end Lsum

/-! ### Bundled versions of `Dfinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/


section mapRange

variable {β β₁ β₂ : ι → Type _}

variable [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (β₁ i)] [∀ i, AddCommMonoid (β₂ i)]

variable [∀ i, Module R (β i)] [∀ i, Module R (β₁ i)] [∀ i, Module R (β₂ i)]

theorem mapRange_smul (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (r : R)
    (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g := by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']
#align dfinsupp.map_range_smul Dfinsupp.mapRange_smul

/-- `Dfinsupp.mapRange` as a `LinearMap`. -/
@[simps! apply]
def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }
#align dfinsupp.map_range.linear_map Dfinsupp.mapRange.linearMap

@[simp]
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i →ₗ[R] _)) = LinearMap.id := by
  ext
  simp [linearMap]
#align dfinsupp.map_range.linear_map_id Dfinsupp.mapRange.linearMap_id

theorem mapRange.linearMap_comp (f : ∀ i, β₁ i →ₗ[R] β₂ i) (f₂ : ∀ i, β i →ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)
#align dfinsupp.map_range.linear_map_comp Dfinsupp.mapRange.linearMap_comp

theorem sum_mapRange_index.linearMap [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i →ₗ[R] β₂ i} {h : ∀ i, β₂ i →ₗ[R] N}
    {l : Π₀ i, β₁ i} :
    -- Porting note: Needed to add (M := ...) below
    (Dfinsupp.lsum ℕ (M := β₂)) h (mapRange.linearMap f l)
      = (Dfinsupp.lsum ℕ (M := β₁)) (fun i => (h i).comp (f i)) l  := by
  simpa [Dfinsupp.sumAddHom_apply] using sum_mapRange_index fun i => by simp
#align dfinsupp.sum_map_range_index.linear_map Dfinsupp.sum_mapRange_index.linearMap

/-- `Dfinsupp.mapRange.linearMap` as a `LinearEquiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }
#align dfinsupp.map_range.linear_equiv Dfinsupp.mapRange.linearEquiv

@[simp]
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id
#align dfinsupp.map_range.linear_equiv_refl Dfinsupp.mapRange.linearEquiv_refl

theorem mapRange.linearEquiv_trans (f : ∀ i, β i ≃ₗ[R] β₁ i) (f₂ : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)
#align dfinsupp.map_range.linear_equiv_trans Dfinsupp.mapRange.linearEquiv_trans

@[simp]
theorem mapRange.linearEquiv_symm (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl
#align dfinsupp.map_range.linear_equiv_symm Dfinsupp.mapRange.linearEquiv_symm

end mapRange

section CoprodMap

variable [DecidableEq ι] [∀ x : N, Decidable (x ≠ 0)]

/-- Given a family of linear maps `f i : M i  →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `LinearMap.coprod` for the binary product version. -/
noncomputable def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (Finsupp.lsum ℕ fun _ : ι => LinearMap.id) ∘ₗ
    (@finsuppLequivDfinsupp ι R N _ _ _ _ _).symm.toLinearMap ∘ₗ Dfinsupp.mapRange.linearMap f
#align dfinsupp.coprod_map Dfinsupp.coprodMap

theorem coprodMap_apply (f : ∀ i : ι, M i →ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      Finsupp.sum (mapRange (fun i => f i) (fun _ => LinearMap.map_zero _) x).toFinsupp fun _ =>
        id :=
  rfl
#align dfinsupp.coprod_map_apply Dfinsupp.coprodMap_apply

theorem coprodMap_apply_single (f : ∀ i : ι, M i →ₗ[R] N) (i : ι) (x : M i) :
    coprodMap f (single i x) = f i x := by
  simp [coprodMap_apply]

end CoprodMap

section Basis

/-- The direct sum of free modules is free.

Note that while this is stated for `Dfinsupp` not `DirectSum`, the types are defeq. -/
noncomputable def basis {η : ι → Type _} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σi, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDfinsupp R).symm)
#align dfinsupp.basis Dfinsupp.basis

end Basis

end Dfinsupp

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open Dfinsupp

theorem dfinsupp_sum_mem {β : ι → Type _} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : ∀ i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    f.sum g ∈ S :=
  _root_.dfinsupp_sum_mem S f g h
#align submodule.dfinsupp_sum_mem Submodule.dfinsupp_sum_mem

theorem dfinsupp_sumAddHom_mem {β : ι → Type _} [∀ i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    Dfinsupp.sumAddHom g f ∈ S :=
  _root_.dfinsupp_sumAddHom_mem S f g h
#align submodule.dfinsupp_sum_add_hom_mem Submodule.dfinsupp_sumAddHom_mem

/-- The supremum of a family of submodules is equal to the range of `Dfinsupp.lsum`; that is
every element in the `iSup` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
theorem iSup_eq_range_dfinsupp_lsum (p : ι → Submodule R N) :
    iSup p = LinearMap.range (Dfinsupp.lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨Dfinsupp.single i ⟨y, hy⟩, Dfinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i ≤ _) (v i).2
#align submodule.supr_eq_range_dfinsupp_lsum Submodule.iSup_eq_range_dfinsupp_lsum

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`Dfinsupp.sumAddHom` composed with `Dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem biSup_eq_range_dfinsupp_lsum (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range
        (LinearMap.comp
          (Dfinsupp.lsum ℕ (M := fun i ↦ ↥(S i)) (fun i => (S i).subtype))
            (Dfinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  · refine' iSup₂_le fun i hi y hy => ⟨Dfinsupp.single i ⟨y, hy⟩, _⟩
    rw [LinearMap.comp_apply, filterLinearMap_apply, filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coeSubtype]
  · rintro x ⟨v, rfl⟩
    refine' dfinsupp_sumAddHom_mem _ _ _ fun i _ => _
    refine' mem_iSup_of_mem i _
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
#align submodule.bsupr_eq_range_dfinsupp_lsum Submodule.biSup_eq_range_dfinsupp_lsum

theorem mem_iSup_iff_exists_dfinsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔
      ∃ f : Π₀ i, p i, Dfinsupp.lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x
#align submodule.mem_supr_iff_exists_dfinsupp Submodule.mem_iSup_iff_exists_dfinsupp

/-- A variant of `Submodule.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι → Submodule R N) [∀ (i) (x : p i), Decidable (x ≠ 0)]
    (x : N) : x ∈ iSup p ↔ ∃ f : Π₀ i, p i, (f.sum fun i xi => ↑xi) = x := by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [Dfinsupp.lsum_apply_apply, Dfinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coeSubtype]
#align submodule.mem_supr_iff_exists_dfinsupp' Submodule.mem_iSup_iff_exists_dfinsupp'

theorem mem_biSup_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i,
        Dfinsupp.lsum ℕ (M := fun i ↦ ↥(S i)) (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x
#align submodule.mem_bsupr_iff_exists_dfinsupp Submodule.mem_biSup_iff_exists_dfinsupp

open BigOperators

theorem mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι → Submodule R N) (a : N) :
    (a ∈ ⨆ i ∈ s, p i) ↔ ∃ μ : ∀ i, p i, (∑ i in s, (μ i : N)) = a := by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ ≤ p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_support_iff, not_ne_iff]
        ext
        rw [coe_zero, ← mem_bot R]
        suffices : ⊥ = ⨆ (_ : x ∈ s), p x
        · exact this.symm ▸ coe_mem (μ x)
        exact (iSup_neg hx).symm
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
    · refine' ⟨Dfinsupp.mk s _, _⟩
      · rintro ⟨i, hi⟩
        refine' ⟨μ i, _⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [Dfinsupp.sum]
      rw [Finset.sum_subset support_mk_subset, ← hμ]
      exact Finset.sum_congr rfl fun x hx => congr_arg Subtype.val <| mk_of_mem hx
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
#align submodule.mem_supr_finset_iff_exists_sum Submodule.mem_iSup_finset_iff_exists_sum

end Submodule

namespace CompleteLattice

open Dfinsupp

section Semiring

variable [Semiring R] [AddCommMonoid N] [Module R N]

/-- Independence of a family of submodules can be expressed as a quantifier over `Dfinsupp`s.

This is an intermediate result used to prove
`CompleteLattice.independent_of_dfinsupp_lsum_injective` and
`CompleteLattice.Independent.dfinsupp_lsum_injective`. -/
theorem independent_iff_forall_dfinsupp (p : ι → Submodule R N) :
    Independent p ↔
      ∀ (i) (x : p i) (v : Π₀ i : ι, ↥(p i)),
        lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) (erase i v) = x → x = 0 := by
  simp_rw [CompleteLattice.independent_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine' forall_congr' fun i => Subtype.forall'.trans _
  simp_rw [Submodule.coe_eq_zero]
#align complete_lattice.independent_iff_forall_dfinsupp CompleteLattice.independent_iff_forall_dfinsupp

/- If `Dfinsupp.lsum` applied with `Submodule.subtype` is injective then the submodules are
independent. -/
theorem independent_of_dfinsupp_lsum_injective (p : ι → Submodule R N)
    (h : Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype)) :
    Independent p := by
  rw [independent_iff_forall_dfinsupp]
  intro i x v hv
  replace hv :
    lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) (erase i v) =
      lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) (single i x)
  · simpa only [lsum_single] using hv
  have := FunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using this
#align complete_lattice.independent_of_dfinsupp_lsum_injective CompleteLattice.independent_of_dfinsupp_lsum_injective

/- If `Dfinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
submonoids are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective (p : ι → AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : Independent p := by
  rw [← independent_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact independent_of_dfinsupp_lsum_injective _ h
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective CompleteLattice.independent_of_dfinsupp_sumAddHom_injective

/-- Combining `Dfinsupp.lsum` with `LinearMap.toSpanSingleton` is the same as `Finsupp.total` -/
theorem lsum_comp_mapRange_toSpanSingleton [∀ m : R, Decidable (m ≠ 0)] (p : ι → Submodule R N)
    {v : ι → N} (hv : ∀ i : ι, v i ∈ p i) :
    (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype : _ →ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ →ₗ[R] _).comp
          (finsuppLequivDfinsupp R : (ι →₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.total ι N R v := by
  ext
  simp
#align complete_lattice.lsum_comp_map_range_to_span_singleton CompleteLattice.lsum_comp_mapRange_toSpanSingleton

end Semiring

section Ring

variable [Ring R] [AddCommGroup N] [Module R N]

/- If `Dfinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
subgroups are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective' (p : ι → AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : Independent p := by
  rw [← independent_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact independent_of_dfinsupp_lsum_injective _ h
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective' CompleteLattice.independent_of_dfinsupp_sumAddHom_injective'

/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `CompleteLattice.Independent`.

Note that this is not generally true for `[Semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `counterexamples/direct_sum_is_internal.lean` for a proof of this fact. -/
theorem Independent.dfinsupp_lsum_injective {p : ι → Submodule R N} (h : Independent p) :
    Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) := by
  -- simplify everything down to binders over equalities in `N`
  rw [independent_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    letI thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  intro m hm
  ext i : 1
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [Dfinsupp.zero_apply, ← neg_eq_zero]
  refine' h i (-m i) m _
  rwa [← erase_add_single i m, LinearMap.map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm
#align complete_lattice.independent.dfinsupp_lsum_injective CompleteLattice.Independent.dfinsupp_lsum_injective

/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `CompleteLattice.Independent`. -/
theorem Independent.dfinsupp_sumAddHom_injective {p : ι → AddSubgroup N} (h : Independent p) :
    Function.Injective (sumAddHom fun i => (p i).subtype) := by
  rw [← independent_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective
#align complete_lattice.independent.dfinsupp_sum_add_hom_injective CompleteLattice.Independent.dfinsupp_sumAddHom_injective

/-- A family of submodules over an additive group are independent if and only iff `Dfinsupp.lsum`
applied with `Submodule.subtype` is injective.

Note that this is not generally true for `[Semiring R]`; see
`CompleteLattice.Independent.dfinsupp_lsum_injective` for details. -/
theorem independent_iff_dfinsupp_lsum_injective (p : ι → Submodule R N) :
    Independent p ↔ Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) :=
  ⟨Independent.dfinsupp_lsum_injective, independent_of_dfinsupp_lsum_injective p⟩
#align complete_lattice.independent_iff_dfinsupp_lsum_injective CompleteLattice.independent_iff_dfinsupp_lsum_injective

/-- A family of additive subgroups over an additive group are independent if and only if
`Dfinsupp.sumAddHom` applied with `AddSubgroup.subtype` is injective. -/
theorem independent_iff_dfinsupp_sumAddHom_injective (p : ι → AddSubgroup N) :
    Independent p ↔ Function.Injective (sumAddHom fun i => (p i).subtype) :=
  ⟨Independent.dfinsupp_sumAddHom_injective, independent_of_dfinsupp_sumAddHom_injective' p⟩
#align complete_lattice.independent_iff_dfinsupp_sum_add_hom_injective CompleteLattice.independent_iff_dfinsupp_sumAddHom_injective

/-- If a family of submodules is `Independent`, then a choice of nonzero vector from each submodule
forms a linearly independent family.

See also `CompleteLattice.Independent.linearIndependent'`. -/
theorem Independent.linearIndependent [NoZeroSMulDivisors R N] (p : ι → Submodule R N)
    (hp : Independent p) {v : ι → N} (hv : ∀ i, v i ∈ p i) (hv' : ∀ i, v i ≠ 0) :
    LinearIndependent R v := by
  let _ := Classical.decEq ι
  let _ := Classical.decEq R
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    Dfinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDfinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext i
  apply smul_left_injective R (hv' i)
  have : l i • v i = a i := rfl
  simp only [coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, smul_eq_zero, ha] at this
  simpa
#align complete_lattice.independent.linear_independent CompleteLattice.Independent.linearIndependent

theorem independent_iff_linearIndependent_of_ne_zero [NoZeroSMulDivisors R N] {v : ι → N}
    (h_ne_zero : ∀ i, v i ≠ 0) : (Independent fun i => R ∙ v i) ↔ LinearIndependent R v :=
  let _ := Classical.decEq ι
  ⟨fun hv => hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero,
    fun hv => hv.independent_span_singleton⟩
#align complete_lattice.independent_iff_linear_independent_of_ne_zero CompleteLattice.independent_iff_linearIndependent_of_ne_zero

end Ring

end CompleteLattice
