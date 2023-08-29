/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.Basis

#align_import linear_algebra.dfinsupp from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Data.DFinsupp`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`;

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

variable {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

variable [dec_ι : DecidableEq ι]

namespace DFinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [AddCommMonoid N] [Module R N]

/-- `DFinsupp.mk` as a `LinearMap`. -/
def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x
#align dfinsupp.lmk DFinsupp.lmk

/-- `DFinsupp.single` as a `LinearMap` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }
#align dfinsupp.lsingle DFinsupp.lsingle

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
#align dfinsupp.lhom_ext DFinsupp.lhom_ext

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext 1100]
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)
#align dfinsupp.lhom_ext' DFinsupp.lhom_ext'

/-- Interpret `fun (f : Π₀ i, M i) ↦ f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i
#align dfinsupp.lapply DFinsupp.lapply

@[simp]
theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl
#align dfinsupp.lmk_apply DFinsupp.lmk_apply

@[simp]
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) →ₗ[R] _) x = single i x :=
  rfl
#align dfinsupp.lsingle_apply DFinsupp.lsingle_apply

@[simp]
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) →ₗ[R] _) f = f i :=
  rfl
#align dfinsupp.lapply_apply DFinsupp.lapply_apply

section Lsum

-- Porting note: Unclear how true these docstrings are in lean 4
/-- Typeclass inference can't find `DFinsupp.addCommMonoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`DFinsupp.moduleOfLinearMap`. -/
instance addCommMonoidOfLinearMap : AddCommMonoid (Π₀ i : ι, M i →ₗ[R] N) :=
  inferInstance
#align dfinsupp.add_comm_monoid_of_linear_map DFinsupp.addCommMonoidOfLinearMap

/-- Typeclass inference can't find `DFinsupp.module` without help for this case.
This is needed to define `DFinsupp.lsum` below.

The cause seems to be an inability to unify the `∀ i, AddCommMonoid (M i →ₗ[R] N)` instance that
we have with the `∀ i, Zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`DFinsupp` type. -/
instance moduleOfLinearMap [Semiring S] [Module S N] [SMulCommClass R S N] :
    Module S (Π₀ i : ι, M i →ₗ[R] N) :=
  DFinsupp.module
#align dfinsupp.module_of_linear_map DFinsupp.moduleOfLinearMap

variable (S)


instance {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] :
    EquivLike (LinearEquiv σ M M₂) M M₂ :=
  inferInstance

/- Porting note: In every application of lsum that follows, the argument M needs to be explicitly
supplied, lean does not manage to gather that information itself -/
/-- The `DFinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      -- Porting note: needed to (β := M) hint below
      map_add' := (DFinsupp.liftAddHom (β := M) (fun (i : ι) => (F i).toAddMonoidHom)).map_add
      map_smul' := fun c f => by
        dsimp
        -- ⊢ ↑(sumAddHom fun i => LinearMap.toAddMonoidHom (F i)) (c • f) = c • ↑(sumAddH …
        apply DFinsupp.induction f
        -- ⊢ ↑(sumAddHom fun i => LinearMap.toAddMonoidHom (F i)) (c • 0) = c • ↑(sumAddH …
        · rw [smul_zero, AddMonoidHom.map_zero, smul_zero]
          -- 🎉 no goals
        · intro a b f _ _ hf
          -- ⊢ ↑(sumAddHom fun i => LinearMap.toAddMonoidHom (F i)) (c • (single a b + f))  …
          rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, smul_add, hf, ← single_smul,
            sumAddHom_single, sumAddHom_single, LinearMap.toAddMonoidHom_coe,
            LinearMap.map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    -- ⊢ ↑((fun F i => LinearMap.comp F (lsingle i)) (AddHom.toFun { toAddHom := { to …
    simp
    -- 🎉 no goals
  right_inv F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    -- ⊢ LinearMap.comp (AddHom.toFun { toAddHom := { toFun := fun F => { toAddHom := …
    ext
    -- ⊢ LinearMap.comp ((fun F => { toAddHom := { toFun := ↑(sumAddHom fun i => Line …
    -- ⊢ ↑(LinearMap.comp (AddHom.toFun { toAddHom := { toFun := fun F => { toAddHom  …
    -- ⊢ ↑(LinearMap.comp ((fun F => { toAddHom := { toFun := ↑(sumAddHom fun i => Li …
    simp
    -- 🎉 no goals
    -- 🎉 no goals
  map_add' F G := by
    -- ⊢ LinearMap.comp (AddHom.toFun { toFun := fun F => { toAddHom := { toFun := ↑( …
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    -- ⊢ ↑(LinearMap.comp (AddHom.toFun { toFun := fun F => { toAddHom := { toFun :=  …
    ext
    -- 🎉 no goals
    simp
  map_smul' c F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
#align dfinsupp.lsum DFinsupp.lsum

/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sumAddHom`
with `DFinsupp.lsum_apply_apply`. -/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : ∀ i, M i →ₗ[R] N) (i)
    (x : M i) : lsum S (M := M) F (single i x) = F i x := by
  simp
  -- 🎉 no goals
#align dfinsupp.lsum_single DFinsupp.lsum_single

end Lsum

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/


section mapRange

variable {β β₁ β₂ : ι → Type*}

variable [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (β₁ i)] [∀ i, AddCommMonoid (β₂ i)]

variable [∀ i, Module R (β i)] [∀ i, Module R (β₁ i)] [∀ i, Module R (β₂ i)]

theorem mapRange_smul (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (r : R)
    (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g := by
  ext
  -- ⊢ ↑(mapRange f hf (r • g)) i✝ = ↑(r • mapRange f hf g) i✝
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']
  -- 🎉 no goals
#align dfinsupp.map_range_smul DFinsupp.mapRange_smul

/-- `DFinsupp.mapRange` as a `LinearMap`. -/
@[simps! apply]
def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }
#align dfinsupp.map_range.linear_map DFinsupp.mapRange.linearMap

@[simp]
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i →ₗ[R] _)) = LinearMap.id := by
  ext
  -- ⊢ ↑(↑(LinearMap.comp (linearMap fun i => LinearMap.id) (lsingle i✝¹)) x✝) i✝ = …
  simp [linearMap]
  -- 🎉 no goals
#align dfinsupp.map_range.linear_map_id DFinsupp.mapRange.linearMap_id

theorem mapRange.linearMap_comp (f : ∀ i, β₁ i →ₗ[R] β₂ i) (f₂ : ∀ i, β i →ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)
                                                             -- 🎉 no goals
#align dfinsupp.map_range.linear_map_comp DFinsupp.mapRange.linearMap_comp

theorem sum_mapRange_index.linearMap [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i →ₗ[R] β₂ i} {h : ∀ i, β₂ i →ₗ[R] N}
    {l : Π₀ i, β₁ i} :
    -- Porting note: Needed to add (M := ...) below
    (DFinsupp.lsum ℕ (M := β₂)) h (mapRange.linearMap f l)
      = (DFinsupp.lsum ℕ (M := β₁)) (fun i => (h i).comp (f i)) l  := by
  simpa [DFinsupp.sumAddHom_apply] using sum_mapRange_index fun i => by simp
  -- 🎉 no goals
#align dfinsupp.sum_map_range_index.linear_map DFinsupp.sum_mapRange_index.linearMap

/-- `DFinsupp.mapRange.linearMap` as a `LinearEquiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }
#align dfinsupp.map_range.linear_equiv DFinsupp.mapRange.linearEquiv

@[simp]
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id
#align dfinsupp.map_range.linear_equiv_refl DFinsupp.mapRange.linearEquiv_refl

theorem mapRange.linearEquiv_trans (f : ∀ i, β i ≃ₗ[R] β₁ i) (f₂ : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)
                                                             -- 🎉 no goals
#align dfinsupp.map_range.linear_equiv_trans DFinsupp.mapRange.linearEquiv_trans

@[simp]
theorem mapRange.linearEquiv_symm (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl
#align dfinsupp.map_range.linear_equiv_symm DFinsupp.mapRange.linearEquiv_symm

end mapRange

section CoprodMap

variable [DecidableEq ι] [∀ x : N, Decidable (x ≠ 0)]

/-- Given a family of linear maps `f i : M i →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `LinearMap.coprod` for the binary product version. -/
def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (DFinsupp.lsum ℕ fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f
#align dfinsupp.coprod_map DFinsupp.coprodMap

theorem coprodMap_apply (f : ∀ i : ι, M i →ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      DFinsupp.sum (mapRange (fun i => f i) (fun _ => LinearMap.map_zero _) x) fun _ =>
        id :=
  DFinsupp.sumAddHom_apply _ _
#align dfinsupp.coprod_map_apply DFinsupp.coprodMap_apply

theorem coprodMap_apply_single (f : ∀ i : ι, M i →ₗ[R] N) (i : ι) (x : M i) :
    coprodMap f (single i x) = f i x := by
  simp [coprodMap]
  -- 🎉 no goals

end CoprodMap

section Basis

/-- The direct sum of free modules is free.

Note that while this is stated for `DFinsupp` not `DirectSum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σi, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)
#align dfinsupp.basis DFinsupp.basis

end Basis

end DFinsupp

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open DFinsupp

theorem dfinsupp_sum_mem {β : ι → Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : ∀ i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    f.sum g ∈ S :=
  _root_.dfinsupp_sum_mem S f g h
#align submodule.dfinsupp_sum_mem Submodule.dfinsupp_sum_mem

theorem dfinsupp_sumAddHom_mem {β : ι → Type*} [∀ i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    DFinsupp.sumAddHom g f ∈ S :=
  _root_.dfinsupp_sumAddHom_mem S f g h
#align submodule.dfinsupp_sum_add_hom_mem Submodule.dfinsupp_sumAddHom_mem

/-- The supremum of a family of submodules is equal to the range of `DFinsupp.lsum`; that is
every element in the `iSup` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
theorem iSup_eq_range_dfinsupp_lsum (p : ι → Submodule R N) :
    iSup p = LinearMap.range (DFinsupp.lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) := by
  apply le_antisymm
  -- ⊢ iSup p ≤ LinearMap.range (↑(lsum ℕ) fun i => Submodule.subtype (p i))
  · apply iSup_le _
    -- ⊢ ∀ (i : ι), p i ≤ LinearMap.range (↑(lsum ℕ) fun i => Submodule.subtype (p i))
    intro i y hy
    -- ⊢ y ∈ LinearMap.range (↑(lsum ℕ) fun i => Submodule.subtype (p i))
    simp only [LinearMap.mem_range, lsum_apply_apply]
    -- ⊢ ∃ y_1, ↑(sumAddHom fun i => LinearMap.toAddMonoidHom (Submodule.subtype (p i …
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
    -- 🎉 no goals
  · rintro x ⟨v, rfl⟩
    -- ⊢ ↑(↑(lsum ℕ) fun i => Submodule.subtype (p i)) v ∈ iSup p
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i ≤ _) (v i).2
    -- 🎉 no goals
#align submodule.supr_eq_range_dfinsupp_lsum Submodule.iSup_eq_range_dfinsupp_lsum

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem biSup_eq_range_dfinsupp_lsum (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range
        (LinearMap.comp
          (DFinsupp.lsum ℕ (M := fun i ↦ ↥(S i)) (fun i => (S i).subtype))
            (DFinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  -- ⊢ ⨆ (i : ι) (_ : p i), S i ≤ LinearMap.range (LinearMap.comp (↑(lsum ℕ) fun i  …
  · refine' iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, _⟩
    -- ⊢ ↑(LinearMap.comp (↑(lsum ℕ) fun i => Submodule.subtype (S i)) (filterLinearM …
    rw [LinearMap.comp_apply, filterLinearMap_apply, filter_single_pos _ _ hi]
    -- ⊢ ↑(↑(lsum ℕ) fun i => Submodule.subtype (S i)) (single i { val := y, property …
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coeSubtype]
    -- 🎉 no goals
  · rintro x ⟨v, rfl⟩
    -- ⊢ ↑(LinearMap.comp (↑(lsum ℕ) fun i => Submodule.subtype (S i)) (filterLinearM …
    refine' dfinsupp_sumAddHom_mem _ _ _ fun i _ => _
    -- ⊢ ↑((fun i => LinearMap.toAddMonoidHom ((fun i => Submodule.subtype (S i)) i)) …
    refine' mem_iSup_of_mem i _
    -- ⊢ ↑((fun i => LinearMap.toAddMonoidHom ((fun i => Submodule.subtype (S i)) i)) …
    by_cases hp : p i
    -- ⊢ ↑((fun i => LinearMap.toAddMonoidHom ((fun i => Submodule.subtype (S i)) i)) …
    · simp [hp]
      -- 🎉 no goals
    · simp [hp]
      -- 🎉 no goals
#align submodule.bsupr_eq_range_dfinsupp_lsum Submodule.biSup_eq_range_dfinsupp_lsum

theorem mem_iSup_iff_exists_dfinsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔
      ∃ f : Π₀ i, p i, DFinsupp.lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x
#align submodule.mem_supr_iff_exists_dfinsupp Submodule.mem_iSup_iff_exists_dfinsupp

/-- A variant of `Submodule.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι → Submodule R N) [∀ (i) (x : p i), Decidable (x ≠ 0)]
    (x : N) : x ∈ iSup p ↔ ∃ f : Π₀ i, p i, (f.sum fun i xi => ↑xi) = x := by
  rw [mem_iSup_iff_exists_dfinsupp]
  -- ⊢ (∃ f, ↑(↑(lsum ℕ) fun i => Submodule.subtype (p i)) f = x) ↔ ∃ f, (sum f fun …
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coeSubtype]
#align submodule.mem_supr_iff_exists_dfinsupp' Submodule.mem_iSup_iff_exists_dfinsupp'

theorem mem_biSup_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i,
        DFinsupp.lsum ℕ (M := fun i ↦ ↥(S i)) (fun i => (S i).subtype) (f.filter p) = x :=
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
    · refine' ⟨DFinsupp.mk s _, _⟩
      · rintro ⟨i, hi⟩
        refine' ⟨μ i, _⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [DFinsupp.sum]
      rw [Finset.sum_subset support_mk_subset, ← hμ]
      exact Finset.sum_congr rfl fun x hx => congr_arg Subtype.val <| mk_of_mem hx
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
#align submodule.mem_supr_finset_iff_exists_sum Submodule.mem_iSup_finset_iff_exists_sum

end Submodule

namespace CompleteLattice

open DFinsupp

section Semiring

variable [Semiring R] [AddCommMonoid N] [Module R N]

/-- Independence of a family of submodules can be expressed as a quantifier over `DFinsupp`s.

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
  -- ⊢ (∀ (x : { a // a ∈ p i }) (x_1 : Π₀ (i : ι), { x // x ∈ p i }), ↑(↑(lsum ℕ)  …
  simp_rw [Submodule.coe_eq_zero]
  -- 🎉 no goals
#align complete_lattice.independent_iff_forall_dfinsupp CompleteLattice.independent_iff_forall_dfinsupp

/- If `DFinsupp.lsum` applied with `Submodule.subtype` is injective then the submodules are
independent. -/
theorem independent_of_dfinsupp_lsum_injective (p : ι → Submodule R N)
    (h : Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype)) :
    Independent p := by
  rw [independent_iff_forall_dfinsupp]
  -- ⊢ ∀ (i : ι) (x : { x // x ∈ p i }) (v : Π₀ (i : ι), { x // x ∈ p i }), ↑(↑(lsu …
  intro i x v hv
  -- ⊢ x = 0
  replace hv :
    lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) (erase i v) =
      lsum ℕ (M := fun i ↦ ↥(p i)) (fun i => (p i).subtype) (single i x)
  · simpa only [lsum_single] using hv
    -- 🎉 no goals
  have := FunLike.ext_iff.mp (h hv) i
  -- ⊢ x = 0
  simpa [eq_comm] using this
  -- 🎉 no goals
#align complete_lattice.independent_of_dfinsupp_lsum_injective CompleteLattice.independent_of_dfinsupp_lsum_injective

/- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
submonoids are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective (p : ι → AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : Independent p := by
  rw [← independent_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  -- ⊢ Independent (↑AddSubmonoid.toNatSubmodule ∘ p)
  exact independent_of_dfinsupp_lsum_injective _ h
  -- 🎉 no goals
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective CompleteLattice.independent_of_dfinsupp_sumAddHom_injective

/-- Combining `DFinsupp.lsum` with `LinearMap.toSpanSingleton` is the same as `Finsupp.total` -/
theorem lsum_comp_mapRange_toSpanSingleton [∀ m : R, Decidable (m ≠ 0)] (p : ι → Submodule R N)
    {v : ι → N} (hv : ∀ i : ι, v i ∈ p i) :
    (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype : _ →ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ →ₗ[R] _).comp
          (finsuppLequivDFinsupp R : (ι →₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.total ι N R v := by
  ext
  -- ⊢ ↑(LinearMap.comp (LinearMap.comp (↑(lsum ℕ) fun i => Submodule.subtype (p i) …
  simp
  -- 🎉 no goals
#align complete_lattice.lsum_comp_map_range_to_span_singleton CompleteLattice.lsum_comp_mapRange_toSpanSingleton

end Semiring

section Ring

variable [Ring R] [AddCommGroup N] [Module R N]

/- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
subgroups are independent. -/
theorem independent_of_dfinsupp_sumAddHom_injective' (p : ι → AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : Independent p := by
  rw [← independent_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  -- ⊢ Independent (↑AddSubgroup.toIntSubmodule ∘ p)
  exact independent_of_dfinsupp_lsum_injective _ h
  -- 🎉 no goals
#align complete_lattice.independent_of_dfinsupp_sum_add_hom_injective' CompleteLattice.independent_of_dfinsupp_sumAddHom_injective'

/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `CompleteLattice.Independent`.

Note that this is not generally true for `[Semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `Counterexamples/DirectSumIsInternal.lean` for a proof of this fact. -/
theorem Independent.dfinsupp_lsum_injective {p : ι → Submodule R N} (h : Independent p) :
    Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) := by
  -- simplify everything down to binders over equalities in `N`
  rw [independent_iff_forall_dfinsupp] at h
  -- ⊢ Function.Injective ↑(↑(lsum ℕ) fun i => Submodule.subtype (p i))
  suffices LinearMap.ker (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    letI thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  -- ⊢ ∀ (m : Π₀ (i : ι), { x // x ∈ p i }), ↑(↑(lsum ℕ) fun i => Submodule.subtype …
  intro m hm
  -- ⊢ m = 0
  ext i : 1
  -- ⊢ ↑m i = ↑0 i
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [DFinsupp.zero_apply, ← neg_eq_zero]
  -- ⊢ -↑m i = 0
  refine' h i (-m i) m _
  -- ⊢ ↑(↑(lsum ℕ) fun i => Submodule.subtype (p i)) (erase i m) = ↑(-↑m i)
  rwa [← erase_add_single i m, LinearMap.map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm
#align complete_lattice.independent.dfinsupp_lsum_injective CompleteLattice.Independent.dfinsupp_lsum_injective

/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `CompleteLattice.Independent`. -/
theorem Independent.dfinsupp_sumAddHom_injective {p : ι → AddSubgroup N} (h : Independent p) :
    Function.Injective (sumAddHom fun i => (p i).subtype) := by
  rw [← independent_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  -- ⊢ Function.Injective ↑(sumAddHom fun i => AddSubgroup.subtype (p i))
  exact h.dfinsupp_lsum_injective
  -- 🎉 no goals
#align complete_lattice.independent.dfinsupp_sum_add_hom_injective CompleteLattice.Independent.dfinsupp_sumAddHom_injective

/-- A family of submodules over an additive group are independent if and only iff `DFinsupp.lsum`
applied with `Submodule.subtype` is injective.

Note that this is not generally true for `[Semiring R]`; see
`CompleteLattice.Independent.dfinsupp_lsum_injective` for details. -/
theorem independent_iff_dfinsupp_lsum_injective (p : ι → Submodule R N) :
    Independent p ↔ Function.Injective (lsum ℕ (M := fun i ↦ ↥(p i)) fun i => (p i).subtype) :=
  ⟨Independent.dfinsupp_lsum_injective, independent_of_dfinsupp_lsum_injective p⟩
#align complete_lattice.independent_iff_dfinsupp_lsum_injective CompleteLattice.independent_iff_dfinsupp_lsum_injective

/-- A family of additive subgroups over an additive group are independent if and only if
`DFinsupp.sumAddHom` applied with `AddSubgroup.subtype` is injective. -/
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
  -- ⊢ LinearIndependent R v
  let _ := Classical.decEq R
  -- ⊢ LinearIndependent R v
  rw [linearIndependent_iff]
  -- ⊢ ∀ (l : ι →₀ R), ↑(Finsupp.total ι N R v) l = 0 → l = 0
  intro l hl
  -- ⊢ l = 0
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext i
  -- ⊢ ↑l i = ↑0 i
  apply smul_left_injective R (hv' i)
  -- ⊢ (fun c => c • v i) (↑l i) = (fun c => c • v i) (↑0 i)
  have : l i • v i = a i := rfl
  -- ⊢ (fun c => c • v i) (↑l i) = (fun c => c • v i) (↑0 i)
  simp only [coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, smul_eq_zero, ha] at this
  -- ⊢ (fun c => c • v i) (↑l i) = (fun c => c • v i) (↑0 i)
  simpa
  -- 🎉 no goals
#align complete_lattice.independent.linear_independent CompleteLattice.Independent.linearIndependent

theorem independent_iff_linearIndependent_of_ne_zero [NoZeroSMulDivisors R N] {v : ι → N}
    (h_ne_zero : ∀ i, v i ≠ 0) : (Independent fun i => R ∙ v i) ↔ LinearIndependent R v :=
  let _ := Classical.decEq ι
  ⟨fun hv => hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero,
    fun hv => hv.independent_span_singleton⟩
#align complete_lattice.independent_iff_linear_independent_of_ne_zero CompleteLattice.independent_iff_linearIndependent_of_ne_zero

end Ring

end CompleteLattice
