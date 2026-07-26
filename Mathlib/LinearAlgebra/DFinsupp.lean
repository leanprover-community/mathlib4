/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Submonoid
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Mathlib/Data/DFinsupp/Module.lean`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.mk` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`.

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

open Module

variable {ι ι' : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

namespace DFinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [AddCommMonoid N] [Module R N]

section DecidableEq
variable [DecidableEq ι]

/-- `DFinsupp.mk` as a `LinearMap`. -/
def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x

/-- `DFinsupp.single` as a `LinearMap` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After applying this lemma, if `M = R` then it suffices to verify
`φ (single a 1) = ψ (single a 1)`. -/
@[ext 1100]
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)

theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl

@[simp]
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) →ₗ[R] _) x = single i x :=
  rfl

end DecidableEq

/-- Interpret `fun (f : Π₀ i, M i) ↦ f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i

@[simp]
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) →ₗ[R] _) f = f i :=
  rfl

theorem injective_pi_lapply : Function.Injective (LinearMap.pi (R := R) <| lapply (M := M)) :=
  fun _ _ h ↦ ext fun _ ↦ congr_fun h _

@[simp]
theorem lapply_comp_lsingle_same [DecidableEq ι] (i : ι) :
    lapply i ∘ₗ lsingle i = (.id : M i →ₗ[R] M i) := by ext; simp

@[simp]
theorem lapply_comp_lsingle_of_ne [DecidableEq ι] (i i' : ι) (h : i ≠ i') :
    lapply i ∘ₗ lsingle i' = (0 : M i' →ₗ[R] M i) := by ext; simp [h.symm]

section Lsum

variable (S)
variable [DecidableEq ι]

instance {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] :
    EquivLike (LinearEquiv σ M M₂) M M₂ :=
  inferInstance

/-- `DFinsupp.equivCongrLeft` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.domLCongr`. -/
@[simps! apply]
def domLCongr (e : ι ≃ ι') : (Π₀ i, M i) ≃ₗ[R] (Π₀ i, M (e.symm i)) where
  __ := DFinsupp.equivCongrLeft e
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.sigmaCurryEquiv` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.curryLinearEquiv`. -/
@[simps! apply symm_apply]
def sigmaCurryLEquiv {α : ι → Type*} {M : (i : ι) → α i → Type*}
    [Π i j, AddCommMonoid (M i j)] [Π i j, Module R (M i j)] :
    (Π₀ (i : (x : ι) × α x), M i.fst i.snd) ≃ₗ[R] Π₀ (i : ι) (j : α i), M i j where
  __ := DFinsupp.sigmaCurryEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.equivFunOnFintype` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.linearEquivFunOnFintype`. -/
@[simps! apply symm_apply]
def linearEquivFunOnFintype [Fintype ι] : (Π₀ i, M i) ≃ₗ[R] (Π i, M i) where
  __ := equivFunOnFintype
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `DFinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, map_zero, smul_zero]
        · intro a b f _ _ hf
          rw [smul_add, map_add, map_add, smul_add, hf, ← single_smul,
            sumAddHom_single, sumAddHom_single, LinearMap.toAddMonoidHom_coe,
            map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    simp
  right_inv F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_add' F G := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_smul' c F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp

/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sumAddHom`
with `DFinsupp.lsum_apply_apply`. -/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : ∀ i, M i →ₗ[R] N) (i)
    (x : M i) : lsum S F (single i x) = F i x := by
  simp

theorem lsum_lsingle [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    lsum S (lsingle (R := R) (M := M)) = .id :=
  lhom_ext (lsum_single _ _)

theorem iSup_range_lsingle : ⨆ i, LinearMap.range (lsingle (R := R) (M := M) i) = ⊤ :=
  top_le_iff.mp fun m _ ↦ by
    rw [← LinearMap.id_apply (R := R) m, ← lsum_lsingle ℕ]
    exact dfinsuppSumAddHom_mem _ _ _ fun i _ ↦ Submodule.mem_iSup_of_mem i ⟨_, rfl⟩

end Lsum

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/

section mapRange
variable {β β₁ β₂ : ι → Type*}

section AddCommMonoid
variable [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (β₁ i)] [∀ i, AddCommMonoid (β₂ i)]
variable [∀ i, Module R (β i)] [∀ i, Module R (β₁ i)] [∀ i, Module R (β₂ i)]

set_option backward.isDefEq.respectTransparency false in
lemma mker_mapRangeAddMonoidHom (f : ∀ i, β₁ i →+ β₂ i) :
    AddMonoidHom.mker (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mker (f i))).comap coeFnAddMonoidHom := by
  ext
  simp [AddSubmonoid.pi, DFinsupp.ext_iff]

lemma mrange_mapRangeAddMonoidHom (f : ∀ i, β₁ i →+ β₂ i) :
    AddMonoidHom.mrange (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mrange (f i))).comap coeFnAddMonoidHom := by
  classical
  ext x
  simp only [AddSubmonoid.mem_comap, coeFnAddMonoidHom_apply]
  refine ⟨fun ⟨y, hy⟩ i hi ↦ ?_, fun h ↦ ?_⟩
  · simp [← hy]
  · choose g hg using fun i => h i (Set.mem_univ _)
    use DFinsupp.mk x.support (g ·)
    ext i
    simp only [Finset.coe_sort_coe, mapRange.addMonoidHom_apply, mapRange_apply]
    by_cases mem : i ∈ x.support
    · rw [mk_of_mem mem, hg]
    · rw [DFinsupp.notMem_support_iff.mp mem, mk_of_notMem mem, map_zero]

theorem mapRange_smul (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (r : R)
    (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g := by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']

/-- `DFinsupp.mapRange` as a `LinearMap`. -/
@[simps! apply]
def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i →ₗ[R] _)) = LinearMap.id := by
  ext
  simp [linearMap]

theorem mapRange.linearMap_comp (f : ∀ i, β₁ i →ₗ[R] β₂ i) (f₂ : ∀ i, β i →ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)

theorem sum_mapRange_index.linearMap [DecidableEq ι] {f : ∀ i, β₁ i →ₗ[R] β₂ i}
    {h : ∀ i, β₂ i →ₗ[R] N} {l : Π₀ i, β₁ i} :
    DFinsupp.lsum ℕ h (mapRange.linearMap f l) = DFinsupp.lsum ℕ (fun i => (h i).comp (f i)) l := by
  classical simpa [DFinsupp.sumAddHom_apply] using! sum_mapRange_index fun i => by simp

lemma ker_mapRangeLinearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) :
    LinearMap.ker (mapRange.linearMap f) =
      (Submodule.pi Set.univ (fun i ↦ LinearMap.ker (f i))).comap (coeFnLinearMap R) :=
  Submodule.toAddSubmonoid_injective <| mker_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

lemma range_mapRangeLinearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) :
    LinearMap.range (mapRange.linearMap f) =
      (Submodule.pi Set.univ (LinearMap.range <| f ·)).comap (coeFnLinearMap R) :=
  Submodule.toAddSubmonoid_injective <| mrange_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

/-- `DFinsupp.mapRange.linearMap` as a `LinearEquiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }

@[simp]
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id

theorem mapRange.linearEquiv_trans (f : ∀ i, β i ≃ₗ[R] β₁ i) (f₂ : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)

@[simp]
theorem mapRange.linearEquiv_symm (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl

end AddCommMonoid

section AddCommGroup

lemma ker_mapRangeAddMonoidHom
    [∀ i, AddCommGroup (β₁ i)] [∀ i, AddCommMonoid (β₂ i)] (f : ∀ i, β₁ i →+ β₂ i) :
    (mapRange.addMonoidHom f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap coeFnAddMonoidHom :=
  AddSubgroup.toAddSubmonoid_injective <| mker_mapRangeAddMonoidHom f

lemma range_mapRangeAddMonoidHom
    [∀ i, AddCommGroup (β₁ i)] [∀ i, AddCommGroup (β₂ i)] (f : ∀ i, β₂ i →+ β₁ i) :
    (mapRange.addMonoidHom f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap coeFnAddMonoidHom :=
  AddSubgroup.toAddSubmonoid_injective <| mrange_mapRangeAddMonoidHom f

end AddCommGroup

end mapRange

section CoprodMap

variable [DecidableEq ι]

/-- Given a family of linear maps `f i : M i →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `LinearMap.coprod` for the binary product version. -/
def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (DFinsupp.lsum ℕ fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f

theorem coprodMap_apply [∀ x : N, Decidable (x ≠ 0)] (f : ∀ i : ι, M i →ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      DFinsupp.sum (mapRange (fun i => f i) (fun _ => map_zero _) x) fun _ =>
        id :=
  DFinsupp.sumAddHom_apply _ _

theorem coprodMap_apply_single (f : ∀ i : ι, M i →ₗ[R] N) (i : ι) (x : M i) :
    coprodMap f (single i x) = f i x := by
  simp [coprodMap]

end CoprodMap

end DFinsupp

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open DFinsupp

section DecidableEq

variable [DecidableEq ι]

theorem dfinsuppSum_mem {β : ι → Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : ∀ i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    f.sum g ∈ S :=
  _root_.dfinsuppSum_mem S f g h

theorem dfinsuppSumAddHom_mem {β : ι → Type*} [∀ i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    DFinsupp.sumAddHom g f ∈ S :=
  _root_.dfinsuppSumAddHom_mem S f g h

/-- The supremum of a family of submodules is equal to the range of `DFinsupp.lsum`; that is
every element in the `iSup` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
theorem iSup_eq_range_dfinsupp_lsum (p : ι → Submodule R N) :
    iSup p = LinearMap.range (DFinsupp.lsum ℕ fun i => (p i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i ≤ _) (v i).2

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem biSup_eq_range_dfinsupp_lsum (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range
        (LinearMap.comp
          (DFinsupp.lsum ℕ (fun i => (S i).subtype))
            (DFinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply, filterLinearMap_apply, filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]

/-- A characterisation of the span of a family of submodules.

See also `Submodule.mem_iSup_iff_exists_finsupp`. -/
theorem mem_iSup_iff_exists_dfinsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔
      ∃ f : Π₀ i, p i, DFinsupp.lsum ℕ (fun i => (p i).subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x

/-- A variant of `Submodule.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded.

See also `Submodule.mem_iSup_iff_exists_finsupp`. -/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι → Submodule R N) [∀ (i) (x : p i), Decidable (x ≠ 0)]
    (x : N) : x ∈ iSup p ↔ ∃ f : Π₀ i, p i, (f.sum fun _ xi => ↑xi) = x := by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coe_subtype]

theorem mem_biSup_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i,
        DFinsupp.lsum ℕ (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x

end DecidableEq

lemma mem_iSup_iff_exists_finsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔ ∃ (f : ι →₀ N), (∀ i, f i ∈ p i) ∧ (f.sum fun _i xi ↦ xi) = x := by
  classical
  rw [mem_iSup_iff_exists_dfinsupp']
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨⟨f.support, fun i ↦ (f i : N), by simp⟩, by simp, hf⟩, ?_⟩
  rintro ⟨f, hf, rfl⟩
  refine ⟨DFinsupp.mk f.support fun i ↦ ⟨f i, hf i⟩, Finset.sum_congr ?_ fun i hi ↦ ?_⟩
  · ext; simp [mk_eq_zero]
  · simp [Finsupp.mem_support_iff.mp hi]

theorem mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι → Submodule R N) (a : N) :
    (a ∈ ⨆ i ∈ s, p i) ↔ ∃ μ : ∀ i, p i, (∑ i ∈ s, (μ i : N)) = a := by
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
        suffices ⊥ = ⨆ (_ : x ∈ s), p x from this.symm ▸ coe_mem (μ x)
        exact (iSup_neg hx).symm
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
    · refine ⟨DFinsupp.mk s ?_, ?_⟩
      · rintro ⟨i, hi⟩
        refine ⟨μ i, ?_⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [DFinsupp.sum]
      rw [Finset.sum_subset support_mk_subset, ← hμ]
      · exact Finset.sum_congr rfl fun x hx => by rw [mk_of_mem hx]
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl

end Submodule

open DFinsupp

section Semiring

variable [DecidableEq ι] [Semiring R] [AddCommMonoid N] [Module R N]

/-- Independence of a family of submodules can be expressed as a quantifier over `DFinsupp`s.

This is an intermediate result used to prove
`iSupIndep_of_dfinsupp_lsum_injective` and
`iSupIndep.dfinsupp_lsum_injective`. -/
theorem iSupIndep_iff_forall_dfinsupp (p : ι → Submodule R N) :
    iSupIndep p ↔
      ∀ (i) (x : p i) (v : Π₀ i : ι, ↥(p i)),
        lsum ℕ (fun i => (p i).subtype) (erase i v) = x → x = 0 := by
  simp_rw [iSupIndep_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine forall_congr' fun i => Subtype.forall'.trans ?_
  simp_rw [Submodule.coe_eq_zero]

/-- If `DFinsupp.lsum` applied with `Submodule.subtype` is injective then the submodules are
iSupIndep. -/
theorem iSupIndep_of_dfinsupp_lsum_injective (p : ι → Submodule R N)
    (h : Function.Injective (lsum ℕ fun i => (p i).subtype)) :
    iSupIndep p := by
  rw [iSupIndep_iff_forall_dfinsupp]
  intro i x v hv
  replace hv : lsum ℕ (fun i => (p i).subtype) (erase i v) =
      lsum ℕ (fun i => (p i).subtype) (single i x) := by
    simpa only [lsum_single] using! hv
  have := DFunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using! this

/-- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
submonoids are independent. -/
theorem iSupIndep_of_dfinsuppSumAddHom_injective (p : ι → AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/-- Combining `DFinsupp.lsum` with `LinearMap.toSpanSingleton` is the same as
`Finsupp.linearCombination` -/
theorem lsum_comp_mapRange_toSpanSingleton [∀ m : R, Decidable (m ≠ 0)] (p : ι → Submodule R N)
    {v : ι → N} (hv : ∀ i : ι, v i ∈ p i) :
    (lsum ℕ fun i => (p i).subtype : _ →ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ →ₗ[R] _).comp
          (finsuppLequivDFinsupp R : (ι →₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.linearCombination R v := by
  ext
  simp

end Semiring

section Ring

variable [DecidableEq ι] [Ring R] [AddCommGroup N] [Module R N]

/-- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
subgroups are independent. -/
theorem iSupIndep_of_dfinsuppSumAddHom_injective' (p : ι → AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `iSupIndep`.

Note that this is not generally true for `[Semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `Counterexamples/DirectSumIsInternal.lean` for a proof of this fact. -/
theorem iSupIndep.dfinsupp_lsum_injective {p : ι → Submodule R N} (h : iSupIndep p) :
    Function.Injective (lsum ℕ fun i => (p i).subtype) := by
  -- simplify everything down to binders over equalities in `N`
  rw [iSupIndep_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum ℕ fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    let thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  intro m hm
  ext i : 1
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [DFinsupp.zero_apply, ← neg_eq_zero]
  refine h i (-m i) m ?_
  rwa [← erase_add_single i m, map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm

/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `iSupIndep`. -/
theorem iSupIndep.dfinsuppSumAddHom_injective {p : ι → AddSubgroup N} (h : iSupIndep p) :
    Function.Injective (sumAddHom fun i => (p i).subtype) := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective

/-- A family of submodules over an additive group are independent if and only iff `DFinsupp.lsum`
applied with `Submodule.subtype` is injective.

Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details. -/
theorem iSupIndep_iff_dfinsupp_lsum_injective (p : ι → Submodule R N) :
    iSupIndep p ↔ Function.Injective (lsum ℕ fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective p⟩

omit [DecidableEq ι] in
theorem iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (p : ι → Submodule R N) :
    iSupIndep p ↔ ∀ (s : Finset ι) (v : ι → N),
    (∀ i ∈ s, v i ∈ p i) → (∑ i ∈ s, v i = 0) → ∀ i ∈ s, v i = 0 := by
  classical
  simp_rw [iSupIndep_def, Submodule.disjoint_def]
  constructor
  · intro h s v hv hv0 i hi
    apply h _ _ (hv i hi)
    rw [← s.add_sum_erase _ hi, add_eq_zero_iff_neg_eq] at hv0
    rw [← Submodule.neg_mem_iff, hv0]
    exact SetLike.le_def.mp (biSup_mono <| by grind) (Submodule.sum_mem_biSup <| by grind)
  · intro h i x hx hsup
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp ..).mp hsup
    contrapose! h
    use insert i f.support, fun j ↦ if j = i then -f.sum fun _ x ↦ x else f j
    refine ⟨fun j hj ↦ ?_, ?_, by grind⟩
    · beta_reduce
      split_ifs with h
      · exact (p j).neg_mem (h ▸ hx)
      · simpa [h] using hf j
    · specialize hf i
      simp at hf
      grind [Finsupp.sum, Finset.sum_congr]

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero := iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero

omit [DecidableEq ι] in
theorem iSupIndep_iff_finsetSum_eq_imp_eq (p : ι → Submodule R N) :
    iSupIndep p ↔ ∀ (s : Finset ι) (v w : ι → N),
    (∀ i ∈ s, v i ∈ p i ∧ w i ∈ p i) → (∑ i ∈ s, v i = ∑ i ∈ s, w i) → ∀ i ∈ s, v i = w i := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  constructor
  · intro h s v w hvw
    simpa [sub_eq_zero] using h s (v - w) fun i hi => (p i).sub_mem (hvw i hi).1 (hvw i hi).2
  · intro h s v hv hv0
    specialize h s v 0
    simp_all

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_imp_eq := iSupIndep_iff_finsetSum_eq_imp_eq

/-- A family of additive subgroups over an additive group are independent if and only if
`DFinsupp.sumAddHom` applied with `AddSubgroup.subtype` is injective. -/
theorem iSupIndep_iff_dfinsuppSumAddHom_injective (p : ι → AddSubgroup N) :
    iSupIndep p ↔ Function.Injective (sumAddHom fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective' p⟩

/-- If `(pᵢ)ᵢ` is a family of independent submodules that generates the whole module `N`, then
`N` is isomorphic to the direct sum of the submodules. -/
@[simps! apply] noncomputable def iSupIndep.linearEquiv {p : ι → Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) : (Π₀ i, p i) ≃ₗ[R] N :=
  .ofBijective _ ⟨ind.dfinsupp_lsum_injective, by
    rwa [← LinearMap.range_eq_top, ← Submodule.iSup_eq_range_dfinsupp_lsum]⟩

set_option backward.isDefEq.respectTransparency false in
theorem iSupIndep.linearEquiv_symm_apply {p : ι → Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) {i : ι} {x : N} (h : x ∈ p i) :
    (ind.linearEquiv iSup_top).symm x = .single i ⟨x, h⟩ := by
  simp [← LinearEquiv.eq_symm_apply, iSupIndep.linearEquiv]

/-- If a family of submodules is independent, then a choice of nonzero vector from each submodule
forms a linearly independent family.

See also `iSupIndep.linearIndependent'`. -/
theorem iSupIndep.linearIndependent [IsDomain R] [IsTorsionFree R N] {ι : Type*}
    (p : ι → Submodule R N) (hp : iSupIndep p) {v : ι → N} (hv : ∀ i, v i ∈ p i)
    (hv' : ∀ i, v i ≠ 0) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext i
  apply smul_left_injective R (hv' i)
  have : l i • v i = a i := rfl
  simp only [coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, smul_eq_zero, ha] at this
  simpa

theorem iSupIndep_iff_linearIndependent_of_ne_zero [IsDomain R] [IsTorsionFree R N]
    {ι : Type*} {v : ι → N} (h_ne_zero : ∀ i, v i ≠ 0) :
    iSupIndep (R ∙ v ·) ↔ LinearIndependent R v where
  mp hv := hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero
  mpr hv := hv.iSupIndep_span_singleton

end Ring

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}
variable {ι : Type*}
variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {σ₁₂ : R →+* R₂}
variable [Module R M] [Module R₂ M₂]

open Submodule

section DFinsupp

open DFinsupp

variable {γ : ι → Type*} [DecidableEq ι]

section Sum

variable [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)]

theorem coe_dfinsuppSum (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
theorem dfinsuppSum_apply (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Sum

section SumAddHom

variable [∀ i, AddZeroClass (γ i)]

@[simp]
theorem map_dfinsuppSumAddHom (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i →+ M} :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)) t :=
  f.toAddMonoidHom.map_dfinsuppSumAddHom _ _

end SumAddHom

end DFinsupp

end AddCommMonoid

end LinearMap

namespace LinearEquiv

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}

section DFinsupp

open DFinsupp

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable {γ : ι → Type*} [DecidableEq ι]

@[simp]
theorem map_dfinsuppSumAddHom [∀ i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
    (g : ∀ i, γ i →+ M) :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddEquiv.toAddMonoidHom.comp (g i)) t :=
  f.toAddEquiv.map_dfinsuppSumAddHom _ _

end DFinsupp

end LinearEquiv
