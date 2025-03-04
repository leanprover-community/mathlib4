/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Restricted products of sets, groups and rings

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open Set Topology Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))
variable (R' : ι → Type*) (A' : (i : ι) → Set (R' i))

def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // ∀ᶠ i in 𝓕, x i ∈ A i}

open Batteries.ExtendedBinder

scoped[RestrictedProduct]
notation3 "Πʳ "(...)", ""["r:(scoped R => R)", "a:(scoped A => A)"]_[" f "]" =>
  RestrictedProduct r a f

scoped[RestrictedProduct]
notation3"Πʳ "(...)", ""["r:(scoped R => R)", "a:(scoped A => A)"]" =>
  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι} {S T : Set ι}

instance : DFunLike (Πʳ i, [R i, A i]_[𝓕]) ι R where
  coe x i := x.1 i
  coe_injective' _ _ := Subtype.ext

lemma range_coe :
    range ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) = {x | ∀ᶠ i in 𝓕, x i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2) (fun x hx ↦ mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)

lemma range_coe_principal :
    range ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) = S.pi A :=
  range_coe R A

variable (𝓕) in
def structureMap (x : Π i, A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨fun i ↦ x i, .of_forall fun i ↦ (x i).2⟩

def inclusion (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, A i]_[𝓖]) :
    Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, x.2.filter_mono h⟩

variable (𝓕) in
lemma inclusion_eq_id : inclusion R A (le_refl 𝓕) = id := rfl

lemma exists_inclusion_eq_of_eventually (h : 𝓕 ≤ 𝓖) {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx𝓖 : ∀ᶠ i in 𝓖, x i ∈ A i) :
    ∃ x' : Πʳ i, [R i, A i]_[𝓖], inclusion R A h x' = x :=
  ⟨⟨x.1, hx𝓖⟩, rfl⟩

lemma exists_structureMap_eq_of_forall {x : Πʳ i, [R i, A i]_[𝓕]}
    (hx : ∀ i, x.1 i ∈ A i) :
    ∃ x' : Π i, A i, structureMap R A 𝓕 x' = x :=
  ⟨fun i ↦ ⟨x i, hx i⟩, rfl⟩

lemma range_inclusion (h : 𝓕 ≤ 𝓖) :
    Set.range (inclusion R A h) = {x | ∀ᶠ i in 𝓖, x i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2)
    (fun _ hx ↦ mem_range.mpr <| exists_inclusion_eq_of_eventually R A h hx)

lemma range_structureMap :
    Set.range (structureMap R A 𝓕) = {f | ∀ i, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i ↦ (x i).2)
    (fun _ hx ↦ mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

section Algebra

variable {S S' : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (R i)] [Π i, SetLike (S' i) (R' i)]
variable {A : Π i, S i} {A' : Π i, S' i}
variable {𝓕 : Filter ι}

@[to_additive]
instance [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] : One (Πʳ i, [R i, A i]_[𝓕]) where
  one := ⟨fun _ ↦ 1, .of_forall fun _ ↦ one_mem _⟩

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (Πʳ i, [R i, A i]_[𝓕]) where
  inv x := ⟨fun i ↦ (x i)⁻¹, x.2.mono fun _ ↦ inv_mem⟩

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (Πʳ i, [R i, A i]_[𝓕]) where
  mul x y := ⟨fun i ↦ x i * y i, y.2.mp (x.2.mono fun _ ↦ mul_mem)⟩

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (Πʳ i, [R i, A i]_[𝓕]) where
  smul g x := ⟨fun i ↦ g • (x i), x.2.mono fun _ ↦ SMulMemClass.smul_mem g⟩

@[to_additive]
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (Πʳ i, [R i, A i]_[𝓕]) where
  div x y := ⟨fun i ↦ x i / y i, y.2.mp (x.2.mono fun _ ↦ div_mem)⟩

instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (Πʳ i, [R i, A i]_[𝓕]) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ pow_mem hi n⟩

instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (Πʳ i, [R i, A i]_[𝓕]) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ zpow_mem hi n⟩

instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Πʳ i, [R i, A i]_[𝓕]) where
  natCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ natCast_mem _ n⟩

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (Πʳ i, [R i, A i]_[𝓕]) where
  intCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ intCast_mem _ n⟩

instance [Π i, AddGroup (R i)] [∀ i, AddSubgroupClass (S i) (R i)] :
    AddGroup (Πʳ i, [R i, A i]_[𝓕]) :=
  haveI : ∀ i, SMulMemClass (S i) ℤ (R i) := fun _ ↦ AddSubgroupClass.zsmulMemClass
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (Πʳ i, [R i, A i]_[𝓕]) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (Πʳ i, [R i, A i]_[𝓕]) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Algebra

section Topology

variable {R A R' A'}
variable {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)] [∀ i, TopologicalSpace (R' i)]

variable (R A 𝓕) in
instance topologicalSpace : TopologicalSpace (Πʳ i, [R i, A i]_[𝓕]) :=
  ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), .coinduced (inclusion R A hS)
    (.induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance)

theorem continuous_coe :
    Continuous ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) :=
  continuous_iSup_dom.mpr fun _ ↦ continuous_iSup_dom.mpr fun _ ↦
    continuous_coinduced_dom.mpr continuous_induced_dom

theorem continuous_inclusion {𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Continuous (inclusion R A h) := by
  simp_rw [continuous_iff_coinduced_le, topologicalSpace, coinduced_iSup, coinduced_compose]
  exact iSup₂_le fun S hS ↦ le_iSup₂_of_le S (le_trans h hS) le_rfl

section principal

variable {S : Set ι}

theorem topologicalSpace_eq_of_principal :
    topologicalSpace R A (𝓟 S) =
      .induced ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) inferInstance :=
  le_antisymm (continuous_iff_le_induced.mp continuous_coe) <|
    (le_iSup₂_of_le S le_rfl <| by rw [inclusion_eq_id R A (𝓟 S), @coinduced_id])

theorem topologicalSpace_eq_of_top :
    topologicalSpace R A ⊤ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) inferInstance :=
  principal_univ ▸ topologicalSpace_eq_of_principal

theorem topologicalSpace_eq_of_bot :
    topologicalSpace R A ⊥ =
      .induced ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) inferInstance :=
  principal_empty ▸ topologicalSpace_eq_of_principal

theorem isInducing_coe_of_principal :
    IsInducing ((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) where
  eq_induced := topologicalSpace_eq_of_principal

theorem isInducing_coe_of_top :
    IsInducing ((↑) : Πʳ i, [R i, A i]_[⊤] → Π i, R i) :=
  principal_univ ▸ isInducing_coe_of_principal

theorem isInducing_coe_of_bot :
    IsInducing ((↑) : Πʳ i, [R i, A i]_[⊥] → Π i, R i) :=
  principal_empty ▸ isInducing_coe_of_principal

theorem continuous_rng_of_principal {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[𝓟 S]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isInducing_coe_of_principal.continuous_iff

theorem continuous_rng_of_top {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊤]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isInducing_coe_of_top.continuous_iff

theorem continuous_rng_of_bot {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ i, [R i, A i]_[⊥]} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  isInducing_coe_of_bot.continuous_iff

def homeoTop : (Π i, A i) ≃ₜ (Πʳ i, [R i, A i]_[⊤]) where
  toFun f := ⟨fun i ↦ f i, fun i ↦ (f i).2⟩
  invFun f i := ⟨f i, f.2 i⟩
  continuous_toFun := continuous_rng_of_top.mpr <| continuous_pi fun i ↦
      continuous_subtype_val.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ continuous_induced_rng.mpr <|
    (continuous_apply i).comp continuous_coe
  left_inv _ := rfl
  right_inv _ := rfl

def homeoBot : (Π i, R i) ≃ₜ (Πʳ i, [R i, A i]_[⊥]) where
  toFun f := ⟨fun i ↦ f i, eventually_bot⟩
  invFun f i := f i
  continuous_toFun := continuous_rng_of_bot.mpr <| continuous_pi fun i ↦ continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ (continuous_apply i).comp continuous_coe
  left_inv _ := rfl
  right_inv _ := rfl

instance [hS : Fact (cofinite ≤ 𝓟 S)]
    [∀ i, WeaklyLocallyCompactSpace (R i)] [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]_[𝓟 S]) where
  exists_compact_mem_nhds := fun x ↦ by
    have hS := hS.out
    rw [le_principal_iff, mem_cofinite] at hS
    classical
    have : ∀ i, ∃ K, IsCompact K ∧ K ∈ 𝓝 (x i) := fun i ↦ exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i ↦ if i ∈ S then A i else K i) with Q_def
    have Q_compact : IsCompact Q := isCompact_univ_pi fun i ↦ by
      split_ifs
      · exact isCompact_iff_compactSpace.mpr inferInstance
      · exact K_compact i
    set U : Set (Π i, R i) := Sᶜ.pi K with U_def
    have U_nhds : U ∈ 𝓝 (x : Π i, R i) := set_pi_mem_nhds hS fun i _ ↦ hK i
    have QU : (↑) ⁻¹' U ⊆ ((↑) ⁻¹' Q : Set (Πʳ i, [R i, A i]_[𝓟 S])) := fun y H i _ ↦ by
      dsimp only
      split_ifs with hi
      · exact y.2 hi
      · exact H i hi
    refine ⟨((↑) ⁻¹' Q), ?_, mem_of_superset ?_ QU⟩
    · refine isInducing_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr Q_compact
      simp_rw [range_coe_principal, Q_def, pi_if, mem_univ, true_and]
      exact inter_subset_left
    · simpa only [isInducing_coe_of_principal.nhds_eq_comap] using preimage_mem_comap U_nhds

end principal

section general

variable (𝓕) in
theorem topologicalSpace_eq_iSup :
    topologicalSpace R A 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
      .coinduced (inclusion R A hS) (topologicalSpace R A (𝓟 S)) := by
  simp_rw [topologicalSpace_eq_of_principal, topologicalSpace]

theorem continuous_dom {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i]_[𝓕] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), Continuous (f ∘ inclusion R A hS) := by
  simp_rw [topologicalSpace_eq_of_principal, continuous_iSup_dom, continuous_coinduced_dom]

theorem isInducing_inclusion_principal {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    IsInducing (inclusion R A hS) :=
  .of_comp (continuous_inclusion hS) continuous_coe isInducing_coe_of_principal

theorem isInducing_inclusion_top :
    IsInducing (inclusion R A (le_top : 𝓕 ≤ ⊤)) :=
  .of_comp (continuous_inclusion _) continuous_coe isInducing_coe_of_top

theorem isEmbedding_inclusion_principal {S : Set ι} (hS : 𝓕 ≤ 𝓟 S) :
    IsEmbedding (inclusion R A hS) where
  toIsInducing := isInducing_inclusion_principal hS
  injective _ _ h := DFunLike.ext _ _ (fun i ↦ DFunLike.congr_fun h i)

theorem isEmbedding_inclusion_top :
    IsEmbedding (inclusion R A (le_top : 𝓕 ≤ ⊤)) where
  toIsInducing := isInducing_inclusion_top
  injective _ _ h := DFunLike.ext _ _ (fun i ↦ DFunLike.congr_fun h i)

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem isInducing_structureMap :
    IsInducing (structureMap R A 𝓕) :=
  isInducing_inclusion_top.comp homeoTop.isInducing

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem isEmbedding_structureMap :
    IsEmbedding (structureMap R A 𝓕) :=
  isEmbedding_inclusion_top.comp homeoTop.isEmbedding

end general

section cofinite

variable (hAopen : ∀ i, IsOpen (A i)) (hAopen' : ∀ i, IsOpen (A' i))

include hAopen in
theorem isOpen_forall_imp_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, p i → f.1 i ∈ A i} := by
  rw [le_principal_iff] at hS
  convert isOpen_set_pi (hS.inter_of_left {i | p i}) (fun i _ ↦ hAopen i) |>.preimage continuous_coe
  ext f
  refine ⟨fun H i hi ↦ H i hi.2, fun H i hiT ↦ ?_⟩
  by_cases hiS : i ∈ S
  · exact f.2 hiS
  · exact H i ⟨hiS, hiT⟩

include hAopen in
theorem isOpen_forall_mem_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpen {f : Πʳ i, [R i, A i]_[𝓟 S] | ∀ i, f.1 i ∈ A i} := by
  convert isOpen_forall_imp_mem_of_principal hAopen hS (p := fun _ ↦ True)
  simp

include hAopen in
theorem isOpen_forall_imp_mem {p : ι → Prop} :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, p i → f.1 i ∈ A i} := by
  simp_rw [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_imp_mem_of_principal hAopen hS

include hAopen in
theorem isOpen_forall_mem :
    IsOpen {f : Πʳ i, [R i, A i] | ∀ i, f.1 i ∈ A i} := by
  simp_rw [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ isOpen_forall_mem_of_principal hAopen hS

include hAopen in
theorem isOpenEmbedding_inclusion_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) :
    IsOpenEmbedding (inclusion R A hS) where
  toIsEmbedding := isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [range_inclusion]
    exact isOpen_forall_imp_mem hAopen

include hAopen in
/-- `Π i, A i` is homeomorphic to an open subset of the restricted product. -/
theorem isOpenEmbedding_structureMap :
    IsOpenEmbedding (structureMap R A cofinite) where
  toIsEmbedding := isEmbedding_structureMap
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem hAopen

include hAopen in
theorem nhds_eq_map_inclusion {S : Set ι} (hS : cofinite ≤ 𝓟 S)
    (x : Πʳ i, [R i, A i]_[𝓟 S]) :
    (𝓝 (inclusion R A hS x)) = map (inclusion R A hS) (𝓝 x) := by
  rw [isOpenEmbedding_inclusion_principal hAopen hS |>.map_nhds_eq x]

include hAopen in
theorem nhds_eq_map_structureMap
    (x : Π i, A i) :
    (𝓝 (structureMap R A cofinite x)) = map (structureMap R A cofinite) (𝓝 x) := by
  rw [isOpenEmbedding_structureMap hAopen |>.map_nhds_eq x]

instance [hAopen : Fact (∀ i, IsOpen (A i))] [∀ i, WeaklyLocallyCompactSpace (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Πʳ i, [R i, A i]) where
  exists_compact_mem_nhds := fun x ↦ by
    set S := {i | x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
    haveI : Fact (cofinite ≤ 𝓟 S) := ⟨hS⟩
    have hSx : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
    rcases exists_inclusion_eq_of_eventually R A hS hSx with ⟨x', hxx'⟩
    rw [← hxx', nhds_eq_map_inclusion hAopen.out]
    rcases exists_compact_mem_nhds x' with ⟨K, K_compact, hK⟩
    exact ⟨inclusion R A hS '' K, K_compact.image (continuous_inclusion hS), image_mem_map hK⟩

-- The key result for continuity of multiplication and addition
include hAopen in
theorem continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Πʳ i, [R i, A i] × Y → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) id)) := by
  refine ⟨fun H S hS ↦ H.comp ((continuous_inclusion hS).prodMap continuous_id),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨x', y⟩

-- The key result for continuity of multiplication and addition
-- TODO: get from the previous one instead of copy-pasting
include hAopen in
theorem continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y × Πʳ i, [R i, A i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map id (inclusion R A hS))) := by
  refine ⟨fun H S hS ↦ H.comp (continuous_id.prodMap (continuous_inclusion hS)),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  have hxS : ∀ i ∈ S, x i ∈ A i := fun i hi ↦ hi
  rcases exists_inclusion_eq_of_eventually R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_inclusion hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨y, x'⟩

-- The key result for continuity of multiplication and addition
include hAopen hAopen' in
theorem continuous_dom_prod {X : Type*} [TopologicalSpace X]
    {f : Πʳ i, [R i, A i] × Πʳ i, [R' i, A' i] → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : cofinite ≤ 𝓟 S),
      Continuous (f ∘ (Prod.map (inclusion R A hS) (inclusion R' A' hS))) := by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS ↦ H S hS S hS, fun H S hS T hT ↦ ?_⟩
  set U := S ∩ T
  have hU : cofinite ≤ 𝓟 (S ∩ T) := inf_principal ▸ le_inf hS hT
  have hSU : 𝓟 U ≤ 𝓟 S := principal_mono.mpr inter_subset_left
  have hTU : 𝓟 U ≤ 𝓟 T := principal_mono.mpr inter_subset_right
  exact (H U hU).comp ((continuous_inclusion hSU).prodMap (continuous_inclusion hTU))

end cofinite

end Topology

-- Compatibility between algebra and topology
section Compatibility

variable {S S' : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (R i)] [Π i, SetLike (S' i) (R' i)]
variable {A : Π i, S i} {A' : Π i, S' i}
variable {T : Set ι} {𝓕 : Filter ι}
variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (R' i)]

section general

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] [∀ i, ContinuousInv (R i)] :
    ContinuousInv (Πʳ i, [R i, A i]_[𝓕]) where
  continuous_inv := by
    rw [continuous_dom]
    intro T hT
    haveI : ContinuousInv (Πʳ i, [R i, A i]_[𝓟 T]) :=
      isInducing_coe_of_principal.continuousInv fun _ ↦ rfl
    exact (continuous_inclusion hT).comp continuous_inv

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousConstSMul G (R i)] :
    ContinuousConstSMul G (Πʳ i, [R i, A i]_[𝓕]) where
  continuous_const_smul g := by
    rw [continuous_dom]
    intro T hT
    haveI : ContinuousConstSMul G (Πʳ i, [R i, A i]_[𝓟 T]) :=
      isInducing_coe_of_principal.continuousConstSMul id rfl
    exact (continuous_inclusion hT).comp (continuous_const_smul g)

end general

section principal

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, A i]_[𝓟 T]) :=
  let φ : Πʳ i, [R i, A i]_[𝓟 T] →ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ ↦ rfl }
  isInducing_coe_of_principal.continuousMul φ

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, A i]_[𝓟 T]) :=
  isInducing_coe_of_principal.continuousSMul continuous_id rfl

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, A i]_[𝓟 T]) where

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, A i]_[𝓟 T]) where

end principal

section cofinite

theorem nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hAopen : ∀ i, IsOpen (A i : Set (R i))) (hT : cofinite ≤ 𝓟 T) :
    (𝓝 (inclusion R (fun i ↦ A i) hT 0)) = map (inclusion R (fun i ↦ A i) hT) (𝓝 0) :=
  nhds_eq_map_inclusion hAopen hT 0

theorem nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hAopen : ∀ i, IsOpen (A i : Set (R i))) :
    (𝓝 (structureMap R (fun i ↦ A i) cofinite 0)) =
      map (structureMap R (fun i ↦ A i) cofinite) (𝓝 0) :=
  nhds_eq_map_structureMap hAopen 0

-- TODO: Make `IsOpen` a class like `IsClosed` ?
variable [hAopen : Fact (∀ i, IsOpen (A i : Set (R i)))]
variable [hAopen' : Fact (∀ i, IsOpen (A' i : Set (R' i)))]

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Πʳ i, [R i, A i]) where
  continuous_mul := by
    rw [continuous_dom_prod hAopen.out hAopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_mul

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Πʳ i, [R i, A i]) where
  continuous_smul := by
    rw [continuous_dom_prod_left hAopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Πʳ i, [R i, A i]) where

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Πʳ i, [R i, A i]) where

open Pointwise in
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] : LocallyCompactSpace (Πʳ i, [R i, A i]) :=
  -- TODO: extract as a lemma
  haveI : ∀ i, WeaklyLocallyCompactSpace (R i) := fun i ↦ .mk fun x ↦
    ⟨x • (A i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
      hAopen.out i |>.smul _ |>.mem_nhds <| by
      simpa using smul_mem_smul_set (a := x) (one_mem (A i))⟩
  inferInstance

end cofinite

end Compatibility

end RestrictedProduct
