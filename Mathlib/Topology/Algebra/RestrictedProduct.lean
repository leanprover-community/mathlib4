import Mathlib.Topology.Algebra.Ring.Basic
-- The import is random

open Set Topology Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))
variable (R' : ι → Type*) (A' : (i : ι) → Set (R' i))

def RestrPi : Type _ := {x : Π i, R i // ∀ᶠ i in cofinite, x i ∈ A i}
def RestrPi.Pre (S : Set ι) : Type _ := {x : Π i, R i // ∀ i ∉ S, x i ∈ A i}

namespace RestrPi

instance : DFunLike (RestrPi R A) ι R where
  coe x i := x.1 i
  coe_injective' _ _ := Subtype.ext

instance {S : Set ι} : DFunLike (Pre R A S) ι R where
  coe x i := x.1 i
  coe_injective' _ _ := Subtype.ext

lemma Pre.range_coe {S : Set ι} : range ((↑) : Pre R A S → Π i, R i) = Sᶜ.pi A :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2) (fun x hx ↦ mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)

def structureMap (x : Π i, A i) : RestrPi R A := ⟨fun i ↦ x i, .of_forall fun i ↦ (x i).2⟩
def Pre.structureMap {S : Set ι} (x : Π i, A i) : Pre R A S := ⟨fun i ↦ x i, fun i _ ↦ (x i).2⟩

def Pre.inclusion {S T : Set ι} (h : S ⊆ T) (x : Pre R A S) : Pre R A T :=
  ⟨x, fun _ hi ↦ x.2 _ fun hi' ↦ hi (h hi')⟩

def ofPre {S : Set ι} (hS : S.Finite) (x : Pre R A S) : RestrPi R A :=
  ⟨x, hS.eventually_cofinite_nmem.mono x.2⟩

lemma exists_ofPre_eq_of_forall {x : RestrPi R A}
    {S : Set ι} (hS : S.Finite) (hxS : ∀ i ∉ S, x.1 i ∈ A i) :
    ∃ x' : Pre R A S, ofPre R A hS x' = x :=
  ⟨⟨x.1, hxS⟩, rfl⟩

lemma exists_structureMap_eq_of_forall {x : RestrPi R A} (hx : ∀ i, x.1 i ∈ A i) :
    ∃ x' : Π i, A i, structureMap R A x' = x :=
  ⟨fun i ↦ ⟨x i, hx i⟩, rfl⟩

lemma range_ofPre {S : Set ι} (hS : S.Finite) :
    Set.range (ofPre R A hS) = {f | ∀ i ∉ S, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ x.2)
    (fun _ hx ↦ mem_range.mpr <| exists_ofPre_eq_of_forall R A hS hx)

lemma range_structureMap :
    Set.range (structureMap R A) = {f | ∀ i, f.1 i ∈ A i} :=
  subset_antisymm (range_subset_iff.mpr fun x i ↦ (x i).2)
    (fun _ hx ↦ mem_range.mpr <| exists_structureMap_eq_of_forall R A hx)

section Algebra

variable {S S' : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (R i)] [Π i, SetLike (S' i) (R' i)]
variable {A : Π i, S i} {A' : Π i, S' i}
variable {T : Set ι}

@[to_additive]
instance [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] : One (RestrPi R (fun i ↦ A i)) where
  one := ⟨fun _ ↦ 1, .of_forall fun _ ↦ one_mem _⟩

@[to_additive]
instance [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] : One (Pre R (fun i ↦ A i) T) where
  one := ⟨fun _ ↦ 1, fun _ _ ↦ one_mem _⟩

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (RestrPi R (fun i ↦ A i)) where
  inv x := ⟨fun i ↦ (x i)⁻¹, x.2.mono fun _ ↦ inv_mem⟩

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] : Inv (Pre R (fun i ↦ A i) T) where
  inv x := ⟨fun i ↦ (x i)⁻¹, fun i hi ↦ inv_mem (x.2 i hi)⟩

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (RestrPi R (fun i ↦ A i)) where
  mul x y := ⟨fun i ↦ x i * y i, y.2.mp (x.2.mono fun _ ↦ mul_mem)⟩

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] : Mul (Pre R (fun i ↦ A i) T) where
  mul x y := ⟨fun i ↦ x i * y i, fun i hi ↦ mul_mem (x.2 i hi) (y.2 i hi)⟩

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (RestrPi R (fun i ↦ A i)) where
  smul g x := ⟨fun i ↦ g • (x i), x.2.mono fun _ ↦ SMulMemClass.smul_mem g⟩

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] :
    SMul G (Pre R (fun i ↦ A i) T) where
  smul g x := ⟨fun i ↦ g • (x i), fun i hi ↦ SMulMemClass.smul_mem g (x.2 i hi)⟩

@[to_additive]
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (RestrPi R (fun i ↦ A i)) where
  div x y := ⟨fun i ↦ x i / y i, y.2.mp (x.2.mono fun _ ↦ div_mem)⟩

@[to_additive]
instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Div (Pre R (fun i ↦ A i) T) where
  div x y := ⟨fun i ↦ x i / y i, fun i hi ↦ div_mem (x.2 i hi) (y.2 i hi)⟩

instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (RestrPi R (fun i ↦ A i)) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ pow_mem hi n⟩

instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Pow (Pre R (fun i ↦ A i) T) ℕ where
  pow x n := ⟨fun i ↦ x i ^ n, fun i hi ↦ pow_mem (x.2 i hi) n⟩

instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (RestrPi R (fun i ↦ A i)) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, x.2.mono fun _ hi ↦ zpow_mem hi n⟩

instance [Π i, DivInvMonoid (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Pow (Pre R (fun i ↦ A i) T) ℤ where
  pow x n := ⟨fun i ↦ x i ^ n, fun i hi ↦ zpow_mem (x.2 i hi) n⟩

instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (RestrPi R (fun i ↦ A i)) where
  natCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ natCast_mem _ n⟩

instance [Π i, AddMonoidWithOne (R i)] [∀ i, AddSubmonoidWithOneClass (S i) (R i)] :
    NatCast (Pre R (fun i ↦ A i) T) where
  natCast n := ⟨fun _ ↦ n, fun _ _ ↦ natCast_mem _ n⟩

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (RestrPi R (fun i ↦ A i)) where
  intCast n := ⟨fun _ ↦ n, .of_forall fun _ ↦ intCast_mem _ n⟩

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    IntCast (Pre R (fun i ↦ A i) T) where
  intCast n := ⟨fun _ ↦ n, fun _ _ ↦ intCast_mem _ n⟩

instance [Π i, AddGroup (R i)] [∀ i, AddSubgroupClass (S i) (R i)] :
    AddGroup (RestrPi R (fun i ↦ A i)) :=
  haveI : ∀ i, SMulMemClass (S i) ℤ (R i) := fun _ ↦ AddSubgroupClass.zsmulMemClass
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Π i, AddGroup (R i)] [∀ i, AddSubgroupClass (S i) (R i)] :
    AddGroup (Pre R (fun i ↦ A i) T) :=
  haveI : ∀ i, SMulMemClass (S i) ℤ (R i) := fun _ ↦ AddSubgroupClass.zsmulMemClass
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (RestrPi R (fun i ↦ A i)) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] :
    Group (Pre R (fun i ↦ A i) T) :=
  DFunLike.coe_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (RestrPi R (fun i ↦ A i)) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    Ring (Pre R (fun i ↦ A i) T) :=
  DFunLike.coe_injective.ring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Algebra

section Topology

variable [∀ i, TopologicalSpace (R i)] [∀ i, TopologicalSpace (R' i)]

-- Topology on `Pre R A S`
section Pre

instance Pre.topologicalSpace {S : Set ι} :
    TopologicalSpace (Pre R A S) :=
  .induced ((↑) : Pre R A S → Π i, R i) inferInstance

theorem Pre.isInducing_coe (S : Set ι) :
    IsInducing ((↑) : Pre R A S → Π i, R i) where
  eq_induced := rfl

variable {R A} in
theorem Pre.continuous_rng {X : Type*} [TopologicalSpace X] {S : Set ι}
    {f : X → Pre R A S} :
    Continuous f ↔ Continuous ((↑) ∘ f : X → Π i, R i) :=
  continuous_induced_rng

theorem Pre.continuous_coe (S : Set ι) :
    Continuous ((↑) : Pre R A S → Π i, R i) :=
  Pre.isInducing_coe R A S |>.continuous

theorem Pre.continuous_inclusion {S T : Set ι} (h : S ⊆ T) :
    Continuous (Pre.inclusion R A h) :=
  continuous_rng.mpr <| Pre.continuous_coe R A S

/-- `PreRestrictedProduct R A ∅` is homeomorphic to `Π i, A i` -/
def Pre.homeo_empty : (Π i, A i) ≃ₜ (Pre R A ∅) where
  toFun f := ⟨fun i ↦ f i, fun i _ ↦ (f i).2⟩
  invFun f i := ⟨f i, f.2 i not_false⟩
  continuous_toFun := continuous_rng.mpr <| continuous_pi fun i ↦
    continuous_subtype_val.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ continuous_induced_rng.mpr <|
    (continuous_apply i).comp continuous_induced_dom
  left_inv _ := rfl
  right_inv _ := rfl

instance {S : Set ι} [hS : Fact (S.Finite)]
    [∀ i, WeaklyLocallyCompactSpace (R i)] [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (Pre R A S) where
  exists_compact_mem_nhds := fun x ↦ by
    classical
    have : ∀ i, ∃ K, IsCompact K ∧ K ∈ 𝓝 (x i) := fun i ↦ exists_compact_mem_nhds (x i)
    choose K K_compact hK using this
    set Q : Set (Π i, R i) := univ.pi (fun i ↦ if i ∈ S then K i else A i) with Q_def
    have Q_compact : IsCompact Q := isCompact_univ_pi fun i ↦ by
      split_ifs
      · exact K_compact i
      · exact isCompact_iff_compactSpace.mpr inferInstance
    set U : Set (Π i, R i) := S.pi K with U_def
    have U_nhds : U ∈ 𝓝 (x : Π i, R i) := set_pi_mem_nhds hS.out fun i _ ↦ hK i
    have QU : (↑) ⁻¹' U ⊆ ((↑) ⁻¹' Q : Set (Pre R A S)) := fun y H i _ ↦ by
      dsimp only
      split_ifs with hi
      · exact H i hi
      · exact y.2 i hi
    refine ⟨((↑) ⁻¹' Q), ?_, mem_of_superset ?_ QU⟩
    · refine Pre.isInducing_coe R A S |>.isCompact_preimage_iff ?_ |>.mpr Q_compact
      simp_rw [Pre.range_coe, Q_def, pi_if, mem_univ, true_and]
      exact inter_subset_right
    · simpa only [nhds_induced] using preimage_mem_comap U_nhds

end Pre

-- Put the inductive limit topology on `RestrPi R A`
section IndLimit

instance topologicalSpace : TopologicalSpace (RestrPi R A) :=
  ⨆ (S : Set ι) (hS : S.Finite), .coinduced (ofPre R A hS) (Pre.topologicalSpace R A)

variable {R A} in
theorem continuous_dom {X : Type*} [TopologicalSpace X]
    {f : RestrPi R A → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite), Continuous (f ∘ ofPre R A hS) := by
  simp_rw [continuous_iSup_dom, continuous_coinduced_dom]

theorem continuous_coe :
    Continuous ((↑) : RestrPi R A → Π i, R i) :=
  continuous_dom.mpr fun S _ ↦ Pre.continuous_coe R A S

theorem continuous_ofPre {S : Set ι} (hS : S.Finite) :
    Continuous (ofPre R A hS) :=
  continuous_iSup_rng <| continuous_iSup_rng continuous_coinduced_rng

theorem isInducing_ofPre {S : Set ι} (hS : S.Finite) :
    IsInducing (ofPre R A hS) :=
  .of_comp (continuous_ofPre R A hS) (continuous_coe R A) (Pre.isInducing_coe R A S)

theorem isEmbedding_ofPre {S : Set ι} (hS : S.Finite) :
    IsEmbedding (ofPre R A hS) where
  toIsInducing := isInducing_ofPre R A hS
  injective _ _ h := DFunLike.ext _ _ (fun i ↦ DFunLike.congr_fun h i)

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem isInducing_structureMap :
    IsInducing (structureMap R A) :=
  (isInducing_ofPre R A Set.finite_empty).comp (Pre.homeo_empty R A).isInducing

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem isEmbedding_structureMap :
    IsEmbedding (structureMap R A) :=
  (isEmbedding_ofPre R A Set.finite_empty).comp (Pre.homeo_empty R A).isEmbedding

end IndLimit

-- Assuming that each `A i` is open, this is in fact a strict inductive limit,
-- which gives us a bunch of facts
section StrIndLimit

variable (hAopen : ∀ i, IsOpen (A i)) (hAopen' : ∀ i, IsOpen (A' i))

include hAopen in
theorem Pre.isOpen_forall_mem' {S : Set ι} (hS : S.Finite) (T : Set ι) :
    IsOpen {f : Pre R A S | ∀ i ∉ T, f.1 i ∈ A i} := by
  convert isOpen_set_pi (hS.diff (t := T)) (fun i _ ↦ hAopen i)
    |>.preimage (Pre.continuous_coe R A S)
  ext f
  refine ⟨fun H i hi ↦ H i hi.2, fun H i hiT ↦ ?_⟩
  by_cases hiS : i ∈ S
  · exact H i ⟨hiS, hiT⟩
  · exact f.2 i hiS

include hAopen in
theorem Pre.isOpen_forall_mem {S : Set ι} (hS : S.Finite) :
    IsOpen {f : Pre R A S | ∀ i, f.1 i ∈ A i} := by
  convert Pre.isOpen_forall_mem' R A hAopen hS ∅
  simp

include hAopen in
theorem isOpen_forall_mem' (T : Set ι) :
    IsOpen {f : RestrPi R A | ∀ i ∉ T, f.1 i ∈ A i} := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ Pre.isOpen_forall_mem' R A hAopen hS T

include hAopen in
theorem isOpen_forall_mem :
    IsOpen {f : RestrPi R A | ∀ i, f.1 i ∈ A i} := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]
  exact fun S hS ↦ Pre.isOpen_forall_mem R A hAopen hS

include hAopen in
theorem isOpenEmbedding_ofPre {S : Set ι} (hS : S.Finite) :
    IsOpenEmbedding (ofPre R A hS) where
  toIsEmbedding := isEmbedding_ofPre R A hS
  isOpen_range := by
    rw [range_ofPre]
    exact isOpen_forall_mem' R A hAopen S

include hAopen in
/-- `Π i, A i` is homeomorphic to an open subset of the restricted product. -/
theorem isOpenEmbedding_structureMap :
    IsOpenEmbedding (structureMap R A) where
  toIsEmbedding := isEmbedding_structureMap R A
  isOpen_range := by
    rw [range_structureMap]
    exact isOpen_forall_mem R A hAopen

include hAopen in
theorem nhds_eq_map_ofPre {S : Set ι} (hS : S.Finite)
    (x : Pre R A S) :
    (𝓝 (ofPre R A hS x)) = map (ofPre R A hS) (𝓝 x) := by
  rw [isOpenEmbedding_ofPre R A hAopen hS |>.map_nhds_eq x]

include hAopen in
theorem nhds_eq_map_structureMap
    (x : Π i, A i) :
    (𝓝 (structureMap R A x)) = map (structureMap R A) (𝓝 x) := by
  rw [isOpenEmbedding_structureMap R A hAopen |>.map_nhds_eq x]

instance [hAopen : Fact (∀ i, IsOpen (A i))] [∀ i, WeaklyLocallyCompactSpace (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] :
    WeaklyLocallyCompactSpace (RestrPi R A) where
  exists_compact_mem_nhds := fun x ↦ by
    set S := {i | x i ∉ A i}
    have hS : S.Finite := x.2
    haveI : Fact (S.Finite) := ⟨hS⟩
    have hSx : ∀ i ∉ S, x i ∈ A i := fun i hi ↦ by_contra hi
    rcases exists_ofPre_eq_of_forall R A hS hSx with ⟨x', hxx'⟩
    rw [← hxx', nhds_eq_map_ofPre R A hAopen.out]
    rcases exists_compact_mem_nhds x' with ⟨K, K_compact, hK⟩
    exact ⟨ofPre R A hS '' K, K_compact.image (continuous_ofPre R A hS), image_mem_map hK⟩

-- The key result for continuity of multiplication and addition
include hAopen in
variable {R A} in
theorem continuous_dom_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : RestrPi R A × Y → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite),
      Continuous (f ∘ (Prod.map (ofPre R A hS) id)) := by
  refine ⟨fun H S hS ↦ H.comp ((continuous_ofPre R A hS).prodMap continuous_id),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x.1 i ∉ A i}
  have hS : S.Finite := x.2
  have hxS : ∀ i ∉ S, x.1 i ∈ A i := fun i hi ↦ by_contra hi
  rcases exists_ofPre_eq_of_forall R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_ofPre R A hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨x', y⟩

-- The key result for continuity of multiplication and addition
-- TODO: get from the previous one instead of copy-pasting
include hAopen in
variable {R A} in
theorem continuous_dom_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y × RestrPi R A → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite),
      Continuous (f ∘ (Prod.map id (ofPre R A hS))) := by
  refine ⟨fun H S hS ↦ H.comp (continuous_id.prodMap (continuous_ofPre R A hS)),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨y, x⟩
  set S : Set ι := {i | x.1 i ∉ A i}
  have hS : S.Finite := x.2
  have hxS : ∀ i ∉ S, x.1 i ∈ A i := fun i hi ↦ by_contra hi
  rcases exists_ofPre_eq_of_forall R A hS hxS with ⟨x', hxx'⟩
  rw [← hxx', nhds_prod_eq, nhds_eq_map_ofPre R A hAopen hS x',
    ← map_id (f := 𝓝 y), prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact H S hS |>.tendsto ⟨y, x'⟩

-- The key result for continuity of multiplication and addition
include hAopen hAopen' in
variable {R A R' A'} in
theorem continuous_dom_prod {X : Type*} [TopologicalSpace X]
    {f : RestrPi R A × RestrPi R' A' → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite),
      Continuous (f ∘ (Prod.map (ofPre R A hS) (ofPre R' A' hS))) := by
  simp_rw [continuous_dom_prod_right hAopen, continuous_dom_prod_left hAopen']
  refine ⟨fun H S hS ↦ H S hS S hS, fun H S hS T hT ↦ ?_⟩
  set U := S ∪ T
  have hU : U.Finite := hS.union hT
  have hSU : S ⊆ U := subset_union_left
  have hTU : T ⊆ U := subset_union_right
  exact (H U hU).comp
    ((Pre.continuous_inclusion R A hSU).prodMap (Pre.continuous_inclusion R' A' hTU))

end StrIndLimit

end Topology

-- Compatibility between algebra and topology
section Compatibility

variable {S S' : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (R i)] [Π i, SetLike (S' i) (R' i)]
variable {A : Π i, S i} {A' : Π i, S' i}
variable {T : Set ι}
variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (R' i)]

-- Results for `Pre R A T`
section Pre

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] [∀ i, ContinuousInv (R i)] :
    ContinuousInv (Pre R (fun i ↦ A i) T) :=
  Pre.isInducing_coe R _ T |>.continuousInv (fun _ ↦ rfl)

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousConstSMul G (R i)] :
    ContinuousConstSMul G (Pre R (fun i ↦ A i) T) :=
  Pre.isInducing_coe R _ T |>.continuousConstSMul id rfl

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (Pre R (fun i ↦ A i) T) :=
  let φ : Pre R (fun i ↦ A i) T →ₙ* Π i, R i :=
  { toFun := (↑)
    map_mul' := fun _ _ ↦ rfl }
  Pre.isInducing_coe R _ T |>.continuousMul φ

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (Pre R (fun i ↦ A i) T) :=
  Pre.isInducing_coe R _ T |>.continuousSMul continuous_id rfl

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (Pre R (fun i ↦ A i) T) where

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (Pre R (fun i ↦ A i) T) where

end Pre

-- Results for `RestrPi` depending only on the fact that it has an inductive limit topology
section IndLimit

@[to_additive]
instance [Π i, Inv (R i)] [∀ i, InvMemClass (S i) (R i)] [∀ i, ContinuousInv (R i)] :
    ContinuousInv (RestrPi R (fun i ↦ A i)) where
  continuous_inv := by
    rw [continuous_dom]
    exact fun S hS ↦ (continuous_ofPre R _ hS).comp continuous_inv

@[to_additive]
instance {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousConstSMul G (R i)] :
    ContinuousConstSMul G (RestrPi R (fun i ↦ A i)) where
  continuous_const_smul g := by
    rw [continuous_dom]
    exact fun S hS ↦ (continuous_ofPre R _ hS).comp (continuous_const_smul g)

end IndLimit

-- Results for `RestrPi` depending on the fact that it has a *strict* inductive limit topology
section StrIndLimit

theorem nhds_zero_eq_map_ofPre [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hAopen : ∀ i, IsOpen (A i : Set (R i))) (hT : T.Finite) :
    (𝓝 (ofPre R (fun i ↦ A i) hT 0)) = map (ofPre R (fun i ↦ A i) hT) (𝓝 0) :=
  nhds_eq_map_ofPre R _ hAopen hT 0

theorem nhds_zero_eq_map_structureMap [Π i, Zero (R i)] [∀ i, ZeroMemClass (S i) (R i)]
    (hAopen : ∀ i, IsOpen (A i : Set (R i))) :
    (𝓝 (structureMap R (fun i ↦ A i) 0)) = map (structureMap R (fun i ↦ A i)) (𝓝 0) :=
  nhds_eq_map_structureMap R _ hAopen 0

-- TODO: Make `IsOpen` a class like `IsClosed` ?
variable [hAopen : Fact (∀ i, IsOpen (A i : Set (R i)))]
variable [hAopen' : Fact (∀ i, IsOpen (A' i : Set (R' i)))]

@[to_additive]
instance [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)] [∀ i, ContinuousMul (R i)] :
    ContinuousMul (RestrPi R (fun i ↦ A i)) where
  continuous_mul := by
    rw [continuous_dom_prod hAopen.out hAopen.out]
    exact fun S hS ↦ (continuous_ofPre R _ hS).comp continuous_mul

@[to_additive]
instance {G : Type*} [TopologicalSpace G] [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)]
    [∀ i, ContinuousSMul G (R i)] :
    ContinuousSMul G (RestrPi R (fun i ↦ A i)) where
  continuous_smul := by
    rw [continuous_dom_prod_left hAopen.out]
    exact fun S hS ↦ (continuous_ofPre R _ hS).comp continuous_smul

@[to_additive]
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)] :
    IsTopologicalGroup (RestrPi R (fun i ↦ A i)) where

instance [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] [∀ i, IsTopologicalRing (R i)] :
    IsTopologicalRing (RestrPi R (fun i ↦ A i)) where

open Pointwise in
instance [Π i, Group (R i)] [∀ i, SubgroupClass (S i) (R i)] [∀ i, IsTopologicalGroup (R i)]
    [hAcompact : ∀ i, CompactSpace (A i)] : LocallyCompactSpace (RestrPi R (A ·)) :=
  -- TODO: extract as a lemma
  haveI : ∀ i, WeaklyLocallyCompactSpace (R i) := fun i ↦ .mk fun x ↦
    ⟨x • (A i : Set (R i)), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
      hAopen.out i |>.smul _ |>.mem_nhds <| by
      simpa using smul_mem_smul_set (a := x) (one_mem (A i))⟩
  inferInstance

end StrIndLimit

end Compatibility

end RestrPi
