import Mathlib.Topology.Algebra.Ring.Basic
-- The import is random

section Prod

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem continuous_prod_iff {f : X → Y × Z} :
    (Continuous f) ↔ Continuous (Prod.fst ∘ f) ∧ Continuous (Prod.snd ∘ f) :=
  continuous_inf_rng.trans <| continuous_induced_rng.and continuous_induced_rng

end Prod

section HomogeneousSpace

open Filter

@[to_additive]
theorem MulAction.continuous_of_continuousAt {G H X Y : Type*} [Mul G] [Group H]
    [SMul G X] [MulAction H Y] [MulAction.IsPretransitive G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] [TopologicalSpace Y] [ContinuousConstSMul H Y]
    {φ : G → H} {f : X → Y} (hfφ : ∀ g x, f (g • x) = φ g • f x)
    {x₀ : X} (hx₀ : ContinuousAt f x₀) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun y₀ ↦ ?_
  rcases exists_smul_eq G y₀ x₀ with ⟨g, hg⟩
  rw [ContinuousAt, ← hg, hfφ] at hx₀
  rw [ContinuousAt, (Homeomorph.smul (α := Y) (φ g)).nhds_eq_comap, tendsto_comap_iff,
    Homeomorph.smul_apply]
  exact (hx₀.comp <| tendsto_id.const_smul _).congr (hfφ _)

@[to_additive]
theorem MulHom.continuous_of_continuousAt {G H F : Type*} [Group G] [Group H]
    [TopologicalSpace G] [ContinuousConstSMul G G] [TopologicalSpace H] [ContinuousConstSMul H H]
    [FunLike F G H] [MulHomClass F G H] {f : F}
    (x₀ : G) (hx₀ : ContinuousAt f x₀) :
    Continuous f :=
  MulAction.continuous_of_continuousAt (φ := f) (map_mul f) hx₀

end HomogeneousSpace

variable {ι : Type*}

namespace Ring

variable (R : ι → Type*) [∀ i, Ring (R i)] (A : (i : ι) → Subring (R i))
variable (R' : ι → Type*) [∀ i, Ring (R' i)] (A' : (i : ι) → Subring (R' i))

def PreRestrictedProduct (S : Set ι) := {x : (i : ι) → R i // ∀ i ∉ S, x i ∈ A i}

def RestrictedProduct := {x : (i : ι) → R i // ∀ᶠ i in Filter.cofinite, x i ∈ A i}

instance (R : ι → Type*) [∀ i, Ring (R i)] (A : (i : ι) → Subring (R i)) (S : Set ι) :
    Ring (PreRestrictedProduct R A S) where
  add x y := ⟨fun i ↦ x.1 i + y.1 i, sorry⟩
  add_assoc := sorry
  zero := ⟨fun i ↦ 0, sorry⟩
  zero_add := sorry
  add_zero := sorry
  nsmul n x := ⟨fun i ↦ n • x.1 i, sorry⟩ -- is this a good idea or not? Someone who understands
                                          -- nsmul diamond issues should be asked about this.
  nsmul_zero := sorry -- ditto
  nsmul_succ := sorry -- ditto
  add_comm := sorry
  mul x y := ⟨fun i ↦ x.1 i * y.1 i, sorry⟩
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry
  neg x := ⟨fun i ↦ -x.1 i, sorry⟩
  neg_add_cancel := sorry
  zsmul z x := ⟨fun i ↦ z • x.1 i, sorry⟩ -- similarly this should be checked.
  zsmul_zero' := sorry -- ditto
  zsmul_succ' := sorry -- ditto
  zsmul_neg' := sorry -- ditto

instance (R : ι → Type*) [∀ i, Ring (R i)] (A : (i : ι) → Subring (R i)) :
    Ring (RestrictedProduct R A) where
  add x y := ⟨fun i ↦ x.1 i + y.1 i, sorry⟩
  add_assoc := sorry
  zero := ⟨fun i ↦ 0, sorry⟩
  zero_add := sorry
  add_zero := sorry
  nsmul n x := ⟨fun i ↦ n • x.1 i, sorry⟩ -- is this a good idea or not? Someone who understands
                                          -- nsmul diamond issues should be asked about this.
  nsmul_zero := sorry -- ditto
  nsmul_succ := sorry -- ditto
  add_comm := sorry
  mul x y := ⟨fun i ↦ x.1 i * y.1 i, sorry⟩
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry
  neg x := ⟨fun i ↦ -x.1 i, sorry⟩
  neg_add_cancel := sorry
  zsmul z x := ⟨fun i ↦ z • x.1 i, sorry⟩ -- similarly this should be checked.
  zsmul_zero' := sorry -- ditto
  zsmul_succ' := sorry -- ditto
  zsmul_neg' := sorry -- ditto

def RestrictedProduct.structureMap : (∀ i, A i) →+* (RestrictedProduct R A) where
  toFun x := ⟨fun i ↦ (x i).1, sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := rfl
  map_mul' x y := rfl

lemma RestrictedProduct.range_structureMap :
    Set.range (RestrictedProduct.structureMap R A) = {f | ∀ i, f.1 i ∈ A i} := by
  sorry

def PreRestrictedProduct.inclusion {S T : Set ι} (h : S ⊆ T) :
    (PreRestrictedProduct R A S) →+* (PreRestrictedProduct R A T) where
  toFun x := ⟨fun i ↦ x.1 i, fun _ hi ↦ x.2 _ (fun hi' ↦ hi (h hi'))⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def PreRestrictedProduct.structureMap (S : Set ι) :
    (∀ i, A i) →+* (PreRestrictedProduct R A S) where
  toFun x := ⟨fun i ↦ (x i).1, sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := rfl
  map_mul' x y := rfl

def RestrictedProduct.ofPre {S : Set ι} (hS : S.Finite) :
    (PreRestrictedProduct R A S) →+* (RestrictedProduct R A) where
  toFun x := ⟨fun i ↦ x.1 i, sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := rfl
  map_mul' x y := rfl

lemma RestrictedProduct.eq_ofPre_of_forall {x : RestrictedProduct R A}
    {S : Set ι} (hS : S.Finite) (hxS : ∀ i ∉ S, x.1 i ∈ A i) :
    ∃ x' : PreRestrictedProduct R A S, x = ofPre R A hS x' :=
  ⟨⟨x.1, hxS⟩, rfl⟩

lemma RestrictedProduct.range_ofPre {S : Set ι} (hS : S.Finite) :
    Set.range (ofPre R A hS) = {f | ∀ i ∉ S, f.1 i ∈ A i} := by
  sorry

def RestrictedProduct.ringEquivProd :
    (RestrictedProduct (fun i ↦ R i × R' i) (fun i ↦ (A i).prod (A' i))) ≃+*
    (RestrictedProduct R A) × (RestrictedProduct R' A') where
  toFun f := ⟨⟨fun i ↦ (f.1 i).1, sorry⟩, ⟨fun i ↦ (f.1 i).2, sorry⟩⟩
  invFun := fun fg ↦ ⟨fun i ↦ ⟨fg.1.1 i, fg.2.1 i⟩, sorry⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def PreRestrictedProduct.toPi (S : Set ι) :
    (PreRestrictedProduct R A S) →+* (Π i, R i) where
  toFun x := fun i ↦ x.1 i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def RestrictedProduct.toPi :
    (RestrictedProduct R A) →+* (Π i, R i) where
  toFun x := fun i ↦ x.1 i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Module (∀ i, A i) (RestrictedProduct R A) :=
  (RestrictedProduct.structureMap R A).toModule

section Topology

open Set Topology Filter

variable [∀ i, TopologicalSpace (R i)] [∀ i, TopologicalSpace (R' i)]

instance PreRestrictedProduct.topologicalSpace {S : Set ι} :
    TopologicalSpace (PreRestrictedProduct R A S) :=
  .induced (PreRestrictedProduct.toPi R A S) inferInstance

theorem PreRestrictedProduct.isInducing_toPi (S : Set ι) :
    IsInducing (PreRestrictedProduct.toPi R A S) where
  eq_induced := rfl

variable {R A} in
theorem PreRestrictedProduct.continuous_rng {X : Type*} [TopologicalSpace X] {S : Set ι}
    {f : X → PreRestrictedProduct R A S} :
    Continuous f ↔ Continuous (toPi R A S ∘ f) :=
  continuous_induced_rng

theorem PreRestrictedProduct.continuous_toPi (S : Set ι) :
    Continuous (PreRestrictedProduct.toPi R A S) :=
  PreRestrictedProduct.isInducing_toPi R A S |>.continuous

theorem PreRestrictedProduct.continuous_inclusion {S T : Set ι} (h : S ⊆ T) :
    Continuous (PreRestrictedProduct.inclusion R A h) :=
  continuous_induced_rng.mpr <| PreRestrictedProduct.continuous_toPi R A S

instance [∀ i, ContinuousAdd (R i)] (S : Set ι) :
    ContinuousAdd (PreRestrictedProduct R A S) :=
  PreRestrictedProduct.isInducing_toPi R A S |>.continuousAdd

instance [∀ i, ContinuousNeg (R i)] (S : Set ι) :
    ContinuousNeg (PreRestrictedProduct R A S) :=
  PreRestrictedProduct.isInducing_toPi R A S |>.continuousNeg (fun _ ↦ rfl)

instance [∀ i, IsTopologicalAddGroup (R i)] (S : Set ι) :
    IsTopologicalAddGroup (PreRestrictedProduct R A S) :=
  PreRestrictedProduct.isInducing_toPi R A S |>.topologicalAddGroup

/-- `PreRestrictedProduct R A ∅` is homeomorphic to `Π i, A i` -/
def PreRestrictedProduct.homeo_empty : (Π i, A i) ≃ₜ (PreRestrictedProduct R A (∅ : Set ι)) where
  toFun f := ⟨fun i ↦ f i, fun i _ ↦ (f i).2⟩
  invFun f i := ⟨f.1 i, f.2 i not_false⟩
  continuous_toFun := continuous_induced_rng.mpr <| continuous_pi fun i ↦
    continuous_subtype_val.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i ↦ continuous_induced_rng.mpr <|
    (continuous_apply i).comp continuous_induced_dom
  left_inv _ := rfl
  right_inv _ := rfl

instance RestrictedProduct.topologicalSpace : TopologicalSpace (RestrictedProduct R A) :=
  ⨆ (S : Set ι) (hS : S.Finite),
    .coinduced (RestrictedProduct.ofPre R A hS)
      (PreRestrictedProduct.topologicalSpace R A)

variable {R A} in
theorem RestrictedProduct.continuous_dom {X : Type*} [TopologicalSpace X]
    {f : RestrictedProduct R A → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite),
      Continuous (f ∘ RestrictedProduct.ofPre R A hS) := by
  simp_rw [continuous_iSup_dom, continuous_coinduced_dom]

theorem RestrictedProduct.continuous_toPi :
    Continuous (RestrictedProduct.toPi R A) :=
  continuous_dom.mpr fun S _ ↦ PreRestrictedProduct.continuous_toPi R A S

theorem RestrictedProduct.continuous_ofPre {S : Set ι} (hS : S.Finite) :
    Continuous (RestrictedProduct.ofPre R A hS) :=
  continuous_iSup_rng <| continuous_iSup_rng continuous_coinduced_rng

instance RestrictedProduct.continuousNeg [∀ i, ContinuousNeg (R i)] :
    ContinuousNeg (RestrictedProduct R A) where
  continuous_neg := by
    rw [continuous_dom]
    exact fun S hS ↦ (continuous_ofPre R A hS).comp continuous_neg

-- Is this useful ?
theorem RestrictedProduct.continuous_of_commutes
    (f : RestrictedProduct R A → RestrictedProduct R A)
    {T : Set ι → Set ι} (hT : ∀ S, S.Finite → (T S).Finite)
    {g : Π (S : Set ι), PreRestrictedProduct R A S → PreRestrictedProduct R A (T S)}
    (g_cont : ∀ S, S.Finite → Continuous (g S))
    (comm : ∀ S (hS : S.Finite),
      f ∘ RestrictedProduct.ofPre R A hS =
      RestrictedProduct.ofPre R A (hT S hS) ∘ (g S)) :
    Continuous f :=
  continuous_iSup_dom.mpr fun S ↦ continuous_iSup_dom.mpr fun hS ↦
    continuous_coinduced_dom.mpr <| comm S hS ▸
      (RestrictedProduct.continuous_ofPre R A (hT S hS) |>.comp (g_cont S hS))

instance RestrictedProduct.continuousConstVAdd [∀ i, IsTopologicalAddGroup (R i)] :
    ContinuousConstVAdd (RestrictedProduct R A) (RestrictedProduct R A) where
  continuous_const_vadd x := continuous_dom.mpr fun S hS ↦ by
      set T := S ∪ {i | x.1 i ∉ A i}
      have hT : T.Finite := hS.union x.2
      have hST : S ⊆ T := subset_union_left
      set x' : PreRestrictedProduct R A T := ⟨fun i ↦ x.1 i, by simp [T]⟩
      exact RestrictedProduct.continuous_ofPre R A hT |>.comp
        (continuous_const_vadd x') |>.comp (PreRestrictedProduct.continuous_inclusion R A hST)

theorem RestrictedProduct.nhds_eq_map_nhds_zero [∀ i, IsTopologicalAddGroup (R i)]
    (x : RestrictedProduct R A) : 𝓝 x = map (x + ·) (𝓝 0) := by
  simpa only [eq_comm, Homeomorph.vadd_apply, vadd_eq_add, add_zero] using
    Homeomorph.vadd x |>.map_nhds_eq (0 : RestrictedProduct R A)

theorem RestrictedProduct.isInducing_ofPre {S : Set ι} (hS : S.Finite) :
    IsInducing (RestrictedProduct.ofPre R A hS) :=
  .of_comp (RestrictedProduct.continuous_ofPre R A hS)
    (RestrictedProduct.continuous_toPi R A)
    (PreRestrictedProduct.isInducing_toPi R A S)

/-- `Π i, A i` has the subset topology from the restricted product. -/
theorem RestrictedProduct.isInducing_structureMap :
    IsInducing (RestrictedProduct.structureMap R A) :=
  (RestrictedProduct.isInducing_ofPre R A Set.finite_empty).comp
  (PreRestrictedProduct.homeo_empty R A).isInducing

variable (hAopen : ∀ i, IsOpen (A i : Set (R i))) (hAopen' : ∀ i, IsOpen (A' i : Set (R' i)))

include hAopen

theorem PreRestrictedProduct.isOpen_forall_mem_A' {S : Set ι} (hS : S.Finite) (T : Set ι) :
    IsOpen {f : PreRestrictedProduct R A S | ∀ i ∉ T, f.1 i ∈ A i} := by
  convert isOpen_set_pi (hS.diff (t := T)) (fun i _ ↦ hAopen i) |>.preimage
    (PreRestrictedProduct.continuous_toPi R A S)
  ext f
  refine ⟨fun H i hi ↦ H i hi.2, fun H i hiT ↦ ?_⟩
  by_cases hiS : i ∈ S
  · exact H i ⟨hiS, hiT⟩
  · exact f.2 i hiS

theorem PreRestrictedProduct.isOpen_forall_mem_A {S : Set ι} (hS : S.Finite) :
    IsOpen {f : PreRestrictedProduct R A S | ∀ i, f.1 i ∈ A i} := by
  convert PreRestrictedProduct.isOpen_forall_mem_A' R A hAopen hS ∅
  simp

theorem RestrictedProduct.isOpen_forall_mem_A' (T : Set ι) :
    IsOpen {f : RestrictedProduct R A | ∀ i ∉ T, f.1 i ∈ A i} := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]
  intro S hS
  exact PreRestrictedProduct.isOpen_forall_mem_A' R A hAopen hS T

theorem RestrictedProduct.isOpen_forall_mem_A :
    IsOpen {f : RestrictedProduct R A | ∀ i, f.1 i ∈ A i} := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]
  intro S hS
  exact PreRestrictedProduct.isOpen_forall_mem_A R A hAopen hS

theorem RestrictedProduct.isOpenEmbedding_ofPre {T : Set ι} (hT : T.Finite) :
    IsOpenEmbedding (RestrictedProduct.ofPre R A hT) where
  toIsInducing := RestrictedProduct.isInducing_ofPre R A hT
  injective := sorry
  isOpen_range := by
    rw [range_ofPre]
    exact RestrictedProduct.isOpen_forall_mem_A' R A hAopen T

/-- `Π i, A i` is homeomorphic to an open subset of the restricted product. -/
theorem RestrictedProduct.isOpenEmbedding_structureMap :
    IsOpenEmbedding (RestrictedProduct.structureMap R A) where
  toIsInducing := RestrictedProduct.isInducing_structureMap R A
  injective := sorry
  isOpen_range := by
    rw [RestrictedProduct.range_structureMap]
    exact RestrictedProduct.isOpen_forall_mem_A R A hAopen

theorem RestrictedProduct.nhds_eq_map_ofPre {S : Set ι} (hS : S.Finite)
    (x' : PreRestrictedProduct R A S) :
    (𝓝 (ofPre R A hS x')) = map (RestrictedProduct.ofPre R A hS) (𝓝 x') := by
  rw [RestrictedProduct.isOpenEmbedding_ofPre R A hAopen hS |>.map_nhds_eq x']

theorem RestrictedProduct.nhds_zero_eq_map_ofPre {S : Set ι} (hS : S.Finite) :
    (𝓝 0 : Filter (RestrictedProduct R A)) = map (RestrictedProduct.ofPre R A hS) (𝓝 0) :=
  RestrictedProduct.nhds_eq_map_ofPre R A hAopen hS 0

theorem RestrictedProduct.nhds_zero_eq_map_structureMap :
    (𝓝 0 : Filter (RestrictedProduct R A)) = map (RestrictedProduct.structureMap R A) (𝓝 0) :=
  RestrictedProduct.isOpenEmbedding_structureMap R A hAopen |>.map_nhds_eq 0 |>.symm

-- The key result
include hAopen' in
variable {R A R' A'} in
theorem RestrictedProduct.continuous_dom_prod {X : Type*} [TopologicalSpace X]
    {f : RestrictedProduct R A × RestrictedProduct R' A' → X} :
    Continuous f ↔ ∀ (S : Set ι) (hS : S.Finite),
      Continuous (f ∘ (Prod.map (ofPre R A hS) (ofPre R' A' hS))) := by
  refine ⟨fun H S hS ↦ H.comp ((continuous_ofPre R A hS).prodMap (continuous_ofPre R' A' hS)),
    fun H ↦ ?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, y⟩
  set S : Set ι := {i | x.1 i ∉ A i} ∪ {i | y.1 i ∉ A' i}
  have hS : S.Finite := .union x.2 y.2
  have hxS : ∀ i ∉ S, x.1 i ∈ A i := fun i hi ↦ by_contra fun hi' ↦ hi (subset_union_left hi')
  have hyS : ∀ i ∉ S, y.1 i ∈ A' i := fun i hi ↦ by_contra fun hi' ↦ hi (subset_union_right hi')
  rcases eq_ofPre_of_forall R A hS hxS with ⟨x', hxx'⟩
  rcases eq_ofPre_of_forall R' A' hS hyS with ⟨y', hyy'⟩
  rw [hxx', hyy', nhds_prod_eq, nhds_eq_map_ofPre R A hAopen hS x',
    nhds_eq_map_ofPre R' A' hAopen' hS y', prod_map_map_eq, ← nhds_prod_eq, tendsto_map'_iff]
  exact (H S hS |>.tendsto ⟨x', y'⟩)

omit hAopen in
instance RestrictedProduct.continuousAdd
    [hAopen : Fact (∀ i, IsOpen (A i : Set (R i)))] [∀ i, ContinuousAdd (R i)] :
    ContinuousAdd (RestrictedProduct R A) where
  continuous_add := by
    rw [continuous_dom_prod hAopen.out hAopen.out]
    exact fun S hS ↦ (continuous_ofPre R A hS).comp continuous_add

omit hAopen in

-- Experimentation starts here

#check continuous_prod_mk

include hAopen' in
def RestrictedProduct.homeomorphProd :
    (RestrictedProduct (fun i ↦ R i × R' i) (fun i ↦ (A i).prod (A' i))) ≃ₜ
    (RestrictedProduct R A) × (RestrictedProduct R' A') :=
  { toEquiv := RestrictedProduct.ringEquivProd R A R' A'
    continuous_toFun := by
      simp_rw [continuous_dom, continuous_prod_iff]
      intro S hS
      refine ⟨(continuous_ofPre R A hS).comp ?_, ?_⟩
      refine continuous_dom.mpr fun S hS ↦ continuous_inf_rng.mpr _
      sorry
    continuous_invFun := by
      sorry}

theorem RestrictedProduct.topology_eq_of_isOpenEmbedding [∀ i, IsTopologicalAddGroup (R i)]
    {t : TopologicalSpace (RestrictedProduct R A)}
    (h_add : ∀ x : RestrictedProduct R A, @nhds _ t x = map (x + ·) (@nhds _ t 0))
    (h_open : IsOpenEmbedding (tY := t) (RestrictedProduct.structureMap R A)) :
    t = RestrictedProduct.topologicalSpace R A := by
  refine TopologicalSpace.ext_nhds fun x ↦ ?_
  rw [h_add x, nhds_eq_map_nhds_zero R A x, nhds_zero_eq_map R A hAopen, h_open.map_nhds_eq 0]
  rfl

-- def RestrictedProduct.topology_prod_eq_induced [∀ i, IsTopologicalAddGroup (R i)] :
--     (instTopologicalSpaceProd (X := RestrictedProduct R A) (Y := RestrictedProduct R A)) =
--     .induced (RestrictedProduct.ringEquivProd R A |>.symm) inferInstance := by
--   refine RestrictedProduct.topology_eq_of_isOpenEmbedding R A hAopen _ _
--   sorry

private lemma RestrictedProduct.ringEquivProd_map_nhds [∀ i, IsTopologicalAddGroup (R i)] :
    map (ringEquivProd R A) (𝓝 0) = 𝓝 0 := by
  rw [RestrictedProduct.nhds_zero_eq_map _ _ (fun i ↦ (hAopen i |>.prod <| hAopen i)), map_map,
      Prod.zero_eq_mk, nhds_prod_eq, RestrictedProduct.nhds_zero_eq_map _ _ hAopen, prod_map_map_eq]

  sorry

def RestrictedProduct.homeomorphProd [∀ i, IsTopologicalAddGroup (R i)] :
    (RestrictedProduct (fun i ↦ R i × R i) (fun i ↦ (A i).prod (A i))) ≃ₜ
    (RestrictedProduct R A) × (RestrictedProduct R A) :=
  haveI : ContinuousConstVAdd (RestrictedProduct R A × RestrictedProduct R A)
    (RestrictedProduct R A × RestrictedProduct R A) :=
    { continuous_const_vadd := fun ⟨a, b⟩ ↦
        (continuous_const_vadd a).prodMap (continuous_const_vadd b) }
  { toEquiv := RestrictedProduct.ringEquivProd R A
    continuous_toFun := by
      refine AddHom.continuous_of_continuousAt (f := ringEquivProd R A) 0 ?_
      rw [ContinuousAt, map_zero, RestrictedProduct.nhds_zero_eq_map _ _
        (fun i ↦ (hAopen i |>.prod <| hAopen i)), Prod.zero_eq_mk, nhds_prod_eq, tendsto_prod_iff',
        RestrictedProduct.nhds_zero_eq_map _ _ hAopen]
    continuous_invFun := by
      refine AddHom.continuous_of_continuousAt (f := (ringEquivProd R A).symm) 0 ?_
      sorry}

instance RestrictedProduct.topologicalAddGroup [∀ i, IsTopologicalAddGroup (R i)] :
    IsTopologicalAddGroup (RestrictedProduct R A) := by
  -- Should not be neded
  haveI : ∀ i, IsTopologicalAddGroup (A i) :=
    fun i ↦ (A i).toAddSubgroup.instIsTopologicalAddGroupSubtypeMem
  -- Why are these slow ????
  haveI : ContinuousAdd (Π i, A i) := sorry
  haveI : ContinuousNeg (Π i, A i) := sorry

  refine .of_comm_of_nhds_zero ?_ ?_ (RestrictedProduct.nhds_eq_map_nhds_zero R A) <;>
  rw [RestrictedProduct.nhds_zero_eq_map R A hAopen]
  · rw [prod_map_map_eq]
    have : Tendsto (fun xy : (Π i, A i) × (Π i, A i) ↦ xy.1 + xy.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
      conv => arg 3; rw [← add_zero 0]
      exact tendsto_fst.add tendsto_snd
    convert tendsto_map.comp this
  · have : Tendsto (fun x : (Π i, A i) ↦ - x) (𝓝 0 ) (𝓝 0) := by
      conv => arg 3; rw [← neg_zero]
      exact tendsto_neg (0)
    convert tendsto_map.comp this

instance RestrictedProduct.topologicalRing [∀ i, TopologicalRing (R i)] :
    TopologicalRing (RestrictedProduct R A) := by
  haveI : IsTopologicalAddGroup (RestrictedProduct R A) := topologicalAddGroup R A hAopen
  refine .of_addGroup_of_nhds_zero ?_ ?_ ?_ <;>
  rw [RestrictedProduct.nhds_zero_eq_map R A hAopen]
  · rw [prod_map_map_eq]
    sorry
  · sorry
  · sorry

def ringFilterBasis : RingFilterBasis (RestrictedProduct R A) where
  sets := {U | ∃ V : Set (∀ i, A i), IsOpen V ∧ 0 ∈ V ∧ structureMap R A '' V = U}
  nonempty := ⟨_, ⊤, isOpen_univ, trivial, rfl⟩
  inter_sets := by
    rintro _ _ ⟨V, hVopen, hV0, rfl⟩ ⟨W, hWopen, hW0, rfl⟩
    exact ⟨structureMap R A '' (V ∩ W), ⟨V ∩ W, IsOpen.inter hVopen hWopen, Set.mem_inter hV0 hW0,
      rfl⟩, Set.image_inter_subset _ _ _⟩
  zero' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    exact ⟨0, hV0, rfl⟩
  add' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWadd⟩ := TopologicalRing.ringFilterBasis_add hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, hWadd <| Set.add_mem_add hx hy, rfl⟩
  neg' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWneg⟩ := TopologicalRing.ringFilterBasis_neg hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hWneg hx, rfl⟩
  conj' r {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    refine ⟨_, ⟨V, hVopen, hV0, rfl⟩, ?_⟩
    simp
  mul' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWmul⟩ := TopologicalRing.ringFilterBasis_mul hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩ -- wtong, need smaller V
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x * y, hWmul <| Set.mul_mem_mul hx hy, rfl⟩
  mul_left' r {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    -- strat: shrink V to make it ∏ᵢ Vᵢ with Vᵢ open in Aᵢ and Vᵢ = Aᵢ for all but finitely many i.
    -- Now define Wᵢ open in Aᵢ thus. If Vᵢ = Aᵢ and rᵢ ∈ Aᵢ then set Wᵢ = Aᵢ (this happens for
    -- all but finitely many i). Now what about the bad i?
    -- For these, apply `ringFilterBasis_mul_left` to Rᵢ, rᵢ and the image of Vᵢ to get
    -- Wᵢ with rᵢWᵢ ⊆ Vᵢ. Then ∏ᵢ Wᵢ works.
    sorry
  mul_right' := sorry -- probably have to repeat the argument mutatis mutandis.

instance : TopologicalSpace (RestrictedProduct R A) := (ringFilterBasis R A).topology

-- instance : TopologicalRing (RestrictedProduct R A) := inferInstance

/-
RingSubgroupsBasis.hasBasis_nhds_zero.{u_1, u_2} {A : Type u_1} {ι : Type u_2} [Ring A] [Nonempty ι]
  {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) : (𝓝 0).HasBasis (fun x ↦ True) fun i ↦ ↑(B i)
-/

-- PR and refactor `RingSubgroupsBasis.hasBasis_nhds_zero`
open Filter in
lemma _root_.RingFilterBasis.hasBasis_nhds_zero {A : Type*} [Ring A]
    (B : RingFilterBasis A) : HasBasis (@nhds A B.topology 0) (fun _ => True)
    fun (i : {S // S ∈ B.sets}) => i :=
  ⟨by
    intro s
    rw [B.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨t, h0, hi⟩
      exact ⟨⟨t, h0⟩, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨i.1, i.2, hi⟩⟩

lemma continuous_structureMap : Continuous (structureMap R A) := by
  -- this must help
  have := RingFilterBasis.hasBasis_nhds_zero (ringFilterBasis R A)
  sorry

lemma isOpenMap_structureMap : IsOpenMap (structureMap R A) := by
  sorry

end Topology

end Ring.RestrictedProduct
