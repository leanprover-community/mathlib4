import Mathlib.Topology.Algebra.Group.Basic

/-!
-/

open Filter Function Set
open scoped Topology

theorem Filter.Tendsto.comp_mapClusterPt' {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : α → X} {l : Filter α} {x : X} {y : Y}
    (hf : Tendsto f (𝓝 x ⊓ map g l) (𝓝 y)) (hg : MapClusterPt x l g) : MapClusterPt y l (f ∘ g) :=
  (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hg)

theorem Filter.Tendsto.comp_mapClusterPt {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : α → X} {l : Filter α} {x : X} {y : Y}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : MapClusterPt x l g) : MapClusterPt y l (f ∘ g) :=
  (hf.mono_left inf_le_left).comp_mapClusterPt' hg

theorem ContinuousAt.comp_mapClusterPt {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : α → X} {l : Filter α} {x : X}
    (hf : ContinuousAt f x) (hg : MapClusterPt x l g) : MapClusterPt (f x) l (f ∘ g) :=
  Tendsto.comp_mapClusterPt hf hg

theorem ContinuousAt.comp_mapClusterPt_of_eq
    {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : α → X} {l : Filter α} {x : X} {y : Y}
    (hf : ContinuousAt f x) (hy : f x = y) (hg : MapClusterPt x l g) : MapClusterPt y l (f ∘ g) :=
  hy ▸ hf.comp_mapClusterPt hg

theorem MapClusterPt.curry_prodMap {α β X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la.curry lb) (.map f g) := by
  rw [mapClusterPt_iff] at hf hg
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  rw [frequently_curry_iff]
  exact (hf s hs).mono fun x hx ↦ (hg t ht).mono fun y hy ↦ ⟨hx, hy⟩

theorem MapClusterPt.prodMap {α β X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : α → X} {g : β → Y} {la : Filter α} {lb : Filter β} {x : X} {y : Y}
    (hf : MapClusterPt x la f) (hg : MapClusterPt y lb g) :
    MapClusterPt (x, y) (la ×ˢ lb) (.map f g) :=
  (hf.curry_prodMap hg).mono <| map_mono curry_le_prod

variable {G : Type*}

@[to_additive]
theorem mapClusterPt_atTop_zpow_iff_pow [DivInvMonoid G] [TopologicalSpace G] {x y : G} :
    MapClusterPt x atTop (y ^ · : ℤ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

variable [Group G] [TopologicalSpace G] [CompactSpace G] [TopologicalGroup G]

@[to_additive]
theorem mapClusterPt_self_zpow_atTop_pow (x : G) (m : ℤ) :
    MapClusterPt (x ^ m) atTop (x ^ · : ℕ → G) := by
  obtain ⟨y, hy⟩ : ∃ y, MapClusterPt y atTop (x ^ · : ℤ → G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b ↦ x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz ↦ x ^ m * yz.2 / yz.1) (y, y) := by fun_prop
    simpa only [comp_def, ← zpow_sub, ← zpow_add, div_eq_mul_inv, Prod.map, mul_inv_cancel_right]
      using this.comp_mapClusterPt (hy.curry_prodMap hy)
  suffices Tendsto ↿(fun a b ↦ m + b - a) (atTop.curry atTop) atTop from H.mono (map_mono this)
  refine Tendsto.curry <| .of_forall fun a ↦ ?_
  simp only [sub_eq_add_neg] -- TODO: add `Tendsto.atTop_sub_const` etc
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left atTop m tendsto_id)

@[to_additive]
theorem mapClusterPt_one_atTop_pow (x : G) : MapClusterPt 1 atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]
theorem mapClusterPt_self_atTop_pow (x : G) : MapClusterPt x atTop (x ^ · : ℕ → G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]
theorem mapClusterPt_atTop_pow_tfae (x y : G) :
    List.TFAE [
      MapClusterPt x atTop (y ^ · : ℕ → G),
      MapClusterPt x atTop (y ^ · : ℤ → G),
      x ∈ closure (range (y ^ · : ℕ → G)),
      x ∈ closure (range (y ^ · : ℤ → G)),
    ] := by
  tfae_have 2 ↔ 1; exact mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 → 4
  · refine fun h ↦ closure_mono (range_subset_iff.2 fun n ↦ ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 → 1
  · refine fun h ↦ closure_minimal ?_ isClosed_setOf_clusterPt h
    exact range_subset_iff.2 (mapClusterPt_self_zpow_atTop_pow _)
  tfae_have 1 → 3
  · rw [mem_closure_iff_clusterPt]
    exact (ClusterPt.mono · (le_principal_iff.2 range_mem_map))
  tfae_finish

@[to_additive]
theorem mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers {x y : G} :
    MapClusterPt x atTop (y ^ · : ℕ → G) ↔ x ∈ (Subgroup.zpowers y).topologicalClosure :=
  (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]
theorem mapClusterPt_inv_atTop_pow {x y : G} :
    MapClusterPt x⁻¹ atTop (y ^ · : ℕ → G) ↔ MapClusterPt x atTop (y ^ · : ℕ → G) := by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]
theorem closure_range_zpow_eq_pow (x : G) :
    closure (range (x ^ · : ℤ → G)) = closure (range (x ^ · : ℕ → G)) := by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]
theorem topologicalClosure_subgroupClosure_toSubmonoid (s : Set G) :
    (Subgroup.closure s).toSubmonoid.topologicalClosure =
      (Submonoid.closure s).topologicalClosure := by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid, Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx ↦ ?_
  refine closure_mono (Submonoid.powers_le.2 (Submonoid.subset_closure <| Set.mem_inv.1 hx)) ?_
  rw [Submonoid.coe_powers, ← closure_range_zpow_eq_pow, ← Subgroup.coe_zpowers,
    ← Subgroup.topologicalClosure_coe, SetLike.mem_coe, ← inv_mem_iff]
  exact subset_closure <| Subgroup.mem_zpowers _

@[to_additive]
theorem closure_submonoidClosure_eq_closure_subgroupClosure (s : Set G) :
    closure (Submonoid.closure s : Set G) = closure (Subgroup.closure s) :=
  congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]
theorem dense_submonoidClosure_iff_subgroupClosure {s : Set G} :
    Dense (Submonoid.closure s : Set G) ↔ Dense (Subgroup.closure s : Set G) := by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]
