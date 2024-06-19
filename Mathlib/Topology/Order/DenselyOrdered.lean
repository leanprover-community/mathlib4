/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Order.IsLUB

/-!
# Order topology on a densely ordered set
-/

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section DenselyOrdered

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α] {a b : α}
  {s : Set α}

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`, unless `a` is a top
element. -/
theorem closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a := by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← diff_subset_closure_iff, Ici_diff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h
#align closure_Ioi' closure_Ioi'

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`. -/
@[simp]
theorem closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici a :=
  closure_Ioi' nonempty_Ioi
#align closure_Ioi closure_Ioi

/-- The closure of the interval `(-∞, a)` is the closed interval `(-∞, a]`, unless `a` is a bottom
element. -/
theorem closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Iic a :=
  closure_Ioi' (α := αᵒᵈ) h
#align closure_Iio' closure_Iio'

/-- The closure of the interval `(-∞, a)` is the interval `(-∞, a]`. -/
@[simp]
theorem closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic a :=
  closure_Iio' nonempty_Iio
#align closure_Iio closure_Iio

/-- The closure of the open interval `(a, b)` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ioo {a b : α} (hab : a ≠ b) : closure (Ioo a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · cases' hab.lt_or_lt with hab hab
    · rw [← diff_subset_closure_iff, Icc_diff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(isGLB_Ioo hab).mem_closure hab', (isLUB_Ioo hab).mem_closure hab'⟩
    · rw [Icc_eq_empty_of_lt hab]
      exact empty_subset _
#align closure_Ioo closure_Ioo

/-- The closure of the interval `(a, b]` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ioc {a b : α} (hab : a ≠ b) : closure (Ioc a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]
#align closure_Ioc closure_Ioc

/-- The closure of the interval `[a, b)` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ico {a b : α} (hab : a ≠ b) : closure (Ico a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]
#align closure_Ico closure_Ico

@[simp]
theorem interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior (Ici a) = Ioi a := by
  rw [← compl_Iio, interior_compl, closure_Iio' ha, compl_Iic]
#align interior_Ici' interior_Ici'

theorem interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = Ioi a :=
  interior_Ici' nonempty_Iio
#align interior_Ici interior_Ici

@[simp]
theorem interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a :=
  interior_Ici' (α := αᵒᵈ) ha
#align interior_Iic' interior_Iic'

theorem interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = Iio a :=
  interior_Iic' nonempty_Ioi
#align interior_Iic interior_Iic

@[simp]
theorem interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) = Ioo a b := by
  rw [← Ici_inter_Iic, interior_inter, interior_Ici, interior_Iic, Ioi_inter_Iio]
#align interior_Icc interior_Icc

@[simp]
theorem Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x : α} :
    Icc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Icc, mem_interior_iff_mem_nhds]

@[simp]
theorem interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b) = Ioo a b := by
  rw [← Ici_inter_Iio, interior_inter, interior_Ici, interior_Iio, Ioi_inter_Iio]
#align interior_Ico interior_Ico

@[simp]
theorem Ico_mem_nhds_iff [NoMinOrder α] {a b x : α} : Ico a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ico, mem_interior_iff_mem_nhds]

@[simp]
theorem interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b) = Ioo a b := by
  rw [← Ioi_inter_Iic, interior_inter, interior_Ioi, interior_Iic, Ioi_inter_Iio]
#align interior_Ioc interior_Ioc

@[simp]
theorem Ioc_mem_nhds_iff [NoMaxOrder α] {a b x : α} : Ioc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ioc, mem_interior_iff_mem_nhds]

theorem closure_interior_Icc {a b : α} (h : a ≠ b) : closure (interior (Icc a b)) = Icc a b :=
  (closure_minimal interior_subset isClosed_Icc).antisymm <|
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)
#align closure_interior_Icc closure_interior_Icc

theorem Ioc_subset_closure_interior (a b : α) : Ioc a b ⊆ closure (interior (Ioc a b)) := by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b ⊆ Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)
#align Ioc_subset_closure_interior Ioc_subset_closure_interior

theorem Ico_subset_closure_interior (a b : α) : Ico a b ⊆ closure (interior (Ico a b)) := by
  simpa only [dual_Ioc] using Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)
#align Ico_subset_closure_interior Ico_subset_closure_interior

@[simp]
theorem frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier (Ici a) = {a} := by
  simp [frontier, ha]
#align frontier_Ici' frontier_Ici'

theorem frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {a} :=
  frontier_Ici' nonempty_Iio
#align frontier_Ici frontier_Ici

@[simp]
theorem frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier (Iic a) = {a} := by
  simp [frontier, ha]
#align frontier_Iic' frontier_Iic'

theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a} :=
  frontier_Iic' nonempty_Ioi
#align frontier_Iic frontier_Iic

@[simp]
theorem frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier (Ioi a) = {a} := by
  simp [frontier, closure_Ioi' ha, Iic_diff_Iio, Icc_self]
#align frontier_Ioi' frontier_Ioi'

theorem frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {a} :=
  frontier_Ioi' nonempty_Ioi
#align frontier_Ioi frontier_Ioi

@[simp]
theorem frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier (Iio a) = {a} := by
  simp [frontier, closure_Iio' ha, Iic_diff_Iio, Icc_self]
#align frontier_Iio' frontier_Iio'

theorem frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {a} :=
  frontier_Iio' nonempty_Iio
#align frontier_Iio frontier_Iio

@[simp]
theorem frontier_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a ≤ b) :
    frontier (Icc a b) = {a, b} := by simp [frontier, h, Icc_diff_Ioo_same]
#align frontier_Icc frontier_Icc

@[simp]
theorem frontier_Ioo {a b : α} (h : a < b) : frontier (Ioo a b) = {a, b} := by
  rw [frontier, closure_Ioo h.ne, interior_Ioo, Icc_diff_Ioo_same h.le]
#align frontier_Ioo frontier_Ioo

@[simp]
theorem frontier_Ico [NoMinOrder α] {a b : α} (h : a < b) : frontier (Ico a b) = {a, b} := by
  rw [frontier, closure_Ico h.ne, interior_Ico, Icc_diff_Ioo_same h.le]
#align frontier_Ico frontier_Ico

@[simp]
theorem frontier_Ioc [NoMaxOrder α] {a b : α} (h : a < b) : frontier (Ioc a b) = {a, b} := by
  rw [frontier, closure_Ioc h.ne, interior_Ioc, Icc_diff_Ioo_same h.le]
#align frontier_Ioc frontier_Ioc

theorem nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a ≤ b) :
    NeBot (𝓝[Ioi a] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Ioi' H₁]
#align nhds_within_Ioi_ne_bot' nhdsWithin_Ioi_neBot'

theorem nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Ioi a] b) :=
  nhdsWithin_Ioi_neBot' nonempty_Ioi H
#align nhds_within_Ioi_ne_bot nhdsWithin_Ioi_neBot

theorem nhdsWithin_Ioi_self_neBot' {a : α} (H : (Ioi a).Nonempty) : NeBot (𝓝[>] a) :=
  nhdsWithin_Ioi_neBot' H (le_refl a)
#align nhds_within_Ioi_self_ne_bot' nhdsWithin_Ioi_self_neBot'

instance nhdsWithin_Ioi_self_neBot [NoMaxOrder α] (a : α) : NeBot (𝓝[>] a) :=
  nhdsWithin_Ioi_neBot (le_refl a)
#align nhds_within_Ioi_self_ne_bot nhdsWithin_Ioi_self_neBot

theorem nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b ≤ c) :
    NeBot (𝓝[Iio c] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Iio' H₁]
#align nhds_within_Iio_ne_bot' nhdsWithin_Iio_neBot'

theorem nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Iio b] a) :=
  nhdsWithin_Iio_neBot' nonempty_Iio H
#align nhds_within_Iio_ne_bot nhdsWithin_Iio_neBot

theorem nhdsWithin_Iio_self_neBot' {b : α} (H : (Iio b).Nonempty) : NeBot (𝓝[<] b) :=
  nhdsWithin_Iio_neBot' H (le_refl b)
#align nhds_within_Iio_self_ne_bot' nhdsWithin_Iio_self_neBot'

instance nhdsWithin_Iio_self_neBot [NoMinOrder α] (a : α) : NeBot (𝓝[<] a) :=
  nhdsWithin_Iio_neBot (le_refl a)
#align nhds_within_Iio_self_ne_bot nhdsWithin_Iio_self_neBot

theorem right_nhdsWithin_Ico_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ico a b] b) :=
  (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)
#align right_nhds_within_Ico_ne_bot right_nhdsWithin_Ico_neBot

theorem left_nhdsWithin_Ioc_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioc a b] a) :=
  (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)
#align left_nhds_within_Ioc_ne_bot left_nhdsWithin_Ioc_neBot

theorem left_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] a) :=
  (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)
#align left_nhds_within_Ioo_ne_bot left_nhdsWithin_Ioo_neBot

theorem right_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] b) :=
  (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)
#align right_nhds_within_Ioo_ne_bot right_nhdsWithin_Ioo_neBot

theorem comap_coe_nhdsWithin_Iio_of_Ioo_subset (hb : s ⊆ Iio b)
    (hs : s.Nonempty → ∃ a < b, Ioo a b ⊆ s) : comap ((↑) : s → α) (𝓝[<] b) = atTop := by
  nontriviality
  haveI : Nonempty s := nontrivial_iff_nonempty.1 ‹_›
  rcases hs (nonempty_subtype.1 ‹_›) with ⟨a, h, hs⟩
  ext u; constructor
  · rintro ⟨t, ht, hts⟩
    obtain ⟨x, ⟨hxa : a ≤ x, hxb : x < b⟩, hxt : Ioo x b ⊆ t⟩ :=
      (mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset h).mp ht
    obtain ⟨y, hxy, hyb⟩ := exists_between hxb
    refine mem_of_superset (mem_atTop ⟨y, hs ⟨hxa.trans_lt hxy, hyb⟩⟩) ?_
    rintro ⟨z, hzs⟩ (hyz : y ≤ z)
    exact hts (hxt ⟨hxy.trans_le hyz, hb hzs⟩)
  · intro hu
    obtain ⟨x : s, hx : ∀ z, x ≤ z → z ∈ u⟩ := mem_atTop_sets.1 hu
    exact ⟨Ioo x b, Ioo_mem_nhdsWithin_Iio' (hb x.2), fun z hz => hx _ hz.1.le⟩
#align comap_coe_nhds_within_Iio_of_Ioo_subset comap_coe_nhdsWithin_Iio_of_Ioo_subset

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
theorem comap_coe_nhdsWithin_Ioi_of_Ioo_subset (ha : s ⊆ Ioi a)
    (hs : s.Nonempty → ∃ b > a, Ioo a b ⊆ s) : comap ((↑) : s → α) (𝓝[>] a) = atBot :=
  comap_coe_nhdsWithin_Iio_of_Ioo_subset (show ofDual ⁻¹' s ⊆ Iio (toDual a) from ha) fun h => by
    simpa only [OrderDual.exists, dual_Ioo] using hs h
#align comap_coe_nhds_within_Ioi_of_Ioo_subset comap_coe_nhdsWithin_Ioi_of_Ioo_subset

theorem map_coe_atTop_of_Ioo_subset (hb : s ⊆ Iio b) (hs : ∀ a' < b, ∃ a < b, Ioo a b ⊆ s) :
    map ((↑) : s → α) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop, Filter.map_bot, hb', nhdsWithin_empty]
  · rw [← comap_coe_nhdsWithin_Iio_of_Ioo_subset hb fun _ => hs a ha, map_comap_of_mem]
    rw [Subtype.range_val]
    exact (mem_nhdsWithin_Iio_iff_exists_Ioo_subset' ha).2 (hs a ha)
#align map_coe_at_top_of_Ioo_subset map_coe_atTop_of_Ioo_subset

theorem map_coe_atBot_of_Ioo_subset (ha : s ⊆ Ioi a) (hs : ∀ b' > a, ∃ b > a, Ioo a b ⊆ s) :
    map ((↑) : s → α) atBot = 𝓝[>] a := by
  -- the elaborator gets stuck without `(... : _)`
  refine (map_coe_atTop_of_Ioo_subset (show ofDual ⁻¹' s ⊆ Iio (toDual a) from ha)
    fun b' hb' => ?_ : _)
  simpa only [OrderDual.exists, dual_Ioo] using hs b' hb'
#align map_coe_at_bot_of_Ioo_subset map_coe_atBot_of_Ioo_subset

/-- The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourhoods filter at
the right endpoint in the ambient order. -/
theorem comap_coe_Ioo_nhdsWithin_Iio (a b : α) : comap ((↑) : Ioo a b → α) (𝓝[<] b) = atTop :=
  comap_coe_nhdsWithin_Iio_of_Ioo_subset Ioo_subset_Iio_self fun h =>
    ⟨a, nonempty_Ioo.1 h, Subset.refl _⟩
#align comap_coe_Ioo_nhds_within_Iio comap_coe_Ioo_nhdsWithin_Iio

/-- The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbourhoods filter at
the left endpoint in the ambient order. -/
theorem comap_coe_Ioo_nhdsWithin_Ioi (a b : α) : comap ((↑) : Ioo a b → α) (𝓝[>] a) = atBot :=
  comap_coe_nhdsWithin_Ioi_of_Ioo_subset Ioo_subset_Ioi_self fun h =>
    ⟨b, nonempty_Ioo.1 h, Subset.refl _⟩
#align comap_coe_Ioo_nhds_within_Ioi comap_coe_Ioo_nhdsWithin_Ioi

theorem comap_coe_Ioi_nhdsWithin_Ioi (a : α) : comap ((↑) : Ioi a → α) (𝓝[>] a) = atBot :=
  comap_coe_nhdsWithin_Ioi_of_Ioo_subset (Subset.refl _) fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩
#align comap_coe_Ioi_nhds_within_Ioi comap_coe_Ioi_nhdsWithin_Ioi

theorem comap_coe_Iio_nhdsWithin_Iio (a : α) : comap ((↑) : Iio a → α) (𝓝[<] a) = atTop :=
  comap_coe_Ioi_nhdsWithin_Ioi (α := αᵒᵈ) a
#align comap_coe_Iio_nhds_within_Iio comap_coe_Iio_nhdsWithin_Iio

@[simp]
theorem map_coe_Ioo_atTop {a b : α} (h : a < b) : map ((↑) : Ioo a b → α) atTop = 𝓝[<] b :=
  map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self fun _ _ => ⟨_, h, Subset.refl _⟩
#align map_coe_Ioo_at_top map_coe_Ioo_atTop

@[simp]
theorem map_coe_Ioo_atBot {a b : α} (h : a < b) : map ((↑) : Ioo a b → α) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self fun _ _ => ⟨_, h, Subset.refl _⟩
#align map_coe_Ioo_at_bot map_coe_Ioo_atBot

@[simp]
theorem map_coe_Ioi_atBot (a : α) : map ((↑) : Ioi a → α) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset (Subset.refl _) fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩
#align map_coe_Ioi_at_bot map_coe_Ioi_atBot

@[simp]
theorem map_coe_Iio_atTop (a : α) : map ((↑) : Iio a → α) atTop = 𝓝[<] a :=
  map_coe_Ioi_atBot (α := αᵒᵈ) _
#align map_coe_Iio_at_top map_coe_Iio_atTop

variable {l : Filter β} {f : α → β}

@[simp]
theorem tendsto_comp_coe_Ioo_atTop (h : a < b) :
    Tendsto (fun x : Ioo a b => f x) atTop l ↔ Tendsto f (𝓝[<] b) l := by
  rw [← map_coe_Ioo_atTop h, tendsto_map'_iff]; rfl
#align tendsto_comp_coe_Ioo_at_top tendsto_comp_coe_Ioo_atTop

@[simp]
theorem tendsto_comp_coe_Ioo_atBot (h : a < b) :
    Tendsto (fun x : Ioo a b => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioo_atBot h, tendsto_map'_iff]; rfl
#align tendsto_comp_coe_Ioo_at_bot tendsto_comp_coe_Ioo_atBot

-- Porting note (#11215): TODO: `simpNF` claims that `simp` can't use
-- this lemma to simplify LHS but it can
@[simp, nolint simpNF]
theorem tendsto_comp_coe_Ioi_atBot :
    Tendsto (fun x : Ioi a => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioi_atBot, tendsto_map'_iff]; rfl
#align tendsto_comp_coe_Ioi_at_bot tendsto_comp_coe_Ioi_atBot

-- Porting note (#11215): TODO: `simpNF` claims that `simp` can't use
-- this lemma to simplify LHS but it can
@[simp, nolint simpNF]
theorem tendsto_comp_coe_Iio_atTop :
    Tendsto (fun x : Iio a => f x) atTop l ↔ Tendsto f (𝓝[<] a) l := by
  rw [← map_coe_Iio_atTop, tendsto_map'_iff]; rfl
#align tendsto_comp_coe_Iio_at_top tendsto_comp_coe_Iio_atTop

@[simp]
theorem tendsto_Ioo_atTop {f : β → Ioo a b} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l (𝓝[<] b) := by
  rw [← comap_coe_Ioo_nhdsWithin_Iio, tendsto_comap_iff]; rfl
#align tendsto_Ioo_at_top tendsto_Ioo_atTop

@[simp]
theorem tendsto_Ioo_atBot {f : β → Ioo a b} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioo_nhdsWithin_Ioi, tendsto_comap_iff]; rfl
#align tendsto_Ioo_at_bot tendsto_Ioo_atBot

@[simp]
theorem tendsto_Ioi_atBot {f : β → Ioi a} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioi_nhdsWithin_Ioi, tendsto_comap_iff]; rfl
#align tendsto_Ioi_at_bot tendsto_Ioi_atBot

@[simp]
theorem tendsto_Iio_atTop {f : β → Iio a} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l (𝓝[<] a) := by
  rw [← comap_coe_Iio_nhdsWithin_Iio, tendsto_comap_iff]; rfl
#align tendsto_Iio_at_top tendsto_Iio_atTop

instance (x : α) [Nontrivial α] : NeBot (𝓝[≠] x) := by
  refine forall_mem_nonempty_iff_neBot.1 fun s hs => ?_
  obtain ⟨u, u_open, xu, us⟩ : ∃ u : Set α, IsOpen u ∧ x ∈ u ∧ u ∩ {x}ᶜ ⊆ s := mem_nhdsWithin.1 hs
  obtain ⟨a, b, a_lt_b, hab⟩ : ∃ a b : α, a < b ∧ Ioo a b ⊆ u := u_open.exists_Ioo_subset ⟨x, xu⟩
  obtain ⟨y, hy⟩ : ∃ y, a < y ∧ y < b := exists_between a_lt_b
  rcases ne_or_eq x y with (xy | rfl)
  · exact ⟨y, us ⟨hab hy, xy.symm⟩⟩
  obtain ⟨z, hz⟩ : ∃ z, a < z ∧ z < x := exists_between hy.1
  exact ⟨z, us ⟨hab ⟨hz.1, hz.2.trans hy.2⟩, hz.2.ne⟩⟩

/-- Let `s` be a dense set in a nontrivial dense linear order `α`. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` does not contain bottom/top elements of `α`. -/
theorem Dense.exists_countable_dense_subset_no_bot_top [Nontrivial α] {s : Set α} [SeparableSpace s]
    (hs : Dense s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∉ t) ∧ ∀ x, IsTop x → x ∉ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } ∪ { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact (diff_subset _ _).trans hts
  · exact htc.mono (diff_subset _ _)
  · exact htd.diff_finite ((subsingleton_isBot α).finite.union (subsingleton_isTop α).finite)
  · simp [hx]
  · simp [hx]
#align dense.exists_countable_dense_subset_no_bot_top Dense.exists_countable_dense_subset_no_bot_top

variable (α)

/-- If `α` is a nontrivial separable dense linear order, then there exists a
countable dense set `s : Set α` that contains neither top nor bottom elements of `α`.
For a dense set containing both bot and top elements, see
`exists_countable_dense_bot_top`. -/
theorem exists_countable_dense_no_bot_top [SeparableSpace α] [Nontrivial α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s := by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top
#align exists_countable_dense_no_bot_top exists_countable_dense_no_bot_top

end DenselyOrdered
