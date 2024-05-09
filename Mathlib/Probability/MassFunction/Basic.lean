import Mathlib.Topology.Instances.ENNReal
import Mathlib.Algebra.Order.Interval.Set.Instances

section

open scoped ENNReal

variable {α β γ : Type*}

theorem Set.inl_range_disjoint_inr_range :
    Disjoint (Set.range (Sum.inl (α := α))) (Set.range (Sum.inr (β := β))) :=
  Set.disjoint_iff_inter_eq_empty.mpr Set.range_inl_inter_range_inr

theorem tsum_sum_type [AddCommMonoid γ] [TopologicalSpace γ] [T2Space γ]
  [ContinuousAdd γ] {f : α ⊕ β → γ}
  (hfl : Summable (f ∘ ((↑) : Set.range (Sum.inl (α := α) (β := β)) → α ⊕ β)))
  (hfr : Summable (f ∘ ((↑) : Set.range (Sum.inr (α := α) (β := β)) → α ⊕ β)))
    : ∑' p : α ⊕ β, f p =
  ∑' a, f (.inl a) + ∑' b, f (.inr b) := by
  rw [← tsum_univ, ← Set.range_inl_union_range_inr]
  rw [tsum_union_disjoint (Set.inl_range_disjoint_inr_range) hfl hfr,
  tsum_range _ Sum.inl_injective, tsum_range _ Sum.inr_injective]

theorem tsum_sum_type_elim [AddCommGroup γ] [UniformSpace γ] [T2Space γ]
  [UniformAddGroup γ] [CompleteSpace γ]
  [ContinuousAdd γ] {f : α → γ} {g : β → γ} (hfg : Summable (Sum.elim f g)) :
    ∑' p : α ⊕ β, Sum.elim f g p = ∑' a, f a + ∑' b, g b := by
  simp_rw [tsum_sum_type (hfg.subtype _) (hfg.subtype _), Sum.elim_inl, Sum.elim_inr]

protected theorem ENNReal.tsum_sum_type {f : α ⊕ β → ℝ≥0∞} :
    ∑' p : α ⊕ β, f p = ∑' a, f (.inl a) + ∑' b, f (.inr b) :=
  tsum_sum_type ENNReal.summable ENNReal.summable

protected theorem ENNReal.tsum_sum_unit_type {f : α ⊕ Unit → ℝ≥0∞} :
    ∑' p : α ⊕ Unit, f p = ∑' a, f (.inl a) + f (.inr ()) := by
  rw [ENNReal.tsum_sum_type, tsum_eq_single () (fun ⟨⟩ h => absurd rfl h)]

protected theorem ENNReal.tsum_unit_type_sum {f : Unit ⊕ β → ℝ≥0∞} :
    ∑' p : Unit ⊕ β, f p = f (.inl ()) + ∑' b, f (.inr b) := by
  rw [ENNReal.tsum_sum_type, tsum_eq_single () (fun ⟨⟩ h => absurd rfl h)]

protected theorem ENNReal.tsum_sum_type_elim {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} :
    ∑' p : α ⊕ β, Sum.elim f g p = ∑' a, f a + ∑' b, g b := by
  simp_rw [ENNReal.tsum_sum_type, Sum.elim_inl, Sum.elim_inr]

protected theorem ENNReal.tsum_sum_unit_type_elim {f : α → ℝ≥0∞} {g : Unit → ℝ≥0∞} :
    ∑' p : α ⊕ Unit, Sum.elim f g p = ∑' a, f a + g () := by
  simp_rw [ENNReal.tsum_sum_unit_type, Sum.elim_inl, Sum.elim_inr]

protected theorem ENNReal.tsum_unit_type_sum_elim {f : Unit → ℝ≥0∞} {g : β → ℝ≥0∞} :
    ∑' p : Unit ⊕ β , Sum.elim f g p = f () + ∑' a, g a := by
  simp_rw [ENNReal.tsum_unit_type_sum, Sum.elim_inl, Sum.elim_inr]

end

section

variable {α : Type*} {a : α} {s : Set α}

@[simp]
theorem Set.inter_singleton_of_mem (h : a ∈ s): s ∩ {a} = {a} :=
  Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)

@[simp]
theorem Set.singleton_inter_of_mem (h : a ∈ s) : s ∩ {a} = {a} :=
  Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)

end

section

variable {α β : Type*} (f : α → β) (a a' : α) (b b' : β)

theorem ite_eq_apply_subst [Decidable (a = a')] :
    (if a = a' then f a else b) = (if a = a' then f a' else b) :=
  ite_congr rfl (congrArg fun a ↦ f a) (congrFun rfl)

theorem ite_eq_comm [Decidable (a = a')] [Decidable (a' = a)] :
    (if a = a' then b else b') = (if a' = a then b else b') :=
  ite_congr (by rw [eq_iff_iff, eq_comm]) (fun _ => rfl) (fun _ => rfl)

end

section

variable {α β : Type*} {b b' : β} {f : β → α} [One α] [Decidable (b' = b)] [Decidable (b = b')]

@[to_additive]
theorem Set.mulIndicator_singleton_apply_self : Set.mulIndicator {b} f b = f b :=
  mulIndicator_of_mem rfl _

@[to_additive (attr := simp)]
theorem Set.mulIndicator_singleton_apply_of_ne (h : b' ≠ b) :
    Set.mulIndicator {b} f b' = 1 :=
  mulIndicator_of_not_mem (Set.eq_of_mem_singleton.mt h) _

@[to_additive (attr := simp)]
theorem Set.mulIndicator_singleton_apply_of_ne' (h : b ≠ b') :
    Set.mulIndicator {b} f b' = 1 :=
  mulIndicator_of_not_mem (Set.eq_of_mem_singleton.mt h.symm) _

@[to_additive (attr := simp)]
theorem Set.mulIndicator_singleton_apply :
    Set.mulIndicator {b} f b' = if b' = b then f b else 1 := by
  rcases (eq_or_ne b' b) with (rfl | ha)
  · rw [if_pos rfl, mulIndicator_singleton_apply_self]
  · rw [if_neg ha, mulIndicator_singleton_apply_of_ne ha]

@[to_additive]
theorem Set.mulIndicator_singleton_apply' :
    Set.mulIndicator {b} f b' = if b = b' then f b else 1 := by
  simp
  exact (ite_eq_comm b' b (f b) 1)

@[to_additive]
theorem Set.mulIndicator_singleton_comm {α β : Type*} {b b' : β} {f : β → α} [One α] :
    ({b} : Set β).mulIndicator f b' = ({b'} : Set β).mulIndicator f b := by
  classical simp_rw [mulIndicator_singleton_apply, ite_eq_comm, ite_eq_apply_subst _ b]

end

section

variable {α β : Type*} [CommMonoid α] [TopologicalSpace α]

@[to_additive (attr := simp)]
theorem tprod_ite_eq' (a : α) (b : β) [DecidablePred (b = ·)] :
    ∏' b', (if b = b' then a else 1) = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive (attr := simp)]
theorem tprod_ite_eq_dep (b : β) [DecidablePred (· = b)] (f : β → α) :
    ∏' b', (if b' = b then f b' else 1) = f b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]
theorem tprod_ite_eq_dep' (b : β) [DecidablePred (b = ·)] (f : β → α) :
    ∏' b', (if b = b' then f b' else 1) = f b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive (attr := simp)]
theorem tprod_dite_eq (b : β) [DecidablePred (· = b)] (f : (b' : β) → b' = b → α) :
    ∏' b', (if h : b' = b then f b' h else 1) = f b rfl := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]
theorem tprod_dite_eq' (b : β) [DecidablePred (b = ·)] (f : (b' : β) → b = b' → α) :
    ∏' b', (if h : b = b' then f b' h else 1) = f b rfl := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive (attr := simp)]
theorem tprod_const_singleton_mulIndicator (b : β) (f : β → α) :
    ∏' (b' : β), ({b} : Set β).mulIndicator f b' = f b := by
  classical simp_rw [Set.mulIndicator_singleton_apply]
  simp_rw [tprod_ite_eq]

@[to_additive (attr := simp)]
theorem tprod_singleton_mulIndicator (b : β) (f : β → α) :
    ∏' (b' : β), ({b'} : Set β).mulIndicator f b = f b := by
  classical simp_rw [Set.mulIndicator_singleton_apply]
  simp_rw [tprod_ite_eq_dep']

end

section

variable {α β : Type*} [Semiring α] [TopologicalSpace α]

@[simp]
theorem tsum_singleton_indicator_mul_left_right :
    ∀ {b f} (g h : β → β → α),
  ∑' (b' : β), h b b' * ({b} : Set β).indicator f b' * g b b' = h b b * f b * g b b := by
  classical simp_rw [Set.indicator_singleton_apply]
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul, tsum_ite_eq_dep, implies_true]

@[simp]
theorem tsum_const_singleton_indicator_mul_left_right :
    ∀ {b f} (g h : β → β → α),
  ∑' (b' : β), h b b' * ({b'} : Set β).indicator f b * g b b' = h b b * f b * g b b := by
  classical simp_rw [Set.indicator_singleton_apply]
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul, tsum_ite_eq_dep', implies_true]

@[simp]
theorem tsum_singleton_indicator_mul_left :
    ∀ {b f} (g : β → β → α),
  ∑' (b' : β), g b b' * ({b'} : Set β).indicator f b = g b b * f b := by
  classical simp only [Set.indicator_singleton_apply, mul_ite,
  mul_zero, tsum_ite_eq_dep', implies_true]

@[simp]
theorem tsum_singleton_indicator_mul_right :
    ∀ {b f} (g : β → β → α),
  ∑' (b' : β), ({b'} : Set β).indicator f b * g b b'  = f b * g b b := by
  classical simp_rw [Set.indicator_singleton_apply]
  simp only [ite_mul, zero_mul, tsum_ite_eq_dep', implies_true]

end

open BigOperators ENNReal NNReal

namespace MassFunction

universe u v

structure MF (α : Type u) where
  toFun : α → ℝ≥0∞

structure FMF (α : Type u) where
  toFun : α → ℝ≥0∞
  mass_lt_top' : tsum (toFun) < ∞

structure SPMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_le_one' : tsum (toFun) ≤ 1

structure PMF (α : Type u) where
  toFun : α → ℝ≥0∞
  mass_eq_one' : tsum (toFun) = 1

abbrev MFLike (M : Type u → Type v) (α : Type u) := FunLike (M α) α ℝ≥0∞

variable {M : Type u → Type v} [∀ α, MFLike M α] {α : Type u} {μ ν : M α} {a b : α} {s t : Set α}

@[ext] theorem MFLike.ext {μ ν : M α} (h : ∀ x, μ x = ν x) : μ = ν :=
  DFunLike.ext _ _ (by assumption)

noncomputable def mass (μ : M α) := tsum μ

noncomputable def support (μ : M α) := (⇑μ).support

noncomputable def massOf (μ : M α) (s : Set α) := tsum (s.indicator μ)

section Mass

theorem mass_eq_tsum_coeFn : mass μ = ∑' i, ⇑μ i := rfl

theorem mass_eq_zero_iff : mass μ = 0 ↔ ∀ a : α, μ a = 0 := ENNReal.tsum_eq_zero

theorem mass_ne_zero_iff : mass μ ≠ 0 ↔ ∃ a : α, μ a ≠ 0 :=
  ENNReal.tsum_eq_zero.not.trans not_forall

end Mass

section Apply

theorem apply_le_mass : μ a ≤ mass μ := ENNReal.le_tsum a

theorem apply_mem_Iic : μ a ∈ Set.Iic (mass μ) := apply_le_mass

end Apply

section Support

theorem support_eq_support_coeFn : support μ = (⇑μ).support := rfl

@[simp]
theorem mem_support_iff : a ∈ support μ ↔ μ a ≠ 0 := Iff.rfl

theorem mem_support_iff' : a ∈ support μ ↔ 0 < μ a :=
  mem_support_iff.trans pos_iff_ne_zero.symm

@[simp]
theorem apply_ne_zero_of_mem_support (ha : a ∈ support μ) : μ a ≠ 0 :=
  mem_support_iff.mp ha

@[simp]
theorem mem_support_of_apply_ne_zero (ha : μ a ≠ 0) : a ∈ support μ :=
  mem_support_iff.mpr ha

@[simp]
theorem apply_pos_of_mem_support (ha : a ∈ support μ) : 0 < μ a :=
  mem_support_iff'.mp ha

@[simp]
theorem mem_support_of_apply_pos_zero (ha : 0 < μ a) : a ∈ support μ :=
  mem_support_iff'.mpr ha

theorem nmem_support_iff : a ∉ support μ ↔ μ a = 0 := Function.nmem_support

theorem apply_eq_zero_of_nmem_support (ha : a ∉ support μ) : μ a = 0 :=
  nmem_support_iff.mp ha

theorem nmem_support_of_apply_eq_zero (ha : μ a = 0) : a ∉ support μ :=
  nmem_support_iff.mpr ha

@[simp]
theorem indicator_support : (support μ).indicator μ = μ := Set.indicator_support

@[simp]
theorem support_indicator : (s.indicator μ).support = s ∩ support μ :=
  Set.support_indicator

theorem support_disjoint_iff : Disjoint (support μ) s ↔ ∀ a ∈ s, μ a = 0 :=
  Function.support_disjoint_iff

theorem disjoint_support_iff : Disjoint s (support μ) ↔ ∀ a ∈ s, μ a = 0 :=
  Function.disjoint_support_iff

theorem support_eq_empty_iff : support μ = ∅ ↔ ∀ a, μ a = 0 :=
  by simp_rw [Set.eq_empty_iff_forall_not_mem, nmem_support_iff]

theorem support_nonempty_iff : (support μ).Nonempty ↔ ∃ a : α, μ a ≠ 0 :=
  by simp_rw [Set.Nonempty, mem_support_iff]

theorem mass_eq_zero_iff' : mass μ = 0 ↔ support μ = ∅ :=
  mass_eq_zero_iff.trans support_eq_empty_iff.symm

theorem mass_ne_zero_iff' : mass μ ≠ 0 ↔ (support μ).Nonempty :=
  mass_ne_zero_iff.trans support_nonempty_iff.symm

end Support

section MassOf

theorem massOf_eq_tsum_indicator_coeFn : massOf μ s = ∑' i, s.indicator ⇑μ i := rfl

theorem massOf_eq_tsum_ite [∀ a, Decidable (a ∈ s)] :
  massOf μ s = ∑' i, if i ∈ s then μ i else 0 := tsum_congr (fun _ => Set.indicator_apply _ _ _)

@[simp]
theorem massOf_fintype [Fintype α] :
    massOf μ s = ∑ i, s.indicator μ i := tsum_fintype _

theorem massOf_finset {s : Finset α} :
    massOf μ s = ∑ i in s, μ i := (sum_eq_tsum_indicator _ _).symm

theorem massOf_le_mass : massOf μ s ≤ mass μ :=
  ENNReal.tsum_le_tsum (s.indicator_le_self _)

theorem massOf_support : massOf μ (support μ) = mass μ :=
  le_antisymm massOf_le_mass
  (ENNReal.tsum_le_tsum (fun _ => by simp_rw [indicator_support, le_refl]))

theorem massOf_univ : massOf μ (Set.univ) = mass μ :=
  tsum_congr (fun _ => congr_fun (Set.indicator_univ μ) _)

theorem massOf_empty : massOf μ ∅ = 0 :=
  ENNReal.tsum_eq_zero.mpr (fun _ => congr_fun (Set.indicator_empty μ) _)

theorem massOf_mono (hst : s ≤ t) : massOf μ s ≤ massOf μ t :=
  ENNReal.tsum_le_tsum (Set.indicator_le_indicator_of_subset hst (fun _ => zero_le _))

theorem massOf_eq_tsum_subtype : massOf μ s = ∑' i : s, μ i := (tsum_subtype _ _).symm

theorem massOf_iUnion_nat {s : ℕ → Set α} :
    massOf μ (⋃ i, s i) ≤ ∑' i, massOf μ (s i) := by
  simp_rw [massOf_eq_tsum_subtype]
  exact ENNReal.tsum_iUnion_le_tsum _ _

@[simp]
theorem massOf_singleton : massOf μ {a} = μ a := by
  rw [massOf_eq_tsum_subtype, tsum_singleton]

theorem massOf_union_disjoint (hst : Disjoint s t) :
    massOf μ (s ∪ t) = massOf μ s + massOf μ t := by
  simp_rw [massOf_eq_tsum_subtype]
  exact tsum_union_disjoint hst ENNReal.summable ENNReal.summable

theorem massOf_pair_disjoint (hab : a ≠ b) : massOf μ {a, b} = μ a + μ b := by
  simp_rw [← massOf_singleton]
  exact massOf_union_disjoint (fun _ ha hb _ hc => (hab ((ha hc).symm.trans (hb hc))).elim)

theorem massOf_caratheodory : massOf μ t = massOf μ (t ∩ s) + massOf μ (t \ s) := by
  nth_rewrite 1 [← Set.inter_union_diff t s]
  exact massOf_union_disjoint Set.disjoint_sdiff_inter.symm

theorem massOf_injective : (massOf : M α → Set α → ℝ≥0∞).Injective := fun d₁ d₂ h => by
  simp_rw [DFunLike.ext_iff, ← massOf_singleton, h, implies_true]

theorem massOf_inj : massOf μ = massOf ν ↔ μ = ν := massOf_injective.eq_iff

theorem massOf_eq_zero_iff : massOf μ s = 0 ↔ ∀ a ∈ s, μ a = 0 := by
  refine' ENNReal.tsum_eq_zero.trans _
  simp_rw [Set.indicator_apply_eq_zero]

theorem massOf_eq_zero_iff_support_disjoint : massOf μ s = 0 ↔ Disjoint (support μ) s := by
  simp_rw [massOf_eq_zero_iff, support_disjoint_iff]

theorem massOf_eq_zero_iff_disjoint_support : massOf μ s = 0 ↔ Disjoint s (support μ) := by
  simp_rw [massOf_eq_zero_iff, disjoint_support_iff]

theorem massOf_eq_zero_iff_mem_nmem_support : massOf μ s = 0 ↔ ∀ a ∈ s, a ∉ support μ := by
  simp_rw [massOf_eq_zero_iff_support_disjoint, Set.disjoint_right]

theorem massOf_eq_zero_iff_mem_support_nmem : massOf μ s = 0 ↔ ∀ a ∈ support μ, a ∉ s := by
  simp_rw [massOf_eq_zero_iff_support_disjoint, Set.disjoint_left]

theorem massOf_ne_zero_iff : massOf μ s ≠ 0 ↔ ∃ a ∈ s, μ a ≠ 0 := by
  simp_rw [ne_eq, massOf_eq_zero_iff_disjoint_support, Set.not_disjoint_iff,
  mem_support_iff]

theorem massOf_ne_zero_iff_support_inter_nonempty :
    massOf μ s ≠ 0 ↔ ((support μ) ∩ s).Nonempty := by
  simp_rw [ne_eq, massOf_eq_zero_iff_support_disjoint, Set.not_disjoint_iff_nonempty_inter]

theorem massOf_ne_zero_iff_inter_suppport_nonempty :
    massOf μ s ≠ 0 ↔ (s ∩ (support μ)).Nonempty := by
  simp_rw [ne_eq, massOf_eq_zero_iff_disjoint_support, Set.not_disjoint_iff_nonempty_inter]

theorem massOf_ne_zero_iff_exists_mem_mem_support : massOf μ s ≠ 0 ↔ ∃ a ∈ s, a ∈ support μ := by
  simp_rw [massOf_ne_zero_iff_support_inter_nonempty, Set.inter_nonempty_iff_exists_right]

theorem massOf_ne_zero_iff_exists_mem_support_mem : massOf μ s ≠ 0 ↔ ∃ a ∈ support μ, a ∈ s := by
  simp_rw [massOf_ne_zero_iff_support_inter_nonempty, Set.inter_nonempty_iff_exists_left]

@[simp]
theorem massOf_apply_inter_support :
    massOf μ (s ∩ support μ) = massOf μ s :=
  tsum_congr (fun _ => congr_fun (Set.indicator_inter_support _ _) _)

theorem massOf_mono' (h : s ∩ support μ ⊆ t) :
    massOf μ s ≤ massOf μ t := massOf_apply_inter_support.symm.le.trans (massOf_mono h)

theorem massOf_apply_eq_of_inter_support_eq (h : s ∩ support μ = t ∩ support μ) :
    massOf μ s = massOf μ t :=
  le_antisymm (massOf_mono' (h.symm ▸ Set.inter_subset_left t (support μ)))
    (massOf_mono' (h ▸ Set.inter_subset_left s (support μ)))

theorem apply_eq_mass_of_support_empty (ha : support μ = ∅) :
    ∀ a, μ a = mass μ := fun a => by
  rw [support_eq_empty_iff] at ha
  rwa [ha, eq_comm, mass_eq_zero_iff]

theorem apply_eq_mass_iff_of_nmem_support (had : a ∉ support μ) :
    μ a = mass μ ↔ support μ = ∅ := by
  rw [apply_eq_zero_of_nmem_support had, support_eq_empty_iff, eq_comm, mass_eq_zero_iff]

theorem apply_eq_mass_of_support_singleton (ha : support μ = {a}) :
    μ a = mass μ := by
  rw [← massOf_singleton, ← massOf_support]
  exact massOf_apply_eq_of_inter_support_eq (ha ▸ rfl)

theorem exists_apply_eq_mass_of_support_subsingleton [Inhabited α]
    (ha : (support μ).Subsingleton) : ∃ a, μ a = mass μ := by
  rcases ha.eq_empty_or_singleton with (ha | ⟨a, ha⟩)
  · exact ⟨_, apply_eq_mass_of_support_empty ha default⟩
  · exact ⟨_, apply_eq_mass_of_support_singleton ha⟩

end MassOf

class ZeroNull (M : Type u → Type v) [∀ α, MFLike M α] (α : Type u) extends Zero (M α) where
(coeFn_zero' : ⇑(0 : M α) = 0)


namespace ZeroNull

variable [ZeroNull M α] {a : α} {s : Set α} {μ : M α}

instance : Zero (M α) := inferInstance

@[simp]
theorem coeFn_zero : ⇑(0 : M α) = 0 := ZeroNull.coeFn_zero'

@[simp]
theorem zero_apply : ((0 : M α) a = 0) := by rw [coeFn_zero, Pi.zero_apply]

@[simp]
theorem mass_zero : mass (0 : M α) = 0 := by
  simp_rw [mass_eq_zero_iff, zero_apply, implies_true]

theorem zero_of_mass_zero (h : mass μ = 0) : μ = 0 := by
  simp_rw [DFunLike.ext_iff, zero_apply, ← mass_eq_zero_iff]
  exact h

theorem mass_eq_empty_iff_zero : mass μ = 0 ↔ μ = 0 :=
  ⟨zero_of_mass_zero, fun h => h ▸ mass_zero⟩

@[simp]
theorem support_zero : support (0 : M α) = ∅ := by
  simp_rw [support_eq_empty_iff, zero_apply, implies_true]

theorem zero_of_support_eq_empty (h : support μ = ∅) : μ = 0 := by
  simp_rw [DFunLike.ext_iff, zero_apply, ← support_eq_empty_iff]
  exact h

theorem support_eq_empty_iff_zero : support μ = ∅ ↔ μ = 0 :=
  ⟨zero_of_support_eq_empty, fun h => h ▸ support_zero⟩

@[simp]
theorem massOf_zero : massOf (0 : M α) s = 0 :=
  massOf_eq_zero_iff.mpr (fun _ _ => zero_apply)

end ZeroNull

class FMFClass (M : Type u → Type v) [∀ α, MFLike M α] : Prop :=
  (mass_lt_top : ∀ {α} (μ : M α), mass μ < ∞)

section FiniteMassFunction

variable [FMFClass M]

section Mass

theorem mass_lt_top : mass μ < ∞ := FMFClass.mass_lt_top _

theorem mass_ne_top : mass μ ≠ ∞ := mass_lt_top.ne_top

theorem mass_mem_Iio : mass μ ∈ Set.Iio ∞ := mass_lt_top

end Mass

section Apply

theorem apply_lt_top : μ a < ∞ := apply_le_mass.trans_lt mass_lt_top

theorem apply_ne_top : μ a ≠ ∞ := apply_lt_top.ne

theorem apply_mem_Iio : μ a ∈ Set.Iio ∞ := apply_lt_top

end Apply

section Support

@[simp]
theorem support_countable : (support μ).Countable :=
  Summable.countable_support_ennreal mass_ne_top

theorem apply_lt_mass_of_support_nontrivial (h : (support μ).Nontrivial) :
    ∀ a, μ a < mass μ := fun a => by
  rcases h.exists_ne a with ⟨b, hbd, hba⟩
  refine' (massOf_le_mass (s := {b, a})).trans_lt' _
  rw [massOf_pair_disjoint hba, add_comm]
  exact ENNReal.lt_add_right apply_ne_top (apply_ne_zero_of_mem_support hbd)

theorem apply_ne_mass_of_support_nontrivial (h : (support μ).Nontrivial) :
    ∀ a, μ a ≠ mass μ := fun a => (apply_lt_mass_of_support_nontrivial h a).ne

theorem support_subsingleton_of_apply_eq_mass (h : ∃ a, μ a = mass μ) :
    (support μ).Subsingleton := by
  rcases h with ⟨a, ha⟩
  by_contra hd
  rw [Set.not_subsingleton_iff] at hd
  exact apply_ne_mass_of_support_nontrivial hd a ha

theorem support_subsingleton_iff_exists_apply_eq_mass [Inhabited α]  :
    (support μ).Subsingleton ↔ ∃ a, μ a = mass μ :=
  ⟨exists_apply_eq_mass_of_support_subsingleton, support_subsingleton_of_apply_eq_mass⟩

theorem support_nontrivial_iff_apply_ne_mass [Inhabited α] :
    (support μ).Nontrivial ↔ ∀ a, μ a ≠ mass μ := by
  rw [← Set.not_subsingleton_iff, support_subsingleton_iff_exists_apply_eq_mass, not_exists]

theorem support_nontrivial_iff_apply_lt_mass [Inhabited α] :
    (support μ).Nontrivial ↔ ∀ a, μ a < mass μ := by
  rw [support_nontrivial_iff_apply_ne_mass]
  exact ⟨fun h a => apply_le_mass.lt_of_ne (h a), fun h a => (h a).ne⟩

theorem apply_eq_mass_iff_of_mem_support (had : a ∈ support μ) :
    μ a = mass μ ↔ support μ = {a} := by
  refine' ⟨fun ha => _, fun ha => _⟩
  · rcases Set.eq_singleton_or_nontrivial had with (had | had)
    · assumption
    · exact (apply_ne_mass_of_support_nontrivial had a ha).elim
  · exact apply_eq_mass_of_support_singleton ha

end Support

section MassOf

@[simp]
theorem massOf_lt_top : massOf μ s < ∞ := massOf_le_mass.trans_lt mass_lt_top

@[simp]
theorem massOf_ne_top : massOf μ s ≠ ∞ := massOf_lt_top.ne

theorem massOf_lt_mass_of_support_diff_nonempty
    (h : (support μ \ s).Nonempty) : massOf μ s < mass μ := by
  rcases h with ⟨a, haf, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) massOf_ne_top
    (fun a => (Set.indicator_le (fun _ _ => le_rfl) a)) _
  rw [Set.indicator_of_not_mem has, zero_lt_iff]
  exact apply_ne_zero_of_mem_support haf

theorem massOf_lt_massOf_of_support_inter_diff_nonempty_of_lt
    (h : ((support μ ∩ t) \ s).Nonempty) (hst : s < t) : massOf μ s < massOf μ t := by
  rcases h with ⟨a, ⟨haf, hat⟩, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) massOf_ne_top
    (fun b => (Set.indicator_le_indicator_of_subset hst.le (fun _ => zero_le _) _)) _
  rw [Set.indicator_of_not_mem has, Set.indicator_of_mem hat, zero_lt_iff]
  exact apply_ne_zero_of_mem_support haf

theorem apply_massOf_eq_mass_iff : massOf μ s = mass μ ↔ support μ ⊆ s := by
  refine' ⟨fun h => _, fun h => _⟩
  · by_contra h'
    rw [Set.not_subset] at h'
    exact ((massOf_lt_mass_of_support_diff_nonempty h').ne h)
  · rw [← massOf_support]
    refine' massOf_apply_eq_of_inter_support_eq _
    rwa [Set.inter_self, Set.inter_eq_right]

end MassOf

end FiniteMassFunction

class SPMFClass (M : Type u → Type v) [∀ α, MFLike M α] : Prop :=
  (mass_le_one : ∀ {α} (μ : M α), mass μ ≤ 1)

instance SPMFClass.toFMFClass [SPMFClass M] : FMFClass M  where
  mass_lt_top f := (mass_le_one f).trans_lt one_lt_top

section SubProbabilityMassFunction

variable [SPMFClass M]

section Mass

@[simp]
theorem mass_le_one : mass μ ≤ 1 := SPMFClass.mass_le_one _

end Mass

section Apply

theorem apply_le_one : μ a ≤ 1 := apply_le_mass.trans mass_le_one

theorem apply_mem_Icc : μ a ∈ Set.Icc 0 1 := ⟨zero_le _, apply_le_one⟩

end Apply

section MassOf

theorem massOf_le_one : massOf μ s ≤ 1 := massOf_le_mass.trans mass_le_one

end MassOf

end SubProbabilityMassFunction

class PMFClass (M : Type u → Type v) [∀ α, MFLike M α] : Prop :=
  (mass_eq_one : ∀ {α} (μ : M α), mass μ = 1)

instance PMFClass.toSPMFClass [PMFClass M] : SPMFClass M where
  mass_le_one f := (mass_eq_one f).le

section ProbabilityMassFunction

variable [PMFClass M]

section Mass

@[simp]
theorem mass_eq_one : mass μ = 1 := PMFClass.mass_eq_one _

theorem mass_ne_zero : mass μ ≠ 0 := mass_eq_one.trans_ne one_ne_zero

end Mass

section Support

@[simp]
theorem support_nonempty : (support μ).Nonempty :=
  mass_ne_zero_iff'.mp mass_ne_zero

end Support

section HasSum

theorem hasSum_coe_one : HasSum μ 1 := (Summable.hasSum_iff ENNReal.summable).mpr mass_eq_one

end HasSum

end ProbabilityMassFunction

namespace MF

variable {r : ℝ≥0∞} {μ : MF α} {a : α} {s : Set α}

instance instMFLike : MFLike MF α := ⟨fun μ => μ.toFun, fun ⟨_⟩ ⟨_⟩ _ => by congr⟩

@[ext] theorem ext {μ ν : MF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZeroNull (α : Type u) : ZeroNull MF α where
  zero := ⟨0⟩
  coeFn_zero' := rfl

instance : Inhabited (MF α) := ⟨0⟩

noncomputable instance : SMul ℝ≥0∞ (MF α) where
  smul r μ := ⟨r • ⇑μ⟩

theorem coeFn_smul : ⇑(r • μ) = r • ⇑μ := rfl

theorem smul_apply : (r • μ) a = r * (μ a) := rfl

theorem mass_smul : mass (r • μ) = r * mass μ := ENNReal.tsum_mul_left

theorem support_smul : support (r • μ) ⊆ support μ := Function.support_const_smul_subset _ _

theorem support_smul_of_ne_zero (hr : r ≠ 0) : support (r • μ) = support μ :=
  Function.support_const_smul_of_ne_zero _ _ hr

@[simp]
theorem massOf_smul : massOf (r • μ) s = r • massOf μ s := by
  simp_rw [massOf_eq_tsum_indicator_coeFn, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0∞ (MF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, ZeroNull.coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end MF

namespace FMF

variable {r : ℝ≥0} {μ : FMF α} {a : α} {s : Set α}

instance instMFLike : MFLike FMF α:= ⟨fun μ => μ.toFun, fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr⟩

instance instFMFClass : FMFClass FMF where mass_lt_top := FMF.mass_lt_top'

@[ext] theorem ext {μ ν : FMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZeroNull (α : Type u) : ZeroNull FMF α where
  zero := ⟨0, tsum_zero.trans_lt zero_lt_top⟩
  coeFn_zero' := rfl

instance : Inhabited (FMF α) := ⟨0⟩

noncomputable instance : SMul ℝ≥0 (FMF α) where
  smul r μ := ⟨r • ⇑μ,
    ENNReal.tsum_mul_left.trans_lt (ENNReal.mul_lt_top ENNReal.coe_ne_top mass_ne_top)⟩

theorem coeFn_smul : ⇑(r • μ) = r • ⇑μ := rfl

theorem smul_apply : (r • μ) a = r * (μ a) := rfl

theorem mass_smul : mass (r • μ) = r * mass μ := ENNReal.tsum_mul_left

theorem support_smul : support (r • μ) ⊆ support μ := Function.support_const_smul_subset _ _

theorem support_smul_of_ne_zero (hr : r ≠ 0) : support (r • μ) = support μ :=
  Function.support_const_smul_of_ne_zero _ _ hr

@[simp]
theorem massOf_smul : massOf (r • μ) s = r • massOf μ s := by
  simp_rw [massOf_eq_tsum_indicator_coeFn, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0 (FMF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, ZeroNull.coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end FMF

namespace SPMF

variable {r : (Set.Icc 0 1 : Set ℝ≥0∞)} {μ : SPMF α} {a : α} {s : Set α}

instance instMFLike : MFLike SPMF α := ⟨fun μ => μ.toFun, fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr⟩

instance instSPMFClass : SPMFClass SPMF where mass_le_one := SPMF.mass_le_one'

@[ext] theorem ext {μ ν : SPMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZeroNull (α : Type u) : ZeroNull SPMF α where
  zero := ⟨0, tsum_zero.trans_le zero_le_one⟩
  coeFn_zero' := rfl

instance : Inhabited (SPMF α) := ⟨0⟩

noncomputable instance :
    SMul (Set.Icc 0 1 : Set ℝ≥0∞) (SPMF α) where
  smul r μ := ⟨(r : ℝ≥0∞) • ⇑μ, ENNReal.tsum_mul_left.trans_le (mul_le_one' r.2.2 mass_le_one)⟩

theorem coeFn_smul : ⇑(r • μ) = (r : ℝ≥0∞) • ⇑μ := rfl

theorem smul_apply : (r • μ) a = r * (μ a) := rfl

theorem mass_smul : mass (r • μ) = r * mass μ := ENNReal.tsum_mul_left

theorem support_smul : support (r • μ) ⊆ support μ := Function.support_const_smul_subset _ _

theorem support_smul_of_ne_zero (hr : r ≠ 0) : support (r • μ) = support μ :=
  Function.support_const_smul_of_ne_zero _ _ (Set.Icc.coe_ne_zero.mpr hr)

@[simp]
theorem massOf_smul : massOf (r • μ) s = (r : ℝ≥0∞) • massOf μ s := by
  simp_rw [massOf_eq_tsum_indicator_coeFn, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0 (FMF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, ZeroNull.coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end SPMF

namespace PMF

instance instMFLike : MFLike PMF α := ⟨fun μ => μ.toFun, fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr⟩

instance instPMFClass : PMFClass PMF where mass_eq_one := PMF.mass_eq_one'

@[ext] theorem ext {μ ν : PMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

end PMF

section Coe

def castMF (μ : M α) : MF α := ⟨μ⟩

def castFMF (μ : M α) (h : mass μ < ⊤) : FMF α := ⟨μ, h⟩

def castSPMF (μ : M α) (h : mass μ ≤ 1) : SPMF α := ⟨μ, h⟩

def castPMF (μ : M α) (h : mass μ = 1) : PMF α := ⟨μ, h⟩

instance : CoeHead (M α) (MF α) := ⟨castMF⟩

instance [FMFClass M] : CoeHead (M α) (FMF α) := ⟨(castFMF · mass_lt_top)⟩

instance [SPMFClass M] : CoeHead (M α) (SPMF α) := ⟨(castSPMF · mass_le_one)⟩

instance [PMFClass M] : CoeHead (M α) (PMF α) := ⟨(castPMF · mass_eq_one)⟩

@[simp] theorem castMF_MF (μ : MF α) : (castMF μ) = μ := rfl
@[simp] theorem castFMF_FMF_eq (μ : FMF α) (h := mass_lt_top) : (castFMF μ h) = μ := rfl
@[simp] theorem castSPMF_SPMF_eq  (μ : SPMF α) (h := mass_le_one) : (castSPMF μ h) = μ := rfl
@[simp] theorem castPMF_PMF_eq (μ : PMF α) (h := mass_eq_one) : (castPMF μ h) = μ := rfl

@[simp] theorem coeFn_castMF_eq_coeFn (μ : M α) :
    ⇑(μ : MF α) = ⇑μ := rfl
@[simp] theorem coeFn_castFMF_eq_coeFn [FMFClass M] (μ : M α) :
    ⇑(μ : FMF α) = ⇑μ := rfl
@[simp] theorem coeFn_castSPMF_eq_coeFn [SPMFClass M] (μ : M α) :
    ⇑(μ : SPMF α) = ⇑μ := rfl
@[simp] theorem coeFn_castPMF_eq_coeFn [PMFClass M] (μ : M α) :
    ⇑(μ : PMF α) = ⇑μ := rfl

@[simp] theorem castMF_apply (μ : M α) (a : α) :
    (μ : MF α) a = μ a := rfl
@[simp] theorem castFMF_apply [FMFClass M] (μ : M α) (a : α) :
    (μ : FMF α) a = μ a := rfl
@[simp] theorem castSPMF_apply [SPMFClass M] (μ : M α) (a : α) :
    (μ : SPMF α) a = μ a := rfl
@[simp] theorem castPMF_apply [PMFClass M] (μ : M α) (a : α) :
    (μ : PMF α) a = μ a := rfl

@[simp] theorem castMF_eq (μ ν : M α) :
    (μ : MF α) = (ν : MF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_castMF_eq_coeFn]
@[simp] theorem castFMF_eq [FMFClass M] (μ ν : M α) :
    (μ : FMF α) = (ν : FMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_castFMF_eq_coeFn]
@[simp] theorem castSPMF_eq [SPMFClass M] (μ ν : M α) :
    (μ : SPMF α) = (ν : SPMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_castSPMF_eq_coeFn]
@[simp] theorem castPMF_eq [PMFClass M] (μ ν : M α) :
    (μ : PMF α) = (ν : PMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_castPMF_eq_coeFn]

@[simp] theorem mass_castMF (μ : M α) :
    mass (μ : MF α) = mass μ := rfl
@[simp] theorem mass_castFMF [FMFClass M] (μ : M α) :
    mass (μ : FMF α) = mass μ := rfl
@[simp] theorem mass_castSPMF [SPMFClass M] (μ : M α) :
    mass (μ : SPMF α) = mass μ := rfl
@[simp] theorem mass_castPMF [PMFClass M] (μ : M α) :
    mass (μ : PMF α) = mass μ := rfl

@[simp] theorem support_castMF (μ : M α) :
    support (μ : MF α) = support μ := rfl
@[simp] theorem support_castFMF [FMFClass M] (μ : M α) :
    support (μ : FMF α) = support μ := rfl
@[simp] theorem support_castSPMF [SPMFClass M] (μ : M α) :
    support (μ : SPMF α) = support μ := rfl
@[simp] theorem support_castPMF [PMFClass M] (μ : M α) :
    support (μ : PMF α) = support μ := rfl

@[simp] theorem massOf_castMF (μ : M α) :
    massOf (μ : MF α) = massOf μ := rfl
@[simp] theorem massOf_castFMF [FMFClass M] (μ : M α) :
    massOf (μ : FMF α) = massOf μ := rfl
@[simp] theorem massOf_castSPMF [SPMFClass M] (μ : M α) :
    massOf (μ : SPMF α) = massOf μ := rfl
@[simp] theorem massOf_castPMF [PMFClass M] (μ : M α) :
    massOf (μ : PMF α) = massOf μ := rfl

end Coe

end MassFunction
