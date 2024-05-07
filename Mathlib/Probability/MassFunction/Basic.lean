import Mathlib.Topology.Instances.ENNReal
import Mathlib.Algebra.Order.Interval.Set.Instances

@[simp]
theorem Set.indicator_singleton_apply_self {α M : Type*} {a : α} {f : α → M} [Zero M] :
    Set.indicator {a} f a = f a := indicator_of_mem rfl _

@[simp]
theorem Set.indicator_singleton_apply_of_ne {α M : Type*} [Zero M] {a a' : α} {f : α → M}
    (h : a' ≠ a) : Set.indicator {a} f a' = 0 :=
  indicator_of_not_mem (Set.eq_of_mem_singleton.mt h) _

open BigOperators ENNReal NNReal

namespace MassFunction

abbrev MFLike (M : Sort*) (α : outParam Type*) := FunLike M α ℝ≥0∞

variable {M : Sort*} {α : Type*} [MFLike M α] {μ ν : M} {a b : α} {s t : Set α}

noncomputable def mass (μ : M) := tsum μ

noncomputable def support (μ : M) := (⇑μ).support

noncomputable def massOf (μ : M) (s : Set α) := tsum (s.indicator μ)

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
theorem apply_pos_of_mem_support (ha : a ∈ support μ) :
  0 < μ a := mem_support_iff'.mp ha

@[simp]
theorem apply_ne_zero_of_mem_support (ha : a ∈ support μ) : μ a ≠ 0 :=
  (apply_pos_of_mem_support ha).ne'

theorem nmem_support_iff : a ∉ support μ ↔ μ a = 0 := Function.nmem_support

theorem apply_eq_zero_of_nmem_support (ha : a ∉ support μ) : μ a = 0 :=
  nmem_support_iff.mp ha

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

theorem massOf_eq_tsum_coe_indicator : massOf μ s = ∑' i, s.indicator ⇑μ i := rfl

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

theorem massOf_injective : (massOf : M → Set α → ℝ≥0∞).Injective := fun d₁ d₂ h => by
  simp_rw [DFunLike.ext_iff, ← massOf_singleton, h, implies_true]

theorem massOf_inj : massOf μ = massOf ν ↔ μ = ν := massOf_injective.eq_iff

theorem massOf_eq_zero_iff : massOf μ s = 0 ↔ ∀ a ∈ s, μ a = 0 := by
  refine' ENNReal.tsum_eq_zero.trans _
  simp_rw [Set.indicator_apply_eq_zero]

theorem massOf_eq_zero_iff_support_disjoint : massOf μ s = 0 ↔ Disjoint (support μ) s := by
  simp_rw [massOf_eq_zero_iff, support_disjoint_iff]

theorem massOf_eq_zero_iff_disjoint_support : massOf μ s = 0 ↔ Disjoint s (support μ) := by
  simp_rw [massOf_eq_zero_iff, disjoint_support_iff]

theorem massOf_ne_zero_iff : massOf μ s ≠ 0 ↔ ∃ a ∈ s, μ a ≠ 0 := by
  simp_rw [Ne.def, massOf_eq_zero_iff_disjoint_support, Set.not_disjoint_iff,
  mem_support_iff]

theorem massOf_ne_zero_iff_support_disjoint : massOf μ s ≠ 0 ↔ ((support μ) ∩ s).Nonempty := by
  simp_rw [Ne.def, massOf_eq_zero_iff_support_disjoint, Set.not_disjoint_iff_nonempty_inter]

theorem massOf_ne_zero_iff_disjoint_support : massOf μ s ≠ 0 ↔ (s ∩ (support μ)).Nonempty := by
  simp_rw [Ne.def, massOf_eq_zero_iff_disjoint_support, Set.not_disjoint_iff_nonempty_inter]

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

class FMFClass (M : Sort*) (α : outParam Type*) [MFLike M α] : Prop :=
  (mass_lt_top : ∀ μ : M, mass μ < ∞)

section FiniteMassFunction

variable [FMFClass M α]

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

class SPMFClass (M : Sort*) (α : outParam Type*) [MFLike M α] : Prop :=
  (mass_le_one : ∀ μ : M, mass μ ≤ 1)

instance SPMFClass.toFMFClass [SPMFClass M α] : FMFClass M α where
  mass_lt_top f := (mass_le_one f).trans_lt one_lt_top

section SubProbabilityMassFunction

variable [SPMFClass M α]

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

class PMFClass (M : Sort*) (α : outParam Type*) [MFLike M α] : Prop :=
  (mass_eq_one : ∀ μ : M, mass μ = 1)

instance PMFClass.toSPMFClass [PMFClass M α] : SPMFClass M α where
  mass_le_one f := (mass_eq_one f).le

section ProbabilityMassFunction

variable [PMFClass M α]

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

section Classes

variable {M : Sort*} {α : Type*} [MFLike M α]

end Classes

structure MF (α : Type*) where
  toFun : α → ℝ≥0∞

namespace MF

variable {α : Type*} {r : ℝ≥0∞} {μ : MF α} {a : α} {s : Set α}

instance instMFLike : MFLike (MF α) α where
  coe f := f.toFun
  coe_injective' := fun ⟨_⟩ ⟨_⟩ _ => by congr

@[ext] theorem ext {μ ν : MF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZero : Zero (MF α) := ⟨⟨0⟩⟩

@[simp]
theorem coeFn_zero : ⇑(0 : MF α) = 0 := rfl

@[simp]
theorem zero_apply : (0 : MF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : MF α) = 0 := tsum_zero

@[simp]
theorem support_zero : support (0 : MF α) = ∅ := Function.support_zero

@[simp]
theorem massOf_zero : massOf (0 : MF α) s = 0 :=
  massOf_eq_zero_iff.mpr (fun _ _ => MF.zero_apply)

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
  simp_rw [massOf_eq_tsum_coe_indicator, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0∞ (MF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end MF

structure FMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_lt_top' : tsum (toFun) < ∞

namespace FMF

variable {α : Type*} {r : ℝ≥0} {μ : FMF α} {a : α} {s : Set α}

instance instMFLike : MFLike (FMF α) α where
  coe μ := μ.toFun
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

instance instFMFClass : FMFClass (FMF α) α where
  mass_lt_top := FMF.mass_lt_top'

@[ext] theorem ext {μ ν : FMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZero : Zero (FMF α) := ⟨0, tsum_zero.trans_lt zero_lt_top⟩

@[simp]
theorem coeFn_zero : ⇑(0 : FMF α) = 0 := rfl

@[simp]
theorem zero_apply : (0 : FMF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : FMF α) = 0 := tsum_zero

@[simp]
theorem support_zero : support (0 : FMF α) = ∅ := Function.support_zero

@[simp]
theorem massOf_zero : massOf (0 : FMF α) s = 0 :=
  massOf_eq_zero_iff.mpr (fun _ _ => FMF.zero_apply)

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
  simp_rw [massOf_eq_tsum_coe_indicator, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0 (FMF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end FMF

structure SPMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_le_one' : tsum (toFun) ≤ 1

namespace SPMF

variable {α : Type*} {r : (Set.Icc 0 1 : Set ℝ≥0∞)} {μ : SPMF α} {a : α} {s : Set α}

instance instMFLike : MFLike (SPMF α) α where
  coe μ := μ.toFun
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

instance instSPMFClass : SPMFClass (SPMF α) α where
  mass_le_one := SPMF.mass_le_one'

@[ext] theorem ext {μ ν : SPMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

instance instZero : Zero (SPMF α) := ⟨0, tsum_zero.trans_le zero_le_one⟩

@[simp]
theorem coeFn_zero : ((0 : SPMF α) : α → ℝ≥0∞) = 0 := rfl

@[simp]
theorem zero_apply : (0 : SPMF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : SPMF α) = 0 := tsum_zero

@[simp]
theorem support_zero : support (0 : SPMF α) = ∅ := Function.support_zero

@[simp]
theorem massOf_zero : massOf (0 : SPMF α) s = 0 :=
  massOf_eq_zero_iff.mpr (fun _ _ => SPMF.zero_apply)

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
  simp_rw [massOf_eq_tsum_coe_indicator, coeFn_smul, Pi.smul_def,
  Set.indicator_const_smul_apply, ENNReal.tsum_const_smul]

noncomputable instance : MulActionWithZero ℝ≥0 (FMF α) :=
  Function.Injective.mulActionWithZero ⟨DFunLike.coe, coeFn_zero⟩
  DFunLike.coe_injective (fun _ _ => rfl)

end SPMF

structure PMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_eq_one' : tsum (toFun) = 1
namespace PMF

variable {α : Type*}

instance instMFLike : MFLike (PMF α) α where
  coe μ := μ.toFun
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

instance instPMFClass : PMFClass (PMF α) α where
  mass_eq_one := PMF.mass_eq_one'

@[ext] theorem ext {μ ν : PMF α} (h : ∀ x, μ x = ν x) : μ = ν := DFunLike.ext _ _ (by assumption)

end PMF

section Coe

variable {M : Sort*} {α : Type*} [MFLike M α]

@[coe]
def MFLike.toMF (μ : M) : MF α := ⟨μ⟩

instance : CoeHead M (MF α) := ⟨MFLike.toMF⟩

@[coe]
def FMFClass.toFMF [FMFClass M α] (μ : M) : FMF α := ⟨μ, mass_lt_top _⟩

instance [FMFClass M α] : CoeHead M (FMF α) := ⟨FMFClass.toFMF⟩

@[coe]
def SPMFClass.toSPMF [SPMFClass M α] (μ : M) : SPMF α := ⟨μ, mass_le_one _⟩

instance [SPMFClass M α] : CoeHead M (SPMF α) := ⟨SPMFClass.toSPMF⟩

@[coe]
def PMFClass.toPMF [PMFClass M α] (μ : M) : PMF α := ⟨μ, mass_eq_one _⟩

instance [PMFClass M α] : CoeHead M (PMF α) := ⟨PMFClass.toPMF⟩

@[simp] theorem coeFn_coeMF_eq_coeFn (μ : M) :
    ⇑(μ : MF α) = ⇑μ := rfl
@[simp] theorem coeFn_coeFMF_eq_coeFn [FMFClass M α] (μ : M) :
    ⇑(μ : FMF α) = ⇑μ := rfl
@[simp] theorem coeFn_coeSPMF_eq_coeFn [SPMFClass M α] (μ : M) :
    ⇑(μ : SPMF α) = ⇑μ := rfl
@[simp] theorem coeFn_coePMF_eq_coeFn [PMFClass M α] (μ : M) :
    ⇑(μ : PMF α) = ⇑μ := rfl

@[simp] theorem coeMF_apply (μ : M) (a : α) :
    (μ : MF α) a = μ a := rfl
@[simp] theorem coeFMF_apply [FMFClass M α] (μ : M) (a : α) :
    (μ : FMF α) a = μ a := rfl
@[simp] theorem coeSPMF_apply [SPMFClass M α] (μ : M) (a : α) :
    (μ : SPMF α) a = μ a := rfl
@[simp] theorem coePMF_apply [PMFClass M α] (μ : M) (a : α) :
    (μ : PMF α) a = μ a := rfl

@[simp] theorem coeMF_eq (μ ν : M) :
    (μ : MF α) = (ν : MF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_coeMF_eq_coeFn]
@[simp] theorem coeFMF_eq [FMFClass M α] (μ ν : M) :
    (μ : FMF α) = (ν : FMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_coeFMF_eq_coeFn]
@[simp] theorem coeSPMF_eq [SPMFClass M α] (μ ν : M) :
    (μ : SPMF α) = (ν : SPMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_coeSPMF_eq_coeFn]
@[simp] theorem coePMF_eq [PMFClass M α] (μ ν : M) :
    (μ : PMF α) = (ν : PMF α) ↔ μ = ν := by
  simp_rw [DFunLike.ext'_iff, coeFn_coePMF_eq_coeFn]

@[simp] theorem mass_coeMF (μ : M) :
    mass (μ : MF α) = mass μ := rfl
@[simp] theorem mass_coeFMF [FMFClass M α] (μ : M) :
    mass (μ : FMF α) = mass μ := rfl
@[simp] theorem mass_coeSPMF [SPMFClass M α] (μ : M) :
    mass (μ : SPMF α) = mass μ := rfl
@[simp] theorem mass_coePMF [PMFClass M α] (μ : M) :
    mass (μ : PMF α) = mass μ := rfl

@[simp] theorem support_coeMF (μ : M) :
    support (μ : MF α) = support μ := rfl
@[simp] theorem support_coeFMF [FMFClass M α] (μ : M) :
    support (μ : FMF α) = support μ := rfl
@[simp] theorem support_coeSPMF [SPMFClass M α] (μ : M) :
    support (μ : SPMF α) = support μ := rfl
@[simp] theorem support_coePMF [PMFClass M α] (μ : M) :
    support (μ : PMF α) = support μ := rfl

@[simp] theorem massOf_coeMF (μ : M) :
    massOf (μ : MF α) = massOf μ := rfl
@[simp] theorem massOf_coeFMF [FMFClass M α] (μ : M) :
    massOf (μ : FMF α) = massOf μ := rfl
@[simp] theorem massOf_coeSPMF [SPMFClass M α] (μ : M) :
    massOf (μ : SPMF α) = massOf μ := rfl
@[simp] theorem massOf_coePMF [PMFClass M α] (μ : M) :
    massOf (μ : PMF α) = massOf μ := rfl

end Coe

end MassFunction
