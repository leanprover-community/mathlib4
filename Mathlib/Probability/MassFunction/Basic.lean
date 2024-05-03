import Mathlib.Topology.Instances.ENNReal

open BigOperators ENNReal


abbrev MFLike (F : Sort*) (α : outParam Type*) := FunLike F α ℝ≥0∞

section MFLike

variable {F : Sort*} {α : Type*} [MFLike F α] {f g : F} {a b : α} {s t : Set α}

section MassFunction

noncomputable def mass (f : F) := ∑' i, f i

noncomputable def massSupport (f : F) := Function.support f

noncomputable def massOf (f : F) (s : Set α) := ∑' i, s.indicator f i

section Coe

theorem coe_eq_zero_iff : ⇑f = 0 ↔ ∀ a : α, f a = 0 := by
  simp_rw [Function.funext_iff, Pi.zero_apply]

theorem coe_ne_zero_iff : ⇑f ≠ 0 ↔ ∃ a : α, f a ≠ 0 := by
  simp_rw [Ne.def, coe_eq_zero_iff.not, not_forall]

theorem summable_coe : Summable f := ENNReal.summable

theorem summable_indicatorc_coe : Summable (s.indicator f) := ENNReal.summable

end Coe

section Mass

@[simp]
theorem tsum_eq_mass {f : F} : ∑' i, f i = mass f := rfl

theorem mass_eq_zero_iff : mass f = 0 ↔ ⇑f = 0 :=
  ENNReal.tsum_eq_zero.trans coe_eq_zero_iff.symm

theorem mass_ne_zero_iff : mass f ≠ 0 ↔ ⇑f ≠ 0 := mass_eq_zero_iff.not

theorem apply_le_mass : f a ≤ mass f := ENNReal.le_tsum a

end Mass

section MassSupport

@[simp]
theorem coe_support_eq_massSupport {f : F}  : (f : α → ℝ≥0∞).support = massSupport f := rfl

@[simp]
theorem mem_massSupport_iff : a ∈ massSupport f ↔ f a ≠ 0 := Iff.rfl

theorem mem_massSupport_iff' : a ∈ massSupport f  ↔ 0 < f a :=
  mem_massSupport_iff.trans pos_iff_ne_zero.symm

@[simp]
theorem apply_pos_of_mem_massSupport (ha : a ∈ massSupport f) : 0 < f a := mem_massSupport_iff'.mp ha

@[simp]
theorem apply_ne_zero_of_mem_massSupport (ha : a ∈ massSupport f) : f a ≠ 0 :=
  (apply_pos_of_mem_massSupport ha).ne'

theorem nmem_massSupport_iff : a ∉ massSupport f ↔ f a = 0 := Function.nmem_support

theorem apply_eq_zero_of_nmem_massSupport (ha : a ∉ massSupport f) : f a = 0 :=
  nmem_massSupport_iff.mp ha

@[simp]
theorem indicator_massSupport : (massSupport f).indicator f = f := Set.indicator_support

@[simp]
theorem massSupport_indicator : (s.indicator f).support = s ∩ massSupport f :=
  Set.support_indicator

theorem massSupport_disjoint_iff : Disjoint (massSupport f) s ↔ ∀ a ∈ s, f a = 0 :=
  Function.support_disjoint_iff

theorem disjoint_massSupport_iff : Disjoint s (massSupport f) ↔ ∀ a ∈ s, f a = 0 :=
  Function.disjoint_support_iff

theorem massSupport_eq_empty_iff : massSupport f = ∅ ↔ ⇑f = 0 := Function.support_eq_empty_iff

theorem massSupport_nonempty_iff : (massSupport f).Nonempty ↔ ⇑f ≠ 0 :=
  Function.support_nonempty_iff

theorem mass_ne_zero_iff' : mass f ≠ 0 ↔ (massSupport f).Nonempty :=
  mass_ne_zero_iff.trans massSupport_nonempty_iff.symm


end MassSupport

section MassOf

@[simp]
theorem tsum_coe_indicator_eq_massOf {f : F} {s : Set α} : ∑' i, s.indicator f i = massOf f s := rfl

@[simp]
theorem massOf_fintype [Fintype α] :
    massOf f s = ∑ i, s.indicator f i := tsum_fintype _

theorem massOf_finset {s : Finset α} :
    massOf f s = ∑ i in s, f i := (sum_eq_tsum_indicator f s).symm

theorem massOf_le_mass : massOf f s ≤ mass f :=
  ENNReal.tsum_le_tsum (s.indicator_le_self _)

theorem massOf_massSupport : massOf f (massSupport f) = mass f :=
  le_antisymm massOf_le_mass
  (ENNReal.tsum_le_tsum (fun _ => by simp_rw [indicator_massSupport, le_refl]))

theorem massOf_univ : massOf f (Set.univ) = mass f :=
  tsum_congr (fun _ => congr_fun (Set.indicator_univ f) _)

theorem massOf_empty : massOf f ∅ = 0 :=
  ENNReal.tsum_eq_zero.mpr (fun _ => congr_fun (Set.indicator_empty f) _)

theorem massOf_mono (hst : s ≤ t) : massOf f s ≤ massOf f t :=
  ENNReal.tsum_le_tsum (Set.indicator_le_indicator_of_subset hst (fun _ => zero_le _))

theorem massOf_eq_tsum_subtype : massOf f s = ∑' i : s, f i := (tsum_subtype s f).symm

theorem massOf_iUnion_nat {s : ℕ → Set α} :
    massOf f (⋃ i, s i) ≤ ∑' i, massOf f (s i) := by
  simp_rw [massOf_eq_tsum_subtype]
  exact ENNReal.tsum_iUnion_le_tsum _ _

@[simp]
theorem massOf_singleton : massOf f {a} = f a := by
  rw [massOf_eq_tsum_subtype, tsum_singleton]

theorem massOf_union_disjoint (hst : Disjoint s t) :
    massOf f (s ∪ t) = massOf f s + massOf f t := by
  simp_rw [massOf_eq_tsum_subtype]
  exact tsum_union_disjoint hst ENNReal.summable ENNReal.summable

theorem massOf_pair_disjoint (hab : a ≠ b) : massOf f {a, b} = f a + f b := by
  simp_rw [← massOf_singleton]
  exact massOf_union_disjoint (fun _ ha hb _ hc => (hab ((ha hc).symm.trans (hb hc))).elim)

theorem massOf_caratheodory : massOf f t = massOf f (t ∩ s) + massOf f (t \ s) := by
  nth_rewrite 1 [← Set.inter_union_diff t s]
  exact massOf_union_disjoint Set.disjoint_sdiff_inter.symm

theorem massOf_injective : (massOf : F → Set α → ℝ≥0∞).Injective := fun d₁ d₂ h => by
  simp_rw [DFunLike.ext_iff, ← massOf_singleton, h, implies_true]

theorem massOf_inj : massOf f = massOf g ↔ f = g := massOf_injective.eq_iff

theorem massOf_eq_zero_iff : massOf f s = 0 ↔ ∀ a ∈ s, f a = 0 := by
  refine' ENNReal.tsum_eq_zero.trans _
  simp_rw [Set.indicator_apply_eq_zero]

theorem massOf_eq_zero_iff_massSupport_disjoint : massOf f s = 0 ↔ Disjoint (massSupport f) s := by
  simp_rw [massOf_eq_zero_iff, massSupport_disjoint_iff]

theorem massOf_eq_zero_iff_disjoint_massSupport : massOf f s = 0 ↔ Disjoint s (massSupport f) := by
  simp_rw [massOf_eq_zero_iff, disjoint_massSupport_iff]

theorem massOf_ne_zero_iff : massOf f s ≠ 0 ↔ ∃ a ∈ s, f a ≠ 0 := by
  simp_rw [Ne.def, massOf_eq_zero_iff_disjoint_massSupport, Set.not_disjoint_iff,
  mem_massSupport_iff]

theorem massOf_ne_zero_iff_massSupport_disjoint : massOf f s ≠ 0 ↔ ((massSupport f) ∩ s).Nonempty := by
  simp_rw [Ne.def, massOf_eq_zero_iff_massSupport_disjoint, Set.not_disjoint_iff_nonempty_inter]

theorem massOf_ne_zero_iff_disjoint_massSupport : massOf f s ≠ 0 ↔ (s ∩ (massSupport f)).Nonempty := by
  simp_rw [Ne.def, massOf_eq_zero_iff_disjoint_massSupport, Set.not_disjoint_iff_nonempty_inter]

@[simp]
theorem massOf_apply_inter_massSupport :
    massOf f (s ∩ massSupport f) = massOf f s :=
  tsum_congr (fun _ => congr_fun (Set.indicator_inter_support _ _) _)

theorem massOf_mono' (h : s ∩ massSupport f ⊆ t) :
    massOf f s ≤ massOf f t := massOf_apply_inter_massSupport.symm.le.trans (massOf_mono h)

theorem massOf_apply_eq_of_inter_massSupport_eq (h : s ∩ massSupport f = t ∩ massSupport f) :
    massOf f s = massOf f t :=
  le_antisymm (massOf_mono' (h.symm ▸ Set.inter_subset_left t (massSupport f)))
    (massOf_mono' (h ▸ Set.inter_subset_left s (massSupport f)))

theorem apply_eq_mass_of_massSupport_empty (ha : massSupport f = ∅) :
    ∀ a, f a = mass f := fun a => by
  rw [massSupport_eq_empty_iff] at ha
  rwa [ha, Pi.zero_apply, eq_comm, mass_eq_zero_iff]

theorem apply_eq_mass_iff_of_nmem_support (had : a ∉ massSupport f) :
    f a = mass f ↔ massSupport f = ∅ := by
  rw [apply_eq_zero_of_nmem_massSupport had, massSupport_eq_empty_iff, eq_comm, mass_eq_zero_iff]

theorem apply_eq_mass_of_massSupport_singleton (ha : massSupport f = {a}) :
    f a = mass f := by
  rw [← massOf_singleton, ← massOf_massSupport]
  exact massOf_apply_eq_of_inter_massSupport_eq (ha ▸ rfl)

theorem exists_apply_eq_mass_of_massSupport_subsingleton [Inhabited α]
    (ha : (massSupport f).Subsingleton) : ∃ a, f a = mass f := by
  rcases ha.eq_empty_or_singleton with (ha | ⟨a, ha⟩)
  · exact ⟨_, apply_eq_mass_of_massSupport_empty ha default⟩
  · exact ⟨_, apply_eq_mass_of_massSupport_singleton ha⟩

end MassOf

end MassFunction


class FMFClass (F : Sort*) (α : outParam Type*) [MFLike F α] : Prop :=
  (mass_lt_top : ∀ {f : F}, mass f < ∞)

section FiniteMassFunction

variable [FMFClass F α]

section Mass

theorem mass_lt_top : mass f < ∞ := FMFClass.mass_lt_top

theorem mass_ne_top : mass f ≠ ∞ := mass_lt_top.ne_top

theorem apply_lt_top : f a < ∞ := apply_le_mass.trans_lt mass_lt_top

theorem apply_ne_top : f a ≠ ∞ := apply_lt_top.ne

end Mass

section MassSupport

@[simp]
theorem massSupport_countable : (massSupport f).Countable :=
  Summable.countable_support_ennreal mass_ne_top

theorem apply_lt_mass_of_massSupport_nontrivial (h : (massSupport f).Nontrivial) :
    ∀ a, f a < mass f := fun a => by
  rcases h.exists_ne a with ⟨b, hbd, hba⟩
  refine' (massOf_le_mass (s := {b, a})).trans_lt' _
  rw [massOf_pair_disjoint hba, add_comm]
  exact ENNReal.lt_add_right apply_ne_top (apply_ne_zero_of_mem_massSupport hbd)

theorem apply_ne_mass_of_massSupport_nontrivial (h : (massSupport f).Nontrivial) :
    ∀ a, f a ≠ mass f := fun a => (apply_lt_mass_of_massSupport_nontrivial h a).ne

theorem support_subsingleton_of_apply_eq_mass (h : ∃ a, f a = mass f) :
    (massSupport f).Subsingleton := by
  rcases h with ⟨a, ha⟩
  by_contra hd
  rw [Set.not_subsingleton_iff] at hd
  exact apply_ne_mass_of_massSupport_nontrivial hd a ha

theorem support_subsingleton_iff_exists_apply_eq_mass [Inhabited α]  :
    (massSupport f).Subsingleton ↔ ∃ a, f a = mass f :=
  ⟨exists_apply_eq_mass_of_massSupport_subsingleton, support_subsingleton_of_apply_eq_mass⟩

theorem support_nontrivial_iff_apply_ne_mass [Inhabited α] :
    (massSupport f).Nontrivial ↔ ∀ a, f a ≠ mass f := by
  rw [← Set.not_subsingleton_iff, support_subsingleton_iff_exists_apply_eq_mass, not_exists]

theorem support_nontrivial_iff_apply_lt_mass [Inhabited α] :
    (massSupport f).Nontrivial ↔ ∀ a, f a < mass f := by
  rw [support_nontrivial_iff_apply_ne_mass]
  exact ⟨fun h a => apply_le_mass.lt_of_ne (h a), fun h a => (h a).ne⟩

theorem apply_eq_mass_iff_of_mem_massSupport (had : a ∈ massSupport f) :
    f a = mass f ↔ massSupport f = {a} := by
  refine' ⟨fun ha => _, fun ha => _⟩
  · rcases Set.eq_singleton_or_nontrivial had with (had | had)
    · assumption
    · exact (apply_ne_mass_of_massSupport_nontrivial had a ha).elim
  · exact apply_eq_mass_of_massSupport_singleton ha

end MassSupport

section MassOf

@[simp]
theorem massOf_lt_top : massOf f s < ∞ := massOf_le_mass.trans_lt mass_lt_top

@[simp]
theorem massOf_ne_top : massOf f s ≠ ∞ := massOf_lt_top.ne

theorem massOf_lt_mass_of_massSupport_diff_nonempty
    (h : (massSupport f \ s).Nonempty) : massOf f s < mass f := by
  rcases h with ⟨a, haf, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) massOf_ne_top
    (fun a => (Set.indicator_le (fun _ _ => le_rfl) a)) _
  rw [Set.indicator_of_not_mem has, zero_lt_iff]
  exact apply_ne_zero_of_mem_massSupport haf

theorem massOf_lt_massOf_of_massSupport_inter_diff_nonempty_of_lt
    (h : ((massSupport f ∩ t) \ s).Nonempty) (hst : s < t) : massOf f s < massOf f t := by
  rcases h with ⟨a, ⟨haf, hat⟩, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) massOf_ne_top
    (fun b => (Set.indicator_le_indicator_of_subset hst.le (fun _ => zero_le _) _)) _
  rw [Set.indicator_of_not_mem has, Set.indicator_of_mem hat, zero_lt_iff]
  exact apply_ne_zero_of_mem_massSupport haf

theorem apply_massOf_eq_mass_iff : massOf f s = mass f ↔ massSupport f ⊆ s := by
  refine' ⟨fun h => _, fun h => _⟩
  · by_contra h'
    rw [Set.not_subset] at h'
    exact ((massOf_lt_mass_of_massSupport_diff_nonempty h').ne h)
  · rw [← massOf_massSupport]
    refine' massOf_apply_eq_of_inter_massSupport_eq _
    rwa [Set.inter_self, Set.inter_eq_right]

end MassOf

end FiniteMassFunction


class SPMFClass (F : Sort*) (α : outParam Type*) [MFLike F α] : Prop :=
  (mass_le_one : ∀ {f : F}, mass f ≤ 1)

section SubProbabilityMassFunction

variable [SPMFClass F α]

section Mass

@[simp]
theorem mass_le_one : mass f ≤ 1 := SPMFClass.mass_le_one

theorem apply_le_one : f a ≤ 1 := apply_le_mass.trans mass_le_one

end Mass

section MassOf

theorem massOf_le_one : massOf f s ≤ 1 := massOf_le_mass.trans mass_le_one

end MassOf

end SubProbabilityMassFunction

class PMFClass (F : Sort*) (α : outParam Type*) [MFLike F α] : Prop :=
  (mass_eq_one : ∀ {f : F}, mass f = 1)

section ProbabilityMassFunction

variable [PMFClass F α]

section Mass

@[simp]
theorem mass_eq_one {f : F} : mass f = 1 := PMFClass.mass_eq_one

end Mass

section HasSum

theorem hasSum_coe_one : HasSum f 1 := (Summable.hasSum_iff summable_coe).mpr mass_eq_one

end HasSum

end ProbabilityMassFunction

end MFLike


structure MF (α : Type*) where
  toFun : α → ℝ≥0∞

namespace MF

variable {α : Type*}

instance instMFLike : MFLike (MF α) α where
  coe f := f.toFun
  coe_injective' := fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext] theorem ext {f g : MF α} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

instance instZero : Zero (MF α) := ⟨⟨0⟩⟩

@[simp]
theorem coe_zero : ((0 : MF α) : α → ℝ≥0∞) = 0 := rfl

@[simp]
theorem zero_apply (a : α) : (0 : MF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : MF α) = 0 := tsum_zero

@[simp]
theorem massSupport_zero : massSupport (0 : MF α) = ∅ := Function.support_zero

instance : Inhabited (MF α) := ⟨0⟩

end MF



structure FMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_lt_top' : ∑' i, toFun i < ∞

namespace FMF

variable {α : Type*}

instance instMFLike : MFLike (FMF α) α where
  coe := FMF.toFun
  coe_injective' := fun ⟨f, _⟩ ⟨g, _⟩ _ => by congr

@[ext] theorem ext {f g : FMF α} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

protected def copy (f : FMF α) (f' : α → ℝ≥0∞) (h : f' = ⇑f) : FMF α where
  toFun := f'
  mass_lt_top' := h.symm ▸ f.mass_lt_top'

instance instZero : Zero (FMF α) := ⟨0, by simp_rw [Pi.zero_apply, tsum_zero, zero_lt_top]⟩

@[simp]
theorem coe_zero : ((0 : FMF α) : α → ℝ≥0∞) = 0 := rfl

@[simp]
theorem zero_apply (a : α) : (0 : FMF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : FMF α) = 0 := tsum_zero

@[simp]
theorem massSupport_zero : massSupport (0 : FMF α) = ∅ := Function.support_zero

instance : Inhabited (FMF α) := ⟨0⟩

end FMF


structure SPMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_le_one' : ∑' i, toFun i ≤ 1

namespace SPMF

variable {α : Type*}

instance instMFLike : MFLike (SPMF α) α where
  coe := SPMF.toFun
  coe_injective' := fun ⟨f, _⟩ ⟨g, _⟩ _ => by congr

@[ext] theorem ext {f g : SPMF α} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

protected def copy (f : SPMF α) (f' : α → ℝ≥0∞) (h : f' = ⇑f) : SPMF α where
  toFun := f'
  mass_le_one' := h.symm ▸ f.mass_le_one'

instance instZero : Zero (SPMF α) := ⟨0, by simp_rw [Pi.zero_apply, tsum_zero, zero_le_one]⟩

@[simp]
theorem coe_zero : ((0 : SPMF α) : α → ℝ≥0∞) = 0 := rfl

@[simp]
theorem zero_apply (a : α) : (0 : SPMF α) a = 0 := rfl

@[simp]
theorem mass_zero : mass (0 : SPMF α) = 0 := tsum_zero

@[simp]
theorem massSupport_zero : massSupport (0 : SPMF α) = ∅ := Function.support_zero

instance : Inhabited (SPMF α) := ⟨0⟩

end SPMF


structure PMF (α : Type*) where
  toFun : α → ℝ≥0∞
  mass_eq_one' : ∑' i, toFun i = 1

namespace PMF

variable {α : Type*}

instance instMFLike : MFLike (PMF α) α where
  coe := PMF.toFun
  coe_injective' := fun ⟨f, _⟩ ⟨g, _⟩ _ => by congr

@[ext] theorem ext {f g : PMF α} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

protected def copy (f : PMF α) (f' : α → ℝ≥0∞) (h : f' = ⇑f) : PMF α where
  toFun := f'
  mass_eq_one' := h.symm ▸ f.mass_eq_one'

end PMF

section Coe

variable {F : Sort*} {α : Type*} [MFLike F α]

@[coe]
def MFLike.toMF (f : F) : MF α := ⟨f⟩

instance : CoeTC F (MF α) := ⟨MFLike.toMF⟩

@[coe]
def FMFClass.toFMF [FMFClass F α] (f : F) : FMF α := ⟨f, mass_lt_top⟩

instance [FMFClass F α] : CoeTC F (FMF α) := ⟨FMFClass.toFMF⟩

@[coe]
def SPMFClass.toSPMF [SPMFClass F α] (f : F) : SPMF α := ⟨f, mass_le_one⟩

instance [SPMFClass F α] : CoeTC F (SPMF α) := ⟨SPMFClass.toSPMF⟩

@[coe]
def PMFClass.toPMF [PMFClass F α] (f : F) : PMF α := ⟨f, mass_eq_one⟩

instance [PMFClass F α] : CoeTC F (PMF α) := ⟨PMFClass.toPMF⟩

@[simp] theorem MFLike.coe_eq_coe (f : F) : ((f : MF α) : α → ℝ≥0∞) = (f : α → ℝ≥0∞) := rfl
@[simp] theorem FMFClass.coe_eq_coe [FMFClass F α] (f : F) :
    ((f : FMF α) : α → ℝ≥0∞) = (f : α → ℝ≥0∞) := rfl
@[simp] theorem SPMFClass.coe_eq_coe [SPMFClass F α] (f : F) :
    ((f : SPMF α) : α → ℝ≥0∞) = (f : α → ℝ≥0∞) := rfl
@[simp] theorem PMFClass.coe_eq_coe [PMFClass F α] (f : F) :
    ((f : PMF α) : α → ℝ≥0∞) = (f : α → ℝ≥0∞) := rfl

@[simp] theorem MFLike.coe_fn_coe (f g : F) :
    (f : MF α) = (g : MF α) ↔ f = g := by
  simp_rw [DFunLike.ext'_iff, MFLike.coe_eq_coe]
@[simp] theorem FMFClass.coe_fn_coe [FMFClass F α] (f g : F) :
    (f : FMF α) = (g : FMF α) ↔ f = g := by
  simp_rw [DFunLike.ext'_iff, FMFClass.coe_eq_coe]
@[simp] theorem SPMFClass.coe_fn_coe [SPMFClass F α] (f g : F) :
    (f : SPMF α) = (g : SPMF α) ↔ f = g := by
  simp_rw [DFunLike.ext'_iff, SPMFClass.coe_eq_coe]
@[simp] theorem PMFClass.coe_fn_coe [PMFClass F α] (f g : F) :
    (f : PMF α) = (g : PMF α) ↔ f = g := by
  simp_rw [DFunLike.ext'_iff, PMFClass.coe_eq_coe]

@[simp] theorem MFLike.coe_apply (f : F) (a : α) :
    (f : MF α) a = f a := rfl
@[simp] theorem FMFClass.coe_apply [FMFClass F α] (f : F) (a : α) :
    (f : FMF α) a = f a := rfl
@[simp] theorem SPMFClass.coe_apply [SPMFClass F α] (f : F) (a : α) :
    (f : SPMF α) a = f a := rfl
@[simp] theorem PMFClass.coe_apply [PMFClass F α] (f : F) (a : α) :
    (f : PMF α) a = f a := rfl

@[simp] theorem MFLike.coe_mass (f : F) : mass (f : MF α) = mass f := rfl
@[simp] theorem FMFClass.coe_mass [FMFClass F α] (f : F) : mass (f : FMF α) = mass f := rfl
@[simp] theorem SPMFClass.coe_mass [SPMFClass F α] (f : F) : mass (f : SPMF α) = mass f := rfl
@[simp] theorem PMFClass.coe_mass [PMFClass F α] (f : F) : mass (f : PMF α) = mass f := rfl

@[simp] theorem MFLike.coe_massSupport (f : F) :
    massSupport (f : MF α) = massSupport f := rfl
@[simp] theorem FMFClass.coe_massSupport [FMFClass F α] (f : F) :
    massSupport (f : FMF α) = massSupport f := rfl
@[simp] theorem SPMFClass.coe_massSupport [SPMFClass F α] (f : F) :
    massSupport (f : SPMF α) = massSupport f := rfl
@[simp] theorem PMFClass.coe_massSupport [PMFClass F α] (f : F) :
    massSupport (f : PMF α) = massSupport f := rfl

@[simp] theorem MFLike.coe_massOf (f : F) : massOf (f : MF α) = massOf f := rfl
@[simp] theorem FMFClass.coe_massOf [FMFClass F α] (f : F) : massOf (f : FMF α) = massOf f := rfl
@[simp] theorem SPMFClass.coe_massOf [SPMFClass F α] (f : F) : massOf (f : SPMF α) = massOf f := rfl
@[simp] theorem PMFClass.coe_massOf [PMFClass F α] (f : F) : massOf (f : PMF α) = massOf f := rfl

end Coe

section Classes

variable {F : Sort*} {α : Type*} [MFLike F α]

instance instFMFClass : FMFClass (FMF α) α where
  mass_lt_top := fun {f} => f.mass_lt_top'

instance SPMFClass.toFMFClass [SPMFClass F α] : FMFClass F α where
  mass_lt_top := mass_le_one.trans_lt one_lt_top

instance instSPMFClass : SPMFClass (SPMF α) α where
  mass_le_one := fun {f} => f.mass_le_one'

instance PMFClass.toSPMFClass [PMFClass F α] : SPMFClass F α where
  mass_le_one := mass_eq_one.le

instance instPMFClass : PMFClass (PMF α) α where
  mass_eq_one := fun {f} => f.mass_eq_one'

end Classes
