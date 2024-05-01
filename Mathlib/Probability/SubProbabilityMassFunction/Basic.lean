import Mathlib.Topology.Instances.ENNReal

open BigOperators ENNReal

def SPMF (α : Type*) := { f : α → ℝ≥0∞ // ∑' i, f i <= 1}

variable {α β : Type*}

namespace SPMF

instance instFunLike : FunLike (SPMF α) α ℝ≥0∞ where
  coe d a := d.1 a
  coe_injective' _ _ := Subtype.ext

@[ext]
protected theorem ext {p q : SPMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

theorem ext_iff {p q : SPMF α} : p = q ↔ ∀ x, p x = q x :=
  DFunLike.ext_iff

instance instZero : Zero (SPMF α) := ⟨⟨0, by simp_rw [Pi.zero_apply, tsum_zero, zero_le]⟩⟩

@[simp]
theorem coe_zero : ((0 : SPMF α) : α → ℝ≥0∞) = 0 := rfl

theorem coe_eq_zero_iff (d : SPMF α) : (d : α → ℝ≥0∞) = 0 ↔ d = 0 := by
  rw [← coe_zero, DFunLike.coe_fn_eq]

theorem coe_ne_zero_iff (d : SPMF α) : (d : α → ℝ≥0∞) ≠ 0 ↔ d ≠ 0 := d.coe_eq_zero_iff.not

@[simp]
theorem zero_apply (a : α) : (0 : SPMF α) a = 0 := rfl

theorem eq_zero_iff (d : SPMF α) : d = 0 ↔ ∀ a, d a = 0 := by simp_rw [ext_iff, zero_apply]

theorem ne_zero_iff (d : SPMF α) : d ≠ 0 ↔ ∃ a, d a ≠ 0 :=
  d.eq_zero_iff.not.trans not_forall

theorem summable (d : SPMF α) : Summable d := ENNReal.summable

noncomputable def mass (d : SPMF α) := ∑' i, d i

theorem mass_def {d : SPMF α} : d.mass = ∑' i, d i := rfl

@[simp]
theorem mass_zero : (0 : SPMF α).mass = 0 := tsum_zero

theorem mass_eq_zero_iff (d : SPMF α) : d.mass = 0 ↔ d = 0 :=
  ENNReal.tsum_eq_zero.trans d.eq_zero_iff.symm

theorem mass_ne_zero_iff (d : SPMF α) : d.mass ≠ 0 ↔ d ≠ 0 := d.mass_eq_zero_iff.not

theorem pos_mass_iff (d : SPMF α) : 0 < d.mass ↔ d ≠ 0 :=
  bot_lt_iff_ne_bot.trans d.mass_ne_zero_iff

theorem le_mass (d : SPMF α) (a : α) : d a ≤ d.mass := ENNReal.le_tsum a

theorem mass_le_one (d : SPMF α) : d.mass ≤ 1 := d.2

theorem apply_le_one (d : SPMF α) (a : α) : d a ≤ 1 := (d.le_mass a).trans d.mass_le_one

theorem apply_lt_top (d : SPMF α) (a : α) : d a < ∞ :=
  (d.apply_le_one a).trans_lt ENNReal.one_lt_top

theorem apply_ne_top (d : SPMF α) (a : α) : d a ≠ ∞ := (d.apply_lt_top a).ne

theorem mass_lt_top (d : SPMF α) : d.mass < ∞ :=
  d.mass_le_one.trans_lt ENNReal.one_lt_top

theorem mass_ne_top (d : SPMF α) : d.mass ≠ ∞ := (d.mass_lt_top).ne

noncomputable instance instHasSMul : SMul ℝ≥0∞ (SPMF α) := ⟨
  fun x d => ⟨(min x 1) • d, by
    simp_rw [Pi.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
    exact mul_le_one (min_le_right _ _) (zero_le _) d.mass_le_one⟩⟩

theorem smul_apply {d : SPMF α} (x : ℝ≥0∞) (a : α) : (x • d) a = (min x 1) * d a := rfl

theorem smul_apply_of_le_one {d : SPMF α} {x : ℝ≥0∞} (hx : x ≤ 1) (a : α) :
    (x • d) a = x * d a := by rw [smul_apply, min_eq_left hx]

theorem smul_apply_of_one_le {d : SPMF α} {x : ℝ≥0∞} (hx : 1 ≤ x) (a : α) :
    (x • d) a = d a := by rw [smul_apply, min_eq_right hx, one_mul]

def support (d : SPMF α) : Set α := Function.support d

theorem support_def (d : SPMF α) : d.support = (d : α → ℝ≥0∞).support := rfl

@[simp]
theorem mem_support_iff (d : SPMF α) (a : α) : a ∈ d.support ↔ d a ≠ 0 := Iff.rfl

theorem mem_support_iff_apply_pos (d : SPMF α) (a : α) : a ∈ d.support ↔ 0 < d a :=
  (d.mem_support_iff a).trans pos_iff_ne_zero.symm

@[simp]
theorem apply_pos_of_mem_support {d : SPMF α} {a : α} (ha : a ∈ d.support) : 0 < d a :=
  (d.mem_support_iff_apply_pos a).mp ha

@[simp]
theorem apply_ne_zero_of_mem_support {d : SPMF α} {a : α} (ha : a ∈ d.support) : d a ≠ 0 :=
  (apply_pos_of_mem_support ha).ne'

theorem nmem_support_iff (d : SPMF α) (a : α) : a ∉ d.support ↔ d a = 0 :=
  Function.nmem_support

theorem apply_eq_zero_of_nmem_support {d : SPMF α} {a : α} (ha : a ∉ d.support) : d a = 0 :=
  (d.nmem_support_iff a).mp ha

@[simp]
theorem indicator_support (d : SPMF α) : (d.support).indicator d = d := Set.indicator_support

@[simp]
theorem support_indicator (d : SPMF α) (s : Set α) : (s.indicator d).support = s ∩ d.support :=
  Set.support_indicator

@[simp]
theorem support_countable (d : SPMF α) : d.support.Countable :=
  Summable.countable_support_ennreal (mass_ne_top d)

theorem support_eq_empty_iff (d : SPMF α) : d.support = ∅ ↔ d = 0 :=
  Function.support_eq_empty_iff.trans d.coe_eq_zero_iff

theorem support_eq_empty_iff_mass_eq_zero (d : SPMF α) : d.support = ∅ ↔ d.mass = 0 := by
  rw [support_eq_empty_iff, mass_eq_zero_iff]

theorem apply_eq_mass_of_support_eq_empty {d : SPMF α} (h : d.support = ∅) :
    ∀ a, d a = d.mass := by
  rw [d.support_eq_empty_iff_mass_eq_zero.mp h]
  rwa [support_eq_empty_iff, eq_zero_iff] at h

theorem support_nonempty_of_exists_apply_ne_mass {d : SPMF α} (h : ∃ a, d a ≠ d.mass) :
    d.support.Nonempty := by
  rcases h with ⟨a, ha⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty] at hd
  exact ha (apply_eq_mass_of_support_eq_empty hd _)

theorem support_nonempty_of_exists_apply_lt_mass {d : SPMF α} (h : ∃ a, d a < d.mass) :
    d.support.Nonempty := by
  rcases h with ⟨a, ha⟩
  exact support_nonempty_of_exists_apply_ne_mass ⟨a, ha.ne⟩

theorem support_nonempty_iff (d : SPMF α) : d.support.Nonempty ↔ d ≠ 0 :=
  Function.support_nonempty_iff.trans d.coe_ne_zero_iff

theorem support_nonempty_iff_mass_ne_zero (d : SPMF α) : d.support.Nonempty ↔ d.mass ≠ 0 := by
  rw [support_nonempty_iff, mass_ne_zero_iff]

theorem support_nonempty_iff_pos_mass (d : SPMF α) : d.support.Nonempty ↔ 0 < d.mass := by
  rw [support_nonempty_iff, pos_mass_iff]

theorem apply_eq_mass_of_support_empty {d : SPMF α} (ha : d.support = ∅) :
    ∀ a, d a = d.mass := by
  rw [support_eq_empty_iff] at ha
  simp_rw [ha, zero_apply, mass_zero, implies_true]

theorem apply_eq_mass_iff_of_nmem_support {d : SPMF α} {a : α}
    (had : a ∉ d.support) : d a = d.mass ↔ d.support = ∅ := by
  rw [apply_eq_zero_of_nmem_support had, support_eq_empty_iff_mass_eq_zero, eq_comm]

theorem support_disjoint_iff (d : SPMF α) (s : Set α) :
    Disjoint d.support s ↔ ∀ a ∈ s, d a = 0 := by
  rw [support_def, Function.support_disjoint_iff]
  rfl

theorem disjoint_support_iff (d : SPMF α) (s : Set α) :
    Disjoint s d.support ↔ ∀ a ∈ s, d a = 0 := by
  rw [support_def, Function.disjoint_support_iff]
  rfl

noncomputable def massOf (d : SPMF α) (s : Set α) := ∑' i, s.indicator d i

theorem massOf_def (d : SPMF α) (s : Set α) : d.massOf s = ∑' i, s.indicator d i := rfl

@[simp]
theorem massOf_fintype [Fintype α] (d : SPMF α) (s : Set α) :
    d.massOf s = ∑ i, s.indicator d i := tsum_fintype _

theorem massOf_finset (d : SPMF α) (s : Finset α) :
    d.massOf s = ∑ i in s, d i := (sum_eq_tsum_indicator d s).symm

theorem massOf_le_mass (d : SPMF α) (s : Set α) : d.massOf s ≤ d.mass :=
  ENNReal.tsum_le_tsum (s.indicator_le_self _)

theorem massOf_le_one (d : SPMF α) (s : Set α) : d.massOf s ≤ 1 :=
  (d.massOf_le_mass s).trans d.mass_le_one

theorem massOf_lt_top (d : SPMF α) (s : Set α) : d.massOf s < ∞ :=
  (d.massOf_le_one s).trans_lt ENNReal.one_lt_top

theorem massOf_ne_top (d : SPMF α) (s : Set α) : d.massOf s ≠ ∞ :=
  (d.massOf_lt_top s).ne

theorem massOf_lt_mass_of_exists_mem_support_nmem {d : SPMF α} {s : Set α}
    (h : (d.support \ s).Nonempty) : d.massOf s < d.mass := by
  rcases h with ⟨a, had, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) (d.massOf_ne_top s)
    (fun a => (Set.indicator_le (fun _ _ => le_rfl) a)) _
  rw [Set.indicator_of_not_mem has, zero_lt_iff]
  exact apply_ne_zero_of_mem_support had

theorem massOf_support (d : SPMF α) : d.massOf (d.support) = d.mass :=
  le_antisymm (d.massOf_le_mass _)
  (ENNReal.tsum_le_tsum (fun _ => d.indicator_support.symm ▸ le_rfl))

theorem massOf_univ (d : SPMF α) : d.massOf (Set.univ) = d.mass := by
  simp_rw [massOf_def, Set.indicator_univ, mass_def]

theorem massOf_empty (d : SPMF α) : d.massOf ∅ = 0 := by
  simp_rw [massOf_def, Set.indicator_empty, tsum_zero]

theorem massOf_mono (d : SPMF α) {s t : Set α} (hst : s ≤ t) : d.massOf s ≤ d.massOf t :=
  ENNReal.tsum_le_tsum (Set.indicator_le_indicator_of_subset hst (fun _ => zero_le _))

theorem massOf_strict_mono {d : SPMF α} {s t : Set α}
    (h : (d.support ∩ (t \ s)).Nonempty) (hst : s < t) : d.massOf s < d.massOf t := by
  rcases h with ⟨a, had, hat, has⟩
  refine' ENNReal.tsum_lt_tsum (i := a) (d.massOf_ne_top s)
    (fun b => (Set.indicator_le_indicator_of_subset hst.le (fun _ => zero_le _) _)) _
  rw [Set.indicator_of_not_mem has, Set.indicator_of_mem hat, zero_lt_iff]
  exact apply_ne_zero_of_mem_support had

theorem tsum_subtype_eq_massOf (d : SPMF α) (s : Set α) : d.massOf s = ∑' i : s, d i :=
  (tsum_subtype s d).symm

theorem massOf_iUnion_nat (d : SPMF α) (s : ℕ → Set α) :
    d.massOf (⋃ i, s i) ≤ ∑' i, d.massOf (s i) := by
  simp_rw [tsum_subtype_eq_massOf]
  exact ENNReal.tsum_iUnion_le_tsum _ _

@[simp]
theorem massOf_singleton (d : SPMF α) (a : α) : d.massOf {a} = d a := by
  rw [tsum_subtype_eq_massOf, tsum_singleton]

theorem massOf_union_disjoint (d : SPMF α) (s t : Set α) (hst : Disjoint s t) :
    d.massOf (s ∪ t) = d.massOf s + d.massOf t := by
  simp_rw [tsum_subtype_eq_massOf]
  exact tsum_union_disjoint hst ENNReal.summable ENNReal.summable

theorem massOf_pair_disjoint (d : SPMF α) {a b : α} (hab : a ≠ b) :
    d.massOf {a, b} = d a + d b := by
  rw [← d.massOf_singleton a, ← d.massOf_singleton b]
  convert d.massOf_union_disjoint {a} {b} _
  simp only [Set.disjoint_singleton_left, Set.mem_singleton_iff, hab, not_false_eq_true]

theorem massOf_caratheodory (d : SPMF α) (s t : Set α) :
    d.massOf t = d.massOf (t ∩ s) + d.massOf (t \ s) := by
  nth_rewrite 1 [← Set.inter_union_diff t s]
  exact d.massOf_union_disjoint _ _ Set.disjoint_sdiff_inter.symm

theorem massOf_injective : (SPMF.massOf : SPMF α → Set α → ℝ≥0∞).Injective := fun d₁ d₂ h => by
  ext
  simp_rw [← massOf_singleton, h]

theorem massOf_inj (d₁ d₂ : SPMF α) : d₁.massOf = d₂.massOf ↔ d₁ = d₂ := massOf_injective.eq_iff

theorem massOf_eq_zero_iff (d : SPMF α) (s : Set α) : d.massOf s = 0 ↔ ∀ a ∈ s, d a = 0 := by
  refine' ENNReal.tsum_eq_zero.trans _
  simp_rw [Set.indicator_apply_eq_zero]

theorem massOf_eq_zero_iff_support_disjoint (d : SPMF α) (s : Set α) :
    d.massOf s = 0 ↔ Disjoint d.support s := by
  simp_rw [massOf_eq_zero_iff, d.support_disjoint_iff]

theorem massOf_eq_zero_iff_disjoint_support (d : SPMF α) (s : Set α) :
    d.massOf s = 0 ↔ Disjoint s d.support := by
  simp_rw [massOf_eq_zero_iff, d.disjoint_support_iff]

@[simp]
theorem massOf_apply_inter_support (d : SPMF α) (s : Set α) :
    d.massOf (s ∩ d.support) = d.massOf s := by
  simp_rw [massOf_def, support_def, Set.indicator_inter_support]

theorem massOf_mono' (d : SPMF α) {s t : Set α} (h : s ∩ d.support ⊆ t) :
    d.massOf s ≤ d.massOf t := d.massOf_apply_inter_support s ▸ d.massOf_mono h

theorem massOf_apply_eq_of_inter_support_eq (d : SPMF α) {s t : Set α}
    (h : s ∩ d.support = t ∩ d.support) : d.massOf s = d.massOf t :=
  le_antisymm (d.massOf_mono' (h.symm ▸ Set.inter_subset_left t d.support))
    (d.massOf_mono' (h ▸ Set.inter_subset_left s d.support))

theorem apply_massOf_eq_mass_iff (d : SPMF α) (s : Set α) :
    d.massOf s = d.mass ↔ d.support ⊆ s := by
  refine' ⟨fun h => _, fun h => _⟩
  · by_contra h'
    rw [Set.not_subset] at h'
    exact ((d.massOf_lt_mass_of_exists_mem_support_nmem h').ne h)
  · rw [← massOf_support]
    refine' massOf_apply_eq_of_inter_support_eq _ _
    rwa [Set.inter_self, Set.inter_eq_right]

theorem apply_lt_mass_of_support_nontrivial {d : SPMF α} (h : d.support.Nontrivial) :
    ∀ a, d a < d.mass := fun a => by
  rcases h.exists_ne a with ⟨b, hbd, hba⟩
  refine' lt_of_lt_of_le (d.massOf_pair_disjoint hba ▸ _) (d.massOf_le_mass {b, a})
  rw [add_comm]
  exact ENNReal.lt_add_right (d.apply_ne_top a) (apply_ne_zero_of_mem_support hbd)

theorem apply_ne_mass_of_support_nontrivial {d : SPMF α} (h : d.support.Nontrivial) :
    ∀ a, d a ≠ d.mass := fun a => (d.apply_lt_mass_of_support_nontrivial h a).ne

theorem support_subsingleton_of_apply_eq_mass {d : SPMF α} (h : ∃ a, d a = d.mass) :
    d.support.Subsingleton := by
  rcases h with ⟨a, ha⟩
  by_contra hd
  rw [Set.not_subsingleton_iff] at hd
  exact apply_ne_mass_of_support_nontrivial hd a ha

theorem apply_eq_mass_of_support_singleton {d : SPMF α} {a : α} (ha : d.support = {a}) :
    d a = d.mass := by
  rw [← d.massOf_singleton a, ← massOf_support]
  exact d.massOf_apply_eq_of_inter_support_eq (ha ▸ rfl)

theorem exists_apply_eq_mass_of_support_subsingleton [Inhabited α] {d : SPMF α}
    (ha : d.support.Subsingleton) : ∃ a, d a = d.mass := by
  rcases ha.eq_empty_or_singleton with (ha | ⟨a, ha⟩)
  · exact ⟨_, apply_eq_mass_of_support_empty ha default⟩
  · exact ⟨_, apply_eq_mass_of_support_singleton ha⟩

theorem support_subsingleton_iff_exists_apply_eq_mass [Inhabited α] {d : SPMF α} :
    d.support.Subsingleton ↔ ∃ a, d a = d.mass :=
  ⟨exists_apply_eq_mass_of_support_subsingleton, support_subsingleton_of_apply_eq_mass⟩

theorem support_nontrivial_iff_apply_ne_mass [Inhabited α] {d : SPMF α} :
    d.support.Nontrivial ↔ ∀ a, d a ≠ d.mass := by
  rw [← Set.not_subsingleton_iff, support_subsingleton_iff_exists_apply_eq_mass, not_exists]

theorem support_nontrivial_iff_apply_lt_mass [Inhabited α] {d : SPMF α} :
    d.support.Nontrivial ↔ ∀ a, d a < d.mass := by
  rw [support_nontrivial_iff_apply_ne_mass]
  exact ⟨fun h a => (d.le_mass a).lt_of_ne (h a), fun h a => (h a).ne⟩

theorem apply_eq_mass_iff_of_mem_support {d : SPMF α} {a : α}
    (had : a ∈ d.support) : d a = d.mass ↔ d.support = {a} := by
  refine' ⟨fun ha => _, fun ha => _⟩
  · rcases Set.eq_singleton_or_nontrivial had with (had | had)
    · assumption
    · exact (apply_ne_mass_of_support_nontrivial had a ha).elim
  · exact apply_eq_mass_of_support_singleton ha


end SPMF
