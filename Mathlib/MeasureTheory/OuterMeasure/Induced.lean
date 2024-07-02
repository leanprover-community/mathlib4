/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Induced Outer Measure

We can extend a function defined on a subset of `Set α` to an outer measure.
The underlying function is called `extend`, and the measure it induces is called
`inducedOuterMeasure`.

Some lemmas below are proven twice, once in the general case, and one where the function `m`
is only defined on measurable sets (i.e. when `P = MeasurableSet`). In the latter cases, we can
remove some hypotheses in the statement. The general version has the same name, but with a prime
at the end.

## Tags

outer measure

-/

#align_import measure_theory.measure.outer_measure from "leanprover-community/mathlib"@"343e80208d29d2d15f8050b929aa50fe4ce71b55"

noncomputable section

open Set Function Filter
open scoped Classical NNReal Topology ENNReal

namespace MeasureTheory

open OuterMeasure


section Extend

variable {α : Type*} {P : α → Prop}
variable (m : ∀ s : α, P s → ℝ≥0∞)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h
#align measure_theory.extend MeasureTheory.extend

theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]
#align measure_theory.extend_eq MeasureTheory.extend_eq

theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ := by simp [extend, h]
#align measure_theory.extend_eq_top MeasureTheory.extend_eq_top

theorem smul_extend {R} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] {c : R} (hc : c ≠ 0) :
    c • extend m = extend fun s h => c • m s h := by
  ext1 s
  dsimp [extend]
  by_cases h : P s
  · simp [h]
  · simp [h, ENNReal.smul_top, hc]
#align measure_theory.smul_extend MeasureTheory.smul_extend

theorem le_extend {s : α} (h : P s) : m s h ≤ extend m s := by
  simp only [extend, le_iInf_iff]
  intro
  rfl
#align measure_theory.le_extend MeasureTheory.le_extend

-- TODO: why this is a bad `congr` lemma?
theorem extend_congr {β : Type*} {Pb : β → Prop} {mb : ∀ s : β, Pb s → ℝ≥0∞} {sa : α} {sb : β}
    (hP : P sa ↔ Pb sb) (hm : ∀ (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
    extend m sa = extend mb sb :=
  iInf_congr_Prop hP fun _h => hm _ _
#align measure_theory.extend_congr MeasureTheory.extend_congr

@[simp]
theorem extend_top {α : Type*} {P : α → Prop} : extend (fun _ _ => ∞ : ∀ s : α, P s → ℝ≥0∞) = ⊤ :=
  funext fun _ => iInf_eq_top.mpr fun _ => rfl
#align measure_theory.extend_top MeasureTheory.extend_top

end Extend

section ExtendSet

variable {α : Type*} {P : Set α → Prop}
variable {m : ∀ s : Set α, P s → ℝ≥0∞}
variable (P0 : P ∅) (m0 : m ∅ P0 = 0)
variable (PU : ∀ ⦃f : ℕ → Set α⦄ (_hm : ∀ i, P (f i)), P (⋃ i, f i))
variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i))

variable (msU : ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, P (f i)), m (⋃ i, f i) (PU hm) ≤ ∑' i, m (f i) (hm i))
variable (m_mono : ∀ ⦃s₁ s₂ : Set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0
#align measure_theory.extend_empty MeasureTheory.extend_empty

theorem extend_iUnion_nat {f : ℕ → Set α} (hm : ∀ i, P (f i))
    (mU : m (⋃ i, f i) (PU hm) = ∑' i, m (f i) (hm i)) :
    extend m (⋃ i, f i) = ∑' i, extend m (f i) :=
  (extend_eq _ _).trans <|
    mU.trans <| by
      congr with i
      rw [extend_eq]
#align measure_theory.extend_Union_nat MeasureTheory.extend_iUnion_nat

section Subadditive

theorem extend_iUnion_le_tsum_nat' (s : ℕ → Set α) :
    extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) := by
  by_cases h : ∀ i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · cases' not_forall.1 h with i hi
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)
#align measure_theory.extend_Union_le_tsum_nat' MeasureTheory.extend_iUnion_le_tsum_nat'

end Subadditive

section Mono

theorem extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ := by
  refine le_iInf ?_
  intro h₂
  rw [extend_eq m h₁]
  exact m_mono h₁ h₂ hs
#align measure_theory.extend_mono' MeasureTheory.extend_mono'

end Mono

section Unions

theorem extend_iUnion {β} [Countable β] {f : β → Set α} (hd : Pairwise (Disjoint on f))
    (hm : ∀ i, P (f i)) : extend m (⋃ i, f i) = ∑' i, extend m (f i) := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂, ← tsum_iUnion_decode₂]
  · exact
      extend_iUnion_nat PU (fun n => Encodable.iUnion_decode₂_cases P0 hm)
        (mU _ (Encodable.iUnion_decode₂_disjoint_on hd))
  · exact extend_empty P0 m0
#align measure_theory.extend_Union MeasureTheory.extend_iUnion

theorem extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
    extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ := by
  rw [union_eq_iUnion,
    extend_iUnion P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂, h₁⟩),
    tsum_fintype]
  simp
#align measure_theory.extend_union MeasureTheory.extend_union

end Unions

variable (m)

/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)
#align measure_theory.induced_outer_measure MeasureTheory.inducedOuterMeasure

variable {m P0 m0}

theorem le_inducedOuterMeasure {μ : OuterMeasure α} :
    μ ≤ inducedOuterMeasure m P0 m0 ↔ ∀ (s) (hs : P s), μ s ≤ m s hs :=
  le_ofFunction.trans <| forall_congr' fun _s => le_iInf_iff
#align measure_theory.le_induced_outer_measure MeasureTheory.le_inducedOuterMeasure

/-- If `P u` is `False` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = inducedOuterMeasure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma implies that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s` and `y ∈ t`. -/
theorem inducedOuterMeasure_union_of_false_of_nonempty_inter {s t : Set α}
    (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → ¬P u) :
    inducedOuterMeasure m P0 m0 (s ∪ t) =
      inducedOuterMeasure m P0 m0 s + inducedOuterMeasure m P0 m0 t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hsu htu => @iInf_of_empty _ _ _ ⟨h u hsu htu⟩ _
#align measure_theory.induced_outer_measure_union_of_false_of_nonempty_inter MeasureTheory.inducedOuterMeasure_union_of_false_of_nonempty_inter

theorem inducedOuterMeasure_eq_extend' {s : Set α} (hs : P s) :
    inducedOuterMeasure m P0 m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)
#align measure_theory.induced_outer_measure_eq_extend' MeasureTheory.inducedOuterMeasure_eq_extend'

theorem inducedOuterMeasure_eq' {s : Set α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend' PU msU m_mono hs).trans <| extend_eq _ _
#align measure_theory.induced_outer_measure_eq' MeasureTheory.inducedOuterMeasure_eq'

theorem inducedOuterMeasure_eq_iInf (s : Set α) :
    inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s ⊆ t), m t ht := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro t ht hs
    refine le_trans (measure_mono hs) ?_
    exact le_of_eq (inducedOuterMeasure_eq' _ msU m_mono _)
  · refine le_iInf ?_
    intro f
    refine le_iInf ?_
    intro hf
    refine le_trans ?_ (extend_iUnion_le_tsum_nat' _ msU _)
    refine le_iInf ?_
    intro h2f
    exact iInf_le_of_le _ (iInf_le_of_le h2f <| iInf_le _ hf)
#align measure_theory.induced_outer_measure_eq_infi MeasureTheory.inducedOuterMeasure_eq_iInf

theorem inducedOuterMeasure_preimage (f : α ≃ α) (Pm : ∀ s : Set α, P (f ⁻¹' s) ↔ P s)
    (mm : ∀ (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) {A : Set α} :
    inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m P0 m0 A := by
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono, inducedOuterMeasure_eq_iInf _ msU m_mono]; symm
    refine f.injective.preimage_surjective.iInf_congr (preimage f) fun s => ?_
    refine iInf_congr_Prop (Pm s) ?_; intro hs
    refine iInf_congr_Prop f.surjective.preimage_subset_preimage_iff ?_
    intro _; exact mm s hs
#align measure_theory.induced_outer_measure_preimage MeasureTheory.inducedOuterMeasure_preimage

theorem inducedOuterMeasure_exists_set {s : Set α} (hs : inducedOuterMeasure m P0 m0 s ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t : Set α,
      P t ∧ s ⊆ t ∧ inducedOuterMeasure m P0 m0 t ≤ inducedOuterMeasure m P0 m0 s + ε := by
  have h := ENNReal.lt_add_right hs hε
  conv at h =>
    lhs
    rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
  simp only [iInf_lt_iff] at h
  rcases h with ⟨t, h1t, h2t, h3t⟩
  exact
    ⟨t, h1t, h2t, le_trans (le_of_eq <| inducedOuterMeasure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩
#align measure_theory.induced_outer_measure_exists_set MeasureTheory.inducedOuterMeasure_exists_set

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `ofFunction_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
theorem inducedOuterMeasure_caratheodory (s : Set α) :
    MeasurableSet[(inducedOuterMeasure m P0 m0).caratheodory] s ↔
      ∀ t : Set α,
        P t →
          inducedOuterMeasure m P0 m0 (t ∩ s) + inducedOuterMeasure m P0 m0 (t \ s) ≤
            inducedOuterMeasure m P0 m0 t := by
  rw [isCaratheodory_iff_le]
  constructor
  · intro h t _ht
    exact h t
  · intro h u
    conv_rhs => rw [inducedOuterMeasure_eq_iInf _ msU m_mono]
    refine le_iInf ?_
    intro t
    refine le_iInf ?_
    intro ht
    refine le_iInf ?_
    intro h2t
    refine le_trans ?_ ((h t ht).trans_eq <| inducedOuterMeasure_eq' _ msU m_mono ht)
    gcongr
#align measure_theory.induced_outer_measure_caratheodory MeasureTheory.inducedOuterMeasure_caratheodory

end ExtendSet

/-! If `P` is `MeasurableSet` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/


section MeasurableSpace

variable {α : Type*} [MeasurableSpace α]
variable {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
variable (m0 : m ∅ MeasurableSet.empty = 0)
variable
  (mU :
    ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion hm) = ∑' i, m (f i) (hm i))

theorem extend_mono {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (hs : s₁ ⊆ s₂) :
    extend m s₁ ≤ extend m s₂ := by
  refine le_iInf ?_; intro h₂
  have :=
    extend_union MeasurableSet.empty m0 MeasurableSet.iUnion mU disjoint_sdiff_self_right h₁
      (h₂.diff h₁)
  rw [union_diff_cancel hs] at this
  rw [← extend_eq m]
  exact le_iff_exists_add.2 ⟨_, this⟩
#align measure_theory.extend_mono MeasureTheory.extend_mono

theorem extend_iUnion_le_tsum_nat : ∀ s : ℕ → Set α,
    extend m (⋃ i, s i) ≤ ∑' i, extend m (s i) := by
  refine extend_iUnion_le_tsum_nat' MeasurableSet.iUnion ?_; intro f h
  simp (config := { singlePass := true }) only [iUnion_disjointed.symm]
  rw [mU (MeasurableSet.disjointed h) (disjoint_disjointed _)]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← extend_eq m, ← extend_eq m]
  exact extend_mono m0 mU (MeasurableSet.disjointed h _) (disjointed_le f _)
#align measure_theory.extend_Union_le_tsum_nat MeasureTheory.extend_iUnion_le_tsum_nat

theorem inducedOuterMeasure_eq_extend {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = extend m s :=
  ofFunction_eq s (fun _t => extend_mono m0 mU hs) (extend_iUnion_le_tsum_nat m0 mU)
#align measure_theory.induced_outer_measure_eq_extend MeasureTheory.inducedOuterMeasure_eq_extend

theorem inducedOuterMeasure_eq {s : Set α} (hs : MeasurableSet s) :
    inducedOuterMeasure m MeasurableSet.empty m0 s = m s hs :=
  (inducedOuterMeasure_eq_extend m0 mU hs).trans <| extend_eq _ _
#align measure_theory.induced_outer_measure_eq MeasureTheory.inducedOuterMeasure_eq

end MeasurableSpace

namespace OuterMeasure

variable {α : Type*} [MeasurableSpace α] (m : OuterMeasure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : OuterMeasure α :=
  inducedOuterMeasure (fun s _ => m s) MeasurableSet.empty m.empty
#align measure_theory.outer_measure.trim MeasureTheory.OuterMeasure.trim

theorem le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁ ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_inducedOuterMeasure
#align measure_theory.outer_measure.le_trim_iff MeasureTheory.OuterMeasure.le_trim_iff

theorem le_trim : m ≤ m.trim := le_trim_iff.2 fun _ _ ↦ le_rfl
#align measure_theory.outer_measure.le_trim MeasureTheory.OuterMeasure.le_trim

@[simp] -- Porting note: added `simp`
theorem trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s :=
  inducedOuterMeasure_eq' MeasurableSet.iUnion (fun f _hf => measure_iUnion_le f)
    (fun _ _ _ _ h => measure_mono h) hs
#align measure_theory.outer_measure.trim_eq MeasureTheory.OuterMeasure.trim_eq

theorem trim_congr {m₁ m₂ : OuterMeasure α} (H : ∀ {s : Set α}, MeasurableSet s → m₁ s = m₂ s) :
    m₁.trim = m₂.trim := by
  simp (config := { contextual := true }) only [trim, H]
#align measure_theory.outer_measure.trim_congr MeasureTheory.OuterMeasure.trim_congr

@[mono]
theorem trim_mono : Monotone (trim : OuterMeasure α → OuterMeasure α) := fun _m₁ _m₂ H _s =>
  iInf₂_mono fun _f _hs => ENNReal.tsum_le_tsum fun _b => iInf_mono fun _hf => H _
#align measure_theory.outer_measure.trim_mono MeasureTheory.OuterMeasure.trim_mono

/-- `OuterMeasure.trim` is antitone in the σ-algebra. -/
theorem trim_anti_measurableSpace (m : OuterMeasure α) {m0 m1 : MeasurableSpace α}
    (h : m0 ≤ m1) : @trim _ m1 m ≤ @trim _ m0 m := by
  simp only [le_trim_iff]
  intro s hs
  rw [trim_eq _ (h s hs)]

theorem trim_le_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_trim_iff.trans <| forall₂_congr fun s hs => by rw [trim_eq _ hs]
#align measure_theory.outer_measure.trim_le_trim_iff MeasureTheory.OuterMeasure.trim_le_trim_iff

theorem trim_eq_trim_iff {m₁ m₂ : OuterMeasure α} :
    m₁.trim = m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s = m₂ s := by
  simp only [le_antisymm_iff, trim_le_trim_iff, forall_and]
#align measure_theory.outer_measure.trim_eq_trim_iff MeasureTheory.OuterMeasure.trim_eq_trim_iff

theorem trim_eq_iInf (s : Set α) : m.trim s = ⨅ (t) (_ : s ⊆ t) (_ : MeasurableSet t), m t := by
  simp (config := { singlePass := true }) only [iInf_comm]
  exact
    inducedOuterMeasure_eq_iInf MeasurableSet.iUnion (fun f _ => measure_iUnion_le f)
      (fun _ _ _ _ h => measure_mono h) s
#align measure_theory.outer_measure.trim_eq_infi MeasureTheory.OuterMeasure.trim_eq_iInf

theorem trim_eq_iInf' (s : Set α) : m.trim s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, m t := by
  simp [iInf_subtype, iInf_and, trim_eq_iInf]
#align measure_theory.outer_measure.trim_eq_infi' MeasureTheory.OuterMeasure.trim_eq_iInf'

theorem trim_trim (m : OuterMeasure α) : m.trim.trim = m.trim :=
  trim_eq_trim_iff.2 fun _s => m.trim_eq
#align measure_theory.outer_measure.trim_trim MeasureTheory.OuterMeasure.trim_trim

@[simp]
theorem trim_top : (⊤ : OuterMeasure α).trim = ⊤ :=
  top_unique <| le_trim _
#align measure_theory.outer_measure.trim_top MeasureTheory.OuterMeasure.trim_top

@[simp]
theorem trim_zero : (0 : OuterMeasure α).trim = 0 :=
  ext fun s =>
    le_antisymm
      ((measure_mono (subset_univ s)).trans_eq <| trim_eq _ MeasurableSet.univ)
      (zero_le _)
#align measure_theory.outer_measure.trim_zero MeasureTheory.OuterMeasure.trim_zero

theorem trim_sum_ge {ι} (m : ι → OuterMeasure α) : (sum fun i => (m i).trim) ≤ (sum m).trim :=
  fun s => by
  simp [trim_eq_iInf];
    exact fun t st ht =>
      ENNReal.tsum_le_tsum fun i => iInf_le_of_le t <| iInf_le_of_le st <| iInf_le _ ht
#align measure_theory.outer_measure.trim_sum_ge MeasureTheory.OuterMeasure.trim_sum_ge

theorem exists_measurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = m.trim s := by
  simp only [trim_eq_iInf]; set ms := ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), m t
  by_cases hs : ms = ∞
  · simp only [hs]
    simp only [iInf_eq_top, ms] at hs
    exact ⟨univ, subset_univ s, MeasurableSet.univ, hs _ (subset_univ s) MeasurableSet.univ⟩
  · have : ∀ r > ms, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < r := by
      intro r hs
      have : ∃t, MeasurableSet t ∧ s ⊆ t ∧ m t < r := by simpa [ms, iInf_lt_iff] using hs
      rcases this with ⟨t, hmt, hin, hlt⟩
      exists t
    have : ∀ n : ℕ, ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t < ms + (n : ℝ≥0∞)⁻¹ := by
      intro n
      refine this _ (ENNReal.lt_add_right hs ?_)
      simp
    choose t hsub hm hm' using this
    refine ⟨⋂ n, t n, subset_iInter hsub, MeasurableSet.iInter hm, ?_⟩
    have : Tendsto (fun n : ℕ => ms + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (ms + 0)) :=
      tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at this
    refine le_antisymm (ge_of_tendsto' this fun n => ?_) ?_
    · exact le_trans (measure_mono <| iInter_subset t n) (hm' n).le
    · refine iInf_le_of_le (⋂ n, t n) ?_
      refine iInf_le_of_le (subset_iInter hsub) ?_
      exact iInf_le _ (MeasurableSet.iInter hm)
#align measure_theory.outer_measure.exists_measurable_superset_eq_trim MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim

theorem exists_measurable_superset_of_trim_eq_zero {m : OuterMeasure α} {s : Set α}
    (h : m.trim s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = 0 := by
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
  exact ⟨t, hst, ht, h ▸ hm⟩
#align measure_theory.outer_measure.exists_measurable_superset_of_trim_eq_zero MeasureTheory.OuterMeasure.exists_measurable_superset_of_trim_eq_zero

/-- If `μ i` is a countable family of outer measures, then for every set `s` there exists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`. -/
theorem exists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι → OuterMeasure α)
    (s : Set α) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = (μ i).trim s := by
  choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s
  replace hst := subset_iInter hst
  replace ht := MeasurableSet.iInter ht
  refine ⟨⋂ i, t i, hst, ht, fun i => le_antisymm ?_ ?_⟩
  exacts [hμt i ▸ (μ i).mono (iInter_subset _ _), (measure_mono hst).trans_eq ((μ i).trim_eq ht)]
#align measure_theory.outer_measure.exists_measurable_superset_forall_eq_trim MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim

/-- If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `m₂.trim`,
and `m₃ s`. -/
theorem trim_binop {m₁ m₂ m₃ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    (h : ∀ s, m₁ s = op (m₂ s) (m₃ s)) (s : Set α) : m₁.trim s = op (m₂.trim s) (m₃.trim s) := by
  rcases exists_measurable_superset_forall_eq_trim ![m₁, m₂, m₃] s with ⟨t, _hst, _ht, htm⟩
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ] at htm
  rw [← htm.1, ← htm.2.1, ← htm.2.2.1, h]
#align measure_theory.outer_measure.trim_binop MeasureTheory.OuterMeasure.trim_binop

/-- If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.trim`. -/
theorem trim_op {m₁ m₂ : OuterMeasure α} {op : ℝ≥0∞ → ℝ≥0∞} (h : ∀ s, m₁ s = op (m₂ s))
    (s : Set α) : m₁.trim s = op (m₂.trim s) :=
  @trim_binop α _ m₁ m₂ 0 (fun a _b => op a) h s
#align measure_theory.outer_measure.trim_op MeasureTheory.OuterMeasure.trim_op

/-- `trim` is additive. -/
theorem trim_add (m₁ m₂ : OuterMeasure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
  ext <| trim_binop (add_apply m₁ m₂)
#align measure_theory.outer_measure.trim_add MeasureTheory.OuterMeasure.trim_add

/-- `trim` respects scalar multiplication. -/
theorem trim_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (m : OuterMeasure α) : (c • m).trim = c • m.trim :=
  ext <| trim_op (smul_apply c m)
#align measure_theory.outer_measure.trim_smul MeasureTheory.OuterMeasure.trim_smul

/-- `trim` sends the supremum of two outer measures to the supremum of the trimmed measures. -/
theorem trim_sup (m₁ m₂ : OuterMeasure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim :=
  ext fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm
#align measure_theory.outer_measure.trim_sup MeasureTheory.OuterMeasure.trim_sup

/-- `trim` sends the supremum of a countable family of outer measures to the supremum
of the trimmed measures. -/
theorem trim_iSup {ι} [Countable ι] (μ : ι → OuterMeasure α) :
    trim (⨆ i, μ i) = ⨆ i, trim (μ i) := by
  simp_rw [← @iSup_plift_down _ ι]
  ext1 s
  obtain ⟨t, _, _, hμt⟩ :=
    exists_measurable_superset_forall_eq_trim
      (Option.elim' (⨆ i, μ (PLift.down i)) (μ ∘ PLift.down)) s
  simp only [Option.forall, Option.elim'] at hμt
  simp only [iSup_apply, ← hμt.1]
  exact iSup_congr hμt.2
#align measure_theory.outer_measure.trim_supr MeasureTheory.OuterMeasure.trim_iSup

/-- The trimmed property of a measure μ states that `μ.toOuterMeasure.trim = μ.toOuterMeasure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
theorem restrict_trim {μ : OuterMeasure α} {s : Set α} (hs : MeasurableSet s) :
    (restrict s μ).trim = restrict s μ.trim := by
  refine le_antisymm (fun t => ?_) (le_trim_iff.2 fun t ht => ?_)
  · rw [restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (t ∩ s) with ⟨t', htt', ht', hμt'⟩
    rw [← hμt']
    rw [inter_subset] at htt'
    refine (measure_mono htt').trans ?_
    rw [trim_eq _ (hs.compl.union ht'), restrict_apply, union_inter_distrib_right, compl_inter_self,
      Set.empty_union]
    exact measure_mono inter_subset_left
  · rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply]
#align measure_theory.outer_measure.restrict_trim MeasureTheory.OuterMeasure.restrict_trim

end OuterMeasure
