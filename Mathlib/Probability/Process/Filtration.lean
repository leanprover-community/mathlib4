/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict

/-!
# Filtrations

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `MeasureTheory.Filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `MeasureTheory.SigmaFiniteFiltration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `MeasureTheory.Filtration.natural`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `MeasureTheory.adapted`.
* `MeasureTheory.Filtration.rightCont`: the right-continuation of a filtration.
* `MeasureTheory.Filtration.IsRightContinuous`: a filtration is right-continuous if it is equal
  to its right-continuation.

## Main results

* `MeasureTheory.Filtration.instCompleteLattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/

@[expose] public section


open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

/-- A `Filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure Filtration {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω) where
  /-- The sequence of sub-σ-algebras of `m` -/
  seq : ι → MeasurableSpace Ω
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

attribute [coe] Filtration.seq

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

instance [Preorder ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorder ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace Ω) = g) : f = g := by
  cases f; cases g; congr

variable (ι) in
/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : MeasurableSpace Ω) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

@[simp]
theorem const_apply {m' : MeasurableSpace Ω} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl

instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance : Bot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

instance : Top (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : Max (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
theorem coeFn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

instance : Min (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
theorem coeFn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

instance : SupSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sSup ((fun f : Filtration ι m => f i) '' s)
      mono' := fun i j hij => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine (f.mono hij).trans ?_
        have hfj_mem : f j ∈ (fun g : Filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_sSup hfj_mem
      le' := fun i => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, _, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

theorem sSup_def (s : Set (Filtration ι m)) (i : ι) :
    sSup s i = sSup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

open scoped Classical in
noncomputable instance : InfSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m
      mono' := fun i j hij => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true, le_sInf_iff, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun f hf_mem => le_trans ?_ (f.mono hij)
        have hfi_mem : f i ∈ (fun g : Filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact sInf_le hfi_mem
      le' := fun i => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_trans (sInf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

open scoped Classical in
theorem sInf_def (s : Set (Filtration ι m)) (i : ι) :
    sInf s i = if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

noncomputable instance instCompleteLattice : CompleteLattice (Filtration ι m) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ h_fg h_gh i := (h_fg i).trans (h_gh i)
  le_antisymm _ _ h_fg h_gf := Filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)
  sup := (· ⊔ ·)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h_fh h_gh i := sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h_fg h_fh i := le_inf (h_fg i) (h_fh i)
  le_sSup _ f hf_mem _ := le_sSup ⟨f, hf_mem, rfl⟩
  sSup_le s f h_forall i :=
    sSup_le fun m' hm' => by
      obtain ⟨g, hg_mem, hfm'⟩ := hm'
      rw [← hfm']
      exact h_forall g hg_mem i
  sInf_le s f hf_mem i := by
    have hs : s.Nonempty := ⟨f, hf_mem⟩
    simp only [sInf_def, hs, if_true]
    exact sInf_le ⟨f, hf_mem, rfl⟩
  le_sInf s f h_forall i := by
    by_cases hs : s.Nonempty
    swap; · simp only [sInf_def, hs, if_false]; exact f.le i
    simp only [sInf_def, hs, if_true, le_sInf_iff, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact fun g hg_mem => h_forall g hg_mem i
  le_top f i := f.le' i
  bot_le _ _ := bot_le

end Filtration

theorem measurableSet_of_filtration [Preorder ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
    (hs : MeasurableSet[f i] s) : MeasurableSet[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class SigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))

instance sigmaFinite_of_sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) :=
  hf.SigmaFinite _

instance (priority := 100) IsFiniteMeasure.sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω)
    (f : Filtration ι m) [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by infer_instance⟩

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condExp_filtration [Preorder ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Filtration ι m} {g : Ω → ℝ} (hg : Integrable g μ) :
    UniformIntegrable (fun i => μ[g|f i]) 1 μ :=
  hg.uniformIntegrable_condExp f.le

theorem Filtration.condExp_condExp [Preorder ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : Ω → E) {μ : Measure Ω} (ℱ : Filtration ι m)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i] := condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j)

section OfSet

variable [Preorder ι]

/-- Given a sequence of measurable sets `(sₙ)`, `filtrationOfSet` is the smallest filtration
such that `sₙ` is measurable with respect to the `n`-th sub-σ-algebra in `filtrationOfSet`. -/
def filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet (s i)) : Filtration ι m where
  seq i := MeasurableSpace.generateFrom {t | ∃ j ≤ i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k

theorem measurableSet_filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[m] (s i)) (i : ι)
    {j : ι} (hj : j ≤ i) : MeasurableSet[filtrationOfSet hsm i] (s j) :=
  MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩

theorem measurableSet_filtrationOfSet' {s : ι → Set Ω} (hsm : ∀ n, MeasurableSet[m] (s n))
    (i : ι) : MeasurableSet[filtrationOfSet hsm i] (s i) :=
  measurableSet_filtrationOfSet hsm i le_rfl

end OfSet

namespace Filtration

section IsRightContinuous

open scoped Classical in
/-- Given a filtration `𝓕`, its **right continuation** is the filtration `𝓕₊` defined as follows:
- If `i` is isolated on the right, then `𝓕₊ i := 𝓕 i`;
- Otherwise, `𝓕₊ i := ⨅ j > i, 𝓕 j`.
It is sometimes simply defined as `𝓕₊ i := ⨅ j > i, 𝓕 j` when the index type is `ℝ`. In the
general case this is not ideal however. If `i` is maximal for instance, then `𝓕₊ i = ⊤`, which
is inconvenient because `𝓕₊` is not  a `Filtration ι m` anymore. If the index type
is discrete (such as `ℕ`), then we would have `𝓕 = 𝓕₊` (i.e. `𝓕` is right-continuous) only if
`𝓕` is constant.

To avoid requiring a `TopologicalSpace` instance on `ι` in the definition, we endow `ι` with
the order topology `Preorder.topology` inside the definition. Say you write a statement about
`𝓕₊` which does not require a `TopologicalSpace` structure on `ι`,
but you wish to use a statement which requires a topology (such as `rightCont_def`).
Then you can endow `ι` with
the order topology by writing
```lean
  letI := Preorder.topology ι
  haveI : OrderTopology ι := ⟨rfl⟩
``` -/
noncomputable def rightCont [PartialOrder ι] (𝓕 : Filtration ι m) : Filtration ι m :=
  letI : TopologicalSpace ι := Preorder.topology ι
  { seq i := if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i
    mono' i j hij := by
      simp only [gt_iff_lt]
      split_ifs with hi hj hj
      · exact le_iInf₂ fun k hkj ↦ iInf₂_le k (hij.trans_lt hkj)
      · obtain rfl | hj := eq_or_ne j i
        · contradiction
        · exact iInf₂_le j (lt_of_le_of_ne hij hj.symm)
      · exact le_iInf₂ fun k hk ↦ 𝓕.mono (hij.trans hk.le)
      · exact 𝓕.mono hij
    le' i := by
      split_ifs with hi
      · obtain ⟨j, hj⟩ := (frequently_gt_nhds i).exists
        exact iInf₂_le_of_le j hj (𝓕.le j)
      · exact 𝓕.le i }

@[inherit_doc] scoped postfix:max "₊" => rightCont

open scoped Classical in
lemma rightCont_def [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = if (𝓝[>] i).NeBot then ⨅ j > i, 𝓕 j else 𝓕 i := by
  simp only [rightCont, OrderTopology.topology_eq_generate_intervals]

lemma rightCont_eq_of_nhdsGT_eq_bot [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : 𝓝[>] i = ⊥) :
    𝓕₊ i = 𝓕 i := by
  rw [rightCont_def, hi, neBot_iff, ne_self_iff_false, if_false]

/-- If the index type is a `SuccOrder`, then `𝓕₊ = 𝓕`. -/
lemma rightCont_eq_self [LinearOrder ι] [SuccOrder ι] (𝓕 : Filtration ι m) :
    𝓕₊ = 𝓕 := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  ext _
  rw [rightCont_eq_of_nhdsGT_eq_bot _ SuccOrder.nhdsGT]

lemma rightCont_eq_of_isMax [PartialOrder ι] (𝓕 : Filtration ι m) {i : ι} (hi : IsMax i) :
    𝓕₊ i = 𝓕 i := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ (hi.Ioi_eq ▸ nhdsWithin_empty i)

lemma rightCont_eq_of_exists_gt [LinearOrder ι] (𝓕 : Filtration ι m) {i : ι}
    (hi : ∃ j > i, Set.Ioo i j = ∅) :
    𝓕₊ i = 𝓕 i := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  obtain ⟨j, hij, hIoo⟩ := hi
  have hcov : i ⋖ j := covBy_iff_Ioo_eq.mpr ⟨hij, hIoo⟩
  exact rightCont_eq_of_nhdsGT_eq_bot _ <| CovBy.nhdsGT hcov

/-- If `i` is not isolated on the right, then `𝓕₊ i = ⨅ j > i, 𝓕 j`. This is for instance the case
when `ι` is a densely ordered linear order with no maximal elements and equipped with the order
topology, see `rightCont_eq`. -/
lemma rightCont_eq_of_neBot_nhdsGT [PartialOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    (𝓕 : Filtration ι m) (i : ι) [(𝓝[>] i).NeBot] :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  rw [rightCont_def, if_pos ‹(𝓝[>] i).NeBot›]

lemma rightCont_eq_of_not_isMax [LinearOrder ι] [DenselyOrdered ι]
    (𝓕 : Filtration ι m) {i : ι} (hi : ¬IsMax i) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  have : (𝓝[>] i).NeBot := nhdsGT_neBot_of_exists_gt (not_isMax_iff.mp hi)
  exact rightCont_eq_of_neBot_nhdsGT _ _

/-- If `ι` is a densely ordered linear order with no maximal elements, then no point is isolated
on the right, so that `𝓕₊ i = ⨅ j > i, 𝓕 j` holds for all `i`. This is in particular the
case when `ι := ℝ≥0`. -/
lemma rightCont_eq [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕₊ i = ⨅ j > i, 𝓕 j := 𝓕.rightCont_eq_of_not_isMax (not_isMax i)

variable [PartialOrder ι]

lemma le_rightCont (𝓕 : Filtration ι m) : 𝓕 ≤ 𝓕₊ := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · rw [rightCont_eq_of_neBot_nhdsGT]
    exact le_iInf₂ fun _ he => 𝓕.mono he.le
  · rw [rightCont_def, if_neg hne]

lemma rightCont_self (𝓕 : Filtration ι m) : 𝓕₊₊ = 𝓕₊ := by
  letI := Preorder.topology ι; haveI : OrderTopology ι := ⟨rfl⟩
  apply le_antisymm _ 𝓕₊.le_rightCont
  intro i
  by_cases hne : (𝓝[>] i).NeBot
  · have hineq : (⨅ j > i, 𝓕₊ j) ≤ ⨅ j > i, 𝓕 j := by
      apply le_iInf₂ fun u hu => ?_
      have hiou : Set.Ioo i u ∈ 𝓝[>] i := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Set.Iio u, (isOpen_Iio' u).mem_nhds hu, fun _ hx ↦ ⟨hx.2, hx.1⟩⟩
      obtain ⟨v, hv⟩ := hne.nonempty_of_mem hiou
      have hle₁ : (⨅ j > i, 𝓕₊ j) ≤ 𝓕₊ v := iInf₂_le_of_le v hv.1 le_rfl
      have hle₂ : 𝓕₊ v ≤ 𝓕 u := by
        by_cases hnv : (𝓝[>] v).NeBot
        · simpa [rightCont_eq_of_neBot_nhdsGT] using iInf₂_le_of_le u hv.2 le_rfl
        · simpa [rightCont_def, hnv] using 𝓕.mono hv.2.le
      exact hle₁.trans hle₂
    simpa [rightCont_eq_of_neBot_nhdsGT] using hineq
  · rw [rightCont_def, if_neg hne]

/-- A filtration `𝓕` is right continuous if it is equal to its right continuation `𝓕₊`. -/
class IsRightContinuous (𝓕 : Filtration ι m) where
    /-- The right continuity property. -/
    RC : 𝓕₊ ≤ 𝓕

lemma IsRightContinuous.eq {𝓕 : Filtration ι m} [h : IsRightContinuous 𝓕] :
    𝓕 = 𝓕₊ := le_antisymm 𝓕.le_rightCont h.RC

lemma isRightContinuous_rightCont (𝓕 : Filtration ι m) : 𝓕₊.IsRightContinuous :=
  ⟨(rightCont_self 𝓕).le⟩

lemma IsRightContinuous.measurableSet {𝓕 : Filtration ι m} [IsRightContinuous 𝓕] {i : ι}
    {s : Set Ω} (hs : MeasurableSet[𝓕₊ i] s) :
    MeasurableSet[𝓕 i] s := IsRightContinuous.eq (𝓕 := 𝓕) ▸ hs

/-- A filtration `𝓕` is said to satisfy the usual conditions if it is right continuous and `𝓕 0`
  and consequently `𝓕 t` is complete (i.e. contains all null sets) for all `t`. -/
class HasUsualConditions [OrderBot ι] (𝓕 : Filtration ι m) (μ : Measure Ω := by volume_tac)
    extends IsRightContinuous 𝓕 where
    /-- `𝓕 ⊥` contains all the null sets. -/
    IsComplete ⦃s : Set Ω⦄ (hs : μ s = 0) : MeasurableSet[𝓕 ⊥] s

variable [OrderBot ι]

instance {𝓕 : Filtration ι m} {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] {i : ι} :
    @Measure.IsComplete Ω (𝓕 i) (μ.trim <| 𝓕.le _) :=
  ⟨fun _ hs ↦ 𝓕.mono bot_le _ <| u.2 (measure_eq_zero_of_trim_eq_zero (Filtration.le 𝓕 _) hs)⟩

lemma HasUsualConditions.measurableSet_of_null
    (𝓕 : Filtration ι m) {μ : Measure Ω} [u : HasUsualConditions 𝓕 μ] (s : Set Ω) (hs : μ s = 0) :
    MeasurableSet[𝓕 ⊥] s :=
  u.2 hs

end IsRightContinuous

variable {β : ι → Type*} [∀ i, TopologicalSpace (β i)] [∀ i, MetrizableSpace (β i)]
  [mβ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
  [Preorder ι]

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that the sequence of functions is measurable with respect to
the filtration. -/
def natural (u : (i : ι) → Ω → β i) (hum : ∀ i, StronglyMeasurable (u i)) : Filtration ι m where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (u j) (mβ j)
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

section

open MeasurableSpace

theorem filtrationOfSet_eq_natural [∀ i, MulZeroOneClass (β i)] [∀ i, Nontrivial (β i)]
    {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[m] (s i)) :
    filtrationOfSet hsm = natural (fun i => (s i).indicator (fun _ => 1 : Ω → β i)) fun i =>
      stronglyMeasurable_one.indicator (hsm i) := by
  simp only [filtrationOfSet, natural, measurableSpace_iSup_eq, exists_prop, mk.injEq]
  ext1 i
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_)
  · rintro _ ⟨j, hij, rfl⟩
    refine measurableSet_generateFrom ⟨j, measurableSet_generateFrom ⟨hij, ?_⟩⟩
    rw [comap_eq_generateFrom]
    refine measurableSet_generateFrom ⟨{1}, measurableSet_singleton 1, ?_⟩
    ext x
    simp
  · rintro t ⟨n, ht⟩
    suffices MeasurableSpace.generateFrom {t | n ≤ i ∧
      MeasurableSet[MeasurableSpace.comap ((s n).indicator (fun _ => 1 : Ω → β n)) (mβ n)] t} ≤
        MeasurableSpace.generateFrom {t | ∃ (j : ι), j ≤ i ∧ s j = t} by
      exact this _ ht
    refine generateFrom_le ?_
    rintro t ⟨hn, u, _, hu'⟩
    obtain heq | heq | heq | heq := Set.indicator_const_preimage (s n) u (1 : β n)
    on_goal 4 => rw [Set.mem_singleton_iff] at heq
    all_goals rw [heq] at hu'; rw [← hu']
    exacts [MeasurableSet.univ, measurableSet_generateFrom ⟨n, hn, rfl⟩,
      MeasurableSet.compl (measurableSet_generateFrom ⟨n, hn, rfl⟩), measurableSet_empty _]

end

section Limit

variable {E : Type*} [Zero E] [TopologicalSpace E] {ℱ : Filtration ι m} {f : ι → Ω → E}
  {μ : Measure Ω}

open scoped Classical in
/-- Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost everywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limitProcess f ℱ μ` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `f` adapted to `ℱ`
converges to `limitProcess f ℱ μ` `μ`-almost everywhere. -/
noncomputable def limitProcess (f : ι → Ω → E) (ℱ : Filtration ι m)
    (μ : Measure Ω) :=
  if h : ∃ g : Ω → E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ) := by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]

theorem stronglyMeasurable_limit_process' : StronglyMeasurable[m] (limitProcess f ℱ μ) :=
  stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)

theorem memLp_limitProcess_of_eLpNorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F]
    {ℱ : Filtration ℕ m} {f : ℕ → Ω → F} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : MemLp (limitProcess f ℱ μ) p μ := by
  rw [limitProcess]
  split_ifs with h
  · refine ⟨StronglyMeasurable.aestronglyMeasurable
      ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
      lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
        (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top : ↑R < ∞))⟩
    simp_rw [liminf_eq, eventually_atTop]
    exact sSup_le fun b ⟨a, ha⟩ => (ha a le_rfl).trans (hbdd _)
  · exact MemLp.zero

end Limit

section piLE

/-! ### Filtration of the first events -/

open MeasurableSpace Preorder

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The canonical filtration on the product space `Π i, X i`, where `piLE i`
consists of measurable sets depending only on coordinates `≤ i`. -/
def piLE : @Filtration (Π i, X i) ι _ pi where
  seq i := pi.comap (restrictLe i)
  mono' i j hij := by
    simp only
    rw [← restrictLe₂_comp_restrictLe hij, ← comap_comp]
    exact comap_mono (measurable_restrictLe₂ _).comap_le
  le' i := (measurable_restrictLe i).comap_le

variable [LocallyFiniteOrderBot ι]

lemma piLE_eq_comap_frestrictLe (i : ι) : piLE (X := X) i = pi.comap (frestrictLe i) := by
  apply le_antisymm
  · simp_rw [piLE, ← piCongrLeft_comp_frestrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
    exact MeasurableSpace.comap_mono <| Measurable.comap_le (by fun_prop)
  · rw [← piCongrLeft_comp_restrictLe, ← MeasurableEquiv.coe_piCongrLeft, ← comap_comp]
    exact MeasurableSpace.comap_mono <| Measurable.comap_le (by fun_prop)

end piLE

section piFinset

open MeasurableSpace Finset

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The filtration of events which only depends on finitely many coordinates
on the product space `Π i, X i`, `piFinset s` consists of measurable sets depending only on
coordinates in `s`, where `s : Finset ι`. -/
def piFinset : @Filtration (Π i, X i) (Finset ι) _ pi where
  seq s := pi.comap s.restrict
  mono' s t hst := by
    simp only
    rw [← restrict₂_comp_restrict hst, ← comap_comp]
    exact comap_mono (measurable_restrict₂ hst).comap_le
  le' s := s.measurable_restrict.comap_le

lemma piFinset_eq_comap_restrict (s : Finset ι) :
    piFinset (X := X) s = pi.comap (s : Set ι).restrict := rfl

end piFinset

variable {α : Type*}

/-- The exterior σ-algebras of finite sets of `α` form a cofiltration indexed by `Finset α`. -/
def cylinderEventsCompl : Filtration (Finset α)ᵒᵈ (.pi (X := fun _ : α ↦ Ω)) where
  seq Λ := cylinderEvents (↑(OrderDual.ofDual Λ))ᶜ
  mono' _ _ h := cylinderEvents_mono <| Set.compl_subset_compl_of_subset h
  le' _  := cylinderEvents_le_pi

end Filtration

end MeasureTheory
