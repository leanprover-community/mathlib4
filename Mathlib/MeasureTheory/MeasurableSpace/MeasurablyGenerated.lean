/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.SmallSets
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.FinCases

/-!
# Measurably generated filters

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `Filter.Eventually`.
-/

open Set Filter

universe uι

variable {α β γ δ : Type*} {ι : Sort uι}

namespace MeasurableSpace

/-- The sigma-algebra generated by a single set `s` is `{∅, s, sᶜ, univ}`. -/
@[simp] theorem generateFrom_singleton (s : Set α) :
    generateFrom {s} = MeasurableSpace.comap (· ∈ s) ⊤ := by
  classical
  letI : MeasurableSpace α := generateFrom {s}
  refine le_antisymm (generateFrom_le fun t ht => ⟨{True}, trivial, by simp [ht.symm]⟩) ?_
  rintro _ ⟨u, -, rfl⟩
  exact (show MeasurableSet s from GenerateMeasurable.basic _ <| mem_singleton s).mem trivial

lemma generateFrom_singleton_le {m : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) :
    MeasurableSpace.generateFrom {s} ≤ m :=
  generateFrom_le (fun _ ht ↦ mem_singleton_iff.1 ht ▸ hs)

end MeasurableSpace

namespace MeasureTheory

theorem measurableSet_generateFrom_singleton_iff {s t : Set α} :
    MeasurableSet[MeasurableSpace.generateFrom {s}] t ↔ t = ∅ ∨ t = s ∨ t = sᶜ ∨ t = univ := by
  simp_rw [MeasurableSpace.generateFrom_singleton]
  change t ∈ {t | _} ↔ _
  simp_rw [MeasurableSpace.measurableSet_top, true_and, mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hT : True ∈ x
    · by_cases hF : False ∈ x
      · refine Or.inr <| Or.inr <| Or.inr <| subset_antisymm (subset_univ _) ?_
        suffices x = univ by simp only [this, preimage_univ, subset_refl]
        refine subset_antisymm (subset_univ _) ?_
        rw [univ_eq_true_false]
        rintro - (rfl | rfl)
        · assumption
        · assumption
      · have hx : x = {True} := by
          ext p
          refine ⟨fun hp ↦ mem_singleton_iff.2 ?_, fun hp ↦ hp ▸ hT⟩
          by_contra hpneg
          rw [eq_iff_iff, iff_true, ← false_iff] at hpneg
          exact hF (by convert hp)
        simp [hx]
    · by_cases hF : False ∈ x
      · have hx : x = {False} := by
          ext p
          refine ⟨fun hp ↦ mem_singleton_iff.2 ?_, fun hp ↦ hp ▸ hF⟩
          by_contra hpneg
          simp only [eq_iff_iff, iff_false, not_not] at hpneg
          refine hT ?_
          convert hp
          simpa
        refine Or.inr <| Or.inr <| Or.inl <| ?_
        simp [hx]
        rfl
      · refine Or.inl <| subset_antisymm ?_ <| empty_subset _
        suffices x ⊆ ∅ by
          rw [subset_empty_iff] at this
          simp only [this, preimage_empty, subset_refl]
        intro p hp
        fin_cases p
        · contradiction
        · contradiction
  · rintro (rfl | rfl | rfl | rfl)
    on_goal 1 => use ∅
    on_goal 2 => use {True}
    on_goal 3 => use {False}
    on_goal 4 => use Set.univ
    all_goals
      simp [compl_def]

end MeasureTheory

namespace Filter

variable [MeasurableSpace α]

/-- A filter `f` is measurably generates if each `s ∈ f` includes a measurable `t ∈ f`. -/
class IsMeasurablyGenerated (f : Filter α) : Prop where
  exists_measurable_subset : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, MeasurableSet t ∧ t ⊆ s

instance isMeasurablyGenerated_bot : IsMeasurablyGenerated (⊥ : Filter α) :=
  ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩

instance isMeasurablyGenerated_top : IsMeasurablyGenerated (⊤ : Filter α) :=
  ⟨fun _s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩

theorem Eventually.exists_measurable_mem {f : Filter α} [IsMeasurablyGenerated f] {p : α → Prop}
    (h : ∀ᶠ x in f, p x) : ∃ s ∈ f, MeasurableSet s ∧ ∀ x ∈ s, p x :=
  IsMeasurablyGenerated.exists_measurable_subset h

theorem Eventually.exists_measurable_mem_of_smallSets {f : Filter α} [IsMeasurablyGenerated f]
    {p : Set α → Prop} (h : ∀ᶠ s in f.smallSets, p s) : ∃ s ∈ f, MeasurableSet s ∧ p s :=
  let ⟨_s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩

instance inf_isMeasurablyGenerated (f g : Filter α) [IsMeasurablyGenerated f]
    [IsMeasurablyGenerated g] : IsMeasurablyGenerated (f ⊓ g) := by
  constructor
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine ⟨s'f ∩ s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, ?_⟩
  exact inter_subset_inter hs'sf hs'sg

theorem principal_isMeasurablyGenerated_iff {s : Set α} :
    IsMeasurablyGenerated (𝓟 s) ↔ MeasurableSet s := by
  refine ⟨?_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := hts.antisymm ht
  rwa [← this]

alias ⟨_, _root_.MeasurableSet.principal_isMeasurablyGenerated⟩ :=
  principal_isMeasurablyGenerated_iff

instance iInf_isMeasurablyGenerated {f : ι → Filter α} [∀ i, IsMeasurablyGenerated (f i)] :
    IsMeasurablyGenerated (⨅ i, f i) := by
  refine ⟨fun s hs => ?_⟩
  rw [← Equiv.plift.surjective.iInf_comp, mem_iInf] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => IsMeasurablyGenerated.exists_measurable_subset (hVf i)
  refine ⟨⋂ i : t, U i, ?_, ?_, ?_⟩
  · rw [← Equiv.plift.surjective.iInf_comp, mem_iInf]
    exact ⟨t, ht, U, hUf, rfl⟩
  · haveI := ht.countable.toEncodable.countable
    exact MeasurableSet.iInter fun i => (hU i).1
  · exact iInter_mono fun i => (hU i).2

end Filter

/-- The set of points for which a sequence of measurable functions converges to a given value
is measurable. -/
@[measurability]
lemma measurableSet_tendsto {_ : MeasurableSpace β} [MeasurableSpace γ]
    [Countable δ] {l : Filter δ} [l.IsCountablyGenerated]
    (l' : Filter γ) [l'.IsCountablyGenerated] [hl' : l'.IsMeasurablyGenerated]
    {f : δ → β → γ} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l l' } := by
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  rcases (Filter.hasBasis_self.mpr hl'.exists_measurable_subset).exists_antitone_subbasis with
    ⟨v, v_meas, hv⟩
  simp only [hu.tendsto_iff hv.toHasBasis, true_imp_iff, true_and, setOf_forall, setOf_exists]
  exact .iInter fun n ↦ .iUnion fun _ ↦ .biInter (to_countable _) fun i _ ↦
    (v_meas n).2.preimage (hf i)

namespace MeasurableSet

variable [MeasurableSpace α]

protected theorem iUnion_of_monotone_of_frequently
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Monotone s) (hs : ∃ᶠ i in atTop, MeasurableSet (s i)) : MeasurableSet (⋃ i, s i) := by
  rcases exists_seq_forall_of_frequently hs with ⟨x, hx, hxm⟩
  rw [← hsm.iUnion_comp_tendsto_atTop hx]
  exact .iUnion hxm

protected theorem iInter_of_antitone_of_frequently
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Antitone s) (hs : ∃ᶠ i in atTop, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  rw [← compl_iff, compl_iInter]
  exact .iUnion_of_monotone_of_frequently (compl_anti.comp hsm) <| hs.mono fun _ ↦ .compl

protected theorem iUnion_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Monotone s) (hs : ∀ i, MeasurableSet (s i)) : MeasurableSet (⋃ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ => exact .iUnion_of_monotone_of_frequently hsm <| .of_forall hs

protected theorem iInter_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α}
    (hsm : Antitone s) (hs : ∀ i, MeasurableSet (s i)) : MeasurableSet (⋂ i, s i) := by
  rw [← compl_iff, compl_iInter]
  exact .iUnion_of_monotone (compl_anti.comp hsm) fun i ↦ (hs i).compl

/-!
### Typeclasses on `Subtype MeasurableSet`
-/

instance Subtype.instMembership : Membership α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun s a => a ∈ (s : Set α)⟩

@[simp]
theorem mem_coe (a : α) (s : Subtype (MeasurableSet : Set α → Prop)) : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

instance Subtype.instEmptyCollection : EmptyCollection (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

@[simp]
theorem coe_empty : ↑(∅ : Subtype (MeasurableSet : Set α → Prop)) = (∅ : Set α) :=
  rfl

instance Subtype.instInsert [MeasurableSingletonClass α] :
    Insert α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => ⟨insert a (s : Set α), s.prop.insert a⟩⟩

@[simp]
theorem coe_insert [MeasurableSingletonClass α] (a : α)
    (s : Subtype (MeasurableSet : Set α → Prop)) :
    ↑(Insert.insert a s) = (Insert.insert a s : Set α) :=
  rfl

instance Subtype.instSingleton [MeasurableSingletonClass α] :
    Singleton α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a => ⟨{a}, .singleton _⟩⟩

@[simp] theorem coe_singleton [MeasurableSingletonClass α] (a : α) :
    ↑({a} : Subtype (MeasurableSet : Set α → Prop)) = ({a} : Set α) :=
  rfl

instance Subtype.instLawfulSingleton [MeasurableSingletonClass α] :
    LawfulSingleton α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun _ => Subtype.eq <| insert_empty_eq _⟩

instance Subtype.instHasCompl : HasCompl (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x => ⟨xᶜ, x.prop.compl⟩⟩

@[simp]
theorem coe_compl (s : Subtype (MeasurableSet : Set α → Prop)) : ↑sᶜ = (sᶜ : Set α) :=
  rfl

instance Subtype.instUnion : Union (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨(x : Set α) ∪ y, x.prop.union y.prop⟩⟩

@[simp]
theorem coe_union (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∪ t) = (s ∪ t : Set α) :=
  rfl

instance Subtype.instSup : Max (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => x ∪ y⟩

@[simp]
protected theorem sup_eq_union (s t : {s : Set α // MeasurableSet s}) : s ⊔ t = s ∪ t := rfl

instance Subtype.instInter : Inter (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∩ y, x.prop.inter y.prop⟩⟩

@[simp]
theorem coe_inter (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∩ t) = (s ∩ t : Set α) :=
  rfl

instance Subtype.instInf : Min (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => x ∩ y⟩

@[simp]
protected theorem inf_eq_inter (s t : {s : Set α // MeasurableSet s}) : s ⊓ t = s ∩ t := rfl

instance Subtype.instSDiff : SDiff (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x \ y, x.prop.diff y.prop⟩⟩

-- TODO: Why does it complain that `x ⇨ y` is noncomputable?
noncomputable instance Subtype.instHImp : HImp (Subtype (MeasurableSet : Set α → Prop)) where
  himp x y := ⟨x ⇨ y, x.prop.himp y.prop⟩

@[simp]
theorem coe_sdiff (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s \ t) = (s : Set α) \ t :=
  rfl

@[simp]
lemma coe_himp (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl

instance Subtype.instBot : Bot (Subtype (MeasurableSet : Set α → Prop)) := ⟨∅⟩

@[simp]
theorem coe_bot : ↑(⊥ : Subtype (MeasurableSet : Set α → Prop)) = (⊥ : Set α) :=
  rfl

instance Subtype.instTop : Top (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨Set.univ, MeasurableSet.univ⟩⟩

@[simp]
theorem coe_top : ↑(⊤ : Subtype (MeasurableSet : Set α → Prop)) = (⊤ : Set α) :=
  rfl

noncomputable instance Subtype.instBooleanAlgebra :
    BooleanAlgebra (Subtype (MeasurableSet : Set α → Prop)) :=
  Subtype.coe_injective.booleanAlgebra _ coe_union coe_inter coe_top coe_bot coe_compl coe_sdiff
    coe_himp

@[measurability]
theorem measurableSet_blimsup {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| blimsup s atTop p := by
  simp only [blimsup_eq_iInf_biSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
  exact .iInter fun _ => .iUnion fun m => .iUnion fun hm => h m hm.1

@[measurability]
theorem measurableSet_bliminf {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.bliminf s Filter.atTop p := by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
  exact .iUnion fun n => .iInter fun m => .iInter fun hm => h m hm.1

@[measurability]
theorem measurableSet_limsup {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.limsup s Filter.atTop := by
  simpa only [← blimsup_true] using measurableSet_blimsup fun n _ => hs n

@[measurability]
theorem measurableSet_liminf {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.liminf s Filter.atTop := by
  simpa only [← bliminf_true] using measurableSet_bliminf fun n _ => hs n

end MeasurableSet
