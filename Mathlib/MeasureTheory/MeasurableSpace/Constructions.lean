/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Finset.Update
import Mathlib.Data.Prod.TProd
import Mathlib.Data.Set.UnionLift
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Order.Disjointed

/-!
# Constructions for measurable spaces and functions

This file provides several ways to construct new measurable spaces and functions from old ones:
`Quotient`, `Subtype`, `Prod`, `Pi`, etc.
-/

assert_not_exists Filter

open Set Function

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)

theorem ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α → ℕ∞} :
    Measurable f ↔ ∀ n : ℕ, MeasurableSet (f ⁻¹' {↑n}) := by
  refine ⟨fun hf n ↦ hf <| measurableSet_singleton _, fun h ↦ measurable_to_countable' fun n ↦ ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top, ← compl_range_some, preimage_compl, ← iUnion_singleton_eq_range,
      preimage_iUnion]
    exact .compl <| .iUnion h
  | coe n => exact h n

@[measurability]
theorem measurable_unit [MeasurableSpace α] (f : Unit → α) : Measurable f :=
  measurable_from_top

section ULift
variable [MeasurableSpace α]

instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift α) :=
  ‹MeasurableSpace α›.map ULift.up

lemma measurable_down : Measurable (ULift.down : ULift α → α) := fun _ ↦ id
lemma measurable_up : Measurable (ULift.up : α → ULift α) := fun _ ↦ id

@[simp] lemma measurableSet_preimage_down {s : Set α} :
    MeasurableSet (ULift.down ⁻¹' s) ↔ MeasurableSet s := Iff.rfl
@[simp] lemma measurableSet_preimage_up {s : Set (ULift α)} :
    MeasurableSet (ULift.up ⁻¹' s) ↔ MeasurableSet s := Iff.rfl

end ULift

section Nat

variable {mα : MeasurableSpace α}

@[measurability]
theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top

theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable

theorem measurable_to_bool {f : α → Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f := by
  apply measurable_to_countable'
  rintro (- | -)
  · convert h.compl
    rw [← preimage_compl, Bool.compl_singleton, Bool.not_true]
  exact h

theorem measurable_to_prop {f : α → Prop} (h : MeasurableSet (f ⁻¹' {True})) : Measurable f := by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl

theorem measurable_findGreatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun _ => hN _ N.findGreatest_le

theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N := by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, setOf_and, setOf_forall, ← compl_setOf]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]
protected theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)

theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) := by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

instance Quot.instMeasurableSpace {α} {r : α → α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)

instance Quotient.instMeasurableSpace {α} {s : Setoid α} [m : MeasurableSpace α] :
    MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''

@[to_additive]
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.instMeasurableSpace

theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl

theorem measurable_from_quotient {s : Setoid α} {f : Quotient s → β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl

@[measurability]
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α → Quotient s) :=
  fun _ => id

@[measurability]
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun _ => id

@[measurability]
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun _ => id

@[to_additive (attr := measurability)]
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable ((↑) : G → G ⧸ S) :=
  measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ ((↑) : G → G ⧸ S)) :=
  measurable_from_quotient

instance Quotient.instDiscreteMeasurableSpace {α} {s : Setoid α} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Quotient s) where
  forall_measurableSet _ := measurableSet_quotient.2 .of_discrete

@[to_additive]
instance QuotientGroup.instDiscreteMeasurableSpace {G} [Group G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (S : Subgroup G) : DiscreteMeasurableSpace (G ⧸ S) :=
  Quotient.instDiscreteMeasurableSpace

end Quotient

section Subtype

instance Subtype.instMeasurableSpace {α} {p : α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Subtype p) :=
  m.comap ((↑) : _ → α)

section

variable [MeasurableSpace α]

@[measurability]
theorem measurable_subtype_coe {p : α → Prop} : Measurable ((↑) : Subtype p → α) :=
  MeasurableSpace.le_map_comap

instance Subtype.instMeasurableSingletonClass {p : α → Prop} [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Subtype p) where
  measurableSet_singleton x :=
    ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton, preimage_image_eq _ Subtype.val_injective]⟩

end

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem MeasurableSet.of_subtype_image {s : Set α} {t : Set s}
    (h : MeasurableSet (Subtype.val '' t)) : MeasurableSet t :=
  ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩

theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t → MeasurableSet (((↑) : s → α) '' t) := by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[measurability]
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[measurability]
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[measurability]
protected theorem Measurable.rangeFactorization {f : α → β} (hf : Measurable f) :
    Measurable (rangeFactorization f) :=
  hf.subtype_mk

theorem Measurable.subtype_map {f : α → β} {p : α → Prop} {q : β → Prop} (hf : Measurable f)
    (hpq : ∀ x, p x → q (f x)) : Measurable (Subtype.map f hpq) :=
  (hf.comp measurable_subtype_coe).subtype_mk

theorem measurable_inclusion {s t : Set α} (h : s ⊆ t) : Measurable (inclusion h) :=
  measurable_id.subtype_map h

theorem MeasurableSet.image_inclusion' {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) := by
  rcases hu with ⟨u, hu, rfl⟩
  convert (measurable_subtype_coe hu).inter hs
  ext ⟨x, hx⟩
  simpa [@and_comm _ (_ = x)] using and_comm

theorem MeasurableSet.image_inclusion {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) :=
  (measurable_subtype_coe hs).image_inclusion' h hu

theorem MeasurableSet.of_union_cover {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hsu : MeasurableSet (((↑) : s → α) ⁻¹' u))
    (htu : MeasurableSet (((↑) : t → α) ⁻¹' u)) : MeasurableSet u := by
  convert (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]

theorem measurable_of_measurable_union_cover {f : α → β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ ⊆ s ∪ t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f := fun _u hu =>
  .of_union_cover hs ht h (hc hu) (hd hu)

theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.restrict f)) (h₂ : Measurable (sᶜ.restrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f)
    {g : (sᶜ : Set α) → β} (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.restrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf

theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.restrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

end Subtype

section Atoms

variable [MeasurableSpace β]

/-- The *measurable atom* of `x` is the intersection of all the measurable sets containing `x`.
It is measurable when the space is countable (or more generally when the measurable space is
countably generated). -/
def measurableAtom (x : β) : Set β :=
  ⋂ (s : Set β) (_h's : x ∈ s) (_hs : MeasurableSet s), s

@[simp] lemma mem_measurableAtom_self (x : β) : x ∈ measurableAtom x := by
  simp +contextual [measurableAtom]

lemma mem_of_mem_measurableAtom {x y : β} (h : y ∈ measurableAtom x) {s : Set β}
    (hs : MeasurableSet s) (hxs : x ∈ s) : y ∈ s := by
  simp only [measurableAtom, mem_iInter] at h
  exact h s hxs hs

lemma measurableAtom_subset {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x ∈ s) :
    measurableAtom x ⊆ s :=
  iInter₂_subset_of_subset s hx fun ⦃a⦄ ↦ (by simp [hs])

@[simp] lemma measurableAtom_of_measurableSingletonClass [MeasurableSingletonClass β] (x : β) :
    measurableAtom x = {x} :=
  Subset.antisymm (measurableAtom_subset (measurableSet_singleton x) rfl) (by simp)

lemma MeasurableSet.measurableAtom_of_countable [Countable β] (x : β) :
    MeasurableSet (measurableAtom x) := by
  have : ∀ (y : β), y ∉ measurableAtom x → ∃ s, x ∈ s ∧ MeasurableSet s ∧ y ∉ s :=
    fun y hy ↦ by simpa [measurableAtom] using hy
  choose! s hs using this
  have : measurableAtom x = ⋂ (y ∈ (measurableAtom x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp only [mem_iInter, mem_compl_iff]
      intro i hi
      exact mem_of_mem_measurableAtom hz (hs i hi).2.1 (hs i hi).1
    · apply compl_subset_compl.1
      intro z hz
      simp only [compl_iInter, mem_iUnion, mem_compl_iff, exists_prop]
      exact ⟨z, hz, (hs z hz).2.2⟩
  rw [this]
  exact MeasurableSet.biInter (to_countable (measurableAtom x)ᶜ) (fun i hi ↦ (hs i hi).2.1)

/-- There is in fact equality: see `measurableAtom_eq_of_mem`. -/
lemma measurableAtom_subset_of_mem {x y : β} (hx : x ∈ measurableAtom y) :
    measurableAtom x ⊆ measurableAtom y := by
  intro z hz
  simp only [measurableAtom, mem_iInter] at hz hx ⊢
  exact fun s hys hs ↦ hz s (hx s hys hs) hs

lemma measurableAtom_eq_of_mem {x y : β} (hx : x ∈ measurableAtom y) :
    measurableAtom x = measurableAtom y := by
  refine subset_antisymm (measurableAtom_subset_of_mem hx) ?_
  by_cases hy : y ∈ measurableAtom x
  · exact measurableAtom_subset_of_mem hy
  exfalso
  simp only [measurableAtom, mem_iInter, not_forall] at hx hy ⊢
  obtain ⟨s, hxs, hs, hys⟩ := hy
  specialize hx sᶜ hys hs.compl
  exact hx hxs

lemma disjoint_measurableAtom_of_notMem {x y : β} (hx : x ∉ measurableAtom y) :
    Disjoint (measurableAtom x) (measurableAtom y) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := measurableAtom_eq_of_mem hzx
  have h2 := measurableAtom_eq_of_mem hzy
  rw [← h2, h1] at hx
  exact hx (mem_measurableAtom_self x)

end Atoms

section Prod

/-- A `MeasurableSpace` structure on the product of two measurable spaces. -/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd

instance Prod.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α × β) :=
  m₁.prod m₂

@[measurability]
theorem measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left

@[measurability]
theorem measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[fun_prop]
theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf

@[fun_prop]
theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf

@[measurability]
theorem Measurable.prod {f : α → β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
  Measurable.of_le_map <|
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]
theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg

@[deprecated (since := "2025-03-05")]
alias Measurable.prod_mk := Measurable.prodMk

@[fun_prop]
theorem Measurable.prodMap [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

@[deprecated (since := "2025-03-05")]
alias Measurable.prod_map := Measurable.prodMap

theorem measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prodMk measurable_id

@[deprecated (since := "2025-03-05")]
alias measurable_prod_mk_left := measurable_prodMk_left

theorem measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prodMk measurable_const

@[deprecated (since := "2025-03-05")]
alias measurable_prod_mk_right := measurable_prodMk_right

theorem Measurable.of_uncurry_left {f : α → β → γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prodMk_left

theorem Measurable.of_uncurry_right {f : α → β → γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prodMk_right

theorem measurable_fun_prod {f : α → β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop, measurability]
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst

theorem measurable_swap_iff {_ : MeasurableSpace γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]
protected theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)

theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t := by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all

theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]

theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩

instance Prod.instMeasurableSingletonClass
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

theorem measurable_from_prod_countable' [Countable β]
    {_ : MeasurableSpace γ} {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y))
    (h'f : ∀ y y' x, y' ∈ measurableAtom y → f (x, y') = f (x, y)) :
    Measurable f := fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ (measurableAtom y : Set β) := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h ↦ ⟨y, h, mem_measurableAtom_self y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exact .iUnion (fun y ↦ (hf y hs).prod (.measurableAtom_of_countable y))

theorem measurable_from_prod_countable [Countable β] [MeasurableSingletonClass β]
    {_ : MeasurableSpace γ} {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y)) :
    Measurable f :=
  measurable_from_prod_countable' hf (by simp +contextual)

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
@[measurability]
theorem Measurable.find {_ : MeasurableSpace α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  have : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

/-- Let `t i` be a countable covering of a set `T` by measurable sets. Let `f i : t i → β` be a
family of functions that agree on the intersections `t i ∩ t j`. Then the function
`Set.iUnionLift t f _ _ : T → β`, defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
theorem measurable_iUnionLift [Countable ι] {t : ι → Set α} {f : ∀ i, t i → β}
    (htf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    {T : Set α} (hT : T ⊆ ⋃ i, t i) (htm : ∀ i, MeasurableSet (t i)) (hfm : ∀ i, Measurable (f i)) :
    Measurable (iUnionLift t f htf T hT) := fun s hs => by
  rw [preimage_iUnionLift]
  exact .preimage (.iUnion fun i => .image_inclusion _ (htm _) (hfm i hs)) (measurable_inclusion _)

/-- Let `t i` be a countable covering of `α` by measurable sets. Let `f i : t i → β` be a family of
functions that agree on the intersections `t i ∩ t j`. Then the function `Set.liftCover t f _ _`,
defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
theorem measurable_liftCover [Countable ι] (t : ι → Set α) (htm : ∀ i, MeasurableSet (t i))
    (f : ∀ i, t i → β) (hfm : ∀ i, Measurable (f i))
    (hf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (htU : ⋃ i, t i = univ) :
    Measurable (liftCover t f hf htU) := fun s hs => by
  rw [preimage_liftCover]
  exact .iUnion fun i => .subtype_image (htm i) <| hfm i hs

/-- Let `t i` be a nonempty countable family of measurable sets in `α`. Let `g i : α → β` be a
family of measurable functions such that `g i` agrees with `g j` on `t i ∩ t j`. Then there exists
a measurable function `f : α → β` that agrees with each `g i` on `t i`.

We only need the assumption `[Nonempty ι]` to prove `[Nonempty (α → β)]`. -/
theorem exists_measurable_piecewise {ι} [Countable ι] [Nonempty ι] (t : ι → Set α)
    (t_meas : ∀ n, MeasurableSet (t n)) (g : ι → α → β) (hg : ∀ n, Measurable (g n))
    (ht : Pairwise fun i j => EqOn (g i) (g j) (t i ∩ t j)) :
    ∃ f : α → β, Measurable f ∧ ∀ n, EqOn f (g n) (t n) := by
  inhabit ι
  set g' : (i : ι) → t i → β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact ht hij ⟨hxi, hxj⟩
  set f : (⋃ i, t i) → β := iUnionLift t g' ht' _ Subset.rfl
  have hfm : Measurable f := measurable_iUnionLift _ _ t_meas
    (fun i => (hg i).comp measurable_subtype_coe)
  classical
    refine ⟨fun x => if hx : x ∈ ⋃ i, t i then f ⟨x, hx⟩ else g default x,
      hfm.dite ((hg default).comp measurable_subtype_coe) (.iUnion t_meas), fun i x hx => ?_⟩
    simp only [dif_pos (mem_iUnion.2 ⟨i, hx⟩)]
    exact iUnionLift_of_mem ⟨x, mem_iUnion.2 ⟨i, hx⟩⟩ hx

end Prod

section Pi

variable {X : δ → Type*} [MeasurableSpace α]

instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (X a)] : MeasurableSpace (∀ a, X a) :=
  ⨆ a, (m a).comap fun b => b a

variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]

theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

@[aesop safe 100 apply (rule_sets := [Measurable])]
theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
theorem measurable_pi_lambda (f : α → ∀ a, X a) (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
@[measurability, fun_prop]
theorem measurable_update' {a : δ} [DecidableEq δ] :
    Measurable (fun p : (∀ i, X i) × X a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[measurability, fun_prop]
theorem measurable_uniqueElim [Unique δ] :
    Measurable (uniqueElim : X (default : δ) → ∀ i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[measurability, fun_prop]
theorem measurable_updateFinset' [DecidableEq δ] {s : Finset δ} :
    Measurable (fun p : (Π i, X i) × (Π i : s, X i) ↦ updateFinset p.1 s p.2) := by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[measurability, fun_prop]
theorem measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : Π i, X i} :
    Measurable (updateFinset x s) :=
  measurable_updateFinset'.comp measurable_prodMk_left

@[measurability, fun_prop]
theorem measurable_updateFinset_left [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i} :
    Measurable (updateFinset · s x) :=
  measurable_updateFinset'.comp measurable_prodMk_right

/-- The function `update f a : X a → Π a, X a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability, fun_prop]
theorem measurable_update (f : ∀ a : δ, X a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  measurable_update'.comp measurable_prodMk_left

@[measurability, fun_prop]
theorem measurable_update_left {a : δ} [DecidableEq δ] {x : X a} :
    Measurable (update · a x) :=
  measurable_update'.comp measurable_prodMk_right

@[measurability, fun_prop]
theorem Set.measurable_restrict (s : Set δ) : Measurable (s.restrict (π := X)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[measurability, fun_prop]
theorem Set.measurable_restrict₂ {s t : Set δ} (hst : s ⊆ t) :
    Measurable (restrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[measurability, fun_prop]
theorem Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π := X)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[measurability, fun_prop]
theorem Finset.measurable_restrict₂ {s t : Finset δ} (hst : s ⊆ t) :
    Measurable (Finset.restrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[measurability, fun_prop]
theorem Set.measurable_restrict_apply (s : Set α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.restrict f) := hf.comp measurable_subtype_coe

@[measurability, fun_prop]
theorem Set.measurable_restrict₂_apply {s t : Set α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

@[measurability, fun_prop]
theorem Finset.measurable_restrict_apply (s : Finset α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.restrict f) := hf.comp measurable_subtype_coe

@[measurability, fun_prop]
theorem Finset.measurable_restrict₂_apply {s t : Finset α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

variable (X) in
theorem measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg X h).mp := by
  cases h
  exact measurable_id

variable (X) in
theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β → X i}
    (hf : Measurable f) : Measurable fun x => (congr_arg X h).mp (f x) :=
  (measurable_eq_mp X h).comp hf

@[measurability, fun_prop]
theorem measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (Equiv.piCongrLeft X f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
  exact Measurable.eq_mp X (f.apply_symm_apply i) <| measurable_pi_apply <| f.symm i

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `MeasurableSet.prod`. -/
@[measurability]
protected theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (X i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) := by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)

protected theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i

theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj

theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ := by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]

instance Pi.instMeasurableSingletonClass [Countable δ] [∀ a, MeasurableSingletonClass (X a)] :
    MeasurableSingletonClass (∀ a, X a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (X)

@[measurability]
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X).symm := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : ∀ i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun (f : ∀ i : { x // ¬p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // ¬p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_snd

@[measurability]
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X) :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

end Pi

instance TProd.instMeasurableSpace (X : δ → Type*) [∀ i, MeasurableSpace (X i)] :
    ∀ l : List δ, MeasurableSpace (List.TProd X l)
  | [] => PUnit.instMeasurableSpace
  | _::is => @Prod.instMeasurableSpace _ _ _ (TProd.instMeasurableSpace X is)

section TProd

open List

variable {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ X l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd X l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simp only [TProd.elim_of_ne _ hji]
      rw [mem_cons] at hj
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd

theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd X l → ∀ i, X i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)

theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (X i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

end TProd

instance Sum.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α ⊕ β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

section Sum

@[measurability]
theorem measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left

@[measurability]
theorem measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem measurableSet_sum_iff {s : Set (α ⊕ β)} :
    MeasurableSet s ↔ MeasurableSet (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s) :=
  Iff.rfl

theorem measurable_fun_sum {_ : MeasurableSpace γ} {f : α ⊕ β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)

@[measurability]
theorem Measurable.sumElim {_ : MeasurableSpace γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_fun_sum hf hg

theorem Measurable.sumMap {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map f g) :=
  (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image

@[simp] theorem measurableSet_inr_image {s : Set β} :
    MeasurableSet (Sum.inr '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image

theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image

theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

end Sum

instance Sigma.instMeasurableSpace {α} {β : α → Type*} [m : ∀ a, MeasurableSpace (β a)] :
    MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

section prop
variable [MeasurableSpace α] {p q : α → Prop}

@[simp] theorem measurableSet_setOf : MeasurableSet {a | p a} ↔ Measurable p :=
  ⟨fun h ↦ measurable_to_prop <| by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩

@[simp] theorem measurable_mem : Measurable (· ∈ s) ↔ MeasurableSet s := measurableSet_setOf.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOf

alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

lemma Measurable.not (hp : Measurable p) : Measurable (¬ p ·) :=
  measurableSet_setOf.1 hp.setOf.compl

lemma Measurable.and (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∧ q a :=
  measurableSet_setOf.1 <| hp.setOf.inter hq.setOf

lemma Measurable.or (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∨ q a :=
  measurableSet_setOf.1 <| hp.setOf.union hq.setOf

lemma Measurable.imp (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a → q a :=
  measurableSet_setOf.1 <| hp.setOf.himp hq.setOf

lemma Measurable.iff (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ↔ q a :=
  measurableSet_setOf.1 <| by simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

lemma Measurable.forall [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∀ i, p i a :=
  measurableSet_setOf.1 <| by rw [setOf_forall]; exact MeasurableSet.iInter fun i ↦ (hp i).setOf

lemma Measurable.exists [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∃ i, p i a :=
  measurableSet_setOf.1 <| by rw [setOf_exists]; exact MeasurableSet.iUnion fun i ↦ (hp i).setOf

end prop

section Set
variable [MeasurableSpace β] {g : β → Set α}

/-- This instance is useful when talking about Bernoulli sequences of random variables or binomial
random graphs. -/
instance Set.instMeasurableSpace : MeasurableSpace (Set α) := by unfold Set; infer_instance

instance Set.instMeasurableSingletonClass [Countable α] : MeasurableSingletonClass (Set α) := by
  unfold Set; infer_instance

lemma measurable_set_iff : Measurable g ↔ ∀ a, Measurable fun x ↦ a ∈ g x := measurable_pi_iff

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_set_mem (a : α) : Measurable fun s : Set α ↦ a ∈ s := measurable_pi_apply _

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_set_notMem (a : α) : Measurable fun s : Set α ↦ a ∉ s :=
  (Measurable.of_discrete (f := Not)).comp <| measurable_set_mem a

@[deprecated (since := "2025-05-23")] alias measurable_set_not_mem := measurable_set_notMem

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurableSet_mem (a : α) : MeasurableSet {s : Set α | a ∈ s} :=
  measurableSet_setOf.2 <| measurable_set_mem _

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurableSet_notMem (a : α) : MeasurableSet {s : Set α | a ∉ s} :=
  measurableSet_setOf.2 <| measurable_set_notMem _

@[deprecated (since := "2025-05-23")] alias measurableSet_not_mem := measurableSet_notMem

lemma measurable_compl : Measurable ((·ᶜ) : Set α → Set α) :=
  measurable_set_iff.2 fun _ ↦ measurable_set_notMem _

lemma MeasurableSet.setOf_finite [Countable α] : MeasurableSet {s : Set α | s.Finite} :=
  Countable.setOf_finite.measurableSet

lemma MeasurableSet.setOf_infinite [Countable α] : MeasurableSet {s : Set α | s.Infinite} :=
  .setOf_finite |> .compl

lemma MeasurableSet.sep_finite [Countable α] {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Finite} :=
  hS.inter .setOf_finite

lemma MeasurableSet.sep_infinite [Countable α] {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Infinite} :=
  hS.inter .setOf_infinite

end Set
