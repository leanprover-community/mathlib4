/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Finset.Update
import Mathlib.Data.Prod.TProd
import Mathlib.GroupTheory.Coset
import Mathlib.Logic.Equiv.Fin
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Set.UnionLift
import Mathlib.Order.Filter.SmallSets

#align_import measure_theory.measurable_space from "leanprover-community/mathlib"@"001ffdc42920050657fd45bd2b8bfbec8eaaeb29"

/-!
# Measurable spaces and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms between them.
The definition of a measurable space is in `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them. A function `f : α → β` induces a Galois connection
between the lattices of σ-algebras on `α` and `β`.

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `Filter.Eventually`.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is
defined in terms of the Galois connection induced by f.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, dynkin system, π-λ theorem, π-system
-/


open Set Encodable Function Equiv Filter MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

namespace MeasurableSpace

section Functors

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet[m] <| f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl s hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using m.measurableSet_iUnion _ hf
#align measurable_space.map MeasurableSpace.map

lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl

@[simp]
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun _ => Iff.rfl
#align measurable_space.map_id MeasurableSpace.map_id

@[simp]
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun _ => Iff.rfl
#align measurable_space.map_comp MeasurableSpace.map_comp

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun s ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩
#align measurable_space.comap MeasurableSpace.comap

theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s, MeasurableSet s ∧ f ⁻¹' s = t } :=
  (@generateFrom_measurableSet _ (.comap f m)).symm
#align measurable_space.comap_eq_generate_from MeasurableSpace.comap_eq_generateFrom

@[simp]
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨_, hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩
#align measurable_space.comap_id MeasurableSpace.comap_id

@[simp]
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun _ =>
    ⟨fun ⟨_, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩
#align measurable_space.comap_comp MeasurableSpace.comap_comp

theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h _s hs => h _ ⟨_, hs, rfl⟩, fun h _s ⟨_t, ht, heq⟩ => heq ▸ h _ ht⟩
#align measurable_space.comap_le_iff_le_map MeasurableSpace.comap_le_iff_le_map

theorem gc_comap_map (f : α → β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun _ _ =>
  comap_le_iff_le_map
#align measurable_space.gc_comap_map MeasurableSpace.gc_comap_map

theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h
#align measurable_space.map_mono MeasurableSpace.map_mono

theorem monotone_map : Monotone (MeasurableSpace.map f) := fun _ _ => map_mono
#align measurable_space.monotone_map MeasurableSpace.monotone_map

theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h
#align measurable_space.comap_mono MeasurableSpace.comap_mono

theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun _ _ h => comap_mono h
#align measurable_space.monotone_comap MeasurableSpace.monotone_comap

@[simp]
theorem comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥ :=
  (gc_comap_map g).l_bot
#align measurable_space.comap_bot MeasurableSpace.comap_bot

@[simp]
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup
#align measurable_space.comap_sup MeasurableSpace.comap_sup

@[simp]
theorem comap_iSup {m : ι → MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup
#align measurable_space.comap_supr MeasurableSpace.comap_iSup

@[simp]
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top
#align measurable_space.map_top MeasurableSpace.map_top

@[simp]
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf
#align measurable_space.map_inf MeasurableSpace.map_inf

@[simp]
theorem map_iInf {m : ι → MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf
#align measurable_space.map_infi MeasurableSpace.map_iInf

theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _
#align measurable_space.comap_map_le MeasurableSpace.comap_map_le

theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _
#align measurable_space.le_map_comap MeasurableSpace.le_map_comap

end Functors

@[simp] theorem map_const {m} (b : β) : MeasurableSpace.map (fun _a : α ↦ b) m = ⊤ :=
  eq_top_iff.2 <| fun s _ ↦ by rw [map_def]; by_cases h : b ∈ s <;> simp [h]
#align measurable_space.map_const MeasurableSpace.map_const

@[simp] theorem comap_const {m} (b : β) : MeasurableSpace.comap (fun _a : α => b) m = ⊥ :=
  eq_bot_iff.2 <| by rintro _ ⟨s, -, rfl⟩; by_cases b ∈ s <;> simp [*]
#align measurable_space.comap_const MeasurableSpace.comap_const

theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun _t hts => GenerateMeasurable.basic _ <| mem_image_of_mem _ <| hts)
    (generateFrom_le fun _t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)
#align measurable_space.comap_generate_from MeasurableSpace.comap_generateFrom

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f :=
  Iff.rfl
#align measurable_iff_le_map measurable_iff_le_map

alias ⟨Measurable.le_map, Measurable.of_le_map⟩ := measurable_iff_le_map
#align measurable.le_map Measurable.le_map
#align measurable.of_le_map Measurable.of_le_map

theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm
#align measurable_iff_comap_le measurable_iff_comap_le

alias ⟨Measurable.comap_le, Measurable.of_comap_le⟩ := measurable_iff_comap_le
#align measurable.comap_le Measurable.comap_le
#align measurable.of_comap_le Measurable.of_comap_le

theorem comap_measurable {m : MeasurableSpace β} (f : α → β) : Measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩
#align comap_measurable comap_measurable

theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun _t ht => ha _ <| hf <| hb _ ht
#align measurable.mono Measurable.mono

theorem measurable_id'' {m mα : MeasurableSpace α} (hm : m ≤ mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm
#align probability_theory.measurable_id'' measurable_id''

-- Porting note (#11215): TODO: add TC `DiscreteMeasurable` + instances

@[measurability]
theorem measurable_from_top [MeasurableSpace β] {f : α → β} : Measurable[⊤] f := fun _ _ => trivial
#align measurable_from_top measurable_from_top

theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h
#align measurable_generate_from measurable_generateFrom

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[nontriviality, measurability]
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun _ _ =>
  @Subsingleton.measurableSet α _ _ _
#align subsingleton.measurable Subsingleton.measurable

@[nontriviality, measurability]
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s _ => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
#align measurable_of_subsingleton_codomain measurable_of_subsingleton_codomain

@[to_additive (attr := measurability)]
theorem measurable_one [One α] : Measurable (1 : β → α) :=
  @measurable_const _ _ _ _ 1
#align measurable_one measurable_one
#align measurable_zero measurable_zero

theorem measurable_of_empty [IsEmpty α] (f : α → β) : Measurable f :=
  Subsingleton.measurable
#align measurable_of_empty measurable_of_empty

theorem measurable_of_empty_codomain [IsEmpty β] (f : α → β) : Measurable f :=
  measurable_of_subsingleton_codomain f
#align measurable_of_empty_codomain measurable_of_empty_codomain

/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
theorem measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : Measurable f := by
  nontriviality β
  inhabit β
  convert @measurable_const α β _ _ (f default) using 2
  apply hf
#align measurable_const' measurable_const'

@[measurability]
theorem measurable_natCast [NatCast α] (n : ℕ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n
#align measurable_nat_cast measurable_natCast

@[measurability]
theorem measurable_intCast [IntCast α] (n : ℤ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n
#align measurable_int_cast measurable_intCast

theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s _ =>
  (f ⁻¹' s).to_countable.measurableSet
#align measurable_of_countable measurable_of_countable

theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  measurable_of_countable f
#align measurable_of_finite measurable_of_finite

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

@[measurability]
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable f^[n]
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate hf n).comp hf
#align measurable.iterate Measurable.iterate

variable {mβ : MeasurableSpace β}

@[measurability]
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht
#align measurable_set_preimage measurableSet_preimage

protected theorem MeasurableSet.preimage {t : Set β} (ht : MeasurableSet t) (hf : Measurable f) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht

@[measurability]
protected theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s)
    (hf : Measurable f) (hg : Measurable g) : Measurable (piecewise s f g) := by
  intro t ht
  rw [piecewise_preimage]
  exact hs.ite (hf ht) (hg ht)
#align measurable.piecewise Measurable.piecewise

/-- This is slightly different from `Measurable.piecewise`. It can be used to show
`Measurable (ite (x=0) 0 1)` by
`exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const`,
but replacing `Measurable.ite` by `Measurable.piecewise` in that example proof does not work. -/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg
#align measurable.ite Measurable.ite

@[measurability]
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const
#align measurable.indicator Measurable.indicator

/-- The measurability of a set `A` is equivalent to the measurability of the indicator function
which takes a constant value `b ≠ 0` on a set `A` and `0` elsewhere. -/
lemma measurable_indicator_const_iff [Zero β] [MeasurableSingletonClass β] (b : β) [NeZero b] :
    Measurable (s.indicator (fun (_ : α) ↦ b)) ↔ MeasurableSet s := by
  constructor <;> intro h
  · convert h (MeasurableSet.singleton (0 : β)).compl
    ext a
    simp [NeZero.ne b]
  · exact measurable_const.indicator h

@[to_additive (attr := measurability)]
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (mulSupport f) :=
  hf (measurableSet_singleton 1).compl
#align measurable_set_mul_support measurableSet_mulSupport
#align measurable_set_support measurableSet_support

/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x ≠ g x }) : Measurable g := by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  refine (h.mono inter_subset_right).measurableSet.union ?_
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } := by
    ext x
    simp (config := { contextual := true })
  rw [this]
  exact (hf ht).inter h.measurableSet.of_compl
#align measurable.measurable_of_countable_ne Measurable.measurable_of_countable_ne

end MeasurableFunctions

section Constructions

theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]
#align measurable_to_countable measurable_to_countable

theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)
#align measurable_to_countable' measurable_to_countable'

@[measurability]
theorem measurable_unit [MeasurableSpace α] (f : Unit → α) : Measurable f :=
  measurable_from_top
#align measurable_unit measurable_unit

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

variable [MeasurableSpace α]

@[measurability]
theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top
#align measurable_from_nat measurable_from_nat

theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable
#align measurable_to_nat measurable_to_nat

theorem measurable_to_bool {f : α → Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f := by
  apply measurable_to_countable'
  rintro (- | -)
  · convert h.compl
    rw [← preimage_compl, Bool.compl_singleton, Bool.not_true]
  exact h
#align measurable_to_bool measurable_to_bool

theorem measurable_to_prop {f : α → Prop} (h : MeasurableSet (f ⁻¹' {True})) : Measurable f := by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl
#align measurable_to_prop measurable_to_prop

theorem measurable_findGreatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun _ => hN _ N.findGreatest_le
#align measurable_find_greatest' measurable_findGreatest'

theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N := by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, setOf_and, setOf_forall, ← compl_setOf]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros
#align measurable_find_greatest measurable_findGreatest

theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) := by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _
#align measurable_find measurable_find

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

instance Quot.instMeasurableSpace {α} {r : α → α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)
#align quot.measurable_space Quot.instMeasurableSpace

instance Quotient.instMeasurableSpace {α} {s : Setoid α} [m : MeasurableSpace α] :
    MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''
#align quotient.measurable_space Quotient.instMeasurableSpace

@[to_additive]
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.instMeasurableSpace
#align quotient_group.measurable_space QuotientGroup.measurableSpace
#align quotient_add_group.measurable_space QuotientAddGroup.measurableSpace

theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl
#align measurable_set_quotient measurableSet_quotient

theorem measurable_from_quotient {s : Setoid α} {f : Quotient s → β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl
#align measurable_from_quotient measurable_from_quotient

@[measurability]
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α → Quotient s) :=
  fun _ => id
#align measurable_quotient_mk measurable_quotient_mk'

@[measurability]
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun _ => id
#align measurable_quotient_mk' measurable_quotient_mk''

@[measurability]
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun _ => id
#align measurable_quot_mk measurable_quot_mk

@[to_additive (attr := measurability)]
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable ((↑) : G → G ⧸ S) :=
  measurable_quotient_mk''
#align quotient_group.measurable_coe QuotientGroup.measurable_coe
#align quotient_add_group.measurable_coe QuotientAddGroup.measurable_coe

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ ((↑) : G → G ⧸ S)) :=
  measurable_from_quotient
#align quotient_group.measurable_from_quotient QuotientGroup.measurable_from_quotient
#align quotient_add_group.measurable_from_quotient QuotientAddGroup.measurable_from_quotient

end Quotient

section Subtype

instance Subtype.instMeasurableSpace {α} {p : α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Subtype p) :=
  m.comap ((↑) : _ → α)
#align subtype.measurable_space Subtype.instMeasurableSpace

section

variable [MeasurableSpace α]

@[measurability]
theorem measurable_subtype_coe {p : α → Prop} : Measurable ((↑) : Subtype p → α) :=
  MeasurableSpace.le_map_comap
#align measurable_subtype_coe measurable_subtype_coe

instance Subtype.instMeasurableSingletonClass {p : α → Prop} [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Subtype p) where
  measurableSet_singleton x :=
    ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton, preimage_image_eq _ Subtype.val_injective]⟩
#align subtype.measurable_singleton_class Subtype.instMeasurableSingletonClass

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
#align measurable_set.subtype_image MeasurableSet.subtype_image

@[measurability]
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf
#align measurable.subtype_coe Measurable.subtype_coe

alias Measurable.subtype_val := Measurable.subtype_coe

@[measurability]
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, (· ∘ ·), Subtype.coe_mk, hf hs.1]
#align measurable.subtype_mk Measurable.subtype_mk

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
#align measurable_of_measurable_union_cover measurable_of_measurable_union_cover

theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.restrict f)) (h₂ : Measurable (sᶜ.restrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂
#align measurable_of_restrict_of_restrict_compl measurable_of_restrict_of_restrict_compl

theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f)
    {g : (sᶜ : Set α) → β} (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)
#align measurable.dite Measurable.dite

theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.restrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf
#align measurable_of_measurable_on_compl_finite measurable_of_measurable_on_compl_finite

theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.restrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf
#align measurable_of_measurable_on_compl_singleton measurable_of_measurable_on_compl_singleton

end Subtype

section Atoms

variable [MeasurableSpace β]

/-- The *measurable atom* of `x` is the intersection of all the measurable sets countaining `x`.
It is measurable when the space is countable (or more generally when the measurable space is
countably generated). -/
def measurableAtom (x : β) : Set β :=
  ⋂ (s : Set β) (_h's : x ∈ s) (_hs : MeasurableSet s), s

@[simp] lemma mem_measurableAtom_self (x : β) : x ∈ measurableAtom x := by
  simp (config := {contextual := true}) [measurableAtom]

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
      show z ∈ s i
      exact mem_of_mem_measurableAtom hz (hs i hi).2.1 (hs i hi).1
    · apply compl_subset_compl.1
      intro z hz
      simp only [compl_iInter, mem_iUnion, mem_compl_iff, exists_prop]
      exact ⟨z, hz, (hs z hz).2.2⟩
  rw [this]
  exact MeasurableSet.biInter (to_countable (measurableAtom x)ᶜ) (fun i hi ↦ (hs i hi).2.1)

end Atoms

section Prod

/-- A `MeasurableSpace` structure on the product of two measurable spaces. -/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
#align measurable_space.prod MeasurableSpace.prod

instance Prod.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α × β) :=
  m₁.prod m₂
#align prod.measurable_space Prod.instMeasurableSpace

@[measurability]
theorem measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left
#align measurable_fst measurable_fst

@[measurability]
theorem measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right
#align measurable_snd measurable_snd

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf
#align measurable.fst Measurable.fst

theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf
#align measurable.snd Measurable.snd

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
#align measurable.prod Measurable.prod

theorem Measurable.prod_mk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg
#align measurable.prod_mk Measurable.prod_mk

theorem Measurable.prod_map [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prod_mk (hg.comp measurable_snd)
#align measurable.prod_map Measurable.prod_map

theorem measurable_prod_mk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prod_mk measurable_id
#align measurable_prod_mk_left measurable_prod_mk_left

theorem measurable_prod_mk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prod_mk measurable_const
#align measurable_prod_mk_right measurable_prod_mk_right

theorem Measurable.of_uncurry_left {f : α → β → γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prod_mk_left
#align measurable.of_uncurry_left Measurable.of_uncurry_left

theorem Measurable.of_uncurry_right {f : α → β → γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prod_mk_right
#align measurable.of_uncurry_right Measurable.of_uncurry_right

theorem measurable_prod {f : α → β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩
#align measurable_prod measurable_prod

@[measurability]
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst
#align measurable_swap measurable_swap

theorem measurable_swap_iff {_ : MeasurableSpace γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩
#align measurable_swap_iff measurable_swap_iff

@[measurability]
protected theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)
#align measurable_set.prod MeasurableSet.prod

theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t := by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prod_mk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prod_mk_left hst
  simp_all
#align measurable_set_prod_of_nonempty measurableSet_prod_of_nonempty

theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]
#align measurable_set_prod measurableSet_prod

theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩
#align measurable_set_swap_iff measurableSet_swap_iff

instance Prod.instMeasurableSingletonClass
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩
#align prod.measurable_singleton_class Prod.instMeasurableSingletonClass

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
  measurable_from_prod_countable' hf (by simp (config := {contextual := true}))
#align measurable_from_prod_countable measurable_from_prod_countable

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
@[measurability]
theorem Measurable.find {_ : MeasurableSpace α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  have : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable fun n => hf n
  this.comp (Measurable.prod_mk measurable_id (measurable_find h hp))
#align measurable.find Measurable.find

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
  -- see #2184
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

/-- Given countably many disjoint measurable sets `t n` and countably many measurable
functions `g n`, one can construct a measurable function that coincides with `g n` on `t n`. -/
@[deprecated exists_measurable_piecewise (since := "2023-02-11")]
theorem exists_measurable_piecewise_nat {m : MeasurableSpace α} (t : ℕ → Set β)
    (t_meas : ∀ n, MeasurableSet (t n)) (t_disj : Pairwise (Disjoint on t)) (g : ℕ → β → α)
    (hg : ∀ n, Measurable (g n)) : ∃ f : β → α, Measurable f ∧ ∀ n x, x ∈ t n → f x = g n x :=
  exists_measurable_piecewise t t_meas g hg <| t_disj.mono fun i j h => by
    simp only [h.inter_eq, eqOn_empty]
#align exists_measurable_piecewise_nat exists_measurable_piecewise_nat

end Prod

section Pi

variable {π : δ → Type*} [MeasurableSpace α]

instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  ⨆ a, (m a).comap fun b => b a
#align measurable_space.pi MeasurableSpace.pi

variable [∀ a, MeasurableSpace (π a)] [MeasurableSpace γ]

theorem measurable_pi_iff {g : α → ∀ a, π a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp, iSup_le_iff]
#align measurable_pi_iff measurable_pi_iff

@[aesop safe 100 apply (rule_sets := [Measurable])]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, π a => f a :=
  measurable_pi_iff.1 measurable_id a
#align measurable_pi_apply measurable_pi_apply

@[aesop safe 100 apply (rule_sets := [Measurable])]
theorem Measurable.eval {a : δ} {g : α → ∀ a, π a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg
#align measurable.eval Measurable.eval

@[aesop safe 100 apply (rule_sets := [Measurable])]
theorem measurable_pi_lambda (f : α → ∀ a, π a) (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf
#align measurable_pi_lambda measurable_pi_lambda

/-- The function `(f, x) ↦ update f a x : (Π a, π a) × π a → Π a, π a` is measurable. -/
theorem measurable_update'  {a : δ} [DecidableEq δ] :
    Measurable (fun p : (∀ i, π i) × π a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

theorem measurable_uniqueElim [Unique δ] [∀ i, MeasurableSpace (π i)] :
    Measurable (uniqueElim : π (default : δ) → ∀ i, π i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

theorem measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : ∀ i, π i} :
    Measurable (updateFinset x s) := by
  simp (config := { unfoldPartialApp := true }) only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
theorem measurable_update (f : ∀ a : δ, π a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  measurable_update'.comp measurable_prod_mk_left
#align measurable_update measurable_update

theorem measurable_update_left {a : δ} [DecidableEq δ] {x : π a} :
    Measurable (update · a x) :=
  measurable_update'.comp measurable_prod_mk_right

variable (π) in
theorem measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg π h).mp := by
  cases h
  exact measurable_id

variable (π) in
theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β → π i}
    (hf : Measurable f) : Measurable fun x => (congr_arg π h).mp (f x) :=
  (measurable_eq_mp π h).comp hf

theorem measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (piCongrLeft π f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [piCongrLeft_apply_eq_cast]
  exact Measurable.eq_mp π (f.apply_symm_apply i) <| measurable_pi_apply <| f.symm i

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `MeasurableSet.prod`. -/
@[measurability]
protected theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (π i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) := by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)
#align measurable_set.pi MeasurableSet.pi

protected theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (π i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i
#align measurable_set.univ_pi MeasurableSet.univ_pi

theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj
#align measurable_set_pi_of_nonempty measurableSet_pi_of_nonempty

theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ := by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]
#align measurable_set_pi measurableSet_pi

instance Pi.instMeasurableSingletonClass [Countable δ] [∀ a, MeasurableSingletonClass (π a)] :
    MeasurableSingletonClass (∀ a, π a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩
#align pi.measurable_singleton_class Pi.instMeasurableSingletonClass

variable (π)

@[measurability]
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π).symm := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : ∀ i : { x // p x }, π i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (π := fun i : {x // p x} => π i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun (f : ∀ i : { x // ¬p x }, π i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (π := fun i : {x // ¬p x} => π i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_snd
#align measurable_pi_equiv_pi_subtype_prod_symm measurable_piEquivPiSubtypeProd_symm

@[measurability]
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π) :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prod_mk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
#align measurable_pi_equiv_pi_subtype_prod measurable_piEquivPiSubtypeProd

end Pi

instance TProd.instMeasurableSpace (π : δ → Type*) [∀ x, MeasurableSpace (π x)] :
    ∀ l : List δ, MeasurableSpace (List.TProd π l)
  | [] => PUnit.instMeasurableSpace
  | _::is => @Prod.instMeasurableSpace _ _ _ (TProd.instMeasurableSpace π is)
#align tprod.measurable_space TProd.instMeasurableSpace

section TProd

open List

variable {π : δ → Type*} [∀ x, MeasurableSpace (π x)]

theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ π l) := by
  induction' l with i l ih
  · exact measurable_const
  · exact (measurable_pi_apply i).prod_mk ih
#align measurable_tprod_mk measurable_tProd_mk

theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd π l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simp only [TProd.elim_of_ne _ hji]
      rw [mem_cons] at hj
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd
#align measurable_tprod_elim measurable_tProd_elim

theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd π l → ∀ i, π i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)
#align measurable_tprod_elim' measurable_tProd_elim'

theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (π i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction' l with i l ih
  · exact MeasurableSet.univ
  · exact (hs i).prod ih
#align measurable_set.tprod MeasurableSet.tProd

end TProd

instance Sum.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α ⊕ β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr
#align sum.measurable_space Sum.instMeasurableSpace

section Sum

@[measurability]
theorem measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left
#align measurable_inl measurable_inl

@[measurability]
theorem measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right
#align measurable_inr measurable_inr

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem measurableSet_sum_iff {s : Set (α ⊕ β)} :
    MeasurableSet s ↔ MeasurableSet (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s) :=
  Iff.rfl

theorem measurable_sum {_ : MeasurableSpace γ} {f : α ⊕ β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)
#align measurable_sum measurable_sum

@[measurability]
theorem Measurable.sumElim {_ : MeasurableSpace γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_sum hf hg
#align measurable.sum_elim Measurable.sumElim

theorem Measurable.sumMap {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map f g) :=
  (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image
#align measurable_set.inl_image MeasurableSet.inl_image

@[simp] theorem measurableSet_inr_image {s : Set β} :
    MeasurableSet (Sum.inr '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image
#align measurable_set_inr_image measurableSet_inr_image

theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image
#align measurable_set_range_inl measurableSet_range_inl

theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image
#align measurable_set_range_inr measurableSet_range_inr

end Sum

instance Sigma.instMeasurableSpace {α} {β : α → Type*} [m : ∀ a, MeasurableSpace (β a)] :
    MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)
#align sigma.measurable_space Sigma.instMeasurableSpace

section prop
variable [MeasurableSpace α] {p q : α → Prop}

@[simp] theorem measurableSet_setOf : MeasurableSet {a | p a} ↔ Measurable p :=
  ⟨fun h ↦ measurable_to_prop <| by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩
#align measurable_set_set_of measurableSet_setOf

@[simp] theorem measurable_mem : Measurable (· ∈ s) ↔ MeasurableSet s := measurableSet_setOf.symm
#align measurable_mem measurable_mem

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOf
#align measurable.set_of Measurable.setOf

alias ⟨_, MeasurableSet.mem⟩ := measurable_mem
#align measurable_set.mem MeasurableSet.mem

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
lemma measurable_set_not_mem (a : α) : Measurable fun s : Set α ↦ a ∉ s :=
  (measurable_discrete Not).comp <| measurable_set_mem a

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurableSet_mem (a : α) : MeasurableSet {s : Set α | a ∈ s} :=
  measurableSet_setOf.2 <| measurable_set_mem _

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurableSet_not_mem (a : α) : MeasurableSet {s : Set α | a ∉ s} :=
  measurableSet_setOf.2 <| measurable_set_not_mem _

lemma measurable_compl : Measurable ((·ᶜ) : Set α → Set α) :=
  measurable_set_iff.2 fun _ ↦ measurable_set_not_mem _

end Set
end Constructions

namespace MeasurableSpace

/-- The sigma-algebra generated by a single set `s` is `{∅, s, sᶜ, univ}`. -/
@[simp] theorem generateFrom_singleton (s : Set α) :
    generateFrom {s} = MeasurableSpace.comap (· ∈ s) ⊤ := by
  classical
  letI : MeasurableSpace α := generateFrom {s}
  refine le_antisymm (generateFrom_le fun t ht => ⟨{True}, trivial, by simp [ht.symm]⟩) ?_
  rintro _ ⟨u, -, rfl⟩
  exact (show MeasurableSet s from GenerateMeasurable.basic _ <| mem_singleton s).mem trivial
#align measurable_space.generate_from_singleton MeasurableSpace.generateFrom_singleton

end MeasurableSpace

namespace Filter

variable [MeasurableSpace α]

/-- A filter `f` is measurably generates if each `s ∈ f` includes a measurable `t ∈ f`. -/
class IsMeasurablyGenerated (f : Filter α) : Prop where
  exists_measurable_subset : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, MeasurableSet t ∧ t ⊆ s
#align filter.is_measurably_generated Filter.IsMeasurablyGenerated

instance isMeasurablyGenerated_bot : IsMeasurablyGenerated (⊥ : Filter α) :=
  ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩
#align filter.is_measurably_generated_bot Filter.isMeasurablyGenerated_bot

instance isMeasurablyGenerated_top : IsMeasurablyGenerated (⊤ : Filter α) :=
  ⟨fun _s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩
#align filter.is_measurably_generated_top Filter.isMeasurablyGenerated_top

theorem Eventually.exists_measurable_mem {f : Filter α} [IsMeasurablyGenerated f] {p : α → Prop}
    (h : ∀ᶠ x in f, p x) : ∃ s ∈ f, MeasurableSet s ∧ ∀ x ∈ s, p x :=
  IsMeasurablyGenerated.exists_measurable_subset h
#align filter.eventually.exists_measurable_mem Filter.Eventually.exists_measurable_mem

theorem Eventually.exists_measurable_mem_of_smallSets {f : Filter α} [IsMeasurablyGenerated f]
    {p : Set α → Prop} (h : ∀ᶠ s in f.smallSets, p s) : ∃ s ∈ f, MeasurableSet s ∧ p s :=
  let ⟨_s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩
#align filter.eventually.exists_measurable_mem_of_small_sets Filter.Eventually.exists_measurable_mem_of_smallSets

instance inf_isMeasurablyGenerated (f g : Filter α) [IsMeasurablyGenerated f]
    [IsMeasurablyGenerated g] : IsMeasurablyGenerated (f ⊓ g) := by
  constructor
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases IsMeasurablyGenerated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine ⟨s'f ∩ s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, ?_⟩
  exact inter_subset_inter hs'sf hs'sg
#align filter.inf_is_measurably_generated Filter.inf_isMeasurablyGenerated

theorem principal_isMeasurablyGenerated_iff {s : Set α} :
    IsMeasurablyGenerated (𝓟 s) ↔ MeasurableSet s := by
  refine ⟨?_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := hts.antisymm ht
  rwa [← this]
#align filter.principal_is_measurably_generated_iff Filter.principal_isMeasurablyGenerated_iff

alias ⟨_, _root_.MeasurableSet.principal_isMeasurablyGenerated⟩ :=
  principal_isMeasurablyGenerated_iff
#align measurable_set.principal_is_measurably_generated MeasurableSet.principal_isMeasurablyGenerated

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
#align filter.infi_is_measurably_generated Filter.iInf_isMeasurablyGenerated

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

/-- We say that a collection of sets is countably spanning if a countable subset spans the
whole type. This is a useful condition in various parts of measure theory. For example, it is
a needed condition to show that the product of two collections generate the product sigma algebra,
see `generateFrom_prod_eq`. -/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ ⋃ n, s n = univ
#align is_countably_spanning IsCountablySpanning

theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩
#align is_countably_spanning_measurable_set isCountablySpanning_measurableSet

namespace MeasurableSet

/-!
### Typeclasses on `Subtype MeasurableSet`
-/

variable [MeasurableSpace α]

instance Subtype.instMembership : Membership α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => a ∈ (s : Set α)⟩
#align measurable_set.subtype.has_mem MeasurableSet.Subtype.instMembership

@[simp]
theorem mem_coe (a : α) (s : Subtype (MeasurableSet : Set α → Prop)) : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl
#align measurable_set.mem_coe MeasurableSet.mem_coe

instance Subtype.instEmptyCollection : EmptyCollection (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩
#align measurable_set.subtype.has_emptyc MeasurableSet.Subtype.instEmptyCollection

@[simp]
theorem coe_empty : ↑(∅ : Subtype (MeasurableSet : Set α → Prop)) = (∅ : Set α) :=
  rfl
#align measurable_set.coe_empty MeasurableSet.coe_empty

instance Subtype.instInsert [MeasurableSingletonClass α] :
    Insert α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => ⟨insert a (s : Set α), s.prop.insert a⟩⟩
#align measurable_set.subtype.has_insert MeasurableSet.Subtype.instInsert

@[simp]
theorem coe_insert [MeasurableSingletonClass α] (a : α)
    (s : Subtype (MeasurableSet : Set α → Prop)) :
    ↑(Insert.insert a s) = (Insert.insert a s : Set α) :=
  rfl
#align measurable_set.coe_insert MeasurableSet.coe_insert

instance Subtype.instSingleton [MeasurableSingletonClass α] :
    Singleton α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a => ⟨{a}, .singleton _⟩⟩

@[simp] theorem coe_singleton [MeasurableSingletonClass α] (a : α) :
    ↑({a} : Subtype (MeasurableSet : Set α → Prop)) = ({a} : Set α) :=
  rfl

instance Subtype.instLawfulSingleton [MeasurableSingletonClass α] :
    LawfulSingleton α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun _ => Subtype.eq <| insert_emptyc_eq _⟩

instance Subtype.instHasCompl : HasCompl (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x => ⟨xᶜ, x.prop.compl⟩⟩
#align measurable_set.subtype.has_compl MeasurableSet.Subtype.instHasCompl

@[simp]
theorem coe_compl (s : Subtype (MeasurableSet : Set α → Prop)) : ↑sᶜ = (sᶜ : Set α) :=
  rfl
#align measurable_set.coe_compl MeasurableSet.coe_compl

instance Subtype.instUnion : Union (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨(x : Set α) ∪ y, x.prop.union y.prop⟩⟩
#align measurable_set.subtype.has_union MeasurableSet.Subtype.instUnion

@[simp]
theorem coe_union (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∪ t) = (s ∪ t : Set α) :=
  rfl
#align measurable_set.coe_union MeasurableSet.coe_union

instance Subtype.instSup : Sup (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => x ∪ y⟩

@[simp]
protected theorem sup_eq_union (s t : {s : Set α // MeasurableSet s}) : s ⊔ t = s ∪ t := rfl

instance Subtype.instInter : Inter (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∩ y, x.prop.inter y.prop⟩⟩
#align measurable_set.subtype.has_inter MeasurableSet.Subtype.instInter

@[simp]
theorem coe_inter (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∩ t) = (s ∩ t : Set α) :=
  rfl
#align measurable_set.coe_inter MeasurableSet.coe_inter

instance Subtype.instInf : Inf (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => x ∩ y⟩

@[simp]
protected theorem inf_eq_inter (s t : {s : Set α // MeasurableSet s}) : s ⊓ t = s ∩ t := rfl

instance Subtype.instSDiff : SDiff (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x \ y, x.prop.diff y.prop⟩⟩
#align measurable_set.subtype.has_sdiff MeasurableSet.Subtype.instSDiff

@[simp]
theorem coe_sdiff (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s \ t) = (s : Set α) \ t :=
  rfl
#align measurable_set.coe_sdiff MeasurableSet.coe_sdiff

instance Subtype.instBot : Bot (Subtype (MeasurableSet : Set α → Prop)) := ⟨∅⟩
#align measurable_set.subtype.has_bot MeasurableSet.Subtype.instBot

@[simp]
theorem coe_bot : ↑(⊥ : Subtype (MeasurableSet : Set α → Prop)) = (⊥ : Set α) :=
  rfl
#align measurable_set.coe_bot MeasurableSet.coe_bot

instance Subtype.instTop : Top (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨Set.univ, MeasurableSet.univ⟩⟩
#align measurable_set.subtype.has_top MeasurableSet.Subtype.instTop

@[simp]
theorem coe_top : ↑(⊤ : Subtype (MeasurableSet : Set α → Prop)) = (⊤ : Set α) :=
  rfl
#align measurable_set.coe_top MeasurableSet.coe_top

instance Subtype.instBooleanAlgebra :
    BooleanAlgebra (Subtype (MeasurableSet : Set α → Prop)) :=
  Subtype.coe_injective.booleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl
#align measurable_set.subtype.boolean_algebra MeasurableSet.Subtype.instBooleanAlgebra

@[measurability]
theorem measurableSet_blimsup {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| blimsup s atTop p := by
  simp only [blimsup_eq_iInf_biSup_of_nat, iSup_eq_iUnion, iInf_eq_iInter]
  exact .iInter fun _ => .iUnion fun m => .iUnion fun hm => h m hm.1
#align measurable_set.measurable_set_blimsup MeasurableSet.measurableSet_blimsup

@[measurability]
theorem measurableSet_bliminf {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.bliminf s Filter.atTop p := by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
  exact .iUnion fun n => .iInter fun m => .iInter fun hm => h m hm.1
#align measurable_set.measurable_set_bliminf MeasurableSet.measurableSet_bliminf

@[measurability]
theorem measurableSet_limsup {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.limsup s Filter.atTop := by
  simpa only [← blimsup_true] using measurableSet_blimsup fun n _ => hs n
#align measurable_set.measurable_set_limsup MeasurableSet.measurableSet_limsup

@[measurability]
theorem measurableSet_liminf {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.liminf s Filter.atTop := by
  simpa only [← bliminf_true] using measurableSet_bliminf fun n _ => hs n
#align measurable_set.measurable_set_liminf MeasurableSet.measurableSet_liminf

end MeasurableSet
