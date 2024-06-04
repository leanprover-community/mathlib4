/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Finset.Update
import Mathlib.Data.Prod.TProd
import Mathlib.GroupTheory.Coset
import Mathlib.Logic.Equiv.Fin
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.SmallSets
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Set.UnionLift

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

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `Filter.Eventually`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is
defined in terms of the Galois connection induced by f.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, measurable equivalence, dynkin system,
π-λ theorem, π-system
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

-- Porting note (#10756): new theorem
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
  refine (h.mono (inter_subset_right _ _)).measurableSet.union ?_
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } := by
    ext x
    simp (config := { contextual := true })
  rw [this]
  exact (hf ht).inter h.measurableSet.of_compl
#align measurable.measurable_of_countable_ne Measurable.measurable_of_countable_ne

end MeasurableFunctions

section Constructions

instance Empty.instMeasurableSpace : MeasurableSpace Empty := ⊤
#align empty.measurable_space Empty.instMeasurableSpace
instance PUnit.instMeasurableSpace : MeasurableSpace PUnit := ⊤
#align punit.measurable_space PUnit.instMeasurableSpace
instance Bool.instMeasurableSpace : MeasurableSpace Bool := ⊤
#align bool.measurable_space Bool.instMeasurableSpace
instance Prop.instMeasurableSpace : MeasurableSpace Prop := ⊤
#align Prop.measurable_space Prop.instMeasurableSpace
instance Nat.instMeasurableSpace : MeasurableSpace ℕ := ⊤
#align nat.measurable_space Nat.instMeasurableSpace
instance Fin.instMeasurableSpace (n : ℕ) : MeasurableSpace (Fin n) := ⊤
instance Int.instMeasurableSpace : MeasurableSpace ℤ := ⊤
#align int.measurable_space Int.instMeasurableSpace
instance Rat.instMeasurableSpace : MeasurableSpace ℚ := ⊤
#align rat.measurable_space Rat.instMeasurableSpace

instance Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]
#noalign empty.measurable_singleton_class
#noalign punit.measurable_singleton_class

instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
#align bool.measurable_singleton_class Bool.instMeasurableSingletonClass
instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩
#align Prop.measurable_singleton_class Prop.instMeasurableSingletonClass
instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ := ⟨fun _ => trivial⟩
#align nat.measurable_singleton_class Nat.instMeasurableSingletonClass
instance Fin.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩
instance Int.instMeasurableSingletonClass : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩
#align int.measurable_singleton_class Int.instMeasurableSingletonClass
instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass ℚ := ⟨fun _ => trivial⟩
#align rat.measurable_singleton_class Rat.instMeasurableSingletonClass

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
@[deprecated exists_measurable_piecewise]
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

-- Porting note (#10756): new theorem
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

-- Porting note (#10756): new theorem
@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image
#align measurable_set.inl_image MeasurableSet.inl_image

-- Porting note (#10756): new theorem
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

/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : Set.range f → α`”, see `MeasurableEmbedding.measurable_rangeSplitting`,
`MeasurableEmbedding.of_measurable_inverse_range`, and
`MeasurableEmbedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`MeasurableEmbedding.equivRange`; the other one follows from
`MeasurableEquiv.measurableEmbedding`, `MeasurableEmbedding.subtype_coe`, and
`MeasurableEmbedding.comp`. -/
structure MeasurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)
#align measurable_embedding MeasurableEmbedding

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

theorem measurableSet_image (hf : MeasurableEmbedding f) {s : Set α} :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩
#align measurable_embedding.measurable_set_image MeasurableEmbedding.measurableSet_image

theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩
#align measurable_embedding.id MeasurableEmbedding.id

theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩
#align measurable_embedding.comp MeasurableEmbedding.comp

theorem subtype_coe {s : Set α} (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s → α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs
#align measurable_embedding.subtype_coe MeasurableEmbedding.subtype_coe

theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ
#align measurable_embedding.measurable_set_range MeasurableEmbedding.measurableSet_range

theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurableSet_image]
#align measurable_embedding.measurable_set_preimage MeasurableEmbedding.measurableSet_preimage

theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]
#align measurable_embedding.measurable_range_splitting MeasurableEmbedding.measurable_rangeSplitting

theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [restrict_extend_range]
    simpa only [rangeSplitting] using hg.comp hf.measurable_rangeSplitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe
#align measurable_embedding.measurable_extend MeasurableEmbedding.measurable_extend

theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_measurable_extend MeasurableEmbedding.exists_measurable_extend

theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk
#align measurable_embedding.measurable_comp_iff MeasurableEmbedding.measurable_comp_iff

end MeasurableEmbedding

theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α} {s : Set α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩
#align measurable_set.exists_measurable_proj MeasurableSet.exists_measurable_proj

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm
#align measurable_equiv MeasurableEquiv

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) := by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
#align measurable_equiv.to_equiv_injective MeasurableEquiv.toEquiv_injective

instance instEquivLike : EquivLike (α ≃ᵐ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' _ _ he _ := toEquiv_injective <| DFunLike.ext' he

@[simp]
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl
#align measurable_equiv.coe_to_equiv MeasurableEquiv.coe_toEquiv

@[measurability]
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_toFun
#align measurable_equiv.measurable MeasurableEquiv.measurable

@[simp]
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl
#align measurable_equiv.coe_mk MeasurableEquiv.coe_mk

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align measurable_equiv.refl MeasurableEquiv.refl

instance instInhabited : Inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun
#align measurable_equiv.trans MeasurableEquiv.trans

theorem coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab := rfl

/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun
  measurable_invFun := ab.measurable_toFun
#align measurable_equiv.symm MeasurableEquiv.symm

@[simp]
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl
#align measurable_equiv.coe_to_equiv_symm MeasurableEquiv.coe_toEquiv_symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵐ β) : α → β := h
#align measurable_equiv.simps.apply MeasurableEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm
#align measurable_equiv.simps.symm_apply MeasurableEquiv.Simps.symm_apply

initialize_simps_projections MeasurableEquiv (toFun → apply, invFun → symm_apply)

@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ := DFunLike.ext' h
#align measurable_equiv.ext MeasurableEquiv.ext

@[simp]
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl
#align measurable_equiv.symm_mk MeasurableEquiv.symm_mk

attribute [simps! apply toEquiv] trans refl

@[simp]
theorem symm_symm (e : α ≃ᵐ β) : e.symm.symm = e := rfl

theorem symm_bijective :
    Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) → β ≃ᵐ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl
#align measurable_equiv.symm_refl MeasurableEquiv.symm_refl

@[simp]
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv
#align measurable_equiv.symm_comp_self MeasurableEquiv.symm_comp_self

@[simp]
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv
#align measurable_equiv.self_comp_symm MeasurableEquiv.self_comp_symm

@[simp]
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y
#align measurable_equiv.apply_symm_apply MeasurableEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x
#align measurable_equiv.symm_apply_apply MeasurableEquiv.symm_apply_apply

@[simp]
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm
#align measurable_equiv.symm_trans_self MeasurableEquiv.symm_trans_self

@[simp]
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self
#align measurable_equiv.self_trans_symm MeasurableEquiv.self_trans_symm

protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.surjective
#align measurable_equiv.surjective MeasurableEquiv.surjective

protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.bijective
#align measurable_equiv.bijective MeasurableEquiv.bijective

protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.injective
#align measurable_equiv.injective MeasurableEquiv.injective

@[simp]
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align measurable_equiv.symm_preimage_preimage MeasurableEquiv.symm_preimage_preimage

theorem image_eq_preimage (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align measurable_equiv.image_eq_preimage MeasurableEquiv.image_eq_preimage

lemma preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s := (image_eq_preimage _ _).symm

lemma image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s := by
  rw [← symm_symm e, preimage_symm, symm_symm]

lemma eq_image_iff_symm_image_eq (e : α ≃ᵐ β) (s : Set β) (t : Set α) :
    s = e '' t ↔ e.symm '' s = t := by
  rw [← coe_toEquiv, Equiv.eq_image_iff_symm_image_eq, coe_toEquiv_symm]

@[simp]
lemma image_preimage (e : α ≃ᵐ β) (s : Set β) : e '' (e ⁻¹' s) = s := by
  rw [← coe_toEquiv, Equiv.image_preimage]

@[simp]
lemma preimage_image (e : α ≃ᵐ β) (s : Set α) : e ⁻¹' (e '' s) = s := by
  rw [← coe_toEquiv, Equiv.preimage_image]

@[simp]
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩
#align measurable_equiv.measurable_set_preimage MeasurableEquiv.measurableSet_preimage

@[simp]
theorem measurableSet_image (e : α ≃ᵐ β) {s : Set α} :
    MeasurableSet (e '' s) ↔ MeasurableSet s := by rw [image_eq_preimage, measurableSet_preimage]
#align measurable_equiv.measurable_set_image MeasurableEquiv.measurableSet_image

@[simp] theorem map_eq (e : α ≃ᵐ β) : MeasurableSpace.map e ‹_› = ‹_› :=
  e.measurable.le_map.antisymm' fun _s ↦ e.measurableSet_preimage.1
#align measurable_equiv.map_eq MeasurableEquiv.map_eq

/-- A measurable equivalence is a measurable embedding. -/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e where
  injective := e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2
#align measurable_equiv.measurable_embedding MeasurableEquiv.measurableEmbedding

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : HEq i₁ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h
  measurable_toFun := by
    subst h
    subst hi
    exact measurable_id
  measurable_invFun := by
    subst h
    subst hi
    exact measurable_id
#align measurable_equiv.cast MeasurableEquiv.cast

/-- Measurable equivalence between `ULift α` and `α`. -/
def ulift.{u, v} {α : Type u} [MeasurableSpace α] : ULift.{v, u} α ≃ᵐ α :=
  ⟨Equiv.ulift, measurable_down, measurable_up⟩

protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable
#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iff

/-- Any two types with unique elements are measurably equivalent. -/
def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := equivOfUnique α β
  measurable_toFun := Subsingleton.measurable
  measurable_invFun := Subsingleton.measurable
#align measurable_equiv.of_unique_of_unique MeasurableEquiv.ofUniqueOfUnique

/-- Products of equivalent measurable spaces are equivalent. -/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv
  measurable_toFun :=
    (ab.measurable_toFun.comp measurable_id.fst).prod_mk
      (cd.measurable_toFun.comp measurable_id.snd)
  measurable_invFun :=
    (ab.measurable_invFun.comp measurable_id.fst).prod_mk
      (cd.measurable_invFun.comp measurable_id.snd)
#align measurable_equiv.prod_congr MeasurableEquiv.prodCongr

/-- Products of measurable spaces are symmetric. -/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β
  measurable_toFun := measurable_id.snd.prod_mk measurable_id.fst
  measurable_invFun := measurable_id.snd.prod_mk measurable_id.fst
#align measurable_equiv.prod_comm MeasurableEquiv.prodComm

/-- Products of measurable spaces are associative. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := measurable_fst.fst.prod_mk <| measurable_fst.snd.prod_mk measurable_snd
  measurable_invFun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd
#align measurable_equiv.prod_assoc MeasurableEquiv.prodAssoc

/-- Sums of measurable spaces are symmetric. -/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : Sum α γ ≃ᵐ Sum β δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable
#align measurable_equiv.sum_congr MeasurableEquiv.sumCongr

/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun :=
    measurable_id.subtype_val.fst.subtype_mk.prod_mk measurable_id.subtype_val.snd.subtype_mk
  measurable_invFun :=
    Measurable.subtype_mk <| measurable_id.fst.subtype_val.prod_mk measurable_id.snd.subtype_val
#align measurable_equiv.set.prod MeasurableEquiv.Set.prod

/-- `univ α ≃ α` as measurable spaces. -/
def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk
#align measurable_equiv.set.univ MeasurableEquiv.Set.univ

/-- `{a} ≃ Unit` as measurable spaces. -/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const
#align measurable_equiv.set.singleton MeasurableEquiv.Set.singleton

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInl : (range Sum.inl : Set (α ⊕ β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    rintro ⟨ab, a, rfl⟩
    simp [Set.range_inl]
  measurable_invFun := Measurable.subtype_mk measurable_inl
#align measurable_equiv.set.range_inl MeasurableEquiv.Set.rangeInl

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInr : (range Sum.inr : Set (Sum α β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    rintro ⟨ab, b, rfl⟩
    simp [Set.range_inr]
  measurable_invFun := Measurable.subtype_mk measurable_inr
#align measurable_equiv.set.range_inr MeasurableEquiv.Set.rangeInr

/-- Products distribute over sums (on the right) as measurable spaces. -/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) where
  toEquiv := .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_sum ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd)
#align measurable_equiv.sum_prod_distrib MeasurableEquiv.sumProdDistrib

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm
#align measurable_equiv.prod_sum_distrib MeasurableEquiv.prodSumDistrib

/-- Products distribute over sums as measurable spaces. -/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)
#align measurable_equiv.sum_prod_sum MeasurableEquiv.sumProdSum

variable {π π' : δ' → Type*} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between `Π a, β₁ a` and `Π a, β₂ a`. -/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)
#align measurable_equiv.Pi_congr_right MeasurableEquiv.piCongrRight

variable (π) in
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a where
  __ := Equiv.piCongrLeft π f
  measurable_toFun := measurable_piCongrLeft f
  measurable_invFun := by
    simp only [invFun_as_coe, coe_fn_symm_mk]
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! (config := .asFn)]
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h
#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTProd

variable (π) in
/-- The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only contains `⋆` -/
@[simps! (config := .asFn)]
def piUnique [Unique δ'] : (∀ i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_uniqueElim

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! (config := .asFn)]
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _
#align measurable_equiv.fun_unique MeasurableEquiv.funUnique

/-- The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps! (config := .asFn)]
def piFinTwo (α : Fin 2 → Type*) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  measurable_toFun := Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  measurable_invFun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩
#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwo

/-- The space `Fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps! (config := .asFn)]
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α
#align measurable_equiv.fin_two_arrow MeasurableEquiv.finTwoArrow

/-- Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`. -/
@[simps! (config := .asFn)]
def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j) where
  toEquiv := .piFinSuccAbove α i
  measurable_toFun := (measurable_pi_apply i).prod_mk <| measurable_pi_iff.2 fun j =>
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 <| i.forall_iff_succAbove.2
    ⟨by simp only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_same, measurable_fst],
      fun j => by simpa only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_succAbove]
        using (measurable_pi_apply _).comp measurable_snd⟩
#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAbove

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`. -/
@[simps! (config := .asFn)]
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π
  measurable_toFun := measurable_piEquivPiSubtypeProd π p
  measurable_invFun := measurable_piEquivPiSubtypeProd_symm π p
#align measurable_equiv.pi_equiv_pi_subtype_prod MeasurableEquiv.piEquivPiSubtypeProd

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
def sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') where
  __ := Equiv.sumPiEquivProdPi α
  measurable_toFun := by
    apply Measurable.prod <;> rw [measurable_pi_iff] <;> rintro i <;> apply measurable_pi_apply
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _

theorem coe_sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α := by rfl

theorem coe_sumPiEquivProdPi_symm (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

/-- The measurable equivalence for (dependent) functions on an Option type
  `(∀ i : Option δ, α i) ≃ᵐ (∀ (i : δ), α i) × α none`. -/
def piOptionEquivProd {δ : Type*} (α : Option δ → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ (i : δ), α i) × α none :=
  let e : Option δ ≃ δ ⊕ Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((a : Option δ) → α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((i : δ) → α (e.symm (Sum.inl i)))
      × ((i' : Unit) → α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i ↦ α (e.symm i))
  let em3 : ((i : δ) → α (e.symm (Sum.inl i))) × ((i' : Unit) → α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) → α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) → α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i ↦ α (e.symm (Sum.inr i)))
  em1.symm.trans <| em2.trans em3

/-- The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i)`
  for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equivalence. -/
def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
    ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i :=
  letI e := Finset.union s t h
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ π (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) e

/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`. -/
def sumCompl {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    s ⊕ (sᶜ : Set α) ≃ᵐ α where
  toEquiv := .sumCompl (· ∈ s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs
#align measurable_equiv.sum_compl MeasurableEquiv.sumCompl

/-- Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`. -/
@[simps toEquiv]
def ofInvolutive (f : α → α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm
  measurable_toFun := hf'
  measurable_invFun := hf'
#align measurable_equiv.of_involutive MeasurableEquiv.ofInvolutive

@[simp] theorem ofInvolutive_apply (f : α → α) (hf : Involutive f) (hf' : Measurable f) (a : α) :
    ofInvolutive f hf hf' a = f a := rfl
#align measurable_equiv.of_involutive_apply MeasurableEquiv.ofInvolutive_apply

@[simp] theorem ofInvolutive_symm (f : α → α) (hf : Involutive f) (hf' : Measurable f) :
    (ofInvolutive f hf hf').symm = ofInvolutive f hf hf' := rfl
#align measurable_equiv.of_involutive_symm MeasurableEquiv.ofInvolutive_symm

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

@[simp] theorem comap_eq (hf : MeasurableEmbedding f) : MeasurableSpace.comap f ‹_› = ‹_› :=
  hf.measurable.comap_le.antisymm fun _s h ↦
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩
#align measurable_embedding.comap_eq MeasurableEmbedding.comap_eq

theorem iff_comap_eq :
    MeasurableEmbedding f ↔
      Injective f ∧ MeasurableSpace.comap f ‹_› = ‹_› ∧ MeasurableSet (range f) :=
  ⟨fun hf ↦ ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf ↦
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩
#align measurable_embedding.iff_comap_eq MeasurableEmbedding.iff_comap_eq

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩; simp [preimage_preimage, Set.image_symm_preimage hf.injective]
    exact measurable_subtype_coe (hf.measurableSet_image' hu)
#align measurable_embedding.equiv_image MeasurableEmbedding.equivImage

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
#align measurable_embedding.equiv_range MeasurableEmbedding.equivRange

theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f := by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective surjective_onto_range⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding
#align measurable_embedding.of_measurable_inverse_on_range MeasurableEmbedding.of_measurable_inverse_on_range

theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H
#align measurable_embedding.of_measurable_inverse MeasurableEmbedding.of_measurable_inverse

open scoped Classical

/-- The **measurable Schröder-Bernstein Theorem**: given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`. -/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ'A : Set α, MeasurableSet A ∧ F A = A by
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun h =>
    compl_subset_compl.mpr <| Set.image_subset _ <| compl_subset_compl.mpr <| Set.image_subset _ h
  let X : ℕ → Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · apply MeasurableSet.iInter
    intro n
    induction' n with n ih
    · exact MeasurableSet.univ
    rw [Function.iterate_succ', Function.comp_apply]
    exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [(injOn_of_injective hf.injective _).image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
#align measurable_embedding.schroeder_bernstein MeasurableEmbedding.schroederBernstein

end MeasurableEmbedding

theorem MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β]
    (h : Measurable (compl : β → β)) (f : α → β) :
    MeasurableSpace.comap (fun a => (f a)ᶜ) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← Function.comp_def, ← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq
#align measurable_space.comap_compl MeasurableSpace.comap_compl

@[simp] theorem MeasurableSpace.comap_not (p : α → Prop) :
    MeasurableSpace.comap (fun a ↦ ¬p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  MeasurableSpace.comap_compl (fun _ _ ↦ measurableSet_top) _
#align measurable_space.comap_not MeasurableSpace.comap_not

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

instance Subtype.instIsLawfulSingleton [MeasurableSingletonClass α] :
    IsLawfulSingleton α (Subtype (MeasurableSet : Set α → Prop)) :=
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

-- Porting note (#10756): new lemma
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

-- Porting note (#10756): new lemma
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
