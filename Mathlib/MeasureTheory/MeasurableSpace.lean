/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measurable_space
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Prod.Tprod
import Mathbin.GroupTheory.Coset
import Mathbin.Logic.Equiv.Fin
import Mathbin.MeasureTheory.MeasurableSpaceDef
import Mathbin.Order.Filter.SmallSets
import Mathbin.Order.LiminfLimsup
import Mathbin.MeasureTheory.Tactic

/-!
# Measurable spaces and measurable functions

This file provides properties of measurable spaces and the functions and isomorphisms
between them. The definition of a measurable space is in `measure_theory.measurable_space_def`.

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
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `filter.eventually`.

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


open Set Encodable Function Equiv

open Filter MeasureTheory

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

namespace MeasurableSpace

section Functors

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}

/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β
    where
  MeasurableSet' s := measurable_set[m] <| f ⁻¹' s
  measurable_set_empty := m.measurable_set_empty
  measurable_set_compl s hs := m.measurable_set_compl _ hs
  measurable_set_unionᵢ f hf := by
    rw [preimage_Union]
    exact m.measurable_set_Union _ hf
#align measurable_space.map MeasurableSpace.map

@[simp]
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun s => Iff.rfl
#align measurable_space.map_id MeasurableSpace.map_id

@[simp]
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun s => Iff.rfl
#align measurable_space.map_comp MeasurableSpace.map_comp

/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α
    where
  MeasurableSet' s := ∃ s', measurable_set[m] s' ∧ f ⁻¹' s' = s
  measurable_set_empty := ⟨∅, m.measurable_set_empty, rfl⟩
  measurable_set_compl := fun s ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurable_set_compl _ h₁, h₂ ▸ rfl⟩
  measurable_set_unionᵢ s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurable_set_unionᵢ _ fun i => (hs' i).left, by simp [hs']⟩
#align measurable_space.comap MeasurableSpace.comap

theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s, MeasurableSet s ∧ f ⁻¹' s = t } := by
  convert generate_from_measurable_set.symm
#align measurable_space.comap_eq_generate_from MeasurableSpace.comap_eq_generateFrom

@[simp]
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨s', hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩
#align measurable_space.comap_id MeasurableSpace.comap_id

@[simp]
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun s =>
    ⟨fun ⟨t, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩
#align measurable_space.comap_comp MeasurableSpace.comap_comp

theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h s hs => h _ ⟨_, hs, rfl⟩, fun h s ⟨t, ht, HEq⟩ => HEq ▸ h _ ht⟩
#align measurable_space.comap_le_iff_le_map MeasurableSpace.comap_le_iff_le_map

theorem gc_comap_map (f : α → β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun f g =>
  comap_le_iff_le_map
#align measurable_space.gc_comap_map MeasurableSpace.gc_comap_map

theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h
#align measurable_space.map_mono MeasurableSpace.map_mono

theorem monotone_map : Monotone (MeasurableSpace.map f) := fun a b h => map_mono h
#align measurable_space.monotone_map MeasurableSpace.monotone_map

theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h
#align measurable_space.comap_mono MeasurableSpace.comap_mono

theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun a b h => comap_mono h
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
theorem comap_supᵢ {m : ι → MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_supᵢ
#align measurable_space.comap_supr MeasurableSpace.comap_supᵢ

@[simp]
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top
#align measurable_space.map_top MeasurableSpace.map_top

@[simp]
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf
#align measurable_space.map_inf MeasurableSpace.map_inf

@[simp]
theorem map_infᵢ {m : ι → MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_infᵢ
#align measurable_space.map_infi MeasurableSpace.map_infᵢ

theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _
#align measurable_space.comap_map_le MeasurableSpace.comap_map_le

theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _
#align measurable_space.le_map_comap MeasurableSpace.le_map_comap

end Functors

theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun t hts => GenerateMeasurable.basic _ <| mem_image_of_mem _ <| hts)
    (generateFrom_le fun t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)
#align measurable_space.comap_generate_from MeasurableSpace.comap_generateFrom

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f :=
  Iff.rfl
#align measurable_iff_le_map measurable_iff_le_map

alias measurable_iff_le_map ↔ Measurable.le_map Measurable.of_le_map
#align measurable.le_map Measurable.le_map
#align measurable.of_le_map Measurable.of_le_map

theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm
#align measurable_iff_comap_le measurable_iff_comap_le

alias measurable_iff_comap_le ↔ Measurable.comap_le Measurable.of_comap_le
#align measurable.comap_le Measurable.comap_le
#align measurable.of_comap_le Measurable.of_comap_le

theorem comap_measurable {m : MeasurableSpace β} (f : α → β) : measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩
#align comap_measurable comap_measurable

theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun t ht => ha _ <| hf <| hb _ ht
#align measurable.mono Measurable.mono

@[measurability]
theorem measurable_from_top [MeasurableSpace β] {f : α → β} : measurable[⊤] f := fun s hs => trivial
#align measurable_from_top measurable_from_top

theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h
#align measurable_generate_from measurable_generateFrom

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

@[nontriviality, measurability]
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun s hs =>
  @Subsingleton.measurableSet α _ _ _
#align subsingleton.measurable Subsingleton.measurable

@[nontriviality, measurability]
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s hs => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
#align measurable_of_subsingleton_codomain measurable_of_subsingleton_codomain

@[to_additive]
theorem measurable_one [One α] : Measurable (1 : β → α) :=
  @measurable_const _ _ _ _ 1
#align measurable_one measurable_one
#align measurable_zero measurable_zero

theorem measurable_of_empty [IsEmpty α] (f : α → β) : Measurable f :=
  Subsingleton.measurable
#align measurable_of_empty measurable_of_empty

theorem measurable_of_empty_codomain [IsEmpty β] (f : α → β) : Measurable f :=
  haveI := Function.isEmpty f
  measurable_of_empty f
#align measurable_of_empty_codomain measurable_of_empty_codomain

/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
theorem measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : Measurable f :=
  by
  cases isEmpty_or_nonempty β
  · exact measurable_of_empty f
  · convert measurable_const
    exact funext fun x => hf x h.some
#align measurable_const' measurable_const'

theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  fun s hs => (f ⁻¹' s).toFinite.MeasurableSet
#align measurable_of_finite measurable_of_finite

theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s hs => (f ⁻¹' s).to_countable.MeasurableSet
#align measurable_of_countable measurable_of_countable

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

include m

@[measurability]
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable (f^[n])
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate n).comp hf
#align measurable.iterate Measurable.iterate

variable {mβ : MeasurableSpace β}

include mβ

@[measurability]
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht
#align measurable_set_preimage measurableSet_preimage

@[measurability]
theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : Measurable f)
    (hg : Measurable g) : Measurable (piecewise s f g) :=
  by
  intro t ht
  rw [piecewise_preimage]
  exact hs.ite (hf ht) (hg ht)
#align measurable.piecewise Measurable.piecewise

/-- this is slightly different from `measurable.piecewise`. It can be used to show
`measurable (ite (x=0) 0 1)` by
`exact measurable.ite (measurable_set_singleton 0) measurable_const measurable_const`,
but replacing `measurable.ite` by `measurable.piecewise` in that example proof does not work. -/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg
#align measurable.ite Measurable.ite

@[measurability]
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const
#align measurable.indicator Measurable.indicator

@[measurability, to_additive]
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (mulSupport f) :=
  hf (measurableSet_singleton 1).compl
#align measurable_set_mul_support measurableSet_mulSupport
#align measurable_set_support measurableSet_support

/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x ≠ g x }) : Measurable g :=
  by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  apply MeasurableSet.union (h.mono (inter_subset_right _ _)).MeasurableSet
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } :=
    by
    ext x
    simp (config := { contextual := true })
  rw [this]
  exact (hf ht).inter h.measurable_set.of_compl
#align measurable.measurable_of_countable_ne Measurable.measurable_of_countable_ne

end MeasurableFunctions

section Constructions

instance : MeasurableSpace Empty :=
  ⊤

instance : MeasurableSpace PUnit :=
  ⊤

-- this also works for `unit`
instance : MeasurableSpace Bool :=
  ⊤

instance : MeasurableSpace ℕ :=
  ⊤

instance : MeasurableSpace ℤ :=
  ⊤

instance : MeasurableSpace ℚ :=
  ⊤

instance : MeasurableSingletonClass Empty :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass PUnit :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass Bool :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℕ :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℤ :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℚ :=
  ⟨fun _ => trivial⟩

theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f :=
  by
  intro s hs
  rw [← bUnion_preimage_singleton]
  refine' MeasurableSet.unionᵢ fun y => MeasurableSet.unionᵢ fun hy => _
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]
#align measurable_to_countable measurable_to_countable

@[measurability]
theorem measurable_unit [MeasurableSpace α] (f : Unit → α) : Measurable f :=
  measurable_from_top
#align measurable_unit measurable_unit

section Nat

variable [MeasurableSpace α]

@[measurability]
theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top
#align measurable_from_nat measurable_from_nat

theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable
#align measurable_to_nat measurable_to_nat

theorem measurable_find_greatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun x => hN _ N.findGreatest_le
#align measurable_find_greatest' measurable_find_greatest'

theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N :=
  by
  refine' measurable_find_greatest' fun k hk => _
  simp only [Nat.findGreatest_eq_iff, set_of_and, set_of_forall, ← compl_set_of]
  repeat'
    apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.interᵢ,
        MeasurableSet.compl, hN] <;>
      try intros
#align measurable_find_greatest measurable_findGreatest

theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) :=
  by
  refine' measurable_to_nat fun x => _
  rw [preimage_find_eq_disjointed]
  exact MeasurableSet.disjointed hm _
#align measurable_find measurable_find

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

instance {α} {r : α → α → Prop} [m : MeasurableSpace α] : MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)

instance {α} {s : Setoid α} [m : MeasurableSpace α] : MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''

@[to_additive]
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.measurableSpace
#align quotient_group.measurable_space QuotientGroup.measurableSpace
#align quotient_add_group.measurable_space quotientAddGroup.measurableSpace

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
  fun s => id
#align measurable_quotient_mk measurable_quotient_mk'

@[measurability]
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun s => id
#align measurable_quotient_mk' measurable_quotient_mk''

@[measurability]
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun s => id
#align measurable_quot_mk measurable_quot_mk

@[to_additive]
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable (coe : G → G ⧸ S) :=
  measurable_quotient_mk''
#align quotient_group.measurable_coe QuotientGroup.measurable_coe
#align quotient_add_group.measurable_coe quotientAddGroup.measurable_coe

attribute [measurability] QuotientGroup.measurable_coe quotientAddGroup.measurable_coe

@[to_additive]
theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G] {S : Subgroup G}
    {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ (coe : G → G ⧸ S)) :=
  measurable_from_quotient
#align quotient_group.measurable_from_quotient QuotientGroup.measurable_from_quotient
#align quotient_add_group.measurable_from_quotient quotientAddGroup.measurable_from_quotient

end Quotient

section Subtype

instance {α} {p : α → Prop} [m : MeasurableSpace α] : MeasurableSpace (Subtype p) :=
  m.comap (coe : _ → α)

section

variable [MeasurableSpace α]

@[measurability]
theorem measurable_subtype_coe {p : α → Prop} : Measurable (coe : Subtype p → α) :=
  MeasurableSpace.le_map_comap
#align measurable_subtype_coe measurable_subtype_coe

instance {p : α → Prop} [MeasurableSingletonClass α] : MeasurableSingletonClass (Subtype p)
    where measurableSet_singleton x :=
    by
    have : MeasurableSet {(x : α)} := measurable_set_singleton _
    convert @measurable_subtype_coe α _ p _ this
    ext y
    simp [Subtype.ext_iff]

end

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

include m

theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t → MeasurableSet ((coe : s → α) '' t)
  | ⟨u, (hu : MeasurableSet u), (Eq : coe ⁻¹' u = t)⟩ =>
    by
    rw [← Eq, Subtype.image_preimage_coe]
    exact hu.inter hs
#align measurable_set.subtype_image MeasurableSet.subtype_image

include mβ

@[measurability]
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf
#align measurable.subtype_coe Measurable.subtype_coe

@[measurability]
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, (· ∘ ·), Subtype.coe_mk, hf hs.1]
#align measurable.subtype_mk Measurable.subtype_mk

theorem measurable_of_measurable_union_cover {f : α → β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ ⊆ s ∪ t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f :=
  by
  intro u hu
  convert (hs.subtype_image (hc hu)).union (ht.subtype_image (hd hu))
  change f ⁻¹' u = coe '' (coe ⁻¹' (f ⁻¹' u) : Set s) ∪ coe '' (coe ⁻¹' (f ⁻¹' u) : Set t)
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, Subtype.range_coe,
    Subtype.range_coe, ← inter_distrib_left, univ_subset_iff.1 h, inter_univ]
#align measurable_of_measurable_union_cover measurable_of_measurable_union_cover

theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.restrict f)) (h₂ : Measurable (sᶜ.restrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s (sᶜ) hs hs.compl (union_compl_self s).ge h₁ h₂
#align measurable_of_restrict_of_restrict_compl measurable_of_restrict_of_restrict_compl

theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f) {g : sᶜ → β}
    (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)
#align measurable.dite Measurable.dite

theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.restrict f)) : Measurable f :=
  letI : Fintype s := finite.fintype hs
  measurable_of_restrict_of_restrict_compl hs.measurable_set (measurable_of_finite _) hf
#align measurable_of_measurable_on_compl_finite measurable_of_measurable_on_compl_finite

theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.restrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf
#align measurable_of_measurable_on_compl_singleton measurable_of_measurable_on_compl_singleton

end Subtype

section Prod

/-- A `measurable_space` structure on the product of two measurable spaces. -/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
#align measurable_space.prod MeasurableSpace.prod

instance {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] : MeasurableSpace (α × β) :=
  m₁.Prod m₂

@[measurability]
theorem measurable_fst {ma : MeasurableSpace α} {mb : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left
#align measurable_fst measurable_fst

@[measurability]
theorem measurable_snd {ma : MeasurableSpace α} {mb : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right
#align measurable_snd measurable_snd

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

include m mβ mγ

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

theorem Measurable.prod_mk {β γ} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg
#align measurable.prod_mk Measurable.prod_mk

theorem Measurable.prod_map [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prod_mk (hg.comp measurable_snd)
#align measurable.prod_map Measurable.prod_map

omit mγ

theorem measurable_prod_mk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prod_mk measurable_id
#align measurable_prod_mk_left measurable_prod_mk_left

theorem measurable_prod_mk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prod_mk measurable_const
#align measurable_prod_mk_right measurable_prod_mk_right

include mγ

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

omit mγ

@[measurability]
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst
#align measurable_swap measurable_swap

theorem measurable_swap_iff {mγ : MeasurableSpace γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => by
    convert hf.comp measurable_swap
    ext ⟨x, y⟩
    rfl, fun hf => hf.comp measurable_swap⟩
#align measurable_swap_iff measurable_swap_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[measurability]
theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)
#align measurable_set.prod MeasurableSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t :=
  by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine' ⟨fun hst => _, fun h => h.1.Prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prod_mk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prod_mk_left hst
  simp_all
#align measurable_set_prod_of_nonempty measurableSet_prod_of_nonempty

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ :=
  by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]
#align measurable_set_prod measurableSet_prod

theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => by
    convert measurable_swap hs
    ext ⟨x, y⟩
    rfl, fun hs => measurable_swap hs⟩
#align measurable_set_swap_iff measurableSet_swap_iff

instance [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ =>
    @singleton_prod_singleton _ _ a b ▸
      (measurableSet_singleton a).Prod (measurableSet_singleton b)⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurable_from_prod_countable [Countable β] [MeasurableSingletonClass β]
    {mγ : MeasurableSpace γ} {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y)) :
    Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ ({y} : Set β) :=
    by
    ext1 ⟨x, y⟩
    simp [and_assoc', and_left_comm]
  rw [this]
  exact MeasurableSet.unionᵢ fun y => (hf y hs).Prod (measurable_set_singleton y)
#align measurable_from_prod_countable measurable_from_prod_countable

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
@[measurability]
theorem Measurable.find {m : MeasurableSpace α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  haveI : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable fun n => hf n
  this.comp (Measurable.prod_mk measurable_id (measurable_find h hp))
#align measurable.find Measurable.find

/-- Given countably many disjoint measurable sets `t n` and countably many measurable
functions `g n`, one can construct a measurable function that coincides with `g n` on `t n`. -/
theorem exists_measurable_piecewise_nat {m : MeasurableSpace α} (t : ℕ → Set β)
    (t_meas : ∀ n, MeasurableSet (t n)) (t_disj : Pairwise (Disjoint on t)) (g : ℕ → β → α)
    (hg : ∀ n, Measurable (g n)) : ∃ f : β → α, Measurable f ∧ ∀ n x, x ∈ t n → f x = g n x := by
  classical
    let p : ℕ → β → Prop := fun n x => x ∈ t n ∪ (⋃ k, t k)ᶜ
    have M : ∀ n, MeasurableSet { x | p n x } := fun n =>
      (t_meas n).union (MeasurableSet.compl (MeasurableSet.unionᵢ t_meas))
    have P : ∀ x, ∃ n, p n x := by
      intro x
      by_cases H : ∀ i : ℕ, x ∉ t i
      · exact ⟨0, Or.inr (by simpa only [mem_Inter, compl_Union] using H)⟩
      · simp only [not_forall, not_not_mem] at H
        rcases H with ⟨n, hn⟩
        exact ⟨n, Or.inl hn⟩
    refine' ⟨fun x => g (Nat.find (P x)) x, Measurable.find hg M P, _⟩
    intro n x hx
    have : x ∈ t (Nat.find (P x)) :=
      by
      have B : x ∈ t (Nat.find (P x)) ∪ (⋃ k, t k)ᶜ := Nat.find_spec (P x)
      have B' : (∀ i : ℕ, x ∉ t i) ↔ False :=
        by
        simp only [iff_false_iff, not_forall, not_not_mem]
        exact ⟨n, hx⟩
      simpa only [B', mem_union, mem_Inter, or_false_iff, compl_Union, mem_compl_iff] using B
    congr
    by_contra h
    exact (t_disj (Ne.symm h)).le_bot ⟨hx, this⟩
#align exists_measurable_piecewise_nat exists_measurable_piecewise_nat

end Prod

section Pi

variable {π : δ → Type _} [MeasurableSpace α]

instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  ⨆ a, (m a).comap fun b => b a
#align measurable_space.pi MeasurableSpace.pi

variable [∀ a, MeasurableSpace (π a)] [MeasurableSpace γ]

theorem measurable_pi_iff {g : α → ∀ a, π a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_supᵢ,
    MeasurableSpace.comap_comp, Function.comp, supᵢ_le_iff]
#align measurable_pi_iff measurable_pi_iff

@[measurability]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, π a => f a :=
  Measurable.of_comap_le <| le_supᵢ _ a
#align measurable_pi_apply measurable_pi_apply

@[measurability]
theorem Measurable.eval {a : δ} {g : α → ∀ a, π a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg
#align measurable.eval Measurable.eval

@[measurability]
theorem measurable_pi_lambda (f : α → ∀ a, π a) (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf
#align measurable_pi_lambda measurable_pi_lambda

/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
theorem measurable_update (f : ∀ a : δ, π a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  by
  apply measurable_pi_lambda
  intro x; by_cases hx : x = a
  · cases hx
    convert measurable_id
    ext
    simp
  simp_rw [update_noteq hx]; apply measurable_const
#align measurable_update measurable_update

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `measurable_set.prod`. -/
@[measurability]
theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (π i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) :=
  by
  rw [pi_def]
  exact MeasurableSet.binterᵢ hs fun i hi => measurable_pi_apply _ (ht i hi)
#align measurable_set.pi MeasurableSet.pi

theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (π i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i
#align measurable_set.univ_pi MeasurableSet.univ_pi

theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine' ⟨fun hst i hi => _, MeasurableSet.pi hs⟩
    convert measurable_update f hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj
#align measurable_set_pi_of_nonempty measurableSet_pi_of_nonempty

theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ :=
  by
  cases' (pi s t).eq_empty_or_nonempty with h h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]
#align measurable_set_pi measurableSet_pi

instance [Countable δ] [∀ a, MeasurableSingletonClass (π a)] :
    MeasurableSingletonClass (∀ a, π a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (π)

@[measurability]
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π).symm :=
  by
  apply measurable_pi_iff.2 fun j => _
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun f : ∀ i : { x // p x }, π ↑i => f ⟨j, hj⟩ := measurable_pi_apply ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun f : ∀ i : { x // ¬p x }, π ↑i => f ⟨j, hj⟩ := measurable_pi_apply ⟨j, hj⟩
    exact Measurable.comp this measurable_snd
#align measurable_pi_equiv_pi_subtype_prod_symm measurable_piEquivPiSubtypeProd_symm

@[measurability]
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π) :=
  by
  refine' measurable_prod.2 _
  constructor <;>
    · apply measurable_pi_iff.2 fun j => _
      simp only [pi_equiv_pi_subtype_prod_apply, measurable_pi_apply]
#align measurable_pi_equiv_pi_subtype_prod measurable_piEquivPiSubtypeProd

end Pi

/- warning: tprod.measurable_space -> Tprod.measurableSpace is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} (π : δ -> Type.{u2}) [_inst_1 : forall (x : δ), MeasurableSpace.{u2} (π x)] (l : List.{u1} δ), MeasurableSpace.{max u2 u3} (List.TProd.{u1, u2, u3} δ π l)
but is expected to have type
  PUnit.{max (max (succ (succ u1)) (succ u2)) (succ (succ u3))}
Case conversion may be inaccurate. Consider using '#align tprod.measurable_space Tprod.measurableSpaceₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance Tprod.measurableSpace (π : δ → Type _) [∀ x, MeasurableSpace (π x)] :
    ∀ l : List δ, MeasurableSpace (List.TProd π l)
  | [] => PUnit.measurableSpace
  | i::is => @Prod.measurableSpace _ _ _ (Tprod.measurableSpace is)
#align tprod.measurable_space Tprod.measurableSpace

section Tprod

open List

variable {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ π l) :=
  by
  induction' l with i l ih
  · exact measurable_const
  · exact (measurable_pi_apply i).prod_mk ih
#align measurable_tprod_mk measurable_tProd_mk

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd π l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp [measurable_fst]
    · rw [funext <| tprod.elim_of_ne _ hji]
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd
#align measurable_tprod_elim measurable_tProd_elim

theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd π l → ∀ i, π i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)
#align measurable_tprod_elim' measurable_tProd_elim'

theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (π i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction' l with i l ih
  exact MeasurableSet.univ
  exact (hs i).Prod ih
#align measurable_set.tprod MeasurableSet.tProd

end Tprod

instance {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] : MeasurableSpace (Sum α β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

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

include m mβ

theorem measurable_sum {mγ : MeasurableSpace γ} {f : Sum α β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)
#align measurable_sum measurable_sum

@[measurability]
theorem Measurable.sum_elim {mγ : MeasurableSpace γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_sum hf hg
#align measurable.sum_elim Measurable.sum_elim

theorem MeasurableSet.inl_image {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet (Sum.inl '' s : Set (Sum α β)) :=
  ⟨show MeasurableSet (Sum.inl ⁻¹' _) by
      rwa [preimage_image_eq]
      exact fun a b => Sum.inl.inj,
    have : Sum.inr ⁻¹' (Sum.inl '' s : Set (Sum α β)) = ∅ :=
      eq_empty_of_subset_empty fun x ⟨y, hy, Eq⟩ => by contradiction
    show MeasurableSet (Sum.inr ⁻¹' _) by
      rw [this]
      exact MeasurableSet.empty⟩
#align measurable_set.inl_image MeasurableSet.inl_image

theorem measurableSet_inr_image {s : Set β} (hs : MeasurableSet s) :
    MeasurableSet (Sum.inr '' s : Set (Sum α β)) :=
  ⟨have : Sum.inl ⁻¹' (Sum.inr '' s : Set (Sum α β)) = ∅ :=
      eq_empty_of_subset_empty fun x ⟨y, hy, Eq⟩ => by contradiction
    show MeasurableSet (Sum.inl ⁻¹' _) by
      rw [this]
      exact MeasurableSet.empty,
    show MeasurableSet (Sum.inr ⁻¹' _) by
      rwa [preimage_image_eq]
      exact fun a b => Sum.inr.inj⟩
#align measurable_set_inr_image measurableSet_inr_image

omit m

theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (Sum α β)) :=
  by
  rw [← image_univ]
  exact measurable_set.univ.inl_image
#align measurable_set_range_inl measurableSet_range_inl

theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (Sum α β)) :=
  by
  rw [← image_univ]
  exact measurableSet_inr_image MeasurableSet.univ
#align measurable_set_range_inr measurableSet_range_inr

end Sum

instance {α} {β : α → Type _} [m : ∀ a, MeasurableSpace (β a)] : MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

end Constructions

/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : range f → α`”, see `measurable_embedding.measurable_range_splitting`,
`measurable_embedding.of_measurable_inverse_range`, and
`measurable_embedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`measurable_embedding.equiv_range`; the other one follows from
`measurable_equiv.measurable_embedding`, `measurable_embedding.subtype_coe`, and
`measurable_embedding.comp`. -/
@[protect_proj]
structure MeasurableEmbedding {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] (f : α → β) :
  Prop where
  Injective : Injective f
  Measurable : Measurable f
  measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)
#align measurable_embedding MeasurableEmbedding

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

include mα

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
  ⟨hg.Injective.comp hf.Injective, hg.Measurable.comp hf.Measurable, fun s hs => by
    rwa [← image_image, hg.measurable_set_image, hf.measurable_set_image]⟩
#align measurable_embedding.comp MeasurableEmbedding.comp

theorem subtype_coe {s : Set α} (hs : MeasurableSet s) : MeasurableEmbedding (coe : s → α) :=
  { Injective := Subtype.coe_injective
    Measurable := measurable_subtype_coe
    measurableSet_image' := fun _ => MeasurableSet.subtype_image hs }
#align measurable_embedding.subtype_coe MeasurableEmbedding.subtype_coe

theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) :=
  by
  rw [← image_univ]
  exact hf.measurable_set_image' MeasurableSet.univ
#align measurable_embedding.measurable_set_range MeasurableEmbedding.measurableSet_range

theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurable_set_image]
#align measurable_embedding.measurable_set_preimage MeasurableEmbedding.measurableSet_preimage

theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) : Measurable (rangeSplitting f) :=
  fun s hs => by
  rwa [preimage_range_splitting hf.injective, ←
    (subtype_coe hf.measurable_set_range).measurableSet_image, ← image_comp,
    coe_comp_range_factorization, hf.measurable_set_image]
#align measurable_embedding.measurable_range_splitting MeasurableEmbedding.measurable_rangeSplitting

theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') :=
  by
  refine' measurable_of_restrict_of_restrict_compl hf.measurable_set_range _ _
  · rw [restrict_extend_range]
    simpa only [range_splitting] using hg.comp hf.measurable_range_splitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe
#align measurable_embedding.measurable_extend MeasurableEmbedding.measurable_extend

theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun x => hf.Injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_measurable_extend MeasurableEmbedding.exists_measurable_extend

theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f :=
  by
  refine' ⟨fun H => _, hg.measurable.comp⟩
  suffices Measurable ((range_splitting g ∘ range_factorization g) ∘ f) by
    rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this
  exact hg.measurable_range_splitting.comp H.subtype_mk
#align measurable_embedding.measurable_comp_iff MeasurableEmbedding.measurable_comp_iff

end MeasurableEmbedding

theorem MeasurableSet.exists_measurable_proj {m : MeasurableSpace α} {s : Set α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩
#align measurable_set.exists_measurable_proj MeasurableSet.exists_measurable_proj

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure MeasurableEquiv (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  measurable_to_fun : Measurable to_equiv
  measurable_inv_fun : Measurable to_equiv.symm
#align measurable_equiv MeasurableEquiv

-- mathport name: «expr ≃ᵐ »
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable (α β) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

instance : CoeFun (α ≃ᵐ β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

variable {α β}

@[simp]
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl
#align measurable_equiv.coe_to_equiv MeasurableEquiv.coe_toEquiv

@[measurability]
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_to_fun
#align measurable_equiv.measurable MeasurableEquiv.measurable

@[simp]
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl
#align measurable_equiv.coe_mk MeasurableEquiv.coe_mk

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type _) [MeasurableSpace α] : α ≃ᵐ α
    where
  toEquiv := Equiv.refl α
  measurable_to_fun := measurable_id
  measurable_inv_fun := measurable_id
#align measurable_equiv.refl MeasurableEquiv.refl

instance : Inhabited (α ≃ᵐ α) :=
  ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ
    where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_to_fun := bc.measurable_to_fun.comp ab.measurable_to_fun
  measurable_inv_fun := ab.measurable_inv_fun.comp bc.measurable_inv_fun
#align measurable_equiv.trans MeasurableEquiv.trans

/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_to_fun := ab.measurable_inv_fun
  measurable_inv_fun := ab.measurable_to_fun
#align measurable_equiv.symm MeasurableEquiv.symm

@[simp]
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl
#align measurable_equiv.coe_to_equiv_symm MeasurableEquiv.coe_toEquiv_symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵐ β) : α → β :=
  h
#align measurable_equiv.simps.apply MeasurableEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ᵐ β) : β → α :=
  h.symm
#align measurable_equiv.simps.symm_apply MeasurableEquiv.Simps.symmApply

initialize_simps_projections MeasurableEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun →
  symm_apply)

theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) :=
  by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
#align measurable_equiv.to_equiv_injective MeasurableEquiv.toEquiv_injective

@[ext]
theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ :=
  toEquiv_injective <| Equiv.coe_fn_injective h
#align measurable_equiv.ext MeasurableEquiv.ext

@[simp]
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl
#align measurable_equiv.symm_mk MeasurableEquiv.symm_mk

attribute [simps apply toEquiv] trans refl

@[simp]
theorem symm_refl (α : Type _) [MeasurableSpace α] : (refl α).symm = refl α :=
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
  e.toEquiv.Surjective
#align measurable_equiv.surjective MeasurableEquiv.surjective

protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.Bijective
#align measurable_equiv.bijective MeasurableEquiv.bijective

protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.Injective
#align measurable_equiv.injective MeasurableEquiv.injective

@[simp]
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align measurable_equiv.symm_preimage_preimage MeasurableEquiv.symm_preimage_preimage

theorem image_eq_preimage (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align measurable_equiv.image_eq_preimage MeasurableEquiv.image_eq_preimage

@[simp]
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.Measurable h⟩
#align measurable_equiv.measurable_set_preimage MeasurableEquiv.measurableSet_preimage

@[simp]
theorem measurableSet_image (e : α ≃ᵐ β) {s : Set α} : MeasurableSet (e '' s) ↔ MeasurableSet s :=
  by rw [image_eq_preimage, measurableSet_preimage]
#align measurable_equiv.measurable_set_image MeasurableEquiv.measurableSet_image

/-- A measurable equivalence is a measurable embedding. -/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e :=
  { Injective := e.Injective
    Measurable := e.Measurable
    measurableSet_image' := fun s => e.measurableSet_image.2 }
#align measurable_equiv.measurable_embedding MeasurableEquiv.measurableEmbedding

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : HEq i₁ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h
  measurable_to_fun := by
    subst h
    subst hi
    exact measurable_id
  measurable_inv_fun := by
    subst h
    subst hi
    exact measurable_id
#align measurable_equiv.cast MeasurableEquiv.cast

protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe =>
      by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.Measurable
      rwa [coe_to_equiv, symm_trans_self] at this)
    fun h => h.comp e.Measurable
#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iff

/-- Any two types with unique elements are measurably equivalent. -/
def ofUniqueOfUnique (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := equivOfUnique α β
  measurable_to_fun := Subsingleton.measurable
  measurable_inv_fun := Subsingleton.measurable
#align measurable_equiv.of_unique_of_unique MeasurableEquiv.ofUniqueOfUnique

/-- Products of equivalent measurable spaces are equivalent. -/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ
    where
  toEquiv := prodCongr ab.toEquiv cd.toEquiv
  measurable_to_fun :=
    (ab.measurable_to_fun.comp measurable_id.fst).prod_mk
      (cd.measurable_to_fun.comp measurable_id.snd)
  measurable_inv_fun :=
    (ab.measurable_inv_fun.comp measurable_id.fst).prod_mk
      (cd.measurable_inv_fun.comp measurable_id.snd)
#align measurable_equiv.prod_congr MeasurableEquiv.prodCongr

/-- Products of measurable spaces are symmetric. -/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := prodComm α β
  measurable_to_fun := measurable_id.snd.prod_mk measurable_id.fst
  measurable_inv_fun := measurable_id.snd.prod_mk measurable_id.fst
#align measurable_equiv.prod_comm MeasurableEquiv.prodComm

/-- Products of measurable spaces are associative. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ
    where
  toEquiv := prodAssoc α β γ
  measurable_to_fun := measurable_fst.fst.prod_mk <| measurable_fst.snd.prod_mk measurable_snd
  measurable_inv_fun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd
#align measurable_equiv.prod_assoc MeasurableEquiv.prodAssoc

/-- Sums of measurable spaces are symmetric. -/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : Sum α γ ≃ᵐ Sum β δ
    where
  toEquiv := sumCongr ab.toEquiv cd.toEquiv
  measurable_to_fun := by
    cases' ab with ab' abm; cases ab'; cases' cd with cd' cdm; cases cd'
    refine' measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
  measurable_inv_fun := by
    cases' ab with ab' _ abm; cases ab'; cases' cd with cd' _ cdm; cases cd'
    refine' measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
#align measurable_equiv.sum_congr MeasurableEquiv.sumCongr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t
    where
  toEquiv := Equiv.Set.prod s t
  measurable_to_fun :=
    measurable_id.subtype_val.fst.subtype_mk.prod_mk measurable_id.subtype_val.snd.subtype_mk
  measurable_inv_fun :=
    Measurable.subtype_mk <| measurable_id.fst.subtype_val.prod_mk measurable_id.snd.subtype_val
#align measurable_equiv.set.prod MeasurableEquiv.Set.prod

/-- `univ α ≃ α` as measurable spaces. -/
def Set.univ (α : Type _) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α
    where
  toEquiv := Equiv.Set.univ α
  measurable_to_fun := measurable_id.subtype_val
  measurable_inv_fun := measurable_id.subtype_mk
#align measurable_equiv.set.univ MeasurableEquiv.Set.univ

/-- `{a} ≃ unit` as measurable spaces. -/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit
    where
  toEquiv := Equiv.Set.singleton a
  measurable_to_fun := measurable_const
  measurable_inv_fun := measurable_const
#align measurable_equiv.set.singleton MeasurableEquiv.Set.singleton

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInl : (range Sum.inl : Set (Sum α β)) ≃ᵐ α
    where
  toFun ab :=
    match ab with
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr b, p⟩ =>
      have : False := by
        cases p
        contradiction
      this.elim
  invFun a := ⟨Sum.inl a, a, rfl⟩
  left_inv := by
    rintro ⟨ab, a, rfl⟩
    rfl
  right_inv a := rfl
  measurable_to_fun s (hs : MeasurableSet s) :=
    by
    refine' ⟨_, hs.inl_image, Set.ext _⟩
    rintro ⟨ab, a, rfl⟩
    simp [set.range_inl._match_1]
  measurable_inv_fun := Measurable.subtype_mk measurable_inl
#align measurable_equiv.set.range_inl MeasurableEquiv.Set.rangeInl

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInr : (range Sum.inr : Set (Sum α β)) ≃ᵐ β
    where
  toFun ab :=
    match ab with
    | ⟨Sum.inr b, _⟩ => b
    | ⟨Sum.inl a, p⟩ =>
      have : False := by
        cases p
        contradiction
      this.elim
  invFun b := ⟨Sum.inr b, b, rfl⟩
  left_inv := by
    rintro ⟨ab, b, rfl⟩
    rfl
  right_inv b := rfl
  measurable_to_fun s (hs : MeasurableSet s) :=
    by
    refine' ⟨_, measurableSet_inr_image hs, Set.ext _⟩
    rintro ⟨ab, b, rfl⟩
    simp [set.range_inr._match_1]
  measurable_inv_fun := Measurable.subtype_mk measurable_inr
#align measurable_equiv.set.range_inr MeasurableEquiv.Set.rangeInr

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Products distribute over sums (on the right) as measurable spaces. -/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Sum α β × γ ≃ᵐ Sum (α × γ) (β × γ)
    where
  toEquiv := sumProdDistrib α β γ
  measurable_to_fun :=
    by
    refine'
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurable_set_range_inl.prod MeasurableSet.univ)
        (measurable_set_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) _ _
    · refine' (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 _
      refine' (prod_congr Set.range_inl (Set.univ _)).symm.measurable_comp_iff.1 _
      dsimp [(· ∘ ·)]
      convert measurable_inl
      ext ⟨a, c⟩
      rfl
    · refine' (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 _
      refine' (prod_congr Set.range_inr (Set.univ _)).symm.measurable_comp_iff.1 _
      dsimp [(· ∘ ·)]
      convert measurable_inr
      ext ⟨b, c⟩
      rfl
  measurable_inv_fun :=
    measurable_sum ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd)
#align measurable_equiv.sum_prod_distrib MeasurableEquiv.sumProdDistrib

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × Sum β γ ≃ᵐ Sum (α × β) (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm
#align measurable_equiv.prod_sum_distrib MeasurableEquiv.prodSumDistrib

/-- Products distribute over sums as measurable spaces. -/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : Sum α β × Sum γ δ ≃ᵐ Sum (Sum (α × γ) (α × δ)) (Sum (β × γ) (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)
#align measurable_equiv.sum_prod_sum MeasurableEquiv.sumProdSum

variable {π π' : δ' → Type _} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between  `Π a, β₁ a` and `Π a, β₂ a`. -/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a
    where
  toEquiv := piCongrRight fun a => (e a).toEquiv
  measurable_to_fun :=
    measurable_pi_lambda _ fun i => (e i).measurable_to_fun.comp (measurable_pi_apply i)
  measurable_inv_fun :=
    measurable_pi_lambda _ fun i => (e i).measurable_inv_fun.comp (measurable_pi_apply i)
#align measurable_equiv.Pi_congr_right MeasurableEquiv.piCongrRight

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps (config := { fullyApplied := false })]
def piMeasurableEquivTprod [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l
    where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_to_fun := measurable_tProd_mk l
  measurable_inv_fun := measurable_tProd_elim' h
#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTprod

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (α β : Type _) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β
    where
  toEquiv := Equiv.funUnique α β
  measurable_to_fun := measurable_pi_apply _
  measurable_inv_fun := measurable_pi_iff.2 fun b => measurable_id
#align measurable_equiv.fun_unique MeasurableEquiv.funUnique

/-- The space `Π i : fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo (α : Fin 2 → Type _) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  measurable_to_fun := Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  measurable_inv_fun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩
#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwo

/-- The space `fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α
#align measurable_equiv.fin_two_arrow MeasurableEquiv.finTwoArrow

/-- Measurable equivalence between `Π j : fin (n + 1), α j` and
`α i × Π j : fin n, α (fin.succ_above i j)`. -/
@[simps (config := { fullyApplied := false })]
def piFinSuccAboveEquiv {n : ℕ} (α : Fin (n + 1) → Type _) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)
    where
  toEquiv := piFinSuccAboveEquiv α i
  measurable_to_fun :=
    (measurable_pi_apply i).prod_mk <| measurable_pi_iff.2 fun j => measurable_pi_apply _
  measurable_inv_fun := by
    simp [measurable_pi_iff, i.forall_iff_succ_above, measurable_fst,
      (measurable_pi_apply _).comp measurable_snd]
#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAboveEquiv

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `equiv.pi_equiv_pi_subtype_prod`. -/
@[simps (config := { fullyApplied := false })]
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i
    where
  toEquiv := piEquivPiSubtypeProd p π
  measurable_to_fun := measurable_piEquivPiSubtypeProd π p
  measurable_inv_fun := measurable_piEquivPiSubtypeProd_symm π p
#align measurable_equiv.pi_equiv_pi_subtype_prod MeasurableEquiv.piEquivPiSubtypeProd

/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`.-/
def sumCompl {s : Set α} [DecidablePred s] (hs : MeasurableSet s) : Sum s (sᶜ : Set α) ≃ᵐ α
    where
  toEquiv := sumCompl s
  measurable_to_fun := by apply Measurable.sum_elim <;> exact measurable_subtype_coe
  measurable_inv_fun := Measurable.dite measurable_inl measurable_inr hs
#align measurable_equiv.sum_compl MeasurableEquiv.sumCompl

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s
    where
  toEquiv := Equiv.Set.image f s hf.Injective
  measurable_to_fun := (hf.Measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_inv_fun := by
    rintro t ⟨u, hu, rfl⟩; simp [preimage_preimage, set.image_symm_preimage hf.injective]
    exact measurable_subtype_coe (hf.measurable_set_image' hu)
#align measurable_embedding.equiv_image MeasurableEmbedding.equivImage

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
#align measurable_embedding.equiv_range MeasurableEmbedding.equivRange

theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f :=
  by
  set e : α ≃ᵐ range f :=
    ⟨⟨range_factorization f, g, H, H.right_inverse_of_surjective surjective_onto_range⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurable_embedding
#align measurable_embedding.of_measurable_inverse_on_range MeasurableEmbedding.of_measurable_inverse_on_range

theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H
#align measurable_embedding.of_measurable_inverse MeasurableEmbedding.of_measurable_inverse

open Classical

/-- The **`measurable Schröder-Bernstein Theorem**: Given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.-/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β :=
  by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ'A : Set α, MeasurableSet A ∧ F A = A
    by
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurable_set_image' Ameas
    refine'
      (MeasurableEquiv.sumCompl Ameas).symm.trans
        (MeasurableEquiv.trans _ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equiv_image _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp
    rw [this]
    exact (hg.equiv_image _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun A B hAB =>
    compl_subset_compl.mpr <| Set.image_subset _ <| compl_subset_compl.mpr <| Set.image_subset _ hAB
  let X : ℕ → Set α := fun n => (F^[n]) univ
  refine' ⟨Inter X, _, _⟩
  · apply MeasurableSet.interᵢ
    intro n
    induction' n with n ih
    · exact MeasurableSet.univ
    rw [Function.iterate_succ', Function.comp_apply]
    exact (hg.measurable_set_image' (hf.measurable_set_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_Inter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (Inter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_Inter] at hx
  apply hy
  rw [(inj_on_of_injective hf.injective _).image_interᵢ_eq]
  swap
  · infer_instance
  rw [mem_Inter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
#align measurable_embedding.schroeder_bernstein MeasurableEmbedding.schroederBernstein

end MeasurableEmbedding

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
  ⟨fun s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩
#align filter.is_measurably_generated_top Filter.isMeasurablyGenerated_top

theorem Eventually.exists_measurable_mem {f : Filter α} [IsMeasurablyGenerated f] {p : α → Prop}
    (h : ∀ᶠ x in f, p x) : ∃ s ∈ f, MeasurableSet s ∧ ∀ x ∈ s, p x :=
  IsMeasurablyGenerated.exists_measurable_subset h
#align filter.eventually.exists_measurable_mem Filter.Eventually.exists_measurable_mem

theorem Eventually.exists_measurable_mem_of_smallSets {f : Filter α} [IsMeasurablyGenerated f]
    {p : Set α → Prop} (h : ∀ᶠ s in f.smallSets, p s) : ∃ s ∈ f, MeasurableSet s ∧ p s :=
  let ⟨s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩
#align filter.eventually.exists_measurable_mem_of_small_sets Filter.Eventually.exists_measurable_mem_of_smallSets

instance inf_isMeasurablyGenerated (f g : Filter α) [IsMeasurablyGenerated f]
    [IsMeasurablyGenerated g] : IsMeasurablyGenerated (f ⊓ g) :=
  by
  refine' ⟨_⟩
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases is_measurably_generated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases is_measurably_generated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine' ⟨s'f ∩ s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, _⟩
  exact inter_subset_inter hs'sf hs'sg
#align filter.inf_is_measurably_generated Filter.inf_isMeasurablyGenerated

theorem principal_isMeasurablyGenerated_iff {s : Set α} :
    IsMeasurablyGenerated (𝓟 s) ↔ MeasurableSet s :=
  by
  refine' ⟨_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := subset.antisymm hts ht
  rwa [← this]
#align filter.principal_is_measurably_generated_iff Filter.principal_isMeasurablyGenerated_iff

alias principal_is_measurably_generated_iff ↔
  _ _root_.measurable_set.principal_is_measurably_generated
#align measurable_set.principal_is_measurably_generated MeasurableSet.principal_isMeasurablyGenerated

instance infᵢ_isMeasurablyGenerated {f : ι → Filter α} [∀ i, IsMeasurablyGenerated (f i)] :
    IsMeasurablyGenerated (⨅ i, f i) :=
  by
  refine' ⟨fun s hs => _⟩
  rw [← equiv.plift.surjective.infi_comp, mem_infi] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => is_measurably_generated.exists_measurable_subset (hVf i)
  refine' ⟨⋂ i : t, U i, _, _, _⟩
  · rw [← equiv.plift.surjective.infi_comp, mem_infi]
    refine' ⟨t, ht, U, hUf, rfl⟩
  · haveI := ht.countable.to_encodable
    exact MeasurableSet.interᵢ fun i => (hU i).1
  · exact Inter_mono fun i => (hU i).2
#align filter.infi_is_measurably_generated Filter.infᵢ_isMeasurablyGenerated

end Filter

/-- We say that a collection of sets is countably spanning if a countable subset spans the
  whole type. This is a useful condition in various parts of measure theory. For example, it is
  a needed condition to show that the product of two collections generate the product sigma algebra,
  see `generate_from_prod_eq`. -/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ (⋃ n, s n) = univ
#align is_countably_spanning IsCountablySpanning

theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, unionᵢ_const _⟩
#align is_countably_spanning_measurable_set isCountablySpanning_measurableSet

namespace MeasurableSet

/-!
### Typeclasses on `subtype measurable_set`
-/


variable [MeasurableSpace α]

instance : Membership α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => a ∈ (s : Set α)⟩

@[simp]
theorem mem_coe (a : α) (s : Subtype (MeasurableSet : Set α → Prop)) : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl
#align measurable_set.mem_coe MeasurableSet.mem_coe

instance : EmptyCollection (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

@[simp]
theorem coe_empty : ↑(∅ : Subtype (MeasurableSet : Set α → Prop)) = (∅ : Set α) :=
  rfl
#align measurable_set.coe_empty MeasurableSet.coe_empty

instance [MeasurableSingletonClass α] : Insert α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => ⟨Insert.insert a s, s.Prop.insert a⟩⟩

@[simp]
theorem coe_insert [MeasurableSingletonClass α] (a : α)
    (s : Subtype (MeasurableSet : Set α → Prop)) :
    ↑(Insert.insert a s) = (Insert.insert a s : Set α) :=
  rfl
#align measurable_set.coe_insert MeasurableSet.coe_insert

instance : HasCompl (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x => ⟨xᶜ, x.Prop.compl⟩⟩

@[simp]
theorem coe_compl (s : Subtype (MeasurableSet : Set α → Prop)) : ↑(sᶜ) = (sᶜ : Set α) :=
  rfl
#align measurable_set.coe_compl MeasurableSet.coe_compl

instance : Union (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∪ y, x.Prop.union y.Prop⟩⟩

@[simp]
theorem coe_union (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∪ t) = (s ∪ t : Set α) :=
  rfl
#align measurable_set.coe_union MeasurableSet.coe_union

instance : Inter (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∩ y, x.Prop.inter y.Prop⟩⟩

@[simp]
theorem coe_inter (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∩ t) = (s ∩ t : Set α) :=
  rfl
#align measurable_set.coe_inter MeasurableSet.coe_inter

instance : SDiff (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x \ y, x.Prop.diffₓ y.Prop⟩⟩

@[simp]
theorem coe_sdiff (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s \ t) = (s \ t : Set α) :=
  rfl
#align measurable_set.coe_sdiff MeasurableSet.coe_sdiff

instance : Bot (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨⊥, MeasurableSet.empty⟩⟩

@[simp]
theorem coe_bot : ↑(⊥ : Subtype (MeasurableSet : Set α → Prop)) = (⊥ : Set α) :=
  rfl
#align measurable_set.coe_bot MeasurableSet.coe_bot

instance : Top (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨⊤, MeasurableSet.univ⟩⟩

@[simp]
theorem coe_top : ↑(⊤ : Subtype (MeasurableSet : Set α → Prop)) = (⊤ : Set α) :=
  rfl
#align measurable_set.coe_top MeasurableSet.coe_top

instance : PartialOrder (Subtype (MeasurableSet : Set α → Prop)) :=
  PartialOrder.lift _ Subtype.coe_injective

instance : DistribLattice (Subtype (MeasurableSet : Set α → Prop)) :=
  { MeasurableSet.Subtype.partialOrder with
    sup := (· ∪ ·)
    le_sup_left := fun a b => show (a : Set α) ≤ a ⊔ b from le_sup_left
    le_sup_right := fun a b => show (b : Set α) ≤ a ⊔ b from le_sup_right
    sup_le := fun a b c ha hb => show (a ⊔ b : Set α) ≤ c from sup_le ha hb
    inf := (· ∩ ·)
    inf_le_left := fun a b => show (a ⊓ b : Set α) ≤ a from inf_le_left
    inf_le_right := fun a b => show (a ⊓ b : Set α) ≤ b from inf_le_right
    le_inf := fun a b c ha hb => show (a : Set α) ≤ b ⊓ c from le_inf ha hb
    le_sup_inf := fun x y z => show ((x ⊔ y) ⊓ (x ⊔ z) : Set α) ≤ x ⊔ y ⊓ z from le_sup_inf }

instance : BoundedOrder (Subtype (MeasurableSet : Set α → Prop))
    where
  top := ⊤
  le_top a := show (a : Set α) ≤ ⊤ from le_top
  bot := ⊥
  bot_le a := show (⊥ : Set α) ≤ a from bot_le

instance : BooleanAlgebra (Subtype (MeasurableSet : Set α → Prop)) :=
  { MeasurableSet.Subtype.boundedOrder,
    MeasurableSet.Subtype.distribLattice with
    sdiff := (· \ ·)
    compl := HasCompl.compl
    inf_compl_le_bot := fun a => BooleanAlgebra.inf_compl_le_bot (a : Set α)
    top_le_sup_compl := fun a => BooleanAlgebra.top_le_sup_compl (a : Set α)
    sdiff_eq := fun a b => Subtype.eq <| sdiff_eq }

@[measurability]
theorem measurableSet_blimsup {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.blimsup s Filter.atTop p :=
  by
  simp only [Filter.blimsup_eq_infᵢ_bsupᵢ_of_nat, supr_eq_Union, infi_eq_Inter]
  exact
    MeasurableSet.interᵢ fun n =>
      MeasurableSet.unionᵢ fun m => MeasurableSet.unionᵢ fun hm => h m hm.1
#align measurable_set.measurable_set_blimsup MeasurableSet.measurableSet_blimsup

@[measurability]
theorem measurableSet_bliminf {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.bliminf s Filter.atTop p :=
  by
  simp only [Filter.bliminf_eq_supᵢ_binfᵢ_of_nat, infi_eq_Inter, supr_eq_Union]
  exact
    MeasurableSet.unionᵢ fun n =>
      MeasurableSet.interᵢ fun m => MeasurableSet.interᵢ fun hm => h m hm.1
#align measurable_set.measurable_set_bliminf MeasurableSet.measurableSet_bliminf

@[measurability]
theorem measurableSet_limsup {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.limsup s Filter.atTop :=
  by
  convert measurable_set_blimsup (fun n h => hs n : ∀ n, True → MeasurableSet (s n))
  simp
#align measurable_set.measurable_set_limsup MeasurableSet.measurableSet_limsup

@[measurability]
theorem measurableSet_liminf {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.liminf s Filter.atTop :=
  by
  convert measurable_set_bliminf (fun n h => hs n : ∀ n, True → MeasurableSet (s n))
  simp
#align measurable_set.measurable_set_liminf MeasurableSet.measurableSet_liminf

end MeasurableSet

