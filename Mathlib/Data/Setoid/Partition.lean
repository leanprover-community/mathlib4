/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot, Wen Yang, Johan Commelin
-/

import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Partition.Finpartition

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : Set (Set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `IsPartition c`
* An indexed partition is a map `s : ι → α` whose image is a partition. This is
  expressed as `IndexedPartition s`.

Of course both implementations are related to `Quotient` and `Setoid`.

`Setoid.isPartition.partition` and `Finpartition.isPartition_parts` furnish
a link between `Setoid.IsPartition` and `Finpartition`.

## TODO

Could the design of `Finpartition` inform the one of `Setoid.IsPartition`? Maybe bundling it and
changing it from `Set (Set α)` to `Set α` where `[Lattice α] [OrderBot α]` would make it more
usable.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/


namespace Setoid

variable {α : Type*}

/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x b b'}
    (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩

/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mkClasses (c : Set (Set α)) (H : ∀ a, ∃! b ∈ c, a ∈ b) : Setoid α where
  r x y := ∀ s ∈ c, x ∈ s → y ∈ s
  iseqv.refl := fun _ _ _ hx => hx
  iseqv.symm := fun {x _y} h s hs hy => by
    obtain ⟨t, ⟨ht, hx⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy ht (h t ht hx)]
  iseqv.trans := fun {_x _ _} h1 h2 s hs hx => h2 s hs (h1 s hs hx)

/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : Setoid α) : Set (Set α) :=
  { s | ∃ y, s = { x | r x y } }

theorem mem_classes (r : Setoid α) (y) : { x | r x y } ∈ r.classes :=
  ⟨y, rfl⟩

theorem classes_ker_subset_fiber_set {β : Type*} (f : α → β) :
    (Setoid.ker f).classes ⊆ Set.range fun y => { x | f x = y } := by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩

theorem finite_classes_ker {α β : Type*} [Finite β] (f : α → β) : (Setoid.ker f).classes.Finite :=
  (Set.finite_range _).subset <| classes_ker_subset_fiber_set f

theorem card_classes_ker_le {α β : Type*} [Fintype β] (f : α → β)
    [Fintype (Setoid.ker f).classes] : Fintype.card (Setoid.ker f).classes ≤ Fintype.card β := by
  classical exact
      le_trans (Set.card_le_card (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
theorem eq_iff_classes_eq {r₁ r₂ : Setoid α} :
    r₁ = r₂ ↔ ∀ x, { y | r₁ x y } = { y | r₂ x y } :=
  ⟨fun h _x => h ▸ rfl, fun h => ext fun x => Set.ext_iff.1 <| h x⟩

theorem rel_iff_exists_classes (r : Setoid α) {x y} : r x y ↔ ∃ c ∈ r.classes, x ∈ c ∧ y ∈ c :=
  ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ => by
    subst c
    exact r.trans' hx (r.symm' hy)⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
theorem classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classes = r₂.classes :=
  ⟨fun h => h ▸ rfl, fun h => ext fun a b => by simp only [rel_iff_exists_classes, h]⟩

/-- The empty set is not an equivalence class. -/
theorem empty_notMem_classes {r : Setoid α} : ∅ ∉ r.classes := fun ⟨y, hy⟩ =>
  Set.notMem_empty y <| hy.symm ▸ r.refl' y

@[deprecated (since := "2025-05-23")] alias empty_not_mem_classes := empty_notMem_classes

/-- Equivalence classes partition the type. -/
theorem classes_eqv_classes {r : Setoid α} (a) : ∃! b ∈ r.classes, a ∈ b :=
  ExistsUnique.intro { x | r x a } ⟨r.mem_classes a, r.refl' _⟩ <| by
    rintro y ⟨⟨_, rfl⟩, ha⟩
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
theorem eq_of_mem_classes {r : Setoid α} {x b} (hc : b ∈ r.classes) (hb : x ∈ b) {b'}
    (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
equivalence relation defined by the set of sets. -/
theorem eq_eqv_class_of_mem {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {s y}
    (hs : s ∈ c) (hy : y ∈ s) : s = { x | mkClasses c H x y } := by
  ext x
  constructor
  · intro hx _s' hs' hx'
    rwa [eq_of_mem_eqv_class H hs' hx' hs hx]
  · intro hx
    obtain ⟨b', ⟨hc, hb'⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy hc (hx b' hc hb')]

/-- The equivalence classes of the equivalence relation defined by a set of sets
partitioning α are elements of the set of sets. -/
theorem eqv_class_mem {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {y} :
    { x | mkClasses c H x y } ∈ c :=
  (H y).elim fun _ hc _ => eq_eqv_class_of_mem H hc.1 hc.2 ▸ hc.1

theorem eqv_class_mem' {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x} :
    { y : α | mkClasses c H x y } ∈ c := by
  convert @Setoid.eqv_class_mem _ _ H x using 3
  rw [Setoid.comm']

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
theorem eqv_classes_disjoint {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) :
    c.PairwiseDisjoint id := fun _b₁ h₁ _b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
    (H x).elim fun _b _hc _hx => h <| eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/-- A set of disjoint sets covering α partition α (classical). -/
theorem eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) (a) : ∃! b ∈ c, a ∈ b :=
  let ⟨b, hc, ha⟩ := Set.mem_sUnion.1 <| show a ∈ _ by rw [hu]; exact Set.mem_univ a
  ExistsUnique.intro b ⟨hc, ha⟩ fun _ hc' => H.elim_set hc'.1 hc _ hc'.2 ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoidOfDisjointUnion {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) : Setoid α :=
  Setoid.mkClasses c <| eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence relation `r`
equals `r`. -/
theorem mkClasses_classes (r : Setoid α) : mkClasses r.classes classes_eqv_classes = r :=
  ext fun x _y =>
    ⟨fun h => r.symm' (h { z | r z x } (r.mem_classes x) <| r.refl' x), fun h _b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp]
theorem sUnion_classes (r : Setoid α) : ⋃₀ r.classes = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨{ y | r y x }, ⟨x, rfl⟩, Setoid.refl _⟩

/-- The equivalence between the quotient by an equivalence relation and its
type of equivalence classes. -/
noncomputable def quotientEquivClasses (r : Setoid α) : Quotient r ≃ Setoid.classes r := by
  let f (a : α) : Setoid.classes r := ⟨{ x | r x a }, Setoid.mem_classes r a⟩
  have f_respects_relation (a b : α) (a_rel_b : r a b) : f a = f b := by
    rw [Subtype.mk.injEq]
    exact Setoid.eq_of_mem_classes (Setoid.mem_classes r a) (Setoid.symm a_rel_b)
        (Setoid.mem_classes r b) (Setoid.refl b)
  apply Equiv.ofBijective (Quot.lift f f_respects_relation)
  constructor
  · intro (q_a : Quotient r) (q_b : Quotient r) h_eq
    induction q_a using Quotient.ind with | _ a
    induction q_b using Quotient.ind with | _ b
    simp only [f, Quotient.lift_mk, Subtype.ext_iff] at h_eq
    apply Quotient.sound
    change a ∈ { x | r x b }
    rw [← h_eq]
    exact Setoid.refl a
  · rw [Quot.surjective_lift]
    intro ⟨c, a, hc⟩
    exact ⟨a, Subtype.ext hc.symm⟩

@[simp]
lemma quotientEquivClasses_mk_eq (r : Setoid α) (a : α) :
    (quotientEquivClasses r (Quotient.mk r a) : Set α) = { x | r x a } :=
  (@Subtype.ext_iff _ _ _ ⟨{ x | r x a }, Setoid.mem_classes r a⟩).mp rfl

section Partition

/-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b

/-- A partition of `α` does not contain the empty set. -/
theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : s ∈ c) :
    s.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 <| hs0 ▸ h

theorem isPartition_classes (r : Setoid α) : IsPartition r.classes :=
  ⟨empty_notMem_classes, classes_eqv_classes⟩

theorem IsPartition.pairwiseDisjoint {c : Set (Set α)} (hc : IsPartition c) :
    c.PairwiseDisjoint id :=
  eqv_classes_disjoint hc.2

lemma _root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty {α : Type*} {s : Set (Set α)}
    (h₁ : s.PairwiseDisjoint id) (h₂ : ∀ a : α, ∃ x ∈ s, a ∈ x) (h₃ : ∅ ∉ s) :
    Setoid.IsPartition s := by
  refine ⟨h₃, fun a ↦ existsUnique_of_exists_of_unique (h₂ a) ?_⟩
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩

theorem IsPartition.sUnion_eq_univ {c : Set (Set α)} (hc : IsPartition c) : ⋃₀ c = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Set.mem_sUnion.2 <|
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only at ht
        tauto⟩

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
theorem exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s ∈ c) :
    ∃ y, s = { x | mkClasses c hc.2 x y } :=
  let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
the original partition. -/
theorem classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) :
    (mkClasses c hc.2).classes = c := by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨b, ⟨hb, hy⟩, _⟩ := hc.2 y
    rwa [← eq_eqv_class_of_mem _ hb hy]
  · exact exists_of_mem_partition hc

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance Partition.le : LE (Subtype (@IsPartition α)) :=
  ⟨fun x y => mkClasses x.1 x.2.2 ≤ mkClasses y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
equivalence relations. -/
instance Partition.partialOrder : PartialOrder (Subtype (@IsPartition α)) where
  le := (· ≤ ·)
  lt x y := x ≤ y ∧ ¬y ≤ x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Subtype.ext_iff, ← classes_mkClasses x.1 x.2, ← classes_mkClasses y.1 y.2, h]

variable (α) in
/-- The order-preserving bijection between equivalence relations on a type `α`, and
partitions of `α` into subsets. -/
protected def Partition.orderIso : Setoid α ≃o { C : Set (Set α) // IsPartition C } where
  toFun r := ⟨r.classes, empty_notMem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by rw [Subtype.ext_iff, ← classes_mkClasses C.1 C.2]
  map_rel_iff' {r s} := by
    conv_rhs => rw [← mkClasses_classes r, ← mkClasses_classes s]
    rfl

/-- A complete lattice instance for partitions; there is more infrastructure for the
equivalent complete lattice on equivalence relations. -/
instance Partition.completeLattice : CompleteLattice (Subtype (@IsPartition α)) :=
  GaloisInsertion.liftCompleteLattice <|
    @OrderIso.toGaloisInsertion _ (Subtype (@IsPartition α)) _ (PartialOrder.toPreorder) <|
      Partition.orderIso α

end Partition

/-- A finite setoid partition furnishes a finpartition -/
@[simps]
def IsPartition.finpartition {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α))) :
    Finpartition (Set.univ : Set α) where
  parts := c
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr <| eqv_classes_disjoint hc.2
  sup_parts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
  bot_notMem := hc.left

end Setoid

/-- A finpartition gives rise to a setoid partition -/
theorem Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
    Setoid.IsPartition (f.parts : Set (Set α)) :=
  ⟨f.bot_notMem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.sup_parts)
      f.supIndep.pairwiseDisjoint⟩

/-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
`s : ι → Set α`.

`IndexedPartition.index` sends an element to its index, while `IndexedPartition.some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not needed, then
`Setoid.ker index` by itself may be sufficient. -/
structure IndexedPartition {ι α : Type*} (s : ι → Set α) where
  /-- two indexes are equal if they are equal in membership -/
  eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j
  /-- sends an index to an element of the corresponding set -/
  some : ι → α
  /-- membership invariance for `some` -/
  some_mem : ∀ i, some i ∈ s i
  /-- index for type `α` -/
  index : α → ι
  /-- membership invariance for `index` -/
  mem_index : ∀ x, x ∈ s (index x)

open scoped Function -- required for scoped `on` notation

/-- The non-constructive constructor for `IndexedPartition`. -/
noncomputable def IndexedPartition.mk' {ι α : Type*} (s : ι → Set α)
    (dis : Pairwise (Disjoint on s)) (nonempty : ∀ i, (s i).Nonempty)
    (ex : ∀ x, ∃ i, x ∈ s i) : IndexedPartition s where
  eq_of_mem {_x _i _j} hxi hxj := by_contradiction fun h => (dis h).le_bot ⟨hxi, hxj⟩
  some i := (nonempty i).some
  some_mem i := (nonempty i).choose_spec
  index x := (ex x).choose
  mem_index x := (ex x).choose_spec

namespace IndexedPartition

open Set

variable {ι α : Type*} {s : ι → Set α}

/-- On a unique index set there is the obvious trivial partition -/
instance [Unique ι] [Inhabited α] : Inhabited (IndexedPartition fun _i : ι => (Set.univ : Set α)) :=
  ⟨{  eq_of_mem := fun {_x _i _j} _hi _hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

attribute [simp] some_mem

variable (hs : IndexedPartition s)

include hs in
theorem exists_mem (x : α) : ∃ i, x ∈ s i :=
  ⟨hs.index x, hs.mem_index x⟩

include hs in
theorem iUnion : ⋃ i, s i = univ := by
  ext x
  simp [hs.exists_mem x]

include hs in
theorem disjoint : Pairwise (Disjoint on s) := fun {_i _j} h =>
  disjoint_left.mpr fun {_x} hxi hxj => h (hs.eq_of_mem hxi hxj)

theorem mem_iff_index_eq {x i} : x ∈ s i ↔ hs.index x = i :=
  ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩

theorem eq (i) : s i = { x | hs.index x = i } :=
  Set.ext fun _ => hs.mem_iff_index_eq

/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
protected abbrev setoid (hs : IndexedPartition s) : Setoid α :=
  Setoid.ker hs.index

@[simp]
theorem index_some (i : ι) : hs.index (hs.some i) = i :=
  (mem_iff_index_eq _).1 <| hs.some_mem i

theorem some_index (x : α) : hs.setoid (hs.some (hs.index x)) x :=
  hs.index_some (hs.index x)

/-- The quotient associated to an indexed partition. -/
protected def Quotient :=
  Quotient hs.setoid

/-- The projection onto the quotient associated to an indexed partition. -/
def proj : α → hs.Quotient :=
  Quotient.mk''

instance [Inhabited α] : Inhabited hs.Quotient :=
  ⟨hs.proj default⟩

theorem proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
  Quotient.eq''

@[simp]
theorem proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
  Quotient.eq''.2 (hs.some_index x)

/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
def equivQuotient : ι ≃ hs.Quotient :=
  (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm

@[simp]
theorem equivQuotient_index_apply (x : α) : hs.equivQuotient (hs.index x) = hs.proj x :=
  hs.proj_eq_iff.mpr (some_index hs x)

@[simp]
theorem equivQuotient_symm_proj_apply (x : α) : hs.equivQuotient.symm (hs.proj x) = hs.index x :=
  rfl

theorem equivQuotient_index : hs.equivQuotient ∘ hs.index = hs.proj :=
  funext hs.equivQuotient_index_apply

/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. This is a computable version of `Quotient.out` using `IndexedPartition.some`. -/
def out : hs.Quotient ↪ α :=
  hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

/-- This lemma is analogous to `Quotient.mk_out'`. -/
@[simp]
theorem out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
  rfl

/-- The indices of `Quotient.out` and `IndexedPartition.out` are equal. -/
theorem index_out (x : hs.Quotient) : hs.index x.out = hs.index (hs.out x) :=
  Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out x).trans (hs.index_some _).symm

/-- This lemma is analogous to `Quotient.out_eq'`. -/
@[simp]
theorem proj_out (x : hs.Quotient) : hs.proj (hs.out x) = x :=
  Quotient.inductionOn' x fun x => Quotient.sound' <| hs.some_index x

theorem class_of {x : α} : setOf (hs.setoid x) = s (hs.index x) :=
  Set.ext fun _y => eq_comm.trans hs.mem_iff_index_eq.symm

theorem proj_fiber (x : hs.Quotient) : hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x) :=
  Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hs.mem_iff_index_eq]
    exact Quotient.eq''

/-- Combine functions with disjoint domains into a new function.
You can use the regular expression `def.*piecewise` to search for
other ways to define piecewise functions in mathlib4. -/
def piecewise {β : Type*} (f : ι → α → β) : α → β := fun x => f (hs.index x) x

lemma piecewise_apply {β : Type*} {f : ι → α → β} (x : α) : hs.piecewise f x = f (hs.index x) x :=
  rfl

open Function

/-- A family of injective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form an injective function. -/
theorem piecewise_inj {β : Type*} {f : ι → α → β}
    (h_injOn : ∀ i, InjOn (f i) (s i))
    (h_disjoint : PairwiseDisjoint (univ : Set ι) fun i => (f i) '' (s i)) :
    Injective (piecewise hs f) := by
  intro x y h
  suffices hs.index x = hs.index y by
    apply h_injOn (hs.index x) (hs.mem_index x) (this ▸ hs.mem_index y)
    simpa only [piecewise_apply, this] using h
  apply h_disjoint.elim trivial trivial
  contrapose! h
  exact h.ne_of_mem (mem_image_of_mem _ (hs.mem_index x)) (mem_image_of_mem _ (hs.mem_index y))

/-- A family of bijective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form a bijective function. -/
theorem piecewise_bij {β : Type*} {f : ι → α → β}
    {t : ι → Set β} (ht : IndexedPartition t)
    (hf : ∀ i, BijOn (f i) (s i) (t i)) :
    Bijective (piecewise hs f) := by
  set g := piecewise hs f with hg
  have hg_bij : ∀ i, BijOn g (s i) (t i) := by
    intro i
    refine BijOn.congr (hf i) ?_
    intro x hx
    rw [hg, piecewise_apply, hs.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, s i) := by
    refine injOn_of_injective ?_
    refine piecewise_inj hs (fun i ↦ BijOn.injOn (hf i)) ?h_disjoint
    simp only [fun i ↦ BijOn.image_eq (hf i)]
    rintro i - j - hij
    exact ht.disjoint hij
  rw [bijective_iff_bijOn_univ, ← hs.iUnion, ← ht.iUnion]
  exact bijOn_iUnion hg_bij hg_inj

end IndexedPartition
