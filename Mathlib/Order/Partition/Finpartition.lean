/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.SupIndep
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : Finset α` which does not contain `⊥` and whose supremum is `a`.

Finpartitions of a finset are at the heart of Szemerédi's regularity lemma. They are also studied
purely order theoretically in Sperner theory.

## Constructions

We provide many ways to build finpartitions:
* `Finpartition.ofErase`: Builds a finpartition by erasing `⊥` for you.
* `Finpartition.ofSubset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `Finpartition.empty`: The empty finpartition of `⊥`.
* `Finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `Finpartition.discrete`: The discrete finpartition of `s : Finset α` made of singletons.
* `Finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `Finpartition.ofExistsUnique`: Builds a finpartition from a collection of parts such that each
  element is in exactly one part.
* `Finpartition.ofSetoid`: With `Fintype α`, constructs the finpartition of `univ : Finset α`
  induced by the equivalence classes of `s : Setoid α`.
* `Finpartition.atomise`: Makes a finpartition of `s : Finset α` by breaking `s` along all finsets
  in `F : Finset (Finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`Finpartition.indiscrete` and `Finpartition.bind` together form the monadic structure of
`Finpartition`.

## Implementation notes

Forbidding `⊥` as a part follows mathematical tradition and is a pragmatic choice concerning
operations on `Finpartition`. Not caring about `⊥` being a part or not breaks extensionality (it's
not because the parts of `P` and the parts of `Q` have the same elements that `P = Q`). Enforcing
`⊥` to be a part makes `Finpartition.bind` uglier and doesn't rid us of the need of
`Finpartition.ofErase`.

## TODO

The order is the wrong way around to make `Finpartition a` a graded order. Is it bad to depart from
the literature and turn the order around?

The specialisation to `Finset α` could be generalised to atomistic orders.
-/


open Finset Function

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext]
structure Finpartition [Lattice α] [OrderBot α] (a : α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset α
  /-- The partition is supremum-independent -/
  protected supIndep : parts.SupIndep id
  /-- The supremum of the partition is `a` -/
  sup_parts : parts.sup id = a
  /-- No element of the partition is bottom -/
  bot_notMem : ⊥ ∉ parts
  deriving DecidableEq

namespace Finpartition

section Lattice

variable [Lattice α] [OrderBot α]

@[deprecated (since := "2025-05-23")]
alias not_bot_mem := bot_notMem

/-- A `Finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps]
def ofErase [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupIndep id)
    (sup_parts : parts.sup id = a) : Finpartition a where
  parts := parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  sup_parts := (sup_erase_bot _).trans sup_parts
  bot_notMem := notMem_erase _ _

/-- A `Finpartition` constructor from a bigger existing finpartition. -/
@[simps]
def ofSubset {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts ⊆ P.parts)
    (sup_parts : parts.sup id = b) : Finpartition b :=
  { parts := parts
    supIndep := P.supIndep.subset subset
    sup_parts := sup_parts
    bot_notMem := fun h ↦ P.bot_notMem (subset h) }

/-- Changes the type of a finpartition to an equal one. -/
@[simps]
def copy {a b : α} (P : Finpartition a) (h : a = b) : Finpartition b where
  parts := P.parts
  supIndep := P.supIndep
  sup_parts := h ▸ P.sup_parts
  bot_notMem := P.bot_notMem

/-- Transfer a finpartition over an order isomorphism. -/
def map {β : Type*} [Lattice β] [OrderBot β] {a : α} (e : α ≃o β) (P : Finpartition a) :
    Finpartition (e a) where
  parts := P.parts.map e
  supIndep u hu _ hb hbu _ hx hxu := by
    rw [← map_symm_subset] at hu
    simp only [mem_map_equiv] at hb
    have := P.supIndep hu hb (by simp [hbu]) (map_rel e.symm hx) ?_
    · rw [← e.symm.map_bot] at this
      exact e.symm.map_rel_iff.mp this
    · convert e.symm.map_rel_iff.mpr hxu
      rw [map_finset_sup, sup_map]
      rfl
  sup_parts := by simp [← P.sup_parts]
  bot_notMem := by
    rw [mem_map_equiv]
    convert P.bot_notMem
    exact e.symm.map_bot

@[simp]
theorem parts_map {β : Type*} [Lattice β] [OrderBot β] {a : α} {e : α ≃o β} {P : Finpartition a} :
    (P.map e).parts = P.parts.map e := rfl

variable (α)

/-- The empty finpartition. -/
@[simps]
protected def empty : Finpartition (⊥ : α) where
  parts := ∅
  supIndep := supIndep_empty _
  sup_parts := Finset.sup_empty
  bot_notMem := notMem_empty ⊥

instance : Inhabited (Finpartition (⊥ : α)) :=
  ⟨Finpartition.empty α⟩

@[simp]
theorem default_eq_empty : (default : Finpartition (⊥ : α)) = Finpartition.empty α :=
  rfl

variable {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps]
def indiscrete (ha : a ≠ ⊥) : Finpartition a where
  parts := {a}
  supIndep := supIndep_singleton _ _
  sup_parts := Finset.sup_singleton
  bot_notMem h := ha (mem_singleton.1 h).symm

variable (P : Finpartition a)

protected theorem le {b : α} (hb : b ∈ P.parts) : b ≤ a :=
  (le_sup hb).trans P.sup_parts.le

theorem ne_bot {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ := by
  intro h
  refine P.bot_notMem (?_)
  rw [h] at hb
  exact hb

protected theorem disjoint : (P.parts : Set α).PairwiseDisjoint id :=
  P.supIndep.pairwiseDisjoint

variable {P}

@[simp]
theorem parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ := by
  simp_rw [← P.sup_parts]
  refine ⟨fun h ↦ ?_, fun h ↦ eq_empty_iff_forall_notMem.2 fun b hb ↦ P.bot_notMem ?_⟩
  · rw [h]
    exact Finset.sup_empty
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]

@[simp]
theorem parts_nonempty_iff : P.parts.Nonempty ↔ a ≠ ⊥ := by
  rw [nonempty_iff_ne_empty, not_iff_not, parts_eq_empty_iff]

theorem parts_nonempty (P : Finpartition a) (ha : a ≠ ⊥) : P.parts.Nonempty :=
  parts_nonempty_iff.2 ha

instance : Unique (Finpartition (⊥ : α)) :=
  { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P ↦ by
      ext a
      exact iff_of_false (fun h ↦ P.ne_bot h <| le_bot_iff.1 <| P.le h) (notMem_empty a) }

-- See note [reducible non-instances]
/-- There's a unique partition of an atom. -/
abbrev _root_.IsAtom.uniqueFinpartition (ha : IsAtom a) : Unique (Finpartition a) where
  default := indiscrete ha.1
  uniq P := by
    have h : ∀ b ∈ P.parts, b = a := fun _ hb ↦
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    refine Iff.trans ⟨h b, ?_⟩ mem_singleton.symm
    rintro rfl
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    simp_rw [← h c hc]
    exact hc

instance [Fintype α] [DecidableEq α] (a : α) : Fintype (Finpartition a) :=
  @Fintype.ofSurjective { p : Finset α // p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p } (Finpartition a) _
    (Subtype.fintype _) (fun i ↦ ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) fun ⟨_, y, z, w⟩ ↦
    ⟨⟨_, y, z, w⟩, rfl⟩

/-! ### Refinement order -/


section Order

/-- We say that `P ≤ Q` if `P` refines `Q`: each part of `P` is less than some part of `Q`. -/
instance : LE (Finpartition a) :=
  ⟨fun P Q ↦ ∀ ⦃b⦄, b ∈ P.parts → ∃ c ∈ Q.parts, b ≤ c⟩

instance : PartialOrder (Finpartition a) :=
  { (inferInstance : LE (Finpartition a)) with
    le_refl := fun _ b hb ↦ ⟨b, hb, le_rfl⟩
    le_trans := fun _ Q R hPQ hQR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hcd⟩ := hQR hc
      exact ⟨d, hd, hbc.trans hcd⟩
    le_antisymm := fun P Q hPQ hQP ↦ by
      ext b
      refine ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        obtain ⟨d, hd, hcd⟩ := hQP hc
        rwa [hbc.antisymm]
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        rwa [hbc.antisymm]
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }

instance [Decidable (a = ⊥)] : OrderTop (Finpartition a) where
  top := if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    · intro x hx
      simpa [h, P.ne_bot hx] using P.le hx
    · exact fun b hb ↦ ⟨a, mem_singleton_self _, P.le hb⟩

theorem parts_top_subset (a : α) [Decidable (a = ⊥)] : (⊤ : Finpartition a).parts ⊆ {a} := by
  intro b hb
  have hb : b ∈ Finpartition.parts (dite _ _ _) := hb
  split_ifs at hb
  · simp only [copy_parts, empty_parts, notMem_empty] at hb
  · exact hb

theorem parts_top_subsingleton (a : α) [Decidable (a = ⊥)] :
    ((⊤ : Finpartition a).parts : Set α).Subsingleton :=
  Set.subsingleton_of_subset_singleton fun _ hb ↦ mem_singleton.1 <| parts_top_subset _ hb

-- TODO: this instance takes double-exponential time to generate all partitions, find a faster way
instance [DecidableEq α] {s : Finset α} : Fintype (Finpartition s) where
  elems := s.powerset.powerset.image
    fun ps ↦ if h : ps.sup id = s ∧ ⊥ ∉ ps ∧ ps.SupIndep id then ⟨ps, h.2.2, h.1, h.2.1⟩ else ⊤
  complete P := by
    refine mem_image.mpr ⟨P.parts, ?_, ?_⟩
    · rw [mem_powerset]; intro p hp; rw [mem_powerset]; exact P.le hp
    · simp [P.supIndep, P.sup_parts, P.bot_notMem, -bot_eq_empty]

end Order

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α]

section Inf

variable [DecidableEq α] {a b c : α}

instance : Min (Finpartition a) :=
  ⟨fun P Q ↦
    ofErase ((P.parts ×ˢ Q.parts).image fun bc ↦ bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        simp only [mem_image, and_imp, forall_exists_index, id, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        · refine Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ ?_)
          intro t
          simp [t] at h
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
      (by
        rw [sup_image, id_comp, sup_product_left]
        trans P.parts.sup id ⊓ Q.parts.sup id
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          rfl
        · rw [P.sup_parts, Q.sup_parts, inf_idem])⟩

@[simp]
theorem parts_inf (P Q : Finpartition a) :
    (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).image fun bc : α × α ↦ bc.1 ⊓ bc.2).erase ⊥ :=
  rfl

instance : SemilatticeInf (Finpartition a) :=
  { min := Min.min
    inf_le_left := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.1, hc.1, inf_le_left⟩
    inf_le_right := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.2, hc.2, inf_le_right⟩
    le_inf := fun P Q R hPQ hPR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hbd⟩ := hPR hb
      have h := _root_.le_inf hbc hbd
      refine
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

end Inf

theorem exists_le_of_le {a b : α} {P Q : Finpartition a} (h : P ≤ Q) (hb : b ∈ Q.parts) :
    ∃ c ∈ P.parts, c ≤ b := by
  by_contra H
  refine Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) ?_)
  rw [← P.sup_parts, Finset.disjoint_sup_right]
  rintro c hc
  obtain ⟨d, hd, hcd⟩ := h hc
  refine (Q.disjoint hb hd ?_).mono_right hcd
  rintro rfl
  simp only [not_exists, not_and] at H
  exact H _ hc hcd

theorem card_mono {a : α} {P Q : Finpartition a} (h : P ≤ Q) : #Q.parts ≤ #P.parts := by
  classical
    have : ∀ b ∈ Q.parts, ∃ c ∈ P.parts, c ≤ b := fun b ↦ exists_le_of_le h
    choose f hP hf using this
    rw [← card_attach]
    refine card_le_card_of_injOn (fun b ↦ f _ b.2) (fun b _ ↦ hP _ b.2) fun b _ c _ h ↦ ?_
    exact
      Subtype.coe_injective
        (Q.disjoint.elim b.2 c.2 fun H ↦
          P.ne_bot (hP _ b.2) <| disjoint_self.1 <| H.mono (hf _ b.2) <| h.le.trans <| hf _ c.2)

variable [DecidableEq α] {a b c : α}

section Bind

variable {P : Finpartition a} {Q : ∀ i ∈ P.parts, Finpartition i}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps]
def bind (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : Finpartition a where
  parts := P.parts.attach.biUnion fun i ↦ (Q i.1 i.2).parts
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint]
    rintro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_biUnion] at ha hb
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb
    obtain rfl | hAB := eq_or_ne A B
    · exact (Q A hA).disjoint ha hb h
    · exact (P.disjoint hA hB hAB).mono ((Q A hA).le ha) ((Q B hB).le hb)
  sup_parts := by
    simp_rw [sup_biUnion]
    trans (sup P.parts id)
    · rw [eq_comm, ← Finset.sup_attach]
      exact sup_congr rfl fun b _hb ↦ (Q b.1 b.2).sup_parts.symm
    · exact P.sup_parts
  bot_notMem h := by
    rw [Finset.mem_biUnion] at h
    obtain ⟨⟨A, hA⟩, -, h⟩ := h
    exact (Q A hA).bot_notMem h

theorem mem_bind : b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts := by
  rw [bind, mem_biUnion]
  constructor
  · rintro ⟨⟨A, hA⟩, -, h⟩
    exact ⟨A, hA, h⟩
  · rintro ⟨A, hA, h⟩
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩

theorem card_bind (Q : ∀ i ∈ P.parts, Finpartition i) :
    #(P.bind Q).parts = ∑ A ∈ P.parts.attach, #(Q _ A.2).parts := by
  apply card_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun, Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne, Subtype.mk_eq_mk] at hbc
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
        (le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans <| (P.disjoint hb hc hbc).le_bot)

end Bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps]
def extend (P : Finpartition a) (hb : b ≠ ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c) :
    Finpartition c where
  parts := insert b P.parts
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_insert]
    exact P.disjoint.insert fun d hd _ ↦ hab.symm.mono_right <| P.le hd
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm]
  bot_notMem h := (mem_insert.1 h).elim hb.symm P.bot_notMem

theorem card_extend (P : Finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : Disjoint a b}
    {hc : a ⊔ b = c} : #(P.extend hb hab hc).parts = #P.parts + 1 :=
  card_insert_of_notMem fun h ↦ hb <| hab.symm.eq_bot_of_le <| P.le h

end DistribLattice

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableEq α] {a b c : α} (P : Finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
@[simps!]
def avoid (b : α) : Finpartition (a \ b) :=
  ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun _ ↦ sdiff_le).supIndep
    (by rw [sup_image, id_comp, Finset.sup_sdiff_right, ← Function.id_def, P.sup_parts])

@[simp]
theorem mem_avoid : c ∈ (P.avoid b).parts ↔ ∃ d ∈ P.parts, ¬d ≤ b ∧ d \ b = c := by
  simp only [avoid, ofErase, mem_erase, Ne, mem_image, ← exists_and_left,
    @and_left_comm (c ≠ ⊥)]
  refine exists_congr fun d ↦ and_congr_right' <| and_congr_left ?_
  rintro rfl
  rw [sdiff_eq_bot_iff]

end GeneralizedBooleanAlgebra

end Finpartition

/-! ### Finite partitions of finsets -/


namespace Finpartition

variable [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

lemma subset {a : Finset α} (ha : a ∈ P.parts) : a ⊆ s := P.le ha

theorem nonempty_of_mem_parts {a : Finset α} (ha : a ∈ P.parts) : a.Nonempty :=
  nonempty_iff_ne_empty.2 <| P.ne_bot ha

@[simp]
theorem empty_notMem_parts : ∅ ∉ P.parts := P.bot_notMem

@[deprecated (since := "2025-05-23")]
alias not_empty_mem_parts := empty_notMem_parts

theorem ne_empty (h : t ∈ P.parts) : t ≠ ∅ := P.ne_bot h

lemma eq_of_mem_parts (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hat : a ∈ t) (hau : a ∈ u) : t = u :=
  P.disjoint.elim ht hu <| not_disjoint_iff.2 ⟨a, hat, hau⟩

theorem exists_mem (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t := by
  simp_rw [← P.sup_parts] at ha
  exact mem_sup.1 ha

theorem biUnion_parts : P.parts.biUnion id = s :=
  (sup_eq_biUnion _ _).symm.trans P.sup_parts

theorem existsUnique_mem (ha : a ∈ s) : ∃! t, t ∈ P.parts ∧ a ∈ t := by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine ⟨t, ⟨ht, ht'⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  exact P.eq_of_mem_parts hu ht hu' ht'

/--
Construct a `Finpartition s` from a finset of finsets `parts` such that each element of `s` is in
exactly one member of `parts`. This provides a converse to `Finpartition.subset`,
`Finpartition.not_empty_mem_parts` and `Finpartition.existsUnique_mem`.
-/
@[simps]
def ofExistsUnique (parts : Finset (Finset α)) (h : ∀ p ∈ parts, p ⊆ s)
    (h' : ∀ a ∈ s, ∃! t ∈ parts, a ∈ t) (h'' : ∅ ∉ parts) :
    Finpartition s where
  parts := parts
  supIndep := by
    simp only [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    exact hab ((h' x (h _ ha hx)).unique ⟨ha, hx⟩ ⟨hb, hx'⟩)
  sup_parts := by
    ext i
    simp only [mem_sup, id_eq]
    constructor
    · rintro ⟨j, hj, hj'⟩
      exact h j hj hj'
    · rintro hi
      exact (h' i hi).exists
  bot_notMem := h''

/-- The part of the finpartition that `a` lies in. -/
def part (a : α) : Finset α := if ha : a ∈ s then choose (hp := P.existsUnique_mem ha) else ∅

@[simp]
lemma part_mem : P.part a ∈ P.parts ↔ a ∈ s := by
  by_cases ha : a ∈ s <;> simp [part, ha, choose_mem]

@[simp]
lemma part_eq_empty : P.part a = ∅ ↔ a ∉ s :=
  ⟨fun h has ↦ P.ne_empty (P.part_mem.2 has) h, fun h ↦ by simp [part, h]⟩

@[simp]
lemma part_nonempty : (P.part a).Nonempty ↔ a ∈ s := by
  simpa only [nonempty_iff_ne_empty] using P.part_eq_empty.not_left

@[simp]
lemma part_subset (a : α) : P.part a ⊆ s := by
  by_cases ha : a ∈ s
  · exact P.le <| P.part_mem.2 ha
  · simp [P.part_eq_empty.2 ha]

@[simp]
lemma mem_part_self : a ∈ P.part a ↔ a ∈ s := by
  by_cases ha : a ∈ s
  · simp [part, ha, choose_property (p := fun s => a ∈ s) P.parts (P.existsUnique_mem ha)]
  · simp [P.part_eq_empty.2, ha]

alias ⟨_, mem_part⟩ := mem_part_self

lemma part_eq_iff_mem (ht : t ∈ P.parts) : P.part a = t ↔ a ∈ t := by
  constructor
  · rintro rfl
    simp_all
  · intro hat
    apply P.eq_of_mem_parts (a := a) <;> simp [*, P.le ht hat]

lemma part_eq_of_mem (ht : t ∈ P.parts) (hat : a ∈ t) : P.part a = t :=
  (P.part_eq_iff_mem ht).2 hat

lemma mem_part_iff_part_eq_part {b : α} (ha : a ∈ s) (hb : b ∈ s) :
    a ∈ P.part b ↔ P.part a = P.part b :=
  ⟨fun c ↦ (P.part_eq_of_mem (P.part_mem.2 hb) c), fun c ↦ c ▸ P.mem_part ha⟩

theorem part_surjOn : Set.SurjOn P.part s P.parts := fun p hp ↦ by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
  have hx' := mem_of_subset (P.le hp) hx
  use x, hx', (P.existsUnique_mem hx').unique ⟨P.part_mem.2 hx', P.mem_part hx'⟩ ⟨hp, hx⟩

theorem exists_subset_part_bijOn : ∃ r ⊆ s, Set.BijOn P.part r P.parts := by
  obtain ⟨r, hrs, hr⟩ := P.part_surjOn.exists_bijOn_subset
  lift r to Finset α using s.finite_toSet.subset hrs
  exact ⟨r, mod_cast hrs, hr⟩

theorem mem_part_iff_exists {b} : a ∈ P.part b ↔ ∃ p ∈ P.parts, a ∈ p ∧ b ∈ p := by
  constructor
  · intro h
    have : b ∈ s := P.part_nonempty.1 ⟨a, h⟩
    refine ⟨_, ?_, h, ?_⟩ <;> simp [this]
  · rintro ⟨p, hp, hap, hbp⟩
    obtain rfl : P.part b = p := P.part_eq_of_mem hp hbp
    exact hap

/-- Equivalence between a finpartition's parts as a dependent sum and the partitioned set. -/
def equivSigmaParts : s ≃ Σ t : P.parts, t.1 where
  toFun x := ⟨⟨P.part x.1, P.part_mem.2 x.2⟩, ⟨x, P.mem_part x.2⟩⟩
  invFun x := ⟨x.2, mem_of_subset (P.le x.1.2) x.2.2⟩
  left_inv x := by simp
  right_inv x := by
    ext e
    · obtain ⟨⟨p, mp⟩, ⟨f, mf⟩⟩ := x
      dsimp only at mf ⊢
      rw [P.part_eq_of_mem mp mf]
    · simp

lemma exists_enumeration : ∃ f : s ≃ Σ t : P.parts, Fin #t.1,
    ∀ a b : s, P.part a = P.part b ↔ (f a).1 = (f b).1 := by
  use P.equivSigmaParts.trans ((Equiv.refl _).sigmaCongr (fun t ↦ t.1.equivFin))
  simp [equivSigmaParts, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]

theorem sum_card_parts : ∑ i ∈ P.parts, #i = #s := by
  convert congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  rfl

/-- `⊥` is the partition in singletons, aka discrete partition. -/
instance (s : Finset α) : Bot (Finpartition s) :=
  ⟨{  parts := s.map ⟨singleton, singleton_injective⟩
      supIndep := Set.PairwiseDisjoint.supIndep <| by
        rw [Finset.coe_map]
        exact Finset.pairwiseDisjoint_range_singleton.subset (Set.image_subset_range _ _)
      sup_parts := by rw [sup_map, id_comp, Embedding.coeFn_mk, Finset.sup_singleton_eq_self]
      bot_notMem := by simp }⟩

@[simp]
theorem parts_bot (s : Finset α) :
    (⊥ : Finpartition s).parts = s.map ⟨singleton, singleton_injective⟩ :=
  rfl

theorem card_bot (s : Finset α) : #(⊥ : Finpartition s).parts = #s := Finset.card_map _

theorem mem_bot_iff : t ∈ (⊥ : Finpartition s).parts ↔ ∃ a ∈ s, {a} = t :=
  mem_map

instance (s : Finset α) : OrderBot (Finpartition s) :=
  { (inferInstance : Bot (Finpartition s)) with
    bot_le := fun P t ht ↦ by
      rw [mem_bot_iff] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨t, ht, hat⟩ := P.exists_mem ha
      exact ⟨t, ht, singleton_subset_iff.2 hat⟩ }

theorem card_parts_le_card : #P.parts ≤ #s := by
  rw [← card_bot s]
  exact card_mono bot_le

lemma card_mod_card_parts_le : #s % #P.parts ≤ #P.parts := by
  obtain h | h := (#P.parts).eq_zero_or_pos
  · rw [h]
    rw [Finset.card_eq_zero, parts_eq_empty_iff, bot_eq_empty, ← Finset.card_eq_zero] at h
    rw [h]
  · exact (Nat.mod_lt _ h).le

section SetSetoid

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps -isSimp]
def ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartition x where
  parts := x.image fun a ↦ {b ∈ x | s.r a b}
  supIndep := by
    suffices ∀ (a b c d : α), s a d → s b d → (s a c ↔ s b c) by
      simp only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise, coe_image,
        Set.mem_image, mem_coe, ne_eq, onFun, id_eq, disjoint_iff_ne, forall_mem_not_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, filter_inj',
        not_forall, @not_imp_comm (_ ↔ _), Decidable.not_not]
      intro _ _ _ _ _ _ _ _ ha _ hb
      exact ⟨(s.trans' hb <| s.trans' (s.symm' ha) ·), (s.trans' ha <| s.trans' (s.symm' hb) ·)⟩
    simp +contextual [← Quotient.eq]
  sup_parts := by
    ext a
    simp_rw [sup_image, id_comp, mem_sup, mem_filter]
    refine ⟨(·.choose_spec.2.1), fun _ ↦ by use a⟩
  bot_notMem := by
    suffices ∀ x₁ ∈ x, ∃ x₂ ∈ x, s x₁ x₂ by simpa [filter_eq_empty_iff]
    intro x _
    use x

theorem mem_part_ofSetSetoid_iff_rel {s : Setoid α} (x : Finset α) [DecidableRel s.r] {b : α} :
    b ∈ (ofSetSetoid s x).part a ↔ a ∈ x ∧ b ∈ x ∧ s a b := by
  suffices (∃ a₁ ∈ x, (b ∈ x ∧ s a₁ b) ∧ a ∈ x ∧ s a₁ a) ↔ a ∈ x ∧ b ∈ x ∧ s a b by
    simpa [mem_part_iff_exists, ofSetSetoid_parts]
  exact ⟨
    fun ⟨c, _, ⟨hb, hcb⟩, ⟨ha, hca⟩⟩ ↦ ⟨ha, hb, s.trans' (s.symm' hca) hcb⟩,
    fun h ↦ ⟨a, ⟨h.1, ⟨⟨h.2.1, h.2.2⟩, ⟨h.1, s.refl _⟩⟩⟩⟩
  ⟩

end SetSetoid

section Setoid

variable [Fintype α]

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps! -isSimp]
def ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α) :=
  ofSetSetoid s univ

theorem mem_part_ofSetoid_iff_rel {s : Setoid α} [DecidableRel s.r] {b : α} :
    b ∈ (ofSetoid s).part a ↔ s a b := by
  suffices b ∈ (ofSetSetoid s univ).part a ↔ a ∈ univ ∧ b ∈ univ ∧ s a b by simpa
  exact mem_part_ofSetSetoid_iff_rel univ

end Setoid

section Atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : Finset α) (F : Finset (Finset α)) : Finpartition s :=
  ofErase (F.powerset.image fun Q ↦ {i ∈ s | ∀ t ∈ F, t ∈ Q ↔ i ∈ t})
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h ↦
      disjoint_left.mpr fun z hz1 hz2 ↦
        h (by
            rw [mem_coe, mem_image] at hx hy
            obtain ⟨Q, hQ, rfl⟩ := hx
            obtain ⟨R, hR, rfl⟩ := hy
            suffices h' : Q = R by
              subst h'
              exact of_eq_true (eq_self {i ∈ s | ∀ t ∈ F, t ∈ Q ↔ i ∈ t})
            rw [id, mem_filter] at hz1 hz2
            rw [mem_powerset] at hQ hR
            ext i
            refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
    (by
      refine (Finset.sup_le fun t ht ↦ ?_).antisymm fun a ha ↦ ?_
      · rw [mem_image] at ht
        obtain ⟨A, _, rfl⟩ := ht
        exact s.filter_subset _
      · rw [mem_sup]
        refine
          ⟨{i ∈ s | ∀ t ∈ F, t ∈ {u ∈ F | a ∈ u} ↔ i ∈ t},
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht ↦ ?_⟩⟩
        rw [mem_filter]
        exact and_iff_right ht)

variable {F : Finset (Finset α)}

theorem mem_atomise :
    t ∈ (atomise s F).parts ↔
      t.Nonempty ∧ ∃ Q ⊆ F, {i ∈ s | ∀ u ∈ F, u ∈ Q ↔ i ∈ u} = t := by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_powerset]

theorem atomise_empty (hs : s.Nonempty) : (atomise s ∅).parts = {s} := by
  simp only [atomise, powerset_empty, image_singleton, notMem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_true]
  exact erase_eq_of_notMem (notMem_singleton.2 hs.ne_empty.symm)

theorem card_atomise_le : #(atomise s F).parts ≤ 2 ^ #F :=
  (card_le_card <| erase_subset _ _).trans <| Finset.card_image_le.trans (card_powerset _).le

theorem biUnion_filter_atomise (ht : t ∈ F) (hts : t ⊆ s) :
    {u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty}.biUnion id = t := by
  ext a
  refine mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ ↦ (mem_filter.1 hu).2.1 ha, fun ha ↦ ?_⟩
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  refine ⟨u, mem_filter.2 ⟨hu, fun b hb ↦ ?_, _, hau⟩, hau⟩
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  rw [mem_filter] at hau hb
  rwa [← hb.2 _ ht, hau.2 _ ht]

theorem card_filter_atomise_le_two_pow (ht : t ∈ F) :
    #{u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty} ≤ 2 ^ (#F - 1) := by
  suffices h :
    {u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty} ⊆
      (F.erase t).powerset.image fun P ↦ {i ∈ s | ∀ x ∈ F, x ∈ insert t P ↔ i ∈ x} by
    refine (card_le_card h).trans (card_image_le.trans ?_)
    rw [card_powerset, card_erase_of_mem ht]
  rw [subset_iff]
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp, and_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  refine ⟨P.erase t, erase_subset_erase _ PQ, ?_⟩
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]

end Atomise

end Finpartition
