/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.SupIndep

#align_import order.partition.finpartition from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

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

Link `Finpartition` and `Setoid.isPartition`.

The order is the wrong way around to make `Finpartition a` a graded order. Is it bad to depart from
the literature and turn the order around?
-/


open BigOperators Finset Function

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext]
structure Finpartition [Lattice α] [OrderBot α] (a : α) where
  -- porting note: Docstrings added
  /-- The elements of the finite partition of `a` -/
  parts : Finset α
  /-- The partition is supremum-independent -/
  supIndep : parts.SupIndep id
  /-- The supremum of the partition is `a` -/
  supParts : parts.sup id = a
  /-- No element of the partition is bottom-/
  not_bot_mem : ⊥ ∉ parts
  deriving DecidableEq
#align finpartition Finpartition
#align finpartition.parts Finpartition.parts
#align finpartition.sup_indep Finpartition.supIndep
#align finpartition.sup_parts Finpartition.supParts
#align finpartition.not_bot_mem Finpartition.not_bot_mem

-- Porting note: attribute [protected] doesn't work
-- attribute [protected] Finpartition.supIndep

namespace Finpartition

section Lattice

variable [Lattice α] [OrderBot α]

/-- A `Finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps]
def ofErase [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupIndep id)
    (sup_parts : parts.sup id = a) : Finpartition a
    where
  parts := parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  supParts := (sup_erase_bot _).trans sup_parts
  not_bot_mem := not_mem_erase _ _
#align finpartition.of_erase Finpartition.ofErase

/-- A `Finpartition` constructor from a bigger existing finpartition. -/
@[simps]
def ofSubset {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts ⊆ P.parts)
    (sup_parts : parts.sup id = b) : Finpartition b :=
  { parts :=parts
    supIndep := P.supIndep.subset subset
    supParts := sup_parts
    not_bot_mem := fun h ↦ P.not_bot_mem (subset h) }
#align finpartition.of_subset Finpartition.ofSubset

/-- Changes the type of a finpartition to an equal one. -/
@[simps]
def copy {a b : α} (P : Finpartition a) (h : a = b) : Finpartition b
    where
  parts := P.parts
  supIndep := P.supIndep
  supParts := h ▸ P.supParts
  not_bot_mem := P.not_bot_mem
#align finpartition.copy Finpartition.copy

variable (α)

/-- The empty finpartition. -/
@[simps]
protected def empty : Finpartition (⊥ : α)
    where
  parts := ∅
  supIndep := supIndep_empty _
  supParts := Finset.sup_empty
  not_bot_mem := not_mem_empty ⊥
#align finpartition.empty Finpartition.empty

instance : Inhabited (Finpartition (⊥ : α)) :=
  ⟨Finpartition.empty α⟩

@[simp]
theorem default_eq_empty : (default : Finpartition (⊥ : α)) = Finpartition.empty α :=
  rfl
#align finpartition.default_eq_empty Finpartition.default_eq_empty

variable {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps]
def indiscrete (ha : a ≠ ⊥) : Finpartition a
    where
  parts := {a}
  supIndep := supIndep_singleton _ _
  supParts := Finset.sup_singleton
  not_bot_mem h := ha (mem_singleton.1 h).symm
#align finpartition.indiscrete Finpartition.indiscrete

variable (P : Finpartition a)

protected theorem le {b : α} (hb : b ∈ P.parts) : b ≤ a :=
  (le_sup hb).trans P.supParts.le
#align finpartition.le Finpartition.le

theorem ne_bot {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ := by
  intro h
  -- ⊢ False
  refine' P.not_bot_mem (_)
  -- ⊢ ⊥ ∈ P.parts
  rw [h] at hb
  -- ⊢ ⊥ ∈ P.parts
  exact hb
  -- 🎉 no goals
#align finpartition.ne_bot Finpartition.ne_bot

protected theorem disjoint : (P.parts : Set α).PairwiseDisjoint id :=
  P.supIndep.pairwiseDisjoint
#align finpartition.disjoint Finpartition.disjoint

variable {P}

theorem parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ := by
  simp_rw [← P.supParts]
  -- ⊢ P.parts = ∅ ↔ sup P.parts id = ⊥
  refine' ⟨fun h ↦ _, fun h ↦ eq_empty_iff_forall_not_mem.2 fun b hb ↦ P.not_bot_mem _⟩
  -- ⊢ sup P.parts id = ⊥
  · rw [h]
    -- ⊢ sup ∅ id = ⊥
    exact Finset.sup_empty
    -- 🎉 no goals
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]
    -- 🎉 no goals
#align finpartition.parts_eq_empty_iff Finpartition.parts_eq_empty_iff

theorem parts_nonempty_iff : P.parts.Nonempty ↔ a ≠ ⊥ := by
  rw [nonempty_iff_ne_empty, not_iff_not, parts_eq_empty_iff]
  -- 🎉 no goals
#align finpartition.parts_nonempty_iff Finpartition.parts_nonempty_iff

theorem parts_nonempty (P : Finpartition a) (ha : a ≠ ⊥) : P.parts.Nonempty :=
  parts_nonempty_iff.2 ha
#align finpartition.parts_nonempty Finpartition.parts_nonempty

instance : Unique (Finpartition (⊥ : α)) :=
  { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P ↦ by
      ext a
      -- ⊢ a ∈ P.parts ↔ a ∈ default.parts
      exact iff_of_false (fun h ↦ P.ne_bot h <| le_bot_iff.1 <| P.le h) (not_mem_empty a) }
      -- 🎉 no goals

-- See note [reducible non instances]
/-- There's a unique partition of an atom. -/
@[reducible]
def _root_.IsAtom.uniqueFinpartition (ha : IsAtom a) : Unique (Finpartition a)
    where
  default := indiscrete ha.1
  uniq P := by
    have h : ∀ b ∈ P.parts, b = a := fun _ hb ↦
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    -- ⊢ b ∈ P.parts ↔ b ∈ default.parts
    refine' Iff.trans ⟨h b, _⟩ mem_singleton.symm
    -- ⊢ b = a → b ∈ P.parts
    rintro rfl
    -- ⊢ b ∈ P.parts
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    -- ⊢ b ∈ P.parts
    simp_rw [← h c hc]
    -- ⊢ c ∈ P.parts
    exact hc
    -- 🎉 no goals
#align is_atom.unique_finpartition IsAtom.uniqueFinpartition

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
    le_refl := fun P b hb ↦ ⟨b, hb, le_rfl⟩
    le_trans := fun P Q R hPQ hQR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      -- ⊢ ∃ c, c ∈ R.parts ∧ b ≤ c
      obtain ⟨d, hd, hcd⟩ := hQR hc
      -- ⊢ ∃ c, c ∈ R.parts ∧ b ≤ c
      exact ⟨d, hd, hbc.trans hcd⟩
      -- 🎉 no goals
    le_antisymm := fun P Q hPQ hQP ↦ by
      ext b
      -- ⊢ b ∈ P.parts ↔ b ∈ Q.parts
      refine' ⟨fun hb ↦ _, fun hb ↦ _⟩
      -- ⊢ b ∈ Q.parts
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        -- ⊢ b ∈ Q.parts
        obtain ⟨d, hd, hcd⟩ := hQP hc
        -- ⊢ b ∈ Q.parts
        rwa [hbc.antisymm]
        -- ⊢ c ≤ b
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
        -- 🎉 no goals
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        -- ⊢ b ∈ P.parts
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        -- ⊢ b ∈ P.parts
        rwa [hbc.antisymm]
        -- ⊢ c ≤ b
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }
        -- 🎉 no goals

instance [Decidable (a = ⊥)] : OrderTop (Finpartition a)
    where
  top := if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    -- ⊢ P ≤ ⊤
    · intro x hx
      -- ⊢ ∃ c, c ∈ ⊤.parts ∧ x ≤ c
      simpa [h, P.ne_bot hx] using P.le hx
      -- 🎉 no goals
    · exact fun b hb ↦ ⟨a, mem_singleton_self _, P.le hb⟩
      -- 🎉 no goals

theorem parts_top_subset (a : α) [Decidable (a = ⊥)] : (⊤ : Finpartition a).parts ⊆ {a} := by
  intro b hb
  -- ⊢ b ∈ {a}
  have hb : b ∈ Finpartition.parts (dite _ _ _) := hb
  -- ⊢ b ∈ {a}
  split_ifs at hb
  -- ⊢ b ∈ {a}
  · simp only [copy_parts, empty_parts, not_mem_empty] at hb
    -- 🎉 no goals
  · exact hb
    -- 🎉 no goals
#align finpartition.parts_top_subset Finpartition.parts_top_subset

theorem parts_top_subsingleton (a : α) [Decidable (a = ⊥)] :
    ((⊤ : Finpartition a).parts : Set α).Subsingleton :=
  Set.subsingleton_of_subset_singleton fun _ hb ↦ mem_singleton.1 <| parts_top_subset _ hb
#align finpartition.parts_top_subsingleton Finpartition.parts_top_subsingleton

end Order

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α]

section Inf

variable [DecidableEq α] {a b c : α}

instance : Inf (Finpartition a) :=
  ⟨fun P Q ↦
    ofErase ((P.parts ×ˢ Q.parts).image fun bc ↦ bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        -- ⊢ ∀ (i : α), i ∈ image (fun bc => bc.fst ⊓ bc.snd) (P.parts ×ˢ Q.parts) → Disj …
        simp only [mem_image, and_imp, exists_prop, forall_exists_index, id.def, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne.def]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        -- ⊢ Disjoint (x₁ ⊓ y₁) (x₂ ⊓ y₂)
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        -- ⊢ Disjoint (x₁ ⊓ y₁) (x₁ ⊓ y₂)
        · refine' Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ _)
          -- ⊢ y₁ ≠ y₂
          intro t
          -- ⊢ False
          simp [t] at h
          -- 🎉 no goals
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
        -- 🎉 no goals
      (by
        rw [sup_image, comp.left_id, sup_product_left]
        -- ⊢ (sup P.parts fun i => sup Q.parts fun i' => (i, i').fst ⊓ (i, i').snd) = a
        trans P.parts.sup id ⊓ Q.parts.sup id
        -- ⊢ (sup P.parts fun i => sup Q.parts fun i' => (i, i').fst ⊓ (i, i').snd) = sup …
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          -- ⊢ (sup P.parts fun i => sup Q.parts fun i' => i ⊓ i') = sup P.parts fun i => s …
          rfl
          -- 🎉 no goals
        · rw [P.supParts, Q.supParts, inf_idem])⟩
          -- 🎉 no goals

@[simp]
theorem parts_inf (P Q : Finpartition a) :
    (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).image fun bc : α × α ↦ bc.1 ⊓ bc.2).erase ⊥ :=
  rfl
#align finpartition.parts_inf Finpartition.parts_inf

instance : SemilatticeInf (Finpartition a) :=
  { (inferInstance : PartialOrder (Finpartition a)),
    (inferInstance : Inf (Finpartition a)) with
    inf_le_left := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      -- ⊢ ∃ c_1, c_1 ∈ P.parts ∧ c.fst ⊓ c.snd ≤ c_1
      rw [mem_product] at hc
      -- ⊢ ∃ c_1, c_1 ∈ P.parts ∧ c.fst ⊓ c.snd ≤ c_1
      exact ⟨c.1, hc.1, inf_le_left⟩
      -- 🎉 no goals
    inf_le_right := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      -- ⊢ ∃ c_1, c_1 ∈ Q.parts ∧ c.fst ⊓ c.snd ≤ c_1
      rw [mem_product] at hc
      -- ⊢ ∃ c_1, c_1 ∈ Q.parts ∧ c.fst ⊓ c.snd ≤ c_1
      exact ⟨c.2, hc.2, inf_le_right⟩
      -- 🎉 no goals
    le_inf := fun P Q R hPQ hPR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      -- ⊢ ∃ c, c ∈ (Q ⊓ R).parts ∧ b ≤ c
      obtain ⟨d, hd, hbd⟩ := hPR hb
      -- ⊢ ∃ c, c ∈ (Q ⊓ R).parts ∧ b ≤ c
      have h := _root_.le_inf hbc hbd
      -- ⊢ ∃ c, c ∈ (Q ⊓ R).parts ∧ b ≤ c
      refine'
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

end Inf

theorem exists_le_of_le {a b : α} {P Q : Finpartition a} (h : P ≤ Q) (hb : b ∈ Q.parts) :
    ∃ c ∈ P.parts, c ≤ b := by
  by_contra H
  -- ⊢ False
  refine' Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) _)
  -- ⊢ Disjoint b a
  rw [← P.supParts, Finset.disjoint_sup_right]
  -- ⊢ ∀ ⦃i : α⦄, i ∈ P.parts → Disjoint b (id i)
  rintro c hc
  -- ⊢ Disjoint b (id c)
  obtain ⟨d, hd, hcd⟩ := h hc
  -- ⊢ Disjoint b (id c)
  refine' (Q.disjoint hb hd _).mono_right hcd
  -- ⊢ b ≠ d
  rintro rfl
  -- ⊢ False
  simp only [not_exists, not_and] at H
  -- ⊢ False
  exact H _ hc hcd
  -- 🎉 no goals
#align finpartition.exists_le_of_le Finpartition.exists_le_of_le

theorem card_mono {a : α} {P Q : Finpartition a} (h : P ≤ Q) : Q.parts.card ≤ P.parts.card := by
  classical
    have : ∀ b ∈ Q.parts, ∃ c ∈ P.parts, c ≤ b := fun b ↦ exists_le_of_le h
    choose f hP hf using this
    rw [← card_attach]
    refine' card_le_card_of_inj_on (fun b ↦ f _ b.2) (fun b _ ↦ hP _ b.2) fun b _ c _ h ↦ _
    exact
      Subtype.coe_injective
        (Q.disjoint.elim b.2 c.2 fun H ↦
          P.ne_bot (hP _ b.2) <| disjoint_self.1 <| H.mono (hf _ b.2) <| h.le.trans <| hf _ c.2)
#align finpartition.card_mono Finpartition.card_mono

variable [DecidableEq α] {a b c : α}

section Bind

variable {P : Finpartition a} {Q : ∀ i ∈ P.parts, Finpartition i}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps]
def bind (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : Finpartition a
    where
  parts := P.parts.attach.biUnion fun i ↦ (Q i.1 i.2).parts
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint]
    -- ⊢ Set.PairwiseDisjoint (↑(Finset.biUnion (attach P.parts) fun i => (Q ↑i (_ :  …
    rintro a ha b hb h
    -- ⊢ (Disjoint on id) a b
    rw [Finset.mem_coe, Finset.mem_biUnion] at ha hb
    -- ⊢ (Disjoint on id) a b
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha
    -- ⊢ (Disjoint on id) a b
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb
    -- ⊢ (Disjoint on id) a b
    obtain rfl | hAB := eq_or_ne A B
    -- ⊢ (Disjoint on id) a b
    · exact (Q A hA).disjoint ha hb h
      -- 🎉 no goals
    · exact (P.disjoint hA hB hAB).mono ((Q A hA).le ha) ((Q B hB).le hb)
      -- 🎉 no goals
  supParts := by
    simp_rw [sup_biUnion]
    -- ⊢ (sup (attach P.parts) fun x => sup (Q ↑x (_ : ↑x ∈ P.parts)).parts id) = a
    trans (sup P.parts id)
    -- ⊢ (sup (attach P.parts) fun x => sup (Q ↑x (_ : ↑x ∈ P.parts)).parts id) = sup …
    · rw [eq_comm, ← Finset.sup_attach]
      -- ⊢ (sup (attach P.parts) fun x => id ↑x) = sup (attach P.parts) fun x => sup (Q …
      exact sup_congr rfl fun b _hb ↦ (Q b.1 b.2).supParts.symm
      -- 🎉 no goals
    · exact P.supParts
      -- 🎉 no goals
  not_bot_mem h := by
    rw [Finset.mem_biUnion] at h
    -- ⊢ False
    obtain ⟨⟨A, hA⟩, -, h⟩ := h
    -- ⊢ False
    exact (Q A hA).not_bot_mem h
    -- 🎉 no goals
#align finpartition.bind Finpartition.bind

theorem mem_bind : b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts := by
  rw [bind, mem_biUnion]
  -- ⊢ (∃ a_1, a_1 ∈ attach P.parts ∧ b ∈ (Q ↑a_1 (_ : ↑a_1 ∈ P.parts)).parts) ↔ ∃  …
  constructor
  -- ⊢ (∃ a_1, a_1 ∈ attach P.parts ∧ b ∈ (Q ↑a_1 (_ : ↑a_1 ∈ P.parts)).parts) → ∃  …
  · rintro ⟨⟨A, hA⟩, -, h⟩
    -- ⊢ ∃ A hA, b ∈ (Q A hA).parts
    exact ⟨A, hA, h⟩
    -- 🎉 no goals
  · rintro ⟨A, hA, h⟩
    -- ⊢ ∃ a_1, a_1 ∈ attach P.parts ∧ b ∈ (Q ↑a_1 (_ : ↑a_1 ∈ P.parts)).parts
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩
    -- 🎉 no goals
#align finpartition.mem_bind Finpartition.mem_bind

theorem card_bind (Q : ∀ i ∈ P.parts, Finpartition i) :
    (P.bind Q).parts.card = ∑ A in P.parts.attach, (Q _ A.2).parts.card := by
  apply card_biUnion
  -- ⊢ ∀ (x : { x // x ∈ P.parts }), x ∈ attach P.parts → ∀ (y : { x // x ∈ P.parts …
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  -- ⊢ Disjoint ((fun i => (Q ↑i (_ : ↑i ∈ P.parts)).parts) { val := b, property := …
  rw [Finset.disjoint_left]
  -- ⊢ ∀ ⦃a_1 : α⦄, a_1 ∈ (fun i => (Q ↑i (_ : ↑i ∈ P.parts)).parts) { val := b, pr …
  rintro d hdb hdc
  -- ⊢ False
  rw [Ne.def, Subtype.mk_eq_mk] at hbc
  -- ⊢ False
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
        (le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans <| (P.disjoint hb hc hbc).le_bot)
#align finpartition.card_bind Finpartition.card_bind

end Bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps]
def extend (P : Finpartition a) (hb : b ≠ ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c) : Finpartition c
    where
  parts := insert b P.parts
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_insert]
    -- ⊢ Set.PairwiseDisjoint (insert b ↑P.parts) id
    exact P.disjoint.insert fun d hd _ ↦ hab.symm.mono_right <| P.le hd
    -- 🎉 no goals
  supParts := by rwa [sup_insert, P.supParts, id, _root_.sup_comm]
                 -- 🎉 no goals
  not_bot_mem h := (mem_insert.1 h).elim hb.symm P.not_bot_mem
#align finpartition.extend Finpartition.extend

theorem card_extend (P : Finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : Disjoint a b}
    {hc : a ⊔ b = c} : (P.extend hb hab hc).parts.card = P.parts.card + 1 :=
  card_insert_of_not_mem fun h ↦ hb <| hab.symm.eq_bot_of_le <| P.le h
#align finpartition.card_extend Finpartition.card_extend

end DistribLattice

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableEq α] {a b c : α} (P : Finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
@[simps!]
def avoid (b : α) : Finpartition (a \ b) :=
  ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun a ↦ sdiff_le).supIndep
    (by rw [sup_image, comp.left_id, Finset.sup_sdiff_right, ← id_def, P.supParts])
        -- 🎉 no goals
#align finpartition.avoid Finpartition.avoid

@[simp]
theorem mem_avoid : c ∈ (P.avoid b).parts ↔ ∃ d ∈ P.parts, ¬d ≤ b ∧ d \ b = c := by
  simp only [avoid, ofErase, mem_erase, Ne.def, mem_image, exists_prop, ← exists_and_left,
    @and_left_comm (c ≠ ⊥)]
  refine' exists_congr fun d ↦ and_congr_right' <| and_congr_left _
  -- ⊢ d \ b = c → (¬c = ⊥ ↔ ¬d ≤ b)
  rintro rfl
  -- ⊢ ¬d \ b = ⊥ ↔ ¬d ≤ b
  rw [sdiff_eq_bot_iff]
  -- 🎉 no goals
#align finpartition.mem_avoid Finpartition.mem_avoid

end GeneralizedBooleanAlgebra

end Finpartition

/-! ### Finite partitions of finsets -/


namespace Finpartition

variable [DecidableEq α] {s t : Finset α} (P : Finpartition s)

theorem nonempty_of_mem_parts {a : Finset α} (ha : a ∈ P.parts) : a.Nonempty :=
  nonempty_iff_ne_empty.2 <| P.ne_bot ha
#align finpartition.nonempty_of_mem_parts Finpartition.nonempty_of_mem_parts

theorem exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t := by
  simp_rw [← P.supParts] at ha
  -- ⊢ ∃ t, t ∈ P.parts ∧ a ∈ t
  exact mem_sup.1 ha
  -- 🎉 no goals
#align finpartition.exists_mem Finpartition.exists_mem

theorem biUnion_parts : P.parts.biUnion id = s :=
  (sup_eq_biUnion _ _).symm.trans P.supParts
#align finpartition.bUnion_parts Finpartition.biUnion_parts

theorem sum_card_parts : ∑ i in P.parts, i.card = s.card := by
  convert congr_arg Finset.card P.biUnion_parts
  -- ⊢ ∑ i in P.parts, card i = card (Finset.biUnion P.parts id)
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  -- ⊢ ∑ i in P.parts, card i = ∑ u in P.parts, card (id u)
  rfl
  -- 🎉 no goals
#align finpartition.sum_card_parts Finpartition.sum_card_parts

/-- `⊥` is the partition in singletons, aka discrete partition. -/
instance (s : Finset α) : Bot (Finpartition s) :=
  ⟨{  parts := s.map ⟨singleton, singleton_injective⟩
      supIndep :=
        Set.PairwiseDisjoint.supIndep
          (by
            rw [Finset.coe_map]
            -- ⊢ Set.PairwiseDisjoint (↑{ toFun := singleton, inj' := (_ : Injective singleto …
            exact Finset.pairwiseDisjoint_range_singleton.subset (Set.image_subset_range _ _))
            -- 🎉 no goals
      supParts := by rw [sup_map, comp.left_id, Embedding.coeFn_mk, Finset.sup_singleton']
                     -- 🎉 no goals
      not_bot_mem := by simp }⟩
                        -- 🎉 no goals

@[simp]
theorem parts_bot (s : Finset α) :
    (⊥ : Finpartition s).parts = s.map ⟨singleton, singleton_injective⟩ :=
  rfl
#align finpartition.parts_bot Finpartition.parts_bot

theorem card_bot (s : Finset α) : (⊥ : Finpartition s).parts.card = s.card :=
  Finset.card_map _
#align finpartition.card_bot Finpartition.card_bot

theorem mem_bot_iff : t ∈ (⊥ : Finpartition s).parts ↔ ∃ a ∈ s, {a} = t :=
  mem_map
#align finpartition.mem_bot_iff Finpartition.mem_bot_iff

instance (s : Finset α) : OrderBot (Finpartition s) :=
  { (inferInstance : Bot (Finpartition s)) with
    bot_le := fun P t ht ↦ by
      rw [mem_bot_iff] at ht
      -- ⊢ ∃ c, c ∈ P.parts ∧ t ≤ c
      obtain ⟨a, ha, rfl⟩ := ht
      -- ⊢ ∃ c, c ∈ P.parts ∧ {a} ≤ c
      obtain ⟨t, ht, hat⟩ := P.exists_mem ha
      -- ⊢ ∃ c, c ∈ P.parts ∧ {a} ≤ c
      exact ⟨t, ht, singleton_subset_iff.2 hat⟩ }
      -- 🎉 no goals

theorem card_parts_le_card (P : Finpartition s) : P.parts.card ≤ s.card := by
  rw [← card_bot s]
  -- ⊢ card P.parts ≤ card ⊥.parts
  exact card_mono bot_le
  -- 🎉 no goals
#align finpartition.card_parts_le_card Finpartition.card_parts_le_card

section Atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : Finset α) (F : Finset (Finset α)) : Finpartition s :=
  ofErase (F.powerset.image fun Q ↦ s.filter fun i ↦ ∀ t ∈ F, t ∈ Q ↔ i ∈ t)
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h ↦
      disjoint_left.mpr fun z hz1 hz2 ↦
        h (by
            rw [mem_coe, mem_image] at hx hy
            -- ⊢ x = y
            obtain ⟨Q, hQ, rfl⟩ := hx
            -- ⊢ filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ i ∈ t)) s = y
            obtain ⟨R, hR, rfl⟩ := hy
            -- ⊢ filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ i ∈ t)) s = filter (fun  …
            suffices h' : Q = R
            -- ⊢ filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ i ∈ t)) s = filter (fun  …
            · subst h'
              -- ⊢ filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ i ∈ t)) s = filter (fun  …
              exact of_eq_true (eq_self (
                filter (fun i ↦ ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ i ∈ t)) s))
            rw [id, mem_filter] at hz1 hz2
            -- ⊢ Q = R
            rw [mem_powerset] at hQ hR
            -- ⊢ Q = R
            ext i
            -- ⊢ i ∈ Q ↔ i ∈ R
            refine' ⟨fun hi ↦ _, fun hi ↦ _⟩
            -- ⊢ i ∈ R
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
              -- 🎉 no goals
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
              -- 🎉 no goals
    (by
      refine' (Finset.sup_le fun t ht ↦ _).antisymm fun a ha ↦ _
      -- ⊢ id t ≤ s
      · rw [mem_image] at ht
        -- ⊢ id t ≤ s
        obtain ⟨A, _, rfl⟩ := ht
        -- ⊢ id (filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ A ↔ i ∈ t)) s) ≤ s
        exact s.filter_subset _
        -- 🎉 no goals
      · rw [mem_sup]
        -- ⊢ ∃ v, v ∈ image (fun Q => filter (fun i => ∀ (t : Finset α), t ∈ F → (t ∈ Q ↔ …
        refine'
          ⟨s.filter fun i ↦ ∀ t, t ∈ F → ((t ∈ F.filter fun u ↦ a ∈ u) ↔ i ∈ t),
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht ↦ _⟩⟩
        rw [mem_filter]
        -- ⊢ t ∈ F ∧ a ∈ t ↔ a ∈ t
        exact and_iff_right ht)
        -- 🎉 no goals
#align finpartition.atomise Finpartition.atomise

variable {F : Finset (Finset α)}

-- porting note:
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection
   (Q «expr ⊆ » F) -/
theorem mem_atomise :
    t ∈ (atomise s F).parts ↔
      t.Nonempty ∧ ∃ (Q : _) (_ : Q ⊆ F), (s.filter fun i ↦ ∀ u ∈ F, u ∈ Q ↔ i ∈ u) = t := by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_singleton, and_comm, mem_powerset, exists_prop]
#align finpartition.mem_atomise Finpartition.mem_atomise

theorem atomise_empty (hs : s.Nonempty) : (atomise s ∅).parts = {s} := by
  simp only [atomise, powerset_empty, image_singleton, not_mem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_True]
  exact erase_eq_of_not_mem (not_mem_singleton.2 hs.ne_empty.symm)
  -- 🎉 no goals
#align finpartition.atomise_empty Finpartition.atomise_empty

theorem card_atomise_le : (atomise s F).parts.card ≤ 2 ^ F.card :=
  (card_le_of_subset <| erase_subset _ _).trans <| Finset.card_image_le.trans (card_powerset _).le
#align finpartition.card_atomise_le Finpartition.card_atomise_le

theorem biUnion_filter_atomise (ht : t ∈ F) (hts : t ⊆ s) :
    ((atomise s F).parts.filter fun u ↦ u ⊆ t ∧ u.Nonempty).biUnion id = t := by
  ext a
  -- ⊢ a ∈ Finset.biUnion (filter (fun u => u ⊆ t ∧ Finset.Nonempty u) (atomise s F …
  refine' mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ ↦ (mem_filter.1 hu).2.1 ha, fun ha ↦ _⟩
  -- ⊢ ∃ a_1, a_1 ∈ filter (fun u => u ⊆ t ∧ Finset.Nonempty u) (atomise s F).parts …
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  -- ⊢ ∃ a_1, a_1 ∈ filter (fun u => u ⊆ t ∧ Finset.Nonempty u) (atomise s F).parts …
  refine' ⟨u, mem_filter.2 ⟨hu, fun b hb ↦ _, _, hau⟩, hau⟩
  -- ⊢ b ∈ t
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  -- ⊢ b ∈ t
  rw [mem_filter] at hau hb
  -- ⊢ b ∈ t
  rwa [← hb.2 _ ht, hau.2 _ ht]
  -- 🎉 no goals
#align finpartition.bUnion_filter_atomise Finpartition.biUnion_filter_atomise

theorem card_filter_atomise_le_two_pow (ht : t ∈ F) :
    ((atomise s F).parts.filter fun u ↦ u ⊆ t ∧ u.Nonempty).card ≤ 2 ^ (F.card - 1) := by
  suffices h :
    ((atomise s F).parts.filter fun u ↦ u ⊆ t ∧ u.Nonempty) ⊆
      (F.erase t).powerset.image fun P ↦ s.filter fun i ↦ ∀ x ∈ F, x ∈ insert t P ↔ i ∈ x
  · refine' (card_le_of_subset h).trans (card_image_le.trans _)
    -- ⊢ card (powerset (erase F t)) ≤ 2 ^ (card F - 1)
    rw [card_powerset, card_erase_of_mem ht]
    -- 🎉 no goals
  rw [subset_iff]
  -- ⊢ ∀ ⦃x : Finset α⦄, x ∈ filter (fun u => u ⊆ t ∧ Finset.Nonempty u) (atomise s …
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  -- ⊢ ∃ a, a ⊆ erase F t ∧ filter (fun i => ∀ (x : Finset α), x ∈ F → (x ∈ insert  …
  refine' ⟨P.erase t, erase_subset_erase _ PQ, _⟩
  -- ⊢ filter (fun i => ∀ (x : Finset α), x ∈ F → (x ∈ insert t (erase P t) ↔ i ∈ x …
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]
  -- 🎉 no goals
#align finpartition.card_filter_atomise_le_two_pow Finpartition.card_filter_atomise_le_two_pow

end Atomise

end Finpartition
