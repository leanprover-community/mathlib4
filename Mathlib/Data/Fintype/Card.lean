/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# Cardinalities of finite types

This file defines the cardinality `Fintype.card α` as the number of elements in `(univ : Finset α)`.
We also include some elementary results on the values of `Fintype.card` on specific types.

## Main declarations

* `Fintype.card α`: Cardinality of a fintype. Equal to `Finset.univ.card`.
* `Finite.surjective_of_injective`: an injective function from a finite type to
  itself is also surjective.

-/

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s :=
  Multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s := by
  rw [← subtype_card s H]
  congr!

@[simp]
theorem card_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Fintype.card p (ofFinset s H) = #s :=
  Fintype.subtype_card s H

theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] :
    Fintype.card p = #s := by rw [← card_ofFinset s H]; congr!

end Fintype

namespace Fintype

theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr!

@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])

/-- Note: this lemma is specifically about `Fintype.ofSubsingleton`. For a statement about
arbitrary `Fintype` instances, use either `Fintype.card_le_one_iff_subsingleton` or
`Fintype.card_unique`. -/
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl

@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

/-- Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement about
arbitrary `Fintype` instances, use `Fintype.card_eq_zero`. -/
theorem card_ofIsEmpty [IsEmpty α] : @Fintype.card α Fintype.ofIsEmpty = 0 :=
  rfl

end Fintype

namespace Set

variable {s t : Set α}

-- We use an arbitrary `[Fintype s]` instance here,
-- not necessarily coming from a `[Fintype α]`.
@[simp]
theorem toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

end Set

@[simp, grind =]
theorem Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α := rfl

theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : #s = Fintype.card α) :
    s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by rw [hs, Finset.card_univ]

theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : #s = Fintype.card α ↔ s = univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

theorem Finset.card_le_univ [Fintype α] (s : Finset α) : #s ≤ Fintype.card α :=
  card_le_card (subset_univ s)

theorem Finset.card_lt_univ_of_notMem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    #s < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

@[deprecated (since := "2025-05-23")]
alias Finset.card_lt_univ_of_not_mem := Finset.card_lt_univ_of_notMem

theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    #s < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)

theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    #sᶜ < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
    #(univ \ s) = Fintype.card α - #s := by grind

theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #sᶜ = Fintype.card α - #s :=
  Finset.card_univ_diff s

@[simp]
theorem Finset.card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    #s + #sᶜ = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

@[simp]
theorem Finset.card_compl_add_card [DecidableEq α] [Fintype α] (s : Finset α) :
    #sᶜ + #s = Fintype.card α := by
  rw [Nat.add_comm, card_add_card_compl]

theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)] :
    Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]

theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique

theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique

theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl

theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl

theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

@[simp]
theorem Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
theorem Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
theorem Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl

@[simp]
theorem Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl

-- Note: The extra hypothesis `h` is there so that the rewrite lemma applies,
-- no matter what instance of `Fintype (Set.univ : Set α)` is used.
@[simp]
theorem Fintype.card_setUniv [Fintype α] {h : Fintype (Set.univ : Set α)} :
    Fintype.card (Set.univ : Set α) = Fintype.card α := by
  apply Fintype.card_of_finset'
  simp

@[simp]
theorem Fintype.card_subtype_true [Fintype α] {h : Fintype {_a : α // True}} :
    @Fintype.card {_a // True} h = Fintype.card α := by
  apply Fintype.card_of_subtype
  simp

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (α ⊕ β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (α ⊕ β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective

theorem Finite.exists_univ_list (α) [Finite α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l := by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩

theorem List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length ≤ Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2

theorem card_lt_of_injective_of_notMem (f : α → β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_notMem (x := b) <| by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

@[deprecated (since := "2025-05-23")]
alias card_lt_of_injective_of_not_mem := card_lt_of_injective_of_notMem

theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_notMem f h hy

theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surjInv h)

theorem card_range_le {α β : Type*} (f : α → β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩

theorem card_range {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective _ <| EmbeddingLike.injective f

theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]

@[simp] theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero

/-- A `Fintype` with cardinality zero is equivalent to `Empty`. -/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  Nat.pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm

theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

@[simp]
theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  _root_.ne_of_gt card_pos

instance [Nonempty α] : NeZero (card α) := ⟨card_ne_zero⟩

theorem existsUnique_iff_card_one {α} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∃! a : α, p a) ↔ #{x | p x} = 1 := by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff, and_comm,
    mem_filter_univ]

nonrec theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and]

theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)

end Fintype

namespace Finite

variable [Finite α]

theorem surjective_of_injective {f : α → α} (hinj : Injective f) : Surjective f := by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
  exact ⟨y, h.2⟩

theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩

theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

theorem injective_iff_surjective_of_equiv {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

alias ⟨_root_.Function.Injective.bijective_of_finite, _⟩ := injective_iff_bijective

alias ⟨_root_.Function.Surjective.bijective_of_finite, _⟩ := surjective_iff_bijective

alias ⟨_root_.Function.Injective.surjective_of_fintype,
    _root_.Function.Surjective.injective_of_fintype⟩ :=
  injective_iff_surjective_of_equiv

end Finite

@[simp]
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s :=
  @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

/-- We can inflate a set `s` to any bigger size. -/
lemma Finset.exists_superset_card_eq [Fintype α] {n : ℕ} {s : Finset α} (hsn : #s ≤ n)
    (hnα : n ≤ Fintype.card α) :
    ∃ t, s ⊆ t ∧ #t = n := by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]
theorem Fintype.card_prop : Fintype.card Prop = 2 :=
  rfl

theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)

theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]

theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [Fintype {a // p a}] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)

lemma Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [Fintype {a // p a}] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_notMem (b := x) (↑) Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]

theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [Fintype {a // p a}] [DecidablePred p] :
    Fintype.card { x // p x } = #{x | p x} := by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ), Set.toFinset_compl,
      Finset.card_compl, Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf]

theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]

theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ Quotient.mk'_surjective

theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  apply le_of_eq
  simp [h, Finset.card_univ]

namespace Finite

variable [Finite α]

theorem wellFounded_of_trans_of_irrefl (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] :
    WellFounded r := by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
    Finset.card_lt_card <| by
      simp_rw [Finset.lt_iff_ssubset.symm, lt_iff_le_not_ge, Finset.le_iff_subset,
        Finset.subset_iff, mem_filter_univ]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
  exact Subrelation.wf (this _ _) (measure _).wf

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedLT [Preorder α] : WellFoundedLT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedGT [Preorder α] : WellFoundedGT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

end Finite

-- Shortcut instances to make sure those are found even in the presence of other instances
-- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/WellFoundedLT.20Prop.20is.20not.20found.20when.20importing.20too.20much
instance Bool.instWellFoundedLT : WellFoundedLT Bool := inferInstance
instance Bool.instWellFoundedGT : WellFoundedGT Bool := inferInstance
instance Prop.instWellFoundedLT : WellFoundedLT Prop := inferInstance
instance Prop.instWellFoundedGT : WellFoundedGT Prop := inferInstance

section Trunc

/-- A `Fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

end Trunc

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `Fintype.card`).

The major premise is `Fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_elim]
theorem Fintype.induction_subsingleton_or_nontrivial {P : ∀ (α) [Fintype α], Prop} (α : Type*)
    [Fintype α] (hbase : ∀ (α) [Fintype α] [Subsingleton α], P α)
    (hstep : ∀ (α) [Fintype α] [Nontrivial α],
      (∀ (β) [Fintype β], Fintype.card β < Fintype.card α → P β) → P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl

section Fin

@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  List.length_finRange

theorem Fintype.card_fin_lt_of_le {m n : ℕ} (h : m ≤ n) :
    Fintype.card {i : Fin n // i < m} = m := by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ ↦ ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ ↦ ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩ }

theorem Finset.card_fin (n : ℕ) : #(univ : Finset (Fin n)) = n := by simp

/-- `Fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Fin := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)

theorem Fin.val_eq_val_of_heq {k l : ℕ} {i : Fin k} {j : Fin l} (h : i ≍ j) :
    (i : ℕ) = (j : ℕ) :=
  (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

/-- A reversed version of `Fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Fin.cast_eq_cast' {n m : ℕ} (h : Fin n = Fin m) :
    _root_.cast h = Fin.cast (fin_injective h) := by
  cases fin_injective h
  rfl

theorem card_finset_fin_le {n : ℕ} (s : Finset (Fin n)) : #s ≤ n := by
  simpa only [Fintype.card_fin] using s.card_le_univ

end Fin
