/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Order.Ideal
import Mathlib.Data.Finset.Lattice

#align_import order.countable_dense_linear_order from "leanprover-community/mathlib"@"2705404e701abc6b3127da906f40bae062a169c9"

/-!
# The back and forth method and countable dense linear orders

## Results

Suppose `α β` are linear orders, with `α` countable and `β` dense, nontrivial. Then there is an
order embedding `α ↪ β`. If in addition `α` is dense, nonempty, without endpoints and `β` is
countable, without endpoints, then we can upgrade this to an order isomorphism `α ≃ β`.

The idea for both results is to consider "partial isomorphisms", which identify a finite subset of
`α` with a finite subset of `β`, and prove that for any such partial isomorphism `f` and `a : α`, we
can extend `f` to include `a` in its domain.

## References

https://en.wikipedia.org/wiki/Back-and-forth_method

## Tags

back and forth, dense, countable, order
-/


noncomputable section

open Classical

namespace Order

/-- Suppose `α` is a nonempty dense linear order without endpoints, and
    suppose `lo`, `hi`, are finite subsets with all of `lo` strictly
    before `hi`. Then there is an element of `α` strictly between `lo`
    and `hi`. -/
theorem exists_between_finsets {α : Type*} [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [nonem : Nonempty α] (lo hi : Finset α) (lo_lt_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y) :
    ∃ m : α, (∀ x ∈ lo, x < m) ∧ ∀ y ∈ hi, m < y :=
  if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use densely_ordered
        Exists.elim
        (exists_between (lo_lt_hi _ (Finset.max'_mem _ nlo) _ (Finset.min'_mem _ nhi))) fun m hm ↦
        ⟨m, fun x hx ↦ lt_of_le_of_lt (Finset.le_max' lo x hx) hm.1, fun y hy ↦
          lt_of_lt_of_le hm.2 (Finset.min'_le hi y hy)⟩
    else-- upper set is empty, use `NoMaxOrder`
        Exists.elim
        (exists_gt (Finset.max' lo nlo)) fun m hm ↦
        ⟨m, fun x hx ↦ lt_of_le_of_lt (Finset.le_max' lo x hx) hm, fun y hy ↦ (nhi ⟨y, hy⟩).elim⟩
  else
    if nhi : hi.Nonempty then
      -- lower set is empty, use `NoMinOrder`
        Exists.elim
        (exists_lt (Finset.min' hi nhi)) fun m hm ↦
        ⟨m, fun x hx ↦ (nlo ⟨x, hx⟩).elim, fun y hy ↦ lt_of_lt_of_le hm (Finset.min'_le hi y hy)⟩
    else-- both sets are empty, use nonempty
          nonem.elim
        fun m ↦ ⟨m, fun x hx ↦ (nlo ⟨x, hx⟩).elim, fun y hy ↦ (nhi ⟨y, hy⟩).elim⟩
#align order.exists_between_finsets Order.exists_between_finsets

variable (α β : Type*) [LinearOrder α] [LinearOrder β]

-- Porting note: Mathport warning: expanding binder collection (p q «expr ∈ » f)
/-- The type of partial order isomorphisms between `α` and `β` defined on finite subsets.
    A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
    of pairs which should be identified. -/
def PartialIso : Type _ :=
  { f : Finset (α × β) //
    ∀ (p) (_ : p ∈ f) (q) (_ : q ∈ f),
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }
#align order.partial_iso Order.PartialIso

namespace PartialIso

instance : Inhabited (PartialIso α β) := ⟨⟨∅, fun _p h _q ↦ (Finset.not_mem_empty _ h).elim⟩⟩

instance : Preorder (PartialIso α β) := Subtype.preorder _

variable {α β}

/-- For each `a`, we can find a `b` in the codomain, such that `a`'s relation to
the domain of `f` is `b`'s relation to the image of `f`.

Thus, if `a` is not already in `f`, then we can extend `f` by sending `a` to `b`.
-/
theorem exists_across [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
    (f : PartialIso α β) (a : α) :
    ∃ b : β, ∀ p ∈ f.val, cmp (Prod.fst p) a = cmp (Prod.snd p) b := by
  by_cases h : ∃ b, (a, b) ∈ f.val
  -- ⊢ ∃ b, ∀ (p : α × β), p ∈ ↑f → cmp p.fst a = cmp p.snd b
  · cases' h with b hb
    -- ⊢ ∃ b, ∀ (p : α × β), p ∈ ↑f → cmp p.fst a = cmp p.snd b
    exact ⟨b, fun p hp ↦ f.prop _ hp _ hb⟩
    -- 🎉 no goals
  have :
    ∀ x ∈ (f.val.filter fun p : α × β ↦ p.fst < a).image Prod.snd,
      ∀ y ∈ (f.val.filter fun p : α × β ↦ a < p.fst).image Prod.snd, x < y := by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  cases' exists_between_finsets _ _ this with b hb
  -- ⊢ ∃ b, ∀ (p : α × β), p ∈ ↑f → cmp p.fst a = cmp p.snd b
  use b
  -- ⊢ ∀ (p : α × β), p ∈ ↑f → cmp p.fst a = cmp p.snd b
  rintro ⟨p1, p2⟩ hp
  -- ⊢ cmp (p1, p2).fst a = cmp (p1, p2).snd b
  have : p1 ≠ a := fun he ↦ h ⟨p2, he ▸ hp⟩
  -- ⊢ cmp (p1, p2).fst a = cmp (p1, p2).snd b
  cases' lt_or_gt_of_ne this with hl hr
  -- ⊢ cmp (p1, p2).fst a = cmp (p1, p2).snd b
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff] at this
    -- ⊢ cmp (p1, p2).fst a = cmp (p1, p2).snd b
    exact this.1.trans this.2.symm
    -- 🎉 no goals
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff] at this
    -- ⊢ cmp (p1, p2).fst a = cmp (p1, p2).snd b
    exact this.1.trans this.2.symm
    -- 🎉 no goals
#align order.partial_iso.exists_across Order.PartialIso.exists_across

/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
protected def comm : PartialIso α β → PartialIso β α :=
  Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq ↦
    Eq.symm <|
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hp
          -- ⊢ ↑(Equiv.prodComm α β).symm p ∈ f
          rwa [← Finset.mem_coe])
          -- 🎉 no goals
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hq
          -- ⊢ ↑(Equiv.prodComm α β).symm q ∈ f
          rwa [← Finset.mem_coe])
          -- 🎉 no goals
#align order.partial_iso.comm Order.PartialIso.comm

variable (β)

/-- The set of partial isomorphisms defined at `a : α`, together with a proof that any
    partial isomorphism can be extended to one defined at `a`. -/
def definedAtLeft [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α) :
    Cofinal (PartialIso α β) where
  carrier := {f | ∃ b : β, (a, b) ∈ f.val}
  mem_gt f := by
    cases' exists_across f a with b a_b
    -- ⊢ ∃ y, y ∈ {f | ∃ b, (a, b) ∈ ↑f} ∧ f ≤ y
    refine
      ⟨⟨insert (a, b) f.val, fun p hp q hq ↦ ?_⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    -- ⊢ cmp p.fst q.fst = cmp p.snd q.snd
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    -- ⊢ cmp (a, b).fst q.fst = cmp (a, b).snd q.snd
                                  -- ⊢ cmp (a, b).fst (a, b).fst = cmp (a, b).snd (a, b).snd
                                  -- ⊢ cmp p.fst (a, b).fst = cmp p.snd (a, b).snd
    · simp only [cmp_self_eq_eq]
      -- 🎉 no goals
    · rw [cmp_eq_cmp_symm]
      -- ⊢ cmp q.fst (a, b).fst = cmp q.snd (a, b).snd
      exact a_b _ qf
      -- 🎉 no goals
    · exact a_b _ pf
      -- 🎉 no goals
    · exact f.prop _ pf _ qf
      -- 🎉 no goals
#align order.partial_iso.defined_at_left Order.PartialIso.definedAtLeft

variable (α) {β}

/-- The set of partial isomorphisms defined at `b : β`, together with a proof that any
    partial isomorphism can be extended to include `b`. We prove this by symmetry. -/
def definedAtRight [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β) :
    Cofinal (PartialIso α β) where
  carrier := {f | ∃ a, (a, b) ∈ f.val}
  mem_gt f := by
    rcases (definedAtLeft α b).mem_gt f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    -- ⊢ ∃ y, y ∈ {f | ∃ a, (a, b) ∈ ↑f} ∧ f ≤ y
    refine' ⟨f'.comm, ⟨a, _⟩, _⟩
    -- ⊢ (a, b) ∈ ↑(PartialIso.comm f')
    · change (a, b) ∈ f'.val.image _
      -- ⊢ (a, b) ∈ Finset.image ↑(Equiv.prodComm β α) ↑f'
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage]
      -- 🎉 no goals
    · change _ ⊆ f'.val.image _
      -- ⊢ (fun a => ↑a) f ⊆ Finset.image ↑(Equiv.prodComm β α) ↑f'
      rwa [← Finset.coe_subset, Finset.coe_image, ← Equiv.subset_image, ← Finset.coe_image,
        Finset.coe_subset]
#align order.partial_iso.defined_at_right Order.PartialIso.definedAtRight

variable {α}

/-- Given an ideal which intersects `definedAtLeft β a`, pick `b : β` such that
    some partial function in the ideal maps `a` to `b`. -/
def funOfIdeal [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtLeft β a ∧ f ∈ I) → { b // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ ↦ ⟨b, f, hf, hb⟩
#align order.partial_iso.fun_of_ideal Order.PartialIso.funOfIdeal

/-- Given an ideal which intersects `definedAtRight α b`, pick `a : α` such that
    some partial function in the ideal maps `a` to `b`. -/
def invOfIdeal [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtRight α b ∧ f ∈ I) → { a // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ ↦ ⟨a, f, hf, ha⟩
#align order.partial_iso.inv_of_ideal Order.PartialIso.invOfIdeal

end PartialIso

open PartialIso

-- variable (α β)

/-- Any countable linear order embeds in any nontrivial dense linear order. -/
theorem embedding_from_countable_to_dense [Encodable α] [DenselyOrdered β] [Nontrivial β] :
    Nonempty (α ↪o β) := by
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  -- ⊢ Nonempty (α ↪o β)
  cases' exists_between hxy with a ha
  -- ⊢ Nonempty (α ↪o β)
  haveI : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  -- ⊢ Nonempty (α ↪o β)
  let our_ideal : Ideal (PartialIso α _) :=
    idealOfCofinals default (definedAtLeft (Set.Ioo x y))
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ _ a)
  -- ⊢ Nonempty (α ↪o β)
  refine
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a ↦ (F a).val) fun a₁ a₂ ↦ ?_)
        (OrderEmbedding.subtype _)⟩
  rcases(F a₁).prop with ⟨f, hf, ha₁⟩
  -- ⊢ a₁ < a₂ → (fun a => ↑(F a)) a₁ < (fun a => ↑(F a)) a₂
  rcases(F a₂).prop with ⟨g, hg, ha₂⟩
  -- ⊢ a₁ < a₂ → (fun a => ↑(F a)) a₁ < (fun a => ↑(F a)) a₂
  rcases our_ideal.directed _ hf _ hg with ⟨m, _hm, fm, gm⟩
  -- ⊢ a₁ < a₂ → (fun a => ↑(F a)) a₁ < (fun a => ↑(F a)) a₂
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp
  -- 🎉 no goals
#align order.embedding_from_countable_to_dense Order.embedding_from_countable_to_dense

/-- Any two countable dense, nonempty linear orders without endpoints are order isomorphic. -/
theorem iso_of_countable_dense [Encodable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Encodable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) :=
  let to_cofinal : Sum α β → Cofinal (PartialIso α β) := fun p ↦
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  ⟨OrderIso.ofCmpEqCmp (fun a ↦ (F a).val) (fun b ↦ (G b).val) fun a b ↦ by
      rcases(F a).prop with ⟨f, hf, ha⟩
      -- ⊢ cmp a ((fun b => ↑(G b)) b) = cmp ((fun a => ↑(F a)) a) b
      rcases(G b).prop with ⟨g, hg, hb⟩
      -- ⊢ cmp a ((fun b => ↑(G b)) b) = cmp ((fun a => ↑(F a)) a) b
      rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
      -- ⊢ cmp a ((fun b => ↑(G b)) b) = cmp ((fun a => ↑(F a)) a) b
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩
      -- 🎉 no goals
#align order.iso_of_countable_dense Order.iso_of_countable_dense

end Order
