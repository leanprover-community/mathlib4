/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Order.Ideal
import Mathlib.Data.Finset.Max

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

namespace Order

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
/-- Suppose `α` is a nonempty dense linear order without endpoints, and
suppose `lo`, `hi`, are finite subsets with all of `lo` strictly before `hi`.
Then there is an element of `α` strictly between `lo` and `hi`. -/
theorem exists_between_finsets [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [nonem : Nonempty α] (lo hi : Finset α) (lo_lt_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y) :
    ∃ m : α, (∀ x ∈ lo, x < m) ∧ ∀ y ∈ hi, m < y :=
  if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use `DenselyOrdered`
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
    else -- both sets are empty, use `Nonempty`
          nonem.elim
        fun m ↦ ⟨m, fun x hx ↦ (nlo ⟨x, hx⟩).elim, fun y hy ↦ (nhi ⟨y, hy⟩).elim⟩

lemma exists_orderEmbedding_insert [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β]
    [nonem : Nonempty β] (S : Finset α) (f : S ↪o β) (a : α) :
    ∃ (g : (insert a S : Finset α) ↪o β),
      g ∘ (Set.inclusion ((S.subset_insert a) : ↑S ⊆ ↑(insert a S))) = f := by
  let Slt := {x ∈ S.attach | x.val < a}.image f
  let Sgt := {x ∈ S.attach | a < x.val}.image f
  obtain ⟨b, hb, hb'⟩ := Order.exists_between_finsets Slt Sgt (fun x hx y hy => by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, Slt, Sgt] at hx hy
    obtain ⟨_, hx, _, rfl⟩ := hx
    obtain ⟨_, hy, _, rfl⟩ := hy
    exact f.strictMono (hx.trans hy))
  refine ⟨OrderEmbedding.ofStrictMono
    (fun (x : (insert a S : Finset α)) => if hx : x.1 ∈ S then f ⟨x.1, hx⟩ else b) ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    if hxS : x ∈ S
    then if hyS : y ∈ S
      then simpa only [hxS, hyS, ↓reduceDIte, OrderEmbedding.lt_iff_lt, Subtype.mk_lt_mk]
      else
        obtain rfl := Finset.eq_of_mem_insert_of_notMem hy hyS
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
    else
      obtain rfl := Finset.eq_of_mem_insert_of_notMem hx hxS
      if hyS : y ∈ S
      then
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb' _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
      else simp only [Finset.eq_of_mem_insert_of_notMem hy hyS, lt_self_iff_false] at hxy
  · ext x
    simp only [OrderEmbedding.coe_ofStrictMono, Finset.insert_val,
      Function.comp_apply, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta]

variable (α β)

/-- The type of partial order isomorphisms between `α` and `β` defined on finite subsets.
A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
of pairs which should be identified. -/
def PartialIso : Type _ :=
  { f : Finset (α × β) //
    ∀ p ∈ f, ∀ q ∈ f,
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }

namespace PartialIso

instance : Inhabited (PartialIso α β) := ⟨⟨∅, fun _p h _q ↦ (Finset.notMem_empty _ h).elim⟩⟩

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
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, fun p hp ↦ f.prop _ hp _ hb⟩
  have :
    ∀ x ∈ {p ∈ f.val | p.fst < a}.image Prod.snd,
      ∀ y ∈ {p ∈ f.val | a < p.fst}.image Prod.snd, x < y := by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  obtain ⟨b, hb⟩ := exists_between_finsets _ _ this
  use b
  rintro ⟨p1, p2⟩ hp
  have : p1 ≠ a := fun he ↦ h ⟨p2, he ▸ hp⟩
  rcases lt_or_gt_of_ne this with hl | hr
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff] at this
    exact this.1.trans this.2.symm
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff] at this
    exact this.1.trans this.2.symm

/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
protected def comm : PartialIso α β → PartialIso β α :=
  Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq ↦
    Eq.symm <|
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hp
          rwa [← Finset.mem_coe])
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hq
          rwa [← Finset.mem_coe])

variable (β)

/-- The set of partial isomorphisms defined at `a : α`, together with a proof that any
partial isomorphism can be extended to one defined at `a`. -/
def definedAtLeft [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α) :
    Cofinal (PartialIso α β) where
  carrier := {f | ∃ b : β, (a, b) ∈ f.val}
  isCofinal f := by
    obtain ⟨b, a_b⟩ := exists_across f a
    refine
      ⟨⟨insert (a, b) f.val, fun p hp q hq ↦ ?_⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact a_b _ qf
    · exact a_b _ pf
    · exact f.prop _ pf _ qf

variable (α) {β}

/-- The set of partial isomorphisms defined at `b : β`, together with a proof that any
partial isomorphism can be extended to include `b`. We prove this by symmetry. -/
def definedAtRight [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β) :
    Cofinal (PartialIso α β) where
  carrier := {f | ∃ a, (a, b) ∈ f.val}
  isCofinal f := by
    rcases (definedAtLeft α b).isCofinal f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    refine ⟨f'.comm, ⟨a, ?_⟩, ?_⟩
    · change (a, b) ∈ f'.val.image _
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage]
    · change _ ⊆ f'.val.image _
      rwa [← Finset.coe_subset, Finset.coe_image, ← Equiv.symm_image_subset, ← Finset.coe_image,
        Finset.coe_subset]

variable {α}

/-- Given an ideal which intersects `definedAtLeft β a`, pick `b : β` such that
some partial function in the ideal maps `a` to `b`. -/
def funOfIdeal [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtLeft β a ∧ f ∈ I) → { b // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ ↦ ⟨b, f, hf, hb⟩

/-- Given an ideal which intersects `definedAtRight α b`, pick `a : α` such that
some partial function in the ideal maps `a` to `b`. -/
def invOfIdeal [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtRight α b ∧ f ∈ I) → { a // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ ↦ ⟨a, f, hf, ha⟩

end PartialIso

open PartialIso

-- variable (α β)

/-- Any countable linear order embeds in any nontrivial dense linear order. -/
theorem embedding_from_countable_to_dense [Countable α] [DenselyOrdered β] [Nontrivial β] :
    Nonempty (α ↪o β) := by
  cases nonempty_encodable α
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  obtain ⟨a, ha⟩ := exists_between hxy
  haveI : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  let our_ideal : Ideal (PartialIso α _) :=
    idealOfCofinals default (definedAtLeft (Set.Ioo x y))
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ _ a)
  refine
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a ↦ (F a).val) fun a₁ a₂ ↦ ?_)
        (OrderEmbedding.subtype _)⟩
  rcases (F a₁).prop with ⟨f, hf, ha₁⟩
  rcases (F a₂).prop with ⟨g, hg, ha₂⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, _hm, fm, gm⟩
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp

/-- Any two countable dense, nonempty linear orders without endpoints are order isomorphic. This is
also known as **Cantor's isomorphism theorem**. -/
theorem iso_of_countable_dense [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let to_cofinal : α ⊕ β → Cofinal (PartialIso α β) := fun p ↦
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  exact ⟨OrderIso.ofCmpEqCmp (fun a ↦ (F a).val) (fun b ↦ (G b).val) fun a b ↦ by
      rcases (F a).prop with ⟨f, hf, ha⟩
      rcases (G b).prop with ⟨g, hg, hb⟩
      rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩

end Order
