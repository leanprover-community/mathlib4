/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Cardinal arithmetic

Arithmetic operations on cardinals are defined in `SetTheory/Cardinal/Order.lean`. However, proving
the important theorem `c * c = c` for infinite cardinals and its corollaries requires the use of
ordinal numbers. This is done within this file.

## Main statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk`: when `α` is infinite, `α` and `List α` have the same cardinality.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

assert_not_exists Module Finsupp Ordinal.log

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

/-! ### Properties of `mul` -/
section mul

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c * c = c := by
  refine le_antisymm ?_ (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans h) c)
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine Acc.recOn (Cardinal.lt_wf.apply c) (fun c _ => Cardinal.inductionOn c fun α IH ol => ?_) h
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩
  classical
  letI := linearOrderOfSTO r
  haveI : IsWellOrder α (· < ·) := wo
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := fun p => max p.1 p.2
  let f : α × α ↪ Ordinal × α × α :=
    ⟨fun p : α × α => (typein (· < ·) (g p), p), fun p q => congr_arg Prod.snd⟩
  let s := f ⁻¹'o Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  -- this is a well order on `α × α`.
  haveI : IsWellOrder _ s := (RelEmbedding.preimage _ _).isWellOrder
  /- it suffices to show that this well order is smaller than `r`
       if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
      `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
      same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
      contradiction. -/
  suffices type s ≤ type r by exact card_le_card this
  refine le_of_forall_lt fun o h => ?_
  rcases typein_surj s h with ⟨p, rfl⟩
  rw [← e, lt_ord]
  refine lt_of_le_of_lt
    (?_ : _ ≤ card (succ (typein (· < ·) (g p))) * card (succ (typein (· < ·) (g p)))) ?_
  · have : { q | s q p } ⊆ insert (g p) { x | x < g p } ×ˢ insert (g p) { x | x < g p } := by
      intro q h
      simp only [s, f, Preimage, Embedding.coeFn_mk, Prod.lex_def, typein_lt_typein,
        typein_inj, mem_setOf_eq] at h
      exact max_le_iff.1 (le_iff_lt_or_eq.2 <| h.imp_right And.left)
    suffices H : (insert (g p) { x | r x (g p) } : Set α) ≃ { x | r x (g p) } ⊕ PUnit from
      ⟨(Set.embeddingOfSubset _ _ this).trans
        ((Equiv.Set.prod _ _).trans (H.prodCongr H)).toEmbedding⟩
    refine (Equiv.Set.insert ?_).trans ((Equiv.refl _).sumCongr punitEquivPUnit)
    apply @irrefl _ r
  rcases lt_or_ge (card (succ (typein (· < ·) (g p)))) ℵ₀ with qo | qo
  · exact (mul_lt_aleph0 qo qo).trans_le ol
  · suffices (succ (typein LT.lt (g p))).card < #α from (IH _ this qo).trans_lt this
    rw [← lt_ord]
    apply (isLimit_ord ol).succ_lt
    rw [e]
    apply typein_lt_type

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans hb) a)
      (by simpa only [one_mul] using mul_le_mul_right' (one_le_aleph0.trans ha) b)

@[simp]
theorem mul_mk_eq_max {α β : Type u} [Infinite α] [Infinite β] : #α * #β = max #α #β :=
  mul_eq_max (aleph0_le_mk α) (aleph0_le_mk β)

@[simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (aleph0_le_aleph o₁) (aleph0_le_aleph o₂), aleph_max]

@[simp]
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_right ha)

@[simp]
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_left ha)

theorem aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α :=
  aleph0_mul_eq (aleph0_le_mk α)

theorem mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α :=
  mul_aleph0_eq (aleph0_le_mk α)

@[simp]
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * ℵ_ o = ℵ_ o :=
  aleph0_mul_eq (aleph0_le_aleph o)

@[simp]
theorem aleph_mul_aleph0 (o : Ordinal) : ℵ_ o * ℵ₀ = ℵ_ o :=
  mul_aleph0_eq (aleph0_le_aleph o)

theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
  (mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_ge (max a b) ℵ₀).elim (fun h => (mul_lt_aleph0 h h).trans_le hc) fun h => by
      rw [mul_eq_self h]
      exact max_lt h1 h2

theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b := by
  convert mul_le_mul' (le_max_left a b) (le_max_right a b) using 1
  rw [mul_eq_self]
  exact h.trans (le_max_left a b)

theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) :
    a * b = max a b := by
  rcases le_or_gt ℵ₀ b with hb | hb
  · exact mul_eq_max h hb
  refine (mul_le_max_of_aleph0_le_left h).antisymm ?_
  have : b ≤ a := hb.le.trans h
  rw [max_eq_left this]
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') a
  rw [mul_one]

theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by
  simpa only [mul_comm b, max_comm b] using mul_le_max_of_aleph0_le_left h

theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by
  rw [mul_comm, max_comm]
  exact mul_eq_max_of_aleph0_le_left h h'

theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b := by
  rcases aleph0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  · exact mul_eq_max_of_aleph0_le_left ha' hb
  · exact mul_eq_max_of_aleph0_le_right ha hb'

theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ := by
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rcases eq_or_ne b 0 with (rfl | hb0); · simp
  rcases le_or_gt ℵ₀ a with ha | ha
  · rw [mul_eq_max_of_aleph0_le_left ha hb0]
    exact le_max_left _ _
  · rcases le_or_gt ℵ₀ b with hb | hb
    · rw [mul_comm, mul_eq_max_of_aleph0_le_left hb ha0, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (mul_lt_aleph0 ha hb).le

theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph0_le_left ha hb', max_eq_left hb]

theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']

theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) a
  rw [one_mul]

theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by
  rw [mul_comm]
  exact le_mul_left h

theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_gt ℵ₀ a with ha | ha
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_gt aleph0_pos
      left
      rw [and_assoc]
      use ha
      constructor
      · rw [← not_lt]
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
      · rintro rfl
        apply this
        rw [mul_zero] at h
        exact h.symm
    right
    by_cases h2a : a = 0
    · exact Or.inr h2a
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      exact h.symm
    left
    rw [← h, mul_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    · contradiction
    · contradiction
    rw [← Ne] at h2a
    rw [← one_le_iff_ne_zero] at h2a hb
    norm_cast at h2a hb h ⊢
    apply le_antisymm _ hb
    rw [← not_lt]
    apply fun h2b => ne_of_gt _ h
    conv_rhs => left; rw [← mul_one n]
    rw [Nat.mul_lt_mul_left]
    · exact id
    apply Nat.lt_of_succ_le h2a
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph0_le_left ha hb, max_eq_left hab]
    all_goals simp

end mul

/-! ### Properties of `add` -/
section add

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by
      convert mul_le_mul_right' ((nat_lt_aleph0 2).le.trans h) c using 1
      <;> simp [two_mul, mul_eq_self h])
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
  le_antisymm
      (add_eq_self (ha.trans (le_max_left a b)) ▸
        add_le_add (le_max_left _ _) (le_max_right _ _)) <|
    max_le (self_le_add_right _ _) (self_le_add_left _ _)

theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]

@[simp]
theorem add_mk_eq_max {α β : Type u} [Infinite α] : #α + #β = max #α #β :=
  add_eq_max (aleph0_le_mk α)

@[simp]
theorem add_mk_eq_max' {α β : Type u} [Infinite β] : #α + #β = max #α #β :=
  add_eq_max' (aleph0_le_mk β)

theorem add_mk_eq_self {α : Type*} [Infinite α] : #α + #α = #α := by
  simp

theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ := by
  rcases le_or_gt ℵ₀ a with ha | ha
  · rw [add_eq_max ha]
    exact le_max_left _ _
  · rcases le_or_gt ℵ₀ b with hb | hb
    · rw [add_comm, add_eq_max hb, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (add_lt_aleph0 ha hb).le

theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eq <| add_eq_self hc

theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  (add_le_add (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_ge (max a b) ℵ₀).elim (fun h => (add_lt_aleph0 h h).trans_le hc) fun h => by
      rw [add_eq_self h]; exact max_lt h1 h2

theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by
  apply le_antisymm
  · rw [← h]
    apply self_le_add_left
  rw [← not_lt]; intro hb
  have : a + b < c := add_lt_of_lt hc ha hb
  simp [h, lt_irrefl] at this

theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_left hb]

theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_comm, add_eq_left hb ha]

theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_gt ℵ₀ a with ha | ha
    · left
      use ha
      rw [← not_lt]
      apply fun hb => ne_of_gt _ h
      intro hb
      exact hb.trans_le (self_le_add_left b a)
    right
    rw [← h, add_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    norm_cast at h ⊢
    rw [← add_right_inj, h, add_zero]
  · rintro (⟨h1, h2⟩ | h3)
    · rw [add_eq_max h1, max_eq_left h2]
    · rw [h3, add_zero]

theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by
  rw [add_comm, add_eq_left_iff]

theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
  add_eq_left ha ((nat_lt_aleph0 _).le.trans ha)

theorem nat_add_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : n + a = a := by
  rw [add_comm, add_nat_eq n ha]

theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
  add_one_of_aleph0_le ha

theorem mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α :=
  add_one_eq (aleph0_le_mk α)

protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  rcases le_or_gt ℵ₀ b with hb | hb
  · have : a < b := ha.trans_le hb
    rw [add_eq_right hb this.le, eq_comm] at h
    rw [eq_of_add_eq_of_aleph0_le h this hb]
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph0 ha hb
    rw [lt_aleph0] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast at h ⊢
    apply add_left_cancel h

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb

end add

/-! ### Properties of `ciSup` -/
section ciSup

variable {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v})

section add

variable [Nonempty ι] [Nonempty ι']

protected theorem ciSup_add (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    (⨆ i, f i) + c = ⨆ i, f i + c := by
  have : ∀ i, f i + c ≤ (⨆ i, f i) + c := fun i ↦ add_le_add_right (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · + c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_ge (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isSuccLimit
      f hf (not_isSuccLimit_of_lt_aleph0 hs) rfl
    exact hi ▸ le_ciSup bdd i
  rw [add_eq_max hs, max_le_iff]
  exact ⟨ciSup_mono bdd fun i ↦ self_le_add_right _ c,
    (self_le_add_left _ _).trans (le_ciSup bdd <| Classical.arbitrary ι)⟩

protected theorem add_ciSup (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    c + (⨆ i, f i) = ⨆ i, c + f i := by
  rw [add_comm, Cardinal.ciSup_add f hf]; simp_rw [add_comm]

protected theorem ciSup_add_ciSup (hf : BddAbove (range f)) (g : ι' → Cardinal.{v})
    (hg : BddAbove (range g)) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ (i) (j), f i + g j := by
  simp_rw [Cardinal.ciSup_add f hf, Cardinal.add_ciSup g hg]

end add

protected theorem ciSup_mul (c : Cardinal.{v}) : (⨆ i, f i) * c = ⨆ i, f i * c := by
  cases isEmpty_or_nonempty ι; · simp
  obtain rfl | h0 := eq_or_ne c 0; · simp
  by_cases hf : BddAbove (range f); swap
  · have hfc : ¬ BddAbove (range (f · * c)) := fun bdd ↦ hf
      ⟨⨆ i, f i * c, forall_mem_range.mpr fun i ↦ (le_mul_right h0).trans (le_ciSup bdd i)⟩
    simp [iSup, csSup_of_not_bddAbove, hf, hfc]
  have : ∀ i, f i * c ≤ (⨆ i, f i) * c := fun i ↦ mul_le_mul_right' (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · * c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_ge (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isSuccLimit
      f hf (not_isSuccLimit_of_lt_aleph0 hs) rfl
    exact hi ▸ le_ciSup bdd i
  rw [mul_eq_max_of_aleph0_le_left hs h0, max_le_iff]
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup' (one_lt_aleph0.trans_le hs)
  exact ⟨ciSup_mono bdd fun i ↦ le_mul_right h0,
    (le_mul_left (zero_lt_one.trans hi).ne').trans (le_ciSup bdd i)⟩

protected theorem mul_ciSup (c : Cardinal.{v}) : c * (⨆ i, f i) = ⨆ i, c * f i := by
  rw [mul_comm, Cardinal.ciSup_mul f]; simp_rw [mul_comm]

protected theorem ciSup_mul_ciSup (g : ι' → Cardinal.{v}) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ (i) (j), f i * g j := by
  simp_rw [Cardinal.ciSup_mul f, Cardinal.mul_ciSup g]

theorem sum_eq_iSup_lift {f : ι → Cardinal.{max u v}} (hι : ℵ₀ ≤ #ι)
    (h : lift.{v} #ι ≤ iSup f) : sum f = iSup f := by
  apply (iSup_le_sum f).antisymm'
  convert sum_le_iSup_lift f
  rw [mul_eq_max (aleph0_le_lift.mpr hι) ((aleph0_le_lift.mpr hι).trans h), max_eq_right h]

theorem sum_eq_iSup {f : ι → Cardinal.{u}} (hι : ℵ₀ ≤ #ι) (h : #ι ≤ iSup f) : sum f = iSup f :=
  sum_eq_iSup_lift hι ((lift_id #ι).symm ▸ h)

end ciSup

/-! ### Properties of `aleph` -/
section aleph

@[simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ + ℵ_ o₂ = ℵ_ (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (aleph0_le_aleph o₁), aleph_max]

theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β :=
  ⟨fun h => Cardinal.eq_of_add_eq_add_right h γ₀, fun h => congr_arg (· + γ) h⟩

@[simp]
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β :=
  add_right_inj_of_lt_aleph0 (nat_lt_aleph0 _)

@[simp]
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β :=
  add_right_inj_of_lt_aleph0 one_lt_aleph0

theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < ℵ₀) :
    α + γ ≤ β + γ ↔ α ≤ β := by
  refine ⟨fun h => ?_, fun h => add_le_add_right h γ⟩
  contrapose h
  rw [not_le, lt_iff_le_and_ne, Ne] at h ⊢
  exact ⟨add_le_add_right h.1 γ, mt (add_right_inj_of_lt_aleph0 γ₀).1 h.2⟩

@[simp]
theorem add_nat_le_add_nat_iff {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 (nat_lt_aleph0 n)

@[simp]
theorem add_one_le_add_one_iff {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 one_lt_aleph0

end aleph

/-! ### Properties about `power` -/
section power

theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_aleph0.1 H2
  H3.symm ▸
    Quotient.inductionOn κ
      (fun α H1 =>
        Nat.recOn n
          (lt_of_lt_of_le
              (by
                rw [Nat.cast_zero, power_zero]
                exact one_lt_aleph0)
              H1).le
          fun n ih =>
          le_of_le_of_eq
            (by
              rw [Nat.cast_succ, power_add, power_one]
              exact mul_le_mul_right' ih _)
            (mul_eq_self H1))
      H1

theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2

theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c := by
  apply ((power_le_power_right <| (cantor c).le).trans _).antisymm
  · exact power_le_power_right ((nat_lt_aleph0 2).le.trans h)
  · rw [← power_mul, mul_eq_self h]

theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} #ι) : prod c = 2 ^ lift.{v} #ι := by
  rw [← lift_id'.{u, v} (prod.{u, v} c), lift_prod, ← lift_two_power]
  apply le_antisymm
  · refine (prod_le_prod _ _ h₂).trans_eq ?_
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph0_le_mk ι), lift_umax.{u, v}]
  · rw [← prod_const', lift_prod]
    refine prod_le_prod _ _ fun i => ?_
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    exact h₁ i

theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)

theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h (by assumption_mod_cast) ((nat_lt_aleph0 n).le.trans h)

theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c :=
  pow_le h (nat_lt_aleph0 n)

theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
  pow_eq h1 (mod_cast h2) (nat_lt_aleph0 n)

theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ := by
  rcases le_or_gt ℵ₀ c with hc | hc
  · exact le_max_of_le_left (power_nat_le hc)
  · exact le_max_of_le_right (power_lt_aleph0 hc (nat_lt_aleph0 _)).le

lemma power_le_aleph0 {a b : Cardinal.{u}} (ha : a ≤ ℵ₀) (hb : b < ℵ₀) : a ^ b ≤ ℵ₀ := by
  lift b to ℕ using hb; simpa [ha] using power_nat_le_max (c := a)

theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c := by
  apply le_antisymm
  · rw [powerlt_le]
    intro c'
    rw [lt_aleph0]
    rintro ⟨n, rfl⟩
    apply power_nat_le h
  convert le_powerlt c one_lt_aleph0; rw [power_one]

theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ := by
  rcases le_or_gt ℵ₀ c with h | h
  · rw [powerlt_aleph0 h]
    apply le_max_left
  rw [powerlt_le]
  exact fun c' hc' => (power_lt_aleph0 h hc').le.trans (le_max_right _ _)

end power

/-! ### Computing cardinality of various types -/
section computing

section Function

variable {α β : Type u} {β' : Type v}

theorem mk_equiv_eq_zero_iff_lift_ne : #(α ≃ β') = 0 ↔ lift.{v} #α ≠ lift.{u} #β' := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_eq']

theorem mk_equiv_eq_zero_iff_ne : #(α ≃ β) = 0 ↔ #α ≠ #β := by
  rw [mk_equiv_eq_zero_iff_lift_ne, lift_id, lift_id]

/-- This lemma makes lemmas assuming `Infinite α` applicable to the situation where we have
  `Infinite β` instead. -/
theorem mk_equiv_comm : #(α ≃ β') = #(β' ≃ α) :=
  (ofBijective _ symm_bijective).cardinal_eq

theorem mk_embedding_eq_zero_iff_lift_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v} #α := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_le', not_le]

theorem mk_embedding_eq_zero_iff_lt : #(α ↪ β) = 0 ↔ #β < #α := by
  rw [mk_embedding_eq_zero_iff_lift_lt, lift_lt]

theorem mk_arrow_eq_zero_iff : #(α → β') = 0 ↔ #α ≠ 0 ∧ #β' = 0 := by
  simp_rw [mk_eq_zero_iff, mk_ne_zero_iff, isEmpty_fun]

theorem mk_surjective_eq_zero_iff_lift :
    #{f : α → β' | Surjective f} = 0 ↔ lift.{v} #α < lift.{u} #β' ∨ (#α ≠ 0 ∧ #β' = 0) := by
  rw [← not_iff_not, not_or, not_lt, lift_mk_le', ← Ne, not_and_or, not_ne_iff, and_comm]
  simp_rw [mk_ne_zero_iff, mk_eq_zero_iff, nonempty_coe_sort,
    Set.Nonempty, mem_setOf, exists_surjective_iff, nonempty_fun]

theorem mk_surjective_eq_zero_iff :
    #{f : α → β | Surjective f} = 0 ↔ #α < #β ∨ (#α ≠ 0 ∧ #β = 0) := by
  rw [mk_surjective_eq_zero_iff_lift, lift_lt]

variable (α β')

theorem mk_equiv_le_embedding : #(α ≃ β') ≤ #(α ↪ β') := ⟨⟨_, Equiv.toEmbedding_injective⟩⟩

theorem mk_embedding_le_arrow : #(α ↪ β') ≤ #(α → β') := ⟨⟨_, DFunLike.coe_injective⟩⟩

variable [Infinite α] {α β'}

theorem mk_perm_eq_self_power : #(Equiv.Perm α) = #α ^ #α :=
  ((mk_equiv_le_embedding α α).trans (mk_embedding_le_arrow α α)).antisymm <| by
    suffices Nonempty ((α → Bool) ↪ Equiv.Perm (α × Bool)) by
      obtain ⟨e⟩ : Nonempty (α ≃ α × Bool) := by
        erw [← Cardinal.eq, mk_prod, lift_uzero, mk_bool,
          lift_natCast, mul_two, add_eq_self (aleph0_le_mk α)]
      erw [← le_def, mk_arrow, lift_uzero, mk_bool, lift_natCast 2] at this
      rwa [← power_def, power_self_eq (aleph0_le_mk α), e.permCongr.cardinal_eq]
    refine ⟨⟨fun f ↦ Involutive.toPerm (fun x ↦ ⟨x.1, xor (f x.1) x.2⟩) fun x ↦ ?_, fun f g h ↦ ?_⟩⟩
    · simp_rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    · ext a; rw [← (f a).xor_false, ← (g a).xor_false]; exact congr(($h ⟨a, false⟩).2)

theorem mk_perm_eq_two_power : #(Equiv.Perm α) = 2 ^ #α := by
  rw [mk_perm_eq_self_power, power_self_eq (aleph0_le_mk α)]

theorem mk_equiv_eq_arrow_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') :
    #(α ≃ β') = #(α → β') := by
  obtain ⟨e⟩ := lift_mk_eq'.mp leq
  have e₁ := lift_mk_eq'.mpr ⟨.equivCongr (.refl α) e⟩
  have e₂ := lift_mk_eq'.mpr ⟨.arrowCongr (.refl α) e⟩
  rw [lift_id'.{u,v}] at e₁ e₂
  rw [← e₁, ← e₂, lift_inj, mk_perm_eq_self_power, power_def]

theorem mk_equiv_eq_arrow_of_eq (eq : #α = #β) : #(α ≃ β) = #(α → β) :=
  mk_equiv_eq_arrow_of_lift_eq congr(lift $eq)

theorem mk_equiv_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = 2 ^ lift.{v} #α := by
  erw [← (lift_mk_eq'.2 ⟨.equivCongr (.refl α) (lift_mk_eq'.1 leq).some⟩).trans (lift_id'.{u,v} _),
    lift_umax.{u,v}, mk_perm_eq_two_power, lift_power, lift_natCast]; rfl

theorem mk_equiv_of_eq (eq : #α = #β) : #(α ≃ β) = 2 ^ #α := by
  rw [mk_equiv_of_lift_eq (lift_inj.mpr eq), lift_id]

theorem mk_embedding_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #(β' ↪ α) = #(β' → α) :=
  (mk_embedding_le_arrow _ _).antisymm <| by
    conv_rhs => rw [← (Equiv.embeddingCongr (.refl _)
      (Cardinal.eq.mp <| mul_eq_self <| aleph0_le_mk α).some).cardinal_eq]
    obtain ⟨e⟩ := lift_mk_le'.mp lle
    exact ⟨⟨fun f ↦ ⟨fun b ↦ ⟨e b, f b⟩, fun _ _ h ↦ e.injective congr(Prod.fst $h)⟩,
      fun f g h ↦ funext fun b ↦ congr(Prod.snd <| $h b)⟩⟩

theorem mk_embedding_eq_arrow_of_le (le : #β ≤ #α) : #(β ↪ α) = #(β → α) :=
  mk_embedding_eq_arrow_of_lift_le (lift_le.mpr le)

theorem mk_surjective_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #{f : α → β' | Surjective f} = #(α → β') :=
  (mk_set_le _).antisymm <|
    have ⟨e⟩ : Nonempty (α ≃ α ⊕ β') := by
      simp_rw [← lift_mk_eq', mk_sum, lift_add, lift_lift]; rw [lift_umax.{u,v}, eq_comm]
      exact add_eq_left (aleph0_le_lift.mpr <| aleph0_le_mk α) lle
    ⟨⟨fun f ↦ ⟨fun a ↦ (e a).elim f id, fun b ↦ ⟨e.symm (.inr b), congr_arg _ (e.right_inv _)⟩⟩,
      fun f g h ↦ funext fun a ↦ by
        simpa only [e.apply_symm_apply] using congr_fun (Subtype.ext_iff.mp h) (e.symm <| .inl a)⟩⟩

theorem mk_surjective_eq_arrow_of_le (le : #β ≤ #α) : #{f : α → β | Surjective f} = #(α → β) :=
  mk_surjective_eq_arrow_of_lift_le (lift_le.mpr le)

end Function

@[simp]
theorem mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α :=
  have H1 : ℵ₀ ≤ #α := aleph0_le_mk α
  Eq.symm <|
    le_antisymm ((le_def _ _).2 ⟨⟨fun a => [a], fun _ => by simp⟩⟩) <|
      calc
        #(List α) = sum fun n : ℕ => #α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun _ : ℕ => #α := sum_le_sum _ _ fun n => pow_le H1 <| nat_lt_aleph0 n
        _ = #α := by simp [H1]

theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀ :=
  mk_le_aleph0.antisymm (aleph0_le_mk _)

theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀ := by
  cases finite_or_infinite α
  · rw [mk_list_eq_aleph0, eq_comm, max_eq_right]
    exact mk_le_aleph0
  · rw [mk_list_eq_mk, eq_comm, max_eq_left]
    exact aleph0_le_mk α

theorem mk_list_le_max (α : Type u) : #(List α) ≤ max ℵ₀ #α := by
  cases finite_or_infinite α
  · exact mk_le_aleph0.trans (le_max_left _ _)
  · rw [mk_list_eq_mk]
    apply le_max_right

@[simp]
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α := by
  classical
  exact Eq.symm <|
    le_antisymm (mk_le_of_injective fun _ _ => Finset.singleton_inj.1) <|
      calc
        #(Finset α) ≤ #(List α) := mk_le_of_surjective List.toFinset_surjective
        _ = #α := mk_list_eq_mk α

theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ #α ^ c := by
  refine le_trans ?_ (by rw [← add_one_eq (aleph0_le_mk α)])
  induction c using Cardinal.inductionOn with | _ β
  fapply mk_le_of_surjective
  · intro f
    use Sum.inl ⁻¹' range f
    refine le_trans (mk_preimage_of_injective _ _ fun x y => Sum.inl.inj) ?_
    apply mk_range_le
  rintro ⟨s, ⟨g⟩⟩
  classical
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.choose h).val
               else Sum.inr (ULift.up 0)
  apply Subtype.eq; ext x
  constructor
  · rintro ⟨y, h⟩
    dsimp only at h
    by_cases h' : ∃ z : s, g z = y
    · rw [dif_pos h'] at h
      cases Sum.inl.inj h
      exact (Classical.choose h').2
    · rw [dif_neg h'] at h
      cases h
  · intro h
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    use g ⟨x, h⟩
    dsimp only
    rw [dif_pos this]
    congr
    suffices Classical.choose this = ⟨x, h⟩ from congr_arg Subtype.val this
    apply g.2
    exact Classical.choose_spec this

theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ max #α ℵ₀ ^ c := by
  trans #{ t : Set ((ULift.{u} ℕ) ⊕ α) // #t ≤ c }
  · refine ⟨Embedding.subtypeMap ?_ ?_⟩
    · apply Embedding.image
      use Sum.inr
      apply Sum.inr.inj
    intro s hs
    exact mk_image_le.trans hs
  apply (mk_bounded_set_le_of_infinite ((ULift.{u} ℕ) ⊕ α) c).trans
  rw [max_comm, ← add_eq_max] <;> rfl

theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    #{ t : Set α // t ⊆ s ∧ #t ≤ c } ≤ max #s ℵ₀ ^ c := by
  refine le_trans ?_ (mk_bounded_set_le s c)
  refine ⟨Embedding.codRestrict _ ?_ ?_⟩
  · use fun t => (↑) ⁻¹' t.1
    rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    apply Subtype.eq
    dsimp only at h ⊢
    refine (preimage_eq_preimage' ?_ ?_).1 h <;> rw [Subtype.range_coe] <;> assumption
  rintro ⟨t, _, h2t⟩; exact (mk_preimage_of_injective _ _ Subtype.val_injective).trans h2t

end computing

/-! ### Properties of `compl` -/
section compl

theorem mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
    #(sᶜ : Set α) = #α := by
  refine eq_of_add_eq_of_aleph0_le ?_ h2 (aleph0_le_mk α)
  exact mk_sum_compl s

theorem mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) :
    #((↑s)ᶜ : Set α) = #α := by
  apply mk_compl_of_infinite
  exact (finset_card_lt_aleph0 s).trans_le (aleph0_le_mk α)

theorem mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs : #s < #α)
    (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]

theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : (lift.{max v w, u} #α) = (lift.{max u w, v} #β))
    (h2 : lift.{max v w, u} #s = lift.{max u w, v} #t) :
    lift.{max v w} #(sᶜ : Set α) = lift.{max u w} #(tᶜ : Set β) := by
  cases nonempty_fintype α
  rcases lift_mk_eq.{u, v, w}.1 h1 with ⟨e⟩; letI : Fintype β := Fintype.ofEquiv α e
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.ofEquiv_card _).symm
  classical
    lift s to Finset α using s.toFinite
    lift t to Finset β using t.toFinite
    simp only [Finset.coe_sort_coe, mk_fintype, Fintype.card_coe, lift_natCast, Nat.cast_inj] at h2
    simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_coe_finset, Finset.card_compl,
      lift_natCast, Nat.cast_inj, h1, h2]

theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β) := by
  rw [← lift_inj.{u, u}]
  apply mk_compl_eq_mk_compl_finite_lift.{u, u, u}
  <;> rwa [lift_inj]

theorem mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h : #s = #t) :
    #(sᶜ : Set α) = #(tᶜ : Set α) :=
  mk_compl_eq_mk_compl_finite.{u} rfl h

end compl

/-! ### Extending an injection to an equiv -/
section extend

theorem extend_function {α β : Type*} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  classical
  have := h; obtain ⟨g⟩ := this
  let h : α ≃ β :=
    (Set.sumCompl (s : Set α)).symm.trans
      ((sumCongr (Equiv.ofInjective f f.2) g).trans (Set.sumCompl (range f)))
  refine ⟨h, ?_⟩; rintro ⟨x, hx⟩; simp [h, Set.sumCompl_symm_apply_of_mem, hx]

theorem extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  apply extend_function.{u, v} f
  obtain ⟨g⟩ := id h
  rw [← lift_mk_eq.{u, v, max u v}] at h
  rw [← lift_mk_eq.{u, v, max u v}, mk_compl_eq_mk_compl_finite_lift.{u, v, max u v} h]
  rw [mk_range_eq_lift.{u, v, max u v}]; exact f.2

theorem extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  cases fintypeOrInfinite α
  · exact extend_function_finite f h
  · apply extend_function f
    obtain ⟨g⟩ := id h
    haveI := Infinite.of_injective _ g.injective
    rw [← lift_mk_eq'] at h ⊢
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]

end extend
end Cardinal
