/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.SetTheory.Cardinal.UnivLE

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limitRecOn`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `Order.succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We discuss the properties of casts of natural numbers of and of `ω` with respect to these
operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `IsLimit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limitRecOn` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.
* `IsNormal`: a function `f : Ordinal → Ordinal` satisfies `IsNormal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `sup`, `lsub`: the supremum / least strict upper bound of an indexed family of ordinals in
  `Type u`, as an ordinal in `Type u`.
* `bsup`, `blsub`: the supremum / least strict upper bound of a set of ordinals indexed by ordinals
  less than a given ordinal `o`.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

assert_not_exists Field
assert_not_exists Module

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Ordinal

universe u v w

namespace Ordinal

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Further properties of addition on ordinals -/

@[simp]
theorem lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift.{u} a + lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equiv.ulift _) (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
theorem lift_succ (a : Ordinal.{v}) : lift.{u} (succ a) = succ (lift.{u} a) := by
  rw [← add_one_eq_succ, lift_add, lift_one]
  rfl

instance instAddLeftReflectLE :
    AddLeftReflectLE Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦ ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : ∃ b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h ↦ ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]

theorem add_left_cancel (a) {b c : Ordinal} : a + b = a + c ↔ b = c := by
  simp only [le_antisymm_iff, add_le_add_iff_left]

private theorem add_lt_add_iff_left' (a) {b c : Ordinal} : a + b < a + c ↔ b < c := by
  rw [← not_le, ← not_le, add_le_add_iff_left]

instance instAddLeftStrictMono : AddLeftStrictMono Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).2⟩

instance instAddLeftReflectLT : AddLeftReflectLT Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).1⟩

instance instAddRightReflectLT : AddRightReflectLT Ordinal.{u} :=
  ⟨fun _a _b _c ↦ lt_imp_lt_of_le_imp_le fun h => add_le_add_right h _⟩

theorem add_le_add_iff_right {a b : Ordinal} : ∀ n : ℕ, a + n ≤ b + n ↔ a ≤ b
  | 0 => by simp
  | n + 1 => by
    simp only [natCast_succ, add_succ, add_succ, succ_le_succ_iff, add_le_add_iff_right]

theorem add_right_cancel {a b : Ordinal} (n : ℕ) : a + n = b + n ↔ a = b := by
  simp only [le_antisymm_iff, add_le_add_iff_right]

theorem add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  inductionOn₂ a b fun α r _ β s _ => by
    simp_rw [← type_sum_lex, type_eq_zero_iff_isEmpty]
    exact isEmpty_sum

theorem left_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : a = 0 :=
  (add_eq_zero_iff.1 h).1

theorem right_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : b = 0 :=
  (add_eq_zero_iff.1 h).2

/-! ### The predecessor of an ordinal -/

open Classical in
/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : Ordinal) : Ordinal :=
  if h : ∃ a, o = succ a then Classical.choose h else o

@[simp]
theorem pred_succ (o) : pred (succ o) = o := by
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩
  simpa only [pred, dif_pos h] using (succ_injective <| Classical.choose_spec h).symm

theorem pred_le_self (o) : pred o ≤ o := by
  classical
  exact if h : ∃ a, o = succ a then by
    let ⟨a, e⟩ := h
    rw [e, pred_succ]; exact le_succ a
  else by rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬∃ a, o = succ a :=
  ⟨fun e ⟨a, e'⟩ => by rw [e', pred_succ] at e; exact (lt_succ a).ne e, fun h => dif_neg h⟩

theorem pred_eq_iff_not_succ' {o} : pred o = o ↔ ∀ a, o ≠ succ a := by
  simpa using pred_eq_iff_not_succ

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
  Iff.trans (by simp only [le_antisymm_iff, pred_le_self, true_and, not_le])
    (iff_not_comm.1 pred_eq_iff_not_succ).symm

@[simp]
theorem pred_zero : pred 0 = 0 :=
  pred_eq_iff_not_succ'.2 fun a => (succ_ne_zero a).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
  ⟨fun e => ⟨_, e.symm⟩, fun ⟨a, e⟩ => by simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o b : Ordinal} (h : ¬∃ a, o = succ a) : succ b < o ↔ b < o :=
  ⟨(lt_succ b).trans, fun l => lt_of_le_of_ne (succ_le_of_lt l) fun e => h ⟨_, e.symm⟩⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b := by
  classical
  exact if h : ∃ a, b = succ a then by
    let ⟨c, e⟩ := h
    rw [e, pred_succ, succ_lt_succ_iff]
  else by simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
  le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp]
theorem lift_is_succ {o : Ordinal.{v}} : (∃ a, lift.{u} o = succ a) ↔ ∃ a, o = succ a :=
  ⟨fun ⟨a, h⟩ =>
    let ⟨b, e⟩ := mem_range_lift_of_le <| show a ≤ lift.{u} o from le_of_lt <| h.symm ▸ lt_succ a
    ⟨b, (lift_inj.{u,v}).1 <| by rw [h, ← e, lift_succ]⟩,
    fun ⟨a, h⟩ => ⟨lift.{u} a, by simp only [h, lift_succ]⟩⟩

@[simp]
theorem lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o) := by
  classical
  exact if h : ∃ a, o = succ a then by cases' h with a e; simp only [e, pred_succ, lift_succ]
  else by rw [pred_eq_iff_not_succ.2 h, pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-! ### Limit ordinals -/


/-- A limit ordinal is an ordinal which is not zero and not a successor.

TODO: deprecate this in favor of `Order.IsSuccLimit`. -/
def IsLimit (o : Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ a < o, succ a < o

theorem IsLimit.isSuccPrelimit {o} (h : IsLimit o) : IsSuccPrelimit o :=
  isSuccPrelimit_iff_succ_lt.mpr h.2

@[deprecated IsLimit.isSuccPrelimit (since := "2024-09-05")]
alias IsLimit.isSuccLimit := IsLimit.isSuccPrelimit

theorem IsLimit.succ_lt {o a : Ordinal} (h : IsLimit o) : a < o → succ a < o :=
  h.2 a

theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal) := isSuccPrelimit_bot

@[deprecated isSuccPrelimit_zero (since := "2024-09-05")]
alias isSuccLimit_zero := isSuccPrelimit_zero

theorem not_zero_isLimit : ¬IsLimit 0
  | ⟨h, _⟩ => h rfl

theorem not_succ_isLimit (o) : ¬IsLimit (succ o)
  | ⟨_, h⟩ => lt_irrefl _ (h _ (lt_succ o))

theorem not_succ_of_isLimit {o} (h : IsLimit o) : ¬∃ a, o = succ a
  | ⟨a, e⟩ => not_succ_isLimit a (e ▸ h)

theorem succ_lt_of_isLimit {o a : Ordinal} (h : IsLimit o) : succ a < o ↔ a < o :=
  ⟨(lt_succ a).trans, h.2 _⟩

theorem le_succ_of_isLimit {o} (h : IsLimit o) {a} : o ≤ succ a ↔ o ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 <| succ_lt_of_isLimit h

theorem limit_le {o} (h : IsLimit o) {a} : o ≤ a ↔ ∀ x < o, x ≤ a :=
  ⟨fun h _x l => l.le.trans h, fun H =>
    (le_succ_of_isLimit h).1 <| le_of_not_lt fun hn => not_lt_of_le (H _ hn) (lt_succ a)⟩

theorem lt_limit {o} (h : IsLimit o) {a} : a < o ↔ ∃ x < o, a < x := by
  -- Porting note: `bex_def` is required.
  simpa only [not_forall₂, not_le, bex_def] using not_congr (@limit_le _ h a)

@[simp]
theorem lift_isLimit (o : Ordinal.{v}) : IsLimit (lift.{u,v} o) ↔ IsLimit o :=
  and_congr (not_congr <| by simpa only [lift_zero] using @lift_inj o 0)
    ⟨fun H a h => (lift_lt.{u,v}).1 <|
      by simpa only [lift_succ] using H _ (lift_lt.2 h), fun H a h => by
        obtain ⟨a', rfl⟩ := mem_range_lift_of_le h.le
        rw [← lift_succ, lift_lt]
        exact H a' (lift_lt.1 h)⟩

theorem IsLimit.pos {o : Ordinal} (h : IsLimit o) : 0 < o :=
  lt_of_le_of_ne (Ordinal.zero_le _) h.1.symm

theorem IsLimit.one_lt {o : Ordinal} (h : IsLimit o) : 1 < o := by
  simpa only [succ_zero] using h.2 _ h.pos

theorem IsLimit.nat_lt {o : Ordinal} (h : IsLimit o) : ∀ n : ℕ, (n : Ordinal) < o
  | 0 => h.pos
  | n + 1 => h.2 _ (IsLimit.nat_lt h n)

theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ IsLimit o := by
  classical
  exact if o0 : o = 0 then Or.inl o0
  else
    if h : ∃ a, o = succ a then Or.inr (Or.inl h)
    else Or.inr <| Or.inr ⟨o0, fun _a => (succ_lt_of_not_succ h).2⟩

theorem isLimit_of_not_succ_of_ne_zero {o : Ordinal} (h : ¬∃ a, o = succ a) (h' : o ≠ 0) :
    IsLimit o := ((zero_or_succ_or_limit o).resolve_left h').resolve_left h

-- TODO: this is an iff with `IsSuccPrelimit`
theorem IsLimit.sSup_Iio {o : Ordinal} (h : IsLimit o) : sSup (Iio o) = o := by
  apply (csSup_le' (fun a ha ↦ le_of_lt ha)).antisymm
  apply le_of_forall_lt
  intro a ha
  exact (lt_succ a).trans_le (le_csSup bddAbove_Iio (h.succ_lt ha))

theorem IsLimit.iSup_Iio {o : Ordinal} (h : IsLimit o) : ⨆ a : Iio o, a.1 = o := by
  rw [← sSup_eq_iSup', h.sSup_Iio]

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_elim]
def limitRecOn {C : Ordinal → Sort*} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
    (H₃ : ∀ o, IsLimit o → (∀ o' < o, C o') → C o) : C o :=
  SuccOrder.prelimitRecOn o (fun o _ ↦ H₂ o) fun o hl ↦
    if h : o = 0 then fun _ ↦ h ▸ H₁ else H₃ o ⟨h, fun _ ↦ hl.succ_lt⟩

@[simp]
theorem limitRecOn_zero {C} (H₁ H₂ H₃) : @limitRecOn C 0 H₁ H₂ H₃ = H₁ := by
  rw [limitRecOn, SuccOrder.prelimitRecOn_of_isSuccPrelimit _ _ isSuccPrelimit_zero, dif_pos rfl]

@[simp]
theorem limitRecOn_succ {C} (o H₁ H₂ H₃) :
    @limitRecOn C (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn C o H₁ H₂ H₃) := by
  rw [limitRecOn, limitRecOn, SuccOrder.prelimitRecOn_succ]

@[simp]
theorem limitRecOn_limit {C} (o H₁ H₂ H₃ h) :
    @limitRecOn C o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn C x H₁ H₂ H₃ := by
  simp_rw [limitRecOn, SuccOrder.prelimitRecOn_of_isSuccPrelimit _ _ h.isSuccPrelimit, dif_neg h.1]

/-- Bounded recursion on ordinals. Similar to `limitRecOn`, with the assumption `o < l`
  added to all cases. The final term's domain is the ordinals below `l`. -/
@[elab_as_elim]
def boundedLimitRecOn {l : Ordinal} (lLim : l.IsLimit) {C : Iio l → Sort*} (o : Iio l)
    (H₁ : C ⟨0, lLim.pos⟩) (H₂ : (o : Iio l) → C o → C ⟨succ o, lLim.succ_lt o.2⟩)
    (H₃ : (o : Iio l) → IsLimit o → (Π o' < o, C o') → C o) : C o :=
  limitRecOn (C := fun p ↦ (h : p < l) → C ⟨p, h⟩) o.1 (fun _ ↦ H₁)
    (fun o ih h ↦ H₂ ⟨o, _⟩ <| ih <| (lt_succ o).trans h)
    (fun _o ho ih _ ↦ H₃ _ ho fun _o' h ↦ ih _ h _) o.2

@[simp]
theorem boundedLimitRec_zero {l} (lLim : l.IsLimit) {C} (H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨0, lLim.pos⟩ H₁ H₂ H₃ = H₁ := by
  rw [boundedLimitRecOn, limitRecOn_zero]

@[simp]
theorem boundedLimitRec_succ {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨succ o.1, lLim.succ_lt o.2⟩ H₁ H₂ H₃ = H₂ o
    (@boundedLimitRecOn l lLim C o H₁ H₂ H₃) := by
  rw [boundedLimitRecOn, limitRecOn_succ]
  rfl

theorem boundedLimitRec_limit {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃ oLim) :
    @boundedLimitRecOn l lLim C o H₁ H₂ H₃ = H₃ o oLim (fun x _ ↦
    @boundedLimitRecOn l lLim C x H₁ H₂ H₃) := by
  rw [boundedLimitRecOn, limitRecOn_limit]
  rfl

instance orderTopToTypeSucc (o : Ordinal) : OrderTop (succ o).toType :=
  @OrderTop.mk _ _ (Top.mk _) le_enum_succ

theorem enum_succ_eq_top {o : Ordinal} :
    enum (α := (succ o).toType) (· < ·) ⟨o, type_toType _ ▸ lt_succ o⟩ = ⊤ :=
  rfl

theorem has_succ_of_type_succ_lt {α} {r : α → α → Prop} [wo : IsWellOrder α r]
    (h : ∀ a < type r, succ a < type r) (x : α) : ∃ y, r x y := by
  use enum r ⟨succ (typein r x), h _ (typein_lt_type r x)⟩
  convert enum_lt_enum (o₁ := ⟨_, typein_lt_type r x⟩) (o₂ := ⟨_, h _ (typein_lt_type r x)⟩).mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

theorem toType_noMax_of_succ_lt {o : Ordinal} (ho : ∀ a < o, succ a < o) : NoMaxOrder o.toType :=
  ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

@[deprecated toType_noMax_of_succ_lt (since := "2024-08-26")]
alias out_no_max_of_succ_lt := toType_noMax_of_succ_lt

theorem bounded_singleton {r : α → α → Prop} [IsWellOrder α r] (hr : (type r).IsLimit) (x) :
    Bounded r {x} := by
  refine ⟨enum r ⟨succ (typein r x), hr.2 _ (typein_lt_type r x)⟩, ?_⟩
  intro b hb
  rw [mem_singleton_iff.1 hb]
  nth_rw 1 [← enum_typein r x]
  rw [@enum_lt_enum _ r, Subtype.mk_lt_mk]
  apply lt_succ

@[simp]
theorem typein_ordinal (o : Ordinal.{u}) :
    @typein Ordinal (· < ·) _ o = Ordinal.lift.{u + 1} o := by
  refine Quotient.inductionOn o ?_
  rintro ⟨α, r, wo⟩; apply Quotient.sound
  constructor; refine ((RelIso.preimage Equiv.ulift r).trans (enum r).symm).symm

-- Porting note: `· < ·` requires a type ascription for an `IsWellOrder` instance.
@[deprecated typein_ordinal (since := "2024-09-19")]
theorem type_subrel_lt (o : Ordinal.{u}) :
    type (@Subrel Ordinal (· < ·) { o' : Ordinal | o' < o }) = Ordinal.lift.{u + 1} o :=
  typein_ordinal o

theorem mk_Iio_ordinal (o : Ordinal.{u}) :
    #(Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [lift_card, ← typein_ordinal]
  rfl

@[deprecated mk_Iio_ordinal (since := "2024-09-19")]
theorem mk_initialSeg (o : Ordinal.{u}) :
    #{ o' : Ordinal | o' < o } = Cardinal.lift.{u + 1} o.card := mk_Iio_ordinal o


/-! ### Normal ordinal functions -/


/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`. -/
def IsNormal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, IsLimit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a

theorem IsNormal.limit_le {f} (H : IsNormal f) :
    ∀ {o}, IsLimit o → ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a :=
  @H.2

theorem IsNormal.limit_lt {f} (H : IsNormal f) {o} (h : IsLimit o) {a} :
    a < f o ↔ ∃ b < o, a < f b :=
  not_iff_not.1 <| by simpa only [exists_prop, not_exists, not_and, not_lt] using H.2 _ h a

theorem IsNormal.strictMono {f} (H : IsNormal f) : StrictMono f := fun a b =>
  limitRecOn b (Not.elim (not_lt_of_le <| Ordinal.zero_le _))
    (fun _b IH h =>
      (lt_or_eq_of_le (le_of_lt_succ h)).elim (fun h => (IH h).trans (H.1 _)) fun e => e ▸ H.1 _)
    fun _b l _IH h => lt_of_lt_of_le (H.1 a) ((H.2 _ l _).1 le_rfl _ (l.2 _ h))

theorem IsNormal.monotone {f} (H : IsNormal f) : Monotone f :=
  H.strictMono.monotone

theorem isNormal_iff_strictMono_limit (f : Ordinal → Ordinal) :
    IsNormal f ↔ StrictMono f ∧ ∀ o, IsLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a :=
  ⟨fun hf => ⟨hf.strictMono, fun a ha c => (hf.2 a ha c).2⟩, fun ⟨hs, hl⟩ =>
    ⟨fun a => hs (lt_succ a), fun a ha c =>
      ⟨fun hac _b hba => ((hs hba).trans_le hac).le, hl a ha c⟩⟩⟩

theorem IsNormal.lt_iff {f} (H : IsNormal f) {a b} : f a < f b ↔ a < b :=
  StrictMono.lt_iff_lt <| H.strictMono

theorem IsNormal.le_iff {f} (H : IsNormal f) {a b} : f a ≤ f b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem IsNormal.inj {f} (H : IsNormal f) {a b} : f a = f b ↔ a = b := by
  simp only [le_antisymm_iff, H.le_iff]

theorem IsNormal.id_le {f} (H : IsNormal f) : id ≤ f :=
  H.strictMono.id_le

theorem IsNormal.le_apply {f} (H : IsNormal f) {a} : a ≤ f a :=
  H.strictMono.le_apply

@[deprecated IsNormal.le_apply (since := "2024-09-11")]
theorem IsNormal.self_le {f} (H : IsNormal f) (a) : a ≤ f a :=
  H.strictMono.le_apply

theorem IsNormal.le_iff_eq {f} (H : IsNormal f) {a} : f a ≤ a ↔ f a = a :=
  H.le_apply.le_iff_eq

theorem IsNormal.le_set {f o} (H : IsNormal f) (p : Set Ordinal) (p0 : p.Nonempty) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f a ≤ o :=
  ⟨fun h _ pa => (H.le_iff.2 ((H₂ _).1 le_rfl _ pa)).trans h, fun h => by
    -- Porting note: `refine'` didn't work well so `induction` is used
    induction b using limitRecOn with
    | H₁ =>
      cases' p0 with x px
      have := Ordinal.le_zero.1 ((H₂ _).1 (Ordinal.zero_le _) _ px)
      rw [this] at px
      exact h _ px
    | H₂ S _ =>
      rcases not_forall₂.1 (mt (H₂ S).2 <| (lt_succ S).not_le) with ⟨a, h₁, h₂⟩
      exact (H.le_iff.2 <| succ_le_of_lt <| not_le.1 h₂).trans (h _ h₁)
    | H₃ S L _ =>
      refine (H.2 _ L _).2 fun a h' => ?_
      rcases not_forall₂.1 (mt (H₂ a).2 h'.not_le) with ⟨b, h₁, h₂⟩
      exact (H.le_iff.2 <| (not_le.1 h₂).le).trans (h _ h₁)⟩

theorem IsNormal.le_set' {f o} (H : IsNormal f) (p : Set α) (p0 : p.Nonempty) (g : α → Ordinal) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, g a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f (g a) ≤ o := by
  simpa [H₂] using H.le_set (g '' p) (p0.image g) b

theorem IsNormal.refl : IsNormal id :=
  ⟨lt_succ, fun _o l _a => Ordinal.limit_le l⟩

theorem IsNormal.trans {f g} (H₁ : IsNormal f) (H₂ : IsNormal g) : IsNormal (f ∘ g) :=
  ⟨fun _x => H₁.lt_iff.2 (H₂.1 _), fun o l _a =>
    H₁.le_set' (· < o) ⟨0, l.pos⟩ g _ fun _c => H₂.2 _ l _⟩

theorem IsNormal.isLimit {f} (H : IsNormal f) {o} (l : IsLimit o) : IsLimit (f o) :=
  ⟨ne_of_gt <| (Ordinal.zero_le _).trans_lt <| H.lt_iff.2 l.pos, fun _ h =>
    let ⟨_b, h₁, h₂⟩ := (H.limit_lt l).1 h
    (succ_le_of_lt h₂).trans_lt (H.lt_iff.2 h₁)⟩

theorem add_le_of_limit {a b c : Ordinal} (h : IsLimit b) : a + b ≤ c ↔ ∀ b' < b, a + b' ≤ c :=
  ⟨fun h _ l => (add_le_add_left l.le _).trans h, fun H =>
    le_of_not_lt <| by
      -- Porting note: `induction` tactics are required because of the parser bug.
      induction a using inductionOn with
      | H α r =>
        induction b using inductionOn with
        | H β s =>
          intro l
          suffices ∀ x : β, Sum.Lex r s (Sum.inr x) (enum _ ⟨_, l⟩) by
            -- Porting note: `revert` & `intro` is required because `cases'` doesn't replace
            --               `enum _ _ l` in `this`.
            revert this; cases' enum _ ⟨_, l⟩ with x x <;> intro this
            · cases this (enum s ⟨0, h.pos⟩)
            · exact irrefl _ (this _)
          intro x
          rw [← typein_lt_typein (Sum.Lex r s), typein_enum]
          have := H _ (h.2 _ (typein_lt_type s x))
          rw [add_succ, succ_le_iff] at this
          refine
            (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
          · rcases a with ⟨a | b, h⟩
            · exact Sum.inl a
            · exact Sum.inr ⟨b, by cases h; assumption⟩
          · rcases a with ⟨a | a, h₁⟩ <;> rcases b with ⟨b | b, h₂⟩ <;> cases h₁ <;> cases h₂ <;>
              rintro ⟨⟩ <;> constructor <;> assumption⟩

theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) :=
  ⟨fun b => (add_lt_add_iff_left a).2 (lt_succ b), fun _b l _c => add_le_of_limit l⟩

@[deprecated isNormal_add_right (since := "2024-10-11")]
alias add_isNormal := isNormal_add_right

theorem isLimit_add (a) {b} : IsLimit b → IsLimit (a + b) :=
  (isNormal_add_right a).isLimit

@[deprecated isLimit_add (since := "2024-10-11")]
alias add_isLimit := isLimit_add

alias IsLimit.add := add_isLimit

/-! ### Subtraction on ordinals -/


/-- The set in the definition of subtraction is nonempty. -/
private theorem sub_nonempty {a b : Ordinal} : { o | a ≤ b + o }.Nonempty :=
  ⟨a, le_add_left _ _⟩

/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
instance sub : Sub Ordinal :=
  ⟨fun a b => sInf { o | a ≤ b + o }⟩

theorem le_add_sub (a b : Ordinal) : a ≤ b + (a - b) :=
  csInf_mem sub_nonempty

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b + c :=
  ⟨fun h => (le_add_sub a b).trans (add_le_add_left h _), fun h => csInf_le' h⟩

theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : Ordinal) : a + b - a = b :=
  le_antisymm (sub_le.2 <| le_rfl) ((add_le_add_iff_left a).1 <| le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : Ordinal) : a - b ≤ a :=
  sub_le.2 <| le_add_left _ _

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : b + (a - b) = a :=
  (le_add_sub a b).antisymm'
    (by
      rcases zero_or_succ_or_limit (a - b) with (e | ⟨c, e⟩ | l)
      · simp only [e, add_zero, h]
      · rw [e, add_succ, succ_le_iff, ← lt_sub, e]
        exact lt_succ c
      · exact (add_le_of_limit l).2 fun c l => (lt_sub.1 l).le)

theorem le_sub_of_le {a b c : Ordinal} (h : b ≤ a) : c ≤ a - b ↔ b + c ≤ a := by
  rw [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h]

theorem sub_lt_of_le {a b c : Ordinal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
  lt_iff_lt_of_le_iff_le (le_sub_of_le h)

instance existsAddOfLE : ExistsAddOfLE Ordinal :=
  ⟨fun h => ⟨_, (Ordinal.add_sub_cancel_of_le h).symm⟩⟩

@[simp]
theorem sub_zero (a : Ordinal) : a - 0 = a := by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by rw [← Ordinal.le_zero]; apply sub_le_self

@[simp]
theorem sub_self (a : Ordinal) : a - a = 0 := by simpa only [add_zero] using add_sub_cancel a 0

protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b, fun h => by
    rwa [← Ordinal.le_zero, sub_le, add_zero]⟩

theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) :=
  eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]
theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by
  rw [← sub_sub, add_sub_cancel]

theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c ≤ a) : c ≤ a - b := by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by
  obtain hab | hba := lt_or_le a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

theorem lt_add_iff {a b c : Ordinal} (hc : c ≠ 0) : a < b + c ↔ ∃ d < c, a ≤ b + d := by
  use fun h ↦ ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (add_lt_add_left hd b)

theorem isLimit_sub {a b} (l : IsLimit a) (h : b < a) : IsLimit (a - b) :=
  ⟨ne_of_gt <| lt_sub.2 <| by rwa [add_zero], fun c h => by
    rw [lt_sub, add_succ]; exact l.2 _ (lt_sub.1 h)⟩

@[deprecated isLimit_sub (since := "2024-10-11")]
alias sub_isLimit := isLimit_sub

theorem one_add_omega0 : 1 + ω = ω := by
  refine le_antisymm ?_ (le_add_left _ _)
  rw [omega0, ← lift_one.{0}, ← lift_add, lift_le, ← type_unit, ← type_sum_lex]
  refine ⟨RelEmbedding.collapse (RelEmbedding.ofMonotone ?_ ?_)⟩
  · apply Sum.rec
    · exact fun _ => 0
    · exact Nat.succ
  · intro a b
    cases a <;> cases b <;> intro H <;> cases' H with _ _ H _ _ H <;>
      [exact H.elim; exact Nat.succ_pos _; exact Nat.succ_lt_succ H]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_add_omega := one_add_omega0

@[simp]
theorem one_add_of_omega0_le {o} (h : ω ≤ o) : 1 + o = o := by
  rw [← Ordinal.add_sub_cancel_of_le h, ← add_assoc, one_add_omega0]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_add_of_omega_le := one_add_of_omega0_le

/-! ### Multiplication of ordinals -/


/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance monoid : Monoid Ordinal.{u} where
  mul a b :=
    Quotient.liftOn₂ a b
      (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧ :
        WellOrder → WellOrder → Ordinal)
      fun ⟨_, _, _⟩ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  one := 1
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Eq.symm <|
        Quotient.sound
          ⟨⟨prodAssoc _ _ _, @fun a b => by
              rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
              rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
              simp [Prod.lex_def, and_or_left, or_assoc, and_assoc]⟩⟩
  mul_one a :=
    inductionOn a fun α r _ =>
      Quotient.sound
        ⟨⟨punitProd _, @fun a b => by
            rcases a with ⟨⟨⟨⟩⟩, a⟩; rcases b with ⟨⟨⟨⟩⟩, b⟩
            simp only [Prod.lex_def, EmptyRelation, false_or]
            simp only [eq_self_iff_true, true_and]
            rfl⟩⟩
  one_mul a :=
    inductionOn a fun α r _ =>
      Quotient.sound
        ⟨⟨prodPUnit _, @fun a b => by
            rcases a with ⟨a, ⟨⟨⟩⟩⟩; rcases b with ⟨b, ⟨⟨⟩⟩⟩
            simp only [Prod.lex_def, EmptyRelation, and_false, or_false]
            rfl⟩⟩

@[simp]
theorem type_prod_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Prod.Lex s r) = type r * type s :=
  rfl

private theorem mul_eq_zero' {a b : Ordinal} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  inductionOn a fun α _ _ =>
    inductionOn b fun β _ _ => by
      simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty]
      rw [or_comm]
      exact isEmpty_prod

instance monoidWithZero : MonoidWithZero Ordinal :=
  { Ordinal.monoid with
    zero := 0
    mul_zero := fun _a => mul_eq_zero'.2 <| Or.inr rfl
    zero_mul := fun _a => mul_eq_zero'.2 <| Or.inl rfl }

instance noZeroDivisors : NoZeroDivisors Ordinal :=
  ⟨fun {_ _} => mul_eq_zero'.1⟩

@[simp]
theorem lift_mul (a b : Ordinal.{v}) : lift.{u} (a * b) = lift.{u} a * lift.{u} b :=
  Quotient.inductionOn₂ a b fun ⟨_α, _r, _⟩ ⟨_β, _s, _⟩ =>
    Quotient.sound
      ⟨(RelIso.preimage Equiv.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equiv.ulift _)
              (RelIso.preimage Equiv.ulift _)).symm⟩

@[simp]
theorem card_mul (a b) : card (a * b) = card a * card b :=
  Quotient.inductionOn₂ a b fun ⟨α, _r, _⟩ ⟨β, _s, _⟩ => mul_comm #β #α

instance leftDistribClass : LeftDistribClass Ordinal.{u} :=
  ⟨fun a b c =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quotient.sound
        ⟨⟨sumProdDistrib _ _ _, by
          rintro ⟨a₁ | a₁, a₂⟩ ⟨b₁ | b₁, b₂⟩ <;>
            simp only [Prod.lex_def, Sum.lex_inl_inl, Sum.Lex.sep, Sum.lex_inr_inl, Sum.lex_inr_inr,
              sumProdDistrib_apply_left, sumProdDistrib_apply_right, reduceCtorEq] <;>
            -- Porting note: `Sum.inr.inj_iff` is required.
            simp only [Sum.inl.inj_iff, Sum.inr.inj_iff, true_or, false_and, false_or]⟩⟩⟩

theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a :=
  mul_add_one a b

instance mulLeftMono : MulLeftMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

instance mulRightMono : MulRightMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ a * b := by
  convert mul_le_mul_left' (one_le_iff_pos.2 hb) a
  rw [mul_one a]

theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_pos.2 hb) a
  rw [one_mul a]

private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
    (h : IsLimit (type s)) (H : ∀ b' < type s, type r * b' ≤ c) (l : c < type r * type s) :
    False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) by
    cases' enum _ ⟨_, l⟩ with b a
    exact irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r), typein_enum]
  have := H _ (h.2 _ (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · refine Sum.inr ⟨a', ?_⟩
      subst e
      cases' h with _ _ _ _ h _ _ _ h
      · exact (irrefl _ h).elim
      · exact h
    · refine Sum.inl (⟨b', ?_⟩, a')
      cases' h with _ _ _ _ h _ _ _ h
      · exact h
      · exact (e rfl).elim
  · rcases a with ⟨⟨b₁, a₁⟩, h₁⟩
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩
    intro h
    by_cases e₁ : b = b₁ <;> by_cases e₂ : b = b₂
    · substs b₁ b₂
      simpa only [subrel_val, Prod.lex_def, @irrefl _ s _ b, true_and, false_or,
        eq_self_iff_true, dif_pos, Sum.lex_inr_inr] using h
    · subst b₁
      simp only [subrel_val, Prod.lex_def, e₂, Prod.lex_def, dif_pos, subrel_val, eq_self_iff_true,
        or_false, dif_neg, not_false_iff, Sum.lex_inr_inl, false_and] at h ⊢
      cases' h₂ with _ _ _ _ h₂_h h₂_h <;> [exact asymm h h₂_h; exact e₂ rfl]
    · simp [e₂, dif_neg e₁, show b₂ ≠ b₁ from e₂ ▸ e₁]
    · simpa only [dif_neg e₁, dif_neg e₂, Prod.lex_def, subrel_val, Subtype.mk_eq_mk,
        Sum.lex_inl_inl] using h

theorem mul_le_of_limit {a b c : Ordinal} (h : IsLimit b) : a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c :=
  ⟨fun h _ l => (mul_le_mul_left' l.le _).trans h, fun H =>
    -- Porting note: `induction` tactics are required because of the parser bug.
    le_of_not_lt <| by
      induction a using inductionOn with
      | H α r =>
        induction b using inductionOn with
        | H β s =>
          exact mul_le_of_limit_aux h H⟩

theorem isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·) :=
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/12129): additional beta reduction needed
  ⟨fun b => by
      beta_reduce
      rw [mul_succ]
      simpa only [add_zero] using (add_lt_add_iff_left (a * b)).2 h,
    fun _ l _ => mul_le_of_limit l⟩

@[deprecated isNormal_mul_right (since := "2024-10-11")]
alias mul_isNormal := isNormal_mul_right

theorem lt_mul_of_limit {a b c : Ordinal} (h : IsLimit c) : a < b * c ↔ ∃ c' < c, a < b * c' := by
  -- Porting note: `bex_def` is required.
  simpa only [not_forall₂, not_le, bex_def] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  (isNormal_mul_right a0).lt_iff

theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  (isNormal_mul_right a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : c * a < c * b :=
  (mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : Ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  simpa only [Ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
  le_imp_le_of_lt_imp_lt (fun h' => mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a b c : Ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  (isNormal_mul_right a0).inj

theorem isLimit_mul {a b : Ordinal} (a0 : 0 < a) : IsLimit b → IsLimit (a * b) :=
  (isNormal_mul_right a0).isLimit

@[deprecated isLimit_mul (since := "2024-10-11")]
alias mul_isLimit := isLimit_mul

theorem isLimit_mul_left {a b : Ordinal} (l : IsLimit a) (b0 : 0 < b) : IsLimit (a * b) := by
  rcases zero_or_succ_or_limit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isLimit_add _ l
  · exact isLimit_mul l.pos lb

@[deprecated isLimit_mul_left (since := "2024-10-11")]
alias mul_isLimit_left := isLimit_mul_left

theorem smul_eq_mul : ∀ (n : ℕ) (a : Ordinal), n • a = a * n
  | 0, a => by rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | n + 1, a => by rw [succ_nsmul, Nat.cast_add, mul_add, Nat.cast_one, mul_one, smul_eq_mul n]

/-! ### Division on ordinals -/


/-- The set in the definition of division is nonempty. -/
private theorem div_nonempty {a b : Ordinal} (h : b ≠ 0) : { o | a < b * succ o }.Nonempty :=
  ⟨a, (succ_le_iff (a := a) (b := b * succ a)).1 <| by
    simpa only [succ_zero, one_mul] using
      mul_le_mul_right' (succ_le_of_lt (Ordinal.pos_iff_ne_zero.2 h)) (succ a)⟩

/-- `a / b` is the unique ordinal `o` satisfying `a = b * o + o'` with `o' < b`. -/
instance div : Div Ordinal :=
  ⟨fun a b => if b = 0 then 0 else sInf { o | a < b * succ o }⟩

@[simp]
theorem div_zero (a : Ordinal) : a / 0 = 0 :=
  dif_pos rfl

private theorem div_def (a) {b : Ordinal} (h : b ≠ 0) : a / b = sInf { o | a < b * succ o } :=
  dif_neg h

theorem lt_mul_succ_div (a) {b : Ordinal} (h : b ≠ 0) : a < b * succ (a / b) := by
  rw [div_def a h]; exact csInf_mem (div_nonempty h)

theorem lt_mul_div_add (a) {b : Ordinal} (h : b ≠ 0) : a < b * (a / b) + b := by
  simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
  ⟨fun h => (lt_mul_succ_div a b0).trans_le (mul_le_mul_left' (succ_le_succ_iff.2 h) _), fun h => by
    rw [div_def a b0]; exact csInf_le' h⟩

theorem lt_div {a b c : Ordinal} (h : c ≠ 0) : a < b / c ↔ c * succ a ≤ b := by
  rw [← not_le, div_le h, not_lt]

theorem div_pos {b c : Ordinal} (h : c ≠ 0) : 0 < b / c ↔ c ≤ b := by simp [lt_div h]

theorem le_div {a b c : Ordinal} (c0 : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b := by
  induction a using limitRecOn with
  | H₁ => simp only [mul_zero, Ordinal.zero_le]
  | H₂ _ _ => rw [succ_le_iff, lt_div c0]
  | H₃ _ h₁ h₂ =>
    revert h₁ h₂
    simp +contextual only [mul_le_of_limit, limit_le, forall_true_iff]

theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c :=
  lt_iff_lt_of_le_iff_le <| le_div b0

theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b * c) : a / b ≤ c :=
  if b0 : b = 0 then by simp only [b0, div_zero, Ordinal.zero_le]
  else
    (div_le b0).2 <| h.trans_lt <| mul_lt_mul_of_pos_left (lt_succ c) (Ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → c * a < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
theorem zero_div (a : Ordinal) : 0 / a = 0 :=
  Ordinal.le_zero.1 <| div_le_of_le_mul <| Ordinal.zero_le _

theorem mul_div_le (a b : Ordinal) : b * (a / b) ≤ a :=
  if b0 : b = 0 then by simp only [b0, zero_mul, Ordinal.zero_le] else (le_div b0).1 le_rfl

theorem div_le_left {a b : Ordinal} (h : a ≤ b) (c : Ordinal) : a / c ≤ b / c := by
  obtain rfl | hc := eq_or_ne c 0
  · rw [div_zero, div_zero]
  · rw [le_div hc]
    exact (mul_div_le a c).trans h

theorem mul_add_div (a) {b : Ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b := by
  apply le_antisymm
  · apply (div_le b0).2
    rw [mul_succ, mul_add, add_assoc, add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  · rw [le_div b0, mul_add, add_le_add_iff_left]
    apply mul_div_le

theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by
  rw [← Ordinal.le_zero, div_le <| Ordinal.pos_iff_ne_zero.1 <| (Ordinal.zero_le _).trans_lt h]
  simpa only [succ_zero, mul_one] using h

@[simp]
theorem mul_div_cancel (a) {b : Ordinal} (b0 : b ≠ 0) : b * a / b = a := by
  simpa only [add_zero, zero_div] using mul_add_div a b0 0

theorem mul_add_div_mul {a c : Ordinal} (hc : c < a) (b d : Ordinal) :
    (a * b + c) / (a * d) = b / d := by
  have ha : a ≠ 0 := ((Ordinal.zero_le c).trans_lt hc).ne'
  obtain rfl | hd := eq_or_ne d 0
  · rw [mul_zero, div_zero, div_zero]
  · have H := mul_ne_zero ha hd
    apply le_antisymm
    · rw [← lt_succ_iff, div_lt H, mul_assoc]
      · apply (add_lt_add_left hc _).trans_le
        rw [← mul_succ]
        apply mul_le_mul_left'
        rw [succ_le_iff]
        exact lt_mul_succ_div b hd
    · rw [le_div H, mul_assoc]
      exact (mul_le_mul_left' (mul_div_le b d) a).trans (le_add_right _ c)

theorem mul_div_mul_cancel {a : Ordinal} (ha : a ≠ 0) (b c) : a * b / (a * c) = b / c := by
  convert mul_add_div_mul (Ordinal.pos_iff_ne_zero.2 ha) b c using 1
  rw [add_zero]

@[simp]
theorem div_one (a : Ordinal) : a / 1 = a := by
  simpa only [one_mul] using mul_div_cancel a Ordinal.one_ne_zero

@[simp]
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 := by
  simpa only [mul_one] using mul_div_cancel 1 h

theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c :=
  if a0 : a = 0 then by simp only [a0, zero_mul, sub_self]
  else
    eq_of_forall_ge_iff fun d => by rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem isLimit_add_iff {a b} : IsLimit (a + b) ↔ IsLimit b ∨ b = 0 ∧ IsLimit a := by
  constructor <;> intro h
  · by_cases h' : b = 0
    · rw [h', add_zero] at h
      right
      exact ⟨h', h⟩
    left
    rw [← add_sub_cancel a b]
    apply isLimit_sub h
    suffices a + 0 < a + b by simpa only [add_zero] using this
    rwa [add_lt_add_iff_left, Ordinal.pos_iff_ne_zero]
  rcases h with (h | ⟨rfl, h⟩)
  · exact isLimit_add a h
  · simpa only [add_zero]

theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ => ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩, fun ⟨d, e⟩ => by
      rw [e, ← mul_add]
      apply dvd_mul_right⟩

theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b
  -- Porting note: `⟨b, rfl⟩ => by` → `⟨b, e⟩ => by subst e`
  | a, _, b0, ⟨b, e⟩ => by
    subst e
    -- Porting note: `Ne` is required.
    simpa only [mul_one] using
      mul_le_mul_left'
        (one_le_iff_ne_zero.2 fun h : b = 0 => by
          simp only [h, mul_zero, Ne, not_true_eq_false] at b0) a

theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then by subst a; exact (eq_zero_of_zero_dvd h₁).symm
  else
    if b0 : b = 0 then by subst b; exact eq_zero_of_zero_dvd h₂
    else (le_of_dvd b0 h₁).antisymm (le_of_dvd a0 h₂)

instance isAntisymm : IsAntisymm Ordinal (· ∣ ·) :=
  ⟨@dvd_antisymm⟩

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance mod : Mod Ordinal :=
  ⟨fun a b => a - b * (a / b)⟩

theorem mod_def (a b : Ordinal) : a % b = a - b * (a / b) :=
  rfl

theorem mod_le (a b : Ordinal) : a % b ≤ a :=
  sub_le_self a _

@[simp]
theorem mod_zero (a : Ordinal) : a % 0 = a := by simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp]
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a :=
  Ordinal.add_sub_cancel_of_le <| mul_div_le _ _

theorem mod_lt (a) {b : Ordinal} (h : b ≠ 0) : a % b < b :=
  (add_lt_add_iff_left (b * (a / b))).1 <| by rw [div_add_mod]; exact lt_mul_div_add a h

@[simp]
theorem mod_self (a : Ordinal) : a % a = 0 :=
  if a0 : a = 0 then by simp only [a0, zero_mod]
  else by simp only [mod_def, div_self a0, mul_one, sub_self]

@[simp]
theorem mod_one (a : Ordinal) : a % 1 = 0 := by simp only [mod_def, div_one, one_mul, sub_self]

theorem dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a :=
  ⟨a / b, by simpa [H] using (div_add_mod a b).symm⟩

theorem mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0 := by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  · simp [mod_def, hb]

theorem dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[simp]
theorem mul_add_mod_self (x y z : Ordinal) : (x * y + z) % x = z % x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rwa [mod_def, mul_add_div, mul_add, ← sub_sub, add_sub_cancel, mod_def]

@[simp]
theorem mul_mod (x y : Ordinal) : x * y % x = 0 := by
  simpa using mul_add_mod_self x y 0

theorem mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y z : Ordinal) :
    (x * y + w) % (x * z) = x * (y % z) + w := by
  rw [mod_def, mul_add_div_mul hw]
  apply sub_eq_of_add_eq
  rw [← add_assoc, mul_assoc, ← mul_add, div_add_mod]

theorem mul_mod_mul (x y z : Ordinal) : (x * y) % (x * z) = x * (y % z) := by
  obtain rfl | hx := Ordinal.eq_zero_or_pos x
  · simp
  · convert mul_add_mod_mul hx y z using 1 <;>
    rw [add_zero]

theorem mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h : c ∣ b) : a % b % c = a % c := by
  nth_rw 2 [← div_add_mod a b]
  rcases h with ⟨d, rfl⟩
  rw [mul_assoc, mul_add_mod_self]

@[simp]
theorem mod_mod (a b : Ordinal) : a % b % b = a % b :=
  mod_mod_of_dvd a dvd_rfl

/-! ### Families of ordinals

There are two kinds of indexed families that naturally arise when dealing with ordinals: those
indexed by some type in the appropriate universe, and those indexed by ordinals less than another.
The following API allows one to convert from one kind of family to the other.

In many cases, this makes it easy to prove claims about one kind of family via the corresponding
claim on the other. -/


/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a specified
well-ordering. -/
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.toType → α :=
  familyOfBFamily' (· < ·) (type_toType o) f

@[simp]
theorem bfamilyOfFamily'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamilyOfFamily', enum_typein]

@[simp]
theorem bfamilyOfFamily_typein {ι} (f : ι → α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamilyOfFamily'_typein _ f i

theorem familyOfBFamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by
  simp only [familyOfBFamily', typein_enum]

theorem familyOfBFamily_enum (o : Ordinal) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.toType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi :=
  familyOfBFamily'_enum _ (type_toType o) f _ _

/-- The range of a family indexed by ordinals. -/
def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

theorem mem_brange {o : Ordinal} {f : ∀ a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a :=
  Iff.rfl

theorem mem_brange_self {o} (f : ∀ a < o, α) (i hi) : f i hi ∈ brange o f :=
  ⟨i, hi, rfl⟩

@[simp]
theorem range_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[simp]
theorem range_familyOfBFamily {o} (f : ∀ a < o, α) : range (familyOfBFamily o f) = brange o f :=
  range_familyOfBFamily' _ _ f

@[simp]
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    brange _ (bfamilyOfFamily' r f) = range f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[simp]
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι → α) : brange _ (bfamilyOfFamily f) = range f :=
  brange_bfamilyOfFamily' _ _

@[simp]
theorem brange_const {o : Ordinal} (ho : o ≠ 0) {c : α} : (brange o fun _ _ => c) = {c} := by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.toType (toType_nonempty_iff_ne_zero.2 ho) c

theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α)
    (g : α → β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

theorem comp_bfamilyOfFamily {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

theorem comp_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) :=
  rfl

theorem comp_familyOfBFamily {o} (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) :=
  rfl

/-! ### Supremum of a family of ordinals -/

/-- The supremum of a family of ordinals -/

@[deprecated iSup (since := "2024-08-27")]
def sup {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup f

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem sSup_eq_sup {ι : Type u} (f : ι → Ordinal.{max u v}) : sSup (Set.range f) = sup.{_, v} f :=
  rfl

/-- The range of an indexed ordinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. See `Ordinal.lsub` for an explicit bound. -/
theorem bddAbove_range {ι : Type u} (f : ι → Ordinal.{max u v}) : BddAbove (Set.range f) :=
  ⟨(iSup (succ ∘ card ∘ f)).ord, by
    rintro a ⟨i, rfl⟩
    exact le_of_lt (Cardinal.lt_ord.2 ((lt_succ _).trans_le
      (le_ciSup (Cardinal.bddAbove_range _) _)))⟩

theorem bddAbove_of_small (s : Set Ordinal.{u}) [h : Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := bddAbove_range (fun x => ((@equivShrink s h).symm x).val)
  use a
  intro b hb
  simpa using ha (mem_range_self (equivShrink s ⟨b, hb⟩))

theorem bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, h⟩ => small_subset <| show s ⊆ Iic a from fun _ hx => h hx, fun _ =>
    bddAbove_of_small _⟩

theorem bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s)
    (f : Ordinal.{u} → Ordinal.{max u v}) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _

theorem bddAbove_range_comp {ι : Type u} {f : ι → Ordinal.{v}} (hf : BddAbove (range f))
    (g : Ordinal.{v} → Ordinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image hf g

/-- `le_ciSup` whenever the input type is small in the output universe. This lemma sometimes
fails to infer `f` in simple cases and needs it to be given explicitly. -/
protected theorem le_iSup {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] : ∀ i, f i ≤ iSup f :=
  le_ciSup (bddAbove_of_small _)

set_option linter.deprecated false in
@[deprecated Ordinal.le_iSup (since := "2024-08-27")]
theorem le_sup {ι : Type u} (f : ι → Ordinal.{max u v}) : ∀ i, f i ≤ sup.{_, v} f := fun i =>
  Ordinal.le_iSup f i

/-- `ciSup_le_iff'` whenever the input type is small in the output universe. -/
protected theorem iSup_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  ciSup_le_iff' (bddAbove_of_small _)

set_option linter.deprecated false in
@[deprecated Ordinal.iSup_le_iff (since := "2024-08-27")]
theorem sup_le_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : sup.{_, v} f ≤ a ↔ ∀ i, f i ≤ a :=
  Ordinal.iSup_le_iff

/-- An alias of `ciSup_le'` for discoverability. -/
protected theorem iSup_le {ι} {f : ι → Ordinal} {a} :
    (∀ i, f i ≤ a) → iSup f ≤ a :=
  ciSup_le'

set_option linter.deprecated false in
@[deprecated Ordinal.iSup_le (since := "2024-08-27")]
theorem sup_le {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : (∀ i, f i ≤ a) → sup.{_, v} f ≤ a :=
  Ordinal.iSup_le

/-- `lt_ciSup_iff'` whenever the input type is small in the output universe. -/
protected theorem lt_iSup_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < iSup f ↔ ∃ i, a < f i :=
  lt_ciSup_iff' (bddAbove_of_small _)

@[deprecated "No deprecation message was provided." (since := "2024-11-12")]
alias lt_iSup := lt_iSup_iff

set_option linter.deprecated false in
@[deprecated Ordinal.lt_iSup (since := "2024-08-27")]
theorem lt_sup {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : a < sup.{_, v} f ↔ ∃ i, a < f i := by
  simpa only [not_forall, not_le] using not_congr (@sup_le_iff.{_, v} _ f a)

@[deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem ne_iSup_iff_lt_iSup {ι : Type u} {f : ι → Ordinal.{max u v}} :
    (∀ i, f i ≠ iSup f) ↔ ∀ i, f i < iSup f :=
  forall_congr' fun i => (Ordinal.le_iSup f i).lt_iff_ne.symm

set_option linter.deprecated false in
@[deprecated ne_iSup_iff_lt_iSup (since := "2024-08-27")]
theorem ne_sup_iff_lt_sup {ι : Type u} {f : ι → Ordinal.{max u v}} :
    (∀ i, f i ≠ sup.{_, v} f) ↔ ∀ i, f i < sup.{_, v} f :=
  ne_iSup_iff_lt_iSup

-- TODO: state in terms of `IsSuccLimit`.
theorem succ_lt_iSup_of_ne_iSup {ι} {f : ι → Ordinal.{u}} [Small.{u} ι]
    (hf : ∀ i, f i ≠ iSup f) {a} (hao : a < iSup f) : succ a < iSup f := by
  by_contra! hoa
  exact hao.not_le (Ordinal.iSup_le fun i => le_of_lt_succ <|
    (lt_of_le_of_ne (Ordinal.le_iSup _ _) (hf i)).trans_le hoa)

set_option linter.deprecated false in
@[deprecated succ_lt_iSup_of_ne_iSup (since := "2024-08-27")]
theorem sup_not_succ_of_ne_sup {ι : Type u} {f : ι → Ordinal.{max u v}}
    (hf : ∀ i, f i ≠ sup.{_, v} f) {a} (hao : a < sup.{_, v} f) : succ a < sup.{_, v} f := by
  by_contra! hoa
  exact
    hao.not_le (sup_le fun i => le_of_lt_succ <| (lt_of_le_of_ne (le_sup _ _) (hf i)).trans_le hoa)

-- TODO: generalize to conditionally complete lattices.
theorem iSup_eq_zero_iff {ι} {f : ι → Ordinal.{u}} [Small.{u} ι] :
    iSup f = 0 ↔ ∀ i, f i = 0 := by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => Ordinal.le_zero.2 (h i)) (Ordinal.zero_le _)⟩
  rw [← Ordinal.le_zero, ← h]
  exact Ordinal.le_iSup f i

set_option linter.deprecated false in
@[deprecated iSup_eq_zero_iff (since := "2024-08-27")]
theorem sup_eq_zero_iff {ι : Type u} {f : ι → Ordinal.{max u v}} :
    sup.{_, v} f = 0 ↔ ∀ i, f i = 0 := by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (sup_le fun i => Ordinal.le_zero.2 (h i)) (Ordinal.zero_le _)⟩
  rw [← Ordinal.le_zero, ← h]
  exact le_sup f i

set_option linter.deprecated false in
@[deprecated ciSup_of_empty (since := "2024-08-27")]
theorem sup_empty {ι} [IsEmpty ι] (f : ι → Ordinal) : sup f = 0 :=
  ciSup_of_empty f

set_option linter.deprecated false in
@[deprecated ciSup_const (since := "2024-08-27")]
theorem sup_const {ι} [_hι : Nonempty ι] (o : Ordinal) : (sup fun _ : ι => o) = o :=
  ciSup_const

set_option linter.deprecated false in
@[deprecated ciSup_unique (since := "2024-08-27")]
theorem sup_unique {ι} [Unique ι] (f : ι → Ordinal) : sup f = f default :=
  ciSup_unique

set_option linter.deprecated false in
@[deprecated csSup_le_csSup' (since := "2024-08-27")]
theorem sup_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : sup.{u, max v w} f ≤ sup.{v, max u w} g :=
  csSup_le_csSup' (bddAbove_range.{v, max u w} _) h

-- TODO: generalize or remove
theorem iSup_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : iSup f = iSup g :=
  congr_arg _ h

set_option linter.deprecated false in
@[deprecated iSup_eq_of_range_eq (since := "2024-08-27")]
theorem sup_eq_of_range_eq {ι : Type u} {ι' : Type v}
    {f : ι → Ordinal.{max u v w}} {g : ι' → Ordinal.{max u v w}}
    (h : Set.range f = Set.range g) : sup.{u, max v w} f = sup.{v, max u w} g :=
  Ordinal.iSup_eq_of_range_eq h

-- TODO: generalize to conditionally complete lattices
theorem iSup_sum {α β} (f : α ⊕ β → Ordinal.{u}) [Small.{u} α] [Small.{u} β]:
    iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b)) := by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x ↦ f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x ↦ f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' (bddAbove_of_small _)
    rintro i ⟨a, rfl⟩
    apply mem_range_self

set_option linter.deprecated false in
@[deprecated iSup_sum (since := "2024-08-27")]
theorem sup_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    sup.{max u v, w} f =
      max (sup.{u, max v w} fun a => f (Sum.inl a)) (sup.{v, max u w} fun b => f (Sum.inr b)) := by
  apply (sup_le_iff.2 _).antisymm (max_le_iff.2 ⟨_, _⟩)
  · rintro (i | i)
    · exact le_max_of_le_left (le_sup _ i)
    · exact le_max_of_le_right (le_sup _ i)
  all_goals
    apply sup_le_of_range_subset.{_, max u v, w}
    rintro i ⟨a, rfl⟩
    apply mem_range_self

theorem unbounded_range_of_le_iSup {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ ⨆ i, typein r (f i)) : Unbounded r (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    h.not_lt <| lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

set_option linter.deprecated false in
@[deprecated unbounded_range_of_le_iSup (since := "2024-08-27")]
theorem unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ sup.{u, u} (typein r ∘ f)) : Unbounded r (range f) :=
  unbounded_range_of_le_iSup r f h

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem le_sup_shrink_equiv {s : Set Ordinal.{u}} (hs : Small.{u} s) (a) (ha : a ∈ s) :
    a ≤ sup.{u, u} fun x => ((@equivShrink s hs).symm x).val := by
  convert le_sup.{u, u} (fun x => ((@equivShrink s hs).symm x).val) ((@equivShrink s hs) ⟨a, ha⟩)
  rw [symm_apply_apply]

theorem IsNormal.map_iSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {ι : Type*} (g : ι → Ordinal.{u}) (hg : BddAbove (range g))
    [Nonempty ι] : f (⨆ i, g i) = ⨆ i, f (g i) := eq_of_forall_ge_iff fun a ↦ by
  have := bddAbove_iff_small.mp hg
  have := univLE_of_injective H.strictMono.injective
  have := Small.trans_univLE.{u, v} (range g)
  have hfg : BddAbove (range (f ∘ g)) := bddAbove_iff_small.mpr <| by
    rw [range_comp]
    exact small_image f (range g)
  change _ ↔ ⨆ i, (f ∘ g) i ≤ a
  rw [ciSup_le_iff hfg, H.le_set' _ Set.univ_nonempty g] <;> simp [ciSup_le_iff hg]

theorem IsNormal.map_iSup {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {ι : Type w} (g : ι → Ordinal.{u}) [Small.{u} ι] [Nonempty ι] :
    f (⨆ i, g i) = ⨆ i, f (g i) :=
  H.map_iSup_of_bddAbove g (bddAbove_of_small _)

theorem IsNormal.map_sSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {s : Set Ordinal.{u}} (hs : BddAbove s) (hn : s.Nonempty) : f (sSup s) = sSup (f '' s) := by
  have := hn.to_subtype
  rw [sSup_eq_iSup', sSup_image', H.map_iSup_of_bddAbove]
  rwa [Subtype.range_coe_subtype, setOf_mem_eq]

theorem IsNormal.map_sSup {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {s : Set Ordinal.{u}} (hn : s.Nonempty) [Small.{u} s] : f (sSup s) = sSup (f '' s) :=
  H.map_sSup_of_bddAbove (bddAbove_of_small s) hn

set_option linter.deprecated false in
@[deprecated IsNormal.map_iSup (since := "2024-08-27")]
theorem IsNormal.sup {f : Ordinal.{max u v} → Ordinal.{max u w}} (H : IsNormal f) {ι : Type u}
    (g : ι → Ordinal.{max u v}) [Nonempty ι] : f (sup.{_, v} g) = sup.{_, w} (f ∘ g) :=
  H.map_iSup g

theorem IsNormal.apply_of_isLimit {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f) {o : Ordinal}
    (ho : IsLimit o) : f o = ⨆ a : Iio o, f a := by
  have : Nonempty (Iio o) := ⟨0, ho.pos⟩
  rw [← H.map_iSup, ho.iSup_Iio]

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem sup_eq_sSup {s : Set Ordinal.{u}} (hs : Small.{u} s) :
    (sup.{u, u} fun x => (@equivShrink s hs).symm x) = sSup s :=
  let hs' := bddAbove_iff_small.2 hs
  ((csSup_le_iff' hs').2 (le_sup_shrink_equiv hs)).antisymm'
    (sup_le fun _x => le_csSup hs' (Subtype.mem _))

theorem sSup_ord {s : Set Cardinal.{u}} (hs : BddAbove s) : (sSup s).ord = sSup (ord '' s) :=
  eq_of_forall_ge_iff fun a => by
    rw [csSup_le_iff'
        (bddAbove_iff_small.2 (@small_image _ _ _ s (Cardinal.bddAbove_iff_small.1 hs))),
      ord_le, csSup_le_iff' hs]
    simp [ord_le]

theorem iSup_ord {ι} {f : ι → Cardinal} (hf : BddAbove (range f)) :
    (iSup f).ord = ⨆ i, (f i).ord := by
  unfold iSup
  convert sSup_ord hf
  -- Porting note: `change` is required.
  conv_lhs => change range (ord ∘ f)
  rw [range_comp]

theorem sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sInf (range f)ᶜ < lift.{v} (succ #ι).ord := by
  by_contra! h
  have : Iio (lift.{v} (succ #ι).ord) ⊆ range f := by
    intro o ho
    have := not_mem_of_lt_csInf' (ho.trans_le h)
    rwa [not_mem_compl_iff] at this
  have := mk_le_mk_of_subset this
  rw [mk_Iio_ordinal, ← lift_card, Cardinal.lift_lift, card_ord, Cardinal.lift_succ,
    succ_le_iff, ← Cardinal.lift_id'.{u, max (u + 1) (v + 1)} #_] at this
  exact this.not_le mk_range_le_lift

theorem sInf_compl_lt_ord_succ {ι : Type u} (f : ι → Ordinal.{u}) :
    sInf (range f)ᶜ < (succ #ι).ord :=
  lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f

-- TODO: remove `bsup` in favor of `iSup` in a future refactor.

section bsup
set_option linter.deprecated false

private theorem sup_le_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop)
    [IsWellOrder ι r] [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily' r ho f) ≤ sup.{_, v} (familyOfBFamily' r' ho' f) :=
  sup_le fun i => by
    cases'
      typein_surj r'
        (by
          rw [ho', ← ho]
          exact typein_lt_type r i) with
      j hj
    simp_rw [familyOfBFamily', ← hj]
    apply le_sup

theorem sup_eq_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal.{u}} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily' r ho f) = sup.{_, v} (familyOfBFamily' r' ho' f) :=
  sup_eq_of_range_eq.{u, u, v} (by simp)

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
    `o : Ordinal.{u}`. This is a special case of `sup` over the family provided by
    `familyOfBFamily`. -/
def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  sup.{_, v} (familyOfBFamily o f)

@[simp]
theorem sup_eq_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily o f) = bsup.{_, v} o f :=
  rfl

@[simp]
theorem sup_eq_bsup' {o : Ordinal.{u}} {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : ∀ a < o, Ordinal.{max u v}) : sup.{_, v} (familyOfBFamily' r ho f) = bsup.{_, v} o f :=
  sup_eq_sup r _ ho _ f

theorem sSup_eq_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    sSup (brange o f) = bsup.{_, v} o f := by
  congr
  rw [range_familyOfBFamily]

@[simp]
theorem bsup_eq_sup' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = sup.{_, v} f := by
  simp (config := { unfoldPartialApp := true }) only [← sup_eq_bsup' r, enum_typein,
    familyOfBFamily', bfamilyOfFamily']

theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [bsup_eq_sup', bsup_eq_sup']

@[simp]
theorem bsup_eq_sup {ι : Type u} (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily f) = sup.{_, v} f :=
  bsup_eq_sup' _ f

@[congr]
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  -- Porting note: `rfl` is required.
  rfl

theorem bsup_le_iff {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  sup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

theorem bsup_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} :
    (∀ i h, f i h ≤ a) → bsup.{u, v} o f ≤ a :=
  bsup_le_iff.2

theorem le_bsup {o} (f : ∀ a < o, Ordinal) (i h) : f i h ≤ bsup o f :=
  bsup_le_iff.1 le_rfl _ _

theorem lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

theorem IsNormal.bsup {f : Ordinal.{max u v} → Ordinal.{max u w}} (H : IsNormal f)
    {o : Ordinal.{u}} :
    ∀ (g : ∀ a < o, Ordinal), o ≠ 0 → f (bsup.{_, v} o g) = bsup.{_, w} o fun a h => f (g a h) :=
  inductionOn o fun α r _ g h => by
    haveI := type_ne_zero_iff_nonempty.1 h
    rw [← sup_eq_bsup' r, IsNormal.sup.{_, v, w} H, ← sup_eq_bsup' r] <;> rfl

theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} :
    (∀ i h, f i h ≠ bsup.{_, v} o f) ↔ ∀ i h, f i h < bsup.{_, v} o f :=
  ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}}
    (hf : ∀ {i : Ordinal} (h : i < o), f i h ≠ bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f → succ a < bsup.{_, v} o f := by
  rw [← sup_eq_bsup] at *
  exact sup_not_succ_of_ne_sup fun i => hf _

@[simp]
theorem bsup_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => Ordinal.le_zero.2 (h i hi)) (Ordinal.zero_le _)⟩
  rw [← Ordinal.le_zero, ← h]
  exact le_bsup f i hi

theorem lt_bsup_of_limit {o : Ordinal} {f : ∀ a < o, Ordinal}
    (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
    (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f :=
  (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

theorem bsup_succ_of_mono {o : Ordinal} {f : ∀ a < succ o, Ordinal}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) :=
  le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[simp]
theorem bsup_zero (f : ∀ a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 :=
  bsup_eq_zero_iff.2 fun i hi => (Ordinal.not_lt_zero i hi).elim

theorem bsup_const {o : Ordinal.{u}} (ho : o ≠ 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a :=
  le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (Ordinal.pos_iff_ne_zero.2 ho))

@[simp]
theorem bsup_one (f : ∀ a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by
  simp_rw [← sup_eq_bsup, sup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

theorem bsup_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

theorem bsup_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

theorem iSup_eq_bsup {o} {f : ∀ a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by
  simp_rw [Iio, bsup, sup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_setOf]

end bsup

-- TODO: bring the lsub API in line with the sSup / iSup API, or deprecate it altogether.

section lsub
set_option linter.deprecated false

/-- The least strict upper bound of a family of ordinals. -/
def lsub {ι} (f : ι → Ordinal) : Ordinal :=
  sup (succ ∘ f)

@[simp]
theorem sup_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} (succ ∘ f) = lsub.{_, v} f :=
  rfl

theorem lsub_le_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} :
    lsub.{_, v} f ≤ a ↔ ∀ i, f i < a := by
  convert sup_le_iff.{_, v} (f := succ ∘ f) (a := a) using 2
  -- Porting note: `comp_apply` is required.
  simp only [comp_apply, succ_le_iff]

theorem lsub_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i < a) → lsub f ≤ a :=
  lsub_le_iff.2

theorem lt_lsub {ι} (f : ι → Ordinal) (i) : f i < lsub f :=
  succ_le_iff.1 (le_sup _ i)

theorem lt_lsub_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} :
    a < lsub.{_, v} f ↔ ∃ i, a ≤ f i := by
  simpa only [not_forall, not_lt, not_le] using not_congr (@lsub_le_iff.{_, v} _ f a)

theorem sup_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : sup.{_, v} f ≤ lsub.{_, v} f :=
  sup_le fun i => (lt_lsub f i).le

theorem lsub_le_sup_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f ≤ succ (sup.{_, v} f) :=
  lsub_le fun i => lt_succ_iff.2 (le_sup f i)

theorem sup_eq_lsub_or_sup_succ_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ∨ succ (sup.{_, v} f) = lsub.{_, v} f := by
  cases' eq_or_lt_of_le (sup_le_lsub.{_, v} f) with h h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_sup_succ f))

theorem sup_succ_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    succ (sup.{_, v} f) ≤ lsub.{_, v} f ↔ ∃ i, f i = sup.{_, v} f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact (succ_le_iff.1 h).ne ((sup_le_lsub f).antisymm (lsub_le (ne_sup_iff_lt_sup.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_lsub _ _

theorem sup_succ_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    succ (sup.{_, v} f) = lsub.{_, v} f ↔ ∃ i, f i = sup.{_, v} f :=
  (lsub_le_sup_succ f).le_iff_eq.symm.trans (sup_succ_le_lsub f)

theorem sup_eq_lsub_iff_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ↔ ∀ a < lsub.{_, v} f, succ a < lsub.{_, v} f := by
  refine ⟨fun h => ?_, fun hf => le_antisymm (sup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => sup_not_succ_of_ne_sup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (sup_succ_eq_lsub f).2 ⟨i, le_antisymm (le_sup _ _) hle⟩
  have :=
    hf _
      (by
        rw [← heq]
        exact lt_succ (sup f))
  rw [heq] at this
  exact this.false

theorem sup_eq_lsub_iff_lt_sup {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ↔ ∀ i, f i < sup.{_, v} f :=
  ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (sup_le_lsub f) (lsub_le h)⟩

@[simp]
theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι → Ordinal) : lsub f = 0 := by
  rw [← Ordinal.le_zero, lsub_le_iff]
  exact h.elim

theorem lsub_pos {ι : Type u} [h : Nonempty ι] (f : ι → Ordinal.{max u v}) : 0 < lsub.{_, v} f :=
  h.elim fun i => (Ordinal.zero_le _).trans_lt (lt_lsub f i)

@[simp]
theorem lsub_eq_zero_iff {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f = 0 ↔ IsEmpty ι := by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

@[simp]
theorem lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o :=
  sup_const (succ o)

@[simp]
theorem lsub_unique {ι} [Unique ι] (f : ι → Ordinal) : lsub f = succ (f default) :=
  sup_unique _

theorem lsub_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : lsub.{u, max v w} f ≤ lsub.{v, max u w} g :=
  sup_le_of_range_subset.{u, v, w} (by convert Set.image_subset succ h <;> apply Set.range_comp)

theorem lsub_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g :=
  (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

@[simp]
theorem lsub_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    lsub.{max u v, w} f =
      max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fun b => f (Sum.inr b)) :=
  sup_sum _

theorem lsub_not_mem_range {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f ∉ Set.range f := fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

theorem nonempty_compl_range {ι : Type u} (f : ι → Ordinal.{max u v}) : (Set.range f)ᶜ.Nonempty :=
  ⟨_, lsub_not_mem_range.{_, v} f⟩

@[simp]
theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α := o.toType) (· < ·)) = o :=
  (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      -- Porting note: `nth_rw` → `conv_rhs` & `rw`
      conv_rhs at h => rw [← type_lt o]
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

theorem sup_typein_limit {o : Ordinal} (ho : ∀ a, a < o → succ a < o) :
    sup.{u, u} (typein ((· < ·) : o.toType → o.toType → Prop)) = o := by
  -- Porting note: `rwa` → `rw` & `assumption`
  rw [(sup_eq_lsub_iff_succ.{u, u} (typein (· < ·))).2] <;> rw [lsub_typein o]; assumption

@[simp]
theorem sup_typein_succ {o : Ordinal} :
    sup.{u, u} (typein ((· < ·) : (succ o).toType → (succ o).toType → Prop)) = o := by
  cases'
    sup_eq_lsub_or_sup_succ_eq_lsub.{u, u}
      (typein ((· < ·) : (succ o).toType → (succ o).toType → Prop)) with
    h h
  · rw [sup_eq_lsub_iff_succ] at h
    simp only [lsub_typein] at h
    exact (h o (lt_succ o)).false.elim
  rw [← succ_eq_succ_iff, h]
  apply lsub_typein

end lsub

-- TODO: either deprecate this in favor of `lsub` when its universes are generalized, or deprecate
-- both of them at once.

section blsub
set_option linter.deprecated false

/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
    some `o : Ordinal.{u}`.

    This is to `lsub` as `bsup` is to `sup`. -/
def blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)

@[simp]
theorem bsup_eq_blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) :
    (bsup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f :=
  rfl

theorem lsub_eq_blsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily' r ho f) = blsub.{_, v} o f :=
  sup_eq_bsup'.{_, v} r ho fun a ha => succ (f a ha)

theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily' r ho f) = lsub.{_, v} (familyOfBFamily' r' ho' f) := by
  rw [lsub_eq_blsub', lsub_eq_blsub']

@[simp]
theorem lsub_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f :=
  lsub_eq_blsub' _ _ _

@[simp]
theorem blsub_eq_lsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r]
    (f : ι → Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f :=
  bsup_eq_sup'.{_, v} r (succ ∘ f)

theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily' r f) = blsub.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [blsub_eq_lsub', blsub_eq_lsub']

@[simp]
theorem blsub_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily f) = lsub.{_, v} f :=
  blsub_eq_lsub' _ _

@[congr]
theorem blsub_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  -- Porting note: `rfl` is required.
  rfl

theorem blsub_le_iff {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} {a} :
    blsub.{_, v} o f ≤ a ↔ ∀ i h, f i h < a := by
  convert bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

theorem blsub_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} : (∀ i h, f i h < a) → blsub o f ≤ a :=
  blsub_le_iff.2

theorem lt_blsub {o} (f : ∀ a < o, Ordinal) (i h) : f i h < blsub o f :=
  blsub_le_iff.1 le_rfl _ _

theorem lt_blsub_iff {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v}} {a} :
    a < blsub.{_, v} o f ↔ ∃ i hi, a ≤ f i hi := by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

theorem bsup_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f ≤ blsub.{_, v} o f :=
  bsup_le fun i h => (lt_blsub f i h).le

theorem blsub_le_bsup_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    blsub.{_, v} o f ≤ succ (bsup.{_, v} o f) :=
  blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) = blsub.{_, v} o f := by
  rw [← sup_eq_bsup, ← lsub_eq_blsub]
  exact sup_eq_lsub_or_sup_succ_eq_lsub _

theorem bsup_succ_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) ≤ blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff, ← hf]
  exact lt_blsub _ _ _

theorem bsup_succ_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f :=
  (blsub_le_bsup_succ f).le_iff_eq.symm.trans (bsup_succ_le_blsub f)

theorem bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ a < blsub.{_, v} o f, succ a < blsub.{_, v} o f := by
  rw [← sup_eq_bsup, ← lsub_eq_blsub]
  apply sup_eq_lsub_iff_succ

theorem bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ i hi, f i hi < bsup.{_, v} o f :=
  ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

theorem bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsLimit o)
    {f : ∀ a < o, Ordinal.{max u v}} (hf : ∀ a ha, f a ha < f (succ a) (ho.2 a ha)) :
    bsup.{_, v} o f = blsub.{_, v} o f := by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

theorem blsub_succ_of_mono {o : Ordinal.{u}} {f : ∀ a < succ o, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : blsub.{_, v} _ f = succ (f o (lt_succ o)) :=
  bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

@[simp]
theorem blsub_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : blsub o f = 0 ↔ o = 0 := by
  rw [← lsub_eq_blsub, lsub_eq_zero_iff]
  exact toType_empty_iff_eq_zero

-- Porting note: `rwa` → `rw`
@[simp]
theorem blsub_zero (f : ∀ a < (0 : Ordinal), Ordinal) : blsub 0 f = 0 := by rw [blsub_eq_zero_iff]

theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : ∀ a < o, Ordinal) : 0 < blsub o f :=
  (Ordinal.zero_le _).trans_lt (lt_blsub f 0 ho)

theorem blsub_type {α : Type u} (r : α → α → Prop) [IsWellOrder α r]
    (f : ∀ a < type r, Ordinal.{max u v}) :
    blsub.{_, v} (type r) f = lsub.{_, v} fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff, lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

theorem blsub_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) :
    (blsub.{u, v} o fun _ _ => a) = succ a :=
  bsup_const.{u, v} ho (succ a)

@[simp]
theorem blsub_one (f : ∀ a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 zero_lt_one) :=
  bsup_one _

@[simp]
theorem blsub_id : ∀ o, (blsub.{u, u} o fun x _ => x) = o :=
  lsub_typein

theorem bsup_id_limit {o : Ordinal} : (∀ a < o, succ a < o) → (bsup.{u, u} o fun x _ => x) = o :=
  sup_typein_limit

@[simp]
theorem bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o :=
  sup_typein_succ

theorem blsub_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : blsub.{u, max v w} o f ≤ blsub.{v, max u w} o' g :=
  bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

theorem blsub_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : { o | ∃ i hi, f i hi = o } = { o | ∃ i hi, g i hi = o }) :
    blsub.{u, max v w} o f = blsub.{v, max u w} o' g :=
  (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

theorem bsup_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (bsup.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f := by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

theorem blsub_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (blsub.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f :=
  @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

theorem IsNormal.bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsLimit o) : (Ordinal.bsup.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u, u, v} H (fun x _ => x) h.1, bsup_id_limit h.2]

theorem IsNormal.blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsLimit o) : (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup_eq.{u, v} H h, bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.1 a

theorem isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧ ∀ o, IsLimit o → (bsup.{_, v} o fun x _ => f x) = f o :=
  ⟨fun h => ⟨h.1, @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    ⟨h₁, fun o ho a => by
      rw [← h₂ o ho]
      exact bsup_le_iff⟩⟩

theorem isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsLimit o → (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u, v}, and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

theorem IsNormal.eq_iff_zero_and_succ {f g : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    (hg : IsNormal g) : f = g ↔ f 0 = g 0 ∧ ∀ a, f a = g a → f (succ a) = g (succ a) :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ =>
    funext fun a => by
      induction a using limitRecOn with
      | H₁ => solve_by_elim
      | H₂ => solve_by_elim
      | H₃ _ ho H =>
        rw [← IsNormal.bsup_eq.{u, u} hf ho, ← IsNormal.bsup_eq.{u, u} hg ho]
        congr
        ext b hb
        exact H b hb⟩

/-- A two-argument version of `Ordinal.blsub`.

Deprecated. If you need this value explicitly, write it in terms of `iSup`. If you just want an
upper bound for the image of `op`, use that `Iio a ×ˢ Iio b` is a small set. -/
@[deprecated "No deprecation message was provided."  (since := "2024-10-11")]
def blsub₂ (o₁ o₂ : Ordinal) (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) :
    Ordinal :=
  lsub (fun x : o₁.toType × o₂.toType => op (typein_lt_self x.1) (typein_lt_self x.2))

@[deprecated "No deprecation message was provided."  (since := "2024-10-11")]
theorem lt_blsub₂ {o₁ o₂ : Ordinal}
    (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) {a b : Ordinal}
    (ha : a < o₁) (hb : b < o₂) : op ha hb < blsub₂ o₁ o₂ op := by
  convert lt_lsub _ (Prod.mk (enum (· < ·) ⟨a, by rwa [type_lt]⟩)
    (enum (· < ·) ⟨b, by rwa [type_lt]⟩))
  simp only [typein_enum]

end blsub

section mex
set_option linter.deprecated false

/-! ### Minimum excluded ordinals -/


/-- The minimum excluded ordinal in a family of ordinals. -/
@[deprecated "use sInf sᶜ instead" (since := "2024-09-20")]
def mex {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal :=
  sInf (Set.range f)ᶜ

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_not_mem_range {ι : Type u} (f : ι → Ordinal.{max u v}) : mex.{_, v} f ∉ Set.range f :=
  csInf_mem (nonempty_compl_range.{_, v} f)

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem le_mex_of_forall {ι : Type u} {f : ι → Ordinal.{max u v}} {a : Ordinal}
    (H : ∀ b < a, ∃ i, f i = b) : a ≤ mex.{_, v} f := by
  by_contra! h
  exact mex_not_mem_range f (H _ h)

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem ne_mex {ι : Type u} (f : ι → Ordinal.{max u v}) : ∀ i, f i ≠ mex.{_, v} f := by
  simpa using mex_not_mem_range.{_, v} f

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_le_of_ne {ι} {f : ι → Ordinal} {a} (ha : ∀ i, f i ≠ a) : mex f ≤ a :=
  csInf_le' (by simp [ha])

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem exists_of_lt_mex {ι} {f : ι → Ordinal} {a} (ha : a < mex f) : ∃ i, f i = a := by
  by_contra! ha'
  exact ha.not_le (mex_le_of_ne ha')

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : mex.{_, v} f ≤ lsub.{_, v} f :=
  csInf_le' (lsub_not_mem_range f)

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_monotone {α β : Type u} {f : α → Ordinal.{max u v}} {g : β → Ordinal.{max u v}}
    (h : Set.range f ⊆ Set.range g) : mex.{_, v} f ≤ mex.{_, v} g := by
  refine mex_le_of_ne fun i hi => ?_
  cases' h ⟨i, rfl⟩ with j hj
  rw [← hj] at hi
  exact ne_mex g j hi

@[deprecated sInf_compl_lt_ord_succ (since := "2024-09-20")]
theorem mex_lt_ord_succ_mk {ι : Type u} (f : ι → Ordinal.{u}) :
    mex.{_, u} f < (succ #ι).ord := by
  by_contra! h
  apply (lt_succ #ι).not_le
  have H := fun a => exists_of_lt_mex ((typein_lt_self a).trans_le h)
  let g : (succ #ι).ord.toType → ι := fun a => Classical.choose (H a)
  have hg : Injective g := fun a b h' => by
    have Hf : ∀ x, f (g x) =
        typein ((· < ·) : (succ #ι).ord.toType → (succ #ι).ord.toType → Prop) x :=
      fun a => Classical.choose_spec (H a)
    apply_fun f at h'
    rwa [Hf, Hf, typein_inj] at h'
  convert Cardinal.mk_le_of_injective hg
  rw [Cardinal.mk_ord_toType (succ #ι)]

/-- The minimum excluded ordinal of a family of ordinals indexed by the set of ordinals less than
    some `o : Ordinal.{u}`. This is a special case of `mex` over the family provided by
    `familyOfBFamily`.

    This is to `mex` as `bsup` is to `sup`. -/
@[deprecated "use sInf sᶜ instead" (since := "2024-09-20")]
def bmex (o : Ordinal) (f : ∀ a < o, Ordinal) : Ordinal :=
  mex (familyOfBFamily o f)

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_not_mem_brange {o : Ordinal} (f : ∀ a < o, Ordinal) : bmex o f ∉ brange o f := by
  rw [← range_familyOfBFamily]
  apply mex_not_mem_range

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem le_bmex_of_forall {o : Ordinal} (f : ∀ a < o, Ordinal) {a : Ordinal}
    (H : ∀ b < a, ∃ i hi, f i hi = b) : a ≤ bmex o f := by
  by_contra! h
  exact bmex_not_mem_brange f (H _ h)

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem ne_bmex {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {i} (hi) :
    f i hi ≠ bmex.{_, v} o f := by
  convert (config := {transparency := .default})
    ne_mex.{_, v} (familyOfBFamily o f) (enum (α := o.toType) (· < ·) ⟨i, by rwa [type_lt]⟩) using 2
  -- Porting note: `familyOfBFamily_enum` → `typein_enum`
  rw [typein_enum]

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_le_of_ne {o : Ordinal} {f : ∀ a < o, Ordinal} {a} (ha : ∀ i hi, f i hi ≠ a) :
    bmex o f ≤ a :=
  mex_le_of_ne fun _i => ha _ _

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem exists_of_lt_bmex {o : Ordinal} {f : ∀ a < o, Ordinal} {a} (ha : a < bmex o f) :
    ∃ i hi, f i hi = a := by
  cases' exists_of_lt_mex ha with i hi
  exact ⟨_, typein_lt_self i, hi⟩

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bmex.{_, v} o f ≤ blsub.{_, v} o f :=
  mex_le_lsub _

@[deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_monotone {o o' : Ordinal.{u}}
    {f : ∀ a < o, Ordinal.{max u v}} {g : ∀ a < o', Ordinal.{max u v}}
    (h : brange o f ⊆ brange o' g) : bmex.{_, v} o f ≤ bmex.{_, v} o' g :=
  mex_monotone (by rwa [range_familyOfBFamily, range_familyOfBFamily])

@[deprecated sInf_compl_lt_ord_succ (since := "2024-09-20")]
theorem bmex_lt_ord_succ_card {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{u}) :
    bmex.{_, u} o f < (succ o.card).ord := by
  rw [← mk_toType]
  exact mex_lt_ord_succ_mk (familyOfBFamily o f)

end mex

end Ordinal

/-! ### Results about injectivity and surjectivity -/


theorem not_surjective_of_ordinal {α : Type u} (f : α → Ordinal.{u}) : ¬Surjective f := fun h =>
  Ordinal.lsub_not_mem_range.{u, u} f (h _)

theorem not_injective_of_ordinal {α : Type u} (f : Ordinal.{u} → α) : ¬Injective f := fun h =>
  not_surjective_of_ordinal _ (invFun_surjective h)

theorem not_surjective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : α → Ordinal.{u}) :
    ¬Surjective f := fun h => not_surjective_of_ordinal _ (h.comp (equivShrink _).symm.surjective)

theorem not_injective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α) :
    ¬Injective f := fun h => not_injective_of_ordinal _ ((equivShrink _).injective.comp h)

/-- The type of ordinals in universe `u` is not `Small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := fun h =>
  @not_injective_of_ordinal_of_small _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1

theorem Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} s] :
    ¬BddAbove sᶜ := by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self, small_univ_iff] at this
  exact not_small_ordinal this

/-! ### Casting naturals into ordinals, compatibility with operations -/


namespace Ordinal

instance instCharZero : CharZero Ordinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← Cardinal.ord_nat, ← Cardinal.ord_nat, Cardinal.ord_inj, Nat.cast_inj] at h

@[simp]
theorem one_add_natCast (m : ℕ) : 1 + (m : Ordinal) = succ m := by
  rw [← Nat.cast_one, ← Nat.cast_add, add_comm]
  rfl

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias one_add_nat_cast := one_add_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem one_add_ofNat (m : ℕ) [m.AtLeastTwo] :
    1 + (no_index (OfNat.ofNat m : Ordinal)) = Order.succ (OfNat.ofNat m : Ordinal) :=
  one_add_natCast m

@[simp, norm_cast]
theorem natCast_mul (m : ℕ) : ∀ n : ℕ, ((m * n : ℕ) : Ordinal) = m * n
  | 0 => by simp
  | n + 1 => by rw [Nat.mul_succ, Nat.cast_add, natCast_mul m n, Nat.cast_succ, mul_add_one]

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_mul := natCast_mul

@[deprecated Nat.cast_le (since := "2024-10-17")]
theorem natCast_le {m n : ℕ} : (m : Ordinal) ≤ n ↔ m ≤ n := Nat.cast_le

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_le := natCast_le

@[deprecated Nat.cast_inj (since := "2024-10-17")]
theorem natCast_inj {m n : ℕ} : (m : Ordinal) = n ↔ m = n := Nat.cast_inj

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_inj := natCast_inj

@[deprecated Nat.cast_lt (since := "2024-10-17")]
theorem natCast_lt {m n : ℕ} : (m : Ordinal) < n ↔ m < n := Nat.cast_lt

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_lt := natCast_lt

@[deprecated Nat.cast_eq_zero (since := "2024-10-17")]
theorem natCast_eq_zero {n : ℕ} : (n : Ordinal) = 0 ↔ n = 0 := Nat.cast_eq_zero

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_eq_zero := natCast_eq_zero

@[deprecated Nat.cast_ne_zero (since := "2024-10-17")]
theorem natCast_ne_zero {n : ℕ} : (n : Ordinal) ≠ 0 ↔ n ≠ 0 := Nat.cast_ne_zero

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_ne_zero := natCast_ne_zero

@[deprecated Nat.cast_pos' (since := "2024-10-17")]
theorem natCast_pos {n : ℕ} : (0 : Ordinal) < n ↔ 0 < n := Nat.cast_pos'

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_pos := natCast_pos

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ((m - n : ℕ) : Ordinal) = m - n := by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h)]
    rfl
  · apply (add_left_cancel n).1
    rw [← Nat.cast_add, add_tsub_cancel_of_le h, Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_sub := natCast_sub

@[simp, norm_cast]
theorem natCast_div (m n : ℕ) : ((m / n : ℕ) : Ordinal) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · have hn' : (n : Ordinal) ≠ 0 := Nat.cast_ne_zero.2 hn
    apply le_antisymm
    · rw [le_div hn', ← natCast_mul, Nat.cast_le, mul_comm]
      apply Nat.div_mul_le_self
    · rw [div_le hn', ← add_one_eq_succ, ← Nat.cast_succ, ← natCast_mul, Nat.cast_lt, mul_comm,
        ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)]
      apply Nat.lt_succ_self

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_div := natCast_div

@[simp, norm_cast]
theorem natCast_mod (m n : ℕ) : ((m % n : ℕ) : Ordinal) = m % n := by
  rw [← add_left_cancel, div_add_mod, ← natCast_div, ← natCast_mul, ← Nat.cast_add,
    Nat.div_add_mod]

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias nat_cast_mod := natCast_mod

@[simp]
theorem lift_natCast : ∀ n : ℕ, lift.{u, v} n = n
  | 0 => by simp
  | n + 1 => by simp [lift_natCast n]

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias lift_nat_cast := lift_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u, v} (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  lift_natCast n

end Ordinal

/-! ### Properties of ω -/


namespace Cardinal

open Ordinal

@[simp]
theorem add_one_of_aleph0_le {c} (h : ℵ₀ ≤ c) : c + 1 = c := by
  rw [add_comm, ← card_ord c, ← card_one, ← card_add, one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

end Cardinal

namespace Ordinal

theorem lt_add_of_limit {a b c : Ordinal.{u}} (h : IsLimit c) :
    a < b + c ↔ ∃ c' < c, a < b + c' := by
  -- Porting note: `bex_def` is required.
  rw [← IsNormal.bsup_eq.{u, u} (isNormal_add_right b) h, lt_bsup, bex_def]

theorem lt_omega0 {o : Ordinal} : o < ω ↔ ∃ n : ℕ, o = n := by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias lt_omega := lt_omega0

theorem nat_lt_omega0 (n : ℕ) : ↑n < ω :=
  lt_omega0.2 ⟨_, rfl⟩

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias nat_lt_omega := nat_lt_omega0

theorem omega0_pos : 0 < ω :=
  nat_lt_omega0 0

theorem omega0_ne_zero : ω ≠ 0 :=
  omega0_pos.ne'

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_ne_zero := omega0_ne_zero

theorem one_lt_omega0 : 1 < ω := by simpa only [Nat.cast_one] using nat_lt_omega0 1

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_lt_omega := one_lt_omega0

theorem isLimit_omega0 : IsLimit ω :=
  ⟨omega0_ne_zero, fun o h => by
    let ⟨n, e⟩ := lt_omega0.1 h
    rw [e]; exact nat_lt_omega0 (n + 1)⟩

@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
alias omega0_isLimit := isLimit_omega0

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_isLimit := isLimit_omega0

theorem omega0_le {o : Ordinal} : ω ≤ o ↔ ∀ n : ℕ, ↑n ≤ o :=
  ⟨fun h n => (nat_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e, ← succ_le_iff]; exact H (n + 1)⟩

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_le := omega0_le

@[simp]
theorem iSup_natCast : iSup Nat.cast = ω :=
  (Ordinal.iSup_le fun n => (nat_lt_omega0 n).le).antisymm <| omega0_le.2 <| Ordinal.le_iSup _

set_option linter.deprecated false in
@[deprecated iSup_natCast (since := "2024-04-17")]
theorem sup_natCast : sup Nat.cast = ω :=
  iSup_natCast

@[deprecated "No deprecation message was provided."  (since := "2024-04-17")]
alias sup_nat_cast := sup_natCast

theorem nat_lt_limit {o} (h : IsLimit o) : ∀ n : ℕ, ↑n < o
  | 0 => lt_of_le_of_ne (Ordinal.zero_le o) h.1.symm
  | n + 1 => h.2 _ (nat_lt_limit h n)

theorem omega0_le_of_isLimit {o} (h : IsLimit o) : ω ≤ o :=
  omega0_le.2 fun n => le_of_lt <| nat_lt_limit h n

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_le_of_isLimit := omega0_le_of_isLimit

theorem isLimit_iff_omega0_dvd {a : Ordinal} : IsLimit a ↔ a ≠ 0 ∧ ω ∣ a := by
  refine ⟨fun l => ⟨l.1, ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩⟩, fun h => ?_⟩
  · refine (limit_le l).2 fun x hx => le_of_lt ?_
    rw [← div_lt omega0_ne_zero, ← succ_le_iff, le_div omega0_ne_zero, mul_succ,
      add_le_of_limit isLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    exact
      (add_le_add_right (mul_div_le _ _) _).trans
        (lt_sub.1 <| nat_lt_limit (isLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    refine isLimit_mul_left isLimit_omega0 (Ordinal.pos_iff_ne_zero.2 <| mt ?_ a0)
    intro e
    simp only [e, mul_zero]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias isLimit_iff_omega_dvd := isLimit_iff_omega0_dvd

theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c)
    (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymm
    ((mul_le_of_limit l).2 fun c' h => by
      apply (mul_le_mul_left' (le_succ c') _).trans
      rw [IH _ h]
      apply (add_le_add_left _ _).trans
      · rw [← mul_succ]
        exact mul_le_mul_left' (succ_le_of_lt <| l.2 _ h) _
      · rw [← ba]
        exact le_add_right _ _)
    (mul_le_mul_right' (le_add_right _ _) _)

theorem add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a * succ c + b := by
  induction c using limitRecOn with
  | H₁ => simp only [succ_zero, mul_one]
  | H₂ c IH =>
    rw [mul_succ, IH, ← add_assoc, add_assoc _ b, ba, ← mul_succ]
  | H₃ c l IH =>
    -- Porting note: Unused.
    -- have := add_mul_limit_aux ba l IH
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assoc]

theorem add_mul_limit {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c) : (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

theorem add_le_of_forall_add_lt {a b c : Ordinal} (hb : 0 < b) (h : ∀ d < b, a + d < c) :
    a + b ≤ c := by
  have H : a + (c - a) = c :=
    Ordinal.add_sub_cancel_of_le
      (by
        rw [← add_zero a]
        exact (h _ hb).le)
  rw [← H]
  apply add_le_add_left _ a
  by_contra! hb
  exact (h _ hb).ne H

theorem IsNormal.apply_omega0 {f : Ordinal.{u} → Ordinal.{v}} (hf : IsNormal f) :
    ⨆ n : ℕ, f n = f ω := by rw [← iSup_natCast, hf.map_iSup]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias IsNormal.apply_omega := IsNormal.apply_omega0

@[simp]
theorem iSup_add_nat (o : Ordinal) : ⨆ n : ℕ, o + n = o + ω :=
  (isNormal_add_right o).apply_omega0

set_option linter.deprecated false in
@[deprecated iSup_add_nat (since := "2024-08-27")]
theorem sup_add_nat (o : Ordinal) : (sup fun n : ℕ => o + n) = o + ω :=
  (isNormal_add_right o).apply_omega0

@[simp]
theorem iSup_mul_nat (o : Ordinal) : ⨆ n : ℕ, o * n = o * ω := by
  rcases eq_zero_or_pos o with (rfl | ho)
  · rw [zero_mul]
    exact iSup_eq_zero_iff.2 fun n => zero_mul (n : Ordinal)
  · exact (isNormal_mul_right ho).apply_omega0

set_option linter.deprecated false in
@[deprecated iSup_add_nat (since := "2024-08-27")]
theorem sup_mul_nat (o : Ordinal) : (sup fun n : ℕ => o * n) = o * ω := by
  rcases eq_zero_or_pos o with (rfl | ho)
  · rw [zero_mul]
    exact sup_eq_zero_iff.2 fun n => zero_mul (n : Ordinal)
  · exact (mul_isNormal ho).apply_omega0

end Ordinal

namespace Cardinal

open Ordinal

theorem isLimit_ord {c} (co : ℵ₀ ≤ c) : (ord c).IsLimit := by
  refine ⟨fun h => aleph0_ne_zero ?_, fun a => lt_imp_lt_of_le_imp_le fun h => ?_⟩
  · rw [← Ordinal.le_zero, ord_le] at h
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h
  · rw [ord_le] at h ⊢
    rwa [← @add_one_of_aleph0_le (card a), ← card_succ]
    rw [← ord_le, ← le_succ_of_isLimit, ord_le]
    · exact co.trans h
    · rw [ord_aleph0]
      exact Ordinal.isLimit_omega0

@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
alias ord_isLimit := isLimit_ord

theorem noMaxOrder {c} (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.toType :=
  toType_noMax_of_succ_lt (isLimit_ord h).2

end Cardinal

set_option linter.style.longFile 2600
