/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.SetTheory.Ordinal.Basic

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

* `Order.IsSuccLimit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limitRecOn` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.
* `IsNormal`: a function `f : Ordinal → Ordinal` satisfies `IsNormal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

assert_not_exists Field Module

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

instance : IsLeftCancelAdd Ordinal where
  add_left_cancel a b c h := by simpa only [le_antisymm_iff, add_le_add_iff_left] using h

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

/-! ### Limit ordinals -/

/-- A limit ordinal is an ordinal which is not zero and not a successor.

Deprecated: use `Order.IsSuccLimit` instead. -/
@[deprecated IsSuccLimit (since := "2025-02-09")]
def IsLimit (o : Ordinal) : Prop :=
  IsSuccLimit o

theorem isSuccLimit_iff {o : Ordinal} : IsSuccLimit o ↔ o ≠ 0 ∧ IsSuccPrelimit o := by
  simp [IsSuccLimit]

@[deprecated (since := "2025-07-09")]
alias isLimit_iff := isSuccLimit_iff

@[deprecated (since := "2025-07-09")]
alias IsLimit.isSuccPrelimit := IsSuccLimit.isSuccPrelimit

@[deprecated (since := "2025-07-09")]
alias IsLimit.succ_lt := IsSuccLimit.succ_lt

@[simp]
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal) := isSuccPrelimit_bot

@[simp]
theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Ordinal) := not_isSuccLimit_bot

@[deprecated (since := "2025-07-09")]
alias not_zero_isLimit := not_isSuccLimit_zero

@[deprecated (since := "2025-07-09")]
alias not_succ_isLimit := not_isSuccLimit_succ

set_option linter.deprecated false in
@[deprecated not_isSuccLimit_succ (since := "2025-07-09")]
theorem not_succ_of_isLimit {o} (h : IsLimit o) : ¬∃ a, o = succ a
  | ⟨a, e⟩ => not_succ_isLimit a (e ▸ h)

@[deprecated (since := "2025-07-09")]
alias succ_lt_of_isLimit := IsSuccLimit.succ_lt_iff

@[deprecated (since := "2025-07-09")]
alias le_succ_of_isLimit := IsSuccLimit.le_succ_iff

@[deprecated (since := "2025-07-09")]
alias limit_le := IsSuccLimit.le_iff_forall_le

@[deprecated (since := "2025-07-09")]
alias lt_limit := IsSuccLimit.lt_iff_exists_lt

@[simp]
theorem isSuccPrelimit_lift {o : Ordinal} : IsSuccPrelimit (lift.{u, v} o) ↔ IsSuccPrelimit o :=
  liftInitialSeg.isSuccPrelimit_apply_iff

@[simp]
theorem isSuccLimit_lift {o : Ordinal} : IsSuccLimit (lift.{u, v} o) ↔ IsSuccLimit o :=
  liftInitialSeg.isSuccLimit_apply_iff

@[deprecated (since := "2025-07-09")]
alias lift_isLimit := isSuccLimit_lift

set_option linter.deprecated false in
@[deprecated IsSuccLimit.bot_lt (since := "2025-07-09")]
theorem IsLimit.pos {o : Ordinal} (h : IsLimit o) : 0 < o :=
  IsSuccLimit.bot_lt h

set_option linter.deprecated false in
@[deprecated IsSuccLimit.ne_bot (since := "2025-07-09")]
theorem IsLimit.ne_zero {o : Ordinal} (h : IsLimit o) : o ≠ 0 :=
  h.pos.ne'

theorem natCast_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) (n : ℕ) : n < o := by
  simpa using h.add_natCast_lt h.bot_lt n

@[deprecated (since := "2025-07-09")]
alias IsLimit.nat_lt := natCast_lt_of_isSuccLimit

theorem one_lt_of_isSuccLimit {o : Ordinal} (h : IsSuccLimit o) : 1 < o :=
  mod_cast natCast_lt_of_isSuccLimit h 1

@[deprecated (since := "2025-07-09")]
alias IsLimit.one_lt := one_lt_of_isSuccLimit

theorem zero_or_succ_or_isSuccLimit (o : Ordinal) : o = 0 ∨ o ∈ range succ ∨ IsSuccLimit o := by
  simpa using isMin_or_mem_range_succ_or_isSuccLimit o

set_option linter.deprecated false in
@[deprecated zero_or_succ_or_isSuccLimit (since := "2025-07-09")]
theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ IsLimit o := by
  simpa [eq_comm] using isMin_or_mem_range_succ_or_isSuccLimit o

set_option linter.deprecated false in
@[deprecated zero_or_succ_or_isSuccLimit (since := "2025-07-09")]
theorem isLimit_of_not_succ_of_ne_zero {o : Ordinal} (h : ¬∃ a, o = succ a) (h' : o ≠ 0) :
    IsLimit o := ((zero_or_succ_or_limit o).resolve_left h').resolve_left h

@[deprecated (since := "2025-07-09")]
alias IsLimit.sSup_Iio := IsSuccLimit.sSup_Iio

@[deprecated (since := "2025-07-09")]
alias IsLimit.iSup_Iio := IsSuccLimit.iSup_Iio

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_elim]
def limitRecOn {motive : Ordinal → Sort*} (o : Ordinal)
    (zero : motive 0) (succ : ∀ o, motive o → motive (succ o))
    (limit : ∀ o, IsSuccLimit o → (∀ o' < o, motive o') → motive o) : motive o :=
  SuccOrder.limitRecOn o (fun _a ha ↦ ha.eq_bot ▸ zero) (fun a _ ↦ succ a) limit

@[simp]
theorem limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRecOn motive 0 H₁ H₂ H₃ = H₁ :=
  SuccOrder.limitRecOn_isMin _ _ _ isMin_bot

@[simp]
theorem limitRecOn_succ {motive} (o H₁ H₂ H₃) :
    @limitRecOn motive (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃) :=
  SuccOrder.limitRecOn_succ ..

@[simp]
theorem limitRecOn_limit {motive} (o H₁ H₂ H₃ h) :
    @limitRecOn motive o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃ :=
  SuccOrder.limitRecOn_of_isSuccLimit ..

/-- Bounded recursion on ordinals. Similar to `limitRecOn`, with the assumption `o < l`
  added to all cases. The final term's domain is the ordinals below `l`. -/
@[elab_as_elim]
def boundedLimitRecOn {l : Ordinal} (lLim : IsSuccLimit l) {motive : Iio l → Sort*} (o : Iio l)
    (zero : motive ⟨0, lLim.bot_lt⟩)
    (succ : (o : Iio l) → motive o → motive ⟨succ o, lLim.succ_lt o.2⟩)
    (limit : (o : Iio l) → IsSuccLimit o.1 → (Π o' < o, motive o') → motive o) : motive o :=
  limitRecOn (motive := fun p ↦ (h : p < l) → motive ⟨p, h⟩) o.1 (fun _ ↦ zero)
    (fun o ih h ↦ succ ⟨o, _⟩ <| ih <| (lt_succ o).trans h)
    (fun _o ho ih _ ↦ limit _ ho fun _o' h ↦ ih _ h _) o.2

@[simp]
theorem boundedLimitRec_zero {l} (lLim : IsSuccLimit l) {motive} (H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim motive ⟨0, lLim.bot_lt⟩ H₁ H₂ H₃ = H₁ := by
  rw [boundedLimitRecOn, limitRecOn_zero]

@[simp]
theorem boundedLimitRec_succ {l} (lLim : IsSuccLimit l) {motive} (o H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim motive ⟨succ o.1, lLim.succ_lt o.2⟩ H₁ H₂ H₃ = H₂ o
    (@boundedLimitRecOn l lLim motive o H₁ H₂ H₃) := by
  rw [boundedLimitRecOn, limitRecOn_succ]
  rfl

theorem boundedLimitRec_limit {l} (lLim : IsSuccLimit l) {motive} (o H₁ H₂ H₃ oLim) :
    @boundedLimitRecOn l lLim motive o H₁ H₂ H₃ = H₃ o oLim (fun x _ ↦
    @boundedLimitRecOn l lLim motive x H₁ H₂ H₃) := by
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
  convert enum_lt_enum.mpr _
  · rw [enum_typein]
  · rw [Subtype.mk_lt_mk, lt_succ_iff]

theorem toType_noMax_of_succ_lt {o : Ordinal} (ho : ∀ a < o, succ a < o) : NoMaxOrder o.toType :=
  ⟨has_succ_of_type_succ_lt (type_toType _ ▸ ho)⟩

theorem bounded_singleton {r : α → α → Prop} [IsWellOrder α r] (hr : IsSuccLimit (type r)) (x) :
    Bounded r {x} := by
  refine ⟨enum r ⟨succ (typein r x), hr.succ_lt (typein_lt_type r x)⟩, ?_⟩
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

theorem mk_Iio_ordinal (o : Ordinal.{u}) :
    #(Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [lift_card, ← typein_ordinal]
  rfl

/-! ### The predecessor of an ordinal -/

/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`, and `o` otherwise. -/
def pred (o : Ordinal) : Ordinal :=
  isSuccPrelimitRecOn o (fun a _ ↦ a) (fun a _ ↦ a)

@[simp]
theorem pred_succ (o) : pred (succ o) = o :=
  isSuccPrelimitRecOn_succ ..

theorem pred_eq_of_isSuccPrelimit {o} : IsSuccPrelimit o → pred o = o :=
  isSuccPrelimitRecOn_of_isSuccPrelimit _ _

alias _root_.Order.IsSuccPrelimit.ordinalPred_eq := pred_eq_of_isSuccPrelimit

theorem _root_.Order.IsSuccLimit.ordinalPred_eq {o} (ho : IsSuccLimit o) : pred o = o :=
  ho.isSuccPrelimit.ordinalPred_eq

@[simp]
theorem pred_zero : pred 0 = 0 :=
  isSuccPrelimit_zero.ordinalPred_eq

@[simp]
theorem pred_le_iff_le_succ {a b} : pred a ≤ b ↔ a ≤ succ b := by
  obtain ⟨a, rfl⟩ | ha := mem_range_succ_or_isSuccPrelimit a
  · simp
  · rw [ha.ordinalPred_eq, ha.le_succ_iff]

@[deprecated pred_le_iff_le_succ (since := "2025-02-11")]
alias pred_le := pred_le_iff_le_succ

@[simp]
theorem lt_pred_iff_succ_lt {a b} : a < pred b ↔ succ a < b :=
  le_iff_le_iff_lt_iff_lt.1 pred_le_iff_le_succ

@[deprecated lt_pred_iff_succ_lt (since := "2025-02-11")]
alias lt_pred := lt_pred_iff_succ_lt

theorem pred_le_self (o) : pred o ≤ o := by
  simpa using le_succ o

/-- `Ordinal.pred` and `Order.succ` form a Galois insertion. -/
def pred_succ_gi : GaloisInsertion pred succ :=
  GaloisConnection.toGaloisInsertion @pred_le_iff_le_succ (by simp)

theorem pred_surjective : Function.Surjective pred :=
  pred_succ_gi.l_surjective

theorem self_le_succ_pred (o) : o ≤ succ (pred o) :=
  pred_succ_gi.gc.le_u_l o

theorem pred_eq_iff_isSuccPrelimit {o} : pred o = o ↔ IsSuccPrelimit o := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simpa using (lt_succ a).ne
  · simp_rw [ho.ordinalPred_eq, ho]

@[deprecated pred_eq_iff_isSuccPrelimit (since := "2025-02-11")]
theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬∃ a, o = succ a := by
  simpa [eq_comm, isSuccPrelimit_iff_succ_ne] using pred_eq_iff_isSuccPrelimit

@[deprecated pred_eq_iff_isSuccPrelimit (since := "2025-02-11")]
theorem pred_eq_iff_not_succ' {o} : pred o = o ↔ ∀ a, o ≠ succ a := by
  simpa [eq_comm, isSuccPrelimit_iff_succ_ne] using pred_eq_iff_isSuccPrelimit

theorem pred_lt_iff_not_isSuccPrelimit {o} : pred o < o ↔ ¬ IsSuccPrelimit o := by
  rw [(pred_le_self o).lt_iff_ne]
  exact pred_eq_iff_isSuccPrelimit.not

@[deprecated pred_lt_iff_not_isSuccPrelimit (since := "2025-02-11")]
theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a := by
  simpa [eq_comm, isSuccPrelimit_iff_succ_ne] using pred_lt_iff_not_isSuccPrelimit

theorem succ_pred_eq_iff_not_isSuccPrelimit {o} : succ (pred o) = o ↔ ¬ IsSuccPrelimit o := by
  rw [← (self_le_succ_pred o).ge_iff_eq', succ_le_iff, pred_lt_iff_not_isSuccPrelimit]

@[deprecated succ_pred_iff_is_succ (since := "2025-02-11")]
theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a := by
  simpa [eq_comm, isSuccPrelimit_iff_succ_ne] using succ_pred_eq_iff_not_isSuccPrelimit

@[deprecated IsSuccPrelimit.succ_lt_iff (since := "2025-02-11")]
theorem succ_lt_of_not_succ {o b : Ordinal} (h : ¬∃ a, o = succ a) : succ b < o ↔ b < o := by
  apply (isSuccPrelimit_of_succ_ne _).succ_lt_iff
  simpa [eq_comm] using h

@[deprecated isSuccPrelimit_lift (since := "2025-02-11")]
theorem lift_is_succ {o : Ordinal.{v}} : (∃ a, lift.{u} o = succ a) ↔ ∃ a, o = succ a := by
  simpa [eq_comm, not_isSuccPrelimit_iff', - isSuccPrelimit_lift] using
    isSuccPrelimit_lift.not

@[simp]
theorem lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o) := by
  obtain ⟨a, rfl⟩ | ho := mem_range_succ_or_isSuccPrelimit o
  · simp
  · rwa [ho.ordinalPred_eq, eq_comm, pred_eq_iff_isSuccPrelimit, isSuccPrelimit_lift]

/-! ### Normal ordinal functions -/

/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.

  Todo: deprecate this in favor of `Order.IsNormal`. -/
def IsNormal (f : Ordinal → Ordinal) : Prop :=
  Order.IsNormal f

theorem IsNormal.limit_le {f} (H : IsNormal f) :
    ∀ {o}, IsSuccLimit o → ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a :=
  H.le_iff_forall_le

theorem IsNormal.limit_lt {f} (H : IsNormal f) {o} (h : IsSuccLimit o) {a} :
    a < f o ↔ ∃ b < o, a < f b :=
  H.lt_iff_exists_lt h

theorem IsNormal.strictMono {f} (H : IsNormal f) : StrictMono f :=
  Order.IsNormal.strictMono H

theorem IsNormal.monotone {f} (H : IsNormal f) : Monotone f :=
  H.strictMono.monotone

theorem isNormal_iff_strictMono_limit (f : Ordinal → Ordinal) :
    IsNormal f ↔ StrictMono f ∧ ∀ o, IsSuccLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a :=
  isNormal_iff

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

theorem IsNormal.le_iff_eq {f} (H : IsNormal f) {a} : f a ≤ a ↔ f a = a :=
  H.le_apply.ge_iff_eq'

theorem IsNormal.le_set {f o} (H : IsNormal f) (p : Set Ordinal) (p0 : p.Nonempty) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f a ≤ o :=
  ⟨fun h _ pa => (H.le_iff.2 ((H₂ _).1 le_rfl _ pa)).trans h, fun h => by
    induction b using limitRecOn with
    | zero =>
      obtain ⟨x, px⟩ := p0
      have := Ordinal.le_zero.1 ((H₂ _).1 (Ordinal.zero_le _) _ px)
      rw [this] at px
      exact h _ px
    | succ S _ =>
      rcases not_forall₂.1 (mt (H₂ S).2 <| (lt_succ S).not_ge) with ⟨a, h₁, h₂⟩
      exact (H.le_iff.2 <| succ_le_of_lt <| not_le.1 h₂).trans (h _ h₁)
    | limit S L _ =>
      refine (H.le_iff_forall_le L).2 fun a h' => ?_
      rcases not_forall₂.1 (mt (H₂ a).2 h'.not_ge) with ⟨b, h₁, h₂⟩
      exact (H.le_iff.2 <| (not_le.1 h₂).le).trans (h _ h₁)⟩

theorem IsNormal.le_set' {f o} (H : IsNormal f) (p : Set α) (p0 : p.Nonempty) (g : α → Ordinal) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, g a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f (g a) ≤ o := by
  simpa [H₂] using H.le_set (g '' p) (p0.image g) b

theorem IsNormal.refl : IsNormal id :=
  .id

theorem IsNormal.trans {f g} (H₁ : IsNormal f) (H₂ : IsNormal g) : IsNormal (f ∘ g) :=
  H₁.comp H₂

theorem IsNormal.isSuccLimit {f} (H : IsNormal f) {o} (ho : IsSuccLimit o) : IsSuccLimit (f o) :=
  H.map_isSuccLimit ho

/-! ### Subtraction on ordinals -/

instance existsAddOfLE : ExistsAddOfLE Ordinal where
  exists_add_of_le {a b} := by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ ↦ ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinal_type_eq.symm⟩

-- TODO: This gives us `zero_le` as an immediate consequence.
-- Private/protect the old theorem, golf proofs.
instance canonicallyOrderedAdd : CanonicallyOrderedAdd Ordinal where
  le_self_add := le_add_right

/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
instance sub : Sub Ordinal where
  sub a b := if h : b ≤ a then Classical.choose (exists_add_of_le h) else 0

private theorem sub_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a - b = 0 :=
  dif_neg h.not_ge

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : b + (a - b) = a := by
  change b + dite _ _ _ = a
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_add_of_le h)).symm

@[simp]
theorem add_sub_cancel (a b : Ordinal) : a + b - a = b := by
  simpa using Ordinal.add_sub_cancel_of_le (le_add_right a b)

theorem le_add_sub (a b : Ordinal) : a ≤ b + (a - b) := by
  obtain h | h := le_or_gt b a
  · exact (Ordinal.add_sub_cancel_of_le h).ge
  · simpa [sub_eq_zero_of_lt h] using h.le

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b + c := by
  refine ⟨fun h ↦ (le_add_sub a b).trans (add_le_add_left h _), fun h ↦ ?_⟩
  obtain h' | h' := le_or_gt b a
  · rwa [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h']
  · simp [sub_eq_zero_of_lt h']

theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : Ordinal) : a - b ≤ a :=
  sub_le.2 <| le_add_left _ _

theorem le_sub_of_le {a b c : Ordinal} (h : b ≤ a) : c ≤ a - b ↔ b + c ≤ a := by
  rw [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h]

theorem sub_lt_of_le {a b c : Ordinal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
  lt_iff_lt_of_le_iff_le (le_sub_of_le h)

@[simp]
theorem sub_zero (a : Ordinal) : a - 0 = a := by simpa only [zero_add] using add_sub_cancel 0 a

@[simp]
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by rw [← Ordinal.le_zero]; apply sub_le_self

@[simp]
theorem sub_self (a : Ordinal) : a - a = 0 := by simpa only [add_zero] using add_sub_cancel a 0

protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b, fun h => by
    rwa [← Ordinal.le_zero, sub_le, add_zero]⟩

protected theorem sub_ne_zero_iff_lt {a b : Ordinal} : a - b ≠ 0 ↔ b < a := by
  simpa using Ordinal.sub_eq_zero_iff_le.not

theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) :=
  eq_of_forall_ge_iff fun d => by rw [sub_le, sub_le, sub_le, add_assoc]

@[simp]
theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by
  rw [← sub_sub, add_sub_cancel]

theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c ≤ a) : c ≤ a - b := by
  rw [← add_le_add_iff_left b]
  exact h.trans (le_add_sub a b)

theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by
  obtain hab | hba := lt_or_ge a b
  · rwa [Ordinal.sub_eq_zero_iff_le.2 hab.le]
  · rwa [sub_lt_of_le hba]

theorem lt_add_iff {a b c : Ordinal} (hc : c ≠ 0) : a < b + c ↔ ∃ d < c, a ≤ b + d := by
  use fun h ↦ ⟨_, sub_lt_of_lt_add h hc.bot_lt, le_add_sub a b⟩
  rintro ⟨d, hd, ha⟩
  exact ha.trans_lt (add_lt_add_left hd b)

theorem add_le_iff {a b c : Ordinal} (hb : b ≠ 0) : a + b ≤ c ↔ ∀ d < b, a + d < c := by
  simpa using (lt_add_iff hb).not

theorem lt_add_iff_of_isSuccLimit {a b c : Ordinal} (hc : IsSuccLimit c) :
    a < b + c ↔ ∃ d < c, a < b + d := by
  rw [lt_add_iff hc.ne_bot]
  constructor <;> rintro ⟨d, hd, ha⟩
  · refine ⟨_, hc.succ_lt hd, ?_⟩
    rwa [add_succ, lt_succ_iff]
  · exact ⟨d, hd, ha.le⟩

@[deprecated (since := "2025-07-08")]
alias lt_add_of_limit := lt_add_iff_of_isSuccLimit

theorem add_le_iff_of_isSuccLimit {a b c : Ordinal} (hb : IsSuccLimit b) :
    a + b ≤ c ↔ ∀ d < b, a + d ≤ c := by
  simpa using (lt_add_iff_of_isSuccLimit hb).not

@[deprecated (since := "2025-07-08")]
alias add_le_of_limit := add_le_iff_of_isSuccLimit

theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) := by
  rw [isNormal_iff_strictMono_limit]
  exact ⟨add_left_strictMono, fun _ l _ ↦ (add_le_iff_of_isSuccLimit l).2⟩

theorem isSuccLimit_add (a : Ordinal) {b : Ordinal} : IsSuccLimit b → IsSuccLimit (a + b) :=
  (isNormal_add_right a).isSuccLimit

@[deprecated (since := "2025-07-09")]
alias isLimit_add := isSuccLimit_add

@[deprecated (since := "2025-07-09")]
alias IsLimit.add := isSuccLimit_add

theorem isSuccLimit_sub {a b : Ordinal} (ha : IsSuccLimit a) (h : b < a) : IsSuccLimit (a - b) := by
  rw [isSuccLimit_iff, Ordinal.sub_ne_zero_iff_lt, isSuccPrelimit_iff_succ_lt]
  refine ⟨h, fun c hc ↦ ?_⟩
  rw [lt_sub] at hc ⊢
  rw [add_succ]
  exact ha.succ_lt hc

@[deprecated (since := "2025-07-09")]
alias isLimit_sub := isSuccLimit_sub

/-! ### Multiplication of ordinals -/

/-- The multiplication of ordinals `o₁` and `o₂` is the (well-founded) lexicographic order on
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
            simp only [true_and]
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
            simp⟩⟩⟩

theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a :=
  mul_add_one a b

instance mulLeftMono : MulLeftMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

instance mulRightMono : MulRightMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ a * b := by
  convert mul_le_mul_left' (one_le_iff_pos.2 hb) a
  rw [mul_one a]

theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_pos.2 hb) a
  rw [one_mul a]

private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
    (h : IsSuccLimit (type s)) (H : ∀ b' < type s, type r * b' ≤ c) (l : c < type r * type s) :
    False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) by
    obtain ⟨b, a⟩ := enum _ ⟨_, l⟩
    exact irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r), typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · refine Sum.inr ⟨a', ?_⟩
      subst e
      obtain ⟨-, -, h⟩ | ⟨-, h⟩ := h
      · exact (irrefl _ h).elim
      · exact h
    · refine Sum.inl (⟨b', ?_⟩, a')
      obtain ⟨-, -, h⟩ | ⟨e, h⟩ := h
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
      simp only [subrel_val, Prod.lex_def, e₂, Prod.lex_def, dif_pos, subrel_val,
        or_false, dif_neg, not_false_iff, Sum.lex_inr_inl, false_and] at h ⊢
      obtain ⟨-, -, h₂_h⟩ | e₂ := h₂ <;> [exact asymm h h₂_h; exact e₂ rfl]
    · simp [e₂, show b₂ ≠ b₁ from e₂ ▸ e₁]
    · simpa only [dif_neg e₁, dif_neg e₂, Prod.lex_def, subrel_val, Subtype.mk_eq_mk,
        Sum.lex_inl_inl] using h

theorem mul_le_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit b) :
    a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c :=
  ⟨fun h _ l => (mul_le_mul_left' l.le _).trans h, fun H =>
    -- We use the `induction` tactic in order to change `h`/`H` too.
    le_of_not_gt <| by
      induction a using inductionOn with
      | H α r =>
        induction b using inductionOn with
        | H β s =>
          exact mul_le_of_limit_aux h H⟩

@[deprecated (since := "2025-07-09")]
alias mul_le_of_limit := mul_le_iff_of_isSuccLimit

theorem isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·) := by
  refine IsNormal.of_succ_lt (fun b ↦ ?_) fun hb ↦ ?_
  · simpa [mul_succ] using (add_lt_add_iff_left (a * b)).2 h
  · simpa [IsLUB, IsLeast, upperBounds, lowerBounds, mul_le_iff_of_isSuccLimit hb] using
      fun c hc ↦ mul_le_mul_left' hc.le a

theorem lt_mul_iff_of_isSuccLimit {a b c : Ordinal} (h : IsSuccLimit c) :
    a < b * c ↔ ∃ c' < c, a < b * c' := by
  simpa using (mul_le_iff_of_isSuccLimit h).not

@[deprecated (since := "2025-07-09")]
alias lt_mul_of_limit := lt_mul_iff_of_isSuccLimit

instance : PosMulStrictMono Ordinal where
  elim a _b _c h := (isNormal_mul_right a.2).strictMono h

@[deprecated mul_lt_mul_left (since := "2025-08-26")]
theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  mul_lt_mul_left a0

@[deprecated mul_le_mul_left (since := "2025-08-26")]
theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  mul_le_mul_iff_right₀ a0

@[deprecated mul_lt_mul_left (since := "2025-08-26")]
theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : c * a < c * b :=
  (mul_lt_mul_left c0).mpr h

@[deprecated mul_pos (since := "2025-08-26")]
protected theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
  mul_pos h₁ h₂

@[deprecated mul_ne_zero (since := "2025-08-26")]
protected theorem mul_ne_zero {a b : Ordinal} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mul_ne_zero ha hb

@[deprecated mul_le_mul_left (since := "2025-08-26")]
theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
  (mul_le_mul_iff_right₀ h0).mp h

@[deprecated mul_left_cancel_iff_of_pos (since := "2025-08-26")]
theorem mul_right_inj {a b c : Ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  mul_left_cancel_iff_of_pos a0

theorem isSuccLimit_mul {a b : Ordinal} (a0 : 0 < a) : IsSuccLimit b → IsSuccLimit (a * b) :=
  (isNormal_mul_right a0).isSuccLimit

@[deprecated (since := "2025-07-09")]
alias isLimit_mul := isSuccLimit_mul

theorem isSuccLimit_mul_left {a b : Ordinal} (l : IsSuccLimit a) (b0 : 0 < b) :
    IsSuccLimit (a * b) := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
  · rw [mul_succ]
    exact isSuccLimit_add _ l
  · exact isSuccLimit_mul l.bot_lt lb

@[deprecated (since := "2025-07-09")]
alias isLimit_mul_left := isSuccLimit_mul_left

theorem smul_eq_mul : ∀ (n : ℕ) (a : Ordinal), n • a = a * n
  | 0, a => by rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | n + 1, a => by rw [succ_nsmul, Nat.cast_add, mul_add, Nat.cast_one, mul_one, smul_eq_mul n]

private theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c)
    (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymm
    ((mul_le_iff_of_isSuccLimit l).2 fun c' h => by
      apply (mul_le_mul_left' (le_succ c') _).trans
      rw [IH _ h]
      apply (add_le_add_left _ _).trans
      · rw [← mul_succ]
        exact mul_le_mul_left' (succ_le_of_lt <| l.succ_lt h) _
      · rw [← ba]
        exact le_add_right _ _)
    (mul_le_mul_right' (le_add_right _ _) _)

theorem add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a * succ c + b := by
  induction c using limitRecOn with
  | zero => simp only [succ_zero, mul_one]
  | succ c IH =>
    rw [mul_succ, IH, ← add_assoc, add_assoc _ b, ba, ← mul_succ]
  | limit c l IH =>
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assoc]

theorem add_mul_of_isSuccLimit {a b c : Ordinal} (ba : b + a = a) (l : IsSuccLimit c) :
    (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

@[deprecated (since := "2025-07-09")]
alias add_mul_limit := add_mul_of_isSuccLimit

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
  | zero => simp only [mul_zero, Ordinal.zero_le]
  | succ _ _ => rw [succ_le_iff, lt_div c0]
  | limit _ h₁ h₂ =>
    revert h₁ h₂
    simp +contextual only [mul_le_iff_of_isSuccLimit, IsSuccLimit.le_iff_forall_le, forall_true_iff]

theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c :=
  lt_iff_lt_of_le_iff_le <| le_div b0

theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b * c) : a / b ≤ c :=
  if b0 : b = 0 then by simp only [b0, div_zero, Ordinal.zero_le]
  else
    (div_le b0).2 <| h.trans_lt <| (mul_lt_mul_left (Ordinal.pos_iff_ne_zero.2 b0)).2 (lt_succ c)

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

theorem isSuccLimit_add_iff {a b : Ordinal} :
    IsSuccLimit (a + b) ↔ IsSuccLimit b ∨ b = 0 ∧ IsSuccLimit a := by
  constructor <;> intro h
  · by_cases h' : b = 0
    · rw [h', add_zero] at h
      right
      exact ⟨h', h⟩
    left
    rw [← add_sub_cancel a b]
    apply isSuccLimit_sub h
    suffices a + 0 < a + b by simpa only [add_zero] using this
    rwa [add_lt_add_iff_left, Ordinal.pos_iff_ne_zero]
  rcases h with (h | ⟨rfl, h⟩)
  · exact isSuccLimit_add a h
  · simpa only [add_zero]

theorem isSuccLimit_add_iff_of_isSuccLimit {a b : Ordinal} (h : IsSuccLimit a) :
    IsSuccLimit (a + b) ↔ IsSuccPrelimit b := by
  rw [isSuccLimit_add_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simpa
  · simp [hb, isSuccLimit_iff]

@[deprecated (since := "2025-07-09")]
alias isLimit_add_iff := isSuccLimit_add_iff

theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ => ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩, fun ⟨d, e⟩ => by
      rw [e, ← mul_add]
      apply dvd_mul_right⟩

theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b
  | a, _, b0, ⟨b, e⟩ => by
    subst e
    simpa only [mul_one] using
      mul_le_mul_left'
        (one_le_iff_ne_zero.2 fun h : b = 0 => by simp [h] at b0)
        a

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

/-! ### Casting naturals into ordinals, compatibility with operations -/

instance instCharZero : CharZero Ordinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← Cardinal.ord_nat, ← Cardinal.ord_nat, Cardinal.ord_inj, Nat.cast_inj] at h

@[simp]
theorem one_add_natCast (m : ℕ) : 1 + (m : Ordinal) = succ m := by
  rw [← Nat.cast_one, ← Nat.cast_add, add_comm]
  rfl

@[simp]
theorem one_add_ofNat (m : ℕ) [m.AtLeastTwo] :
    1 + (ofNat(m) : Ordinal) = Order.succ (OfNat.ofNat m : Ordinal) :=
  one_add_natCast m

@[simp, norm_cast]
theorem natCast_mul (m : ℕ) : ∀ n : ℕ, ((m * n : ℕ) : Ordinal) = m * n
  | 0 => by simp
  | n + 1 => by rw [Nat.mul_succ, Nat.cast_add, natCast_mul m n, Nat.cast_succ, mul_add_one]

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ((m - n : ℕ) : Ordinal) = m - n := by
  rcases le_total m n with h | h
  · rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (Nat.cast_le.2 h), Nat.cast_zero]
  · rw [← add_left_cancel_iff (a := ↑n), ← Nat.cast_add, add_tsub_cancel_of_le h,
      Ordinal.add_sub_cancel_of_le (Nat.cast_le.2 h)]

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

@[simp, norm_cast]
theorem natCast_mod (m n : ℕ) : ((m % n : ℕ) : Ordinal) = m % n := by
  rw [← add_left_cancel_iff, div_add_mod, ← natCast_div, ← natCast_mul, ← Nat.cast_add,
    Nat.div_add_mod]

@[simp]
theorem lift_natCast : ∀ n : ℕ, lift.{u, v} n = n
  | 0 => by simp
  | n + 1 => by simp [lift_natCast n]

@[simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u, v} ofNat(n) = OfNat.ofNat n :=
  lift_natCast n

/-! ### Properties of `ω` -/

theorem lt_omega0 {o : Ordinal} : o < ω ↔ ∃ n : ℕ, o = n := by
  simp_rw [← Cardinal.ord_aleph0, Cardinal.lt_ord, lt_aleph0, card_eq_nat]

theorem nat_lt_omega0 (n : ℕ) : ↑n < ω :=
  lt_omega0.2 ⟨_, rfl⟩

theorem eq_nat_or_omega0_le (o : Ordinal) : (∃ n : ℕ, o = n) ∨ ω ≤ o := by
  obtain ho | ho := lt_or_ge o ω
  · exact Or.inl <| lt_omega0.1 ho
  · exact Or.inr ho

@[simp]
theorem omega0_pos : 0 < ω :=
  nat_lt_omega0 0

@[simp]
theorem omega0_ne_zero : ω ≠ 0 :=
  omega0_pos.ne'

@[simp]
theorem one_lt_omega0 : 1 < ω := by simpa only [Nat.cast_one] using nat_lt_omega0 1

theorem isSuccLimit_omega0 : IsSuccLimit ω := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  refine ⟨omega0_ne_zero, fun o h => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact nat_lt_omega0 (n + 1)

@[deprecated (since := "2025-07-09")]
alias isLimit_omega0 := isSuccLimit_omega0

@[deprecated (since := "2025-07-09")]
alias nat_lt_limit := natCast_lt_of_isSuccLimit

theorem omega0_le {o : Ordinal} : ω ≤ o ↔ ∀ n : ℕ, ↑n ≤ o :=
  ⟨fun h n => (nat_lt_omega0 _).le.trans h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega0.1 h
      rw [e, ← succ_le_iff]; exact H (n + 1)⟩

theorem omega0_le_of_isSuccLimit {o} (h : IsSuccLimit o) : ω ≤ o :=
  omega0_le.2 fun n => le_of_lt <| natCast_lt_of_isSuccLimit h n

@[deprecated (since := "2025-07-09")]
alias omega0_le_of_isLimit := omega0_le_of_isSuccLimit

theorem natCast_add_omega0 (n : ℕ) : n + ω = ω := by
  refine le_antisymm (le_of_forall_lt fun a ha ↦ ?_) (le_add_left _ _)
  obtain ⟨b, hb', hb⟩ := (lt_add_iff omega0_ne_zero).1 ha
  obtain ⟨m, rfl⟩ := lt_omega0.1 hb'
  apply hb.trans_lt
  exact_mod_cast nat_lt_omega0 (n + m)

theorem one_add_omega0 : 1 + ω = ω :=
  mod_cast natCast_add_omega0 1

theorem add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  exact natCast_add_omega0 n

@[simp]
theorem natCast_add_of_omega0_le {o} (h : ω ≤ o) (n : ℕ) : n + o = o := by
  rw [← Ordinal.add_sub_cancel_of_le h, ← add_assoc, natCast_add_omega0]

@[simp]
theorem one_add_of_omega0_le {o} (h : ω ≤ o) : 1 + o = o :=
  mod_cast natCast_add_of_omega0_le h 1

open Ordinal

-- TODO: prove `IsSuccPrelimit a ↔ ω ∣ a`.
theorem isSuccLimit_iff_omega0_dvd {a : Ordinal} : IsSuccLimit a ↔ a ≠ 0 ∧ ω ∣ a := by
  refine ⟨fun l => ⟨l.ne_bot, ⟨a / ω, le_antisymm ?_ (mul_div_le _ _)⟩⟩, fun h => ?_⟩
  · refine l.le_iff_forall_le.2 fun x hx => le_of_lt ?_
    rw [← div_lt omega0_ne_zero, ← succ_le_iff, le_div omega0_ne_zero, mul_succ,
      add_le_iff_of_isSuccLimit isSuccLimit_omega0]
    intro b hb
    rcases lt_omega0.1 hb with ⟨n, rfl⟩
    exact
      (add_le_add_right (mul_div_le _ _) _).trans
        (lt_sub.1 <| natCast_lt_of_isSuccLimit (isSuccLimit_sub l hx) _).le
  · rcases h with ⟨a0, b, rfl⟩
    refine isSuccLimit_mul_left isSuccLimit_omega0 (Ordinal.pos_iff_ne_zero.2 <| mt ?_ a0)
    intro e
    simp only [e, mul_zero]

@[deprecated (since := "2025-07-09")]
alias isLimit_iff_omega0_dvd := isSuccLimit_iff_omega0_dvd

@[simp]
theorem natCast_mod_omega0 (n : ℕ) : n % ω = n :=
  mod_eq_of_lt (nat_lt_omega0 n)

end Ordinal

namespace Cardinal

open Ordinal

@[simp]
theorem add_one_of_aleph0_le {c} (h : ℵ₀ ≤ c) : c + 1 = c := by
  rw [add_comm, ← card_ord c, ← card_one, ← card_add, one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

theorem isSuccLimit_ord {c} (co : ℵ₀ ≤ c) : IsSuccLimit (ord c) := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  refine ⟨fun h => aleph0_ne_zero ?_, fun a => lt_imp_lt_of_le_imp_le fun h => ?_⟩
  · rw [← Ordinal.le_zero, ord_le] at h
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h
  · rw [ord_le] at h ⊢
    rwa [← @add_one_of_aleph0_le (card a), ← card_succ]
    rw [← ord_le, ← IsSuccLimit.le_succ_iff, ord_le]
    · exact co.trans h
    · rw [ord_aleph0]
      exact Ordinal.isSuccLimit_omega0

@[deprecated (since := "2025-07-09")]
alias isLimit_ord := isSuccLimit_ord

theorem noMaxOrder {c} (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.toType :=
  toType_noMax_of_succ_lt fun _ ↦ (isSuccLimit_ord h).succ_lt

end Cardinal
