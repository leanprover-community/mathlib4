/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.nat.part_enat
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Data.Part
import Mathbin.Data.Enat.Lattice
import Mathbin.Tactic.NormNum

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`. This implementation uses `part ℕ` as an
implementation. Use `ℕ∞` instead unless you care about computability.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid part_enat`
* `canonically_ordered_add_monoid part_enat`
* `complete_linear_order part_enat`

There is no additive analogue of `monoid_with_zero`; if there were then `part_enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `part_enat` to `ℕ∞`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : part_enat ≃+ ℕ∞`
* `with_top_order_iso : part_enat ≃o ℕ∞`

## Implementation details

`part_enat` is defined to be `part ℕ`.

`+` and `≤` are defined on `part_enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `part_enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

part_enat, ℕ∞
-/


open Part hiding some

/-- Type of natural numbers with infinity (`⊤`) -/
def PartEnat : Type :=
  Part ℕ
#align part_enat PartEnat

namespace PartEnat

/-- The computable embedding `ℕ → part_enat`.

This coincides with the coercion `coe : ℕ → part_enat`, see `part_enat.some_eq_coe`.
However, `coe` is noncomputable so `some` is preferable when computability is a concern. -/
def some : ℕ → PartEnat :=
  Part.some
#align part_enat.some PartEnat.some

instance : Zero PartEnat :=
  ⟨some 0⟩

instance : Inhabited PartEnat :=
  ⟨0⟩

instance : One PartEnat :=
  ⟨some 1⟩

instance : Add PartEnat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => get x h.1 + get y h.2⟩⟩

instance (n : ℕ) : Decidable (some n).Dom :=
  isTrue trivial

@[simp]
theorem dom_some (x : ℕ) : (some x).Dom :=
  trivial
#align part_enat.dom_some PartEnat.dom_some

instance : AddCommMonoid PartEnat where
  add := (· + ·)
  zero := 0
  add_comm x y := Part.ext' and_comm fun _ _ => add_comm _ _
  zero_add x := Part.ext' (true_and_iff _) fun _ _ => zero_add _
  add_zero x := Part.ext' (and_true_iff _) fun _ _ => add_zero _
  add_assoc x y z := Part.ext' and_assoc fun _ _ => add_assoc _ _ _

instance : AddCommMonoidWithOne PartEnat :=
  { PartEnat.addCommMonoid with
    one := 1
    natCast := some
    nat_cast_zero := rfl
    nat_cast_succ := fun _ => Part.ext' (true_and_iff _).symm fun _ _ => rfl }

theorem some_eq_coe (n : ℕ) : some n = n :=
  rfl
#align part_enat.some_eq_coe PartEnat.some_eq_coe

@[simp, norm_cast]
theorem coe_inj {x y : ℕ} : (x : PartEnat) = y ↔ x = y :=
  Part.some_inj
#align part_enat.coe_inj PartEnat.coe_inj

@[simp]
theorem dom_coe (x : ℕ) : (x : PartEnat).Dom :=
  trivial
#align part_enat.dom_coe PartEnat.dom_coe

instance : LE PartEnat :=
  ⟨fun x y => ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy⟩

instance : Top PartEnat :=
  ⟨none⟩

instance : Bot PartEnat :=
  ⟨0⟩

instance : HasSup PartEnat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => x.get h.1 ⊔ y.get h.2⟩⟩

theorem le_def (x y : PartEnat) :
    x ≤ y ↔ ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl
#align part_enat.le_def PartEnat.le_def

@[elab_as_elim]
protected theorem cases_on' {P : PartEnat → Prop} :
    ∀ a : PartEnat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on
#align part_enat.cases_on' PartEnat.cases_on'

@[elab_as_elim]
protected theorem cases_on {P : PartEnat → Prop} : ∀ a : PartEnat, P ⊤ → (∀ n : ℕ, P n) → P a :=
  by
  simp only [← some_eq_coe]
  exact PartEnat.cases_on'
#align part_enat.cases_on PartEnat.cases_on

@[simp]
theorem top_add (x : PartEnat) : ⊤ + x = ⊤ :=
  Part.ext' (false_and_iff _) fun h => h.left.elim
#align part_enat.top_add PartEnat.top_add

@[simp]
theorem add_top (x : PartEnat) : x + ⊤ = ⊤ := by rw [add_comm, top_add]
#align part_enat.add_top PartEnat.add_top

@[simp]
theorem coe_get {x : PartEnat} (h : x.Dom) : (x.get h : PartEnat) = x :=
  by
  rw [← some_eq_coe]
  exact Part.ext' (iff_of_true trivial h) fun _ _ => rfl
#align part_enat.coe_get PartEnat.coe_get

@[simp, norm_cast]
theorem get_coe' (x : ℕ) (h : (x : PartEnat).Dom) : get (x : PartEnat) h = x := by
  rw [← coe_inj, coe_get]
#align part_enat.get_coe' PartEnat.get_coe'

theorem get_coe {x : ℕ} : get (x : PartEnat) (dom_coe x) = x :=
  get_coe' _ _
#align part_enat.get_coe PartEnat.get_coe

theorem coe_add_get {x : ℕ} {y : PartEnat} (h : ((x : PartEnat) + y).Dom) :
    get ((x : PartEnat) + y) h = x + get y h.2 :=
  by
  simp only [← some_eq_coe] at h⊢
  rfl
#align part_enat.coe_add_get PartEnat.coe_add_get

@[simp]
theorem get_add {x y : PartEnat} (h : (x + y).Dom) : get (x + y) h = x.get h.1 + y.get h.2 :=
  rfl
#align part_enat.get_add PartEnat.get_add

@[simp]
theorem get_zero (h : (0 : PartEnat).Dom) : (0 : PartEnat).get h = 0 :=
  rfl
#align part_enat.get_zero PartEnat.get_zero

@[simp]
theorem get_one (h : (1 : PartEnat).Dom) : (1 : PartEnat).get h = 1 :=
  rfl
#align part_enat.get_one PartEnat.get_one

theorem get_eq_iff_eq_some {a : PartEnat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some
#align part_enat.get_eq_iff_eq_some PartEnat.get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : PartEnat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = b := by
  rw [get_eq_iff_eq_some, some_eq_coe]
#align part_enat.get_eq_iff_eq_coe PartEnat.get_eq_iff_eq_coe

theorem dom_of_le_of_dom {x y : PartEnat} : x ≤ y → y.Dom → x.Dom := fun ⟨h, _⟩ => h
#align part_enat.dom_of_le_of_dom PartEnat.dom_of_le_of_dom

theorem dom_of_le_some {x : PartEnat} {y : ℕ} (h : x ≤ some y) : x.Dom :=
  dom_of_le_of_dom h trivial
#align part_enat.dom_of_le_some PartEnat.dom_of_le_some

theorem dom_of_le_coe {x : PartEnat} {y : ℕ} (h : x ≤ y) : x.Dom :=
  by
  rw [← some_eq_coe] at h
  exact dom_of_le_some h
#align part_enat.dom_of_le_coe PartEnat.dom_of_le_coe

instance decidableLe (x y : PartEnat) [Decidable x.Dom] [Decidable y.Dom] : Decidable (x ≤ y) :=
  if hx : x.Dom then
    decidable_of_decidable_of_iff
        (show Decidable (∀ hy : (y : PartEnat).Dom, x.get hx ≤ (y : PartEnat).get hy) from
          forallPropDecidable _) <|
      by
      dsimp [(· ≤ ·)]
      simp only [hx, exists_prop_of_true, forall_true_iff]
  else
    if hy : y.Dom then is_false fun h => hx <| dom_of_le_of_dom h hy
    else isTrue ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩
#align part_enat.decidable_le PartEnat.decidableLe

/-- The coercion `ℕ → part_enat` preserves `0` and addition. -/
def coeHom : ℕ →+ PartEnat :=
  ⟨coe, Nat.cast_zero, Nat.cast_add⟩
#align part_enat.coe_hom PartEnat.coeHom

@[simp]
theorem coe_coeHom : ⇑coe_hom = coe :=
  rfl
#align part_enat.coe_coe_hom PartEnat.coe_coeHom

instance : PartialOrder PartEnat where
  le := (· ≤ ·)
  le_refl x := ⟨id, fun _ => le_rfl⟩
  le_trans := fun x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ =>
    ⟨hxy₁ ∘ hyz₁, fun _ => le_trans (hxy₂ _) (hyz₂ _)⟩
  le_antisymm := fun x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ =>
    Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymm (hxy₂ _) (hyx₂ _)

theorem lt_def (x y : PartEnat) : x < y ↔ ∃ hx : x.Dom, ∀ hy : y.Dom, x.get hx < y.get hy :=
  by
  rw [lt_iff_le_not_le, le_def, le_def, not_exists]
  constructor
  · rintro ⟨⟨hyx, H⟩, h⟩
    by_cases hx : x.dom
    · use hx
      intro hy
      specialize H hy
      specialize h fun _ => hy
      rw [not_forall] at h
      cases' h with hx' h
      rw [not_le] at h
      exact h
    · specialize h fun hx' => (hx hx').elim
      rw [not_forall] at h
      cases' h with hx' h
      exact (hx hx').elim
  · rintro ⟨hx, H⟩
    exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_le (h _) (H _)⟩
#align part_enat.lt_def PartEnat.lt_def

@[simp, norm_cast]
theorem coe_le_coe {x y : ℕ} : (x : PartEnat) ≤ y ↔ x ≤ y :=
  by
  rw [← some_eq_coe, ← some_eq_coe]
  exact ⟨fun ⟨_, h⟩ => h trivial, fun h => ⟨fun _ => trivial, fun _ => h⟩⟩
#align part_enat.coe_le_coe PartEnat.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℕ} : (x : PartEnat) < y ↔ x < y := by
  rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]
#align part_enat.coe_lt_coe PartEnat.coe_lt_coe

@[simp]
theorem get_le_get {x y : PartEnat} {hx : x.Dom} {hy : y.Dom} : x.get hx ≤ y.get hy ↔ x ≤ y := by
  conv =>
    lhs
    rw [← coe_le_coe, coe_get, coe_get]
#align part_enat.get_le_get PartEnat.get_le_get

theorem le_coe_iff (x : PartEnat) (n : ℕ) : x ≤ n ↔ ∃ h : x.Dom, x.get h ≤ n :=
  by
  rw [← some_eq_coe]
  show (∃ h : True → x.dom, _) ↔ ∃ h : x.dom, x.get h ≤ n
  simp only [forall_prop_of_true, some_eq_coe, dom_coe, get_coe']
#align part_enat.le_coe_iff PartEnat.le_coe_iff

theorem lt_coe_iff (x : PartEnat) (n : ℕ) : x < n ↔ ∃ h : x.Dom, x.get h < n := by
  simp only [lt_def, forall_prop_of_true, get_coe', dom_coe]
#align part_enat.lt_coe_iff PartEnat.lt_coe_iff

theorem coe_le_iff (n : ℕ) (x : PartEnat) : (n : PartEnat) ≤ x ↔ ∀ h : x.Dom, n ≤ x.get h :=
  by
  rw [← some_eq_coe]
  simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff]
  rfl
#align part_enat.coe_le_iff PartEnat.coe_le_iff

theorem coe_lt_iff (n : ℕ) (x : PartEnat) : (n : PartEnat) < x ↔ ∀ h : x.Dom, n < x.get h :=
  by
  rw [← some_eq_coe]
  simp only [lt_def, exists_prop_of_true, dom_some, forall_true_iff]
  rfl
#align part_enat.coe_lt_iff PartEnat.coe_lt_iff

instance NeZero.one : NeZero (1 : PartEnat) :=
  ⟨coe_inj.Not.mpr (by decide)⟩
#align part_enat.ne_zero.one PartEnat.NeZero.one

instance semilatticeSup : SemilatticeSup PartEnat :=
  { PartEnat.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩
    sup_le := fun x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ =>
      ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }
#align part_enat.semilattice_sup PartEnat.semilatticeSup

instance orderBot : OrderBot PartEnat where
  bot := ⊥
  bot_le _ := ⟨fun _ => trivial, fun _ => Nat.zero_le _⟩
#align part_enat.order_bot PartEnat.orderBot

instance orderTop : OrderTop PartEnat where
  top := ⊤
  le_top x := ⟨fun h => False.elim h, fun hy => False.elim hy⟩
#align part_enat.order_top PartEnat.orderTop

theorem eq_zero_iff {x : PartEnat} : x = 0 ↔ x ≤ 0 :=
  eq_bot_iff
#align part_enat.eq_zero_iff PartEnat.eq_zero_iff

theorem ne_zero_iff {x : PartEnat} : x ≠ 0 ↔ ⊥ < x :=
  bot_lt_iff_ne_bot.symm
#align part_enat.ne_zero_iff PartEnat.ne_zero_iff

theorem dom_of_lt {x y : PartEnat} : x < y → x.Dom :=
  PartEnat.cases_on x not_top_lt fun _ _ => dom_coe _
#align part_enat.dom_of_lt PartEnat.dom_of_lt

theorem top_eq_none : (⊤ : PartEnat) = none :=
  rfl
#align part_enat.top_eq_none PartEnat.top_eq_none

@[simp]
theorem coe_lt_top (x : ℕ) : (x : PartEnat) < ⊤ :=
  Ne.lt_top fun h => absurd (congr_arg Dom h) <| by simpa only [dom_coe] using true_ne_false
#align part_enat.coe_lt_top PartEnat.coe_lt_top

@[simp]
theorem coe_ne_top (x : ℕ) : (x : PartEnat) ≠ ⊤ :=
  ne_of_lt (coe_lt_top x)
#align part_enat.coe_ne_top PartEnat.coe_ne_top

theorem not_isMax_coe (x : ℕ) : ¬IsMax (x : PartEnat) :=
  not_isMax_of_lt (coe_lt_top x)
#align part_enat.not_is_max_coe PartEnat.not_isMax_coe

theorem ne_top_iff {x : PartEnat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n := by
  simpa only [← some_eq_coe] using Part.ne_none_iff
#align part_enat.ne_top_iff PartEnat.ne_top_iff

theorem ne_top_iff_dom {x : PartEnat} : x ≠ ⊤ ↔ x.Dom := by
  classical exact not_iff_comm.1 part.eq_none_iff'.symm
#align part_enat.ne_top_iff_dom PartEnat.ne_top_iff_dom

theorem not_dom_iff_eq_top {x : PartEnat} : ¬x.Dom ↔ x = ⊤ :=
  Iff.not_left ne_top_iff_dom.symm
#align part_enat.not_dom_iff_eq_top PartEnat.not_dom_iff_eq_top

theorem ne_top_of_lt {x y : PartEnat} (h : x < y) : x ≠ ⊤ :=
  ne_of_lt <| lt_of_lt_of_le h le_top
#align part_enat.ne_top_of_lt PartEnat.ne_top_of_lt

theorem eq_top_iff_forall_lt (x : PartEnat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartEnat) < x :=
  by
  constructor
  · rintro rfl n
    exact coe_lt_top _
  · contrapose!
    rw [ne_top_iff]
    rintro ⟨n, rfl⟩
    exact ⟨n, irrefl _⟩
#align part_enat.eq_top_iff_forall_lt PartEnat.eq_top_iff_forall_lt

theorem eq_top_iff_forall_le (x : PartEnat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartEnat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_le (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩
#align part_enat.eq_top_iff_forall_le PartEnat.eq_top_iff_forall_le

theorem pos_iff_one_le {x : PartEnat} : 0 < x ↔ 1 ≤ x :=
  PartEnat.cases_on x (by simp only [iff_true_iff, le_top, coe_lt_top, ← @Nat.cast_zero PartEnat])
    fun n =>
    by
    rw [← Nat.cast_zero, ← Nat.cast_one, PartEnat.coe_lt_coe, PartEnat.coe_le_coe]
    rfl
#align part_enat.pos_iff_one_le PartEnat.pos_iff_one_le

instance : IsTotal PartEnat (· ≤ ·)
    where Total x y :=
    PartEnat.cases_on x (Or.inr le_top)
      (PartEnat.cases_on y (fun _ => Or.inl le_top) fun x y =>
        (le_total x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2))

noncomputable instance : LinearOrder PartEnat :=
  { PartEnat.partialOrder with
    le_total := IsTotal.total
    decidableLe := Classical.decRel _
    max := (· ⊔ ·)
    max_def := @sup_eq_maxDefault _ _ (id _) _ }

instance : BoundedOrder PartEnat :=
  { PartEnat.orderTop, PartEnat.orderBot with }

noncomputable instance : Lattice PartEnat :=
  { PartEnat.semilatticeSup with
    inf := min
    inf_le_left := min_le_left
    inf_le_right := min_le_right
    le_inf := fun _ _ _ => le_min }

instance : OrderedAddCommMonoid PartEnat :=
  { PartEnat.linearOrder, PartEnat.addCommMonoid with
    add_le_add_left := fun a b ⟨h₁, h₂⟩ c =>
      PartEnat.cases_on c (by simp) fun c =>
        ⟨fun h => And.intro (dom_coe _) (h₁ h.2), fun h => by
          simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩ }

instance : CanonicallyOrderedAddMonoid PartEnat :=
  { PartEnat.semilatticeSup, PartEnat.orderBot,
    PartEnat.orderedAddCommMonoid with
    le_self_add := fun a b =>
      PartEnat.cases_on b (le_top.trans_eq (add_top _).symm) fun b =>
        PartEnat.cases_on a (top_add _).ge fun a =>
          (coe_le_coe.2 le_self_add).trans_eq (Nat.cast_add _ _)
    exists_add_of_le := fun a b =>
      PartEnat.cases_on b (fun _ => ⟨⊤, (add_top _).symm⟩) fun b =>
        PartEnat.cases_on a (fun h => ((coe_lt_top _).not_le h).elim) fun a h =>
          ⟨(b - a : ℕ), by
            rw [← Nat.cast_add, coe_inj, add_comm, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩ }

protected theorem add_lt_add_right {x y z : PartEnat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z :=
  by
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩
  induction' y using PartEnat.cases_on with n
  · rw [top_add]
    apply_mod_cast coe_lt_top
  norm_cast  at h; apply_mod_cast add_lt_add_right h
#align part_enat.add_lt_add_right PartEnat.add_lt_add_right

protected theorem add_lt_add_iff_right {x y z : PartEnat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => PartEnat.add_lt_add_right h hz⟩
#align part_enat.add_lt_add_iff_right PartEnat.add_lt_add_iff_right

protected theorem add_lt_add_iff_left {x y z : PartEnat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := by
  rw [add_comm z, add_comm z, PartEnat.add_lt_add_iff_right hz]
#align part_enat.add_lt_add_iff_left PartEnat.add_lt_add_iff_left

protected theorem lt_add_iff_pos_right {x y : PartEnat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y :=
  by
  conv_rhs => rw [← PartEnat.add_lt_add_iff_left hx]
  rw [add_zero]
#align part_enat.lt_add_iff_pos_right PartEnat.lt_add_iff_pos_right

theorem lt_add_one {x : PartEnat} (hx : x ≠ ⊤) : x < x + 1 :=
  by
  rw [PartEnat.lt_add_iff_pos_right hx]
  norm_cast
  norm_num
#align part_enat.lt_add_one PartEnat.lt_add_one

theorem le_of_lt_add_one {x y : PartEnat} (h : x < y + 1) : x ≤ y :=
  by
  induction' y using PartEnat.cases_on with n; apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.le_of_lt_succ; apply_mod_cast h
#align part_enat.le_of_lt_add_one PartEnat.le_of_lt_add_one

theorem add_one_le_of_lt {x y : PartEnat} (h : x < y) : x + 1 ≤ y :=
  by
  induction' y using PartEnat.cases_on with n; apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.succ_le_of_lt; apply_mod_cast h
#align part_enat.add_one_le_of_lt PartEnat.add_one_le_of_lt

theorem add_one_le_iff_lt {x y : PartEnat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y :=
  by
  constructor; swap; exact add_one_le_of_lt
  intro h; rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using PartEnat.cases_on with n; apply coe_lt_top
  apply_mod_cast Nat.lt_of_succ_le; apply_mod_cast h
#align part_enat.add_one_le_iff_lt PartEnat.add_one_le_iff_lt

theorem lt_add_one_iff_lt {x y : PartEnat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y :=
  by
  constructor; exact le_of_lt_add_one
  intro h; rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using PartEnat.cases_on with n;
  · rw [top_add]
    apply coe_lt_top
  apply_mod_cast Nat.lt_succ_of_le; apply_mod_cast h
#align part_enat.lt_add_one_iff_lt PartEnat.lt_add_one_iff_lt

theorem add_eq_top_iff {a b : PartEnat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  apply PartEnat.cases_on a <;> apply PartEnat.cases_on b <;> simp <;>
      simp only [(Nat.cast_add _ _).symm, PartEnat.coe_ne_top] <;>
    simp
#align part_enat.add_eq_top_iff PartEnat.add_eq_top_iff

protected theorem add_right_cancel_iff {a b c : PartEnat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b :=
  by
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩
  apply PartEnat.cases_on a <;> apply PartEnat.cases_on b <;>
        simp [add_eq_top_iff, coe_ne_top, @eq_comm _ (⊤ : PartEnat)] <;>
      simp only [(Nat.cast_add _ _).symm, add_left_cancel_iff, PartEnat.coe_inj, add_comm] <;>
    tauto
#align part_enat.add_right_cancel_iff PartEnat.add_right_cancel_iff

protected theorem add_left_cancel_iff {a b c : PartEnat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  rw [add_comm a, add_comm a, PartEnat.add_right_cancel_iff ha]
#align part_enat.add_left_cancel_iff PartEnat.add_left_cancel_iff

section WithTop

/-- Computably converts an `part_enat` to a `ℕ∞`. -/
def toWithTop (x : PartEnat) [Decidable x.Dom] : ℕ∞ :=
  x.toOption
#align part_enat.to_with_top PartEnat.toWithTop

theorem toWithTop_top : toWithTop ⊤ = ⊤ :=
  rfl
#align part_enat.to_with_top_top PartEnat.toWithTop_top

@[simp]
theorem toWithTop_top' {h : Decidable (⊤ : PartEnat).Dom} : toWithTop ⊤ = ⊤ := by
  convert to_with_top_top
#align part_enat.to_with_top_top' PartEnat.toWithTop_top'

theorem toWithTop_zero : toWithTop 0 = 0 :=
  rfl
#align part_enat.to_with_top_zero PartEnat.toWithTop_zero

@[simp]
theorem toWithTop_zero' {h : Decidable (0 : PartEnat).Dom} : toWithTop 0 = 0 := by
  convert to_with_top_zero
#align part_enat.to_with_top_zero' PartEnat.toWithTop_zero'

theorem toWithTop_some (n : ℕ) : toWithTop (some n) = n :=
  rfl
#align part_enat.to_with_top_some PartEnat.toWithTop_some

theorem toWithTop_coe (n : ℕ) {_ : Decidable (n : PartEnat).Dom} : toWithTop n = n := by
  simp only [← some_eq_coe, ← to_with_top_some]
#align part_enat.to_with_top_coe PartEnat.toWithTop_coe

@[simp]
theorem toWithTop_coe' (n : ℕ) {h : Decidable (n : PartEnat).Dom} : toWithTop (n : PartEnat) = n :=
  by convert to_with_top_coe n
#align part_enat.to_with_top_coe' PartEnat.toWithTop_coe'

@[simp]
theorem toWithTop_le {x y : PartEnat} :
    ∀ [Decidable x.Dom] [Decidable y.Dom], to_with_top x ≤ to_with_top y ↔ x ≤ y :=
  PartEnat.cases_on y (by simp) (PartEnat.cases_on x (by simp) (by intros <;> simp))
#align part_enat.to_with_top_le PartEnat.toWithTop_le

@[simp]
theorem toWithTop_lt {x y : PartEnat} [Decidable x.Dom] [Decidable y.Dom] :
    toWithTop x < toWithTop y ↔ x < y :=
  lt_iff_lt_of_le_iff_le toWithTop_le
#align part_enat.to_with_top_lt PartEnat.toWithTop_lt

end WithTop

section WithTopEquiv

open Classical

@[simp]
theorem toWithTop_add {x y : PartEnat} : toWithTop (x + y) = toWithTop x + toWithTop y := by
  apply PartEnat.cases_on y <;> apply PartEnat.cases_on x <;> simp [← Nat.cast_add, ← ENat.coe_add]
#align part_enat.to_with_top_add PartEnat.toWithTop_add

/-- `equiv` between `part_enat` and `ℕ∞` (for the order isomorphism see
`with_top_order_iso`). -/
noncomputable def withTopEquiv : PartEnat ≃ ℕ∞
    where
  toFun x := toWithTop x
  invFun x :=
    match x with
    | Option.some n => coe n
    | none => ⊤
  left_inv x := by apply PartEnat.cases_on x <;> intros <;> simp <;> rfl
  right_inv x := by cases x <;> simp [with_top_equiv._match_1] <;> rfl
#align part_enat.with_top_equiv PartEnat.withTopEquiv

@[simp]
theorem withTopEquiv_top : withTopEquiv ⊤ = ⊤ :=
  to_with_top_top'
#align part_enat.with_top_equiv_top PartEnat.withTopEquiv_top

@[simp]
theorem withTopEquiv_coe (n : Nat) : withTopEquiv n = n :=
  toWithTop_coe' _
#align part_enat.with_top_equiv_coe PartEnat.withTopEquiv_coe

@[simp]
theorem withTopEquiv_zero : withTopEquiv 0 = 0 := by
  simpa only [Nat.cast_zero] using with_top_equiv_coe 0
#align part_enat.with_top_equiv_zero PartEnat.withTopEquiv_zero

@[simp]
theorem withTopEquiv_le {x y : PartEnat} : withTopEquiv x ≤ withTopEquiv y ↔ x ≤ y :=
  to_with_top_le
#align part_enat.with_top_equiv_le PartEnat.withTopEquiv_le

@[simp]
theorem withTopEquiv_lt {x y : PartEnat} : withTopEquiv x < withTopEquiv y ↔ x < y :=
  to_with_top_lt
#align part_enat.with_top_equiv_lt PartEnat.withTopEquiv_lt

/-- `to_with_top` induces an order isomorphism between `part_enat` and `ℕ∞`. -/
noncomputable def withTopOrderIso : PartEnat ≃o ℕ∞ :=
  { withTopEquiv with map_rel_iff' := fun _ _ => withTopEquiv_le }
#align part_enat.with_top_order_iso PartEnat.withTopOrderIso

@[simp]
theorem withTopEquiv_symm_top : withTopEquiv.symm ⊤ = ⊤ :=
  rfl
#align part_enat.with_top_equiv_symm_top PartEnat.withTopEquiv_symm_top

@[simp]
theorem withTopEquiv_symm_coe (n : Nat) : withTopEquiv.symm n = n :=
  rfl
#align part_enat.with_top_equiv_symm_coe PartEnat.withTopEquiv_symm_coe

@[simp]
theorem withTopEquiv_symm_zero : withTopEquiv.symm 0 = 0 :=
  rfl
#align part_enat.with_top_equiv_symm_zero PartEnat.withTopEquiv_symm_zero

@[simp]
theorem withTopEquiv_symm_le {x y : ℕ∞} : withTopEquiv.symm x ≤ withTopEquiv.symm y ↔ x ≤ y := by
  rw [← with_top_equiv_le] <;> simp
#align part_enat.with_top_equiv_symm_le PartEnat.withTopEquiv_symm_le

@[simp]
theorem withTopEquiv_symm_lt {x y : ℕ∞} : withTopEquiv.symm x < withTopEquiv.symm y ↔ x < y := by
  rw [← with_top_equiv_lt] <;> simp
#align part_enat.with_top_equiv_symm_lt PartEnat.withTopEquiv_symm_lt

/-- `to_with_top` induces an additive monoid isomorphism between `part_enat` and `ℕ∞`. -/
noncomputable def withTopAddEquiv : PartEnat ≃+ ℕ∞ :=
  { withTopEquiv with
    map_add' := fun x y => by simp only [with_top_equiv] <;> convert to_with_top_add }
#align part_enat.with_top_add_equiv PartEnat.withTopAddEquiv

end WithTopEquiv

theorem lt_wf : @WellFounded PartEnat (· < ·) := by
  classical
    change WellFounded fun a b : PartEnat => a < b
    simp_rw [← to_with_top_lt]
    exact InvImage.wf _ (WithTop.wellFounded_lt Nat.lt_wfRel)
#align part_enat.lt_wf PartEnat.lt_wf

instance : WellFoundedLt PartEnat :=
  ⟨lt_wf⟩

instance : IsWellOrder PartEnat (· < ·) where

instance : WellFoundedRelation PartEnat :=
  ⟨(· < ·), lt_wf⟩

section Find

variable (P : ℕ → Prop) [DecidablePred P]

/-- The smallest `part_enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : PartEnat :=
  ⟨∃ n, P n, Nat.find⟩
#align part_enat.find PartEnat.find

@[simp]
theorem find_get (h : (find P).Dom) : (find P).get h = Nat.find h :=
  rfl
#align part_enat.find_get PartEnat.find_get

theorem find_dom (h : ∃ n, P n) : (find P).Dom :=
  h
#align part_enat.find_dom PartEnat.find_dom

theorem lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : PartEnat) < find P :=
  by
  rw [coe_lt_iff]; intro h'; rw [find_get]
  have := @Nat.find_spec P _ h'
  contrapose! this
  exact h _ this
#align part_enat.lt_find PartEnat.lt_find

theorem lt_find_iff (n : ℕ) : (n : PartEnat) < find P ↔ ∀ m ≤ n, ¬P m :=
  by
  refine' ⟨_, lt_find P n⟩
  intro h m hm
  by_cases H : (find P).Dom
  · apply Nat.find_min H
    rw [coe_lt_iff] at h
    specialize h H
    exact lt_of_le_of_lt hm h
  · exact not_exists.mp H m
#align part_enat.lt_find_iff PartEnat.lt_find_iff

theorem find_le (n : ℕ) (h : P n) : find P ≤ n :=
  by
  rw [le_coe_iff]
  refine' ⟨⟨_, h⟩, @Nat.find_min' P _ _ _ h⟩
#align part_enat.find_le PartEnat.find_le

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => lt_find P n fun _ _ => h _⟩
#align part_enat.find_eq_top_iff PartEnat.find_eq_top_iff

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop PartEnat :=
  { PartEnat.linearOrder, PartEnat.orderedAddCommMonoid, PartEnat.orderTop with
    top_add' := top_add }

noncomputable instance : CompleteLinearOrder PartEnat :=
  { PartEnat.lattice, withTopOrderIso.symm.toGaloisInsertion.liftCompleteLattice,
    PartEnat.linearOrder with
    inf := (· ⊓ ·)
    sup := (· ⊔ ·)
    top := ⊤
    bot := ⊥
    le := (· ≤ ·)
    lt := (· < ·) }

end PartEnat

