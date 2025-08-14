/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Part
import Mathlib.Tactic.NormNum

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`. This implementation uses `Part ℕ` as an
implementation. Use `ℕ∞` instead unless you care about computability.

## Main definitions

The following instances are defined:

* `OrderedAddCommMonoid PartENat`
* `CanonicallyOrderedAdd PartENat`
* `CompleteLinearOrder PartENat`

There is no additive analogue of `MonoidWithZero`; if there were then `PartENat` could
be an `AddMonoidWithTop`.

* `toWithTop` : the map from `PartENat` to `ℕ∞`, with theorems that it plays well
  with `+` and `≤`.

* `withTopAddEquiv : PartENat ≃+ ℕ∞`
* `withTopOrderIso : PartENat ≃o ℕ∞`

## Implementation details

`PartENat` is defined to be `Part ℕ`.

`+` and `≤` are defined on `PartENat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `PartENat`.

Before the `open scoped Classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `toWithTopZero` proved by `rfl`,
followed by `@[simp] lemma toWithTopZero'` whose proof uses `convert`.


## Tags

PartENat, ℕ∞
-/


open Part hiding some

/-- Type of natural numbers with infinity (`⊤`) -/
def PartENat : Type :=
  Part ℕ

namespace PartENat

/-- The computable embedding `ℕ → PartENat`.

This coincides with the coercion `coe : ℕ → PartENat`, see `PartENat.some_eq_natCast`. -/
@[coe]
def some : ℕ → PartENat :=
  Part.some

instance : Zero PartENat :=
  ⟨some 0⟩

instance : Inhabited PartENat :=
  ⟨0⟩

instance : One PartENat :=
  ⟨some 1⟩

instance : Add PartENat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => get x h.1 + get y h.2⟩⟩

instance (n : ℕ) : Decidable (some n).Dom :=
  isTrue trivial

@[simp]
theorem dom_some (x : ℕ) : (some x).Dom :=
  trivial

instance addCommMonoid : AddCommMonoid PartENat where
  add := (· + ·)
  zero := 0
  add_comm _ _ := Part.ext' and_comm fun _ _ => add_comm _ _
  zero_add _ := Part.ext' (iff_of_eq (true_and _)) fun _ _ => zero_add _
  add_zero _ := Part.ext' (iff_of_eq (and_true _)) fun _ _ => add_zero _
  add_assoc _ _ _ := Part.ext' and_assoc fun _ _ => add_assoc _ _ _
  nsmul := nsmulRec

instance : AddCommMonoidWithOne PartENat :=
  { PartENat.addCommMonoid with
    one := 1
    natCast := some
    natCast_zero := rfl
    natCast_succ := fun _ => Part.ext' (iff_of_eq (true_and _)).symm fun _ _ => rfl }

theorem some_eq_natCast (n : ℕ) : some n = n :=
  rfl

instance : CharZero PartENat where
  cast_injective := Part.some_injective

/-- Alias of `Nat.cast_inj` specialized to `PartENat` -/
theorem natCast_inj {x y : ℕ} : (x : PartENat) = y ↔ x = y :=
  Nat.cast_inj

@[simp]
theorem dom_natCast (x : ℕ) : (x : PartENat).Dom :=
  trivial

@[simp]
theorem dom_ofNat (x : ℕ) [x.AtLeastTwo] : (ofNat(x) : PartENat).Dom :=
  trivial

@[simp]
theorem dom_zero : (0 : PartENat).Dom :=
  trivial

@[simp]
theorem dom_one : (1 : PartENat).Dom :=
  trivial

instance : CanLift PartENat ℕ (↑) Dom :=
  ⟨fun n hn => ⟨n.get hn, Part.some_get _⟩⟩

instance : LE PartENat :=
  ⟨fun x y => ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy⟩

instance : Top PartENat :=
  ⟨none⟩

instance : Bot PartENat :=
  ⟨0⟩

instance : Max PartENat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => x.get h.1 ⊔ y.get h.2⟩⟩

theorem le_def (x y : PartENat) :
    x ≤ y ↔ ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl

@[elab_as_elim]
protected theorem casesOn' {P : PartENat → Prop} :
    ∀ a : PartENat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on

@[elab_as_elim]
protected theorem casesOn {P : PartENat → Prop} : ∀ a : PartENat, P ⊤ → (∀ n : ℕ, P n) → P a := by
  exact PartENat.casesOn'

-- not a simp lemma as we will provide a `LinearOrderedAddCommMonoidWithTop` instance later
theorem top_add (x : PartENat) : ⊤ + x = ⊤ :=
  Part.ext' (iff_of_eq (false_and _)) fun h => h.left.elim

-- not a simp lemma as we will provide a `LinearOrderedAddCommMonoidWithTop` instance later
theorem add_top (x : PartENat) : x + ⊤ = ⊤ := by rw [add_comm, top_add]

@[simp]
theorem natCast_get {x : PartENat} (h : x.Dom) : (x.get h : PartENat) = x := by
  exact Part.ext' (iff_of_true trivial h) fun _ _ => rfl

@[simp, norm_cast]
theorem get_natCast' (x : ℕ) (h : (x : PartENat).Dom) : get (x : PartENat) h = x := by
  rw [← natCast_inj, natCast_get]

theorem get_natCast {x : ℕ} : get (x : PartENat) (dom_natCast x) = x :=
  get_natCast' _ _

theorem coe_add_get {x : ℕ} {y : PartENat} (h : ((x : PartENat) + y).Dom) :
    get ((x : PartENat) + y) h = x + get y h.2 := by
  rfl

@[simp]
theorem get_add {x y : PartENat} (h : (x + y).Dom) : get (x + y) h = x.get h.1 + y.get h.2 :=
  rfl

@[simp]
theorem get_zero (h : (0 : PartENat).Dom) : (0 : PartENat).get h = 0 :=
  rfl

@[simp]
theorem get_one (h : (1 : PartENat).Dom) : (1 : PartENat).get h = 1 :=
  rfl

@[simp]
theorem get_ofNat' (x : ℕ) [x.AtLeastTwo] (h : (ofNat(x) : PartENat).Dom) :
    Part.get (ofNat(x) : PartENat) h = ofNat(x) :=
  get_natCast' x h

nonrec theorem get_eq_iff_eq_some {a : PartENat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : PartENat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = b := by
  rw [get_eq_iff_eq_some]
  rfl

theorem dom_of_le_of_dom {x y : PartENat} : x ≤ y → y.Dom → x.Dom := fun ⟨h, _⟩ => h

theorem dom_of_le_some {x : PartENat} {y : ℕ} (h : x ≤ some y) : x.Dom :=
  dom_of_le_of_dom h trivial

theorem dom_of_le_natCast {x : PartENat} {y : ℕ} (h : x ≤ y) : x.Dom := by
  exact dom_of_le_some h

instance decidableLe (x y : PartENat) [Decidable x.Dom] [Decidable y.Dom] : Decidable (x ≤ y) :=
  if hx : x.Dom then
    decidable_of_decidable_of_iff (le_def x y).symm
  else
    if hy : y.Dom then isFalse fun h => hx <| dom_of_le_of_dom h hy
    else isTrue ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩

instance partialOrder : PartialOrder PartENat where
  le := (· ≤ ·)
  le_refl _ := ⟨id, fun _ => le_rfl⟩
  le_trans := fun _ _ _ ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ =>
    ⟨hxy₁ ∘ hyz₁, fun _ => le_trans (hxy₂ _) (hyz₂ _)⟩
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm := fun _ _ ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ =>
    Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymm (hxy₂ _) (hyx₂ _)

theorem lt_def (x y : PartENat) : x < y ↔ ∃ hx : x.Dom, ∀ hy : y.Dom, x.get hx < y.get hy := by
  rw [lt_iff_le_not_ge, le_def, le_def, not_exists]
  constructor
  · rintro ⟨⟨hyx, H⟩, h⟩
    by_cases hx : x.Dom
    · use hx
      intro hy
      specialize H hy
      specialize h fun _ => hy
      rw [not_forall] at h
      omega
    · specialize h fun hx' => (hx hx').elim
      rw [not_forall] at h
      obtain ⟨hx', h⟩ := h
      exact (hx hx').elim
  · rintro ⟨hx, H⟩
    exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_ge (h _) (H _)⟩

noncomputable instance isOrderedAddMonoid : IsOrderedAddMonoid PartENat :=
  { add_le_add_left := fun a b ⟨h₁, h₂⟩ c =>
      PartENat.casesOn c (by simp [top_add]) fun c =>
        ⟨fun h => And.intro (dom_natCast _) (h₁ h.2), fun h => by
          simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩ }

instance semilatticeSup : SemilatticeSup PartENat :=
  { PartENat.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩
    sup_le := fun _ _ _ ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ =>
      ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }

instance orderBot : OrderBot PartENat where
  bot := ⊥
  bot_le _ := ⟨fun _ => trivial, fun _ => Nat.zero_le _⟩

instance orderTop : OrderTop PartENat where
  top := ⊤
  le_top _ := ⟨fun h => False.elim h, fun hy => False.elim hy⟩

instance : ZeroLEOneClass PartENat where
  zero_le_one := bot_le

/-- Alias of `Nat.cast_le` specialized to `PartENat` -/
theorem coe_le_coe {x y : ℕ} : (x : PartENat) ≤ y ↔ x ≤ y := Nat.cast_le

/-- Alias of `Nat.cast_lt` specialized to `PartENat` -/
theorem coe_lt_coe {x y : ℕ} : (x : PartENat) < y ↔ x < y := Nat.cast_lt

@[simp]
theorem get_le_get {x y : PartENat} {hx : x.Dom} {hy : y.Dom} : x.get hx ≤ y.get hy ↔ x ≤ y := by
  conv =>
    lhs
    rw [← coe_le_coe, natCast_get, natCast_get]

theorem le_coe_iff (x : PartENat) (n : ℕ) : x ≤ n ↔ ∃ h : x.Dom, x.get h ≤ n := by
  change (∃ h : True → x.Dom, _) ↔ ∃ h : x.Dom, x.get h ≤ n
  simp only [forall_prop_of_true, dom_natCast, get_natCast']

theorem lt_coe_iff (x : PartENat) (n : ℕ) : x < n ↔ ∃ h : x.Dom, x.get h < n := by
  simp only [lt_def, forall_prop_of_true, get_natCast', dom_natCast]

theorem coe_le_iff (n : ℕ) (x : PartENat) : (n : PartENat) ≤ x ↔ ∀ h : x.Dom, n ≤ x.get h := by
  rw [← some_eq_natCast]
  simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff]
  rfl

theorem coe_lt_iff (n : ℕ) (x : PartENat) : (n : PartENat) < x ↔ ∀ h : x.Dom, n < x.get h := by
  rw [← some_eq_natCast]
  simp only [lt_def, exists_prop_of_true, dom_some]
  rfl

nonrec theorem eq_zero_iff {x : PartENat} : x = 0 ↔ x ≤ 0 :=
  eq_bot_iff

theorem ne_zero_iff {x : PartENat} : x ≠ 0 ↔ ⊥ < x :=
  bot_lt_iff_ne_bot.symm

theorem dom_of_lt {x y : PartENat} : x < y → x.Dom :=
  PartENat.casesOn x not_top_lt fun _ _ => dom_natCast _

theorem top_eq_none : (⊤ : PartENat) = Part.none :=
  rfl

@[simp]
theorem natCast_lt_top (x : ℕ) : (x : PartENat) < ⊤ :=
  Ne.lt_top fun h => absurd (congr_arg Dom h) <| by simp only [dom_natCast]; exact true_ne_false

@[simp]
theorem zero_lt_top : (0 : PartENat) < ⊤ :=
  natCast_lt_top 0

@[simp]
theorem one_lt_top : (1 : PartENat) < ⊤ :=
  natCast_lt_top 1

@[simp]
theorem ofNat_lt_top (x : ℕ) [x.AtLeastTwo] : (ofNat(x) : PartENat) < ⊤ :=
  natCast_lt_top x

@[simp]
theorem natCast_ne_top (x : ℕ) : (x : PartENat) ≠ ⊤ :=
  ne_of_lt (natCast_lt_top x)

@[simp]
theorem zero_ne_top : (0 : PartENat) ≠ ⊤ :=
  natCast_ne_top 0

@[simp]
theorem one_ne_top : (1 : PartENat) ≠ ⊤ :=
  natCast_ne_top 1

@[simp]
theorem ofNat_ne_top (x : ℕ) [x.AtLeastTwo] : (ofNat(x) : PartENat) ≠ ⊤ :=
  natCast_ne_top x

theorem not_isMax_natCast (x : ℕ) : ¬IsMax (x : PartENat) :=
  not_isMax_of_lt (natCast_lt_top x)

theorem ne_top_iff {x : PartENat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n := by
  simpa only [← some_eq_natCast] using Part.ne_none_iff

theorem ne_top_iff_dom {x : PartENat} : x ≠ ⊤ ↔ x.Dom := by
  classical exact not_iff_comm.1 Part.eq_none_iff'.symm

theorem not_dom_iff_eq_top {x : PartENat} : ¬x.Dom ↔ x = ⊤ :=
  Iff.not_left ne_top_iff_dom.symm

theorem ne_top_of_lt {x y : PartENat} (h : x < y) : x ≠ ⊤ :=
  ne_of_lt <| lt_of_lt_of_le h le_top

theorem eq_top_iff_forall_lt (x : PartENat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartENat) < x := by
  constructor
  · rintro rfl n
    exact natCast_lt_top _
  · contrapose!
    rw [ne_top_iff]
    rintro ⟨n, rfl⟩
    exact ⟨n, irrefl _⟩

theorem eq_top_iff_forall_le (x : PartENat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartENat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_le (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩

theorem pos_iff_one_le {x : PartENat} : 0 < x ↔ 1 ≤ x :=
  PartENat.casesOn x
    (by simp only [le_top, natCast_lt_top, ← @Nat.cast_zero PartENat])
    fun n => by
      rw [← Nat.cast_zero, ← Nat.cast_one, PartENat.coe_lt_coe, PartENat.coe_le_coe]
      rfl

instance isTotal : IsTotal PartENat (· ≤ ·) where
  total x y :=
    PartENat.casesOn (P := fun z => z ≤ y ∨ y ≤ z) x (Or.inr le_top)
      (PartENat.casesOn y (fun _ => Or.inl le_top) fun x y =>
        (le_total x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2))

noncomputable instance linearOrder : LinearOrder PartENat :=
  { PartENat.partialOrder with
    le_total := IsTotal.total
    toDecidableLE := Classical.decRel _
    max := (· ⊔ ·)
    max_def a b := congr_fun₂ (@sup_eq_maxDefault PartENat _ (_) _) _ _ }

instance boundedOrder : BoundedOrder PartENat :=
  { PartENat.orderTop, PartENat.orderBot with }

noncomputable instance lattice : Lattice PartENat :=
  { PartENat.semilatticeSup with
    inf := min
    inf_le_left := min_le_left
    inf_le_right := min_le_right
    le_inf := fun _ _ _ => le_min }

instance : CanonicallyOrderedAdd PartENat :=
  { le_self_add := fun a b =>
      PartENat.casesOn b (le_top.trans_eq (add_top _).symm) fun _ =>
        PartENat.casesOn a (top_add _).ge fun _ =>
          (coe_le_coe.2 le_self_add).trans_eq (Nat.cast_add _ _)
    exists_add_of_le := fun {a b} =>
      PartENat.casesOn b (fun _ => ⟨⊤, (add_top _).symm⟩) fun b =>
        PartENat.casesOn a (fun h => ((natCast_lt_top _).not_ge h).elim) fun a h =>
          ⟨(b - a : ℕ), by
            rw [← Nat.cast_add, natCast_inj, add_comm, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩ }

theorem eq_natCast_sub_of_add_eq_natCast {x y : PartENat} {n : ℕ} (h : x + y = n) :
    x = ↑(n - y.get (dom_of_le_natCast ((le_add_left le_rfl).trans_eq h))) := by
  lift x to ℕ using dom_of_le_natCast ((le_add_right le_rfl).trans_eq h)
  lift y to ℕ using dom_of_le_natCast ((le_add_left le_rfl).trans_eq h)
  rw [← Nat.cast_add, natCast_inj] at h
  rw [get_natCast, natCast_inj, eq_tsub_of_add_eq h]

protected theorem add_lt_add_right {x y z : PartENat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z := by
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩
  induction y using PartENat.casesOn
  · rw [top_add]
    exact_mod_cast natCast_lt_top _
  norm_cast at h
  exact_mod_cast add_lt_add_right h _

protected theorem add_lt_add_iff_right {x y z : PartENat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => PartENat.add_lt_add_right h hz⟩

protected theorem add_lt_add_iff_left {x y z : PartENat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := by
  rw [add_comm z, add_comm z, PartENat.add_lt_add_iff_right hz]

protected theorem lt_add_iff_pos_right {x y : PartENat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y := by
  conv_rhs => rw [← PartENat.add_lt_add_iff_left hx]
  rw [add_zero]

theorem lt_add_one {x : PartENat} (hx : x ≠ ⊤) : x < x + 1 := by
  rw [PartENat.lt_add_iff_pos_right hx]
  norm_cast

theorem le_of_lt_add_one {x y : PartENat} (h : x < y + 1) : x ≤ y := by
  induction y using PartENat.casesOn
  · apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  exact_mod_cast Nat.le_of_lt_succ (by norm_cast at h)

theorem add_one_le_of_lt {x y : PartENat} (h : x < y) : x + 1 ≤ y := by
  induction y using PartENat.casesOn
  · apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  exact_mod_cast Nat.succ_le_of_lt (by norm_cast at h)

theorem add_one_le_iff_lt {x y : PartENat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y := by
  refine ⟨fun h => ?_, add_one_le_of_lt⟩
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction y using PartENat.casesOn
  · apply natCast_lt_top
  exact_mod_cast Nat.lt_of_succ_le (by norm_cast at h)

theorem coe_succ_le_iff {n : ℕ} {e : PartENat} : ↑n.succ ≤ e ↔ ↑n < e := by
  rw [Nat.succ_eq_add_one n, Nat.cast_add, Nat.cast_one, add_one_le_iff_lt (natCast_ne_top n)]

theorem lt_add_one_iff_lt {x y : PartENat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y := by
  refine ⟨le_of_lt_add_one, fun h => ?_⟩
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction y using PartENat.casesOn
  · rw [top_add]
    apply natCast_lt_top
  exact_mod_cast Nat.lt_succ_of_le (by norm_cast at h)

lemma lt_coe_succ_iff_le {x : PartENat} {n : ℕ} (hx : x ≠ ⊤) : x < n.succ ↔ x ≤ n := by
  rw [Nat.succ_eq_add_one n, Nat.cast_add, Nat.cast_one, lt_add_one_iff_lt hx]

theorem add_eq_top_iff {a b : PartENat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  refine PartENat.casesOn a ?_ ?_
  <;> refine PartENat.casesOn b ?_ ?_
  <;> simp [top_add, add_top]
  simp only [← Nat.cast_add, PartENat.natCast_ne_top, forall_const, not_false_eq_true]

protected theorem add_right_cancel_iff {a b c : PartENat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b := by
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩
  refine PartENat.casesOn a ?_ ?_
  <;> refine PartENat.casesOn b ?_ ?_
  <;> simp [add_eq_top_iff, natCast_ne_top, @eq_comm _ (⊤ : PartENat), top_add]
  simp only [← Nat.cast_add, add_left_cancel_iff, PartENat.natCast_inj, add_comm, forall_const]

protected theorem add_left_cancel_iff {a b c : PartENat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  rw [add_comm a, add_comm a, PartENat.add_right_cancel_iff ha]

section WithTop

/-- Computably converts a `PartENat` to a `ℕ∞`. -/
def toWithTop (x : PartENat) [Decidable x.Dom] : ℕ∞ :=
  x.toOption

theorem toWithTop_top :
    have : Decidable (⊤ : PartENat).Dom := Part.noneDecidable
    toWithTop ⊤ = ⊤ :=
  rfl

@[simp]
theorem toWithTop_top' {h : Decidable (⊤ : PartENat).Dom} : toWithTop ⊤ = ⊤ := by
  convert toWithTop_top

theorem toWithTop_zero :
    have : Decidable (0 : PartENat).Dom := someDecidable 0
    toWithTop 0 = 0 :=
  rfl

@[simp]
theorem toWithTop_zero' {h : Decidable (0 : PartENat).Dom} : toWithTop 0 = 0 := by
  convert toWithTop_zero

theorem toWithTop_one :
    have : Decidable (1 : PartENat).Dom := someDecidable 1
    toWithTop 1 = 1 :=
  rfl

@[simp]
theorem toWithTop_one' {h : Decidable (1 : PartENat).Dom} : toWithTop 1 = 1 := by
  convert toWithTop_one

theorem toWithTop_some (n : ℕ) : toWithTop (some n) = n :=
  rfl

theorem toWithTop_natCast (n : ℕ) {_ : Decidable (n : PartENat).Dom} : toWithTop n = n := by
  simp only [← toWithTop_some]
  congr

@[simp]
theorem toWithTop_natCast' (n : ℕ) {_ : Decidable (n : PartENat).Dom} :
    toWithTop (n : PartENat) = n := by
  rw [toWithTop_natCast n]

@[simp]
theorem toWithTop_ofNat (n : ℕ) [n.AtLeastTwo] {_ : Decidable (OfNat.ofNat n : PartENat).Dom} :
    toWithTop (ofNat(n) : PartENat) = OfNat.ofNat n := toWithTop_natCast' n

@[simp]
theorem toWithTop_le {x y : PartENat} [hx : Decidable x.Dom] [hy : Decidable y.Dom] :
    toWithTop x ≤ toWithTop y ↔ x ≤ y := by
  induction y using PartENat.casesOn generalizing hy
  · simp
  induction x using PartENat.casesOn generalizing hx
  · simp
  · simp

@[simp]
theorem toWithTop_lt {x y : PartENat} [Decidable x.Dom] [Decidable y.Dom] :
    toWithTop x < toWithTop y ↔ x < y :=
  lt_iff_lt_of_le_iff_le toWithTop_le

end WithTop

/-- Coercion from `ℕ∞` to `PartENat`. -/
@[coe]
def ofENat : ℕ∞ → PartENat :=
  fun x => match x with
  | Option.none => none
  | Option.some n => some n

instance : Coe ℕ∞ PartENat := ⟨ofENat⟩

example (n : ℕ) : ((n : ℕ∞) : PartENat) = ↑n := rfl

@[simp, norm_cast]
lemma ofENat_top : ofENat ⊤ = ⊤ := rfl

@[simp, norm_cast]
lemma ofENat_coe (n : ℕ) : ofENat n = n := rfl

@[simp, norm_cast]
theorem ofENat_zero : ofENat 0 = 0 := rfl

@[simp, norm_cast]
theorem ofENat_one : ofENat 1 = 1 := rfl

@[simp, norm_cast]
theorem ofENat_ofNat (n : Nat) [n.AtLeastTwo] : ofENat ofNat(n) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem toWithTop_ofENat (n : ℕ∞) {_ : Decidable (n : PartENat).Dom} : toWithTop (↑n) = n := by
  cases n with
  | top => simp
  | coe n => simp

@[simp, norm_cast]
theorem ofENat_toWithTop (x : PartENat) {_ : Decidable (x : PartENat).Dom} : toWithTop x = x := by
  induction x using PartENat.casesOn <;> simp

@[simp, norm_cast]
theorem ofENat_le {x y : ℕ∞} : ofENat x ≤ ofENat y ↔ x ≤ y := by
  classical
  rw [← toWithTop_le, toWithTop_ofENat, toWithTop_ofENat]

@[simp, norm_cast]
theorem ofENat_lt {x y : ℕ∞} : ofENat x < ofENat y ↔ x < y := by
  classical
  rw [← toWithTop_lt, toWithTop_ofENat, toWithTop_ofENat]

section WithTopEquiv

open scoped Classical in
@[simp]
theorem toWithTop_add {x y : PartENat} : toWithTop (x + y) = toWithTop x + toWithTop y := by
  refine PartENat.casesOn y ?_ ?_ <;> refine PartENat.casesOn x ?_ ?_ <;>
    simp [add_top, top_add, ← Nat.cast_add]

open scoped Classical in
/-- `Equiv` between `PartENat` and `ℕ∞` (for the order isomorphism see
`withTopOrderIso`). -/
@[simps]
noncomputable def withTopEquiv : PartENat ≃ ℕ∞ where
  toFun x := toWithTop x
  invFun x := ↑x
  left_inv x := by simp
  right_inv x := by simp

theorem withTopEquiv_top : withTopEquiv ⊤ = ⊤ := by
  simp

theorem withTopEquiv_natCast (n : Nat) : withTopEquiv n = n := by
  simp

theorem withTopEquiv_zero : withTopEquiv 0 = 0 := by
  simp

theorem withTopEquiv_one : withTopEquiv 1 = 1 := by
  simp

theorem withTopEquiv_ofNat (n : Nat) [n.AtLeastTwo] :
    withTopEquiv ofNat(n) = OfNat.ofNat n := by
  simp

theorem withTopEquiv_le {x y : PartENat} : withTopEquiv x ≤ withTopEquiv y ↔ x ≤ y := by
  simp

theorem withTopEquiv_lt {x y : PartENat} : withTopEquiv x < withTopEquiv y ↔ x < y := by
  simp

theorem withTopEquiv_symm_top : withTopEquiv.symm ⊤ = ⊤ := by
  simp

theorem withTopEquiv_symm_coe (n : Nat) : withTopEquiv.symm n = n := by
  simp

theorem withTopEquiv_symm_zero : withTopEquiv.symm 0 = 0 := by
  simp

theorem withTopEquiv_symm_one : withTopEquiv.symm 1 = 1 := by
  simp

theorem withTopEquiv_symm_ofNat (n : Nat) [n.AtLeastTwo] :
    withTopEquiv.symm ofNat(n) = OfNat.ofNat n := by
  simp

theorem withTopEquiv_symm_le {x y : ℕ∞} : withTopEquiv.symm x ≤ withTopEquiv.symm y ↔ x ≤ y := by
  simp

theorem withTopEquiv_symm_lt {x y : ℕ∞} : withTopEquiv.symm x < withTopEquiv.symm y ↔ x < y := by
  simp

/-- `toWithTop` induces an order isomorphism between `PartENat` and `ℕ∞`. -/
noncomputable def withTopOrderIso : PartENat ≃o ℕ∞ :=
  { withTopEquiv with map_rel_iff' := @fun _ _ => withTopEquiv_le }

/-- `toWithTop` induces an additive monoid isomorphism between `PartENat` and `ℕ∞`. -/
noncomputable def withTopAddEquiv : PartENat ≃+ ℕ∞ :=
  { withTopEquiv with
    map_add' := fun x y => by
      simp only [withTopEquiv]
      exact toWithTop_add }

end WithTopEquiv

theorem lt_wf : @WellFounded PartENat (· < ·) := by
  classical
    change WellFounded fun a b : PartENat => a < b
    simp_rw [← withTopEquiv_lt]
    exact InvImage.wf _ wellFounded_lt

instance : WellFoundedLT PartENat :=
  ⟨lt_wf⟩

instance wellFoundedRelation : WellFoundedRelation PartENat :=
  ⟨(· < ·), lt_wf⟩

section Find

variable (P : ℕ → Prop) [DecidablePred P]

/-- The smallest `PartENat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : PartENat :=
  ⟨∃ n, P n, Nat.find⟩

@[simp]
theorem find_get (h : (find P).Dom) : (find P).get h = Nat.find h :=
  rfl

theorem find_dom (h : ∃ n, P n) : (find P).Dom :=
  h

theorem lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : PartENat) < find P := by
  rw [coe_lt_iff]
  intro h₁
  rw [find_get]
  have h₂ := @Nat.find_spec P _ h₁
  revert h₂
  contrapose!
  exact h _

theorem lt_find_iff (n : ℕ) : (n : PartENat) < find P ↔ ∀ m ≤ n, ¬P m := by
  refine ⟨?_, lt_find P n⟩
  intro h m hm
  by_cases H : (find P).Dom
  · apply Nat.find_min H
    rw [coe_lt_iff] at h
    specialize h H
    exact lt_of_le_of_lt hm h
  · exact not_exists.mp H m

theorem find_le (n : ℕ) (h : P n) : find P ≤ n := by
  rw [le_coe_iff]
  exact ⟨⟨_, h⟩, @Nat.find_min' P _ _ _ h⟩

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => lt_find P n fun _ _ => h _⟩

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop PartENat :=
  { PartENat.linearOrder, PartENat.isOrderedAddMonoid, PartENat.orderTop with
    top_add' := top_add }

noncomputable instance : CompleteLinearOrder PartENat :=
  { lattice, withTopOrderIso.symm.toGaloisInsertion.liftCompleteLattice,
    linearOrder, linearOrder.toBiheytingAlgebra with }

end PartENat
