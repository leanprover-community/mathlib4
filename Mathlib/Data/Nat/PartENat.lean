/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Data.Part
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.NormNum

#align_import data.nat.part_enat from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`. This implementation uses `Part ℕ` as an
implementation. Use `ℕ∞` instead unless you care about computability.

## Main definitions

The following instances are defined:

* `OrderedAddCommMonoid PartENat`
* `CanonicallyOrderedAddMonoid PartENat`
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

Before the `open Classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `toWithTopZero` proved by `rfl`,
followed by `@[simp] lemma toWithTopZero'` whose proof uses `convert`.


## Tags

PartENat, ℕ∞
-/


open Part hiding some

/-- Type of natural numbers with infinity (`⊤`) -/
def PartENat : Type :=
  Part ℕ
#align part_enat PartENat

namespace PartENat

/-- The computable embedding `ℕ → PartENat`.

This coincides with the coercion `coe : ℕ → PartENat`, see `PartENat.some_eq_natCast`. -/
@[coe]
def some : ℕ → PartENat :=
  Part.some
#align part_enat.some PartENat.some

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
#align part_enat.dom_some PartENat.dom_some

instance addCommMonoid : AddCommMonoid PartENat where
  add := (· + ·)
  zero := 0
  add_comm x y := Part.ext' and_comm fun _ _ => add_comm _ _
  zero_add x := Part.ext' (true_and_iff _) fun _ _ => zero_add _
  add_zero x := Part.ext' (and_true_iff _) fun _ _ => add_zero _
  add_assoc x y z := Part.ext' and_assoc fun _ _ => add_assoc _ _ _

instance : AddCommMonoidWithOne PartENat :=
  { PartENat.addCommMonoid with
    one := 1
    natCast := some
    natCast_zero := rfl
    natCast_succ := fun _ => Part.ext' (true_and_iff _).symm fun _ _ => rfl }

theorem some_eq_natCast (n : ℕ) : some n = n :=
  rfl
#align part_enat.some_eq_coe PartENat.some_eq_natCast

@[simp, norm_cast]
theorem natCast_inj {x y : ℕ} : (x : PartENat) = y ↔ x = y :=
  Part.some_inj
#align part_enat.coe_inj PartENat.natCast_inj

@[simp]
theorem dom_natCast (x : ℕ) : (x : PartENat).Dom :=
  trivial
#align part_enat.dom_coe PartENat.dom_natCast

instance : CanLift PartENat ℕ (↑) Dom :=
  ⟨fun n hn => ⟨n.get hn, Part.some_get _⟩⟩

instance : LE PartENat :=
  ⟨fun x y => ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy⟩

instance : Top PartENat :=
  ⟨none⟩

instance : Bot PartENat :=
  ⟨0⟩

instance : Sup PartENat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => x.get h.1 ⊔ y.get h.2⟩⟩

theorem le_def (x y : PartENat) :
    x ≤ y ↔ ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl
#align part_enat.le_def PartENat.le_def

@[elab_as_elim]
protected theorem casesOn' {P : PartENat → Prop} :
    ∀ a : PartENat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on
#align part_enat.cases_on' PartENat.casesOn'

@[elab_as_elim]
protected theorem casesOn {P : PartENat → Prop} : ∀ a : PartENat, P ⊤ → (∀ n : ℕ, P n) → P a := by
  exact PartENat.casesOn'
  -- 🎉 no goals
#align part_enat.cases_on PartENat.casesOn

-- not a simp lemma as we will provide a `LinearOrderedAddCommMonoidWithTop` instance later
theorem top_add (x : PartENat) : ⊤ + x = ⊤ :=
  Part.ext' (false_and_iff _) fun h => h.left.elim
#align part_enat.top_add PartENat.top_add

-- not a simp lemma as we will provide a `LinearOrderedAddCommMonoidWithTop` instance later
theorem add_top (x : PartENat) : x + ⊤ = ⊤ := by rw [add_comm, top_add]
                                                 -- 🎉 no goals
#align part_enat.add_top PartENat.add_top

@[simp]
theorem natCast_get {x : PartENat} (h : x.Dom) : (x.get h : PartENat) = x := by
  exact Part.ext' (iff_of_true trivial h) fun _ _ => rfl
  -- 🎉 no goals
#align part_enat.coe_get PartENat.natCast_get

@[simp, norm_cast]
theorem get_natCast' (x : ℕ) (h : (x : PartENat).Dom) : get (x : PartENat) h = x := by
  rw [← natCast_inj, natCast_get]
  -- 🎉 no goals
#align part_enat.get_coe' PartENat.get_natCast'

theorem get_natCast {x : ℕ} : get (x : PartENat) (dom_natCast x) = x :=
  get_natCast' _ _
#align part_enat.get_coe PartENat.get_natCast

theorem coe_add_get {x : ℕ} {y : PartENat} (h : ((x : PartENat) + y).Dom) :
    get ((x : PartENat) + y) h = x + get y h.2 := by
  rfl
  -- 🎉 no goals
#align part_enat.coe_add_get PartENat.coe_add_get

@[simp]
theorem get_add {x y : PartENat} (h : (x + y).Dom) : get (x + y) h = x.get h.1 + y.get h.2 :=
  rfl
#align part_enat.get_add PartENat.get_add

@[simp]
theorem get_zero (h : (0 : PartENat).Dom) : (0 : PartENat).get h = 0 :=
  rfl
#align part_enat.get_zero PartENat.get_zero

@[simp]
theorem get_one (h : (1 : PartENat).Dom) : (1 : PartENat).get h = 1 :=
  rfl
#align part_enat.get_one PartENat.get_one

nonrec theorem get_eq_iff_eq_some {a : PartENat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some
#align part_enat.get_eq_iff_eq_some PartENat.get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : PartENat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = b := by
  rw [get_eq_iff_eq_some]
  -- ⊢ a = ↑b ↔ a = ↑b
  rfl
  -- 🎉 no goals
#align part_enat.get_eq_iff_eq_coe PartENat.get_eq_iff_eq_coe

theorem dom_of_le_of_dom {x y : PartENat} : x ≤ y → y.Dom → x.Dom := fun ⟨h, _⟩ => h
#align part_enat.dom_of_le_of_dom PartENat.dom_of_le_of_dom

theorem dom_of_le_some {x : PartENat} {y : ℕ} (h : x ≤ some y) : x.Dom :=
  dom_of_le_of_dom h trivial
#align part_enat.dom_of_le_some PartENat.dom_of_le_some

theorem dom_of_le_natCast {x : PartENat} {y : ℕ} (h : x ≤ y) : x.Dom := by
  exact dom_of_le_some h
  -- 🎉 no goals
#align part_enat.dom_of_le_coe PartENat.dom_of_le_natCast

instance decidableLe (x y : PartENat) [Decidable x.Dom] [Decidable y.Dom] : Decidable (x ≤ y) :=
  if hx : x.Dom then
    decidable_of_decidable_of_iff (by rw [le_def])
                                      -- 🎉 no goals
  else
    if hy : y.Dom then isFalse fun h => hx <| dom_of_le_of_dom h hy
    else isTrue ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩
#align part_enat.decidable_le PartENat.decidableLe

/-- The coercion `ℕ → PartENat` preserves `0` and addition. -/
def natCast_AddMonoidHom : ℕ →+ PartENat where
  toFun := some
  map_zero' := Nat.cast_zero
  map_add' := Nat.cast_add
#align part_enat.coe_hom PartENat.natCast_AddMonoidHom

@[simp]
theorem coe_coeHom : natCast_AddMonoidHom = some :=
  rfl
#align part_enat.coe_coe_hom PartENat.coe_coeHom

instance partialOrder : PartialOrder PartENat where
  le := (· ≤ ·)
  le_refl _ := ⟨id, fun _ => le_rfl⟩
  le_trans := fun _ _ _ ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ =>
    ⟨hxy₁ ∘ hyz₁, fun _ => le_trans (hxy₂ _) (hyz₂ _)⟩
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm := fun _ _ ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ =>
    Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymm (hxy₂ _) (hyx₂ _)

theorem lt_def (x y : PartENat) : x < y ↔ ∃ hx : x.Dom, ∀ hy : y.Dom, x.get hx < y.get hy := by
  rw [lt_iff_le_not_le, le_def, le_def, not_exists]
  -- ⊢ ((∃ h, ∀ (hy : y.Dom), Part.get x (_ : x.Dom) ≤ Part.get y hy) ∧ ∀ (x_1 : x. …
  constructor
  -- ⊢ ((∃ h, ∀ (hy : y.Dom), Part.get x (_ : x.Dom) ≤ Part.get y hy) ∧ ∀ (x_1 : x. …
  · rintro ⟨⟨hyx, H⟩, h⟩
    -- ⊢ ∃ hx, ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
    by_cases hx : x.Dom
    -- ⊢ ∃ hx, ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
    · use hx
      -- ⊢ ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
      intro hy
      -- ⊢ Part.get x hx < Part.get y hy
      specialize H hy
      -- ⊢ Part.get x hx < Part.get y hy
      specialize h fun _ => hy
      -- ⊢ Part.get x hx < Part.get y hy
      rw [not_forall] at h
      -- ⊢ Part.get x hx < Part.get y hy
      cases' h with hx' h
      -- ⊢ Part.get x hx < Part.get y hy
      rw [not_le] at h
      -- ⊢ Part.get x hx < Part.get y hy
      exact h
      -- 🎉 no goals
    · specialize h fun hx' => (hx hx').elim
      -- ⊢ ∃ hx, ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
      rw [not_forall] at h
      -- ⊢ ∃ hx, ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
      cases' h with hx' h
      -- ⊢ ∃ hx, ∀ (hy : y.Dom), Part.get x hx < Part.get y hy
      exact (hx hx').elim
      -- 🎉 no goals
  · rintro ⟨hx, H⟩
    -- ⊢ (∃ h, ∀ (hy : y.Dom), Part.get x (_ : x.Dom) ≤ Part.get y hy) ∧ ∀ (x_1 : x.D …
    exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_le (h _) (H _)⟩
    -- 🎉 no goals
#align part_enat.lt_def PartENat.lt_def

@[simp, norm_cast]
theorem coe_le_coe {x y : ℕ} : (x : PartENat) ≤ y ↔ x ≤ y := by
  exact ⟨fun ⟨_, h⟩ => h trivial, fun h => ⟨fun _ => trivial, fun _ => h⟩⟩
  -- 🎉 no goals
#align part_enat.coe_le_coe PartENat.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℕ} : (x : PartENat) < y ↔ x < y := by
  rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]
  -- 🎉 no goals
#align part_enat.coe_lt_coe PartENat.coe_lt_coe

@[simp]
theorem get_le_get {x y : PartENat} {hx : x.Dom} {hy : y.Dom} : x.get hx ≤ y.get hy ↔ x ≤ y := by
  conv =>
    lhs
    rw [← coe_le_coe, natCast_get, natCast_get]
#align part_enat.get_le_get PartENat.get_le_get

theorem le_coe_iff (x : PartENat) (n : ℕ) : x ≤ n ↔ ∃ h : x.Dom, x.get h ≤ n := by
  show (∃ h : True → x.Dom, _) ↔ ∃ h : x.Dom, x.get h ≤ n
  -- ⊢ (∃ h, ∀ (hy : (↑n).Dom), Part.get x (_ : x.Dom) ≤ Part.get (↑n) hy) ↔ ∃ h, P …
  simp only [forall_prop_of_true, dom_natCast, get_natCast']
  -- 🎉 no goals
#align part_enat.le_coe_iff PartENat.le_coe_iff

theorem lt_coe_iff (x : PartENat) (n : ℕ) : x < n ↔ ∃ h : x.Dom, x.get h < n := by
  simp only [lt_def, forall_prop_of_true, get_natCast', dom_natCast]
  -- 🎉 no goals
#align part_enat.lt_coe_iff PartENat.lt_coe_iff

theorem coe_le_iff (n : ℕ) (x : PartENat) : (n : PartENat) ≤ x ↔ ∀ h : x.Dom, n ≤ x.get h := by
  rw [← some_eq_natCast]
  -- ⊢ ↑n ≤ x ↔ ∀ (h : x.Dom), n ≤ Part.get x h
  simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff]
  -- ⊢ (∀ (hy : x.Dom), Part.get ↑n (_ : (↑n).Dom) ≤ Part.get x hy) ↔ ∀ (h : x.Dom) …
  rfl
  -- 🎉 no goals
#align part_enat.coe_le_iff PartENat.coe_le_iff

theorem coe_lt_iff (n : ℕ) (x : PartENat) : (n : PartENat) < x ↔ ∀ h : x.Dom, n < x.get h := by
  rw [← some_eq_natCast]
  -- ⊢ ↑n < x ↔ ∀ (h : x.Dom), n < Part.get x h
  simp only [lt_def, exists_prop_of_true, dom_some, forall_true_iff]
  -- ⊢ (∀ (hy : x.Dom), Part.get ↑n (_ : (↑n).Dom) < Part.get x hy) ↔ ∀ (h : x.Dom) …
  rfl
  -- 🎉 no goals
#align part_enat.coe_lt_iff PartENat.coe_lt_iff

instance NeZero.one : NeZero (1 : PartENat) :=
  ⟨natCast_inj.not.mpr (by decide)⟩
                           -- 🎉 no goals
#align part_enat.ne_zero.one PartENat.NeZero.one

instance semilatticeSup : SemilatticeSup PartENat :=
  { PartENat.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩
    sup_le := fun _ _ _ ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ =>
      ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }
#align part_enat.semilattice_sup PartENat.semilatticeSup

instance orderBot : OrderBot PartENat where
  bot := ⊥
  bot_le _ := ⟨fun _ => trivial, fun _ => Nat.zero_le _⟩
#align part_enat.order_bot PartENat.orderBot

instance orderTop : OrderTop PartENat where
  top := ⊤
  le_top _ := ⟨fun h => False.elim h, fun hy => False.elim hy⟩
#align part_enat.order_top PartENat.orderTop

nonrec theorem eq_zero_iff {x : PartENat} : x = 0 ↔ x ≤ 0 :=
  eq_bot_iff
#align part_enat.eq_zero_iff PartENat.eq_zero_iff

theorem ne_zero_iff {x : PartENat} : x ≠ 0 ↔ ⊥ < x :=
  bot_lt_iff_ne_bot.symm
#align part_enat.ne_zero_iff PartENat.ne_zero_iff

theorem dom_of_lt {x y : PartENat} : x < y → x.Dom :=
  PartENat.casesOn x not_top_lt fun _ _ => dom_natCast _
#align part_enat.dom_of_lt PartENat.dom_of_lt

theorem top_eq_none : (⊤ : PartENat) = Part.none :=
  rfl
#align part_enat.top_eq_none PartENat.top_eq_none

@[simp]
theorem natCast_lt_top (x : ℕ) : (x : PartENat) < ⊤ :=
  Ne.lt_top fun h => absurd (congr_arg Dom h) <| by simp only [dom_natCast]; exact true_ne_false
                                                    -- ⊢ ¬True = ⊤.Dom
                                                                             -- 🎉 no goals
#align part_enat.coe_lt_top PartENat.natCast_lt_top

@[simp]
theorem natCast_ne_top (x : ℕ) : (x : PartENat) ≠ ⊤ :=
  ne_of_lt (natCast_lt_top x)
#align part_enat.coe_ne_top PartENat.natCast_ne_top

theorem not_isMax_natCast (x : ℕ) : ¬IsMax (x : PartENat) :=
  not_isMax_of_lt (natCast_lt_top x)
#align part_enat.not_is_max_coe PartENat.not_isMax_natCast

theorem ne_top_iff {x : PartENat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n := by
  simpa only [← some_eq_natCast] using Part.ne_none_iff
  -- 🎉 no goals
#align part_enat.ne_top_iff PartENat.ne_top_iff

theorem ne_top_iff_dom {x : PartENat} : x ≠ ⊤ ↔ x.Dom := by
  classical exact not_iff_comm.1 Part.eq_none_iff'.symm
  -- 🎉 no goals
#align part_enat.ne_top_iff_dom PartENat.ne_top_iff_dom

theorem not_dom_iff_eq_top {x : PartENat} : ¬x.Dom ↔ x = ⊤ :=
  Iff.not_left ne_top_iff_dom.symm
#align part_enat.not_dom_iff_eq_top PartENat.not_dom_iff_eq_top

theorem ne_top_of_lt {x y : PartENat} (h : x < y) : x ≠ ⊤ :=
  ne_of_lt <| lt_of_lt_of_le h le_top
#align part_enat.ne_top_of_lt PartENat.ne_top_of_lt

theorem eq_top_iff_forall_lt (x : PartENat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartENat) < x := by
  constructor
  -- ⊢ x = ⊤ → ∀ (n : ℕ), ↑n < x
  · rintro rfl n
    -- ⊢ ↑n < ⊤
    exact natCast_lt_top _
    -- 🎉 no goals
  · contrapose!
    -- ⊢ x ≠ ⊤ → ∃ n, ¬↑n < x
    rw [ne_top_iff]
    -- ⊢ (∃ n, x = ↑n) → ∃ n, ¬↑n < x
    rintro ⟨n, rfl⟩
    -- ⊢ ∃ n_1, ¬↑n_1 < ↑n
    exact ⟨n, irrefl _⟩
    -- 🎉 no goals
#align part_enat.eq_top_iff_forall_lt PartENat.eq_top_iff_forall_lt

theorem eq_top_iff_forall_le (x : PartENat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartENat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_le (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩
#align part_enat.eq_top_iff_forall_le PartENat.eq_top_iff_forall_le

theorem pos_iff_one_le {x : PartENat} : 0 < x ↔ 1 ≤ x :=
  PartENat.casesOn x
    (by simp only [iff_true_iff, le_top, natCast_lt_top, ← @Nat.cast_zero PartENat])
        -- 🎉 no goals
    fun n => by
      rw [← Nat.cast_zero, ← Nat.cast_one, PartENat.coe_lt_coe, PartENat.coe_le_coe]
      -- ⊢ 0 < n ↔ 1 ≤ n
      rfl
      -- 🎉 no goals
#align part_enat.pos_iff_one_le PartENat.pos_iff_one_le

instance isTotal : IsTotal PartENat (· ≤ ·) where
  total x y :=
    PartENat.casesOn (P := fun z => z ≤ y ∨ y ≤ z) x (Or.inr le_top)
      (PartENat.casesOn y (fun _ => Or.inl le_top) fun x y =>
        (le_total x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2))

noncomputable instance linearOrder : LinearOrder PartENat :=
  { PartENat.partialOrder with
    le_total := IsTotal.total
    decidableLE := Classical.decRel _
    max := (· ⊔ ·)
    -- Porting note: was `max_def := @sup_eq_maxDefault _ _ (id _) _ }`
    max_def := fun a b => by
      change (fun a b => a ⊔ b) a b = _
      -- ⊢ (fun a b => a ⊔ b) a b = if a ≤ b then b else a
      rw [@sup_eq_maxDefault PartENat _ (id _) _]
      -- ⊢ maxDefault a b = if a ≤ b then b else a
      rfl }
      -- 🎉 no goals

instance boundedOrder : BoundedOrder PartENat :=
  { PartENat.orderTop, PartENat.orderBot with }

noncomputable instance lattice : Lattice PartENat :=
  { PartENat.semilatticeSup with
    inf := min
    inf_le_left := min_le_left
    inf_le_right := min_le_right
    le_inf := fun _ _ _ => le_min }

noncomputable instance orderedAddCommMonoid : OrderedAddCommMonoid PartENat :=
  { PartENat.linearOrder, PartENat.addCommMonoid with
    add_le_add_left := fun a b ⟨h₁, h₂⟩ c =>
      PartENat.casesOn c (by simp [top_add]) fun c =>
                             -- 🎉 no goals
        ⟨fun h => And.intro (dom_natCast _) (h₁ h.2), fun h => by
          simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩ }
          -- 🎉 no goals

noncomputable instance : CanonicallyOrderedAddMonoid PartENat :=
  { PartENat.semilatticeSup, PartENat.orderBot,
    PartENat.orderedAddCommMonoid with
    le_self_add := fun a b =>
      PartENat.casesOn b (le_top.trans_eq (add_top _).symm) fun b =>
        PartENat.casesOn a (top_add _).ge fun a =>
          (coe_le_coe.2 le_self_add).trans_eq (Nat.cast_add _ _)
    exists_add_of_le := fun {a b} =>
      PartENat.casesOn b (fun _ => ⟨⊤, (add_top _).symm⟩) fun b =>
        PartENat.casesOn a (fun h => ((natCast_lt_top _).not_le h).elim) fun a h =>
          ⟨(b - a : ℕ), by
            rw [← Nat.cast_add, natCast_inj, add_comm, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩ }
            -- 🎉 no goals

theorem eq_natCast_sub_of_add_eq_natCast {x y : PartENat} {n : ℕ} (h : x + y = n) :
    x = ↑(n - y.get (dom_of_le_natCast ((le_add_left le_rfl).trans_eq h))) := by
  lift x to ℕ using dom_of_le_natCast ((le_add_right le_rfl).trans_eq h)
  -- ⊢ ↑x = ↑(n - Part.get y (_ : y.Dom))
  lift y to ℕ using dom_of_le_natCast ((le_add_left le_rfl).trans_eq h)
  -- ⊢ ↑x = ↑(n - Part.get ↑y (_ : (↑y).Dom))
  rw [← Nat.cast_add, natCast_inj] at h
  -- ⊢ ↑x = ↑(n - Part.get ↑y (_ : (↑y).Dom))
  rw [get_natCast, natCast_inj, eq_tsub_of_add_eq h]
  -- 🎉 no goals
#align part_enat.eq_coe_sub_of_add_eq_coe PartENat.eq_natCast_sub_of_add_eq_natCast

protected theorem add_lt_add_right {x y z : PartENat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z := by
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  -- ⊢ ↑m + z < y + z
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩
  -- ⊢ ↑m + ↑k < y + ↑k
  induction' y using PartENat.casesOn with n
  -- ⊢ ↑m + ↑k < ⊤ + ↑k
  · rw [top_add]
    -- ⊢ ↑m + ↑k < ⊤
    -- Porting note: was apply_mod_cast natCast_lt_top
    norm_cast; apply natCast_lt_top
    -- ⊢ ↑(m + k) < ⊤
               -- 🎉 no goals
  norm_cast at h
  -- ⊢ ↑m + ↑k < ↑n + ↑k
  -- Porting note: was `apply_mod_cast add_lt_add_right h`
  norm_cast; apply add_lt_add_right h
  -- ⊢ m + k < n + k
             -- 🎉 no goals
#align part_enat.add_lt_add_right PartENat.add_lt_add_right

protected theorem add_lt_add_iff_right {x y z : PartENat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => PartENat.add_lt_add_right h hz⟩
#align part_enat.add_lt_add_iff_right PartENat.add_lt_add_iff_right

protected theorem add_lt_add_iff_left {x y z : PartENat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := by
  rw [add_comm z, add_comm z, PartENat.add_lt_add_iff_right hz]
  -- 🎉 no goals
#align part_enat.add_lt_add_iff_left PartENat.add_lt_add_iff_left

protected theorem lt_add_iff_pos_right {x y : PartENat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y := by
  conv_rhs => rw [← PartENat.add_lt_add_iff_left hx]
  -- ⊢ x < x + y ↔ x + 0 < x + y
  rw [add_zero]
  -- 🎉 no goals
#align part_enat.lt_add_iff_pos_right PartENat.lt_add_iff_pos_right

theorem lt_add_one {x : PartENat} (hx : x ≠ ⊤) : x < x + 1 := by
  rw [PartENat.lt_add_iff_pos_right hx]
  -- ⊢ 0 < 1
  norm_cast
  -- 🎉 no goals
#align part_enat.lt_add_one PartENat.lt_add_one

theorem le_of_lt_add_one {x y : PartENat} (h : x < y + 1) : x ≤ y := by
  induction' y using PartENat.casesOn with n
  -- ⊢ x ≤ ⊤
  · apply le_top
    -- 🎉 no goals
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  -- ⊢ ↑m ≤ ↑n
  -- Porting note: was `apply_mod_cast Nat.le_of_lt_succ; apply_mod_cast h`
  norm_cast; apply Nat.le_of_lt_succ; norm_cast at h
  -- ⊢ m ≤ n
             -- ⊢ m < Nat.succ n
                                      -- 🎉 no goals
#align part_enat.le_of_lt_add_one PartENat.le_of_lt_add_one

theorem add_one_le_of_lt {x y : PartENat} (h : x < y) : x + 1 ≤ y := by
  induction' y using PartENat.casesOn with n
  -- ⊢ x + 1 ≤ ⊤
  · apply le_top
    -- 🎉 no goals
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  -- ⊢ ↑m + 1 ≤ ↑n
  -- Porting note: was `apply_mod_cast Nat.succ_le_of_lt; apply_mod_cast h`
  norm_cast; apply Nat.succ_le_of_lt; norm_cast at h
  -- ⊢ m + 1 ≤ n
             -- ⊢ m < n
                                      -- 🎉 no goals
#align part_enat.add_one_le_of_lt PartENat.add_one_le_of_lt

theorem add_one_le_iff_lt {x y : PartENat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y := by
  refine ⟨fun h => ?_, add_one_le_of_lt⟩
  -- ⊢ x < y
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  -- ⊢ ↑m < y
  induction' y using PartENat.casesOn with n
  -- ⊢ ↑m < ⊤
  · apply natCast_lt_top
    -- 🎉 no goals
  -- Porting note: was `apply_mod_cast Nat.lt_of_succ_le; apply_mod_cast h`
  norm_cast; apply Nat.lt_of_succ_le; norm_cast at h
  -- ⊢ m < n
             -- ⊢ Nat.succ m ≤ n
                                      -- 🎉 no goals
#align part_enat.add_one_le_iff_lt PartENat.add_one_le_iff_lt

theorem coe_succ_le_iff {n : ℕ} {e : PartENat} : ↑n.succ ≤ e ↔ ↑n < e:= by
  rw [Nat.succ_eq_add_one n, Nat.cast_add, Nat.cast_one, add_one_le_iff_lt (natCast_ne_top n)]
  -- 🎉 no goals
#align part_enat.coe_succ_le_succ_iff PartENat.coe_succ_le_iff

theorem lt_add_one_iff_lt {x y : PartENat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y := by
  refine ⟨le_of_lt_add_one, fun h => ?_⟩
  -- ⊢ x < y + 1
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  -- ⊢ ↑m < y + 1
  induction' y using PartENat.casesOn with n
  -- ⊢ ↑m < ⊤ + 1
  · rw [top_add]
    -- ⊢ ↑m < ⊤
    apply natCast_lt_top
    -- 🎉 no goals
  -- Porting note: was `apply_mod_cast Nat.lt_succ_of_le; apply_mod_cast h`
  norm_cast; apply Nat.lt_succ_of_le; norm_cast at h
  -- ⊢ m < n + 1
             -- ⊢ m ≤ n
                                      -- 🎉 no goals
#align part_enat.lt_add_one_iff_lt PartENat.lt_add_one_iff_lt

lemma lt_coe_succ_iff_le {x : PartENat} {n : ℕ} (hx : x ≠ ⊤) : x < n.succ ↔ x ≤ n := by
  rw [Nat.succ_eq_add_one n, Nat.cast_add, Nat.cast_one, lt_add_one_iff_lt hx]
  -- 🎉 no goals
#align part_enat.lt_coe_succ_iff_le PartENat.lt_coe_succ_iff_le

theorem add_eq_top_iff {a b : PartENat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  refine PartENat.casesOn a ?_ ?_
  -- ⊢ ⊤ + b = ⊤ ↔ ⊤ = ⊤ ∨ b = ⊤
  <;> refine PartENat.casesOn b ?_ ?_
      -- ⊢ ⊤ + ⊤ = ⊤ ↔ ⊤ = ⊤ ∨ ⊤ = ⊤
      -- ⊢ ∀ (n : ℕ), ↑n + ⊤ = ⊤ ↔ ↑n = ⊤ ∨ ⊤ = ⊤
  <;> simp [top_add, add_top]
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
      -- ⊢ ∀ (n n_1 : ℕ), ¬↑n_1 + ↑n = ⊤
  simp only [←Nat.cast_add, PartENat.natCast_ne_top, forall_const]
  -- 🎉 no goals
#align part_enat.add_eq_top_iff PartENat.add_eq_top_iff

protected theorem add_right_cancel_iff {a b c : PartENat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b := by
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩
  -- ⊢ a + ↑c = b + ↑c ↔ a = b
  refine PartENat.casesOn a ?_ ?_
  -- ⊢ ⊤ + ↑c = b + ↑c ↔ ⊤ = b
  <;> refine PartENat.casesOn b ?_ ?_
      -- ⊢ ⊤ + ↑c = ⊤ + ↑c ↔ ⊤ = ⊤
      -- ⊢ ∀ (n : ℕ), ↑n + ↑c = ⊤ + ↑c ↔ ↑n = ⊤
  <;> simp [add_eq_top_iff, natCast_ne_top, @eq_comm _ (⊤ : PartENat), top_add]
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
      -- ⊢ ∀ (n n_1 : ℕ), ↑n_1 + ↑c = ↑n + ↑c ↔ n_1 = n
  simp only [←Nat.cast_add, add_left_cancel_iff, PartENat.natCast_inj, add_comm, forall_const]
  -- 🎉 no goals
#align part_enat.add_right_cancel_iff PartENat.add_right_cancel_iff

protected theorem add_left_cancel_iff {a b c : PartENat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  rw [add_comm a, add_comm a, PartENat.add_right_cancel_iff ha]
  -- 🎉 no goals
#align part_enat.add_left_cancel_iff PartENat.add_left_cancel_iff

section WithTop

/-- Computably converts a `PartENat` to a `ℕ∞`. -/
def toWithTop (x : PartENat) [Decidable x.Dom] : ℕ∞ :=
  x.toOption
#align part_enat.to_with_top PartENat.toWithTop

theorem toWithTop_top :
    have : Decidable (⊤ : PartENat).Dom := Part.noneDecidable
    toWithTop ⊤ = ⊤ :=
  rfl
#align part_enat.to_with_top_top PartENat.toWithTop_top

@[simp]
theorem toWithTop_top' {h : Decidable (⊤ : PartENat).Dom} : toWithTop ⊤ = ⊤ := by
  convert toWithTop_top
  -- 🎉 no goals
#align part_enat.to_with_top_top' PartENat.toWithTop_top'

theorem toWithTop_zero :
    have : Decidable (0 : PartENat).Dom := someDecidable 0
    toWithTop 0 = 0 :=
  rfl
#align part_enat.to_with_top_zero PartENat.toWithTop_zero

@[simp]
theorem toWithTop_zero' {h : Decidable (0 : PartENat).Dom} : toWithTop 0 = 0 := by
  convert toWithTop_zero
  -- 🎉 no goals
#align part_enat.to_with_top_zero' PartENat.toWithTop_zero'

theorem toWithTop_some (n : ℕ) : toWithTop (some n) = n :=
  rfl
#align part_enat.to_with_top_some PartENat.toWithTop_some

theorem toWithTop_natCast (n : ℕ) {_ : Decidable (n : PartENat).Dom} : toWithTop n = n := by
  simp only [← toWithTop_some]
  -- ⊢ toWithTop ↑n = toWithTop ↑n
  congr
  -- 🎉 no goals
#align part_enat.to_with_top_coe PartENat.toWithTop_natCast

@[simp]
theorem toWithTop_natCast' (n : ℕ) {h : Decidable (n : PartENat).Dom} :
    toWithTop (n : PartENat) = n := by
  rw [toWithTop_natCast n]
  -- 🎉 no goals
#align part_enat.to_with_top_coe' PartENat.toWithTop_natCast'

-- Porting note: statement changed. Mathlib 3 statement was
-- ```
-- @[simp] lemma to_with_top_le {x y : part_enat} :
--   Π [decidable x.dom] [decidable y.dom], by exactI to_with_top x ≤ to_with_top y ↔ x ≤ y :=
-- ```
-- This used to be really slow to typecheck when the definition of `ENat`
-- was still `deriving AddCommMonoidWithOne`. Now that I removed that it is fine.
-- (The problem was that the last `simp` got stuck at `CharZero ℕ∞ ≟ CharZero ℕ∞` where
-- one side used `instENatAddCommMonoidWithOne` and the other used
-- `NonAssocSemiring.toAddCommMonoidWithOne`. Now the former doesn't exist anymore.)
@[simp]
theorem toWithTop_le {x y : PartENat} [hx : Decidable x.Dom] [hy : Decidable y.Dom] :
    toWithTop x ≤ toWithTop y ↔ x ≤ y := by
  induction y using PartENat.casesOn generalizing hy
  -- ⊢ toWithTop x ≤ toWithTop ⊤ ↔ x ≤ ⊤
  · simp
    -- 🎉 no goals
  induction x using PartENat.casesOn generalizing hx
  -- ⊢ toWithTop ⊤ ≤ toWithTop ↑n✝ ↔ ⊤ ≤ ↑n✝
  · simp
    -- 🎉 no goals
  · simp -- Porting note: this takes too long.
    -- 🎉 no goals
#align part_enat.to_with_top_le PartENat.toWithTop_le

/-
Porting note: As part of the investigation above, I noticed that Lean4 does not
find the following two instances which it could find in Lean3 automatically:
```
#synth Decidable (⊤ : PartENat).Dom
variable {n : ℕ}
#synth Decidable (n : PartENat).Dom
```
-/

@[simp]
theorem toWithTop_lt {x y : PartENat} [Decidable x.Dom] [Decidable y.Dom] :
    toWithTop x < toWithTop y ↔ x < y :=
  lt_iff_lt_of_le_iff_le toWithTop_le
#align part_enat.to_with_top_lt PartENat.toWithTop_lt

end WithTop

-- Porting note : new, extracted from `withTopEquiv`.
/-- Coercion from `ℕ∞` to `PartENat`. -/
@[coe]
def ofENat : ℕ∞ → PartENat :=
  fun x => match x with
  | Option.none => none
  | Option.some n => some n

-- Porting note : new
instance : Coe ℕ∞ PartENat := ⟨ofENat⟩

-- Porting note: new. This could probably be moved to tests or removed.
example (n : ℕ) : ((n : ℕ∞) : PartENat) = ↑n := rfl

-- Porting note : new
@[simp]
lemma ofENat_none : ofENat Option.none = ⊤ := by rfl
                                                 -- 🎉 no goals

-- Porting note : new
@[simp]
lemma ofENat_some (n : ℕ) : ofENat (Option.some n) = ↑n := by rfl
                                                              -- 🎉 no goals

-- Porting note : new
@[simp, norm_cast]
theorem toWithTop_ofENat (n : ℕ∞) {_ : Decidable (n : PartENat).Dom} : toWithTop (↑n) = n := by
  induction n with
  | none => simp
  | some n =>
    simp only [toWithTop_natCast', ofENat_some]
    rfl

section WithTopEquiv

open Classical

@[simp]
theorem toWithTop_add {x y : PartENat} : toWithTop (x + y) = toWithTop x + toWithTop y := by
  refine PartENat.casesOn y ?_ ?_ <;> refine PartENat.casesOn x ?_ ?_
  -- ⊢ toWithTop (x + ⊤) = toWithTop x + toWithTop ⊤
                                      -- ⊢ toWithTop (⊤ + ⊤) = toWithTop ⊤ + toWithTop ⊤
                                      -- ⊢ ∀ (n : ℕ), toWithTop (⊤ + ↑n) = toWithTop ⊤ + toWithTop ↑n
  --Porting note: was `simp [← Nat.cast_add, ← ENat.coe_add]`
  · simp only [add_top, toWithTop_top', _root_.add_top]
    -- 🎉 no goals
  · simp only [add_top, toWithTop_top', toWithTop_natCast', _root_.add_top, forall_const]
    -- 🎉 no goals
  · simp only [top_add, toWithTop_top', toWithTop_natCast', _root_.top_add, forall_const]
    -- 🎉 no goals
  · simp_rw [toWithTop_natCast', ← Nat.cast_add, toWithTop_natCast', forall_const]
    -- 🎉 no goals
#align part_enat.to_with_top_add PartENat.toWithTop_add

-- Porting note: The old proof of `right_inv` didn't work.
-- (`by cases x; simp [with_top_equiv._match_1]; refl`)
-- In order to get it to work, I introduced some new statements (see above),
-- in particular `toWithTop_ofENat`.
/-- `Equiv` between `PartENat` and `ℕ∞` (for the order isomorphism see
`withTopOrderIso`). -/
noncomputable def withTopEquiv : PartENat ≃ ℕ∞ where
  toFun x := toWithTop x
  invFun x := ↑x
  left_inv x := by
    induction x using PartENat.casesOn <;>
    -- ⊢ (fun x => ↑x) ((fun x => toWithTop x) ⊤) = ⊤
    intros <;>
    -- ⊢ (fun x => ↑x) ((fun x => toWithTop x) ⊤) = ⊤
    -- ⊢ (fun x => ↑x) ((fun x => toWithTop x) ↑n✝) = ↑n✝
    simp <;>
    -- ⊢ ↑⊤ = ⊤
    -- ⊢ ↑↑n✝ = ↑n✝
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
  right_inv x := by
    simp [toWithTop_ofENat]
    -- 🎉 no goals
#align part_enat.with_top_equiv PartENat.withTopEquiv

@[simp]
theorem withTopEquiv_top : withTopEquiv ⊤ = ⊤ :=
  toWithTop_top'
#align part_enat.with_top_equiv_top PartENat.withTopEquiv_top

@[simp]
theorem withTopEquiv_natCast (n : Nat) : withTopEquiv n = n :=
  toWithTop_natCast' _
#align part_enat.with_top_equiv_coe PartENat.withTopEquiv_natCast

@[simp]
theorem withTopEquiv_zero : withTopEquiv 0 = 0 := by
  simpa only [Nat.cast_zero] using withTopEquiv_natCast 0
  -- 🎉 no goals
#align part_enat.with_top_equiv_zero PartENat.withTopEquiv_zero

@[simp]
theorem withTopEquiv_le {x y : PartENat} : withTopEquiv x ≤ withTopEquiv y ↔ x ≤ y :=
  toWithTop_le
#align part_enat.with_top_equiv_le PartENat.withTopEquiv_le

@[simp]
theorem withTopEquiv_lt {x y : PartENat} : withTopEquiv x < withTopEquiv y ↔ x < y :=
  toWithTop_lt
#align part_enat.with_top_equiv_lt PartENat.withTopEquiv_lt

/-- `to_WithTop` induces an order isomorphism between `PartENat` and `ℕ∞`. -/
noncomputable def withTopOrderIso : PartENat ≃o ℕ∞ :=
  { withTopEquiv with map_rel_iff' := @fun _ _ => withTopEquiv_le }
#align part_enat.with_top_order_iso PartENat.withTopOrderIso

@[simp]
theorem withTopEquiv_symm_top : withTopEquiv.symm ⊤ = ⊤ :=
  rfl
#align part_enat.with_top_equiv_symm_top PartENat.withTopEquiv_symm_top

@[simp]
theorem withTopEquiv_symm_coe (n : Nat) : withTopEquiv.symm n = n :=
  rfl
#align part_enat.with_top_equiv_symm_coe PartENat.withTopEquiv_symm_coe

@[simp]
theorem withTopEquiv_symm_zero : withTopEquiv.symm 0 = 0 :=
  rfl
#align part_enat.with_top_equiv_symm_zero PartENat.withTopEquiv_symm_zero

@[simp]
theorem withTopEquiv_symm_le {x y : ℕ∞} : withTopEquiv.symm x ≤ withTopEquiv.symm y ↔ x ≤ y := by
  rw [← withTopEquiv_le]
  -- ⊢ ↑withTopEquiv (↑withTopEquiv.symm x) ≤ ↑withTopEquiv (↑withTopEquiv.symm y)  …
  simp
  -- 🎉 no goals
#align part_enat.with_top_equiv_symm_le PartENat.withTopEquiv_symm_le

@[simp]
theorem withTopEquiv_symm_lt {x y : ℕ∞} : withTopEquiv.symm x < withTopEquiv.symm y ↔ x < y := by
  rw [← withTopEquiv_lt]
  -- ⊢ ↑withTopEquiv (↑withTopEquiv.symm x) < ↑withTopEquiv (↑withTopEquiv.symm y)  …
  simp
  -- 🎉 no goals
#align part_enat.with_top_equiv_symm_lt PartENat.withTopEquiv_symm_lt

/-- `toWithTop` induces an additive monoid isomorphism between `PartENat` and `ℕ∞`. -/
noncomputable def withTopAddEquiv : PartENat ≃+ ℕ∞ :=
  { withTopEquiv with
    map_add' := fun x y => by
      simp only [withTopEquiv]
      -- ⊢ toWithTop (x + y) = toWithTop x + toWithTop y
      exact toWithTop_add }
      -- 🎉 no goals
#align part_enat.with_top_add_equiv PartENat.withTopAddEquiv

end WithTopEquiv

theorem lt_wf : @WellFounded PartENat (· < ·) := by
  classical
    change WellFounded fun a b : PartENat => a < b
    simp_rw [← withTopEquiv_lt]
    exact InvImage.wf _ (WithTop.wellFounded_lt Nat.lt_wfRel.wf)
#align part_enat.lt_wf PartENat.lt_wf

instance : WellFoundedLT PartENat :=
  ⟨lt_wf⟩

instance isWellOrder : IsWellOrder PartENat (· < ·) := {}

instance wellFoundedRelation : WellFoundedRelation PartENat :=
  ⟨(· < ·), lt_wf⟩

section Find

variable (P : ℕ → Prop) [DecidablePred P]

/-- The smallest `PartENat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : PartENat :=
  ⟨∃ n, P n, Nat.find⟩
#align part_enat.find PartENat.find

@[simp]
theorem find_get (h : (find P).Dom) : (find P).get h = Nat.find h :=
  rfl
#align part_enat.find_get PartENat.find_get

theorem find_dom (h : ∃ n, P n) : (find P).Dom :=
  h
#align part_enat.find_dom PartENat.find_dom

theorem lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : PartENat) < find P := by
  rw [coe_lt_iff]
  -- ⊢ ∀ (h : (find P).Dom), n < Part.get (find P) h
  intro h₁
  -- ⊢ n < Part.get (find P) h₁
  rw [find_get]
  -- ⊢ n < Nat.find h₁
  have h₂ := @Nat.find_spec P _ h₁
  -- ⊢ n < Nat.find h₁
  revert h₂
  -- ⊢ P (Nat.find h₁) → n < Nat.find h₁
  contrapose!
  -- ⊢ Nat.find h₁ ≤ n → ¬P (Nat.find h₁)
  exact h _
  -- 🎉 no goals
#align part_enat.lt_find PartENat.lt_find

theorem lt_find_iff (n : ℕ) : (n : PartENat) < find P ↔ ∀ m ≤ n, ¬P m := by
  refine' ⟨_, lt_find P n⟩
  -- ⊢ ↑n < find P → ∀ (m : ℕ), m ≤ n → ¬P m
  intro h m hm
  -- ⊢ ¬P m
  by_cases H : (find P).Dom
  -- ⊢ ¬P m
  · apply Nat.find_min H
    -- ⊢ m < Nat.find H
    rw [coe_lt_iff] at h
    -- ⊢ m < Nat.find H
    specialize h H
    -- ⊢ m < Nat.find H
    exact lt_of_le_of_lt hm h
    -- 🎉 no goals
  · exact not_exists.mp H m
    -- 🎉 no goals
#align part_enat.lt_find_iff PartENat.lt_find_iff

theorem find_le (n : ℕ) (h : P n) : find P ≤ n := by
  rw [le_coe_iff]
  -- ⊢ ∃ h, Part.get (find P) h ≤ n
  refine' ⟨⟨_, h⟩, @Nat.find_min' P _ _ _ h⟩
  -- 🎉 no goals
#align part_enat.find_le PartENat.find_le

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => lt_find P n fun _ _ => h _⟩
#align part_enat.find_eq_top_iff PartENat.find_eq_top_iff

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop PartENat :=
  { PartENat.linearOrder, PartENat.orderedAddCommMonoid, PartENat.orderTop with
    top_add' := top_add }

noncomputable instance : CompleteLinearOrder PartENat :=
  { PartENat.lattice, withTopOrderIso.symm.toGaloisInsertion.liftCompleteLattice,
    PartENat.linearOrder with
    inf := (· ⊓ ·)
    sup := (· ⊔ ·)
    top := ⊤
    bot := ⊥
    le := (· ≤ ·)
    lt := (· < ·) }

end PartENat
