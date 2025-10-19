/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.NatOrdinal` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `Game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

## Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`NatOrdinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `Ordinal`.

## Todo

- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

universe u v

open Function Order Set

noncomputable section

/-! ### Basic casts between `Ordinal` and `NatOrdinal` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  Ordinal
deriving Zero, Inhabited, One, WellFoundedRelation, Uncountable,
  LinearOrder, SuccOrder, OrderBot, NoMaxOrder, ZeroLEOneClass

instance NatOrdinal.instNeZeroOne : NeZero (1 : NatOrdinal) := Ordinal.instNeZeroOne

/-- The identity function between `Ordinal` and `NatOrdinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _

/-- The identity function between `NatOrdinal` and `Ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _

namespace NatOrdinal

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal :=
  rfl

@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : a.toOrdinal.toNatOrdinal = a :=
  rfl

theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : ConditionallyCompleteLinearOrderBot NatOrdinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp] theorem bot_eq_zero : (⊥ : NatOrdinal) = 0 := rfl

@[simp] theorem toOrdinal_zero : toOrdinal 0 = 0 := rfl
@[simp] theorem toOrdinal_one : toOrdinal 1 = 1 := rfl

@[simp] theorem toOrdinal_eq_zero {a} : toOrdinal a = 0 ↔ a = 0 := Iff.rfl
@[simp] theorem toOrdinal_eq_one {a} : toOrdinal a = 1 ↔ a = 1 := Iff.rfl

@[simp]
theorem toOrdinal_max (a b : NatOrdinal) : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

@[simp]
theorem toOrdinal_min (a b : NatOrdinal) : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : NatOrdinal) : succ a = toNatOrdinal (toOrdinal a + 1) :=
  rfl

@[simp]
theorem zero_le (o : NatOrdinal) : 0 ≤ o :=
  Ordinal.zero_le o

theorem not_lt_zero (o : NatOrdinal) : ¬ o < 0 :=
  Ordinal.not_lt_zero o

@[simp]
theorem lt_one_iff_zero {o : NatOrdinal} : o < 1 ↔ o = 0 :=
  Ordinal.lt_one_iff_zero

/-- A recursor for `NatOrdinal`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : NatOrdinal → Sort*} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `NatOrdinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

instance small_Iio (a : NatOrdinal.{u}) : Small.{u} (Set.Iio a) := Ordinal.small_Iio a
instance small_Iic (a : NatOrdinal.{u}) : Small.{u} (Set.Iic a) := Ordinal.small_Iic a
instance small_Ico (a b : NatOrdinal.{u}) : Small.{u} (Set.Ico a b) := Ordinal.small_Ico a b
instance small_Icc (a b : NatOrdinal.{u}) : Small.{u} (Set.Icc a b) := Ordinal.small_Icc a b
instance small_Ioo (a b : NatOrdinal.{u}) : Small.{u} (Set.Ioo a b) := Ordinal.small_Ioo a b
instance small_Ioc (a b : NatOrdinal.{u}) : Small.{u} (Set.Ioc a b) := Ordinal.small_Ioc a b

end NatOrdinal

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp] theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal := rfl

@[simp] theorem toNatOrdinal_toOrdinal (a : Ordinal) : a.toNatOrdinal.toOrdinal = a := rfl

@[simp] theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 := rfl
@[simp] theorem toNatOrdinal_one : toNatOrdinal 1 = 1 := rfl

@[simp] theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 := Iff.rfl
@[simp] theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 := Iff.rfl

@[simp]
theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

@[simp]
theorem toNatOrdinal_min (a b : Ordinal) :
    toNatOrdinal (min a b) = min (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `NaturalOps` scope once. -/

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd (a b : Ordinal.{u}) : Ordinal.{u} :=
  max (⨆ x : Iio a, succ (nadd x.1 b)) (⨆ x : Iio b, succ (nadd a x.1))
termination_by (a, b)
decreasing_by all_goals cases x; decreasing_tactic

@[inherit_doc]
scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

open NaturalOps

/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul (a b : Ordinal.{u}) : Ordinal.{u} :=
  sInf {c | ∀ a' < a, ∀ b' < b, nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
termination_by (a, b)

@[inherit_doc]
scoped[NaturalOps] infixl:70 " ⨳ " => Ordinal.nmul

/-! ### Natural addition -/

theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by
  rw [nadd]
  simp [Ordinal.lt_iSup_iff]

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by
  rw [← not_lt, lt_nadd_iff]
  simp

theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)

theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)

theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c := by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_left h a).le
  · exact le_rfl

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a := by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl

variable (a b)

theorem nadd_comm (a b) : a ♯ b = b ♯ a := by
  rw [nadd, nadd, max_comm]
  congr <;> ext x <;> cases x <;> apply congr_arg _ (nadd_comm _ _)
termination_by (a, b)

@[deprecated "blsub will soon be deprecated" (since := "2024-11-18")]
theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    blsub.{u, v} _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) := by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  · intro i h
    rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ ha'))
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ hb'))
  all_goals
    apply blsub_le_of_brange_subset.{u, u, v}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self

private theorem iSup_nadd_of_monotone {a b} (f : Ordinal.{u} → Ordinal.{u}) (h : Monotone f) :
    ⨆ x : Iio (a ♯ b), f x = max (⨆ a' : Iio a, f (a'.1 ♯ b)) (⨆ b' : Iio b, f (a ♯ b'.1)) := by
  apply (max_le _ _).antisymm'
  · rw [Ordinal.iSup_le_iff]
    rintro ⟨i, hi⟩
    obtain ⟨x, hx, hi⟩ | ⟨x, hx, hi⟩ := lt_nadd_iff.1 hi
    · exact le_max_of_le_left ((h hi).trans <| Ordinal.le_iSup (fun x : Iio a ↦ _) ⟨x, hx⟩)
    · exact le_max_of_le_right ((h hi).trans <| Ordinal.le_iSup (fun x : Iio b ↦ _) ⟨x, hx⟩)
  all_goals
    apply csSup_le_csSup' (bddAbove_of_small _)
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    refine mem_range_self (⟨_, ?_⟩ : Iio _)
    apply_rules [nadd_lt_nadd_left, nadd_lt_nadd_right]

theorem nadd_assoc (a b c) : a ♯ b ♯ c = a ♯ (b ♯ c) := by
  unfold nadd
  rw [iSup_nadd_of_monotone fun a' ↦ succ (a' ♯ c), iSup_nadd_of_monotone fun b' ↦ succ (a ♯ b'),
    max_assoc]
  · congr <;> ext x <;> cases x <;> apply congr_arg _ (nadd_assoc _ _ _)
  · exact succ_mono.comp fun x y h ↦ nadd_le_nadd_left h _
  · exact succ_mono.comp fun x y h ↦ nadd_le_nadd_right h _
termination_by (a, b, c)

@[simp]
theorem nadd_zero (a : Ordinal) : a ♯ 0 = a := by
  rw [nadd, ciSup_of_empty fun _ : Iio 0 ↦ _, sup_bot_eq]
  convert _root_.iSup_succ a
  rename_i x
  cases x
  exact nadd_zero _
termination_by a

@[simp]
theorem zero_nadd : 0 ♯ a = a := by rw [nadd_comm, nadd_zero]

@[simp]
theorem nadd_one (a : Ordinal) : a ♯ 1 = succ a := by
  rw [nadd, ciSup_unique (s := fun _ : Iio 1 ↦ _), Iio_one_default_eq, nadd_zero,
    max_eq_right_iff, Ordinal.iSup_le_iff]
  rintro ⟨i, hi⟩
  rwa [nadd_one, succ_le_succ_iff, succ_le_iff]
termination_by a

@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]

theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by rw [← nadd_one (a ♯ b), nadd_assoc, nadd_one]

theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by rw [← one_nadd (a ♯ b), ← nadd_assoc, one_nadd]

@[simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n := by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn]

@[simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by rw [nadd_comm, nadd_nat]

theorem add_le_nadd : a + b ≤ a ♯ b := by
  induction b using limitRecOn with
  | zero => simp
  | succ c h =>
    rwa [add_succ, nadd_succ, succ_le_succ_iff]
  | limit c hc H =>
    rw [(isNormal_add_right a).apply_of_isSuccLimit hc, Ordinal.iSup_le_iff]
    rintro ⟨i, hi⟩
    exact (H i hi).trans (nadd_le_nadd_left hi.le a)

end Ordinal

namespace NatOrdinal

open Ordinal NaturalOps

instance : Add NatOrdinal := ⟨nadd⟩
instance : SuccAddOrder NatOrdinal := ⟨fun x => (nadd_one x).symm⟩

theorem lt_add_iff {a b c : NatOrdinal} :
    a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' :=
  Ordinal.lt_nadd_iff

theorem add_le_iff {a b c : NatOrdinal} :
     b + c ≤ a ↔ (∀ b' < b, b' + c < a) ∧ ∀ c' < c, b + c' < a :=
  Ordinal.nadd_le_iff

instance : AddLeftStrictMono NatOrdinal.{u} :=
  ⟨fun a _ _ h => nadd_lt_nadd_left h a⟩

instance : AddLeftMono NatOrdinal.{u} :=
  ⟨fun a _ _ h => nadd_le_nadd_left h a⟩

instance : AddLeftReflectLE NatOrdinal.{u} :=
  ⟨fun a b c h => by by_contra! h'; exact h.not_gt (by gcongr)⟩

instance : AddCommMonoid NatOrdinal :=
  { add := (· + ·)
    add_assoc := nadd_assoc
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm
    nsmul := nsmulRec }

instance : IsOrderedCancelAddMonoid NatOrdinal :=
  { add_le_add_left := fun _ _ => add_le_add_left
    le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left }

instance : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

@[simp]
theorem toOrdinal_natCast (n : ℕ) : toOrdinal n = n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change (toOrdinal n) ♯ 1 = n + 1
    rw [hn]; exact nadd_one n

instance : CharZero NatOrdinal where
  cast_injective m n h := by
    apply_fun toOrdinal at h
    simpa using h

end NatOrdinal

open NatOrdinal

open NaturalOps

namespace Ordinal

theorem nadd_eq_add (a b : Ordinal) : a ♯ b = toOrdinal (toNatOrdinal a + toNatOrdinal b) :=
  rfl

@[simp]
theorem toNatOrdinal_natCast (n : ℕ) : toNatOrdinal n = n := by
  rw [← toOrdinal_natCast n]
  rfl

theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
  @lt_of_add_lt_add_left NatOrdinal _ _ _

theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c :=
  @lt_of_add_lt_add_right NatOrdinal _ _ _

theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c :=
  @le_of_add_le_add_left NatOrdinal _ _ _

theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c :=
  @le_of_add_le_add_right NatOrdinal _ _ _

@[simp]
theorem nadd_lt_nadd_iff_left : ∀ (a) {b c}, a ♯ b < a ♯ c ↔ b < c :=
  @add_lt_add_iff_left NatOrdinal _ _ _ _

@[simp]
theorem nadd_lt_nadd_iff_right : ∀ (a) {b c}, b ♯ a < c ♯ a ↔ b < c :=
  @add_lt_add_iff_right NatOrdinal _ _ _ _

@[simp]
theorem nadd_le_nadd_iff_left : ∀ (a) {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c :=
  @add_le_add_iff_left NatOrdinal _ _ _ _

@[simp]
theorem nadd_le_nadd_iff_right : ∀ (a) {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
  @_root_.add_le_add_iff_right NatOrdinal _ _ _ _

theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d :=
  @add_le_add NatOrdinal _ _ _ _

theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add NatOrdinal _ _ _ _

theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d :=
  @add_lt_add_of_lt_of_le NatOrdinal _ _ _ _

theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add_of_le_of_lt NatOrdinal _ _ _ _

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
  @_root_.add_left_cancel NatOrdinal _ _

theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
  @_root_.add_right_cancel NatOrdinal _ _

@[simp]
theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _

@[simp]
theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
  @add_right_cancel_iff NatOrdinal _ _

theorem le_nadd_self {a b} : a ≤ b ♯ a := by simpa using nadd_le_nadd_right (Ordinal.zero_le b) a

theorem le_nadd_left {a b c} (h : a ≤ c) : a ≤ b ♯ c :=
  le_nadd_self.trans (nadd_le_nadd_left h b)

theorem le_self_nadd {a b} : a ≤ a ♯ b := by simpa using nadd_le_nadd_left (Ordinal.zero_le b) a

theorem le_nadd_right {a b c} (h : a ≤ b) : a ≤ b ♯ c :=
  le_self_nadd.trans (nadd_le_nadd_right h c)

theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) :=
  @add_left_comm NatOrdinal _

theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b :=
  @add_right_comm NatOrdinal _

/-! ### Natural multiplication -/

variable {a b c d : Ordinal.{u}}

@[deprecated "avoid using the definition of `nmul` directly" (since := "2024-11-19")]
theorem nmul_def (a b : Ordinal) :
    a ⨳ b = sInf {c | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} := by
  rw [nmul]

/-- The set in the definition of `nmul` is nonempty. -/
private theorem nmul_nonempty (a b : Ordinal.{u}) :
    {c : Ordinal.{u} | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.Nonempty := by
  obtain ⟨c, hc⟩ : BddAbove ((fun x ↦ x.1 ⨳ b ♯ a ⨳ x.2) '' Set.Iio a ×ˢ Set.Iio b) :=
    bddAbove_of_small _
  exact ⟨_, fun x hx y hy ↦
    (lt_succ_of_le <| hc <| Set.mem_image_of_mem _ <| Set.mk_mem_prod hx hy).trans_le le_self_nadd⟩

theorem nmul_nadd_lt {a' b' : Ordinal} (ha : a' < a) (hb : b' < b) :
    a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' := by
  conv_rhs => rw [nmul]
  exact csInf_mem (nmul_nonempty a b) a' ha b' hb

theorem nmul_nadd_le {a' b' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · rcases lt_or_eq_of_le hb with (hb | rfl)
    · exact (nmul_nadd_lt ha hb).le
    · rw [nadd_comm]
  · exact le_rfl

theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ a' < a, ∃ b' < b, c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [nmul] at h
    simpa using notMem_of_lt_csInf h ⟨0, fun _ _ => bot_le⟩
  · rintro ⟨a', ha, b', hb, h⟩
    have := h.trans_lt (nmul_nadd_lt ha hb)
    rwa [nadd_lt_nadd_iff_right] at this

theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' := by
  rw [← not_iff_not]; simp [lt_nmul_iff]

theorem nmul_comm (a b) : a ⨳ b = b ⨳ a := by
  rw [nmul, nmul]
  congr; ext x; constructor <;> intro H c hc d hd
  · rw [nadd_comm, ← nmul_comm, ← nmul_comm a, ← nmul_comm d]
    exact H _ hd _ hc
  · rw [nadd_comm, nmul_comm, nmul_comm c, nmul_comm c]
    exact H _ hd _ hc
termination_by (a, b)

@[simp]
theorem nmul_zero (a) : a ⨳ 0 = 0 := by
  rw [← Ordinal.le_zero, nmul_le_iff]
  exact fun _ _ a ha => (Ordinal.not_lt_zero a ha).elim

@[simp]
theorem zero_nmul (a) : 0 ⨳ a = 0 := by rw [nmul_comm, nmul_zero]

@[simp]
theorem nmul_one (a : Ordinal) : a ⨳ 1 = a := by
  rw [nmul]
  convert csInf_Ici
  ext b
  refine ⟨fun H ↦ le_of_forall_lt (a := a) fun c hc ↦ ?_, fun ha c hc ↦ ?_⟩
  · simpa [nmul_one c] using H c hc
  · simpa [nmul_one c] using hc.trans_le ha
termination_by a

@[simp]
theorem one_nmul (a) : 1 ⨳ a = a := by rw [nmul_comm, nmul_one]

theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b :=
  lt_nmul_iff.2 ⟨0, h₂, a, h₁, by simp⟩

theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
  lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩

theorem nmul_le_nmul_left (h : a ≤ b) (c) : c ⨳ a ≤ c ⨳ b := by
  rcases lt_or_eq_of_le h with (h₁ | rfl) <;> rcases (eq_zero_or_pos c).symm with (h₂ | rfl)
  · exact (nmul_lt_nmul_of_pos_left h₁ h₂).le
  all_goals simp

theorem nmul_le_nmul_right (h : a ≤ b) (c) : a ⨳ c ≤ b ⨳ c := by
  rw [nmul_comm, nmul_comm b]
  exact nmul_le_nmul_left h c

theorem nmul_nadd (a b c : Ordinal) : a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c := by
  refine le_antisymm (nmul_le_iff.2 fun a' ha d hd => ?_)
    (nadd_le_iff.2 ⟨fun d hd => ?_, fun d hd => ?_⟩)
  · rw [nmul_nadd]
    rcases lt_nadd_iff.1 hd with (⟨b', hb, hd⟩ | ⟨c', hc, hd⟩)
    · have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha hb) (nmul_nadd_le ha.le hd)
      rw [nmul_nadd, nmul_nadd] at this
      simp only [nadd_assoc] at this
      rwa [nadd_left_comm, nadd_left_comm _ (a ⨳ b'), nadd_left_comm (a ⨳ b),
        nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b),
        nadd_lt_nadd_iff_left, ← nadd_assoc, ← nadd_assoc] at this
    · have := nadd_lt_nadd_of_le_of_lt (nmul_nadd_le ha.le hd) (nmul_nadd_lt ha hc)
      rw [nmul_nadd, nmul_nadd] at this
      simp only [nadd_assoc] at this
      rwa [nadd_left_comm, nadd_comm (a ⨳ c), nadd_left_comm (a' ⨳ d), nadd_left_comm (a ⨳ c'),
        nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a' ⨳ c), nadd_left_comm (a ⨳ d),
        nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a ⨳ d),
        nadd_comm (a' ⨳ d), ← nadd_assoc, ← nadd_assoc] at this
  · rcases lt_nmul_iff.1 hd with ⟨a', ha, b', hb, hd⟩
    have := nadd_lt_nadd_of_le_of_lt hd (nmul_nadd_lt ha (nadd_lt_nadd_right hb c))
    rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this
    simp only [nadd_assoc] at this
    rwa [nadd_left_comm (a' ⨳ b'), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_left_comm _ (a' ⨳ b'), nadd_left_comm (a ⨳ b'), nadd_lt_nadd_iff_left,
      nadd_left_comm (a' ⨳ c), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
      nadd_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left] at this
  · rcases lt_nmul_iff.1 hd with ⟨a', ha, c', hc, hd⟩
    have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha (nadd_lt_nadd_left hc b)) hd
    rw [nmul_nadd, nmul_nadd, nmul_nadd a'] at this
    simp only [nadd_assoc] at this
    rwa [nadd_left_comm _ (a' ⨳ b), nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ c'),
      nadd_left_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left, nadd_left_comm, nadd_comm (a' ⨳ c'),
      nadd_left_comm _ (a ⨳ c'), nadd_lt_nadd_iff_left, nadd_comm _ (a' ⨳ c'),
      nadd_comm _ (a' ⨳ c'), nadd_left_comm, nadd_lt_nadd_iff_left] at this
termination_by (a, b, c)

theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c := by
  rw [nmul_comm, nmul_nadd, nmul_comm, nmul_comm c]

theorem nmul_nadd_lt₃ {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_lt (nmul_nadd_lt ha hb) hc

theorem nmul_nadd_le₃ {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_le (nmul_nadd_le ha hb) hc

private theorem nmul_nadd_lt₃' {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_lt₃ hb hc ha using 1 <;>
    (simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf)

@[deprecated nmul_nadd_le₃ (since := "2024-11-19")]
theorem nmul_nadd_le₃' {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_le₃ hb hc ha using 1 <;>
    (simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf)

theorem lt_nmul_iff₃ : d < a ⨳ b ⨳ c ↔ ∃ a' < a, ∃ b' < b, ∃ c' < c,
    d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
      a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' := by
  refine ⟨fun h ↦ ?_, fun ⟨a', ha, b', hb, c', hc, h⟩ ↦ ?_⟩
  · rcases lt_nmul_iff.1 h with ⟨e, he, c', hc, H₁⟩
    rcases lt_nmul_iff.1 he with ⟨a', ha, b', hb, H₂⟩
    refine ⟨a', ha, b', hb, c', hc, ?_⟩
    have := nadd_le_nadd H₁ (nmul_nadd_le H₂ hc.le)
    simp only [nadd_nmul, nadd_assoc] at this
    rw [nadd_left_comm, nadd_left_comm d, nadd_left_comm, nadd_le_nadd_iff_left,
      nadd_left_comm (a ⨳ b' ⨳ c), nadd_left_comm (a' ⨳ b ⨳ c), nadd_left_comm (a ⨳ b ⨳ c'),
      nadd_le_nadd_iff_left, nadd_left_comm (a ⨳ b ⨳ c'), nadd_left_comm (a ⨳ b ⨳ c')] at this
    simpa only [nadd_assoc]
  · have := h.trans_lt (nmul_nadd_lt₃ ha hb hc)
    repeat rw [nadd_lt_nadd_iff_right] at this
    assumption

theorem nmul_le_iff₃ : a ⨳ b ⨳ c ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa using lt_nmul_iff₃.not

private theorem nmul_le_iff₃' : a ⨳ (b ⨳ c) ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _), nmul_le_iff₃, nadd_eq_add, toOrdinal_toNatOrdinal]
  constructor <;> intro h a' ha b' hb c' hc
  · convert h b' hb c' hc a' ha using 1 <;> abel_nf
  · convert h c' hc a' ha b' hb using 1 <;> abel_nf

@[deprecated lt_nmul_iff₃ (since := "2024-11-19")]
theorem lt_nmul_iff₃' : d < a ⨳ (b ⨳ c) ↔ ∃ a' < a, ∃ b' < b, ∃ c' < c,
    d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
      a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') := by
  simpa using nmul_le_iff₃'.not

theorem nmul_assoc (a b c : Ordinal) : a ⨳ b ⨳ c = a ⨳ (b ⨳ c) := by
  apply le_antisymm
  · rw [nmul_le_iff₃]
    intro a' ha b' hb c' hc
    repeat rw [nmul_assoc]
    exact nmul_nadd_lt₃' ha hb hc
  · rw [nmul_le_iff₃']
    intro a' ha b' hb c' hc
    repeat rw [← nmul_assoc]
    exact nmul_nadd_lt₃ ha hb hc
termination_by (a, b, c)

end Ordinal

namespace NatOrdinal

open Ordinal

instance : Mul NatOrdinal :=
  ⟨nmul⟩

theorem lt_mul_iff {a b c : NatOrdinal} :
    c < a * b ↔ ∃ a' < a, ∃ b' < b, c + a' * b' ≤ a' * b + a * b' :=
  Ordinal.lt_nmul_iff

theorem mul_le_iff {a b c : NatOrdinal} :
    a * b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' * b + a * b' < c + a' * b' :=
  Ordinal.nmul_le_iff

theorem mul_add_lt {a b a' b' : NatOrdinal} (ha : a' < a) (hb : b' < b) :
    a' * b + a * b' < a * b + a' * b' :=
  Ordinal.nmul_nadd_lt ha hb

theorem nmul_nadd_le {a b a' b' : NatOrdinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' * b + a * b' ≤ a * b + a' * b' :=
  Ordinal.nmul_nadd_le ha hb

instance : CommSemiring NatOrdinal :=
  { NatOrdinal.instAddCommMonoid with
    mul := (· * ·)
    left_distrib := nmul_nadd
    right_distrib := nadd_nmul
    zero_mul := zero_nmul
    mul_zero := nmul_zero
    mul_assoc := nmul_assoc
    one := 1
    one_mul := one_nmul
    mul_one := nmul_one
    mul_comm := nmul_comm }

instance : IsOrderedRing NatOrdinal :=
  { mul_le_mul_of_nonneg_left := fun _ _ c h _ => nmul_le_nmul_left h c
    mul_le_mul_of_nonneg_right := fun _ _ c h _ => nmul_le_nmul_right h c }

end NatOrdinal

namespace Ordinal

theorem nmul_eq_mul (a b) : a ⨳ b = toOrdinal (toNatOrdinal a * toNatOrdinal b) :=
  rfl

theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a :=
  @mul_add_one NatOrdinal _ _ _

theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b :=
  @add_one_mul NatOrdinal _ _ _

theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by rw [← nadd_one, nmul_nadd_one]

theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by rw [← nadd_one, nadd_one_nmul]

theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a :=
  nmul_succ

theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b :=
  succ_nmul

theorem mul_le_nmul (a b : Ordinal.{u}) : a * b ≤ a ⨳ b := by
  refine b.limitRecOn ?_ ?_ ?_
  · simp
  · intro c h
    rw [mul_succ, nmul_succ]
    exact (add_le_nadd _ a).trans (nadd_le_nadd_right h a)
  · intro c hc H
    rcases eq_zero_or_pos a with (rfl | ha)
    · simp
    · rw [(isNormal_mul_right ha).apply_of_isSuccLimit hc, Ordinal.iSup_le_iff]
      rintro ⟨i, hi⟩
      exact (H i hi).trans (nmul_le_nmul_left hi.le a)

end Ordinal
