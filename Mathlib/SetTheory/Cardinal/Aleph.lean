/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Cardinal.PartENat
import Mathlib.SetTheory.Ordinal.Enum

/-!
# Omega, aleph, and beth functions

* The function `Ordinal.omega'` enumerates the initial ordinals, i.e. the smallest ordinals with any
  given cardinality. Thus `omega' n = n`, `omega' ω = ω`, `omega' (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.aleph'` is an order isomorphism between ordinals and cardinals. Thus
  `aleph n = n`, `aleph' ω = ℵ₀`, `aleph' (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more standard
  function which skips over finite ordinals.
* The function `Cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Notation

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`. These are scoped notations
  in `Ordinal`.
-/

assert_not_exists Module
assert_not_exists Finsupp
assert_not_exists Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

/-- An ordinal is initial when it is the first ordinal with a given cardinality. -/
def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o

theorem IsInitial.ord_card {o : Ordinal} (h : IsInitial o) : o.card.ord = o := h

theorem IsInitial.le_of_card_le {a b : Ordinal} (ha : IsInitial a)
    (hb : a.card ≤ b.card) : a ≤ b := by
  rw [← ha.ord_card]
  exact (ord_mono hb).trans (ord_card_le b)

theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by
  rw [IsInitial, card_ord]

theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) (hb : IsInitial b) :
    a.card ≤ b.card ↔ a ≤ b := by
  rw [← ord_le_ord, ha.ord_card, hb.ord_card]

theorem IsInitial.card_lt_card {a b : Ordinal} (ha : IsInitial a) (hb : IsInitial b) :
    a.card < b.card ↔ a < b :=
  lt_iff_lt_of_le_iff_le (hb.card_le_card ha)

theorem isInitial_natCast (n : ℕ) : IsInitial n := by
  rw [IsInitial, card_nat, ord_nat]

theorem isInitial_zero : IsInitial 0 := by
  exact_mod_cast isInitial_natCast 0

theorem isInitial_one : IsInitial 1 := by
  exact_mod_cast isInitial_natCast 1

theorem isInitial_omega0 : IsInitial ω := by
  rw [IsInitial, card_omega0, ord_aleph0]

theorem not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x} := by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_le this

/-- Initial ordinals are order-isomorphic to the cardinals. -/
@[simps!]
def isInitialIso : {x // IsInitial x} ≃o Cardinal where
  toFun x := x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a b} := a.2.card_le_card b.2

/-- The `omega'` function gives the initial ordinals listed by their ordinal index. `omega' n = n`,
`omega' ω = ω`, `aleph' (ω + 1) = ω₁`, etc.

For the more common omega function skipping over finite ordinals, see `Ordinal.omega`. -/
def omega' : Ordinal.{u} ↪o Ordinal.{u} where
  toFun := enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_iff not_bddAbove_isInitial

-- This shouldn't fire for theorems ending in `omega'`.
set_option linter.docPrime false

theorem coe_omega' : omega' = enumOrd {x | IsInitial x} :=
  rfl

theorem omega'_strictMono : StrictMono omega' :=
  omega'.strictMono

theorem omega'_lt {o₁ o₂ : Ordinal} : omega' o₁ < omega' o₂ ↔ o₁ < o₂ :=
  omega'.lt_iff_lt

theorem omega'_le {o₁ o₂ : Ordinal} : omega' o₁ ≤ omega' o₂ ↔ o₁ ≤ o₂ :=
  omega'.le_iff_le

theorem omega'_max (o₁ o₂ : Ordinal) : omega' (max o₁ o₂) = max (omega' o₁) (omega' o₂) :=
  omega'.monotone.map_max

theorem isInitial_omega' (o : Ordinal) : IsInitial (omega' o) :=
  enumOrd_mem not_bddAbove_isInitial o

theorem le_omega'_apply (o : Ordinal) : o ≤ omega' o :=
  le_enumOrd_apply not_bddAbove_isInitial

@[simp]
theorem omega'_zero : omega' 0 = 0 := by
  rw [coe_omega', enumOrd_eq_zero]
  exact isInitial_zero

@[simp]
theorem omega'_natCast (n : ℕ) : omega' n = n := by
  induction n with
  | zero => exact omega'_zero
  | succ n IH =>
    apply (le_omega'_apply _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

theorem omega'_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : ∀ b < o, omega' b < a) :
    omega' o ≤ a :=
  enumOrd_le_of_forall_lt ha H

theorem isNormal_omega' : IsNormal omega' := by
  rw [isNormal_iff_strictMono_limit]
  refine ⟨omega'_strictMono, fun o ho a ha ↦
    (omega'_le_of_forall_lt (isInitial_ord _) fun b hb ↦ ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_omega' _).card_lt_card (isInitial_ord _), card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_omega' _).card_lt_card (isInitial_omega' _), omega'_lt]
  exact lt_succ b

@[simp]
theorem omega'_omega0 : omega' ω = ω := by
  simp_rw [← isNormal_omega'.apply_omega0, omega'_natCast, iSup_natCast]

/-- The `omega` function gives the infinite initial ordinals listed by their ordinal index.
`omega 0 = ω`, `omega 1 = ω₁` is the first uncountable ordinal, and so on.

For a version including finite ordinals, see `Ordinal.omega'`. -/
def omega : Ordinal ↪o Ordinal :=
  (OrderEmbedding.addLeft ω).trans omega'

@[inherit_doc]
scoped prefix:75 "ω_ " => omega

/-- `ω₁` is the first uncountable ordinal. -/
scoped notation "ω₁" => ω_ 1

theorem omega_eq_omega' (o : Ordinal) : ω_ o = omega' (ω + o) :=
  rfl

theorem isInitial_omega (o : Ordinal) : IsInitial (ω_ o) :=
  isInitial_omega' _

theorem omega_lt {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂ :=
  omega.lt_iff_lt

theorem omega_le {o₁ o₂ : Ordinal} : ω_ o₁ ≤ ω_ o₂ ↔ o₁ ≤ o₂ :=
  omega.le_iff_le

theorem omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂) :=
  omega.monotone.map_max

@[simp]
theorem omega_zero : ω_ 0 = ω := by
  rw [omega_eq_omega', add_zero, omega'_omega0]

theorem omega0_le_omega (o : Ordinal) : ω ≤ ω_ o := by
  rw [← omega_zero, omega_le]
  exact Ordinal.zero_le o

theorem omega0_lt_omega1 : ω < ω₁ := by
  rw [← omega_zero, omega_lt]
  exact zero_lt_one

@[deprecated omega0_lt_omega1 (since := "2024-10-11")]
alias omega_lt_omega1 := omega0_lt_omega1

theorem isNormal_omega : IsNormal omega :=
  isNormal_omega'.trans (add_isNormal _)

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal index. `aleph' n = n`,
`aleph' ω = ℵ₀`, `aleph' (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
def aleph' : Ordinal.{u} ≃o Cardinal.{u} :=
  (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

-- This shouldn't fire for theorems ending in `aleph'`.
set_option linter.docPrime false

@[simp]
theorem _root_.Ordinal.card_omega' (o : Ordinal) : (omega' o).card = aleph' o :=
  rfl

@[simp]
theorem ord_aleph' (o : Ordinal) : (aleph' o).ord = omega' o := by
  rw [← o.card_omega', (isInitial_omega' o).ord_card]

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `alephIdx`.
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ℵ₀ = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `alephIdx`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  aleph'.symm.toRelIsoLT

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx : Cardinal → Ordinal :=
  aleph'.symm

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx :=
  rfl

@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id]
  exact Quotient.sound ⟨aleph'.symm.toRelIsoLT⟩

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
@[deprecated aleph' (since := "2024-08-28")]
def Aleph'.relIso :=
  aleph'

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl

theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  aleph'.lt_iff_lt

theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  aleph'.le_iff_le

theorem aleph'_max (o₁ o₂ : Ordinal) : aleph' (max o₁ o₂) = max (aleph' o₁) (aleph' o₂) :=
  aleph'.monotone.map_max

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

@[simp]
theorem aleph'_zero : aleph' 0 = 0 :=
  aleph'.map_bot

@[simp]
theorem aleph'_succ (o : Ordinal) : aleph' (succ o) = succ (aleph' o) :=
  aleph'.map_succ o

@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
  | 0 => aleph'_zero
  | n + 1 => show aleph' (succ n) = n.succ by rw [aleph'_succ, aleph'_nat n, nat_succ]

theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
  ⟨fun h o' h' => (aleph'_le.2 <| h'.le).trans h, fun h => by
    rw [← aleph'.apply_symm_apply c, aleph'_le, limit_le l]
    intro x h'
    rw [← aleph'_le, aleph'.apply_symm_apply]
    exact h _ h'⟩

theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a := by
  refine le_antisymm ?_ (ciSup_le' fun i => aleph'_le.2 (le_of_lt i.2))
  rw [aleph'_le_of_limit ho]
  exact fun a ha => le_ciSup (bddAbove_of_small _) (⟨a, ha⟩ : Iio o)

@[simp]
theorem aleph'_omega0 : aleph' ω = ℵ₀ :=
  eq_of_forall_ge_iff fun c => by
    simp only [aleph'_le_of_limit omega0_isLimit, lt_omega0, exists_imp, aleph0_le]
    exact forall_swap.trans (forall_congr' fun n => by simp only [forall_eq, aleph'_nat])

@[deprecated (since := "2024-09-30")]
alias aleph'_omega := aleph'_omega0

set_option linter.deprecated false in
/-- `aleph'` and `aleph_idx` form an equivalence between `Ordinal` and `Cardinal` -/
@[deprecated aleph' (since := "2024-08-28")]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.aleph'`. -/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans aleph'.toOrderEmbedding

@[simp]
theorem _root_.Ordinal.card_omega (o : Ordinal) : (omega o).card = aleph o :=
  rfl

@[simp]
theorem ord_aleph (o : Ordinal) : (aleph o).ord = omega o := by
  rw [← o.card_omega, (isInitial_omega o).ord_card]

theorem aleph_eq_aleph' (o : Ordinal) : aleph o = aleph' (ω + o) :=
  rfl

theorem aleph_lt {o₁ o₂ : Ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt

theorem aleph_le {o₁ o₂ : Ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  aleph.le_iff_le

theorem aleph_max (o₁ o₂ : Ordinal) : aleph (max o₁ o₂) = max (aleph o₁) (aleph o₂) :=
  aleph.monotone.map_max

@[deprecated aleph_max (since := "2024-08-28")]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) :=
  (aleph_max o₁ o₂).symm

@[simp]
theorem aleph_succ (o : Ordinal) : aleph (succ o) = succ (aleph o) := by
  rw [aleph_eq_aleph', add_succ, aleph'_succ, aleph_eq_aleph']

@[simp]
theorem aleph_zero : aleph 0 = ℵ₀ := by rw [aleph_eq_aleph', add_zero, aleph'_omega0]

theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : aleph o = ⨆ a : Iio o, aleph a := by
  apply le_antisymm _ (ciSup_le' _)
  · rw [aleph_eq_aleph', aleph'_limit (ho.add _)]
    refine ciSup_mono' (bddAbove_of_small _) ?_
    rintro ⟨i, hi⟩
    cases' lt_or_le i ω with h h
    · rcases lt_omega0.1 h with ⟨n, rfl⟩
      use ⟨0, ho.pos⟩
      simpa using (nat_lt_aleph0 n).le
    · exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, aleph'_le.2 (le_add_sub _ _)⟩
  · exact fun i => aleph_le.2 (le_of_lt i.2)

theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by rw [← aleph'_omega0, aleph'_le]

theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ aleph o := by
  rw [aleph_eq_aleph', aleph0_le_aleph']
  apply Ordinal.le_add_right

theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by rwa [← aleph'_zero, aleph'_lt]

theorem aleph_pos (o : Ordinal) : 0 < aleph o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

@[simp]
theorem aleph_toNat (o : Ordinal) : toNat (aleph o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o

@[simp]
theorem aleph_toPartENat (o : Ordinal) : toPartENat (aleph o) = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o

instance nonempty_toType_aleph (o : Ordinal) : Nonempty (aleph o).ord.toType := by
  rw [toType_nonempty_iff_ne_zero, ← ord_zero]
  exact fun h => (ord_injective h).not_gt (aleph_pos o)

theorem ord_aleph_isLimit (o : Ordinal) : (aleph o).ord.IsLimit :=
  ord_isLimit <| aleph0_le_aleph _

instance (o : Ordinal) : NoMaxOrder (aleph o).ord.toType :=
  toType_noMax_of_succ_lt (ord_aleph_isLimit o).2

theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
    ⟨aleph'.symm c - ω, by
      rw [aleph_eq_aleph', Ordinal.add_sub_cancel_of_le, aleph'.apply_symm_apply]
      rwa [← aleph0_le_aleph', aleph'.apply_symm_apply]⟩,
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩

@[deprecated isNormal_omega' (since := "2024-10-11")]
theorem aleph'_isNormal : IsNormal (ord ∘ aleph') := by
  convert isNormal_omega'
  exact funext ord_aleph'

@[deprecated isNormal_omega (since := "2024-10-11")]
theorem aleph_isNormal : IsNormal (ord ∘ aleph) := by
  convert isNormal_omega
  exact funext ord_aleph

theorem succ_aleph0 : succ ℵ₀ = aleph 1 := by rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]

theorem aleph0_lt_aleph_one : ℵ₀ < aleph 1 := by
  rw [← succ_aleph0]
  apply lt_succ

theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < aleph 1 := by
  rw [← succ_aleph0, lt_succ_iff, le_aleph0_iff_set_countable]

section deprecated

set_option linter.deprecated false

-- TODO: these lemmas should be stated in terms of the `ω` function and of an `IsInitial` predicate,
-- neither of which currently exist.
--
-- They should also use `¬ BddAbove` instead of `Unbounded (· < ·)`.

/-- Ordinals that are cardinals are unbounded. -/
@[deprecated (since := "2024-09-24")]
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩

@[deprecated (since := "2024-09-24")]
theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
  ⟨aleph'.symm o.card, by simpa using ho⟩

/-- Infinite ordinals that are cardinals are unbounded. -/
@[deprecated (since := "2024-09-24")]
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ ω ≤ b } :=
  (unbounded_lt_inter_le ω).2 ord_card_unbounded

@[deprecated (since := "2024-09-24")]
theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
    ∃ a, (aleph a).ord = o := by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  use a - ω
  rwa [aleph_eq_aleph', Ordinal.add_sub_cancel_of_le]
  rwa [← aleph0_le_aleph', ← ord_le_ord, ha, ord_aleph0]

end deprecated

/-! ### Beth cardinals -/

/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ (beth o)`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o aleph0 (fun _ x => (2 : Cardinal) ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2

@[simp]
theorem beth_zero : beth 0 = aleph0 :=
  limitRecOn_zero _ _ _

@[simp]
theorem beth_succ (o : Ordinal) : beth (succ o) = 2 ^ beth o :=
  limitRecOn_succ _ _ _ _

theorem beth_limit {o : Ordinal} : o.IsLimit → beth o = ⨆ a : Iio o, beth a :=
  limitRecOn_limit _ _ _ _

theorem beth_strictMono : StrictMono beth := by
  intro a b
  induction' b using Ordinal.induction with b IH generalizing a
  intro h
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · exact (Ordinal.not_lt_zero a h).elim
  · rw [lt_succ_iff] at h
    rw [beth_succ]
    apply lt_of_le_of_lt _ (cantor _)
    rcases eq_or_lt_of_le h with (rfl | h)
    · rfl
    exact (IH c (lt_succ c) h).le
  · apply (cantor _).trans_le
    rw [beth_limit hb, ← beth_succ]
    exact le_ciSup (bddAbove_of_small _) (⟨_, hb.succ_lt h⟩ : Iio b)

theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone

@[simp]
theorem beth_lt {o₁ o₂ : Ordinal} : beth o₁ < beth o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
theorem beth_le {o₁ o₂ : Ordinal} : beth o₁ ≤ beth o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le

theorem aleph_le_beth (o : Ordinal) : aleph o ≤ beth o := by
  induction o using limitRecOn with
  | H₁ => simp
  | H₂ o h =>
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  | H₃ o ho IH =>
    rw [aleph_limit ho, beth_limit ho]
    exact ciSup_mono (bddAbove_of_small _) fun x => IH x.1 x.2

theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ beth o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o

theorem beth_pos (o : Ordinal) : 0 < beth o :=
  aleph0_pos.trans_le <| aleph0_le_beth o

theorem beth_ne_zero (o : Ordinal) : beth o ≠ 0 :=
  (beth_pos o).ne'

theorem beth_normal : IsNormal.{u} fun o => (beth o).ord :=
  (isNormal_iff_strictMono_limit _).2
    ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha => by
      rw [beth_limit ho, ord_le]
      exact ciSup_le' fun b => ord_le.1 (ha _ b.2)⟩

end Cardinal
