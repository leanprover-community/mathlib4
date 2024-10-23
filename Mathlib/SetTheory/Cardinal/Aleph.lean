/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Cardinal.PartENat
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Aleph and beth functions

* The function `Cardinal.preAleph` gives the cardinals listed by their ordinal index.
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `Cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on. The notation `ω_` combines the latter with `Cardinal.ord`,
  giving an enumeration of (infinite) initial ordinals.
  Thus `ω_ 0 = ω` and `ω₁ = ω_ 1` is the first uncountable ordinal.
* The function `Cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Notation

The following notation is scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib.SetTheory.Cardinal.Continuum`.
-/

assert_not_exists Module
assert_not_exists Finsupp
assert_not_exists Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

/-- An ordinal is initial when it is the first ordinal with a given cardinality.

This is written as `o.card.ord = o`, i.e. `o` is the smallest ordinal with cardinality `o.card`. -/
def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o

theorem IsInitial.ord_card {o : Ordinal} (h : IsInitial o) : o.card.ord = o := h

theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) : a.card ≤ b.card ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, Ordinal.card_le_card⟩
  rw [← ord_le_ord, ha.ord_card] at h
  exact h.trans (ord_card_le b)

theorem IsInitial.card_lt_card {a b : Ordinal} (hb : IsInitial b) : a.card < b.card ↔ a < b :=
  lt_iff_lt_of_le_iff_le hb.card_le_card

theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by
  rw [IsInitial, card_ord]

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
  map_rel_iff' {a _} := a.2.card_le_card

-- TODO: define `omega` as the enumerator function of `IsInitial`, and redefine
-- `aleph x = (omega x).card`.

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/-- The "pre-aleph" function gives the cardinals listed by their ordinal index. `preAleph n = n`,
`preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
def preAleph : Ordinal.{u} ≃o Cardinal.{u} := by
  let f := RelEmbedding.collapse Cardinal.ord.orderEmbedding.ltEmbedding.{u}
  refine (OrderIso.ofRelIsoLT <| RelIso.ofSurjective f ?_).symm
  apply f.eq_or_principal.resolve_right
  rintro ⟨o, e⟩
  have : ∀ c, f c < o := fun c => (e _).1 ⟨_, rfl⟩
  refine Ordinal.inductionOn o ?_ this
  intro α r _ h
  let s := ⨆ a, invFun f (Ordinal.typein r a)
  apply (lt_succ s).not_le
  have I : Injective f := f.toEmbedding.injective
  simpa only [typein_enum, leftInverse_invFun I (succ s)] using
    le_ciSup
      (Cardinal.bddAbove_range.{u, u} fun a : α => invFun f (Ordinal.typein r a))
      (Ordinal.enum r ⟨_, h (succ s)⟩)

@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id]
  exact Quotient.sound ⟨preAleph.symm.toRelIsoLT⟩

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal

theorem preAleph_lt_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ < preAleph o₂ ↔ o₁ < o₂ :=
  preAleph.lt_iff_lt

theorem preAleph_le_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ ≤ preAleph o₂ ↔ o₁ ≤ o₂ :=
  preAleph.le_iff_le

theorem preAleph_max (o₁ o₂ : Ordinal) : preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂) :=
  preAleph.monotone.map_max

@[simp]
theorem preAleph_zero : preAleph 0 = 0 :=
  preAleph.map_bot

@[simp]
theorem preAleph_succ (o : Ordinal) : preAleph (succ o) = succ (preAleph o) :=
  preAleph.map_succ o

@[simp]
theorem preAleph_nat : ∀ n : ℕ, preAleph n = n
  | 0 => preAleph_zero
  | n + 1 => show preAleph (succ n) = n.succ by rw [preAleph_succ, preAleph_nat n, nat_succ]

theorem preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o := by
  rw [← preAleph_zero, preAleph_lt_preAleph]

@[simp]
theorem lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o) :=
  ((InitialSeg.ofIso preAleph.toRelIsoLT).trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans (InitialSeg.ofIso preAleph.toRelIsoLT)) o

theorem preAleph_le_of_isLimit {o : Ordinal} (l : o.IsLimit) {c} :
    preAleph o ≤ c ↔ ∀ o' < o, preAleph o' ≤ c :=
  ⟨fun h o' h' => (preAleph_le_preAleph.2 <| h'.le).trans h, fun h => by
    rw [← preAleph.apply_symm_apply c, preAleph_le_preAleph, limit_le l]
    intro x h'
    rw [← preAleph_le_preAleph, preAleph.apply_symm_apply]
    exact h _ h'⟩

theorem preAleph_limit {o : Ordinal} (ho : o.IsLimit) : preAleph o = ⨆ a : Iio o, preAleph a := by
  refine le_antisymm ?_ (ciSup_le' fun i => preAleph_le_preAleph.2 i.2.le)
  rw [preAleph_le_of_isLimit ho]
  exact fun a ha => le_ciSup (bddAbove_of_small _) (⟨a, ha⟩ : Iio o)

@[simp]
theorem preAleph_omega0 : preAleph ω = ℵ₀ :=
  eq_of_forall_ge_iff fun c => by
    simp only [preAleph_le_of_isLimit isLimit_omega0, lt_omega0, exists_imp, aleph0_le]
    exact forall_swap.trans (forall_congr' fun n => by simp only [forall_eq, preAleph_nat])

@[simp]
theorem aleph0_le_preAleph {o : Ordinal} : ℵ₀ ≤ preAleph o ↔ ω ≤ o := by
  rw [← preAleph_omega0, preAleph_le_preAleph]

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.aleph'`. -/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans preAleph.toOrderEmbedding

@[inherit_doc]
scoped notation "ℵ_ " => aleph

/-- `ℵ₁` is the first uncountable ordinal. -/
scoped notation "ℵ₁" => ℵ_ 1

theorem aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o) :=
  rfl

theorem aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt

@[deprecated aleph_lt_aleph (since := "2024-10-22")]
alias aleph_lt := aleph_lt_aleph

theorem aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ ≤ ℵ_ o₂ ↔ o₁ ≤ o₂ :=
  aleph.le_iff_le

@[deprecated aleph_le_aleph (since := "2024-10-22")]
alias aleph_le := aleph_le_aleph

theorem aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂) :=
  aleph.monotone.map_max

@[deprecated aleph_max (since := "2024-08-28")]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (ℵ_ o₁) (ℵ_ o₂) = ℵ_ (max o₁ o₂) :=
  (aleph_max o₁ o₂).symm

@[simp]
theorem aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o) := by
  rw [aleph_eq_preAleph, add_succ, preAleph_succ, aleph_eq_preAleph]

@[simp]
theorem aleph_zero : ℵ_ 0 = ℵ₀ := by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  simp [aleph_eq_preAleph]

theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : ℵ_ o = ⨆ a : Iio o, ℵ_ a := by
  apply le_antisymm _ (ciSup_le' _)
  · rw [aleph_eq_preAleph, preAleph_limit (ho.add _)]
    refine ciSup_mono' (bddAbove_of_small _) ?_
    rintro ⟨i, hi⟩
    cases' lt_or_le i ω with h h
    · rcases lt_omega0.1 h with ⟨n, rfl⟩
      use ⟨0, ho.pos⟩
      simpa using (nat_lt_aleph0 n).le
    · exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, preAleph_le_preAleph.2 (le_add_sub _ _)⟩
  · exact fun i => aleph_le_aleph.2 i.2.le

theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ ℵ_ o := by
  rw [aleph_eq_preAleph, aleph0_le_preAleph]
  apply Ordinal.le_add_right

theorem aleph_pos (o : Ordinal) : 0 < ℵ_ o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

@[simp]
theorem aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o

@[simp]
theorem aleph_toPartENat (o : Ordinal) : toPartENat (ℵ_ o) = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o

instance nonempty_toType_aleph (o : Ordinal) : Nonempty (ℵ_ o).ord.toType := by
  rw [toType_nonempty_iff_ne_zero, ← ord_zero]
  exact fun h => (ord_injective h).not_gt (aleph_pos o)

theorem ord_aleph_isLimit (o : Ordinal) : (ℵ_ o).ord.IsLimit :=
  isLimit_ord <| aleph0_le_aleph _

instance (o : Ordinal) : NoMaxOrder (ℵ_ o).ord.toType :=
  toType_noMax_of_succ_lt (ord_aleph_isLimit o).2

theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = ℵ_ o :=
  ⟨fun h =>
    ⟨preAleph.symm c - ω, by
      rw [aleph_eq_preAleph, Ordinal.add_sub_cancel_of_le, preAleph.apply_symm_apply]
      rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]⟩,
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩

theorem preAleph_isNormal : IsNormal (ord ∘ preAleph) :=
  ⟨fun o => ord_lt_ord.2 <| preAleph_lt_preAleph.2 <| lt_succ o, fun o l a => by
    simp [ord_le, preAleph_le_of_isLimit l]⟩

theorem aleph_isNormal : IsNormal (ord ∘ aleph) :=
  preAleph_isNormal.trans <| isNormal_add_right ω

theorem succ_aleph0 : succ ℵ₀ = ℵ₁ := by rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]

theorem aleph0_lt_aleph_one : ℵ₀ < ℵ₁ := by
  rw [← succ_aleph0]
  apply lt_succ

theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ₁ := by
  rw [← succ_aleph0, lt_succ_iff, le_aleph0_iff_set_countable]

@[simp]
theorem aleph1_le_lift {c : Cardinal.{u}} : ℵ₁ ≤ lift.{v} c ↔ ℵ₁ ≤ c := by
  simpa using lift_le (a := ℵ₁)

@[simp]
theorem lift_le_aleph1 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₁ ↔ c ≤ ℵ₁ := by
  simpa using lift_le (b := ℵ₁)

@[simp]
theorem aleph1_lt_lift {c : Cardinal.{u}} : ℵ₁ < lift.{v} c ↔ ℵ₁ < c := by
  simpa using lift_lt (a := ℵ₁)

@[simp]
theorem lift_lt_aleph1 {c : Cardinal.{u}} : lift.{v} c < ℵ₁ ↔ c < ℵ₁ := by
  simpa using lift_lt (b := ℵ₁)

@[simp]
theorem aleph1_eq_lift {c : Cardinal.{u}} : ℵ₁ = lift.{v} c ↔ ℵ₁ = c := by
  simpa using lift_inj (a := ℵ₁)

@[simp]
theorem lift_eq_aleph1 {c : Cardinal.{u}} : lift.{v} c = ℵ₁ ↔ c = ℵ₁ := by
  simpa using lift_inj (b := ℵ₁)

section deprecated

set_option linter.deprecated false
set_option linter.docPrime false

@[deprecated preAleph (since := "2024-10-22")]
noncomputable alias aleph' := preAleph

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `alephIdx`.
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated preAleph (since := "2024-08-28")]
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ℵ₀ = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `alephIdx`. -/
@[deprecated preAleph (since := "2024-08-28")]
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

@[deprecated (since := "2024-08-28")]
theorem alephIdx.initialSeg_coe : (alephIdx.initialSeg : Cardinal → Ordinal) = alephIdx :=
  rfl

@[deprecated (since := "2024-08-28")]
theorem alephIdx_lt {a b} : alephIdx a < alephIdx b ↔ a < b :=
  alephIdx.initialSeg.toRelEmbedding.map_rel_iff

@[deprecated (since := "2024-08-28")]
theorem alephIdx_le {a b} : alephIdx a ≤ alephIdx b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, alephIdx_lt]

@[deprecated (since := "2024-08-28")]
theorem alephIdx.init {a b} : b < alephIdx a → ∃ c, alephIdx c = b :=
  alephIdx.initialSeg.init

@[deprecated (since := "2024-08-28")]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx :=
  rfl

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
@[deprecated aleph' (since := "2024-08-28")]
def Aleph'.relIso :=
  aleph'

@[deprecated (since := "2024-08-28")]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl

@[deprecated preAleph_lt_preAleph (since := "2024-10-22")]
theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  aleph'.lt_iff_lt

@[deprecated preAleph_le_preAleph (since := "2024-10-22")]
theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  aleph'.le_iff_le

@[deprecated preAleph_max (since := "2024-10-22")]
theorem aleph'_max (o₁ o₂ : Ordinal) : aleph' (max o₁ o₂) = max (aleph' o₁) (aleph' o₂) :=
  aleph'.monotone.map_max

@[deprecated (since := "2024-08-28")]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c

@[deprecated (since := "2024-08-28")]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

@[deprecated preAleph_zero (since := "2024-10-22")]
theorem aleph'_zero : aleph' 0 = 0 :=
  aleph'.map_bot

@[deprecated preAleph_succ (since := "2024-10-22")]
theorem aleph'_succ (o : Ordinal) : aleph' (succ o) = succ (aleph' o) :=
  aleph'.map_succ o

@[deprecated preAleph_nat (since := "2024-10-22")]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n :=
  preAleph_nat

@[deprecated lift_preAleph (since := "2024-10-22")]
theorem lift_aleph' (o : Ordinal.{u}) : lift.{v} (aleph' o) = aleph' (Ordinal.lift.{v} o) :=
  lift_preAleph o

@[deprecated preAleph_le_of_isLimit (since := "2024-10-22")]
theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
  preAleph_le_of_isLimit l

@[deprecated preAleph_limit (since := "2024-10-22")]
theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a :=
  preAleph_limit ho

@[deprecated preAleph_omega0 (since := "2024-10-22")]
theorem aleph'_omega0 : aleph' ω = ℵ₀ :=
  preAleph_omega0

@[deprecated (since := "2024-09-30")]
alias aleph'_omega := aleph'_omega0

/-- `aleph'` and `aleph_idx` form an equivalence between `Ordinal` and `Cardinal` -/
@[deprecated aleph' (since := "2024-08-28")]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩

theorem aleph_eq_aleph' (o : Ordinal) : ℵ_ o = preAleph (ω + o) :=
  rfl

@[deprecated aleph0_le_preAleph (since := "2024-10-22")]
theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by
  rw [← aleph'_omega0, aleph'_le]

@[deprecated preAleph_pos (since := "2024-10-22")]
theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by
  rwa [← aleph'_zero, aleph'_lt]

@[deprecated preAleph_isNormal (since := "2024-10-22")]
theorem aleph'_isNormal : IsNormal (ord ∘ aleph') :=
  preAleph_isNormal

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
    ∃ a, (ℵ_ a).ord = o := by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  use a - ω
  rwa [aleph_eq_aleph', Ordinal.add_sub_cancel_of_le]
  rwa [← aleph0_le_aleph', ← ord_le_ord, ha, ord_aleph0]

end deprecated

/-! ### Beth cardinals -/

/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ beth o`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o ℵ₀ (fun _ x => 2 ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2

@[inherit_doc]
scoped notation "ℶ_ " => beth

@[simp]
theorem beth_zero : ℶ_ 0 = ℵ₀ :=
  limitRecOn_zero _ _ _

@[simp]
theorem beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ beth o :=
  limitRecOn_succ _ _ _ _

theorem beth_limit {o : Ordinal} : o.IsLimit → ℶ_ o = ⨆ a : Iio o, ℶ_ a :=
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
theorem beth_lt {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
theorem beth_le {o₁ o₂ : Ordinal} : ℶ_ o₁ ≤ ℶ_ o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le

theorem aleph_le_beth (o : Ordinal) : ℵ_ o ≤ ℶ_ o := by
  induction o using limitRecOn with
  | H₁ => simp
  | H₂ o h =>
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  | H₃ o ho IH =>
    rw [aleph_limit ho, beth_limit ho]
    exact ciSup_mono (bddAbove_of_small _) fun x => IH x.1 x.2

theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ ℶ_ o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o

theorem beth_pos (o : Ordinal) : 0 < ℶ_ o :=
  aleph0_pos.trans_le <| aleph0_le_beth o

theorem beth_ne_zero (o : Ordinal) : ℶ_ o ≠ 0 :=
  (beth_pos o).ne'

theorem isNormal_beth : IsNormal (ord ∘ beth) := by
  refine (isNormal_iff_strictMono_limit _).2
    ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha ↦ ?_⟩
  rw [comp_apply, beth_limit ho, ord_le]
  exact ciSup_le' fun b => ord_le.1 (ha _ b.2)

@[deprecated isNormal_beth (since := "2024-10-11")]
theorem beth_normal : IsNormal.{u} fun o => (beth o).ord :=
  isNormal_beth

end Cardinal

/-! ### Omega ordinals -/

namespace Ordinal

/--
`ω_ o` is a notation for the *initial ordinal* of cardinality
`aleph o`. Thus, for example `ω_ 0 = ω`.
-/
scoped notation "ω_" o => ord <| aleph o

/--
`ω₁` is the first uncountable ordinal.
-/
scoped notation "ω₁" => ord <| aleph 1

lemma omega_lt_omega1 : ω < ω₁ := ord_aleph0.symm.trans_lt (ord_lt_ord.mpr (aleph0_lt_aleph_one))

end Ordinal
