/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Linarith

#align_import set_theory.cardinal.ordinal from "leanprover-community/mathlib"@"7c2ce0c2da15516b4e65d0c9e254bb6dc93abd1f"

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `Cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `Cardinal.aleph/idx`.
  `aleph' n = n`, `aleph' ω = ℵ₀`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `Cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on.
* The function `Cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Main Statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `List α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal Ordinal

universe u v w

namespace Cardinal

section UsingOrdinals

open Ordinal

theorem ord_isLimit {c} (co : ℵ₀ ≤ c) : (ord c).IsLimit := by
  refine' ⟨fun h => aleph0_ne_zero _, fun a => lt_imp_lt_of_le_imp_le fun h => _⟩
  -- ⊢ ℵ₀ = 0
  · rw [← Ordinal.le_zero, ord_le] at h
    -- ⊢ ℵ₀ = 0
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h
    -- 🎉 no goals
  · rw [ord_le] at h ⊢
    -- ⊢ c ≤ card a
    rwa [← @add_one_of_aleph0_le (card a), ← card_succ]
    -- ⊢ ℵ₀ ≤ card a
    rw [← ord_le, ← le_succ_of_isLimit, ord_le]
    -- ⊢ ℵ₀ ≤ card (succ a)
    · exact co.trans h
      -- 🎉 no goals
    · rw [ord_aleph0]
      -- ⊢ Ordinal.IsLimit ω
      exact omega_isLimit
      -- 🎉 no goals
#align cardinal.ord_is_limit Cardinal.ord_isLimit

/-! ### Aleph cardinals -/


/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `alephIdx`.
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding
#align cardinal.aleph_idx.initial_seg Cardinal.alephIdx.initialSeg

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
def alephIdx : Cardinal → Ordinal :=
  alephIdx.initialSeg
#align cardinal.aleph_idx Cardinal.alephIdx

@[simp]
theorem alephIdx.initialSeg_coe : (alephIdx.initialSeg : Cardinal → Ordinal) = alephIdx :=
  rfl
#align cardinal.aleph_idx.initial_seg_coe Cardinal.alephIdx.initialSeg_coe

@[simp]
theorem alephIdx_lt {a b} : alephIdx a < alephIdx b ↔ a < b :=
  alephIdx.initialSeg.toRelEmbedding.map_rel_iff
#align cardinal.aleph_idx_lt Cardinal.alephIdx_lt

@[simp]
theorem alephIdx_le {a b} : alephIdx a ≤ alephIdx b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, alephIdx_lt]
  -- 🎉 no goals
#align cardinal.aleph_idx_le Cardinal.alephIdx_le

theorem alephIdx.init {a b} : b < alephIdx a → ∃ c, alephIdx c = b :=
  alephIdx.initialSeg.init
#align cardinal.aleph_idx.init Cardinal.alephIdx.init

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ℵ₀ = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `alephIdx`. -/
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  @RelIso.ofSurjective Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) alephIdx.initialSeg.{u} <|
    (InitialSeg.eq_or_principal alephIdx.initialSeg.{u}).resolve_right fun ⟨o, e⟩ => by
      have : ∀ c, alephIdx c < o := fun c => (e _).2 ⟨_, rfl⟩
      -- ⊢ False
      refine' Ordinal.inductionOn o _ this; intro α r _ h
      -- ⊢ ∀ (α : Type u) (r : α → α → Prop) [inst : IsWellOrder α r], (∀ (c : Cardinal …
                                            -- ⊢ False
      let s := ⨆ a, invFun alephIdx (Ordinal.typein r a)
      -- ⊢ False
      apply (lt_succ s).not_le
      -- ⊢ succ s ≤ s
      have I : Injective.{u+2, u+2} alephIdx := alephIdx.initialSeg.toEmbedding.injective
      -- ⊢ succ s ≤ s
      simpa only [typein_enum, leftInverse_invFun I (succ s)] using
        le_ciSup
          (Cardinal.bddAbove_range.{u, u} fun a : α => invFun alephIdx (Ordinal.typein r a))
          (Ordinal.enum r _ (h (succ s)))
#align cardinal.aleph_idx.rel_iso Cardinal.alephIdx.relIso

@[simp]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx :=
  rfl
#align cardinal.aleph_idx.rel_iso_coe Cardinal.alephIdx.relIso_coe

@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id]; exact Quotient.sound ⟨alephIdx.relIso⟩
  -- ⊢ (type fun x x_1 => x < x_1) = type fun x x_1 => x < x_1
                        -- 🎉 no goals
#align cardinal.type_cardinal Cardinal.type_cardinal

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal
  -- 🎉 no goals
#align cardinal.mk_cardinal Cardinal.mk_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def Aleph'.relIso :=
  Cardinal.alephIdx.relIso.symm
#align cardinal.aleph'.rel_iso Cardinal.Aleph'.relIso

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc. -/
def aleph' : Ordinal → Cardinal :=
  Aleph'.relIso
#align cardinal.aleph' Cardinal.aleph'

@[simp]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl
#align cardinal.aleph'.rel_iso_coe Cardinal.aleph'.relIso_coe

@[simp]
theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  Aleph'.relIso.map_rel_iff
#align cardinal.aleph'_lt Cardinal.aleph'_lt

@[simp]
theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph'_lt
#align cardinal.aleph'_le Cardinal.aleph'_le

@[simp]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c
#align cardinal.aleph'_aleph_idx Cardinal.aleph'_alephIdx

@[simp]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o
#align cardinal.aleph_idx_aleph' Cardinal.alephIdx_aleph'

@[simp]
theorem aleph'_zero : aleph' 0 = 0 := by
  rw [← nonpos_iff_eq_zero, ← aleph'_alephIdx 0, aleph'_le]
  -- ⊢ 0 ≤ alephIdx 0
  apply Ordinal.zero_le
  -- 🎉 no goals
#align cardinal.aleph'_zero Cardinal.aleph'_zero

@[simp]
theorem aleph'_succ {o : Ordinal} : aleph' (succ o) = succ (aleph' o) := by
  apply (succ_le_of_lt <| aleph'_lt.2 <| lt_succ o).antisymm' (Cardinal.alephIdx_le.1 <| _)
  -- ⊢ alephIdx (aleph' (succ o)) ≤ alephIdx (succ (aleph' o))
  rw [alephIdx_aleph', succ_le_iff, ← aleph'_lt, aleph'_alephIdx]
  -- ⊢ aleph' o < succ (aleph' o)
  apply lt_succ
  -- 🎉 no goals
#align cardinal.aleph'_succ Cardinal.aleph'_succ

@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
  | 0 => aleph'_zero
  | n + 1 => show aleph' (succ n) = n.succ by rw [aleph'_succ, aleph'_nat n, nat_succ]
                                              -- 🎉 no goals
#align cardinal.aleph'_nat Cardinal.aleph'_nat

theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
  ⟨fun h o' h' => (aleph'_le.2 <| h'.le).trans h, fun h => by
    rw [← aleph'_alephIdx c, aleph'_le, limit_le l]
    -- ⊢ ∀ (x : Ordinal.{u_1}), x < o → x ≤ alephIdx c
    intro x h'
    -- ⊢ x ≤ alephIdx c
    rw [← aleph'_le, aleph'_alephIdx]
    -- ⊢ aleph' x ≤ c
    exact h _ h'⟩
    -- 🎉 no goals
#align cardinal.aleph'_le_of_limit Cardinal.aleph'_le_of_limit

theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a := by
  refine' le_antisymm _ (ciSup_le' fun i => aleph'_le.2 (le_of_lt i.2))
  -- ⊢ aleph' o ≤ ⨆ (a : ↑(Iio o)), aleph' ↑a
  rw [aleph'_le_of_limit ho]
  -- ⊢ ∀ (o' : Ordinal.{u_1}), o' < o → aleph' o' ≤ ⨆ (a : ↑(Iio o)), aleph' ↑a
  exact fun a ha => le_ciSup (bddAbove_of_small _) (⟨a, ha⟩ : Iio o)
  -- 🎉 no goals
#align cardinal.aleph'_limit Cardinal.aleph'_limit

@[simp]
theorem aleph'_omega : aleph' ω = ℵ₀ :=
  eq_of_forall_ge_iff fun c => by
    simp only [aleph'_le_of_limit omega_isLimit, lt_omega, exists_imp, aleph0_le]
    -- ⊢ (∀ (o' : Ordinal.{u_1}) (x : ℕ), o' = ↑x → aleph' o' ≤ c) ↔ ∀ (n : ℕ), ↑n ≤ c
    exact forall_swap.trans (forall_congr' fun n => by simp only [forall_eq, aleph'_nat])
    -- 🎉 no goals
#align cardinal.aleph'_omega Cardinal.aleph'_omega

/-- `aleph'` and `aleph_idx` form an equivalence between `Ordinal` and `Cardinal` -/
@[simp]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩
#align cardinal.aleph'_equiv Cardinal.aleph'Equiv

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on. -/
def aleph (o : Ordinal) : Cardinal :=
  aleph' (ω + o)
#align cardinal.aleph Cardinal.aleph

@[simp]
theorem aleph_lt {o₁ o₂ : Ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph'_lt.trans (add_lt_add_iff_left _)
#align cardinal.aleph_lt Cardinal.aleph_lt

@[simp]
theorem aleph_le {o₁ o₂ : Ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph_lt
#align cardinal.aleph_le Cardinal.aleph_le

@[simp]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) := by
  cases' le_total (aleph o₁) (aleph o₂) with h h
  -- ⊢ max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂)
  · rw [max_eq_right h, max_eq_right (aleph_le.1 h)]
    -- 🎉 no goals
  · rw [max_eq_left h, max_eq_left (aleph_le.1 h)]
    -- 🎉 no goals
#align cardinal.max_aleph_eq Cardinal.max_aleph_eq

@[simp]
theorem aleph_succ {o : Ordinal} : aleph (succ o) = succ (aleph o) := by
  rw [aleph, add_succ, aleph'_succ, aleph]
  -- 🎉 no goals
#align cardinal.aleph_succ Cardinal.aleph_succ

@[simp]
theorem aleph_zero : aleph 0 = ℵ₀ := by rw [aleph, add_zero, aleph'_omega]
                                        -- 🎉 no goals
#align cardinal.aleph_zero Cardinal.aleph_zero

theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : aleph o = ⨆ a : Iio o, aleph a := by
  apply le_antisymm _ (ciSup_le' _)
  -- ⊢ aleph o ≤ ⨆ (i : ↑(Iio o)), aleph ↑i
  · rw [aleph, aleph'_limit (ho.add _)]
    -- ⊢ ⨆ (a : ↑(Iio (ω + o))), aleph' ↑a ≤ ⨆ (i : ↑(Iio o)), aleph ↑i
    refine' ciSup_mono' (bddAbove_of_small _) _
    -- ⊢ ∀ (i : ↑(Iio (ω + o))), ∃ i', aleph' ↑i ≤ aleph ↑i'
    rintro ⟨i, hi⟩
    -- ⊢ ∃ i', aleph' ↑{ val := i, property := hi } ≤ aleph ↑i'
    cases' lt_or_le i ω with h h
    -- ⊢ ∃ i', aleph' ↑{ val := i, property := hi } ≤ aleph ↑i'
    · rcases lt_omega.1 h with ⟨n, rfl⟩
      -- ⊢ ∃ i', aleph' ↑{ val := ↑n, property := hi } ≤ aleph ↑i'
      use ⟨0, ho.pos⟩
      -- ⊢ aleph' ↑{ val := ↑n, property := hi } ≤ aleph ↑{ val := 0, property := (_ :  …
      simpa using (nat_lt_aleph0 n).le
      -- 🎉 no goals
    · exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, aleph'_le.2 (le_add_sub _ _)⟩
      -- 🎉 no goals
  · exact fun i => aleph_le.2 (le_of_lt i.2)
    -- 🎉 no goals
#align cardinal.aleph_limit Cardinal.aleph_limit

theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by rw [← aleph'_omega, aleph'_le]
                                                                     -- 🎉 no goals
#align cardinal.aleph_0_le_aleph' Cardinal.aleph0_le_aleph'

theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ aleph o := by
  rw [aleph, aleph0_le_aleph']
  -- ⊢ ω ≤ ω + o
  apply Ordinal.le_add_right
  -- 🎉 no goals
#align cardinal.aleph_0_le_aleph Cardinal.aleph0_le_aleph

theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by rwa [← aleph'_zero, aleph'_lt]
                                                                   -- 🎉 no goals
#align cardinal.aleph'_pos Cardinal.aleph'_pos

theorem aleph_pos (o : Ordinal) : 0 < aleph o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)
#align cardinal.aleph_pos Cardinal.aleph_pos

@[simp]
theorem aleph_toNat (o : Ordinal) : toNat (aleph o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o
#align cardinal.aleph_to_nat Cardinal.aleph_toNat

@[simp]
theorem aleph_toPartENat (o : Ordinal) : toPartENat (aleph o) = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o
#align cardinal.aleph_to_part_enat Cardinal.aleph_toPartENat

instance nonempty_out_aleph (o : Ordinal) : Nonempty (aleph o).ord.out.α := by
  rw [out_nonempty_iff_ne_zero, ← ord_zero]
  -- ⊢ ord (aleph o) ≠ ord 0
  exact fun h => (ord_injective h).not_gt (aleph_pos o)
  -- 🎉 no goals
#align cardinal.nonempty_out_aleph Cardinal.nonempty_out_aleph

theorem ord_aleph_isLimit (o : Ordinal) : (aleph o).ord.IsLimit :=
  ord_isLimit <| aleph0_le_aleph _
#align cardinal.ord_aleph_is_limit Cardinal.ord_aleph_isLimit

instance (o : Ordinal) : NoMaxOrder (aleph o).ord.out.α :=
  out_no_max_of_succ_lt (ord_aleph_isLimit o).2

theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
    ⟨alephIdx c - ω, by
      rw [aleph, Ordinal.add_sub_cancel_of_le, aleph'_alephIdx]
      -- ⊢ ω ≤ alephIdx c
      rwa [← aleph0_le_aleph', aleph'_alephIdx]⟩,
      -- 🎉 no goals
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩
#align cardinal.exists_aleph Cardinal.exists_aleph

theorem aleph'_isNormal : IsNormal (ord ∘ aleph') :=
  ⟨fun o => ord_lt_ord.2 <| aleph'_lt.2 <| lt_succ o, fun o l a => by
    simp [ord_le, aleph'_le_of_limit l]⟩
    -- 🎉 no goals
#align cardinal.aleph'_is_normal Cardinal.aleph'_isNormal

theorem aleph_isNormal : IsNormal (ord ∘ aleph) :=
  aleph'_isNormal.trans <| add_isNormal ω
#align cardinal.aleph_is_normal Cardinal.aleph_isNormal

theorem succ_aleph0 : succ ℵ₀ = aleph 1 := by rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]
                                              -- 🎉 no goals
#align cardinal.succ_aleph_0 Cardinal.succ_aleph0

theorem aleph0_lt_aleph_one : ℵ₀ < aleph 1 := by
  rw [← succ_aleph0]
  -- ⊢ ℵ₀ < succ ℵ₀
  apply lt_succ
  -- 🎉 no goals
#align cardinal.aleph_0_lt_aleph_one Cardinal.aleph0_lt_aleph_one

theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < aleph 1 := by
  rw [← succ_aleph0, lt_succ_iff, le_aleph0_iff_set_countable]
  -- 🎉 no goals
#align cardinal.countable_iff_lt_aleph_one Cardinal.countable_iff_lt_aleph_one

/-- Ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp
        -- ⊢ ord (card (ord (succ (card a)))) = ord (succ (card a))
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩
        -- 🎉 no goals
#align cardinal.ord_card_unbounded Cardinal.ord_card_unbounded

theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
  ⟨Cardinal.alephIdx.relIso o.card, by simpa using ho⟩
                                       -- 🎉 no goals
#align cardinal.eq_aleph'_of_eq_card_ord Cardinal.eq_aleph'_of_eq_card_ord

/-- `ord ∘ aleph'` enumerates the ordinals that are cardinals. -/
theorem ord_aleph'_eq_enum_card : ord ∘ aleph' = enumOrd { b : Ordinal | b.card.ord = b } := by
  rw [← eq_enumOrd _ ord_card_unbounded, range_eq_iff]
  -- ⊢ StrictMono (ord ∘ aleph') ∧ (∀ (a : Ordinal.{u_1}), (ord ∘ aleph') a ∈ {b |  …
  exact
    ⟨aleph'_isNormal.strictMono,
      ⟨fun a => by
        dsimp
        rw [card_ord], fun b hb => eq_aleph'_of_eq_card_ord hb⟩⟩
#align cardinal.ord_aleph'_eq_enum_card Cardinal.ord_aleph'_eq_enum_card

/-- Infinite ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ ω ≤ b } :=
  (unbounded_lt_inter_le ω).2 ord_card_unbounded
#align cardinal.ord_card_unbounded' Cardinal.ord_card_unbounded'

theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
    ∃ a, (aleph a).ord = o := by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  -- ⊢ ∃ a, ord (aleph a) = o
  use a - ω
  -- ⊢ ord (aleph (a - ω)) = o
  unfold aleph
  -- ⊢ ord (aleph' (ω + (a - ω))) = o
  rwa [Ordinal.add_sub_cancel_of_le]
  -- ⊢ ω ≤ a
  rwa [← aleph0_le_aleph', ← ord_le_ord, ha, ord_aleph0]
  -- 🎉 no goals
#align cardinal.eq_aleph_of_eq_card_ord Cardinal.eq_aleph_of_eq_card_ord

/-- `ord ∘ aleph` enumerates the infinite ordinals that are cardinals. -/
theorem ord_aleph_eq_enum_card :
    ord ∘ aleph = enumOrd { b : Ordinal | b.card.ord = b ∧ ω ≤ b } := by
  rw [← eq_enumOrd _ ord_card_unbounded']
  -- ⊢ StrictMono (ord ∘ aleph) ∧ range (ord ∘ aleph) = {b | ord (card b) = b ∧ ω ≤ …
  use aleph_isNormal.strictMono
  -- ⊢ range (ord ∘ aleph) = {b | ord (card b) = b ∧ ω ≤ b}
  rw [range_eq_iff]
  -- ⊢ (∀ (a : Ordinal.{u_1}), (ord ∘ aleph) a ∈ {b | ord (card b) = b ∧ ω ≤ b}) ∧  …
  refine' ⟨fun a => ⟨_, _⟩, fun b hb => eq_aleph_of_eq_card_ord hb.1 hb.2⟩
  -- ⊢ ord (card ((ord ∘ aleph) a)) = (ord ∘ aleph) a
  · rw [Function.comp_apply, card_ord]
    -- 🎉 no goals
  · rw [← ord_aleph0, Function.comp_apply, ord_le_ord]
    -- ⊢ ℵ₀ ≤ aleph a
    exact aleph0_le_aleph _
    -- 🎉 no goals
#align cardinal.ord_aleph_eq_enum_card Cardinal.ord_aleph_eq_enum_card

/-! ### Beth cardinals -/


/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ (beth o)`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o aleph0 (fun _ x => (2 : Cardinal) ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2
#align cardinal.beth Cardinal.beth

@[simp]
theorem beth_zero : beth 0 = aleph0 :=
  limitRecOn_zero _ _ _
#align cardinal.beth_zero Cardinal.beth_zero

@[simp]
theorem beth_succ (o : Ordinal) : beth (succ o) = 2 ^ beth o :=
  limitRecOn_succ _ _ _ _
#align cardinal.beth_succ Cardinal.beth_succ

theorem beth_limit {o : Ordinal} : o.IsLimit → beth o = ⨆ a : Iio o, beth a :=
  limitRecOn_limit _ _ _ _
#align cardinal.beth_limit Cardinal.beth_limit

theorem beth_strictMono : StrictMono beth := by
  intro a b
  -- ⊢ a < b → beth a < beth b
  induction' b using Ordinal.induction with b IH generalizing a
  -- ⊢ a < b → beth a < beth b
  intro h
  -- ⊢ beth a < beth b
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · exact (Ordinal.not_lt_zero a h).elim
    -- 🎉 no goals
  · rw [lt_succ_iff] at h
    -- ⊢ beth a < beth (succ c)
    rw [beth_succ]
    -- ⊢ beth a < 2 ^ beth c
    apply lt_of_le_of_lt _ (cantor _)
    -- ⊢ beth a ≤ beth c
    rcases eq_or_lt_of_le h with (rfl | h)
    -- ⊢ beth a ≤ beth a
    · rfl
      -- 🎉 no goals
    exact (IH c (lt_succ c) h).le
    -- 🎉 no goals
  · apply (cantor _).trans_le
    -- ⊢ 2 ^ beth a ≤ beth b
    rw [beth_limit hb, ← beth_succ]
    -- ⊢ beth (succ a) ≤ ⨆ (a : ↑(Iio b)), beth ↑a
    exact le_ciSup (bddAbove_of_small _) (⟨_, hb.succ_lt h⟩ : Iio b)
    -- 🎉 no goals
#align cardinal.beth_strict_mono Cardinal.beth_strictMono

theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone
#align cardinal.beth_mono Cardinal.beth_mono

@[simp]
theorem beth_lt {o₁ o₂ : Ordinal} : beth o₁ < beth o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt
#align cardinal.beth_lt Cardinal.beth_lt

@[simp]
theorem beth_le {o₁ o₂ : Ordinal} : beth o₁ ≤ beth o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le
#align cardinal.beth_le Cardinal.beth_le

theorem aleph_le_beth (o : Ordinal) : aleph o ≤ beth o := by
  induction o using limitRecOn with
  | H₁ => simp
  | H₂ o h =>
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  | H₃ o ho IH =>
    rw [aleph_limit ho, beth_limit ho]
    exact ciSup_mono (bddAbove_of_small _) fun x => IH x.1 x.2
#align cardinal.aleph_le_beth Cardinal.aleph_le_beth

theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ beth o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o
#align cardinal.aleph_0_le_beth Cardinal.aleph0_le_beth

theorem beth_pos (o : Ordinal) : 0 < beth o :=
  aleph0_pos.trans_le <| aleph0_le_beth o
#align cardinal.beth_pos Cardinal.beth_pos

theorem beth_ne_zero (o : Ordinal) : beth o ≠ 0 :=
  (beth_pos o).ne'
#align cardinal.beth_ne_zero Cardinal.beth_ne_zero

theorem beth_normal : IsNormal.{u} fun o => (beth o).ord :=
  (isNormal_iff_strictMono_limit _).2
    ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha => by
      rw [beth_limit ho, ord_le]
      -- ⊢ ⨆ (a : ↑(Iio o)), beth ↑a ≤ card a
      exact ciSup_le' fun b => ord_le.1 (ha _ b.2)⟩
      -- 🎉 no goals
#align cardinal.beth_normal Cardinal.beth_normal

/-! ### Properties of `mul` -/



/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c * c = c := by
  refine' le_antisymm _ (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans h) c)
  -- ⊢ c * c ≤ c
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine' Acc.recOn (Cardinal.lt_wf.apply c) (fun c _ => Quotient.inductionOn c fun α IH ol => _) h
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  skip
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  letI := linearOrderOfSTO r
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  haveI : IsWellOrder α (· < ·) := wo
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := fun p => max p.1 p.2
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  let f : α × α ↪ Ordinal × α × α :=
    ⟨fun p : α × α => (typein (· < ·) (g p), p), fun p q => congr_arg Prod.snd⟩
  let s := f ⁻¹'o Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  -- this is a well order on `α × α`.
  haveI : IsWellOrder _ s := (RelEmbedding.preimage _ _).isWellOrder
  -- ⊢ Quotient.mk isEquivalent α * Quotient.mk isEquivalent α ≤ Quotient.mk isEqui …
  /- it suffices to show that this well order is smaller than `r`
       if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
      `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
      same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
      contradiction. -/
  suffices type s ≤ type r by exact card_le_card this
  -- ⊢ type s ≤ type r
  refine' le_of_forall_lt fun o h => _
  -- ⊢ o < type r
  rcases typein_surj s h with ⟨p, rfl⟩
  -- ⊢ typein s p < type r
  rw [← e, lt_ord]
  -- ⊢ card (typein s p) < #α
  refine'
    lt_of_le_of_lt (_ : _ ≤ card (succ (typein (· < ·) (g p))) * card (succ (typein (· < ·) (g p))))
      _
  · have : { q | s q p } ⊆ insert (g p) { x | x < g p } ×ˢ insert (g p) { x | x < g p } := by
      intro q h
      simp only [Preimage, ge_iff_le, Embedding.coeFn_mk, Prod.lex_def, typein_lt_typein,
        typein_inj, mem_setOf_eq] at h
      exact max_le_iff.1 (le_iff_lt_or_eq.2 <| h.imp_right And.left)
    suffices H : (insert (g p) { x | r x (g p) } : Set α) ≃ Sum { x | r x (g p) } PUnit
    -- ⊢ card (typein s p) ≤ card (succ (typein (fun x x_1 => x < x_1) (g p))) * card …
    · exact
        ⟨(Set.embeddingOfSubset _ _ this).trans
            ((Equiv.Set.prod _ _).trans (H.prodCongr H)).toEmbedding⟩
    refine' (Equiv.Set.insert _).trans ((Equiv.refl _).sumCongr punitEquivPUnit)
    -- ⊢ ¬g p ∈ {x | r x (g p)}
    apply @irrefl _ r
    -- 🎉 no goals
  cases' lt_or_le (card (succ (typein (· < ·) (g p)))) ℵ₀ with qo qo
  -- ⊢ card (succ (typein (fun x x_1 => x < x_1) (g p))) * card (succ (typein (fun  …
  · exact (mul_lt_aleph0 qo qo).trans_le ol
    -- 🎉 no goals
  · suffices : (succ (typein LT.lt (g p))).card < ⟦α⟧
    -- ⊢ card (succ (typein (fun x x_1 => x < x_1) (g p))) * card (succ (typein (fun  …
    · exact (IH _ this qo).trans_lt this
      -- 🎉 no goals
    rw [← lt_ord]
    -- ⊢ succ (typein LT.lt (g p)) < ord (Quotient.mk isEquivalent α)
    apply (ord_isLimit ol).2
    -- ⊢ typein LT.lt (g p) < ord (Quotient.mk isEquivalent α)
    rw [mk'_def, e]
    -- ⊢ typein LT.lt (g p) < type r
    apply typein_lt_type
    -- 🎉 no goals
#align cardinal.mul_eq_self Cardinal.mul_eq_self

end UsingOrdinals

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans hb) a)
               -- 🎉 no goals
      (by simpa only [one_mul] using mul_le_mul_right' (one_le_aleph0.trans ha) b)
          -- 🎉 no goals
#align cardinal.mul_eq_max Cardinal.mul_eq_max

@[simp]
theorem mul_mk_eq_max {α β : Type _} [Infinite α] [Infinite β] : #α * #β = max #α #β :=
  mul_eq_max (aleph0_le_mk α) (aleph0_le_mk β)
#align cardinal.mul_mk_eq_max Cardinal.mul_mk_eq_max

@[simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : aleph o₁ * aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (aleph0_le_aleph o₁) (aleph0_le_aleph o₂), max_aleph_eq]
  -- 🎉 no goals
#align cardinal.aleph_mul_aleph Cardinal.aleph_mul_aleph

@[simp]
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_right ha)
#align cardinal.aleph_0_mul_eq Cardinal.aleph0_mul_eq

@[simp]
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_left ha)
#align cardinal.mul_aleph_0_eq Cardinal.mul_aleph0_eq

--Porting note: removed `simp`, `simp` can prove it
theorem aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α :=
  aleph0_mul_eq (aleph0_le_mk α)
#align cardinal.aleph_0_mul_mk_eq Cardinal.aleph0_mul_mk_eq

--Porting note: removed `simp`, `simp` can prove it
theorem mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α :=
  mul_aleph0_eq (aleph0_le_mk α)
#align cardinal.mk_mul_aleph_0_eq Cardinal.mk_mul_aleph0_eq

@[simp]
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * aleph o = aleph o :=
  aleph0_mul_eq (aleph0_le_aleph o)
#align cardinal.aleph_0_mul_aleph Cardinal.aleph0_mul_aleph

@[simp]
theorem aleph_mul_aleph0 (o : Ordinal) : aleph o * ℵ₀ = aleph o :=
  mul_aleph0_eq (aleph0_le_aleph o)
#align cardinal.aleph_mul_aleph_0 Cardinal.aleph_mul_aleph0

theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
  (mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (mul_lt_aleph0 h h).trans_le hc) fun h => by
      rw [mul_eq_self h]
      -- ⊢ max a b < c
      exact max_lt h1 h2
      -- 🎉 no goals
#align cardinal.mul_lt_of_lt Cardinal.mul_lt_of_lt

theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b := by
  convert mul_le_mul' (le_max_left a b) (le_max_right a b) using 1
  -- ⊢ max a b = max a b * max a b
  rw [mul_eq_self]
  -- ⊢ ℵ₀ ≤ max a b
  refine' h.trans (le_max_left a b)
  -- 🎉 no goals
#align cardinal.mul_le_max_of_aleph_0_le_left Cardinal.mul_le_max_of_aleph0_le_left

theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) :
    a * b = max a b := by
  cases' le_or_lt ℵ₀ b with hb hb
  -- ⊢ a * b = max a b
  · exact mul_eq_max h hb
    -- 🎉 no goals
  refine' (mul_le_max_of_aleph0_le_left h).antisymm _
  -- ⊢ max a b ≤ a * b
  have : b ≤ a := hb.le.trans h
  -- ⊢ max a b ≤ a * b
  rw [max_eq_left this]
  -- ⊢ a ≤ a * b
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') a
  -- ⊢ a = a * 1
  rw [mul_one]
  -- 🎉 no goals
#align cardinal.mul_eq_max_of_aleph_0_le_left Cardinal.mul_eq_max_of_aleph0_le_left

theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by
  simpa only [mul_comm b, max_comm b] using mul_le_max_of_aleph0_le_left h
  -- 🎉 no goals
#align cardinal.mul_le_max_of_aleph_0_le_right Cardinal.mul_le_max_of_aleph0_le_right

theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by
  rw [mul_comm, max_comm]
  -- ⊢ b * a = max b a
  exact mul_eq_max_of_aleph0_le_left h h'
  -- 🎉 no goals
#align cardinal.mul_eq_max_of_aleph_0_le_right Cardinal.mul_eq_max_of_aleph0_le_right

theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b := by
  rcases aleph0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  -- ⊢ a * b = max a b
  · exact mul_eq_max_of_aleph0_le_left ha' hb
    -- 🎉 no goals
  · exact mul_eq_max_of_aleph0_le_right ha hb'
    -- 🎉 no goals
#align cardinal.mul_eq_max' Cardinal.mul_eq_max'

theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ := by
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  -- ⊢ 0 * b ≤ max (max 0 b) ℵ₀
                                          -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb0); · simp
  -- ⊢ a * 0 ≤ max (max a 0) ℵ₀
                                          -- 🎉 no goals
  cases' le_or_lt ℵ₀ a with ha ha
  -- ⊢ a * b ≤ max (max a b) ℵ₀
  · rw [mul_eq_max_of_aleph0_le_left ha hb0]
    -- ⊢ max a b ≤ max (max a b) ℵ₀
    exact le_max_left _ _
    -- 🎉 no goals
  · cases' le_or_lt ℵ₀ b with hb hb
    -- ⊢ a * b ≤ max (max a b) ℵ₀
    · rw [mul_comm, mul_eq_max_of_aleph0_le_left hb ha0, max_comm]
      -- ⊢ max a b ≤ max (max a b) ℵ₀
      exact le_max_left _ _
      -- 🎉 no goals
    · exact le_max_of_le_right (mul_lt_aleph0 ha hb).le
      -- 🎉 no goals
#align cardinal.mul_le_max Cardinal.mul_le_max

theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph0_le_left ha hb', max_eq_left hb]
  -- 🎉 no goals
#align cardinal.mul_eq_left Cardinal.mul_eq_left

theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']
  -- 🎉 no goals
#align cardinal.mul_eq_right Cardinal.mul_eq_right

theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) a
  -- ⊢ a = 1 * a
  rw [one_mul]
  -- 🎉 no goals
#align cardinal.le_mul_left Cardinal.le_mul_left

theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by
  rw [mul_comm]
  -- ⊢ a ≤ b * a
  exact le_mul_left h
  -- 🎉 no goals
#align cardinal.le_mul_right Cardinal.le_mul_right

theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  -- ⊢ a * b = a ↔ (ℵ₀ ≤ a ∧ b ≤ a) ∧ b ≠ 0 ∨ b = 1 ∨ a = 0
  refine' ⟨fun h => _, _⟩
  -- ⊢ (ℵ₀ ≤ a ∧ b ≤ a) ∧ b ≠ 0 ∨ b = 1 ∨ a = 0
  · cases' le_or_lt ℵ₀ a with ha ha
    -- ⊢ (ℵ₀ ≤ a ∧ b ≤ a) ∧ b ≠ 0 ∨ b = 1 ∨ a = 0
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_lt aleph0_pos
      left
      -- ⊢ (ℵ₀ ≤ a ∧ b ≤ a) ∧ b ≠ 0
      rw [and_assoc]
      -- ⊢ ℵ₀ ≤ a ∧ b ≤ a ∧ b ≠ 0
      use ha
      -- ⊢ b ≤ a ∧ b ≠ 0
      constructor
      -- ⊢ b ≤ a
      · rw [← not_lt]
        -- ⊢ ¬a < b
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
        -- 🎉 no goals
      · rintro rfl
        -- ⊢ False
        apply this
        -- ⊢ a = 0
        rw [mul_zero] at h
        -- ⊢ a = 0
        exact h.symm
        -- 🎉 no goals
    right
    -- ⊢ b = 1 ∨ a = 0
    by_cases h2a : a = 0
    -- ⊢ b = 1 ∨ a = 0
    · exact Or.inr h2a
      -- 🎉 no goals
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      exact h.symm
    left
    -- ⊢ b = 1
    rw [← h, mul_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    -- ⊢ b = 1
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    contradiction
    -- ⊢ 0 = 1
    contradiction
    -- ⊢ ↑m = 1
    rw [← Ne] at h2a
    -- ⊢ ↑m = 1
    rw [← one_le_iff_ne_zero] at h2a hb
    -- ⊢ ↑m = 1
    norm_cast at h2a hb h ⊢
    -- ⊢ m = 1
    apply le_antisymm _ hb
    -- ⊢ m ≤ 1
    rw [← not_lt]
    -- ⊢ ¬1 < m
    apply fun h2b => ne_of_gt _ h
    -- ⊢ 1 < m → n < n * m
    conv_rhs => left; rw [← mul_one n]
    -- ⊢ 1 < m → n * 1 < n * m
    rw [mul_lt_mul_left]
    -- ⊢ 1 < m → 1 < m
    exact id
    -- ⊢ 0 < n
    apply Nat.lt_of_succ_le h2a
    -- 🎉 no goals
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph0_le_left ha hb, max_eq_left hab]
      -- 🎉 no goals
    all_goals simp
    -- 🎉 no goals
#align cardinal.mul_eq_left_iff Cardinal.mul_eq_left_iff

/-! ### Properties of `add` -/


/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by
      convert mul_le_mul_right' ((nat_lt_aleph0 2).le.trans h) c using 1
      -- ⊢ c + c = ↑2 * c
      <;> simp [two_mul, mul_eq_self h])
          -- 🎉 no goals
          -- 🎉 no goals
    (self_le_add_left c c)
#align cardinal.add_eq_self Cardinal.add_eq_self

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
  le_antisymm
      (add_eq_self (ha.trans (le_max_left a b)) ▸
        add_le_add (le_max_left _ _) (le_max_right _ _)) <|
    max_le (self_le_add_right _ _) (self_le_add_left _ _)
#align cardinal.add_eq_max Cardinal.add_eq_max

theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]
  -- 🎉 no goals
#align cardinal.add_eq_max' Cardinal.add_eq_max'

@[simp]
theorem add_mk_eq_max {α β : Type _} [Infinite α] : #α + #β = max #α #β :=
  add_eq_max (aleph0_le_mk α)
#align cardinal.add_mk_eq_max Cardinal.add_mk_eq_max

@[simp]
theorem add_mk_eq_max' {α β : Type _} [Infinite β] : #α + #β = max #α #β :=
  add_eq_max' (aleph0_le_mk β)
#align cardinal.add_mk_eq_max' Cardinal.add_mk_eq_max'

theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ := by
  cases' le_or_lt ℵ₀ a with ha ha
  -- ⊢ a + b ≤ max (max a b) ℵ₀
  · rw [add_eq_max ha]
    -- ⊢ max a b ≤ max (max a b) ℵ₀
    exact le_max_left _ _
    -- 🎉 no goals
  · cases' le_or_lt ℵ₀ b with hb hb
    -- ⊢ a + b ≤ max (max a b) ℵ₀
    · rw [add_comm, add_eq_max hb, max_comm]
      -- ⊢ max a b ≤ max (max a b) ℵ₀
      exact le_max_left _ _
      -- 🎉 no goals
    · exact le_max_of_le_right (add_lt_aleph0 ha hb).le
      -- 🎉 no goals
#align cardinal.add_le_max Cardinal.add_le_max

theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eq <| add_eq_self hc
#align cardinal.add_le_of_le Cardinal.add_le_of_le

theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  (add_le_add (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (add_lt_aleph0 h h).trans_le hc) fun h => by
      rw [add_eq_self h]; exact max_lt h1 h2
      -- ⊢ max a b < c
                          -- 🎉 no goals
#align cardinal.add_lt_of_lt Cardinal.add_lt_of_lt

theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by
  apply le_antisymm
  -- ⊢ b ≤ c
  · rw [← h]
    -- ⊢ b ≤ a + b
    apply self_le_add_left
    -- 🎉 no goals
  rw [← not_lt]; intro hb
  -- ⊢ ¬b < c
                 -- ⊢ False
  have : a + b < c := add_lt_of_lt hc ha hb
  -- ⊢ False
  simp [h, lt_irrefl] at this
  -- 🎉 no goals
#align cardinal.eq_of_add_eq_of_aleph_0_le Cardinal.eq_of_add_eq_of_aleph0_le

theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_left hb]
  -- 🎉 no goals
#align cardinal.add_eq_left Cardinal.add_eq_left

theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_comm, add_eq_left hb ha]
  -- 🎉 no goals
#align cardinal.add_eq_right Cardinal.add_eq_right

theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 := by
  rw [max_le_iff]
  -- ⊢ a + b = a ↔ ℵ₀ ≤ a ∧ b ≤ a ∨ b = 0
  refine' ⟨fun h => _, _⟩
  -- ⊢ ℵ₀ ≤ a ∧ b ≤ a ∨ b = 0
  · cases' le_or_lt ℵ₀ a with ha ha
    -- ⊢ ℵ₀ ≤ a ∧ b ≤ a ∨ b = 0
    · left
      -- ⊢ ℵ₀ ≤ a ∧ b ≤ a
      use ha
      -- ⊢ b ≤ a
      rw [← not_lt]
      -- ⊢ ¬a < b
      apply fun hb => ne_of_gt _ h
      -- ⊢ a < b → a < a + b
      intro hb
      -- ⊢ a < a + b
      exact hb.trans_le (self_le_add_left b a)
      -- 🎉 no goals
    right
    -- ⊢ b = 0
    rw [← h, add_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    -- ⊢ b = 0
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    -- ⊢ ↑m = 0
    norm_cast at h ⊢
    -- ⊢ m = 0
    rw [← add_right_inj, h, add_zero]
    -- 🎉 no goals
  · rintro (⟨h1, h2⟩ | h3)
    -- ⊢ a + b = a
    · rw [add_eq_max h1, max_eq_left h2]
      -- 🎉 no goals
    · rw [h3, add_zero]
      -- 🎉 no goals
#align cardinal.add_eq_left_iff Cardinal.add_eq_left_iff

theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by
  rw [add_comm, add_eq_left_iff]
  -- 🎉 no goals
#align cardinal.add_eq_right_iff Cardinal.add_eq_right_iff

theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
  add_eq_left ha ((nat_lt_aleph0 _).le.trans ha)
#align cardinal.add_nat_eq Cardinal.add_nat_eq

theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
  add_eq_left ha (one_le_aleph0.trans ha)
#align cardinal.add_one_eq Cardinal.add_one_eq

--Porting note: removed `simp`, `simp` can prove it
theorem mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α :=
  add_one_eq (aleph0_le_mk α)
#align cardinal.mk_add_one_eq Cardinal.mk_add_one_eq

protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  cases' le_or_lt ℵ₀ b with hb hb
  -- ⊢ b = c
  · have : a < b := ha.trans_le hb
    -- ⊢ b = c
    rw [add_eq_right hb this.le, eq_comm] at h
    -- ⊢ b = c
    rw [eq_of_add_eq_of_aleph0_le h this hb]
    -- 🎉 no goals
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph0 ha hb
    rw [lt_aleph0] at *
    -- ⊢ b = c
    rcases ha with ⟨n, rfl⟩
    -- ⊢ b = c
    rcases hb with ⟨m, rfl⟩
    -- ⊢ ↑m = c
    rcases hc with ⟨k, rfl⟩
    -- ⊢ ↑m = ↑k
    norm_cast at h ⊢
    -- ⊢ m = k
    apply add_left_cancel h
    -- 🎉 no goals
#align cardinal.eq_of_add_eq_add_left Cardinal.eq_of_add_eq_add_left

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  -- ⊢ a = c
  exact Cardinal.eq_of_add_eq_add_left h hb
  -- 🎉 no goals
#align cardinal.eq_of_add_eq_add_right Cardinal.eq_of_add_eq_add_right

@[simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : aleph o₁ + aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (aleph0_le_aleph o₁), max_aleph_eq]
  -- 🎉 no goals
#align cardinal.aleph_add_aleph Cardinal.aleph_add_aleph

theorem principal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Ordinal.Principal (· + ·) c.ord :=
  fun a b ha hb => by
  rw [lt_ord, Ordinal.card_add] at *
  -- ⊢ card a + card b < c
  exact add_lt_of_lt hc ha hb
  -- 🎉 no goals
#align cardinal.principal_add_ord Cardinal.principal_add_ord

theorem principal_add_aleph (o : Ordinal) : Ordinal.Principal (· + ·) (aleph o).ord :=
  principal_add_ord <| aleph0_le_aleph o
#align cardinal.principal_add_aleph Cardinal.principal_add_aleph

theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β :=
  ⟨fun h => Cardinal.eq_of_add_eq_add_right h γ₀, fun h => congr_fun (congr_arg (· + ·) h) γ⟩
#align cardinal.add_right_inj_of_lt_aleph_0 Cardinal.add_right_inj_of_lt_aleph0

@[simp]
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β :=
  add_right_inj_of_lt_aleph0 (nat_lt_aleph0 _)
#align cardinal.add_nat_inj Cardinal.add_nat_inj

@[simp]
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β :=
  add_right_inj_of_lt_aleph0 one_lt_aleph0
#align cardinal.add_one_inj Cardinal.add_one_inj

theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < Cardinal.aleph0) :
    α + γ ≤ β + γ ↔ α ≤ β := by
  refine' ⟨fun h => _, fun h => add_le_add_right h γ⟩
  -- ⊢ α ≤ β
  contrapose h
  -- ⊢ ¬α + γ ≤ β + γ
  rw [not_le, lt_iff_le_and_ne, Ne] at h ⊢
  -- ⊢ β + γ ≤ α + γ ∧ ¬β + γ = α + γ
  exact ⟨add_le_add_right h.1 γ, mt (add_right_inj_of_lt_aleph0 γ₀).1 h.2⟩
  -- 🎉 no goals
#align cardinal.add_le_add_iff_of_lt_aleph_0 Cardinal.add_le_add_iff_of_lt_aleph0

@[simp]
theorem add_nat_le_add_nat_iff_of_lt_aleph_0 {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 (nat_lt_aleph0 n)
#align cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0 Cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0

@[simp]
theorem add_one_le_add_one_iff_of_lt_aleph_0 {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 one_lt_aleph0
#align cardinal.add_one_le_add_one_iff_of_lt_aleph_0 Cardinal.add_one_le_add_one_iff_of_lt_aleph_0

/-! ### Properties about power -/

--Porting note: Annoying workaround because `c ^ n` when `n` is a `ℕ` coerces `c` for some reason.
local infixr:0 "^'" => @HPow.hPow Cardinal Cardinal Cardinal.instPowCardinal
-- -- mathport name: cardinal.pow.nat
local infixr:80 " ^ℕ " => @HPow.hPow Cardinal ℕ Cardinal instHPow

theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_aleph0.1 H2
  H3.symm ▸
    Quotient.inductionOn κ
      (fun α H1 =>
        Nat.recOn n
          (lt_of_lt_of_le
              (by
                rw [Nat.cast_zero, power_zero]
                -- ⊢ 1 < ℵ₀
                exact one_lt_aleph0)
                -- 🎉 no goals
              H1).le
          fun n ih =>
          le_of_le_of_eq
            (by
              rw [Nat.cast_succ, power_add, power_one]
              -- ⊢ Quotient.mk isEquivalent α ^ ↑n * Quotient.mk isEquivalent α ≤ Quotient.mk i …
              exact mul_le_mul_right' ih _)
              -- 🎉 no goals
            (mul_eq_self H1))
      H1
#align cardinal.pow_le Cardinal.pow_le

theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2
#align cardinal.pow_eq Cardinal.pow_eq

theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c := by
  apply ((power_le_power_right <| (cantor c).le).trans _).antisymm
  -- ⊢ 2 ^ c ≤ c ^ c
  · exact power_le_power_right ((nat_lt_aleph0 2).le.trans h)
    -- 🎉 no goals
  · rw [← power_mul, mul_eq_self h]
    -- 🎉 no goals
#align cardinal.power_self_eq Cardinal.power_self_eq

theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} #ι) : prod c = 2 ^ lift.{v} #ι := by
  rw [← lift_id'.{u, v} (prod.{u, v} c), lift_prod, ← lift_two_power]
  -- ⊢ (prod fun i => lift.{u, v} (c i)) = lift.{v, u} (2 ^ #ι)
  apply le_antisymm
  -- ⊢ (prod fun i => lift.{u, v} (c i)) ≤ lift.{v, u} (2 ^ #ι)
  · refine' (prod_le_prod _ _ h₂).trans_eq _
    -- ⊢ (prod fun i => lift.{v, u} #ι) = lift.{v, u} (2 ^ #ι)
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph0_le_mk ι), lift_umax.{u, v}]
    -- 🎉 no goals
  · rw [← prod_const', lift_prod]
    -- ⊢ (prod fun i => lift.{v, u} 2) ≤ prod fun i => lift.{u, v} (c i)
    refine' prod_le_prod _ _ fun i => _
    -- ⊢ lift.{v, u} 2 ≤ lift.{u, v} (c i)
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    -- ⊢ 2 ≤ c i
    exact h₁ i
    -- 🎉 no goals
#align cardinal.prod_eq_two_power Cardinal.prod_eq_two_power

theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)
#align cardinal.power_eq_two_power Cardinal.power_eq_two_power

theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h (by assumption_mod_cast) ((nat_lt_aleph0 n).le.trans h)
                           -- 🎉 no goals
#align cardinal.nat_power_eq Cardinal.nat_power_eq

theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ℕ n ≤ c :=
  pow_le h (nat_lt_aleph0 n)
#align cardinal.power_nat_le Cardinal.power_nat_le

theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ℕ n = c :=
  pow_eq h1 (by exact_mod_cast h2) (nat_lt_aleph0 n)
                -- 🎉 no goals
#align cardinal.power_nat_eq Cardinal.power_nat_eq

theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ := by
  cases' le_or_lt ℵ₀ c with hc hc
  -- ⊢ c ^ ↑n ≤ max c ℵ₀
  · exact le_max_of_le_left (power_nat_le hc)
    -- 🎉 no goals
  · exact le_max_of_le_right (power_lt_aleph0 hc (nat_lt_aleph0 _)).le
    -- 🎉 no goals
#align cardinal.power_nat_le_max Cardinal.power_nat_le_max

theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c := by
  apply le_antisymm
  -- ⊢ c ^< ℵ₀ ≤ c
  · rw [powerlt_le]
    -- ⊢ ∀ (x : Cardinal.{u_1}), x < ℵ₀ → c ^ x ≤ c
    intro c'
    -- ⊢ c' < ℵ₀ → c ^ c' ≤ c
    rw [lt_aleph0]
    -- ⊢ (∃ n, c' = ↑n) → c ^ c' ≤ c
    rintro ⟨n, rfl⟩
    -- ⊢ c ^ ↑n ≤ c
    apply power_nat_le h
    -- 🎉 no goals
  convert le_powerlt c one_lt_aleph0; rw [power_one]
  -- ⊢ c = c ^ 1
                                      -- 🎉 no goals
#align cardinal.powerlt_aleph_0 Cardinal.powerlt_aleph0

theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ := by
  cases' le_or_lt ℵ₀ c with h h
  -- ⊢ c ^< ℵ₀ ≤ max c ℵ₀
  · rw [powerlt_aleph0 h]
    -- ⊢ c ≤ max c ℵ₀
    apply le_max_left
    -- 🎉 no goals
  rw [powerlt_le]
  -- ⊢ ∀ (x : Cardinal.{u_1}), x < ℵ₀ → c ^ x ≤ max c ℵ₀
  exact fun c' hc' => (power_lt_aleph0 h hc').le.trans (le_max_right _ _)
  -- 🎉 no goals
#align cardinal.powerlt_aleph_0_le Cardinal.powerlt_aleph0_le

/-! ### Computing cardinality of various types -/


@[simp]
theorem mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α :=
  have H1 : ℵ₀ ≤ #α := aleph0_le_mk α
  Eq.symm <|
    le_antisymm ((le_def _ _).2 ⟨⟨fun a => [a], fun _ => by simp⟩⟩) <|
                                                            -- 🎉 no goals
      calc
        #(List α) = sum fun n : ℕ => #α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun _ : ℕ => #α := sum_le_sum _ _ fun n => pow_le H1 <| nat_lt_aleph0 n
        _ = #α := by simp [H1]
                     -- 🎉 no goals
#align cardinal.mk_list_eq_mk Cardinal.mk_list_eq_mk

theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀ :=
  mk_le_aleph0.antisymm (aleph0_le_mk _)
#align cardinal.mk_list_eq_aleph_0 Cardinal.mk_list_eq_aleph0

theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀ := by
  cases finite_or_infinite α
  -- ⊢ #(List α) = max #α ℵ₀
  · rw [mk_list_eq_aleph0, eq_comm, max_eq_right]
    -- ⊢ #α ≤ ℵ₀
    exact mk_le_aleph0
    -- 🎉 no goals
  · rw [mk_list_eq_mk, eq_comm, max_eq_left]
    -- ⊢ ℵ₀ ≤ #α
    exact aleph0_le_mk α
    -- 🎉 no goals
#align cardinal.mk_list_eq_max_mk_aleph_0 Cardinal.mk_list_eq_max_mk_aleph0

theorem mk_list_le_max (α : Type u) : #(List α) ≤ max ℵ₀ #α := by
  cases finite_or_infinite α
  -- ⊢ #(List α) ≤ max ℵ₀ #α
  · exact mk_le_aleph0.trans (le_max_left _ _)
    -- 🎉 no goals
  · rw [mk_list_eq_mk]
    -- ⊢ #α ≤ max ℵ₀ #α
    apply le_max_right
    -- 🎉 no goals
#align cardinal.mk_list_le_max Cardinal.mk_list_le_max

@[simp]
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α :=
  Eq.symm <|
    le_antisymm (mk_le_of_injective fun _ _ => Finset.singleton_inj.1) <|
      calc
        #(Finset α) ≤ #(List α) := mk_le_of_surjective List.toFinset_surjective
        _ = #α := mk_list_eq_mk α
#align cardinal.mk_finset_of_infinite Cardinal.mk_finset_of_infinite

@[simp]
theorem mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  apply le_antisymm
  -- ⊢ #(α →₀ β) ≤ max (lift.{v, u} #α) (lift.{u, v} #β)
  · calc
      #(α →₀ β) ≤ #(Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = #(α × β) := mk_finset_of_infinite _
      _ = max (lift.{v} #α) (lift.{u} #β) :=
        by rw [mk_prod, mul_eq_max_of_aleph0_le_left] <;> simp

  · apply max_le <;> rw [← lift_id #(α →₀ β), ← lift_umax]
    -- ⊢ lift.{v, u} #α ≤ #(α →₀ β)
                     -- ⊢ lift.{max u v, u} #α ≤ lift.{max u v, max u v} #(α →₀ β)
                     -- ⊢ lift.{max v u, v} #β ≤ lift.{max u v, max u v} #(α →₀ β)
    · cases' exists_ne (0 : β) with b hb
      -- ⊢ lift.{max u v, u} #α ≤ lift.{max u v, max u v} #(α →₀ β)
      exact lift_mk_le.{v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
      -- 🎉 no goals
    · inhabit α
      -- ⊢ lift.{max v u, v} #β ≤ lift.{max u v, max u v} #(α →₀ β)
      exact lift_mk_le.{u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩
      -- 🎉 no goals
#align cardinal.mk_finsupp_lift_of_infinite Cardinal.mk_finsupp_lift_of_infinite

theorem mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max #α #β := by simp
                                -- 🎉 no goals
#align cardinal.mk_finsupp_of_infinite Cardinal.mk_finsupp_of_infinite

@[simp]
theorem mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  cases fintypeOrInfinite α
  -- ⊢ #(α →₀ β) = max (lift.{v, u} #α) (lift.{u, v} #β)
  · rw [mk_finsupp_lift_of_fintype]
    -- ⊢ lift.{u, v} #β ^ Fintype.card α = max (lift.{v, u} #α) (lift.{u, v} #β)
    have : ℵ₀ ≤ (#β).lift := aleph0_le_lift.2 (aleph0_le_mk β)
    -- ⊢ lift.{u, v} #β ^ Fintype.card α = max (lift.{v, u} #α) (lift.{u, v} #β)
    rw [max_eq_right (le_trans _ this), power_nat_eq this]
    -- ⊢ 1 ≤ Fintype.card α
    exacts [Fintype.card_pos, lift_le_aleph0.2 (lt_aleph0_of_finite _).le]
    -- 🎉 no goals
  · apply mk_finsupp_lift_of_infinite
    -- 🎉 no goals
#align cardinal.mk_finsupp_lift_of_infinite' Cardinal.mk_finsupp_lift_of_infinite'

theorem mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max #α #β := by simp
                                -- 🎉 no goals
#align cardinal.mk_finsupp_of_infinite' Cardinal.mk_finsupp_of_infinite'

theorem mk_finsupp_nat (α : Type u) [Nonempty α] : #(α →₀ ℕ) = max #α ℵ₀ := by simp
                                                                               -- 🎉 no goals
#align cardinal.mk_finsupp_nat Cardinal.mk_finsupp_nat

@[simp]
theorem mk_multiset_of_nonempty (α : Type u) [Nonempty α] : #(Multiset α) = max #α ℵ₀ :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)
#align cardinal.mk_multiset_of_nonempty Cardinal.mk_multiset_of_nonempty

theorem mk_multiset_of_infinite (α : Type u) [Infinite α] : #(Multiset α) = #α := by simp
                                                                                     -- 🎉 no goals
#align cardinal.mk_multiset_of_infinite Cardinal.mk_multiset_of_infinite

@[simp]
theorem mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : #(Multiset α) = 1 :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)
                                                   -- 🎉 no goals
#align cardinal.mk_multiset_of_is_empty Cardinal.mk_multiset_of_isEmpty

theorem mk_multiset_of_countable (α : Type u) [Countable α] [Nonempty α] : #(Multiset α) = ℵ₀ :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)
                                                   -- 🎉 no goals
#align cardinal.mk_multiset_of_countable Cardinal.mk_multiset_of_countable

theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ #α ^ c := by
  refine' le_trans _ (by rw [← add_one_eq (aleph0_le_mk α)])
  -- ⊢ #{ t // #↑t ≤ c } ≤ (#α + 1) ^ c
  induction' c using Cardinal.inductionOn with β
  -- ⊢ #{ t // #↑t ≤ #β } ≤ (#α + 1) ^ #β
  fapply mk_le_of_surjective
  -- ⊢ (fun α β => β → α) (α ⊕ ULift (Fin 1)) β → { t // #↑t ≤ #β }
  · intro f
    -- ⊢ { t // #↑t ≤ #β }
    use Sum.inl ⁻¹' range f
    -- ⊢ #↑(Sum.inl ⁻¹' range f) ≤ #β
    refine' le_trans (mk_preimage_of_injective _ _ fun x y => Sum.inl.inj) _
    -- ⊢ #↑(range f) ≤ #β
    apply mk_range_le
    -- 🎉 no goals
  rintro ⟨s, ⟨g⟩⟩
  -- ⊢ ∃ a, (fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹' …
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.choose h).val
               else Sum.inr (ULift.up 0)
  apply Subtype.eq; ext x
  -- ⊢ ↑((fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹' ra …
                    -- ⊢ x ∈ ↑((fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹ …
  constructor
  -- ⊢ x ∈ ↑((fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹ …
  · rintro ⟨y, h⟩
    -- ⊢ x ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
    dsimp only at h
    -- ⊢ x ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
    by_cases h' : ∃ z : s, g z = y
    -- ⊢ x ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
    · rw [dif_pos h'] at h
      -- ⊢ x ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
      cases Sum.inl.inj h
      -- ⊢ ↑(choose h') ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
      exact (Classical.choose h').2
      -- 🎉 no goals
    · rw [dif_neg h'] at h
      -- ⊢ x ∈ ↑{ val := s, property := (_ : Nonempty (↑s ↪ β)) }
      cases h
      -- 🎉 no goals
  · intro h
    -- ⊢ x ∈ ↑((fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹ …
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    -- ⊢ x ∈ ↑((fun f => { val := Sum.inl ⁻¹' range f, property := (_ : #↑(Sum.inl ⁻¹ …
    use g ⟨x, h⟩
    -- ⊢ (fun y => if h : ∃ x, ↑g x = y then Sum.inl ↑(choose h) else Sum.inr { down  …
    dsimp only
    -- ⊢ (if h_1 : ∃ x_1, ↑g x_1 = ↑g { val := x, property := h } then Sum.inl ↑(choo …
    rw [dif_pos this]
    -- ⊢ Sum.inl ↑(choose this) = Sum.inl x
    congr
    -- ⊢ ↑(choose this) = x
    suffices : Classical.choose this = ⟨x, h⟩
    -- ⊢ ↑(choose this✝) = x
    exact congr_arg Subtype.val this
    -- ⊢ choose this = { val := x, property := h }
    apply g.2
    -- ⊢ Embedding.toFun g (choose this) = Embedding.toFun g { val := x, property :=  …
    exact Classical.choose_spec this
    -- 🎉 no goals
#align cardinal.mk_bounded_set_le_of_infinite Cardinal.mk_bounded_set_le_of_infinite

theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ max #α ℵ₀ ^ c := by
  trans #{ t : Set (Sum (ULift.{u} ℕ) α) // #t ≤ c }
  -- ⊢ #{ t // #↑t ≤ c } ≤ #{ t // #↑t ≤ c }
  · refine' ⟨Embedding.subtypeMap _ _⟩
    -- ⊢ Set α ↪ Set (ULift ℕ ⊕ α)
    apply Embedding.image
    -- ⊢ α ↪ ULift ℕ ⊕ α
    use Sum.inr
    -- ⊢ Injective Sum.inr
    apply Sum.inr.inj
    -- ⊢ ∀ ⦃x : Set α⦄, #↑x ≤ c → #↑(↑(Embedding.image { toFun := Sum.inr, inj' := (_ …
    intro s hs
    -- ⊢ #↑(↑(Embedding.image { toFun := Sum.inr, inj' := (_ : ∀ {val val_1 : α}, Sum …
    exact mk_image_le.trans hs
    -- 🎉 no goals
  apply (mk_bounded_set_le_of_infinite (Sum (ULift.{u} ℕ) α) c).trans
  -- ⊢ #(ULift ℕ ⊕ α) ^ c ≤ max #α ℵ₀ ^ c
  rw [max_comm, ← add_eq_max] <;> rfl
  -- ⊢ #(ULift ℕ ⊕ α) ^ c ≤ (ℵ₀ + #α) ^ c
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align cardinal.mk_bounded_set_le Cardinal.mk_bounded_set_le

theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    #{ t : Set α // t ⊆ s ∧ #t ≤ c } ≤ max #s ℵ₀ ^ c := by
  refine' le_trans _ (mk_bounded_set_le s c)
  -- ⊢ #{ t // t ⊆ s ∧ #↑t ≤ c } ≤ #{ t // #↑t ≤ c }
  refine' ⟨Embedding.codRestrict _ _ _⟩
  -- ⊢ { t // t ⊆ s ∧ #↑t ≤ c } ↪ Set ↑s
  use fun t => (↑) ⁻¹' t.1
  -- ⊢ Injective fun t => Subtype.val ⁻¹' ↑t
  · rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    -- ⊢ { val := t, property := (_ : t ⊆ s ∧ #↑t ≤ c) } = { val := t', property := ( …
    apply Subtype.eq
    -- ⊢ ↑{ val := t, property := (_ : t ⊆ s ∧ #↑t ≤ c) } = ↑{ val := t', property := …
    dsimp only at h ⊢
    -- ⊢ t = t'
    refine' (preimage_eq_preimage' _ _).1 h <;> rw [Subtype.range_coe] <;> assumption
    -- ⊢ t ⊆ range Subtype.val
                                                -- ⊢ t ⊆ s
                                                -- ⊢ t' ⊆ s
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
  rintro ⟨t, _, h2t⟩; exact (mk_preimage_of_injective _ _ Subtype.val_injective).trans h2t
  -- ⊢ ↑{ toFun := fun t => Subtype.val ⁻¹' ↑t, inj' := (_ : ∀ ⦃a₁ a₂ : { t // t ⊆  …
                      -- 🎉 no goals
#align cardinal.mk_bounded_subset_le Cardinal.mk_bounded_subset_le

/-! ### Properties of `compl` -/


theorem mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
    #(sᶜ : Set α) = #α := by
  refine' eq_of_add_eq_of_aleph0_le _ h2 (aleph0_le_mk α)
  -- ⊢ #↑s + #↑sᶜ = #α
  exact mk_sum_compl s
  -- 🎉 no goals
#align cardinal.mk_compl_of_infinite Cardinal.mk_compl_of_infinite

theorem mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) :
    #((↑s)ᶜ : Set α) = #α := by
  apply mk_compl_of_infinite
  -- ⊢ #↑↑s < #α
  exact (finset_card_lt_aleph0 s).trans_le (aleph0_le_mk α)
  -- 🎉 no goals
#align cardinal.mk_compl_finset_of_infinite Cardinal.mk_compl_finset_of_infinite

theorem mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs : #s < #α)
    (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]
  -- 🎉 no goals
#align cardinal.mk_compl_eq_mk_compl_infinite Cardinal.mk_compl_eq_mk_compl_infinite

theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : (lift.{max v w, u} #α) = (lift.{max u w, v} #β))
    (h2 : lift.{max v w, u} #s = lift.{max u w, v} #t) :
    lift.{max v w} #(sᶜ : Set α) = lift.{max u w} #(tᶜ : Set β) := by
  cases nonempty_fintype α
  -- ⊢ lift.{max v w, u} #↑sᶜ = lift.{max u w, v} #↑tᶜ
  rcases lift_mk_eq.{u, v, w}.1 h1 with ⟨e⟩; letI : Fintype β := Fintype.ofEquiv α e
  -- ⊢ lift.{max v w, u} #↑sᶜ = lift.{max u w, v} #↑tᶜ
                                             -- ⊢ lift.{max v w, u} #↑sᶜ = lift.{max u w, v} #↑tᶜ
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.ofEquiv_card _).symm
  -- ⊢ lift.{max v w, u} #↑sᶜ = lift.{max u w, v} #↑tᶜ
  classical
    lift s to Finset α using s.toFinite
    lift t to Finset β using t.toFinite
    simp only [Finset.coe_sort_coe, mk_fintype, Fintype.card_coe, lift_natCast, Nat.cast_inj] at h2
    simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_coe_finset, Finset.card_compl,
      lift_natCast, Nat.cast_inj, h1, h2]
#align cardinal.mk_compl_eq_mk_compl_finite_lift Cardinal.mk_compl_eq_mk_compl_finite_lift

theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β) := by
  rw [← lift_inj.{u, max u v}]
  -- ⊢ lift.{max u v, u} #↑sᶜ = lift.{max u v, u} #↑tᶜ
  apply mk_compl_eq_mk_compl_finite_lift.{u, u, max u v}
  -- ⊢ lift.{max u v, u} #α = lift.{max u v, u} #β
  <;> rwa [lift_inj]
      -- 🎉 no goals
      -- 🎉 no goals
#align cardinal.mk_compl_eq_mk_compl_finite Cardinal.mk_compl_eq_mk_compl_finite

theorem mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h : #s = #t) :
    #(sᶜ : Set α) = #(tᶜ : Set α) :=
  mk_compl_eq_mk_compl_finite.{u, u} rfl h
#align cardinal.mk_compl_eq_mk_compl_finite_same Cardinal.mk_compl_eq_mk_compl_finite_same

/-! ### Extending an injection to an equiv -/


theorem extend_function {α β : Type*} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  intros; have := h; cases' this with g
  -- ⊢ ∃ g, ∀ (x : ↑s), ↑g ↑x = ↑f x
          -- ⊢ ∃ g, ∀ (x : ↑s), ↑g ↑x = ↑f x
                     -- ⊢ ∃ g, ∀ (x : ↑s), ↑g ↑x = ↑f x
  let h : α ≃ β :=
    (Set.sumCompl (s : Set α)).symm.trans
      ((sumCongr (Equiv.ofInjective f f.2) g).trans (Set.sumCompl (range f)))
  refine' ⟨h, _⟩; rintro ⟨x, hx⟩; simp [Set.sumCompl_symm_apply_of_mem, hx]
  -- ⊢ ∀ (x : ↑s), ↑h ↑x = ↑f x
                  -- ⊢ ↑h ↑{ val := x, property := hx } = ↑f { val := x, property := hx }
                                  -- 🎉 no goals
#align cardinal.extend_function Cardinal.extend_function

theorem extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  apply extend_function.{v, u} f
  -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
  cases' id h with g
  -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
  rw [← lift_mk_eq.{u, v, max u v}] at h
  -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
  rw [← lift_mk_eq.{u, v, max u v}, mk_compl_eq_mk_compl_finite_lift.{u, v, max u v} h]
  -- ⊢ lift.{max u v, u} #↑s = lift.{max u v, v} #↑(range ↑f)
  rw [mk_range_eq_lift.{u, v, max u v}]; exact f.2
  -- ⊢ Injective ↑f
                                         -- 🎉 no goals
#align cardinal.extend_function_finite Cardinal.extend_function_finite

theorem extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  cases fintypeOrInfinite α
  -- ⊢ ∃ g, ∀ (x : ↑s), ↑g ↑x = ↑f x
  · exact extend_function_finite f h
    -- 🎉 no goals
  · apply extend_function f
    -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
    cases' id h with g
    -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
    haveI := Infinite.of_injective _ g.injective
    -- ⊢ Nonempty (↑sᶜ ≃ ↑(range ↑f)ᶜ)
    rw [← lift_mk_eq'] at h ⊢
    -- ⊢ lift.{u_2, u_1} #↑sᶜ = lift.{u_1, u_2} #↑(range ↑f)ᶜ
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    -- ⊢ #↑(range ↑f) < #β
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]
    -- 🎉 no goals
#align cardinal.extend_function_of_lt Cardinal.extend_function_of_lt


--Porting note: we no longer express literals as `bit0` and `bit1` in Lean 4, so we can't use this
-- section Bit

-- /-!
-- This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
-- for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
-- `simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
-- is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
-- enough for practical situations, though.

-- For specific numbers, these inequalities could also be deduced from the corresponding
-- inequalities of natural numbers using `norm_cast`:
-- ```
-- example : (37 : cardinal) < 42 :=
-- by { norm_cast, norm_num }
-- ```
-- -/


-- theorem bit0_ne_zero (a : Cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 := by simp [bit0]
-- #align cardinal.bit0_ne_zero Cardinal.bit0_ne_zero

-- @[simp]
-- theorem bit1_ne_zero (a : Cardinal) : ¬bit1 a = 0 := by simp [bit1]
-- #align cardinal.bit1_ne_zero Cardinal.bit1_ne_zero

-- @[simp]
-- theorem zero_lt_bit0 (a : Cardinal) : 0 < bit0 a ↔ 0 < a := by
--   rw [← not_iff_not]
--   simp [bit0]
-- #align cardinal.zero_lt_bit0 Cardinal.zero_lt_bit0

-- @[simp]
-- theorem zero_lt_bit1 (a : Cardinal) : 0 < bit1 a :=
--   zero_lt_one.trans_le (self_le_add_left _ _)
-- #align cardinal.zero_lt_bit1 Cardinal.zero_lt_bit1

-- @[simp]
-- theorem one_le_bit0 (a : Cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
--   ⟨fun h => (zero_lt_bit0 a).mp (zero_lt_one.trans_le h), fun h =>
--     (one_le_iff_pos.mpr h).trans (self_le_add_left a a)⟩
-- #align cardinal.one_le_bit0 Cardinal.one_le_bit0

-- @[simp]
-- theorem one_le_bit1 (a : Cardinal) : 1 ≤ bit1 a :=
--   self_le_add_left _ _
-- #align cardinal.one_le_bit1 Cardinal.one_le_bit1

-- theorem bit0_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : bit0 c = c :=
--   add_eq_self h
-- #align cardinal.bit0_eq_self Cardinal.bit0_eq_self

-- @[simp]
-- theorem bit0_lt_aleph0 {c : Cardinal} : bit0 c < ℵ₀ ↔ c < ℵ₀ :=
--   by simp [bit0, add_lt_aleph_0_iff]
-- #align cardinal.bit0_lt_aleph_0 Cardinal.bit0_lt_aleph0

-- @[simp]
-- theorem aleph0_le_bit0 {c : Cardinal} : ℵ₀ ≤ bit0 c ↔ ℵ₀ ≤ c := by
--   rw [← not_iff_not]
--   simp
-- #align cardinal.aleph_0_le_bit0 Cardinal.aleph0_le_bit0

-- @[simp]
-- theorem bit1_eq_self_iff {c : Cardinal} : bit1 c = c ↔ ℵ₀ ≤ c := by
--   by_cases h : ℵ₀ ≤ c
--   · simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_aleph_0_le]
--   · refine' iff_of_false (ne_of_gt _) h
--     rcases lt_aleph_0.1 (not_le.1 h) with ⟨n, rfl⟩
--     norm_cast
--     dsimp [bit1, bit0]
--     linarith
-- #align cardinal.bit1_eq_self_iff Cardinal.bit1_eq_self_iff

-- @[simp]
-- theorem bit1_lt_aleph0 {c : Cardinal} : bit1 c < ℵ₀ ↔ c < ℵ₀ := by
--   simp [bit1, bit0, add_lt_aleph_0_iff, one_lt_aleph_0]
-- #align cardinal.bit1_lt_aleph_0 Cardinal.bit1_lt_aleph0

-- @[simp]
-- theorem aleph0_le_bit1 {c : Cardinal} : ℵ₀ ≤ bit1 c ↔ ℵ₀ ≤ c := by
--   rw [← not_iff_not]
--   simp
-- #align cardinal.aleph_0_le_bit1 Cardinal.aleph0_le_bit1

-- @[simp]
-- theorem bit0_le_bit0 {a b : Cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · rw [bit0_eq_self ha, bit0_eq_self hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit0_le_bit0
-- #align cardinal.bit0_le_bit0 Cardinal.bit0_le_bit0

-- @[simp]
-- theorem bit0_le_bit1 {a b : Cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
--     have A : bit1 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact Nat.bit0_le_bit1_iff
-- #align cardinal.bit0_le_bit1 Cardinal.bit0_le_bit1

-- @[simp]
-- theorem bit1_le_bit1 {a b : Cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
--   ⟨fun h => bit0_le_bit1.1 ((self_le_add_right (bit0 a) 1).trans h), fun h =>
--     (add_le_add_right (add_le_add_left h a) 1).trans (add_le_add_right (add_le_add_right h b) 1)⟩
-- #align cardinal.bit1_le_bit1 Cardinal.bit1_le_bit1

-- @[simp]
-- theorem bit1_le_bit0 {a b : Cardinal} : bit1 a ≤ bit0 b ↔ a < b ∨ a ≤ b ∧ ℵ₀ ≤ a := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_true_iff]
--     refine' ⟨fun h => Or.inr h, fun h => _⟩
--     cases h
--     · exact le_of_lt h
--     · exact h
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) fun h => _
--     · have A : bit0 b < ℵ₀ := by simpa using hb
--       exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--     · exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt And.left)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).le.trans hb) (Or.inl <| ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     simp [not_le.mpr ha]
-- #align cardinal.bit1_le_bit0 Cardinal.bit1_le_bit0

-- @[simp]
-- theorem bit0_lt_bit0 {a b : Cardinal} : bit0 a < bit0 b ↔ a < b := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · rw [bit0_eq_self ha, bit0_eq_self hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit0_lt_bit0
-- #align cardinal.bit0_lt_bit0 Cardinal.bit0_lt_bit0

-- @[simp]
-- theorem bit1_lt_bit0 {a b : Cardinal} : bit1 a < bit0 b ↔ a < b := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb]
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact Nat.bit1_lt_bit0_iff
-- #align cardinal.bit1_lt_bit0 Cardinal.bit1_lt_bit0

-- @[simp]
-- theorem bit1_lt_bit1 {a b : Cardinal} : bit1 a < bit1 b ↔ a < b := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb]
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit1 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit1_lt_bit1
-- #align cardinal.bit1_lt_bit1 Cardinal.bit1_lt_bit1

-- @[simp]
-- theorem bit0_lt_bit1 {a b : Cardinal} : bit0 a < bit1 b ↔ a < b ∨ a ≤ b ∧ a < ℵ₀ := by
--   cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
--   · simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) fun h => _
--     · have A : bit1 b < ℵ₀ := by simpa using hb
--       exact lt_irrefl _ ((A.trans_le ha).trans h)
--     · exact (hb.trans_le ha).not_le (h.elim le_of_lt And.left)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (Or.inl <| ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     simp only [ha, and_true_iff, Nat.bit0_lt_bit1_iff, or_iff_right_of_imp le_of_lt]
-- #align cardinal.bit0_lt_bit1 Cardinal.bit0_lt_bit1

-- theorem one_lt_two : (1 : Cardinal) < 2 := by
--   -- This strategy works generally to prove inequalities between numerals in `cardinality`.
--   norm_cast
--   norm_num
-- #align cardinal.one_lt_two Cardinal.one_lt_two

-- @[simp]
-- theorem one_lt_bit0 {a : Cardinal} : 1 < bit0 a ↔ 0 < a := by simp [← bit1_zero]
-- #align cardinal.one_lt_bit0 Cardinal.one_lt_bit0

-- @[simp]
-- theorem one_lt_bit1 (a : Cardinal) : 1 < bit1 a ↔ 0 < a := by simp [← bit1_zero]
-- #align cardinal.one_lt_bit1 Cardinal.one_lt_bit1

-- end Bit

end Cardinal
