/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.SetTheory.Ordinal.Enum

/-!
# Omega, aleph, and beth functions

This file defines the `ω`, `ℵ`, and `ℶ` functions which enumerate certain kinds of ordinals and
cardinals. Each is provided in two variants: the standard versions which only take infinite values,
and "preliminary" versions which include finite values and are sometimes more convenient.

* The function `Ordinal.preOmega` enumerates the initial ordinals, i.e. the smallest ordinals with
  any given cardinality. Thus `preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.preAleph` is an order isomorphism between ordinals and cardinals. Thus
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more
  standard function which skips over finite cardinals.
* The function `Cardinal.preBeth` is the unique normal function with `beth 0 = 0` and
  `beth (succ o) = 2 ^ beth o`. `Cardinal.beth` is the more standard function which skips over
  finite cardinals.

## Notation

The following notations are scoped to the `Ordinal` namespace.

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`.

The following notations are scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib/SetTheory/Cardinal/Continuum.lean`.
-/

assert_not_exists Field Finsupp Module Cardinal.mul_eq_self

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

@[simp]
theorem isInitial_natCast (n : ℕ) : IsInitial n := by
  rw [IsInitial, card_nat, ord_nat]

theorem isInitial_zero : IsInitial 0 := by
  exact_mod_cast isInitial_natCast 0

theorem isInitial_one : IsInitial 1 := by
  exact_mod_cast isInitial_natCast 1

theorem isInitial_omega0 : IsInitial ω := by
  rw [IsInitial, card_omega0, ord_aleph0]

theorem isInitial_succ {o : Ordinal} : IsInitial (succ o) ↔ o < ω :=
  ⟨Function.mtr fun hwo ↦ ne_of_lt <| by simp_all [ord_card_le],
  fun how ↦ (Ordinal.lt_omega0.1 how).rec fun n h ↦ h ▸ isInitial_natCast (n + 1)⟩

theorem not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x} := by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_ge this

/-- Initial ordinals are order-isomorphic to the cardinals. -/
@[simps!]
def isInitialIso : {x // IsInitial x} ≃o Cardinal where
  toFun x := x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card

/-- The "pre-omega" function gives the initial ordinals listed by their ordinal index.
`preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.

For the more common omega function skipping over finite ordinals, see `Ordinal.omega`. -/
def preOmega : Ordinal.{u} ↪o Ordinal.{u} where
  toFun := enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial

theorem coe_preOmega : preOmega = enumOrd {x | IsInitial x} :=
  rfl

theorem preOmega_strictMono : StrictMono preOmega :=
  preOmega.strictMono

theorem preOmega_lt_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ < preOmega o₂ ↔ o₁ < o₂ :=
  preOmega.lt_iff_lt

theorem preOmega_le_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ ≤ preOmega o₂ ↔ o₁ ≤ o₂ :=
  preOmega.le_iff_le

theorem preOmega_max (o₁ o₂ : Ordinal) : preOmega (max o₁ o₂) = max (preOmega o₁) (preOmega o₂) :=
  preOmega.monotone.map_max

theorem isInitial_preOmega (o : Ordinal) : IsInitial (preOmega o) :=
  enumOrd_mem not_bddAbove_isInitial o

theorem le_preOmega_self (o : Ordinal) : o ≤ preOmega o :=
  preOmega_strictMono.le_apply

@[simp]
theorem preOmega_zero : preOmega 0 = 0 := by
  rw [coe_preOmega, enumOrd_zero]
  exact csInf_eq_bot_of_bot_mem isInitial_zero

@[simp]
theorem preOmega_natCast (n : ℕ) : preOmega n = n := by
  induction n with
  | zero => exact preOmega_zero
  | succ n IH =>
    apply (le_preOmega_self _).antisymm'
    apply enumOrd_succ_le not_bddAbove_isInitial (isInitial_natCast _) (IH.trans_lt _)
    rw [Nat.cast_lt]
    exact lt_succ n

@[simp]
theorem preOmega_ofNat (n : ℕ) [n.AtLeastTwo] : preOmega ofNat(n) = n :=
  preOmega_natCast n

theorem preOmega_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : ∀ b < o, preOmega b < a) :
    preOmega o ≤ a :=
  enumOrd_le_of_forall_lt ha H

theorem isNormal_preOmega : IsNormal preOmega := by
  rw [isNormal_iff_strictMono_limit]
  refine ⟨preOmega_strictMono, fun o ho a ha ↦
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb ↦ ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card, card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card, preOmega_lt_preOmega]
  exact lt_succ b

@[simp]
theorem range_preOmega : range preOmega = {x | IsInitial x} :=
  range_enumOrd not_bddAbove_isInitial

theorem mem_range_preOmega_iff {x : Ordinal} : x ∈ range preOmega ↔ IsInitial x := by
  rw [range_preOmega, mem_setOf]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]
theorem preOmega_omega0 : preOmega ω = ω := by
  simp_rw [← isNormal_preOmega.apply_omega0, preOmega_natCast, iSup_natCast]

@[simp]
theorem omega0_le_preOmega_iff {x : Ordinal} : ω ≤ preOmega x ↔ ω ≤ x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[simp]
theorem omega0_lt_preOmega_iff {x : Ordinal} : ω < preOmega x ↔ ω < x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_lt_preOmega]

/-- The `omega` function gives the infinite initial ordinals listed by their ordinal index.
`omega 0 = ω`, `omega 1 = ω₁` is the first uncountable ordinal, and so on.

This is not to be confused with the first infinite ordinal `Ordinal.omega0`.

For a version including finite ordinals, see `Ordinal.preOmega`. -/
def omega : Ordinal ↪o Ordinal :=
  (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc]
scoped notation "ω_ " => omega

/-- `ω₁` is the first uncountable ordinal. -/
scoped notation "ω₁" => ω_ 1

theorem omega_eq_preOmega (o : Ordinal) : ω_ o = preOmega (ω + o) :=
  rfl

theorem omega_strictMono : StrictMono omega :=
  omega.strictMono

theorem omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂ :=
  omega.lt_iff_lt

theorem omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ ≤ ω_ o₂ ↔ o₁ ≤ o₂ :=
  omega.le_iff_le

theorem omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂) :=
  omega.monotone.map_max

theorem preOmega_le_omega (o : Ordinal) : preOmega o ≤ ω_ o :=
  preOmega_le_preOmega.2 (Ordinal.le_add_left _ _)

theorem isInitial_omega (o : Ordinal) : IsInitial (omega o) :=
  isInitial_preOmega _

theorem le_omega_self (o : Ordinal) : o ≤ omega o :=
  omega_strictMono.le_apply

@[simp]
theorem omega_zero : ω_ 0 = ω := by
  rw [omega_eq_preOmega, add_zero, preOmega_omega0]

theorem omega0_le_omega (o : Ordinal) : ω ≤ ω_ o := by
  rw [← omega_zero, omega_le_omega]
  exact Ordinal.zero_le o

/-- For the theorem `0 < ω`, see `omega0_pos`. -/
theorem omega_pos (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

theorem omega0_lt_omega1 : ω < ω₁ := by
  rw [← omega_zero, omega_lt_omega]
  exact zero_lt_one

theorem isNormal_omega : IsNormal omega :=
  isNormal_preOmega.trans (isNormal_add_right _)

@[simp]
theorem range_omega : range omega = {x | ω ≤ x ∧ IsInitial x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega, Ordinal.add_sub_cancel_of_le ha']

theorem mem_range_omega_iff {x : Ordinal} : x ∈ range omega ↔ ω ≤ x ∧ IsInitial x := by
  rw [range_omega, mem_setOf]

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/-- The "pre-aleph" function gives the cardinals listed by their ordinal index. `preAleph n = n`,
`preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
def preAleph : Ordinal.{u} ≃o Cardinal.{u} :=
  (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[simp]
theorem _root_.Ordinal.card_preOmega (o : Ordinal) : (preOmega o).card = preAleph o :=
  rfl

@[simp]
theorem ord_preAleph (o : Ordinal) : (preAleph o).ord = preOmega o := by
  rw [← o.card_preOmega, (isInitial_preOmega o).ord_card]

@[simp]
theorem type_cardinal : typeLT Cardinal = Ordinal.univ.{u, u + 1} := by
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
theorem preAleph_nat (n : ℕ) : preAleph n = n := by
  rw [← card_preOmega, preOmega_natCast, card_nat]

@[simp]
theorem preAleph_omega0 : preAleph ω = ℵ₀ := by
  rw [← card_preOmega, preOmega_omega0, card_omega0]

@[simp]
theorem preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o := by
  rw [← preAleph_zero, preAleph_lt_preAleph]

@[simp]
theorem aleph0_le_preAleph {o : Ordinal} : ℵ₀ ≤ preAleph o ↔ ω ≤ o := by
  rw [← preAleph_omega0, preAleph_le_preAleph]

@[simp]
theorem lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o) :=
  (preAleph.toInitialSeg.trans liftInitialSeg).eq
    (Ordinal.liftInitialSeg.trans preAleph.toInitialSeg) o

@[simp]
theorem _root_.Ordinal.lift_preOmega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (preOmega o) = preOmega (Ordinal.lift.{v} o) := by
  rw [← ord_preAleph, lift_ord, lift_preAleph, ord_preAleph]

theorem isNormal_preAleph : Order.IsNormal preAleph :=
  OrderIso.isNormal _

theorem preAleph_le_of_isSuccPrelimit {o : Ordinal} (l : IsSuccPrelimit o) {c} :
    preAleph o ≤ c ↔ ∀ o' < o, preAleph o' ≤ c := by
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.le_iff_forall_le ⟨by simpa, l⟩

@[deprecated (since := "2025-07-08")]
alias preAleph_le_of_isLimit := preAleph_le_of_isSuccPrelimit

theorem preAleph_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preAleph o = ⨆ a : Iio o, preAleph a := by
  obtain rfl | h := eq_or_ne o 0
  · simp
  · exact isNormal_preAleph.apply_of_isSuccLimit ⟨by simpa, ho⟩

theorem preAleph_le_of_strictMono {f : Ordinal → Cardinal} (hf : StrictMono f) (o : Ordinal) :
    preAleph o ≤ f o := by
  simpa using (hf.comp preAleph.symm.strictMono).id_le (preAleph o)

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.preAleph`. -/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans preAleph.toOrderEmbedding

@[inherit_doc]
scoped notation "ℵ_ " => aleph

/-- `ℵ₁` is the first uncountable cardinal. -/
scoped notation "ℵ₁" => ℵ_ 1

theorem aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o) :=
  rfl

@[simp]
theorem _root_.Ordinal.card_omega (o : Ordinal) : (ω_ o).card = ℵ_ o :=
  rfl

@[simp]
theorem ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o :=
  ord_preAleph _

theorem aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt

theorem aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ ≤ ℵ_ o₂ ↔ o₁ ≤ o₂ :=
  aleph.le_iff_le

theorem aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂) :=
  aleph.monotone.map_max

theorem preAleph_le_aleph (o : Ordinal) : preAleph o ≤ ℵ_ o :=
  preAleph_le_preAleph.2 (Ordinal.le_add_left _ _)

@[simp]
theorem aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o) := by
  rw [aleph_eq_preAleph, add_succ, preAleph_succ, aleph_eq_preAleph]

@[simp]
theorem aleph_zero : ℵ_ 0 = ℵ₀ := by rw [aleph_eq_preAleph, add_zero, preAleph_omega0]

@[simp]
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  simp [aleph_eq_preAleph]

/-- For the theorem `lift ω = ω`, see `lift_omega0`. -/
@[simp]
theorem _root_.Ordinal.lift_omega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (ω_ o) = ω_ (Ordinal.lift.{v} o) := by
  simp [omega_eq_preOmega]

theorem isNormal_aleph : Order.IsNormal aleph :=
  isNormal_preAleph.comp (isNormal_add_right _)

theorem aleph_limit {o : Ordinal} (ho : IsSuccLimit o) : ℵ_ o = ⨆ a : Iio o, ℵ_ a :=
  isNormal_aleph.apply_of_isSuccLimit ho

theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ ℵ_ o := by
  rw [aleph_eq_preAleph, aleph0_le_preAleph]
  apply Ordinal.le_add_right

theorem aleph_pos (o : Ordinal) : 0 < ℵ_ o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

@[simp]
theorem aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o

@[simp]
theorem aleph_toENat (o : Ordinal) : toENat (ℵ_ o) = ⊤ :=
  (toENat_eq_top.2 (aleph0_le_aleph o))

theorem isSuccLimit_omega (o : Ordinal) : IsSuccLimit (ω_ o) := by
  rw [← ord_aleph]
  exact isSuccLimit_ord (aleph0_le_aleph _)

@[deprecated (since := "2025-07-08")]
alias isLimit_omega := isSuccLimit_omega

@[simp]
theorem range_aleph : range aleph = Set.Ici ℵ₀ := by
  ext c
  refine ⟨fun ⟨o, e⟩ => e ▸ aleph0_le_aleph _, fun hc ↦ ⟨preAleph.symm c - ω, ?_⟩⟩
  rw [aleph_eq_preAleph, Ordinal.add_sub_cancel_of_le, preAleph.apply_symm_apply]
  rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]

theorem mem_range_aleph_iff {c : Cardinal} : c ∈ range aleph ↔ ℵ₀ ≤ c := by
  rw [range_aleph, mem_Ici]

@[simp]
theorem succ_aleph0 : succ ℵ₀ = ℵ₁ := by
  rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]

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

theorem lt_omega_iff_card_lt {x o : Ordinal} : x < ω_ o ↔ x.card < ℵ_ o := by
  rw [← (isInitial_omega o).card_lt_card, card_omega]

/-! ### Beth cardinals -/

/-- The "pre-beth" function is defined so that `preBeth o` is the supremum of `2 ^ preBeth a` for
`a < o`. This implies `beth 0 = 0`, `beth (succ o) = 2 ^ beth o`, and that for a limit ordinal `o`,
`beth o` is the supremum of `beth a` for `a < o`.

For the usual function starting at `ℵ₀`, see `Cardinal.beth`. -/
def preBeth (o : Ordinal.{u}) : Cardinal.{u} :=
  ⨆ a : Iio o, 2 ^ preBeth a
termination_by o
decreasing_by exact a.2

theorem preBeth_strictMono : StrictMono preBeth := by
  intro a b h
  conv_rhs => rw [preBeth]
  rw [lt_ciSup_iff' (bddAbove_of_small _)]
  exact ⟨⟨a, h⟩, cantor _⟩

theorem preBeth_mono : Monotone preBeth :=
  preBeth_strictMono.monotone

theorem preAleph_le_preBeth (o : Ordinal) : preAleph o ≤ preBeth o :=
  preAleph_le_of_strictMono preBeth_strictMono o

@[simp]
theorem preBeth_lt_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ < preBeth o₂ ↔ o₁ < o₂ :=
  preBeth_strictMono.lt_iff_lt

@[simp]
theorem preBeth_le_preBeth {o₁ o₂ : Ordinal} : preBeth o₁ ≤ preBeth o₂ ↔ o₁ ≤ o₂ :=
  preBeth_strictMono.le_iff_le

@[simp]
theorem preBeth_inj {o₁ o₂ : Ordinal} : preBeth o₁ = preBeth o₂ ↔ o₁ = o₂ :=
  preBeth_strictMono.injective.eq_iff

@[simp]
theorem preBeth_zero : preBeth 0 = 0 := by
  rw [preBeth]
  simp

@[simp]
theorem preBeth_succ (o : Ordinal) : preBeth (succ o) = 2 ^ preBeth o := by
  rw [preBeth, Iio_succ]
  exact ciSup_Iic o fun x y h ↦ power_le_power_left two_ne_zero (preBeth_mono h)

theorem preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit o) :
    preBeth o = ⨆ a : Iio o, preBeth a := by
  rw [preBeth]
  apply (ciSup_mono (bddAbove_of_small _) fun _ ↦ (cantor _).le).antisymm'
  rw [ciSup_le_iff' (bddAbove_of_small _)]
  intro a
  rw [← preBeth_succ]
  exact le_ciSup (bddAbove_of_small _) (⟨_, ho.succ_lt a.2⟩ : Iio o)

theorem isNormal_preBeth : Order.IsNormal preBeth := by
  rw [isNormal_iff]
  refine ⟨preBeth_strictMono, fun o ho ↦ ?_⟩
  simp [preBeth_limit ho.isSuccPrelimit, ciSup_le_iff' (bddAbove_of_small _)]

theorem preBeth_nat : ∀ n : ℕ, preBeth n = (2 ^ ·)^[n] (0 : ℕ)
  | 0 => by simp
  | n + 1 => by
    rw [natCast_succ, preBeth_succ, Function.iterate_succ_apply', preBeth_nat]
    simp

@[simp]
theorem preBeth_one : preBeth 1 = 1 := by
  simpa using preBeth_nat 1

@[simp]
theorem preBeth_omega : preBeth ω = ℵ₀ := by
  apply le_antisymm
  · rw [preBeth_limit isSuccLimit_omega0.isSuccPrelimit, ciSup_le_iff' (bddAbove_of_small _)]
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [preBeth_nat]
    exact (nat_lt_aleph0 _).le
  · simpa using preAleph_le_preBeth ω

@[simp]
theorem preBeth_pos {o : Ordinal} : 0 < preBeth o ↔ 0 < o := by
  simpa using preBeth_lt_preBeth (o₁ := 0)

@[simp]
theorem preBeth_eq_zero {o : Ordinal} : preBeth o = 0 ↔ o = 0 := by
  simpa using preBeth_inj (o₂ := 0)

theorem isStrongLimit_preBeth {o : Ordinal} : IsStrongLimit (preBeth o) ↔ IsSuccLimit o := by
  by_cases H : IsSuccLimit o
  · refine iff_of_true ⟨by simpa using H.ne_bot, fun a ha ↦ ?_⟩ H
    rw [preBeth_limit H.isSuccPrelimit] at ha
    rcases exists_lt_of_lt_ciSup' ha with ⟨⟨i, hi⟩, ha⟩
    have := power_le_power_left two_ne_zero ha.le
    rw [← preBeth_succ] at this
    exact this.trans_lt (preBeth_strictMono (H.succ_lt hi))
  · apply iff_of_false _ H
    rw [not_isSuccLimit_iff, not_isSuccPrelimit_iff'] at H
    obtain ho | ⟨a, rfl⟩ := H
    · simp [ho.eq_bot]
    · intro h
      simpa using h.two_power_lt (preBeth_strictMono (lt_succ a))

/-- The Beth function is defined so that `beth 0 = ℵ₀'`, `beth (succ o) = 2 ^ beth o`, and that for
a limit ordinal `o`, `beth o` is the supremum of `beth a` for `a < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, we have `ℶ_ o = ℵ_ o`
for all ordinals.

For a version which starts at zero, see `Cardinal.preBeth`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  preBeth (ω + o)

@[inherit_doc]
scoped notation "ℶ_ " => beth

theorem beth_eq_preBeth (o : Ordinal) : beth o = preBeth (ω + o) :=
  rfl

theorem preBeth_le_beth (o : Ordinal) : preBeth o ≤ ℶ_ o :=
  preBeth_le_preBeth.2 (Ordinal.le_add_left _ _)

theorem beth_strictMono : StrictMono beth :=
  preBeth_strictMono.comp fun _ _ h ↦ by gcongr

theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone

@[simp]
theorem beth_lt_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
theorem beth_le_beth {o₁ o₂ : Ordinal} : ℶ_ o₁ ≤ ℶ_ o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le

@[simp]
theorem beth_zero : ℶ_ 0 = ℵ₀ := by
  simp [beth]

@[simp]
theorem beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ ℶ_ o := by
  simp [beth, add_succ]

theorem isNormal_beth : Order.IsNormal beth :=
  isNormal_preBeth.comp (isNormal_add_right _)

theorem beth_limit {o : Ordinal} (ho : IsSuccLimit o) : ℶ_ o = ⨆ a : Iio o, ℶ_ a :=
  isNormal_beth.apply_of_isSuccLimit ho

theorem aleph_le_beth (o : Ordinal) : ℵ_ o ≤ ℶ_ o :=
  preAleph_le_preBeth _

theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ ℶ_ o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o

theorem beth_pos (o : Ordinal) : 0 < ℶ_ o :=
  aleph0_pos.trans_le <| aleph0_le_beth o

theorem beth_ne_zero (o : Ordinal) : ℶ_ o ≠ 0 :=
  (beth_pos o).ne'

theorem isStrongLimit_beth {o : Ordinal} : IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o := by
  rw [beth_eq_preBeth, isStrongLimit_preBeth, isSuccLimit_add_iff_of_isSuccLimit isSuccLimit_omega0]

end Cardinal
