/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Units modulo `n`-th powers

For a commutative monoid `α` and a natural number `n`, this file defines `Units.ModPow α n`,
the group `αˣ ⧸ (αˣ)ⁿ` of units of `α` modulo `n`-th powers, and provides its basic API.

For a field `K`, this is the group `Kˣ/(Kˣ)ⁿ`, which Kummer theory identifies with the Galois
cohomology group `H¹(K, μₙ)` when `K` contains the `n`-th roots of unity; it is the ambient group
of the Selmer groups `K⟮S, n⟯` of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`.

## Main definitions

* `Units.ModPow α n`: the group of units of `α` modulo `n`-th powers.
* `Units.ModPow.map`, `Units.ModPow.congr`: the homomorphism, resp. isomorphism, induced by a
  monoid homomorphism, resp. a multiplicative equivalence, `α → β`.
* `Units.ModPow.piEquiv`: the units modulo `n`-th powers of a product are the product of the
  units modulo `n`-th powers of the factors.

## Main statements

* `Units.ModPow.mk_eq_one_iff`, `Units.ModPow.mk_eq_one_iff_exists_pow_eq_val`,
  `Units.ModPow.unit_eq_one_iff`: the class of a unit is trivial if and only if the unit is an
  `n`-th power (in `αˣ`, or equivalently in `α`).
* `Units.ModPow.mk_eq_mk_iff`: two units have the same class if and only if they differ by an
  `n`-th power.
* `Units.ModPow.pow_eq_one`: `Units.ModPow α n` has exponent dividing `n`.

## Implementation notes

`Units.ModPow α n` is an abbreviation for `αˣ ⧸ (powMonoidHom n).range`, so that the
`QuotientGroup` API applies to it directly. The additive version is `AddUnits.ModNSMul α n`.
-/

@[expose] public section

/-- The group `αˣ ⧸ (αˣ)ⁿ` of units of a commutative monoid `α` modulo `n`-th powers, as the
quotient of `αˣ` by the range of `powMonoidHom n`. -/
@[to_additive /-- The group of additive units of an additive commutative monoid `α` modulo
`n`-th multiples, as the quotient of `AddUnits α` by the range of `nsmulAddMonoidHom n`. -/]
abbrev Units.ModPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

namespace Units.ModPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α} {n : ℕ}

open QuotientGroup

/-- The class of a unit `u` is trivial in `Units.ModPow α n` exactly when `u` is an `n`-th power
in `αˣ`. -/
@[to_additive /-- The class of an additive unit `u` is trivial in `AddUnits.ModNSMul α n` exactly
when `u` is an `n`-th multiple in `AddUnits α`. -/]
lemma mk_eq_one_iff {u : αˣ} : (u : ModPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by simp

/-- The class of a unit `u` is trivial in `Units.ModPow α n` exactly when `u` is an `n`-th power
in `α`. -/
@[to_additive /-- The class of an additive unit `u` is trivial in `AddUnits.ModNSMul α n` exactly
when `u` is an `n`-th multiple in `α`. -/]
lemma mk_eq_one_iff_exists_pow_eq_val {u : αˣ} : (u : ModPow α n) = 1 ↔ ∃ x : α, x ^ n = u :=
  mk_eq_one_iff.trans (by simpa using u.isUnit.exists_pow_eq_unit_iff)

@[to_additive]
lemma mk_eq_mk_iff {u v : αˣ} : (u : ModPow α n) = v ↔ ∃ w : αˣ, v = u * w ^ n := by
  simp only [QuotientGroup.eq, MonoidHom.mem_range, powMonoidHom_apply]
  exact congr(∃ _, $(eq_comm.trans _root_.inv_mul_eq_iff_eq_mul))

@[to_additive]
lemma unit_eq_one_iff (ha : IsUnit a) : (ha.unit : ModPow α n) = 1 ↔ ∃ x, x ^ n = a := by
  rw [mk_eq_one_iff_exists_pow_eq_val, IsUnit.unit_spec]

@[to_additive]
lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    (ha.unit : ModPow α n) * hb.unit * hc.unit = 1 ↔ ∃ x, x ^ n = a * b * c := by
  rw [← mk_mul, ← mk_mul, mk_eq_one_iff_exists_pow_eq_val]
  simp

-- `to_additive` does not translate the declaration correctly (`1` stays `1`).
/-- The class of a unit `u` is trivial in `Units.ModPow α 2` exactly when `u` is a square
in `α`. -/
@[to_additive /-- The class of an additive unit `u` is trivial in `AddUnits.ModNSMul α 2`
exactly when `u` is even in `α`. -/]
lemma mk_eq_one_iff_isSquare {u : αˣ} : (u : ModPow α 2) = 1 ↔ IsSquare (u : α) := by
  rw [mk_eq_one_iff_exists_pow_eq_val, isSquare_iff_exists_sq]
  exact congr(∃ _, $eq_comm)

@[to_additive (attr := simp)]
lemma pow_eq_one (m : ModPow α n) : m ^ n = 1 :=
  QuotientGroup.induction_on m fun u ↦ (mk_pow ..).symm.trans (mk_eq_one_iff.mpr ⟨u, rfl⟩)

/-- If every unit of `α` is an `n`-th power, then `Units.ModPow α n` is trivial. -/
@[to_additive /-- If every additive unit of `α` is an `n`-th multiple, then `AddUnits.ModNSMul α n`
is trivial. -/]
lemma subsingleton_of_forall_exists_pow (h : ∀ u : αˣ, ∃ w : αˣ, w ^ n = u) :
    Subsingleton (ModPow α n) :=
  ⟨fun a b ↦ QuotientGroup.induction_on a fun u ↦ QuotientGroup.induction_on b fun w ↦
    (mk_eq_one_iff.mpr (h u)).trans (mk_eq_one_iff.mpr (h w)).symm⟩

/-- A monoid homomorphism `α →* β` induces a homomorphism `Units.ModPow α n →* Units.ModPow β n`
of the groups of units modulo `n`-th powers. -/
@[to_additive /-- An additive monoid homomorphism `α →+ β` induces a homomorphism
`AddUnits.ModNSMul α n →+ AddUnits.ModNSMul β n` of the groups of additive units modulo `n`-th
multiples. -/]
def map (φ : α →* β) (n : ℕ) : ModPow α n →* ModPow β n :=
  QuotientGroup.map _ _ (Units.map φ) fun _ ⟨u, hu⟩ ↦ ⟨Units.map φ u, hu ▸ by simp⟩

@[to_additive (attr := simp)]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) : map φ n u = (Units.map φ u : ModPow β n) :=
  rfl

@[to_additive (attr := simp)]
lemma map_id (n : ℕ) : map (MonoidHom.id α) n = MonoidHom.id (ModPow α n) := by
  ext
  simp

@[to_additive]
lemma map_comp {γ : Type*} [CommMonoid γ] (ψ : β →* γ) (φ : α →* β) (n : ℕ) :
    (map ψ n).comp (map φ n) = map (ψ.comp φ) n := by
  ext
  simp

@[to_additive]
lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : ModPow α n) = ((ha.map φ).unit : ModPow β n) :=
  (map_mk ..).trans (congrArg _ (Units.ext rfl))

/-- A multiplicative equivalence `α ≃* β` induces an isomorphism
`Units.ModPow α n ≃* Units.ModPow β n` of the groups of units modulo `n`-th powers. -/
@[to_additive /-- An additive equivalence `α ≃+ β` induces an isomorphism
`AddUnits.ModNSMul α n ≃+ AddUnits.ModNSMul β n` of the groups of additive units modulo `n`-th
multiples. -/]
def congr (e : α ≃* β) (n : ℕ) : ModPow α n ≃* ModPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n

@[to_additive (attr := simp)]
lemma congr_mk (e : α ≃* β) (n : ℕ) (u : αˣ) :
    congr e n u = (Units.mapEquiv e u : ModPow β n) :=
  rfl

/-- The map on units modulo `n`-th powers induced by a bijective homomorphism is bijective. -/
@[to_additive /-- The map on additive units modulo `n`-th multiples induced by a bijective
homomorphism is bijective. -/]
lemma bijective_map {φ : α →* β} (hφ : Function.Bijective φ) (n : ℕ) :
    Function.Bijective (map φ n) :=
  have h : ⇑(map φ n) = ⇑(congr (MulEquiv.ofBijective φ hφ) n) :=
    funext fun m ↦ QuotientGroup.induction_on m fun _ ↦ rfl
  h ▸ (congr (MulEquiv.ofBijective φ hφ) n).bijective

/-- Taking units modulo `n`-th powers commutes with products. -/
@[to_additive /-- Taking additive units modulo `n`-th multiples commutes with products. -/]
noncomputable def piEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommMonoid (M i)] (n : ℕ) :
    ModPow ((i : ι) → M i) n ≃* ((i : ι) → ModPow (M i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (M i)ˣ) n

@[to_additive (attr := simp)]
lemma piEquiv_mk {ι : Type*} (M : ι → Type*) [∀ i, CommMonoid (M i)] (n : ℕ)
    (u : ((i : ι) → M i)ˣ) (i : ι) :
    piEquiv M n u i = (MulEquiv.piUnits u i : ModPow (M i) n) := by
  simp [piEquiv]

end Units.ModPow
