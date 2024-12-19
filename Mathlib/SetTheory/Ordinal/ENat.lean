/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Yury Kudryashov
-/
import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Conversion between `Ordinal` and `ℕ∞`

In this file we define a coercion `Ordinal.ofENat : ℕ∞ → Ordinal`
and a projection `Ordinal.toENat : Ordinal →*₀o ℕ∞`.
We also prove basic theorems about these definitions.

## Implementation notes

We define `Ordinal.ofENat` as a function instead of a bundled homomorphism
so that we can use it as a coercion and delaborate its application to `↑n`.

We define `Ordinal.toENat` as a bundled homomorphism
so that we can use all the theorems about homomorphisms without specializing them to this function.
Since it is not registered as a coercion, the argument about delaboration does not apply.

This file is very similar to SetTheory/Cardinal/ENat. Please keep them in sync.

## Keywords

set theory, ordinals, extended natural numbers
-/


open Function Set
universe u v

namespace Ordinal

/-- Coercion `ℕ∞ → Ordinal`. It sends natural numbers to natural numbers and `⊤` to `ω`.

See also `Ordinal.ofENatHom` for a bundled homomorphism version. -/
@[coe] def ofENat : ℕ∞ → Ordinal
  | (n : ℕ) => n
  | ⊤ => ω

instance : Coe ENat Ordinal := ⟨Ordinal.ofENat⟩

@[simp, norm_cast] lemma ofENat_top : ofENat ⊤ = ω := rfl
@[simp, norm_cast] lemma ofENat_nat (n : ℕ) : ofENat n = n := rfl
@[simp, norm_cast] lemma ofENat_zero : ofENat 0 = 0 := rfl
@[simp, norm_cast] lemma ofENat_one : ofENat 1 = 1 := Nat.cast_one

@[simp, norm_cast] lemma ofENat_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℕ∞)) : Ordinal) = OfNat.ofNat n :=
  rfl

lemma ofENat_strictMono : StrictMono ofENat :=
  WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, nat_lt_omega0⟩

@[simp, norm_cast]
lemma ofENat_lt_ofENat {m n : ℕ∞} : (m : Ordinal) < n ↔ m < n :=
  ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]
lemma ofENat_lt_omega0 {m : ℕ∞} : (m : Ordinal) < ω ↔ m < ⊤ :=
  ofENat_lt_ofENat (n := ⊤)

@[simp] lemma ofENat_lt_nat {m : ℕ∞} {n : ℕ} : ofENat m < n ↔ m < n := by norm_cast

@[simp] lemma ofENat_lt_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m < no_index (OfNat.ofNat n) ↔ m < OfNat.ofNat n := ofENat_lt_nat

@[simp] lemma nat_lt_ofENat {m : ℕ} {n : ℕ∞} : (m : Ordinal) < n ↔ m < n := by norm_cast
@[simp] lemma ofENat_pos {m : ℕ∞} : 0 < (m : Ordinal) ↔ 0 < m := by norm_cast
@[simp] lemma one_lt_ofENat {m : ℕ∞} : 1 < (m : Ordinal) ↔ 1 < m := by norm_cast

@[simp, norm_cast] lemma ofNat_lt_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
  no_index (OfNat.ofNat m : Ordinal) < n ↔ OfNat.ofNat m < n := nat_lt_ofENat

lemma ofENat_mono : Monotone ofENat := ofENat_strictMono.monotone

@[simp, norm_cast]
lemma ofENat_le_ofENat {m n : ℕ∞} : (m : Ordinal) ≤ n ↔ m ≤ n := ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat

@[simp] lemma ofENat_le_omega0 (n : ℕ∞) : ↑n ≤ ω := ofENat_le_ofENat.2 le_top
@[simp] lemma ofENat_le_nat {m : ℕ∞} {n : ℕ} : ofENat m ≤ n ↔ m ≤ n := by norm_cast
@[simp] lemma ofENat_le_one {m : ℕ∞} : ofENat m ≤ 1 ↔ m ≤ 1 := by norm_cast

@[simp] lemma ofENat_le_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m ≤ no_index (OfNat.ofNat n) ↔ m ≤ OfNat.ofNat n := ofENat_le_nat

@[simp] lemma nat_le_ofENat {m : ℕ} {n : ℕ∞} : (m : Ordinal) ≤ n ↔ m ≤ n := by norm_cast
@[simp] lemma one_le_ofENat {n : ℕ∞} : 1 ≤ (n : Ordinal) ↔ 1 ≤ n := by norm_cast

@[simp]
lemma ofNat_le_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
    no_index (OfNat.ofNat m : Ordinal) ≤ n ↔ OfNat.ofNat m ≤ n := nat_le_ofENat

lemma ofENat_injective : Injective ofENat := ofENat_strictMono.injective

@[simp, norm_cast]
lemma ofENat_inj {m n : ℕ∞} : (m : Ordinal) = n ↔ m = n := ofENat_injective.eq_iff

@[simp] lemma ofENat_eq_nat {m : ℕ∞} {n : ℕ} : (m : Ordinal) = n ↔ m = n := by norm_cast
@[simp] lemma nat_eq_ofENat {m : ℕ} {n : ℕ∞} : (m : Ordinal) = n ↔ m = n := by norm_cast

@[simp] lemma ofENat_eq_zero {m : ℕ∞} : (m : Ordinal) = 0 ↔ m = 0 := by norm_cast
@[simp] lemma zero_eq_ofENat {m : ℕ∞} : 0 = (m : Ordinal) ↔ m = 0 := by norm_cast; apply eq_comm

@[simp] lemma ofENat_eq_one {m : ℕ∞} : (m : Ordinal) = 1 ↔ m = 1 := by norm_cast
@[simp] lemma one_eq_ofENat {m : ℕ∞} : 1 = (m : Ordinal) ↔ m = 1 := by norm_cast; apply eq_comm

@[simp] lemma ofENat_eq_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    (m : Ordinal) = no_index (OfNat.ofNat n) ↔ m = OfNat.ofNat n := ofENat_eq_nat

@[simp] lemma ofNat_eq_ofENat {m : ℕ} {n : ℕ∞} [m.AtLeastTwo] :
    no_index (OfNat.ofNat m) = (n : Ordinal) ↔ OfNat.ofNat m = n := nat_eq_ofENat

@[simp, norm_cast] lemma lift_ofENat : ∀ m : ℕ∞, lift.{u, v} m = m
  | (m : ℕ) => lift_natCast m
  | ⊤ => lift_omega0

@[simp] lemma lift_lt_ofENat {x : Ordinal.{v}} {m : ℕ∞} : lift.{u} x < m ↔ x < m := by
  rw [← lift_ofENat.{u, v}, lift_lt]

@[simp] lemma lift_le_ofENat {x : Ordinal.{v}} {m : ℕ∞} : lift.{u} x ≤ m ↔ x ≤ m := by
  rw [← lift_ofENat.{u, v}, lift_le]

@[simp] lemma lift_eq_ofENat {x : Ordinal.{v}} {m : ℕ∞} : lift.{u} x = m ↔ x = m := by
  rw [← lift_ofENat.{u, v}, lift_inj]

@[simp] lemma ofENat_lt_lift {x : Ordinal.{v}} {m : ℕ∞} : m < lift.{u} x ↔ m < x := by
  rw [← lift_ofENat.{u, v}, lift_lt]

@[simp] lemma ofENat_le_lift {x : Ordinal.{v}} {m : ℕ∞} : m ≤ lift.{u} x ↔ m ≤ x := by
  rw [← lift_ofENat.{u, v}, lift_le]

@[simp] lemma ofENat_eq_lift {x : Ordinal.{v}} {m : ℕ∞} : m = lift.{u} x ↔ m = x := by
  rw [← lift_ofENat.{u, v}, lift_inj]

@[simp]
lemma range_ofENat : range ofENat = Iic ω := by
  refine (range_subset_iff.2 ofENat_le_omega0).antisymm fun x (hx : x ≤ ω) ↦ ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to ℕ using hlt
    exact mem_range_self (x : ℕ∞)
  · exact mem_range_self (⊤ : ℕ∞)

instance : CanLift Ordinal ℕ∞ (↑) (· ≤ ω) where
  prf x := (Set.ext_iff.1 range_ofENat x).2

/-- Unbundled version of `Ordinal.toENat`. -/
noncomputable def toENatAux (o : Ordinal.{u}) : ℕ∞ := Cardinal.toENat o.card

lemma toENatAux_nat (n : ℕ) : toENatAux n = n := by
  rw [toENatAux, card_nat, Cardinal.toENat_nat]
lemma toENatAux_zero : toENatAux 0 = 0 := toENatAux_nat 0
lemma toENatAux_one : toENatAux 1 = 1 := by exact_mod_cast toENatAux_nat 1

lemma toENatAux_eq_top {a : Ordinal} (ha : ω ≤ a) : toENatAux a = ⊤ := by
  rw [toENatAux, Cardinal.toENat_eq_top]
  exact card_le_card ha

lemma toENatAux_ofENat : ∀ n : ℕ∞, toENatAux n = n
  | (n : ℕ) => toENatAux_nat n
  | ⊤ => toENatAux_eq_top le_rfl

attribute [local simp] toENatAux_nat toENatAux_zero toENatAux_ofENat

lemma toENatAux_gc : GaloisConnection (↑) toENatAux := fun n x ↦ by
  cases lt_or_le x ω with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_omega0 n).trans hx]

theorem toENatAux_le_nat {x : Ordinal} {n : ℕ} : toENatAux x ≤ n ↔ x ≤ n := by
  cases lt_or_le x ω with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (nat_lt_omega0 n).trans_le hx]

lemma toENatAux_eq_nat {x : Ordinal} {n : ℕ} : toENatAux x = n ↔ x = n := by
  simp [toENatAux]

lemma toENatAux_eq_zero {x : Ordinal} : toENatAux x = 0 ↔ x = 0 := toENatAux_eq_nat

/-- Projection from cardinals to `ℕ∞`. Sends all infinite cardinals to `⊤`.

We define this function as a bundled monotone monoid with zero homomorphism. This function also
preserves addition, but `→+*o` requires commutativity of addition, which we don't have. -/
noncomputable def toENat : Ordinal.{u} →*₀o ℕ∞ where
  toFun := toENatAux
  map_one' := toENatAux_one
  map_mul' x y := by simp [toENatAux]
  map_zero' := toENatAux_zero
  monotone' := toENatAux_gc.monotone_u

@[simp]
theorem toENat_add (x y : Ordinal) : toENat (x + y) = toENat x + toENat y := by
  simp [toENat, toENatAux]

/-- The coercion `Ordinal.ofENat` and the projection `Ordinal.toENat` form a Galois connection.
See also `Ordinal.gciENat`. -/
lemma enat_gc : GaloisConnection (↑) toENat := toENatAux_gc

@[simp] lemma toENat_ofENat (n : ℕ∞) : toENat n = n := toENatAux_ofENat n
@[simp] lemma toENat_comp_ofENat : toENat ∘ (↑) = id := funext toENat_ofENat

/-- The coercion `Ordinal.ofENat` and the projection `Ordinal.toENat`
form a Galois coinsertion. -/
noncomputable def gciENat : GaloisCoinsertion (↑) toENat :=
  enat_gc.toGaloisCoinsertion fun n ↦ (toENat_ofENat n).le

lemma toENat_strictMonoOn : StrictMonoOn toENat (Iic ω) := by
  simp only [← range_ofENat, StrictMonoOn, forall_mem_range, toENat_ofENat, ofENat_lt_ofENat]
  exact fun _ _ ↦ id

lemma toENat_injOn : InjOn toENat (Iic ω) := toENat_strictMonoOn.injOn

lemma ofENat_toENat_le (a : Ordinal) : ↑(toENat a) ≤ a := enat_gc.l_u_le _

@[simp]
lemma ofENat_toENat_eq_self {a : Ordinal} : toENat a = a ↔ a ≤ ω := by
  rw [eq_comm, ← enat_gc.exists_eq_l]
  simpa only [mem_range, eq_comm] using Set.ext_iff.1 range_ofENat a

@[simp] alias ⟨_, ofENat_toENat⟩ := ofENat_toENat_eq_self

@[simp] lemma toENat_nat (n : ℕ) : toENat n = n := toENatAux_nat n

@[simp] lemma toENat_le_nat {a : Ordinal} {n : ℕ} : toENat a ≤ n ↔ a ≤ n := toENatAux_le_nat
@[simp] lemma toENat_eq_nat {a : Ordinal} {n : ℕ} : toENat a = n ↔ a = n := toENatAux_eq_nat
@[simp] lemma toENat_eq_zero {a : Ordinal} : toENat a = 0 ↔ a = 0 := toENatAux_eq_zero
@[simp] lemma toENat_le_one {a : Ordinal} : toENat a ≤ 1 ↔ a ≤ 1 := by
  rw [← Nat.cast_one, toENat_le_nat, Nat.cast_one]
@[simp] lemma toENat_eq_one {a : Ordinal} : toENat a = 1 ↔ a = 1 := by
  rw [← Nat.cast_one, toENat_eq_nat, Nat.cast_one]

@[simp] lemma toENat_le_ofNat {a : Ordinal} {n : ℕ} [n.AtLeastTwo] :
    toENat a ≤ no_index (OfNat.ofNat n) ↔ a ≤ OfNat.ofNat n := toENat_le_nat

@[simp] lemma toENat_eq_ofNat {a : Ordinal} {n : ℕ} [n.AtLeastTwo] :
    toENat a = no_index (OfNat.ofNat n) ↔ a = OfNat.ofNat n := toENat_eq_nat

@[simp] lemma toENat_eq_top {a : Ordinal} : toENat a = ⊤ ↔ ω ≤ a := enat_gc.u_eq_top

@[simp]
theorem toENat_lift {a : Ordinal.{v}} : toENat (lift.{u} a) = toENat a := by
  cases le_total a ω with
  | inl ha => lift a to ℕ∞ using ha; simp
  | inr ha => simp [toENat_eq_top.2, ha]

/-- The coercion `Ordinal.ofENat` as a bundled homomorphism. -/
def ofENatHom : ℕ∞ →o Ordinal where
  toFun := (↑)
  monotone' := ofENat_mono

end Ordinal

@[simp]
theorem Cardinal.toENat_card (o : Ordinal) : Cardinal.toENat o.card = Ordinal.toENat o :=
  rfl

@[simp]
theorem Ordinal.toENat_ord (c : Cardinal) : Ordinal.toENat c.ord = Cardinal.toENat c := by
  rw [← c.card_ord, Cardinal.toENat_card, c.card_ord]
