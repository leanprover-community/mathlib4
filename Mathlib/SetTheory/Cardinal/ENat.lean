/-
Copyright (c) 2024 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.Order.Hom.Ring

/-!
# Conversion between `Cardinal` and `ℕ∞`
-/

open Function Set
universe u v

namespace Cardinal

@[coe]
def ofENat : ℕ∞ → Cardinal
  | (n : ℕ) => n
  | ⊤ => ℵ₀

instance : Coe ENat Cardinal := ⟨Cardinal.ofENat⟩

@[simp, norm_cast] lemma ofENat_top : ofENat ⊤ = ℵ₀ := rfl
@[simp, norm_cast] lemma ofENat_nat (n : ℕ) : ofENat n = n := rfl
@[simp, norm_cast] lemma ofENat_zero : ofENat 0 = 0 := rfl
@[simp, norm_cast] lemma ofENat_one : ofENat 1 = 1 := rfl

@[simp, norm_cast] lemma ofENat_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℕ∞)) : Cardinal) = OfNat.ofNat n :=
  rfl
  
lemma ofENat_strictMono : StrictMono ofENat :=
  WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, nat_lt_aleph0⟩

@[simp, norm_cast]
lemma ofENat_lt_ofENat {m n : ℕ∞} : (m : Cardinal) < n ↔ m < n :=
  ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]
lemma ofENat_lt_aleph0 {m : ℕ∞} : (m : Cardinal) < ℵ₀ ↔ m < ⊤ :=
  ofENat_lt_ofENat (n := ⊤)

@[simp] lemma ofENat_lt_nat {m : ℕ∞} {n : ℕ} : ofENat m < n ↔ m < n := by norm_cast

@[simp] lemma ofENat_lt_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m < no_index (OfNat.ofNat n) ↔ m < OfNat.ofNat n := ofENat_lt_nat

@[simp] lemma nat_lt_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) < n ↔ m < n := by norm_cast
@[simp] lemma ofENat_pos {m : ℕ∞} : 0 < (m : Cardinal) ↔ 0 < m := by norm_cast
@[simp] lemma one_lt_ofENat {m : ℕ∞} : 1 < (m : Cardinal) ↔ 1 < m := by norm_cast

@[simp, norm_cast] lemma ofNat_lt_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
  no_index (OfNat.ofNat m : Cardinal) < n ↔ OfNat.ofNat m < n := nat_lt_ofENat

lemma ofENat_mono : Monotone ofENat := ofENat_strictMono.monotone

@[simp, norm_cast]
lemma ofENat_le_ofENat {m n : ℕ∞} : (m : Cardinal) ≤ n ↔ m ≤ n := ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat

@[simp] lemma ofENat_le_aleph0 (n : ℕ∞) : ↑n ≤ ℵ₀ := ofENat_le_ofENat.2 le_top
@[simp] lemma ofENat_le_nat {m : ℕ∞} {n : ℕ} : ofENat m ≤ n ↔ m ≤ n := by norm_cast
@[simp] lemma ofENat_le_one {m : ℕ∞} : ofENat m ≤ 1 ↔ m ≤ 1 := by norm_cast

@[simp] lemma ofENat_le_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m ≤ no_index (OfNat.ofNat n) ↔ m ≤ OfNat.ofNat n := ofENat_le_nat

@[simp] lemma nat_le_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) ≤ n ↔ m ≤ n := by norm_cast
@[simp] lemma one_le_ofENat {n : ℕ∞} : 1 ≤ (n : Cardinal) ↔ 1 ≤ n := by norm_cast

@[simp]
lemma ofNat_le_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
    no_index (OfNat.ofNat m : Cardinal) ≤ n ↔ OfNat.ofNat m ≤ n := nat_le_ofENat

lemma ofENat_injective : Injective ofENat := ofENat_strictMono.injective

@[simp, norm_cast]
lemma ofENat_inj {m n : ℕ∞} : (m : Cardinal) = n ↔ m = n := ofENat_injective.eq_iff

@[simp] lemma ofENat_eq_nat {m : ℕ∞} {n : ℕ} : (m : Cardinal) = n ↔ m = n := by norm_cast
@[simp] lemma nat_eq_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) = n ↔ m = n := by norm_cast

@[simp] lemma ofENat_eq_zero {m : ℕ∞} : (m : Cardinal) = 0 ↔ m = 0 := by norm_cast
@[simp] lemma zero_eq_ofENat {m : ℕ∞} : 0 = (m : Cardinal) ↔ m = 0 := by norm_cast; apply eq_comm

@[simp] lemma ofENat_eq_one {m : ℕ∞} : (m : Cardinal) = 1 ↔ m = 1 := by norm_cast
@[simp] lemma one_eq_ofENat {m : ℕ∞} : 1 = (m : Cardinal) ↔ m = 1 := by norm_cast; apply eq_comm

@[simp] lemma ofENat_eq_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    (m : Cardinal) = no_index (OfNat.ofNat n) ↔ m = OfNat.ofNat n := ofENat_eq_nat

@[simp] lemma ofNat_eq_ofENat {m : ℕ} {n : ℕ∞} [m.AtLeastTwo] :
    no_index (OfNat.ofNat m) = (n : Cardinal) ↔ OfNat.ofNat m = n := nat_eq_ofENat

@[simp, norm_cast] lemma lift_ofENat : ∀ m : ℕ∞, lift.{u, v} m = m
  | (m : ℕ) => lift_natCast m
  | ⊤ => lift_aleph0

@[simp] lemma lift_lt_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x < m ↔ x < m := by
  rw [← lift_ofENat.{u, v}, lift_lt]

@[simp] lemma lift_le_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x ≤ m ↔ x ≤ m := by
  rw [← lift_ofENat.{u, v}, lift_le]

@[simp] lemma lift_eq_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x = m ↔ x = m := by
  rw [← lift_ofENat.{u, v}, lift_inj]

@[simp] lemma ofENat_lt_lift {x : Cardinal.{v}} {m : ℕ∞} : m < lift.{u} x ↔ m < x := by
  rw [← lift_ofENat.{u, v}, lift_lt]

@[simp] lemma ofENat_le_lift {x : Cardinal.{v}} {m : ℕ∞} : m ≤ lift.{u} x ↔ m ≤ x := by
  rw [← lift_ofENat.{u, v}, lift_le]

@[simp] lemma ofENat_eq_lift {x : Cardinal.{v}} {m : ℕ∞} : m = lift.{u} x ↔ m = x := by
  rw [← lift_ofENat.{u, v}, lift_inj]

@[simp] lemma ofENat_add_aleph0 : ∀ m : ℕ∞, m + ℵ₀ = ℵ₀
  | (m : ℕ) => nat_add_aleph0 m
  | ⊤ => aleph0_add_aleph0

@[simp] lemma aleph0_add_ofENat (m : ℕ∞) : ℵ₀ + m = ℵ₀ := by rw [add_comm, ofENat_add_aleph0]

@[simp, norm_cast]
lemma ofENat_add : ∀ m n : ℕ∞, ofENat (m + n) = m + n
  | (m : ℕ), (n : ℕ) => Nat.cast_add m n
  | ⊤, _ => by simp
  | _, ⊤ => by simp

@[simp] lemma ofENat_mul_aleph0 {m : ℕ∞} (hm : m ≠ 0) : ↑m * ℵ₀ = ℵ₀ := by
  induction m using ENat.recTopCoe with
  | top => exact aleph0_mul_aleph0
  | coe m => rw [ofENat_nat, nat_mul_aleph0 (mod_cast hm)]

@[simp] lemma aleph0_mul_ofENat {m : ℕ∞} (hm : m ≠ 0) : ℵ₀ * m = ℵ₀ := by
  rw [mul_comm, ofENat_mul_aleph0 hm]

@[simp] lemma ofENat_mul (m n : ℕ∞) : ofENat (m * n) = m * n := by
  have : ∀ a : ℕ∞, ofENat (a * ⊤) = a * ℵ₀ := fun a ↦ by
    rcases eq_or_ne a 0 with rfl | ha <;> simp [*]
  induction m using ENat.recTopCoe with
  | top => rw [mul_comm, this, mul_comm, ofENat_top]
  | coe m =>
    induction n using ENat.recTopCoe with
    | top => apply this
    | coe n => norm_cast; norm_cast -- TODO: why has to be run twice?

def ofENatHom : ℕ∞ →+*o Cardinal where
  toFun := (↑)
  map_one' := ofENat_one
  map_mul' := ofENat_mul
  map_zero' := ofENat_zero
  map_add' := ofENat_add
  monotone' := ofENat_mono

@[simp]
lemma range_ofENat : range ofENat = Iic ℵ₀ := by
  refine (range_subset_iff.2 ofENat_le_aleph0).antisymm fun x (hx : x ≤ ℵ₀) ↦ ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to ℕ using hlt
    exact mem_range_self (x : ℕ∞)
  · exact mem_range_self (⊤ : ℕ∞)

instance : CanLift Cardinal ℕ∞ (↑) (· ≤ ℵ₀) where
  prf x := (Set.ext_iff.1 range_ofENat x).2

noncomputable def toENatAux : Cardinal.{u} → ℕ∞ := extend Nat.cast Nat.cast fun _ ↦ ⊤

lemma toENatAux_nat (n : ℕ) : toENatAux n = n := Nat.cast_injective.extend_apply ..
lemma toENatAux_zero : toENatAux 0 = 0 := toENatAux_nat 0

lemma toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ ≤ a) : toENatAux a = ⊤ :=
  extend_apply' _ _ _ fun ⟨n, hn⟩ ↦ ha.not_lt <| hn ▸ nat_lt_aleph0 n

lemma toENatAux_ofENat : ∀ n : ℕ∞, toENatAux n = n
  | (n : ℕ) => toENatAux_nat n
  | ⊤ => toENatAux_eq_top le_rfl

attribute [local simp] toENatAux_nat toENatAux_zero toENatAux_ofENat

lemma toENatAux_gc : GaloisConnection (↑) toENatAux := fun n x ↦ by
  cases lt_or_le x ℵ₀ with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_aleph0 n).trans hx]

lemma toENatAux_eq_nat {x : Cardinal} {n : ℕ} : toENatAux x = n ↔ x = n := by
  cases lt_or_le x ℵ₀ with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simpa [toENatAux_eq_top hx] using ((nat_lt_aleph0 n).trans_le hx).ne'

lemma toENatAux_eq_zero {x : Cardinal} : toENatAux x = 0 ↔ x = 0 := toENatAux_eq_nat

noncomputable def toENat : Cardinal.{u} →+*o ℕ∞ where
  toFun := toENatAux
  map_one' := toENatAux_nat 1
  map_mul' x y := by
    wlog hle : x ≤ y; · rw [mul_comm, this y x (le_of_not_le hle), mul_comm]
    cases lt_or_le y ℵ₀ with
    | inl hy =>
      lift x to ℕ using hle.trans_lt hy; lift y to ℕ using hy
      simp only [← Nat.cast_mul, toENatAux_nat]
    | inr hy =>
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · simp only [toENatAux_eq_top hy]
        rw [toENatAux_eq_top, ENat.mul_top]
        · rwa [Ne.def, toENatAux_eq_zero]
        · exact le_mul_of_one_le_of_le (one_le_iff_ne_zero.2 hx) hy
  map_add' x y := by
    wlog hle : x ≤ y; · rw [add_comm, this y x (le_of_not_le hle), add_comm]
    cases lt_or_le y ℵ₀ with
    | inl hy =>
      lift x to ℕ using hle.trans_lt hy; lift y to ℕ using hy
      simp only [← Nat.cast_add, toENatAux_nat]
    | inr hy =>
      simp only [toENatAux_eq_top hy, add_top]
      exact toENatAux_eq_top <| le_add_left hy
  map_zero' := toENatAux_zero
  monotone' := toENatAux_gc.monotone_u

lemma enat_gc : GaloisConnection (↑) toENat := toENatAux_gc

@[simp] lemma toENat_ofENat (n : ℕ∞) : toENat n = n := toENatAux_ofENat n
@[simp] lemma toENat_comp_ofENat : toENat ∘ (↑) = id := funext toENat_ofENat

noncomputable def gciENat : GaloisCoinsertion (↑) toENat :=
  enat_gc.toGaloisCoinsertion fun n ↦ (toENat_ofENat n).le

lemma toENat_injOn : InjOn toENat (Iic ℵ₀) :=
  range_ofENat ▸ Injective.injOn_range <| by simp [injective_id]

lemma ofENat_toENat

end Cardinal
