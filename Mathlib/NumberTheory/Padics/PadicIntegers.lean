/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric IsLocalRing

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def PadicInt : Type := {x : ℚ_[p] // ‖x‖ ≤ 1}

/-- The ring of `p`-adic integers. -/
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt
variable {p} {x y : ℤ_[p]}

/-! ### Ring structure and coercion to `ℚ_[p]` -/

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext

variable (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := (Padic.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := Iff.rfl

variable {p}

instance instCommRing : CommRing ℤ_[p] := inferInstanceAs <| CommRing (subring p)

instance : Inhabited ℤ_[p] := ⟨0⟩

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp, norm_cast]
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl

@[simp, norm_cast]
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl

@[simp, norm_cast]
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl

@[simp, norm_cast]
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

@[simp] lemma coe_eq_zero : (x : ℚ_[p]) = 0 ↔ x = 0 := by rw [← coe_zero, Subtype.coe_inj]

lemma coe_ne_zero : (x : ℚ_[p]) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl

@[simp, norm_cast]
theorem coe_intCast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype

@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n := rfl

theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := by simp

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

instance : CharZero ℤ_[p] where
  cast_injective m n h :=
    Nat.cast_injective (R := ℚ_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]
theorem intCast_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by simp

/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variable (p)

instance : MetricSpace ℤ_[p] := Subtype.metricSpace

instance : IsUltrametricDist ℤ_[p] := IsUltrametricDist.subtype _

instance completeSpace : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ‖x‖ ≤ 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe

instance : Norm ℤ_[p] := ⟨fun z => ‖(z : ℚ_[p])‖⟩

variable {p} in
theorem norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ := rfl

instance : NormedCommRing ℤ_[p] where
  __ := instCommRing
  dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ ↦ rfl
  norm_mul_le := by simp [norm_def]

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

instance : NormMulClass ℤ_[p] := ⟨fun x y ↦ by simp [norm_def]⟩

instance : IsDomain ℤ_[p] := NoZeroDivisors.to_isDomain _

variable {p}

/-! ### Norm -/

theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2

theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean _ _

theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖ :=
  Padic.add_eq_max_of_ne

theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h

theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]

theorem norm_intCast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]

@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl

@[simp]
theorem norm_p : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p

theorem norm_p_pow (n : ℕ) : ‖(p : ℤ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := by simp

private def cauSeq_to_rat_cauSeq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)

instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ ≤ 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩

theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos

theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℚ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : ℝ) = (p : ℚ) by simp] at hk
  exact mod_cast hk

variable {p}

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  Padic.norm_intCast_lt_one_iff

theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} :
    ‖(k : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  Padic.norm_int_le_pow_iff_dvd _ _

@[simp]
lemma norm_natCast_eq_one_iff {n : ℕ} :
    ‖(n : ℤ_[p])‖ = 1 ↔ p.Coprime n := by
  rw [norm_def, coe_natCast, Padic.norm_natCast_eq_one_iff]

@[simp]
lemma norm_natCast_lt_one_iff {n : ℕ} :
    ‖(n : ℤ_[p])‖ < 1 ↔ p ∣ n := by
  rw [norm_def, coe_natCast, Padic.norm_natCast_lt_one_iff]

@[simp]
lemma norm_intCast_eq_one_iff {z : ℤ} :
    ‖(z : ℤ_[p])‖ = 1 ↔ IsCoprime z p := by
  rw [norm_def, coe_intCast, Padic.norm_intCast_eq_one_iff]

@[simp]
lemma norm_intCast_lt_one_iff {z : ℤ} :
    ‖(z : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ z := by
  rw [norm_def, coe_intCast, Padic.norm_intCast_lt_one_iff]

/-! ### Valuation on `ℤ_[p]` -/

lemma valuation_coe_nonneg : 0 ≤ (x : ℚ_[p]).valuation := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have := x.2
  rwa [Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx, zpow_le_one_iff_right₀, neg_nonpos]
    at this
  exact mod_cast hp.out.one_lt

/-- `PadicInt.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`. -/
def valuation (x : ℤ_[p]) : ℕ := (x : ℚ_[p]).valuation.toNat

@[simp, norm_cast] lemma valuation_coe (x : ℤ_[p]) : (x : ℚ_[p]).valuation = x.valuation := by
  simp [valuation, valuation_coe_nonneg]

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 := by simp [valuation]
@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 := by simp [valuation]
@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [valuation]

lemma le_valuation_add (hxy : x + y ≠ 0) : min x.valuation y.valuation ≤ (x + y).valuation := by
  zify; simpa [← valuation_coe] using Padic.le_valuation_add <| coe_ne_zero.2 hxy

@[simp] lemma valuation_mul (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).valuation = x.valuation + y.valuation := by
  zify; simp [← valuation_coe, Padic.valuation_mul (coe_ne_zero.2 hx) (coe_ne_zero.2 hy)]

@[simp]
lemma valuation_pow (x : ℤ_[p]) (n : ℕ) : (x ^ n).valuation = n * x.valuation := by
  zify; simp [← valuation_coe]

lemma norm_eq_zpow_neg_valuation {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = p ^ (-x.valuation : ℤ) := by
  simp [norm_def, Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx]

-- TODO: Do we really need this lemma?
@[simp]
theorem valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
    ((p : ℤ_[p]) ^ n * c).valuation = n + c.valuation := by
  rw [valuation_mul (NeZero.ne _) hc, valuation_pow, valuation_p, mul_one]

section Units

/-! ### Units of `ℤ_[p]` -/

theorem mul_inv : ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1
  | ⟨k, _⟩, h => by
    have hk : k ≠ 0 := fun h' => zero_ne_one' ℚ_[p] (by simp [h'] at h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    dsimp only
    rw [dif_pos h]
    apply Subtype.ext_iff.2
    simp [mul_inv_cancel₀ hk]

theorem inv_mul {z : ℤ_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]

theorem isUnit_iff {z : ℤ_[p]} : IsUnit z ↔ ‖z‖ = 1 :=
  ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine le_antisymm (norm_le_one _) ?_
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
  lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
  calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

theorem mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ‖z‖ < 1 := by
  simp [norm_le_one z, nonunits, isUnit_iff]

theorem not_isUnit_iff {z : ℤ_[p]} : ¬IsUnit z ↔ ‖z‖ < 1 := by
  simpa using mem_nonunits

/-- A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`. -/
def mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ :=
  let z : ℤ_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
theorem mkUnits_eq {u : ℚ_[p]} (h : ‖u‖ = 1) : ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u := rfl

@[simp]
theorem norm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 := isUnit_iff.mp <| by simp

/-- `unitCoeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unitCoeff_spec`. -/
def unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  let u : ℚ_[p] := x * (p : ℚ_[p]) ^ (-x.valuation : ℤ)
  have hu : ‖u‖ = 1 := by
    simp [u, hx, pow_ne_zero _ (NeZero.ne _), norm_eq_zpow_neg_valuation]
  mkUnits hu

@[simp]
theorem unitCoeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
    (unitCoeff hx : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation : ℤ) := rfl

theorem unitCoeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
    x = (unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation := by
  apply Subtype.coe_injective
  push_cast
  rw [unitCoeff_coe, mul_assoc, ← zpow_natCast, ← zpow_add₀]
  · simp
  · exact NeZero.ne _

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/

theorem norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ n ≤ x.valuation := by
  rw [norm_eq_zpow_neg_valuation hx, zpow_le_zpow_iff_right₀, neg_le_neg_iff, Nat.cast_le]
  exact mod_cast hp.out.one_lt

theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔ n ≤ x.valuation := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c ≠ 0 by
      rw [valuation_p_pow_mul _ _ this]
      exact le_self_add
    contrapose! hx
    rw [hx, mul_zero]
  · nth_rewrite 2 [unitCoeff_spec hx]
    simpa [Units.isUnit, IsUnit.dvd_mul_left] using pow_dvd_pow _

theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_natCast, inv_nonneg, iff_true, Submodule.zero_mem]
    exact mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]

theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ < (p : ℝ) ^ n ↔ ‖x‖ ≤ (p : ℝ) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

theorem norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x := by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton, pow_one] at this
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.natCast_succ, neg_add_cancel, zero_add]

@[simp]
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p : ℤ_[p]) ^ n ∣ a ↔ (p ^ n : ℤ) ∣ a := by
  rw [← Nat.cast_pow, ← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton, Nat.cast_pow]

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/

instance : IsLocalRing ℤ_[p] :=
  IsLocalRing.of_nonunits_add <| by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add

theorem p_nonunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] := by
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ <| mod_cast hp.out.one_lt
  rwa [← norm_p, ← mem_nonunits] at this

@[deprecated (since := "2025-07-27")] alias p_nonnunit := p_nonunit

theorem maximalIdeal_eq_span_p : maximalIdeal ℤ_[p] = Ideal.span {(p : ℤ_[p])} := by
  apply le_antisymm
  · intro x hx
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonunit

theorem prime_p : Prime (p : ℤ_[p]) := by
  rw [← Ideal.span_singleton_prime, ← maximalIdeal_eq_span_p]
  · infer_instance
  · exact NeZero.ne _

theorem irreducible_p : Irreducible (p : ℤ_[p]) := Prime.irreducible prime_p

instance : IsDiscreteValuationRing ℤ_[p] :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩

theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) :
    ∃ n : ℕ, s = Ideal.span {(p : ℤ_[p]) ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

open CauSeq

instance : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] where
  prec' x hx := by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq ℤ_[p] norm := ⟨x, ?_⟩; swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      rw [← neg_sub, norm_neg]
      exact hx hn
    · refine ⟨x'.lim, fun n => ?_⟩
      have : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (mod_cast hp.out.pos) _
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases hin : i ≤ n
      · exact (hi i le_rfl n hin).le
      · push_neg at hin
        specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i : ℤ_[p]) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        exact this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

end Dvr

section FractionRing

instance algebra : Algebra ℤ_[p] ℚ_[p] :=
  Algebra.ofSubring (subring p)

@[simp]
theorem algebraMap_apply (x : ℤ_[p]) : algebraMap ℤ_[p] ℚ_[p] x = x :=
  rfl

instance isFractionRing : IsFractionRing ℤ_[p] ℚ_[p] where
  map_units := fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ ≤ 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one, map_one, mul_one, PadicInt.algebraMap_apply, Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : ℤ) = -x.valuation := by
        rw [hn, Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
        exact hx.le
      set a := x * (p : ℚ_[p]) ^ n with ha
      have ha_norm : ‖a‖ = 1 := by
        have hx : x ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hx
          exact hx zero_le_one
        rw [ha, padicNormE.mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx,
          ← zpow_add', hn_coe, neg_neg, neg_add_cancel, zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : ℤ_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [a, map_pow, map_natCast, algebraMap_apply]
  exists_of_eq := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    exact fun h => ⟨1, by rw [h]⟩

end FractionRing

end PadicInt
