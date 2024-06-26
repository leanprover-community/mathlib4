/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Bezout
import Mathlib.Tactic.FieldSimp

#align_import ring_theory.valuation.valuation_ring from "leanprover-community/mathlib"@"c163ec99dfc664628ca15d215fce0a5b9c265b68"

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]`,
there is a natural valuation `Valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebraMap A K` agrees with `(Valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `ValuationRing.tFAE`.
1. `R` is a valuation ring.
2. For each `x : FractionRing K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

-/


universe u v w

/-- An integral domain is called a `ValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
class ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop where
  cond' : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a
#align valuation_ring ValuationRing

-- Porting note: this lemma is needed since infer kinds are unsupported in Lean 4
lemma ValuationRing.cond {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] (a b : A) :
    ∃ c : A, a * c = b ∨ b * c = a := @ValuationRing.cond' A _ _ _ _ _

namespace ValuationRing

section

variable (A : Type u) [CommRing A]
variable (K : Type v) [Field K] [Algebra A K]

/-- The value group of the valuation ring `A`. Note: this is actually a group with zero. -/
def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)
#align valuation_ring.value_group ValuationRing.ValueGroup

instance : Inhabited (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

instance : LE (ValueGroup A K) :=
  LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => ∃ c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        constructor
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t at he
          simpa [mul_smul] using he
        · rintro ⟨e, he⟩; dsimp
          use c * e * (d⁻¹ : Aˣ)
          simp_rw [Units.smul_def, ← he, mul_smul]
          rw [← mul_smul _ _ b, Units.inv_mul, one_smul])

instance : Zero (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

instance : One (ValueGroup A K) := ⟨Quotient.mk'' 1⟩

instance : Mul (ValueGroup A K) :=
  Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotient.sound'
        dsimp
        use c * d
        simp only [mul_smul, Algebra.smul_def, Units.smul_def, RingHom.map_mul, Units.val_mul]
        ring)

instance : Inv (ValueGroup A K) :=
  Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotient.sound'
        use b⁻¹
        dsimp
        rw [Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def, mul_inv,
          map_units_inv])

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]

protected theorem le_total (a b : ValueGroup A K) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
  obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
  have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  · right
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← RingHom.map_mul, ← h]; congr 1; ring
  · left
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← RingHom.map_mul, ← h]; congr 1; ring
#align valuation_ring.le_total ValuationRing.le_total

-- Porting note: it is much faster to split the instance `LinearOrderedCommGroupWithZero`
-- into two parts
noncomputable instance linearOrder : LinearOrder (ValueGroup A K) where
  le_refl := by rintro ⟨⟩; use 1; rw [one_smul]
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    by_cases hb : b = 0; · simp [hb]
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
      rw [← mul_smul, Algebra.smul_def] at hf
      nth_rw 2 [← one_mul b] at hf
      rw [← (algebraMap A K).map_one] at hf
      exact IsFractionRing.injective _ _ (mul_right_cancel₀ hb hf).symm
    apply Quotient.sound'
    exact ⟨this.unit, rfl⟩
  le_total := ValuationRing.le_total _ _
  decidableLE := by classical infer_instance

noncomputable instance linearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero (ValueGroup A K) :=
  { linearOrder .. with
    mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]; apply Setoid.refl'
    one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]; apply Setoid.refl'
    mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]; apply Setoid.refl'
    mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]; apply Setoid.refl'
    mul_le_mul_left := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c, rfl⟩ ⟨d⟩
      use c; simp only [Algebra.smul_def]; ring
    zero_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [zero_mul]; apply Setoid.refl'
    mul_zero := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_zero]; apply Setoid.refl'
    zero_le_one := ⟨0, by rw [zero_smul]⟩
    exists_pair_ne := by
      use 0, 1
      intro c; obtain ⟨d, hd⟩ := Quotient.exact' c
      apply_fun fun t => d⁻¹ • t at hd
      simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd
    inv_zero := by apply Quotient.sound'; rw [inv_zero]; apply Setoid.refl'
    mul_inv_cancel := by
      rintro ⟨a⟩ ha
      apply Quotient.sound'
      use 1
      simp only [one_smul, ne_eq]
      apply (mul_inv_cancel _).symm
      contrapose ha
      simp only [Classical.not_not] at ha ⊢
      rw [ha]
      rfl }

/-- Any valuation ring induces a valuation on its fraction field. -/
def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
    obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    · dsimp
      apply le_trans _ (le_max_left _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      congr 1; ring
    · apply le_trans _ (le_max_right _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      congr 1; ring
#align valuation_ring.valuation ValuationRing.valuation

theorem mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebraMap A K a = x := by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def, mul_one]
#align valuation_ring.mem_integer_iff ValuationRing.mem_integer_iff

/-- The valuation ring `A` is isomorphic to the ring of integers of its associated valuation. -/
noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (algebraMap (valuation A K).integer K) at h
        exact IsFractionRing.injective _ _ h
      · rintro ⟨-, ha⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        exact ⟨a, rfl⟩)
#align valuation_ring.equiv_integer ValuationRing.equivInteger

@[simp]
theorem coe_equivInteger_apply (a : A) : (equivInteger A K a : K) = algebraMap A K a := rfl
#align valuation_ring.coe_equiv_integer_apply ValuationRing.coe_equivInteger_apply

theorem range_algebraMap_eq : (valuation A K).integer = (algebraMap A K).range := by
  ext; exact mem_integer_iff _ _ _
#align valuation_ring.range_algebra_map_eq ValuationRing.range_algebraMap_eq

end

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

instance (priority := 100) localRing : LocalRing A :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self
    (by
      intro a
      obtain ⟨c, h | h⟩ := ValuationRing.cond a (1 - a)
      · left
        apply isUnit_of_mul_eq_one _ (c + 1)
        simp [mul_add, h]
      · right
        apply isUnit_of_mul_eq_one _ (c + 1)
        simp [mul_add, h])

instance [DecidableRel ((· ≤ ·) : Ideal A → Ideal A → Prop)] : LinearOrder (Ideal A) :=
  { (inferInstance : CompleteLattice (Ideal A)) with
    le_total := by
      intro α β
      by_cases h : α ≤ β; · exact Or.inl h
      erw [not_forall] at h
      push_neg at h
      obtain ⟨a, h₁, h₂⟩ := h
      right
      intro b hb
      obtain ⟨c, h | h⟩ := ValuationRing.cond a b
      · rw [← h]
        exact Ideal.mul_mem_right _ _ h₁
      · exfalso; apply h₂; rw [← h]
        apply Ideal.mul_mem_right _ _ hb
    decidableLE := inferInstance }

end

section

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*}
variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem iff_dvd_total : ValuationRing R ↔ IsTotal R (· ∣ ·) := by
  classical
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := ValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := @IsTotal.total _ _ H a b <;> use c <;> simp
#align valuation_ring.iff_dvd_total ValuationRing.iff_dvd_total

theorem iff_ideal_total : ValuationRing R ↔ IsTotal (Ideal R) (· ≤ ·) := by
  classical
  refine ⟨fun _ => ⟨le_total⟩, fun H => iff_dvd_total.mpr ⟨fun a b => ?_⟩⟩
  have := @IsTotal.total _ _ H (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm
#align valuation_ring.iff_ideal_total ValuationRing.iff_ideal_total

variable (K)

theorem dvd_total [h : ValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x :=
  @IsTotal.total _ _ (iff_dvd_total.mp h) x y
#align valuation_ring.dvd_total ValuationRing.dvd_total

theorem unique_irreducible [ValuationRing R] ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq, or_self_iff] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this
#align valuation_ring.unique_irreducible ValuationRing.unique_irreducible

variable (R)

theorem iff_isInteger_or_isInteger :
    ValuationRing R ↔ ∀ x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact Or.inr
        ⟨s, eq_inv_of_mul_eq_one_left <| by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩
    · exact Or.inl ⟨s, by rwa [eq_div_iff, map_mul, mul_comm]⟩
  · intro H
    constructor
    intro a b
    by_cases ha : a = 0; · subst ha; exact ⟨0, Or.inr <| mul_zero b⟩
    by_cases hb : b = 0; · subst hb; exact ⟨0, Or.inl <| mul_zero a⟩
    replace ha := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
    replace hb := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
    obtain ⟨c, e⟩ | ⟨c, e⟩ := H (algebraMap R K a / algebraMap R K b)
    · rw [eq_div_iff hb, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm] at e
      exact ⟨c, Or.inr e⟩
    · rw [inv_div, eq_div_iff ha, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm c] at e
      exact ⟨c, Or.inl e⟩
#align valuation_ring.iff_is_integer_or_is_integer ValuationRing.iff_isInteger_or_isInteger

variable {K}

theorem isInteger_or_isInteger [h : ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  (iff_isInteger_or_isInteger R K).mp h x
#align valuation_ring.is_integer_or_is_integer ValuationRing.isInteger_or_isInteger

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
instance (priority := 100) [ValuationRing R] : IsBezout R := by
  classical
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  rw [Ideal.span_insert]
  rcases le_total (Ideal.span {x} : Ideal R) (Ideal.span {y}) with h | h
  · erw [sup_eq_right.mpr h]; exact ⟨⟨_, rfl⟩⟩
  · erw [sup_eq_left.mpr h]; exact ⟨⟨_, rfl⟩⟩

instance (priority := 100) [LocalRing R] [IsBezout R] : ValuationRing R := by
  classical
  refine iff_dvd_total.mpr ⟨fun a b => ?_⟩
  obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_isPrincipal a b
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show a ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show b ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨x, y, e'⟩ := Ideal.mem_span_pair.mp
      (show g ∈ Ideal.span {a * g, b * g} by rw [e]; exact Ideal.subset_span (by simp))
  rcases eq_or_ne g 0 with h | h
  · simp [h]
  have : x * a + y * b = 1 := by
    apply mul_left_injective₀ h; convert e' using 1 <;> ring
  cases' LocalRing.isUnit_or_isUnit_of_add_one this with h' h' <;> [left; right]
  all_goals exact mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right h') _) _

theorem iff_local_bezout_domain : ValuationRing R ↔ LocalRing R ∧ IsBezout R :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
#align valuation_ring.iff_local_bezout_domain ValuationRing.iff_local_bezout_domain

protected theorem tFAE (R : Type u) [CommRing R] [IsDomain R] :
    List.TFAE
      [ValuationRing R,
        ∀ x : FractionRing R, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹,
        IsTotal R (· ∣ ·), IsTotal (Ideal R) (· ≤ ·), LocalRing R ∧ IsBezout R] := by
  tfae_have 1 ↔ 2; · exact iff_isInteger_or_isInteger R _
  tfae_have 1 ↔ 3; · exact iff_dvd_total
  tfae_have 1 ↔ 4; · exact iff_ideal_total
  tfae_have 1 ↔ 5; · exact iff_local_bezout_domain
  tfae_finish
#align valuation_ring.tfae ValuationRing.tFAE

end

theorem _root_.Function.Surjective.valuationRing {R S : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f) :
    ValuationRing S :=
  ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := ValuationRing.cond a b
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩
#align function.surjective.valuation_ring Function.Surjective.valuationRing

section

variable {𝒪 : Type u} {K : Type v} {Γ : Type w} [CommRing 𝒪] [IsDomain 𝒪] [Field K] [Algebra 𝒪 K]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (hh : v.Integers 𝒪)

/-- If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring. -/
theorem of_integers : ValuationRing 𝒪 := by
  constructor
  intro a b
  rcases le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inr hc.symm
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inl hc.symm
#align valuation_ring.of_integers ValuationRing.of_integers

end

section

variable (K : Type u) [Field K]

/-- A field is a valuation ring. -/
instance (priority := 100) of_field : ValuationRing K := by
  constructor
  intro a b
  by_cases h : b = 0
  · use 0; left; simp [h]
  · use a * b⁻¹; right; field_simp
#align valuation_ring.of_field ValuationRing.of_field

end

section

variable (A : Type u) [CommRing A] [IsDomain A] [DiscreteValuationRing A]

/-- A DVR is a valuation ring. -/
instance (priority := 100) of_discreteValuationRing : ValuationRing A := by
  constructor
  intro a b
  by_cases ha : a = 0; · use 0; right; simp [ha]
  by_cases hb : b = 0; · use 0; left; simp [hb]
  obtain ⟨ϖ, hϖ⟩ := DiscreteValuationRing.exists_irreducible A
  obtain ⟨m, u, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n, v, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rcases le_total m n with h | h
  · use (u⁻¹ * v : Aˣ) * ϖ ^ (n - m); left
    simp_rw [mul_comm (u : A), Units.val_mul, ← mul_assoc, mul_assoc _ (u : A)]
    simp only [Units.mul_inv, mul_one, mul_comm _ (v : A), mul_assoc, ← pow_add]
    congr 2
    exact Nat.add_sub_of_le h
  · use (v⁻¹ * u : Aˣ) * ϖ ^ (m - n); right
    simp_rw [mul_comm (v : A), Units.val_mul, ← mul_assoc, mul_assoc _ (v : A)]
    simp only [Units.mul_inv, mul_one, mul_comm _ (u : A), mul_assoc, ← pow_add]
    congr 2
    exact Nat.add_sub_of_le h
#align valuation_ring.of_discrete_valuation_ring ValuationRing.of_discreteValuationRing

end

end ValuationRing
