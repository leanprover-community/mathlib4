module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Int

@[expose] public section

theorem IsPrimitiveRoot.eq_neg_one_of_two_right' {R : Type*} [CommRing R] [NoZeroDivisors R]
    {ζ : Rˣ} (h : IsPrimitiveRoot ζ 2) : ζ = -1 := by
  simp [Units.ext_iff, (IsPrimitiveRoot.coe_units_iff.mpr h).eq_neg_one_of_two_right]

theorem Units.neg_one_zpow (M : Type*) [Monoid M] [HasDistribNeg M] (n : ℤ) :
    (-1 : Mˣ) ^ n = if Even n then 1 else -1 := by
  have {m : ℤ} : (-1 : Mˣ) ^ (2 * m) = 1 := by
    rw [zpow_mul, zpow_ofNat, neg_one_pow_two, one_zpow]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [← two_mul, this]
  · rw [Int.not_even_iff_odd] at h
    obtain ⟨m, rfl⟩ := h
    rw [zpow_add, this, one_mul, zpow_one]

theorem Int.exists_nat_eq_ideal_quot {I : Ideal ℤ} (hI : I ≠ ⊥) (x : ℤ ⧸ I) :
    ∃ a : ℕ, a < Ideal.absNorm I ∧ x = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha₁, ha₂⟩ := Int.existsUnique_equiv_nat b
    (Int.natCast_pos.mpr <| Nat.ne_zero_iff_zero_lt.mp <| Ideal.absNorm_eq_zero_iff.not.mpr hI)
  refine ⟨a, by rwa [Nat.cast_lt] at ha₁, ?_⟩
  change Ideal.Quotient.mk I b = Ideal.Quotient.mk I a
  rwa [← Int.ideal_span_absNorm_eq_self I, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    Ideal.mem_span_singleton, ← Int.modEq_iff_dvd]

open Ideal

variable {p : ℕ} [NeZero p] {A R : Type*} [CommRing A] [CommRing R] (P : Ideal A)

local notation3 "𝒑" => span {(p : ℤ)}

variable {ζ : R} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] Ideal.Quotient.field

@[simps]
noncomputable def addCharTrace [P.LiesOver 𝒑] : AddChar (A ⧸ P) R where
  toFun x :=
    Quotient.liftOn' (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)
      (fun x ↦ ((hζ.isUnit (NeZero.ne p)).unit ^ x).val)
      (fun x y hxy ↦ by
        rwa [Units.val_inj, ← orderOf_dvd_sub_iff_zpow_eq_zpow,
          ← IsPrimitiveRoot.eq_orderOf (hζ.isUnit_unit (NeZero.ne p)), ← mem_span_singleton,
          ← Submodule.quotientRel_def])
  map_zero_eq_one' := by
    rw [map_zero, show (0 : ℤ ⧸ 𝒑) = ⟦0⟧ by rfl, Quotient.liftOn'_mk 0, zpow_zero, Units.val_one]
  map_add_eq_mul' x y := by
    rw [map_add]
    refine Quotient.inductionOn₂' ((Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P)) x)
      ((Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P)) y) fun _ _ ↦ ?_
    rw [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk''_eq_mk, Quotient.liftOn'_mk, zpow_add, Units.val_mul,
      ← Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk''_eq_mk, Quotient.liftOn'_mk,
      Quotient.liftOn'_mk]

theorem addCharTrace_apply' [P.LiesOver 𝒑] {a : ℤ} {x : A ⧸ P}
    (ha : Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = Ideal.Quotient.mk 𝒑 a) :
    addCharTrace P hζ x = ((hζ.isUnit (NeZero.ne p)).unit ^ a : Rˣ) := by
  rw [addCharTrace_apply, ha, ← Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk,
    Quotient.liftOn'_mk]

theorem addCharTrace_apply_eq_one_iff [P.LiesOver 𝒑] {x : A ⧸ P} :
    addCharTrace P hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = 0 := by
  rw [addCharTrace_apply]
  nth_rewrite 1 [← Ideal.Quotient.mk_out (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)]
  rw [← Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk, Quotient.liftOn'_mk, Units.val_eq_one,
    ← orderOf_dvd_iff_zpow_eq_one, ← IsPrimitiveRoot.eq_orderOf (hζ.isUnit_unit (NeZero.ne p)),
    ← Quotient.eq_zero_iff_dvd, Ideal.Quotient.mk_out]

theorem addCharTrace_apply'_of_two [NoZeroDivisors R] (hζ : IsPrimitiveRoot ζ 2)
    [P.LiesOver (span {(2 : ℤ)})] (a : ℤ) (x : A ⧸ P)
    (ha : Algebra.trace (ℤ ⧸ span {(2 : ℤ)}) (A ⧸ P) x = Ideal.Quotient.mk (span {(2 : ℤ)}) a) :
    addCharTrace P hζ x = if Even a then 1 else -1 := by
  rw [addCharTrace_apply' P hζ ha, (hζ.isUnit_unit two_ne_zero).eq_neg_one_of_two_right',
    Units.neg_one_zpow, apply_ite Units.val, Units.val_neg, Units.val_one]

theorem addCharTrace_ne_zero [P.LiesOver 𝒑] [𝒑.IsMaximal] [Module.Free (ℤ ⧸ 𝒑) (A ⧸ P)]
    (h : ¬ p ∣ 𝒑.inertiaDeg P) :
    addCharTrace P hζ ≠ 0 := by
  refine AddChar.ne_zero_iff.mpr ⟨algebraMap (ℤ ⧸ 𝒑) (A ⧸ P) 1, ?_⟩
  rwa [ne_eq, addCharTrace_apply_eq_one_iff, Algebra.trace_algebraMap, nsmul_one,
    ← inertiaDeg_algebraMap, ← map_natCast' (Ideal.Quotient.mk 𝒑) rfl, Quotient.eq_zero_iff_dvd,
    Int.natCast_dvd_natCast]

theorem addCharTrace_ne_one [P.LiesOver 𝒑] [𝒑.IsMaximal] [P.IsMaximal]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] [Algebra.IsSeparable (ℤ ⧸ 𝒑) (A ⧸ P)] :
    addCharTrace P hζ ≠ 1 := by
  rw [AddChar.ne_one_iff]
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) (A ⧸ P)
  exact ⟨x, by rwa [ne_eq, addCharTrace_apply_eq_one_iff]⟩

theorem addCharTrace_frob [hp : Fact (p.Prime)] [P.IsMaximal] [P.LiesOver 𝒑] [Finite (A ⧸ P)]
    (x : A ⧸ P) :
    addCharTrace P hζ (x ^ p) = addCharTrace P hζ x := by
  have : CharP (A ⧸ P) p := ringChar.of_eq <| by simp [Ideal.ringChar_quot, ← over_def P 𝒑]
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  have : x ^ p = FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) (A ⧸ P) p x := by
    rw [FiniteField.frobeniusAlgEquiv_apply, ← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [addCharTrace_apply, addCharTrace_apply, this, Algebra.trace_eq_of_algEquiv]

theorem isPrimitive_addCharTrace [P.LiesOver 𝒑] [𝒑.IsMaximal] [P.IsMaximal]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] [Algebra.IsSeparable (ℤ ⧸ 𝒑) (A ⧸ P)] :
    (addCharTrace P hζ).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (addCharTrace_ne_one P hζ)

theorem exists_nat_addCharTrace_eq_sum_pow [P.LiesOver 𝒑] (x : A ⧸ P) :
    ∃ a : ℕ, (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P)) x = a ∧
      addCharTrace P hζ x =
        ∑ n ∈ Finset.range (a + 1), ((ζ - 1) ^ n * ↑(a.choose n)) := by
  obtain ⟨a, -, ha⟩ := Int.exists_nat_eq_ideal_quot
    (by simp [NeZero.ne p]) (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)
  rw [addCharTrace_apply' P hζ (a := a) (by simp [ha])]
  refine ⟨a, ha, ?_⟩
  rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  nth_rewrite 1 [show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp_rw [one_pow, mul_one]

theorem addCharTrace_mk [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A ⧸ P) :
    Ideal.Quotient.mk 𝓟 (addCharTrace P hζ x) = 1 := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_addCharTrace_eq_sum_pow P hζ x
  rw [ha', map_sum]
  cases a
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, map_one]
    intro _ _
    rw [map_mul]
    apply mul_eq_zero_of_left
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_add, pow_one]
    exact Ideal.mul_mem_left _ _ h

theorem addCharTrace_comp_mk_eq_one [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) :
    (Ideal.Quotient.mk 𝓟).compAddChar (addCharTrace P hζ) = 1 := by
  rw [AddChar.eq_one_iff]
  intro _
  rw [MonoidHom.compAddChar_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Function.comp_apply]
  exact addCharTrace_mk P hζ h _

theorem addCharTrace_mk_sq [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A ⧸ P)
    [(𝓟 ^ 2).LiesOver 𝒑] :
    Ideal.Quotient.mk (𝓟 ^ 2) (addCharTrace P hζ x) =
      1 + Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x • Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1) := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_addCharTrace_eq_sum_pow P hζ x
  rw [ha', map_sum]
  cases a
  · aesop
  · rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp [ha, add_comm, Algebra.smul_def, mul_comm]
    · intro _ _
      rw [map_mul]
      apply mul_eq_zero_of_left
      rw [Ideal.Quotient.eq_zero_iff_mem, add_assoc, pow_add]
      exact Ideal.mul_mem_left _ _ <| Submodule.pow_mem_pow 𝓟 h 2
