module

public import Mathlib

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

open Ideal

variable {p : ℕ} [NeZero p] {A : Type*} [CommRing A] [Algebra ℤ A] (P : Ideal A)

local notation3 "𝒑" => span {(p : ℤ)}

variable {ζ : A} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] Ideal.Quotient.field

@[simps]
noncomputable def addCharTrace [P.LiesOver 𝒑] : AddChar (A ⧸ P) A where
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
    addCharTrace P hζ x = ((hζ.isUnit (NeZero.ne p)).unit ^ a : Aˣ) := by
  rw [addCharTrace_apply, ha, ← Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk,
    Quotient.liftOn'_mk]

theorem addCharTrace_apply_eq_one_iff [P.LiesOver 𝒑] {x : A ⧸ P} :
    addCharTrace P hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = 0 := by
  rw [addCharTrace_apply]
  nth_rewrite 1 [← Ideal.Quotient.mk_out (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)]
  rw [← Quotient.mk_eq_mk, ← Submodule.Quotient.mk''_eq_mk, Quotient.liftOn'_mk, Units.val_eq_one,
    ← orderOf_dvd_iff_zpow_eq_one, ← IsPrimitiveRoot.eq_orderOf (hζ.isUnit_unit (NeZero.ne p)),
    ← Quotient.eq_zero_iff_dvd, Ideal.Quotient.mk_out]

theorem addCharTrace_apply'_of_two [NoZeroDivisors A] (hζ : IsPrimitiveRoot ζ 2)
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

-- Psi_frob
