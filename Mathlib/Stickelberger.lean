import Mathlib
import Mathlib.Misc
import Mathlib.Cyclotomic

noncomputable section

namespace Stickelberger

open MonoidAlgebra

variable (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
  [IsMulCommutative (K ≃ₐ[ℚ] K)]

local notation3 "G" => (K ≃ₐ[ℚ] K)

local notation3 "ℚ[G]" => MonoidAlgebra ℚ G

local notation3 "ℤ[G]" => MonoidAlgebra ℤ G

/-- Docstring. -/
local instance : Algebra ℤ[G] ℚ[G] := (mapRangeRingHom G (Int.castRingHom ℚ)).toAlgebra

@[simp]
theorem algebraMap_apply (z : ℤ[G]) (σ : G) : algebraMap ℤ[G] ℚ[G] z σ = z σ := by
  simp [RingHom.algebraMap_toAlgebra]

@[simp]
theorem algebraMap_single (z : ℤ) (σ : G) :
    algebraMap ℤ[G] ℚ[G] (single σ z) = single σ (z : ℚ) := by
  simp [RingHom.algebraMap_toAlgebra]

@[simp]
theorem single_smul_single (z : ℤ) (q : ℚ) (σ τ : G) :
    single σ z • single τ q = single (σ * τ) (z * q) := by
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

@[simp]
theorem single_smul_one (z : ℤ) (σ : G) : single σ z • (1 : ℚ[G]) = single σ (z : ℚ) := by
  simp [one_def]

omit [IsMulCommutative G] in
theorem smul_single (z : ℤ) (q : ℚ) (σ : G) :
    z • single σ q = single σ (z * q) := by
  rw [Algebra.smul_def, algebraMap_int_eq, eq_intCast, MonoidAlgebra.intCast_def,
    single_mul_single, one_mul]

theorem mem_ZG_iff {x : ℚ[G]} :
    x ∈ (1 : Submodule ℤ[G] ℚ[G]) ↔ ∀ σ, ∃ n : ℤ, x σ = n := by
  simp [MonoidAlgebra.ext_iff]
---  simp only [RingHom.mem_range, MonoidAlgebra.ext_iff, mapRangeRingHom_apply, eq_intCast]
  constructor
  · rintro ⟨z, hz⟩ σ
    exact ⟨z σ, (hz σ).symm⟩
  · intro h
    refine ⟨?_, ?_⟩
    · exact Finsupp.equivFunOnFinite.symm fun σ ↦ (h σ).choose
    · exact fun σ ↦ by simpa using (h σ).choose_spec.symm

variable {m K} in
/--
Docstring.
-/
def ν : G ≃* (ZMod m)ˣ :=
  IsCyclotomicExtension.autEquivPow K <| Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

variable {K} in
/--
Docstring.
-/
abbrev nν : G → ℕ := fun σ ↦ ((ν σ).val : ZMod m).val

omit [IsMulCommutative G] in
theorem nν_mul (σ τ : G) :
    (nν m (σ * τ) / m : ℚ) = Int.fract ((nν m σ) * (nν m τ) / m : ℚ) := by
  rw [← Nat.cast_mul]
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  rw [← ZMod.val_mul, ← Units.val_mul, ← map_mul]

/--
Docstring.
-/
abbrev Stick : ℚ[G] := ∑ σ : G, single σ (nν m σ⁻¹ / m)

@[simp]
theorem Stick_apply (σ : G) :
    Stick m K σ = nν m σ⁻¹ / m := by
  classical
  rw [Finset.sum_apply']
  simp [single_apply]

theorem smul_Stick_mem_ZG :
    (m : ℤ[G]) • Stick m K ∈ (1 : Submodule ℤ[G] ℚ[G]) := by
  rw [mem_ZG_iff]
  intro _
  refine ⟨?_, ?_⟩
  rotate_left
  · rw [natCast_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mapRangeRingHom_single]
    rw [single_mul_apply, inv_one, one_mul, Stick_apply, map_natCast]
    rw [mul_div_cancel₀ _ (NeZero.ne _)]
    rfl

theorem single_mul_Stick (τ : G) (q : ℚ) :
    single τ q * Stick m K = ∑ σ, single σ (q * nν m (τ * σ⁻¹) / m : ℚ) := by
  simp_rw [Finset.mul_sum, single_mul_single]
  rw [← Equiv.sum_comp (Equiv.mulRight τ⁻¹)]
  exact Fintype.sum_congr  _ _ fun _ ↦ by simp [mul_div]

theorem single_sub_one_mul_Stick (τ : G) :
    (single τ (1 : ℤ) - single 1 (nν m τ : ℤ)) • Stick m K =
      (∑ σ : G, single σ (-⌊(nν m τ * nν m σ⁻¹ : ℚ) / m⌋)) • 1 := by
  rw [Algebra.smul_def, map_sub, algebraMap_single, algebraMap_single]
  rw [sub_mul, single_mul_Stick, Finset.mul_sum, Finset.sum_smul]
  simp_rw [single_mul_single, one_mul, single_smul_one]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← single_sub, Int.cast_one, one_mul]
  simp_rw [nν_mul, ← mul_div_assoc]
  simp

/-- Docstring. -/
abbrev StickDen : Ideal ℤ[G] :=
  Ideal.span ({single 1 (m : ℤ)} ∪
    (Set.range fun σ ↦ single σ (1 : ℤ) - single 1 (nν m σ : ℤ)))

theorem mem_StickDen : (m : ℤ[G]) ∈ StickDen m K := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ rfl

theorem smul_Stick_mem_ZG_iff (x : ℤ[G]) :
    x • Stick m K ∈ (1 : Submodule ℤ[G] ℚ[G]) ↔ x ∈ StickDen m K := by
  classical
  constructor
  · intro h
    rw [mem_ZG_iff] at h
    have h₁ : (m : ℤ) ∣ ∑ σ, (x σ) * (nν m σ) := by
      obtain ⟨y, hy⟩ := h 1
      rw [← fintype_sum_single x] at hy
      simp_rw [Finset.smul_sum, Finset.sum_smul, single_smul_single] at hy
      rw [Finset.sum_apply'] at hy
      conv_lhs at hy =>
        enter [2, σ]
        rw [Finset.sum_apply']
        enter [2, τ]
        rw [single_apply, mul_eq_one_iff_eq_inv]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, reduceIte] at hy
      rw [← Equiv.sum_comp (Equiv.inv G)] at hy
      simp only [Equiv.inv_apply, inv_inv] at hy
      simp_rw [← mul_div_assoc] at hy
      rw [← Finset.sum_div, div_eq_mul_inv] at hy
      rw [mul_inv_eq_iff_eq_mul₀] at hy
      simp_rw [← Int.cast_natCast (R := ℚ), ← Int.cast_mul] at hy
      rw [← Int.cast_sum] at hy
      rw [Int.cast_inj, mul_comm] at hy
      refine ⟨y, hy⟩
      simp [NeZero.ne m]
    have h₂ : x = ∑ σ, (x σ : ℤ[G]) * (single σ (1 : ℤ) - single 1 (nν m σ : ℤ)) +
        (∑ σ, x σ * nν m σ : ℤ[G]) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [mul_sub, intCast_def, natCast_def, single_mul_single, one_mul, mul_one, Int.cast_eq,
        ZMod.natCast_val, Finsupp.single_mul, sub_add_cancel, fintype_sum_single]
    rw [h₂]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_smul_mem _ _ fun σ _ ↦ ?_
      apply Ideal.subset_span
      apply Set.mem_union_right
      exact Set.mem_range_self σ
    · simp_rw [← Int.cast_natCast (R := ℤ[G]), ← Int.cast_mul]
      rw [← Int.cast_sum]
      obtain ⟨q, hq⟩ := h₁
      rw [hq]
      simp only [Int.cast_mul, Int.cast_natCast]
      apply Ideal.mul_mem_right
      exact mem_StickDen m K
  · intro h
    induction h using Submodule.span_induction with
    | mem x h =>
      obtain ⟨_, rfl⟩ | ⟨σ, rfl⟩ := h
      · exact smul_Stick_mem_ZG m K
      · rw [single_sub_one_mul_Stick]
        exact Submodule.smul_mem _ _ <| Submodule.mem_one.mpr ⟨1, by rw [map_one]⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_smul]
      refine Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ hx

end Stickelberger

section GaussSums

open Ideal NumberField Units

attribute [local instance] Ideal.Quotient.field

variable (p f : ℕ) [NeZero (p ^ f - 1)] [NeZero f]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

variable {K : Type*} [Field K]

section Psi

variable {A : Type*} [CommRing A]

section T

variable (ζ : Aˣ) (hζ : IsPrimitiveRoot ζ p)

/-- Docstring. -/
abbrev T₀ : ℤ → A := fun a ↦ (ζ ^ a : Aˣ)

@[simp]
theorem T₀_apply (a : ℤ) :  T₀ ζ a = (ζ ^ a : Aˣ) := rfl

theorem T₀_neg (a : ℤ) : T₀ ζ (- a) = T₀ ζ⁻¹ a := by simp

theorem T₀_add (a b : ℤ) : T₀ ζ (a + b) = (T₀ ζ a) * (T₀ ζ b) := by
  rw [T₀_apply, T₀_apply, T₀_apply, zpow_add, Units.val_mul]

variable {ζ}

theorem T₀_eq_one_iff (hζ : IsPrimitiveRoot ζ p) {a : ℤ} : T₀ ζ a = 1 ↔ (p : ℤ) ∣ a := by
  rw [T₀_apply, Units.val_eq_one, hζ.zpow_eq_one_iff_dvd]

variable [NeZero p]

theorem T₀_eq_T₀_iff (hζ : IsPrimitiveRoot ζ p) {a b : ℤ} :
    T₀ ζ a = T₀ ζ b ↔ (p : ℤ) ∣ a - b := by
  simp [← (hζ.isUnit_unit (NeZero.ne _)).zpow_eq_one_iff_dvd, zpow_sub, _root_.mul_inv_eq_one,
    ← Units.val_inj]

theorem T₀_ne_zero {a : ℤ} [Nontrivial A] : T₀ ζ a ≠ 0 := ne_zero _

variable (ζ) in
theorem ideal_quot_mk_sq_T₀' (𝓟 : Ideal A) (h : ζ.val - 1 ∈ 𝓟) (a : ℕ) :
    Ideal.Quotient.mk (𝓟 ^ 2) (T₀ ζ a) = 1 + a • Ideal.Quotient.mk (𝓟 ^ 2) (ζ.val - 1) := by
  rw [T₀_apply, zpow_natCast, val_pow_eq_pow_val, map_pow]
  nth_rewrite 1 [show ζ.val = 1 + (ζ.val - 1) by ring]
  rw [map_add, add_comm, add_pow]
  cases a with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero (fun x hx ↦ ?_)]
    · simp only [map_sub, map_one, zero_add, pow_one, add_tsub_cancel_right, one_pow, mul_one,
        Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_zero, tsub_zero,
        Nat.choose_zero_right]
      ring
    · apply mul_eq_zero_of_left
      apply mul_eq_zero_of_left
      rw [← map_pow, Quotient.eq_zero_iff_mem, show x + 1 + 1 = 2 + x by ring, pow_add]
      exact Ideal.mul_mem_right _ _ <| Ideal.pow_mem_pow h 2

theorem T₀_apply_of_two' [NoZeroDivisors A] (hζ : IsPrimitiveRoot ζ 2) {a : ℕ} :
    T₀ ζ a = if Even a then 1 else -1 := by
  rw [T₀_apply, hζ.eq_neg_one_of_two_right', zpow_natCast, val_pow_eq_pow_val, Units.val_neg,
    val_one, neg_one_pow_eq_ite]

theorem T₀_apply_of_eq_two [NoZeroDivisors A] (hζ : IsPrimitiveRoot ζ 2) {a : ℤ} :
    T₀ ζ a = if Even a then 1 else -1 := by
  obtain ⟨a, (rfl | rfl)⟩ := Int.eq_nat_or_neg a
  · simp [T₀_apply_of_two' hζ, Int.even_coe_nat]
  · simp only [T₀_neg, T₀_apply_of_two' hζ.inv, even_neg, Int.even_coe_nat]

theorem T₀_quot_mk_sq (𝓟 : Ideal A) (h : ζ.val - 1 ∈ 𝓟) (a : ℤ) :
    Ideal.Quotient.mk (𝓟 ^ 2) (T₀ ζ a) =
      1 + a • Ideal.Quotient.mk (𝓟 ^ 2) (ζ.val - 1) := by
  obtain ⟨a, (rfl | rfl)⟩ := Int.eq_nat_or_neg a
  · exact_mod_cast ideal_quot_mk_sq_T₀' ζ 𝓟 h a
  · have h₀ : ζ⁻¹.val - 1 = - ζ⁻¹ * (ζ - 1) := by
      ring_nf
      rw [Units.inv_mul]
      ring
    have h₁ : ζ⁻¹.val - 1 ∈ 𝓟 := by
      rw [h₀]
      exact mul_mem_left 𝓟 (-↑ζ⁻¹) h
    have h₂ : ζ⁻¹.val - 1 + (ζ.val - 1) ∈ 𝓟 ^ 2 := by
      rw [h₀, ← add_one_mul, neg_add_eq_sub, ← neg_sub, neg_mul, Ideal.neg_mem_iff, sq]
      exact Submodule.mul_mem_mul h₁ h
    rw [T₀_neg, ideal_quot_mk_sq_T₀' ζ⁻¹ 𝓟 h₁, _root_.neg_smul, ← _root_.smul_neg, ← map_neg,
      nsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    congr 2
    rwa [Ideal.Quotient.eq, sub_neg_eq_add]

-- variable (ζ) in
-- theorem ideal_quot_mk_T₀' (𝓟 : Ideal A) (h : ζ.val - 1 ∈ 𝓟) (a : ℕ) :
--     Ideal.Quotient.mk 𝓟 (T₀ ζ a) = 1 := by
--   suffices (Ideal.Quotient.mk 𝓟) ζ = 1 by
--     rw [T₀_apply, zpow_natCast, val_pow_eq_pow_val, map_pow, this, one_pow]
--   rwa [← RingHom.map_one (Ideal.Quotient.mk 𝓟 ), Ideal.Quotient.eq]

-- include hζ in
-- attribute [local instance] Ideal.Quotient.field in
-- theorem ideal_quot_mk_T₀' [IsDedekindDomain A] [Module.Free ℤ A] [Module.Finite ℤ A] (𝓟 : Ideal A)
--     [𝓟.LiesOver 𝒑] [𝓟.IsMaximal] (a : ℕ) (hp : Nat.Prime p) :
--     Ideal.Quotient.mk 𝓟 (T₀ ζ a) = 1 := by
--   have : Fact (p.Prime) := ⟨hp⟩
--   rw [T₀_apply, zpow_natCast, val_pow_eq_pow_val, map_pow]
--   have : (Ideal.Quotient.mk 𝓟) ↑ζ = 1 := by
--     have := orderOf_dvd_natCard (G := (A ⧸ 𝓟)ˣ) (Units.map (Ideal.Quotient.mk 𝓟) ζ)
--     rwa [Nat.card_units, ← Submodule.cardQuot_apply, ← absNorm_apply,
--         absNorm_eq_pow_inertiaDeg' _ hp, Nat.dvd_sub_iff_right, Nat.dvd_one, orderOf_eq_one_iff,
--         Units.ext_iff, coe_map, MonoidHom.coe_coe, val_one] at this
--     · exact NeZero.one_le
--     · have := orderOf_map_dvd (Units.map (Ideal.Quotient.mk 𝓟).toMonoidHom) ζ
--       rw [← hζ.eq_orderOf] at this
--       refine Nat.dvd_trans this (dvd_pow_self _ ?_)
--       exact inertiaDeg_ne_zero _ _
--   rw [this, one_pow]

-- theorem ideal_quot_mk_T₀ (𝓟 : Ideal A) (h : ζ.val - 1 ∈ 𝓟) (a : ℤ) :
--     Ideal.Quotient.mk 𝓟 (T₀ ζ a) = 1 := by
--   obtain ⟨a, (rfl | rfl)⟩ := Int.eq_nat_or_neg a
--   · exact ideal_quot_mk_T₀' ζ 𝓟 h a
--   · rw [T₀_neg]
--     refine ideal_quot_mk_T₀' ζ⁻¹ 𝓟 ?_ a
--     rw [show ((ζ⁻¹ : Aˣ) : A) - 1 = -ζ⁻¹ * (ζ - 1) by ring_nf; rw [Units.inv_mul]; ring]
--     exact mul_mem_left 𝓟 _ h

variable {p}

/-- Docstring. -/
def T₁ (hζ : IsPrimitiveRoot ζ p) : ℤ ⧸ 𝒑 → A := by
  intro x
  refine Quotient.liftOn' x (fun x ↦ T₀ ζ x) fun a b h ↦ ?_
  rwa [Submodule.quotientRel_def, mem_span_singleton, ← T₀_eq_T₀_iff p hζ] at h

theorem T₁_apply (x : ℤ) (a : ℤ ⧸ 𝒑) (h : Ideal.Quotient.mk 𝒑 x = a) :
    T₁ hζ a = T₀ ζ x := by
  rw [← h]
  rfl

theorem T₁_apply' (a : ℤ ⧸ 𝒑) :
    T₁ hζ a = T₀ ζ (Quotient.out a) :=
  T₁_apply hζ _ _ <| Ideal.Quotient.mk_out a

theorem T₁_apply_of_eq_two [NoZeroDivisors A] (hζ : IsPrimitiveRoot ζ 2) (b : ℤ) (a : ℤ ⧸ span {2})
    (h : Ideal.Quotient.mk (span {2}) b = a) :
    T₁ hζ a = if Even b then 1 else -1 := by
  rw [T₁_apply _ _ _ h, T₀_apply_of_eq_two hζ]

theorem T₁_add (a b : ℤ ⧸ 𝒑) : T₁ hζ (a + b) = (T₁ hζ a) * (T₁ hζ b) := by
  rw [T₁_apply' _ a, T₁_apply' _ b, ← T₀_add, T₁_apply]
  rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]

theorem T₁_zero : T₁ hζ 0 = 1 := by
  rw [T₁_apply hζ 0 0, (T₀_eq_one_iff p hζ).mpr (Int.dvd_zero ↑p)]
  rfl

theorem T₁_injective : Function.Injective (T₁ hζ) := by
  intro _ _ h
  rwa [T₁_apply', T₁_apply', T₀_eq_T₀_iff p hζ, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq,
    Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h

theorem T₁_eq_one_iff {a : ℤ ⧸ 𝒑} : T₁ hζ a = 1 ↔ a = 0 := by
  rw [← T₁_zero (p := p)]
  exact (T₁_injective hζ).eq_iff

theorem T₁_quot_mk_sq (𝓟 : Ideal A) [Algebra (ℤ ⧸ 𝒑) (A ⧸ 𝓟 ^ 2)] (h : ζ.val - 1 ∈ 𝓟) (a : ℤ ⧸ 𝒑) :
    Ideal.Quotient.mk (𝓟 ^ 2) (T₁ hζ a) = 1 + a • Ideal.Quotient.mk (𝓟 ^ 2) (ζ.val - 1) := by
  rw [T₁_apply', T₀_quot_mk_sq _ h, Algebra.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply ℤ (ℤ ⧸ 𝒑) (A ⧸ 𝓟 ^ 2), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.mk_out]

end T

variable {p} [NeZero p] {ζ : A} (hζ : IsPrimitiveRoot ζ p) {K : Type*} [Field K] (P : Ideal (𝓞 K))

/--
Docstring.
-/
def Psi [P.LiesOver 𝒑] : AddChar (𝓞 K ⧸ P) A := {
  toFun := fun x ↦ T₁ (hζ.isUnit_unit (NeZero.ne _)) <| Algebra.trace (ℤ ⧸ 𝒑) ((𝓞 K) ⧸ P) x
  map_zero_eq_one' := by simpa [map_zero] using T₁_zero _
  map_add_eq_mul' a b := by rw [map_add, T₁_add] }

theorem Psi_apply [P.LiesOver 𝒑] (x : 𝓞 K ⧸ P) :
    Psi hζ P x = T₁ (hζ.isUnit_unit (NeZero.ne _)) (Algebra.trace (ℤ ⧸ 𝒑) ((𝓞 K) ⧸ P) x) := by
  rfl

theorem Psi_apply' [P.LiesOver 𝒑] (a : ℤ) {x : 𝓞 K ⧸ P}
    (ha : Ideal.Quotient.mk 𝒑 a = Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) x) :
    Psi hζ P x = T₁ (hζ.isUnit_unit (NeZero.ne _)) (Ideal.Quotient.mk 𝒑 a) := by
  rw [Psi_apply, ← ha]

theorem Psi_apply_of_two [NoZeroDivisors A] [P.LiesOver (span {2} : Ideal ℤ)]
    (hζ : IsPrimitiveRoot ζ 2) (a : ℤ) {x : 𝓞 K ⧸ P}
    (ha : Ideal.Quotient.mk (span {2}) a = Algebra.trace (ℤ ⧸ span {2}) (𝓞 K ⧸ P) x) :
    Psi hζ P x = if Even a then 1 else -1 := by
  rw [Psi_apply' hζ P a ha, T₁_apply_of_eq_two]
  simp

theorem Psi_ne_zero [P.LiesOver 𝒑] [𝒑.IsMaximal] (h : ¬ p ∣ 𝒑.inertiaDeg P) : Psi hζ P ≠ 0 := by
  refine AddChar.ne_zero_iff.mpr ?_
  refine ⟨algebraMap (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) 1, ?_⟩
  simp only [Psi, AddChar.coe_mk]
  rw [Algebra.trace_algebraMap, ne_eq, T₁_eq_one_iff, nsmul_one, ← inertiaDeg_algebraMap]
  change ¬ Ideal.Quotient.mk 𝒑 (𝒑.inertiaDeg P) = 0
  rwa [Quotient.eq_zero_iff_dvd, Int.natCast_dvd_natCast]

theorem Psi_frob [NumberField K] [hp : Fact (p.Prime)] [P.IsMaximal] [P.LiesOver 𝒑] (x : 𝓞 K ⧸ P) :
    Psi hζ P (x ^ p) = Psi hζ P x := by
  unfold Psi
  have : ExpChar (𝓞 K ⧸ P) p :=
    expChar_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (ℤ ⧸ 𝒑) (𝓞 K ⧸ P)) p
  have : Finite (𝓞 K ⧸ P) := by
    refine finiteQuotientOfFreeOfNeBot P ?_
    apply 𝒑.ne_bot_of_liesOver_of_ne_bot (Int.ideal_span_ne_bot p) P
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  let e := FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) p
  have : x ^ p = e x := by
    simp only [FiniteField.frobeniusAlgEquiv_apply, e]
    rw [← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [AddChar.coe_mk, this, Algebra.trace_eq_of_algEquiv]

theorem Psi_ne_one [NumberField K] [hp : Fact (p.Prime)] [P.IsMaximal] [P.LiesOver 𝒑] :
    Psi hζ P ≠ 1 := by
  rw [AddChar.ne_one_iff]
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) (𝓞 K ⧸ P)
  exact ⟨x, by rwa [Psi, AddChar.coe_mk, ne_eq, T₁_eq_one_iff]⟩

theorem Psi_isPrimitive [NumberField K] [hp : Fact (p.Prime)] [P.IsMaximal] [P.LiesOver 𝒑] :
    (Psi hζ P).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  exact Psi_ne_one _ _

theorem Psi_quot_mk_sq [P.LiesOver 𝒑] (𝓟 : Ideal A) [Algebra (ℤ ⧸ 𝒑) (A ⧸ 𝓟 ^ 2)] (h : ζ - 1 ∈ 𝓟)
    (a : 𝓞 K ⧸ P) :
    Ideal.Quotient.mk (𝓟 ^ 2) (Psi hζ P a) =
      1 + Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) a • Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1) := by
  rw [Psi_apply' hζ P (Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) a).out, T₁_quot_mk_sq, IsUnit.unit_spec,
    Ideal.Quotient.mk_out]
  · simpa using h
  · rw [Ideal.Quotient.mk_out]

theorem Psi_comp_ideal_quot_eq_one [P.LiesOver 𝒑] (𝓟 : Ideal A) [Algebra (ℤ ⧸ 𝒑) (A ⧸ 𝓟 ^ 2)]
    (h : ζ - 1 ∈ 𝓟) :
    (Ideal.Quotient.mk 𝓟).compAddChar (Psi hζ P) = 1 := by
  rw [AddChar.eq_one_iff]
  intro x
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply]
  let _ : Algebra (A ⧸ 𝓟 ^ 2) (A ⧸ 𝓟) :=
    RingHom.toAlgebra <| Ideal.Quotient.factor <| Ideal.pow_le_self two_ne_zero
  have : IsScalarTower A (A ⧸ 𝓟 ^ 2) (A ⧸ 𝓟) :=
    IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply A (A ⧸ 𝓟 ^2) (A ⧸ 𝓟),
    Ideal.Quotient.algebraMap_eq, Psi_quot_mk_sq _ _ _ h, map_add, map_one, Algebra.smul_def,
    map_mul, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A (A ⧸ 𝓟 ^ 2) (A ⧸ 𝓟),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr h, mul_zero, add_zero]

theorem Psi_comp_ideal_quot_eq_one_of_two [NoZeroDivisors A] (hζ : IsPrimitiveRoot ζ 2)
    [P.LiesOver (span {2} : Ideal ℤ)] (𝓟 : Ideal A) [Nontrivial (A ⧸ 𝓟)]
    [𝓟.LiesOver (span {2} : Ideal ℤ)] :
    (Ideal.Quotient.mk 𝓟).compAddChar (Psi hζ P) = 1 := by
  rw [AddChar.eq_one_iff]
  intro x
  simp
  rw [Psi_apply_of_two P hζ _ (by rw [Ideal.Quotient.mk_out])]
  split_ifs
  · rw [map_one]
  · rw [map_neg, map_one, neg_one_eq_one_iff, Int.ringChar_idealQuot, ← over_def 𝓟 (span {2})]
    simp

end Psi

variable [hp : Fact (p.Prime)] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
  (P : Ideal (𝓞 K)) [P.IsMaximal]

omit [NeZero (p ^ f - 1)] in
theorem not_prime_dvd_pow_sub_one : ¬ p ∣ p ^ f - 1 := by
  refine (Nat.dvd_sub_iff_right NeZero.one_le ?_).not.mpr hp.out.not_dvd_one
  exact dvd_pow_self p (NeZero.ne f)

theorem inertiaDeg_eq [P.LiesOver 𝒑] : 𝒑.inertiaDeg P = f := by
  rw [IsCyclotomicExtension.Rat.inertiaDeg_of_not_dvd  _ _ _ (not_prime_dvd_pow_sub_one p f),
    ZMod.orderOf_mod_self_pow_sub_one (Nat.Prime.one_lt hp.out) (NeZero.pos f)]

theorem absNorm_eq [P.LiesOver 𝒑] : absNorm P = p ^ f := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp.out, inertiaDeg_eq p f]

local instance : Fintype (𝓞 K ⧸ P) := by
    have := Ideal.finiteQuotientOfFreeOfNeBot P ?_
    · exact Fintype.ofFinite (𝓞 K ⧸ P)
    refine Ring.ne_bot_of_isMaximal_of_not_isField inferInstance ?_
    exact RingOfIntegers.not_isField K

theorem card_quot [P.LiesOver 𝒑] : Fintype.card (𝓞 K ⧸ P) = p ^ f := by
  rw [← absNorm_eq p f P, absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

@[simps! apply]
def omega' [P.LiesOver 𝒑] : (rootsOfUnity (p ^ f - 1) (𝓞 K)) ≃* (𝓞 K ⧸ P)ˣ := by
  classical
  have hP : Fintype.card (𝓞 K ⧸ P)ˣ = p ^ f - 1 := by
    let _ := Ideal.Quotient.field P
    rw [Fintype.card_units, card_quot p f P]
  have : Function.Injective (P.rootsOfUnityMapQuot (p ^ f - 1)) := by
    apply Ideal.rootsOfUnityMapQuot_injective
    · rw [absNorm_eq p f P, ne_eq, Nat.pow_eq_one, not_or]
      exact ⟨Nat.Prime.ne_one hp.out, NeZero.ne _⟩
    · rw [absNorm_eq p f P, Nat.coprime_self_sub_right NeZero.one_le]
      exact Nat.coprime_one_right _
  refine MulEquiv.ofBijective (P.rootsOfUnityMapQuot (p ^ f - 1)) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · exact this
  · rw [hP]
    apply Units.card_rootsOfUnity
    rw [torsionOrder_eq_of_isCyclotomicExtension (p ^ f - 1)]
    aesop

abbrev omega [P.LiesOver 𝒑] := (omega' p f P).symm

theorem omega_apply [P.LiesOver 𝒑] (x : (𝓞 K ⧸ P)ˣ) :
    Ideal.Quotient.mk P ((omega p f P x : (𝓞 K)ˣ) : 𝓞 K) = x := by
  convert congr_arg Units.val (omega'_apply p f P (omega p f P x)).symm
  exact (MulEquiv.symm_apply_apply (omega p f P) x).symm

variable (L : Type*) [Field L] [Algebra K L] (𝓟 : Ideal (𝓞 L)) [𝓟.IsMaximal] -- [NeZero 𝓟]

open Classical in
def Omega [P.LiesOver 𝒑] : MulChar (𝓞 K ⧸ P) (𝓞 L) := {
  toFun := fun x ↦ if hx : IsUnit x then algebraMap (𝓞 K) (𝓞 L) (omega p f P hx.unit).val else 0
  map_one' := by simp
  map_mul' x y := by
    by_cases h : IsUnit (x * y)
    · obtain ⟨hx, hy⟩ := IsUnit.mul_iff.mp h
      rw [dif_pos h, dif_pos hx, dif_pos hy, IsUnit.unit_mul hx hy, map_mul, Subgroup.coe_mul,
        val_mul, map_mul]
    · obtain hx | hy := not_and_or.mp <| IsUnit.mul_iff.not.mp h
      · rw [dif_neg h, dif_neg hx, zero_mul]
      · rw [dif_neg h, dif_neg hy, mul_zero]
  map_nonunit' x hx := by rw [dif_neg hx] }

theorem Omega_zero [P.LiesOver 𝒑] :
    Omega p f P L 0 = 0 := by
  simp [Omega]

theorem Omega_inv_zero [P.LiesOver 𝒑] :
    (Omega p f P L)⁻¹ 0 = 0 := by
  rw [MulChar.inv_apply', inv_zero, Omega_zero]

@[simp]
theorem Omega_apply [P.LiesOver 𝒑] (x : (𝓞 K ⧸ P)ˣ) :
    Omega p f P L x = (algebraMap (𝓞 K) (𝓞 L)) (omega p f P x : (𝓞 K)ˣ) := by
  unfold Omega
  dsimp
  rw [dif_pos x.isUnit, IsUnit.unit_of_val_units]

theorem Omega_eq_one_iff [P.LiesOver 𝒑] (x : (𝓞 K ⧸ P)ˣ) :
    Omega p f P L x = 1 ↔ x = 1 := by simp

theorem Omega_pow_eq_one [P.LiesOver 𝒑] (x : (𝓞 K ⧸ P)ˣ) :
    Omega p f P L x ^ (p ^ f - 1) = 1 := by
  rw [Omega_apply, ← map_pow, ← rootsOfUnity.coe_pow, rootsOfUnity_pow_eq_one,
    OneMemClass.coe_one, val_one, map_one]

theorem IsPrimitiveRoot.exists_omega_eq [P.LiesOver 𝒑] {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ (p ^ f - 1)) :
    ∃ x : ((𝓞 K) ⧸ P)ˣ, Omega p f P L x = algebraMap (𝓞 K) (𝓞 L) ζ := by
  use omega' p f P hζ.toRootsOfUnity
  rw [Omega_apply, omega, MulEquiv.symm_apply_apply, IsPrimitiveRoot.val_toRootsOfUnity_coe]

theorem Omega_orderOf [P.LiesOver 𝒑] : orderOf (Omega p f P L) = p ^ f - 1 := by
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨?_, ?_⟩
  · rw [MulChar.eq_one_iff]
    intro x
    rw [MulChar.pow_apply_coe, Omega_pow_eq_one]
  · intro m hm₁ hm₂
    rw [MulChar.ne_one_iff]
    have hζ := IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K
    obtain ⟨x, hx⟩ := hζ.toInteger_isPrimitiveRoot.exists_omega_eq p f P L
    refine ⟨x, ?_⟩
    rw [MulChar.pow_apply_coe, hx]
    have : IsPrimitiveRoot ((algebraMap (𝓞 K) (𝓞 L)) hζ.toInteger) (p ^ f - 1) := by
      refine (IsPrimitiveRoot.map_iff_of_injective ?_).mpr ?_
      exact RingOfIntegers.algebraMap.injective K L
      exact IsPrimitiveRoot.toInteger_isPrimitiveRoot hζ
    rw [IsPrimitiveRoot.iff] at this
    · exact this.2 m hm₂ hm₁
    · exact NeZero.pos _

theorem Omega_pow_ne_one [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    (Omega p f P L) ^ a ≠ 1 := by
  rwa [ne_eq, ← orderOf_dvd_iff_zpow_eq_one, Omega_orderOf]

omit [𝓟.IsMaximal] in
theorem Omega_mk_eq [(𝓟 ^ 2).LiesOver P] [P.LiesOver 𝒑] (x : 𝓞 K ⧸ P) :
    Ideal.Quotient.mk (𝓟 ^ 2) (Omega p f P L x) =
      algebraMap (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2) x := by
  by_cases hx : x = 0
  · rw [hx, Omega_zero, map_zero, map_zero]
  lift x to (𝓞 K ⧸ P)ˣ using Ne.isUnit hx
  rw [← Ideal.Quotient.algebraMap_eq, Omega_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K ⧸ P), Ideal.Quotient.algebraMap_eq, omega_apply]

omit [𝓟.IsMaximal] in
theorem Omega_inv_mk_eq [(𝓟 ^ 2).LiesOver P] [P.LiesOver 𝒑] (x : 𝓞 K ⧸ P) :
    Ideal.Quotient.mk (𝓟 ^ 2) ((Omega p f P L)⁻¹ x) =
      algebraMap (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2) x⁻¹ := by
  rw [MulChar.inv_apply', Omega_mk_eq]

theorem Omega_comp_ideal_quot_ne_one' (a : ℕ) [NumberField L] [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑]
    (ha : ¬↑(p ^ f - 1) ∣ a) :
    (Omega p f P L ^ (a : ℤ)).ringHomComp (Ideal.Quotient.mk 𝓟) ≠ 1 := by
  have ha' : a ≠ 0 := by aesop
  rw [MulChar.ne_one_iff]
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K
  obtain ⟨x, hx⟩ := hζ.toInteger_isPrimitiveRoot.exists_omega_eq p f P L
  refine ⟨x, fun h ↦ ?_⟩
  rw [MulChar.ringHomComp_apply, zpow_natCast, MulChar.pow_apply' _ ha', map_pow] at h
  rw [hx] at h
  have := IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one
    (n := (p ^ f - 1) / (p ^ f - 1).gcd a) ?_ ?_ ?_ h
  · rw [absNorm_eq_pow_inertiaDeg' 𝓟 hp.out] at this
    refine this ?_
    apply Nat.Coprime.coprime_div_right
    · apply  Nat.Coprime.pow_left
      rw [← Nat.coprime_pow_left_iff (NeZero.pos f), Nat.coprime_self_sub_right]
      · exact Nat.coprime_one_right _
      · exact NeZero.one_le
    · exact Nat.gcd_dvd_left _ _
  · rw [ne_eq, absNorm_eq_one_iff]
    exact IsPrime.ne_top'
  · apply Nat.two_le_div_of_dvd
    · exact Nat.gcd_dvd_left _ _
    · rw [ne_eq]
      rwa [Nat.gcd_eq_left_iff_dvd]
    · exact NeZero.ne _
  · refine IsPrimitiveRoot.pow_div_gcd ha' ?_
    refine IsPrimitiveRoot.coe_submonoidClass_iff.mpr ?_
    refine (IsPrimitiveRoot.map_iff_of_injective ?_).mpr ?_
    · exact FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
    · exact IsPrimitiveRoot.toInteger_isPrimitiveRoot hζ

theorem Omega_comp_ideal_quot_ne_one (a : ℤ) [NumberField L] [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑]
    (ha : ¬↑(p ^ f - 1) ∣ a) :
    (Omega p f P L ^ (a : ℤ)).ringHomComp (Ideal.Quotient.mk 𝓟) ≠ 1 := by
  obtain ⟨a, (rfl | rfl)⟩ := Int.eq_nat_or_neg a
  · exact Omega_comp_ideal_quot_ne_one' p f P L 𝓟 _ (by rwa [Int.natCast_dvd_natCast] at ha)
  · rw [zpow_neg, zpow_natCast, ne_eq, ← MulChar.ringHomComp_inv, inv_eq_one]
    refine Omega_comp_ideal_quot_ne_one' p f P L 𝓟 _ ?_
    rwa [dvd_neg, Int.natCast_dvd_natCast] at ha

variable {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)

abbrev GaussSum [P.LiesOver 𝒑] (a : ℤ) : (𝓞 L) := gaussSum (Omega p f P L ^ (- a)) (Psi hζ P)

theorem GaussSum_ne_zero [CharZero L] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GaussSum p f P L hζ a ≠ 0 := by
  refine gaussSum_ne_zero_of_nontrivial (by simp) ?_ (Psi_isPrimitive hζ P)
  exact Omega_pow_ne_one _ _ _ _ _ (by rwa [Int.dvd_neg])

theorem GaussSum_p_mul [P.LiesOver 𝒑] (a : ℤ) :
    GaussSum p f P L hζ (p * a) = GaussSum p f P L hζ a := by
  unfold GaussSum gaussSum
  have : ExpChar (𝓞 K ⧸ P) p :=
    expChar_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (ℤ ⧸ 𝒑) (𝓞 K ⧸ P)) p
  have : Finite (𝓞 K ⧸ P) := by
    refine finiteQuotientOfFreeOfNeBot P ?_
    apply 𝒑.ne_bot_of_liesOver_of_ne_bot (Int.ideal_span_ne_bot p) P
  nth_rewrite 2 [← Equiv.sum_comp (frobeniusEquiv ((𝓞 K) ⧸ P) p).toEquiv]
  simp_rw [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, frobeniusEquiv_apply, frobenius_def,
    Psi_frob, map_pow, ← MulChar.pow_apply' _ (NeZero.ne _), ← zpow_natCast, ← zpow_mul', mul_neg]

theorem GaussSum_mul_GaussSum_neg [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GaussSum p f P L hζ a * GaussSum p f P L hζ (-a) =
      (Omega p f P L ^ (-a)) (-1) * (p ^ f : ℕ) := by
  convert gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (χ := (Omega p f P L ^ (-a))) (ψ := Psi hζ P) ?_ (Psi_isPrimitive hζ P)
  · rw [← zpow_natCast, ← zpow_mul, Nat.cast_sub, mul_sub, Nat.cast_one, mul_one, neg_neg,
      sub_neg_eq_add, zpow_add, zpow_mul, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_refl _), one_mul]
    exact orderOf_pos _
  · rw [card_quot p f P]
  · rwa [ne_eq, ← orderOf_dvd_iff_zpow_eq_one, Omega_orderOf, Int.dvd_neg]

theorem GaussSum_pow_sub_one_sub [P.LiesOver 𝒑] (a : ℤ) :
    GaussSum p f P L hζ ((p ^ f - 1 : ℕ) - a) = GaussSum p f P L hζ (-a) := by
  unfold GaussSum
  rw [neg_sub, neg_neg, zpow_sub, zpow_natCast,
    orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq <| Omega_orderOf p f P L), inv_one, mul_one]

variable {L} in
abbrev Jac [P.LiesOver 𝒑] (a b : ℤ) : 𝓞 L := jacobiSum (Omega p f P L ^ (-a)) (Omega p f P L ^ (-b))

theorem GaussSum_mul_gaussSum [P.LiesOver 𝒑] {a b : ℤ} (h : ¬ ↑(p ^ f - 1 : ℕ) ∣ a + b) :
  GaussSum p f P L hζ a * GaussSum p f P L hζ b =
    GaussSum p f P L hζ (a + b) * Jac p f P a b := by
  unfold GaussSum
  rw [← jacobiSum_mul_nontrivial, neg_add, zpow_add]
  rwa [← zpow_add, ← neg_add, ne_eq, zpow_eq_one_iff_modEq, ← neg_zero, Int.neg_modEq_neg,
    Omega_orderOf, Int.modEq_zero_iff_dvd]

omit [𝓟.IsMaximal] in
set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 1500000 in
theorem GaussSum_one_mk_sq_eq [P.LiesOver 𝒑] [(𝓟 ^ 2).LiesOver P] (h : p ^ f ≠ 2)
    (h' : ζ - 1 ∈ 𝓟) :
    Ideal.Quotient.mk (𝓟 ^ 2) (GaussSum p f P L hζ 1) = -(Ideal.Quotient.mk (𝓟 ^ 2)) (ζ - 1) := by
  classical
  have : AddMonoidHomClass (𝓞 K ⧸ P →+* 𝓞 L ⧸ 𝓟 ^ 2) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2) :=
    RingHomClass.toNonUnitalRingHomClass.toAddMonoidHomClass
  have : (𝓟 ^ 2).LiesOver 𝒑 := LiesOver.trans (𝓟 ^ 2) P 𝒑
  have : IsScalarTower (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2) := by
    refine IsScalarTower.to₂₃₄ ℤ (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2) ?_
    simpa only [zsmul_eq_mul, mul_one, eq_intCast] using (Ideal.Quotient.mk_surjective (I := 𝒑))
  rw [GaussSum, gaussSum, map_sum]
  simp_rw [map_mul, Psi_quot_mk_sq _ _ _ h', mul_add, mul_one]
  rw [Finset.sum_add_distrib, ← map_sum, MulChar.sum_eq_zero_of_ne_one, map_zero, zero_add]
  · simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2),
      FiniteField.algebraMap_trace_eq_sum_pow, ← mul_assoc, zpow_neg_one, Omega_inv_mk_eq,
      ← map_mul, Finset.mul_sum, map_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [← map_sum, Int.card_ideal_quot p]
    have hsum₀ : ∑ a : 𝓞 K ⧸ P,  a⁻¹ * a = -1 := by
      rw [← Finset.univ.sum_erase (by rw [mul_zero]),
        Finset.sum_subtype (p := fun x ↦ x ≠ 0) _ (by grind), ← unitsEquivNeZero.sum_comp,
        Fintype.sum_congr _ (fun x ↦ x.val ^ 0) (by simp),
        FiniteField.sum_pow_units, if_pos (Nat.dvd_zero _)]
    have hsum₁ {s : Fin (f - 1)} : ∑ a : 𝓞 K ⧸ P,  a⁻¹ * a ^ (p ^ (s + 1 : ℕ)) = 0 := by
      rw [← FiniteField.sum_pow_lt_card_sub_one (𝓞 K ⧸ P) (p ^ (s + 1 : ℕ) - 1)]
      · refine Fintype.sum_congr _ _ fun x ↦ ?_
        by_cases hx : x = 0
        · rw [hx, inv_zero, zero_mul, zero_pow]
          exact Nat.sub_ne_zero_iff_lt.mpr <| lt_of_lt_of_le hp.out.one_lt (Nat.le_pow (by bound))
        · rw [inv_mul_eq_iff_eq_mul₀ hx, ← pow_succ', Nat.sub_add_cancel NeZero.one_le]
      · rw [card_quot p f, Nat.sub_lt_sub_iff_right NeZero.one_le]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by grind)
    rw [← Ideal.inertiaDeg_algebraMap, inertiaDeg_eq p f,
      show f = f - 1 + 1 by rw [Nat.sub_add_cancel NeZero.one_le], Finset.sum_range_succ',
      Finset.sum_range]
    simp_rw [hsum₁, pow_zero, pow_one]
    rw [Finset.sum_const_zero, zero_add, hsum₀]
    rw [map_neg, map_one, neg_one_mul]
  apply Omega_pow_ne_one
  rw [Int.dvd_neg, Int.natCast_dvd_ofNat, Nat.dvd_one]
  rwa [Nat.pred_eq_succ_iff, zero_add]

variable [NumberField L]

open IsDedekindDomain.HeightOneSpectrum

abbrev Val [NeZero 𝓟] : Valuation (𝓞 L) (WithZero (Multiplicative ℤ)) :=
  intValuation ⟨𝓟, IsMaximal.isPrime inferInstance, NeZero.ne _⟩

-- abbrev Val₀ (x : 𝓞 L) : ℤ := WithZero.log (Val L 𝓟 x)

-- abbrev AddVal : AddValuation (𝓞 L) (WithTop ℤ) := by
--   refine AddValuation.of ?_ ?_ ?_ ?_ ?_
--   · exact fun x ↦ ((Val L 𝓟 x)⁻¹ : WithZero (Multiplicative ℤ))
--   · simp
--     rfl
--   · simp
--     rfl
--   · intro x y

--     exact Valuation.map_add (Val L 𝓟) x y
--   · intro x y
--     exact  Valuation.map_mul (Val L 𝓟) x y
--  let e := AddValuation.ofValuation (Γ₀ := WithTop ℤ) (R := 𝓞 L)

theorem Val_Omega_pow [NeZero 𝓟] [P.LiesOver 𝒑] (a : ℕ) (x : (𝓞 K ⧸ P)ˣ) :
    Val L 𝓟 ((Omega p f P L ^ a) x) = 1 := by
  rw [← pow_left_inj₀ (n := p ^ f - 1) (WithZero.zero_le _) zero_le_one (NeZero.ne _), one_pow,
    ← Valuation.map_pow, MulChar.pow_apply_coe, ← pow_mul', pow_mul, Omega_pow_eq_one, one_pow,
    Valuation.map_one]

-- theorem Val₀_Omega_pow [P.LiesOver 𝒑] (a : ℕ) (x : (𝓞 K ⧸ P)ˣ) :
--     Val₀ L 𝓟 ((Omega p f P L ^ a) x) = 0 := by
--   unfold Val₀
--   apply WithZero.exp_injective
--   rw [← WithZero.log_inv, WithZero.exp_log]
--   rw [← pow_left_inj₀ (n := p ^ f - 1) (WithZero.zero_le _) zero_le_one (NeZero.ne _), one_pow,
--     ← Valuation.map_pow, MulChar.pow_apply_coe, ← pow_mul', pow_mul, Omega_pow_eq_one, one_pow,
--     Valuation.map_one]

theorem Val_Omega_zpow [NeZero 𝓟] [P.LiesOver 𝒑] (a : ℤ) (x : (𝓞 K ⧸ P)ˣ) :
    Val L 𝓟 ((Omega p f P L ^ a) x) = 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [zpow_natCast, Val_Omega_pow]
  · rw [zpow_neg, zpow_natCast, MulChar.inv_apply, Ring.inverse_unit, Val_Omega_pow]

variable {p L} in
abbrev GSV [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) :=
  haveI : NeZero 𝓟 := ⟨by
    have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
    exact ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using hp.out.ne_zero) _⟩
  Val L 𝓟 (GaussSum p f P L hζ a)

-- variable {p L} in
-- abbrev GSV₀ [P.LiesOver 𝒑] (a : ℤ) := Val₀ L 𝓟 (GaussSum p f P L hζ a)

-- theorem GSV₀_eq_GSV_log [P.LiesOver 𝒑] (a : ℤ) :
--     GSV₀ f P 𝓟 hζ a = (GSV f P 𝓟 hζ a).log := rfl

theorem GSV_eq_one_of_dvd [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) (h : ↑(p ^ f - 1) ∣ a) :
    GSV f P 𝓟 hζ a = 1 := by
  unfold GSV GaussSum
  rw [orderOf_dvd_iff_zpow_eq_one.mp (by rwa [Omega_orderOf, Int.dvd_neg]), gaussSum_one_left]
  by_cases h : Psi hζ P = 0
  · rw [if_pos h, ← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, Ideal.absNorm_eq_pow_inertiaDeg' P hp.out, Nat.cast_pow]
    rw [Valuation.map_sub_swap, Valuation.map_one_sub_of_lt]
    rw [intValuation_lt_one_iff_dvd]
    rw [dvd_span_singleton]
    refine pow_mem_of_mem 𝓟 ?_ (𝒑.inertiaDeg P) ?_
    · have : 𝓟.LiesOver (span {(p : ℤ)}) := LiesOver.trans 𝓟 P 𝒑
      simpa using Int.mem_ideal_of_liesOver_span p 𝓟
    · exact inertiaDeg_pos 𝒑 P
  · rw [if_neg h, Valuation.map_neg, Valuation.map_one]

-- theorem GSV₀_eq_zero_of_dvd [P.LiesOver 𝒑] [𝓟.LiesOver P] (a : ℤ) (h : ↑(p ^ f - 1 : ℕ) ∣ a) :
--     GSV₀ f P 𝓟 hζ a = 0 := by
--   rw [GSV₀_eq_GSV_log, GSV_eq_one_of_dvd _ _ _ _ _ _ _ h, WithZero.log_one]

theorem GSV_zero [𝓟.LiesOver P] [P.LiesOver 𝒑] : GSV f P 𝓟 hζ 0 = 1 := by
  apply GSV_eq_one_of_dvd
  exact Int.dvd_zero _

variable {f p P L 𝓟 hζ} in
theorem GSV_nonneg [𝓟.LiesOver P] [P.LiesOver 𝒑] {a : ℤ} :
    0 ≤ GSV f P 𝓟 hζ a := WithZero.zero_le _

variable {f p P L 𝓟 hζ} in
theorem GSV_le_one [𝓟.LiesOver P] [P.LiesOver 𝒑] {a : ℤ} :
    GSV f P 𝓟 hζ a ≤ 1 := intValuation_le_one _ _

/-- s(α + β) ≤ s(α) + s(β) -/
theorem GSV_mul_GSV_le [𝓟.LiesOver P] [P.LiesOver 𝒑] (a b : ℤ) :
    GSV f P 𝓟 hζ a * GSV f P 𝓟 hζ b ≤ GSV f P 𝓟 hζ (a + b) := by
  by_cases h : ↑(p ^ f - 1 : ℕ) ∣ a + b
  · rw [GSV_eq_one_of_dvd p f P L 𝓟 hζ (a + b) h, ← Valuation.map_mul]
    exact intValuation_le_one _ _
  · rw [← Valuation.map_mul, GaussSum_mul_gaussSum p f P L hζ h, Valuation.map_mul]
    exact mul_le_of_le_one_right GSV_nonneg (intValuation_le_one _ _)

/-- s(p * α) = s(α) -/
theorem GSV_p_mul [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) :
    GSV f P 𝓟 hζ (p * a) = GSV f P 𝓟 hζ a := by
  unfold GSV
  rw [GaussSum_p_mul]

include hζ in
theorem zeta_sub_one_mem [𝓟.LiesOver 𝒑] : ζ - 1 ∈ 𝓟 := by
  rw [← Ideal.Quotient.eq, map_one]
  have hp' : p ≠ 0 := hp.out.ne_zero
  have := orderOf_dvd_natCard (G := (𝓞 L ⧸ 𝓟)ˣ)
    (Units.map (Ideal.Quotient.mk 𝓟) (hζ.isUnit hp').unit)
  rwa [Nat.card_units, ← Submodule.cardQuot_apply, ← absNorm_apply,
    absNorm_eq_pow_inertiaDeg' _ hp.out, Nat.dvd_sub_iff_right,  Nat.dvd_one,
    orderOf_eq_one_iff, Units.ext_iff, coe_map, MonoidHom.coe_coe, val_one,
    IsUnit.unit_spec] at this
  · exact NeZero.one_le
  · have := orderOf_map_dvd (Units.map (Ideal.Quotient.mk 𝓟).toMonoidHom) (hζ.isUnit hp').unit
    refine Nat.dvd_trans this <| Nat.dvd_trans ?_ (dvd_pow_self _ (inertiaDeg_ne_zero _ _))
    rw [← (hζ.isUnit_unit hp').eq_orderOf]

open IntermediateField in
include hζ in
theorem zeta_sub_one_not_mem_sq [𝓟.LiesOver 𝒑] : ζ - 1 ∉ 𝓟 ^ 2 := by
  let F := ℚ⟮(ζ : L)⟯
  let μ := AdjoinSimple.gen ℚ (ζ : L)
  have hμ : IsPrimitiveRoot μ p := by
    refine IsPrimitiveRoot.coe_submonoidClass_iff.mp ?_
    exact hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  have := hμ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let Q := Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) 𝓟
  have : Q.IsPrime := IsPrime.under (𝓞 ↥F) 𝓟
  have : ζ - 1 = algebraMap (𝓞 F) (𝓞 L) (hμ.toInteger - 1) := sorry
  rw [this, ← Ideal.mem_comap, ← Ideal.dvd_span_singleton,
    ← IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver]



  have := Ideal.le_comap_pow (algebraMap (𝓞 F) (𝓞 L)) (K := 𝓟) 2
  rw [← Ideal.dvd_iff_le] at this





#exit

variable [hL : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

omit [NeZero (p ^ f - 1)] in
include hL in
theorem ramificationIdx_eq_sub_one [𝓟.LiesOver 𝒑] :
    ramificationIdx (algebraMap ℤ (𝓞 L)) 𝒑 𝓟 = p - 1 := by
  convert IsCyclotomicExtension.Rat.ramificationIdx_eq (p := p) (k := 0)
      (p * (p ^ f - 1)) L 𝓟 ?_ (not_prime_dvd_pow_sub_one p f) using 1
  · rw [pow_zero, one_mul]
  · simp

omit [NeZero (p ^ f - 1)] in
include hL in
theorem sq_liesOver [h : 𝓟.LiesOver 𝒑] (hp' : Odd p) :
    (𝓟 ^ 2).LiesOver 𝒑 := by
  apply Ideal.liesOver_pow_of_le_ramificationIdx _ _ one_le_two
  rw [ramificationIdx_eq_sub_one p f]
  exact Nat.sub_le_sub_right (hp.out.three_le_of_odd hp') 1

omit [NeZero (p ^ f - 1)] in
include hL in
theorem val_𝓟_p [𝓟.LiesOver 𝒑] :
    haveI : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using hp.out.ne_zero) _⟩
    Val L 𝓟 p = Multiplicative.ofAdd (-(p - 1) : ℤ) := by
  classical
  have hp' : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have hP : 𝓟 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp' _
  have h : Irreducible (Associates.mk 𝓟) := by
    rw [Associates.irreducible_mk, UniqueFactorizationMonoid.irreducible_iff_prime]
    exact prime_of_isPrime hP inferInstance
  rw [intValuation_apply, intValuationDef_if_neg _ (by simpa using hp.out.ne_zero),
    Associates.factors_mk _ (by simpa using hp.out.ne_zero), Associates.count_some h,
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, Associates.map_subtype_coe_factors',
    Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := Ideal (𝓞 L))),
    show span {(p : 𝓞 L)} = 𝒑.map (algebraMap ℤ (𝓞 L)) by simp [map_span],
    ← IsDedekindDomain.ramificationIdx_eq_factors_count (map_ne_bot_of_ne_bot hp') inferInstance hP,
    ramificationIdx_eq_sub_one p f L, Nat.cast_sub NeZero.one_le]
  rfl

theorem GSV_mul_GSV_sub_self' [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GSV f P 𝓟 hζ a * GSV f P 𝓟 hζ ((p ^ f - 1 : ℕ) - a) =
      Multiplicative.ofAdd (-(p - 1 : ℤ) * f) := by
  classical
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using hp.out.ne_zero) _⟩
  unfold GSV
  rw [← Valuation.map_mul, GaussSum_pow_sub_one_sub, GaussSum_mul_GaussSum_neg _ _ _ _ _ _ ha,
    Valuation.map_mul, ← Units.coe_neg_one, Val_Omega_zpow, one_mul, Nat.cast_pow,
    Valuation.map_pow, val_𝓟_p p f, Int.ofAdd_mul, zpow_natCast, WithZero.coe_pow]

theorem GSV_mul_GSV_sub_self [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) :
    GSV f P 𝓟 hζ a * GSV f P 𝓟 hζ ((p ^ f - 1 : ℕ) - a) =
      if ↑(p ^ f - 1) ∣ a then 1 else Multiplicative.ofAdd (-(p - 1 : ℤ) * f) := by
  split_ifs with h
  · rw [WithZero.coe_one, GSV_eq_one_of_dvd _ _ _ _ _ _ _ h, GSV_eq_one_of_dvd, mul_one]
    exact dvd_sub_self_left.mpr h
  · exact GSV_mul_GSV_sub_self' _ _ _ _ _ _ _ h

theorem prod_GSV [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    ∏ a ∈ Finset.range (p ^ f - 1).succ, GSV f P 𝓟 hζ a =
      Multiplicative.ofAdd (-(p ^ f - 2 : ℤ) * f * (p - 1) / 2) := by
  rw [← sq_eq_sq₀ (WithZero.zero_le _) (by simp), sq, ← Fin.prod_univ_eq_prod_range]
  nth_rewrite 2 [← Equiv.prod_comp Fin.revPerm]
  rw [← Finset.prod_mul_distrib]
  simp_rw [Fin.revPerm_apply, Fin.val_rev, Nat.reduceSubDiff, Nat.cast_sub (Fin.is_le _),
    GSV_mul_GSV_sub_self, apply_ite, WithZero.coe_one]
  rw [Fin.prod_univ_eq_prod_range
    (fun x ↦ (if ↑(p ^ f - 1) ∣ (x : ℤ) then (1 : WithZero (Multiplicative ℤ)) else
    ↑(Multiplicative.ofAdd (-(p - 1 : ℤ) * f)))) (p ^ f - 1).succ, Finset.prod_range_succ,
    ← Finset.mul_prod_erase _ _ (a := 0) (Finset.mem_range.mpr (NeZero.pos _)),
    if_pos (Int.dvd_refl _), if_pos (by simp), one_mul, mul_one]
  have : ∀ x ∈ (Finset.range (p ^ f - 1)).erase 0, ¬ (p ^ f - 1) ∣ x := by
    exact fun _ _ ↦ Nat.not_dvd_of_pos_of_lt (by grind) (by grind)
  simp_rw +contextual [Int.natCast_dvd_natCast, if_neg (this _ _)]
  rw [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_range, Nat.sub_sub,
    ← WithZero.coe_pow, ← WithZero.coe_pow, ← zpow_natCast, ← zpow_natCast, ← Int.ofAdd_mul,
    ← Int.ofAdd_mul, Nat.cast_ofNat, Int.ediv_mul_cancel, Nat.cast_sub, Nat.cast_pow]
  · grind
  · exact le_trans hp.out.two_le (Nat.le_pow (NeZero.pos f))
  · obtain rfl | hp' := hp.out.eq_two_or_odd'
    · apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_left
      rw [Nat.cast_ofNat, Int.dvd_neg, dvd_sub_self_right]
      exact dvd_pow_self 2 (NeZero.ne f)
    · apply dvd_mul_of_dvd_right
      rw [← even_iff_two_dvd]
      exact Odd.sub_odd ((Int.odd_coe_nat p).mpr hp') odd_one
  · exact Finset.mem_range.mpr (NeZero.pos _)

theorem GaussSum_mem [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GaussSum p f P L hζ a ∈ 𝓟 := by
  obtain rfl | hp' := hp.out.eq_two_or_odd'
  · unfold GaussSum gaussSum


    sorry
  · have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
    have : (𝓟 ^ 2).LiesOver 𝒑 := sq_liesOver p f L 𝓟 hp'
    rw [← Quotient.eq_zero_iff_mem, gaussSum_map,
      Psi_comp_ideal_quot_eq_one _ _ _ (zeta_sub_one_mem p L 𝓟 hζ), gaussSum_one_right]
    apply Omega_comp_ideal_quot_ne_one
    rwa [Int.dvd_neg]

theorem GSV_lt_one [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GSV f P 𝓟 hζ a < 1 := by
  obtain rfl | hp' := hp.out.eq_two_or_odd'
  · unfold GSV GaussSum gaussSum

    sorry
  · have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
    have : (𝓟 ^ 2).LiesOver 𝒑 := sq_liesOver p f L 𝓟 hp'
    unfold GSV Val GaussSum
    rw [intValuation_lt_one_iff_dvd, dvd_span_singleton, ← Quotient.eq_zero_iff_mem, gaussSum_map,
      Psi_comp_ideal_quot_eq_one _ _ _ (zeta_sub_one_mem p L 𝓟 hζ), gaussSum_one_right]
    apply Omega_comp_ideal_quot_ne_one
    rwa [Int.dvd_neg]

theorem GSV_one [𝓟.LiesOver P] [P.LiesOver 𝒑] (h : p ^ f ≠ 2) :
    GSV f P 𝓟 hζ 1 = Multiplicative.ofAdd (-1 : ℤ) := by
  have : 𝓟.LiesOver 𝒑 := sorry
  have : (𝓟 ^ 2).LiesOver P := sorry
  have : (𝓟 ^ 2).LiesOver 𝒑 := sorry
  apply le_antisymm
  · change _ ≤ WithZero.exp (- ((1 : ℕ) : ℤ))
    rw [intValuation_le_pow_iff_mem, pow_one]
    dsimp
    apply GaussSum_mem
    rwa [Int.natCast_dvd_ofNat, Nat.dvd_one, Nat.pred_eq_succ_iff, zero_add]
  · change WithZero.exp (- ((1 : ℕ) : ℤ)) ≤ _
    rw [intValuation_pow_le_iff_not_mem]
    · rw [← Ideal.Quotient.eq_zero_iff_mem,
        GaussSum_one_mk_sq_eq _ _ _ _ _ hζ h (zeta_sub_one_mem p L 𝓟 hζ), neg_eq_zero]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      sorry
    · apply GaussSum_ne_zero
      rwa [Int.natCast_dvd_ofNat, Nat.dvd_one, Nat.pred_eq_succ_iff, zero_add]

end GaussSums
