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

theorem T₀_ne_zero {a : ℕ} [Nontrivial A] : T₀ ζ a ≠ 0 := ne_zero _

variable {p}

/-- Docstring. -/
def T₁ (hζ : IsPrimitiveRoot ζ p) : ℤ ⧸ 𝒑 → A := by
  intro x
  refine Quotient.liftOn' x (fun x ↦ T₀ ζ x) fun a b h ↦ ?_
  rwa [Submodule.quotientRel_def, mem_span_singleton, ← T₀_eq_T₀_iff p hζ] at h

@[simp]
theorem T₁_apply (x : ℤ) : T₁ hζ (Ideal.Quotient.mk 𝒑 x) = T₀ ζ x := rfl

-- theorem T₁_neg (a : ℤ ⧸ 𝒑) : T₁ p hζ (- a) = (T₁ p hζ a)⁻¹ := by
--   rw [← Ideal.Quotient.mk_out a, T₁_apply, ← T₀_neg, ← T₁_apply p, ← Ideal.Quotient.mk_eq_mk,
--     ← Submodule.Quotient.mk_neg, Ideal.Quotient.mk_eq_mk]

theorem T₁_add (a b : ℤ ⧸ 𝒑) : T₁ hζ (a + b) = (T₁ hζ a) * (T₁ hζ b) := by
  rw [← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b, T₁_apply, T₁_apply, ← T₀_add,
    ← T₁_apply (p := p), map_add]

theorem T₁_zero : T₁ hζ 0 = 1 := by
  change T₁ hζ (Ideal.Quotient.mk 𝒑 0) = 1
  rw [T₁_apply, T₀_eq_one_iff p hζ]
  exact Int.dvd_zero ↑p

theorem T₁_injective : Function.Injective (T₁ hζ) := by
  intro a b h
  rwa [← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b, T₁_apply, T₁_apply, T₀_eq_T₀_iff p hζ,
    ← Ideal.mem_span_singleton, ← Submodule.Quotient.eq, Submodule.Quotient.mk_out,
    Submodule.Quotient.mk_out] at h

theorem T₁_eq_one_iff {a : ℤ ⧸ 𝒑} : T₁ hζ a = 1 ↔ a = 0 := by
  rw [← T₁_zero (p := p)]
  exact (T₁_injective hζ).eq_iff

end T

variable {p} [NeZero p] {ζ : A} (hζ : IsPrimitiveRoot ζ p) {K : Type*} [Field K] (P : Ideal (𝓞 K))

def Psi [P.LiesOver 𝒑] : AddChar (𝓞 K ⧸ P) A := {
  toFun := fun x ↦ T₁ (hζ.isUnit_unit (NeZero.ne _)) <| Algebra.trace (ℤ ⧸ 𝒑) ((𝓞 K) ⧸ P) x
  map_zero_eq_one' := by simpa [map_zero] using T₁_zero _
  map_add_eq_mul' a b := by rw [map_add, T₁_add] }

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

end Psi

variable [hp : Fact (p.Prime)] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
  (P : Ideal (𝓞 K)) [P.IsMaximal]

theorem inertiaDeg_eq [P.LiesOver 𝒑] : 𝒑.inertiaDeg P = f := by
  have : ¬ p ∣ p ^ f - 1 := by
    refine (Nat.dvd_sub_iff_right NeZero.one_le ?_).not.mpr hp.out.not_dvd_one
    exact dvd_pow_self p (NeZero.ne f)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_of_not_dvd (p ^ f - 1) p _ this,
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

variable (L : Type*) [Field L] [Algebra K L] (𝓟 : Ideal (𝓞 L)) [𝓟.IsMaximal] [NeZero 𝓟]

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

variable {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)

abbrev GaussSum [P.LiesOver 𝒑] (a : ℤ) : (𝓞 L) := gaussSum (Omega p f P L ^ (- a)) (Psi hζ P)

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
    GaussSum p f P L hζ ((p ^ f - 1 : ℕ) - a) = GaussSum p f P L hζ (- a) := by
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

variable [NumberField L]

open IsDedekindDomain.HeightOneSpectrum

abbrev Val : Valuation (𝓞 L) (WithZero (Multiplicative ℤ)) :=
  intValuation ⟨𝓟, IsMaximal.isPrime inferInstance, NeZero.ne _ ⟩

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

theorem Val_Omega_pow [P.LiesOver 𝒑] (a : ℕ) (x : (𝓞 K ⧸ P)ˣ) :
    Val L 𝓟 ((Omega p f P L ^ a) x) = 1 := by
  rw [← pow_left_inj₀ (n := p ^ f - 1) (WithZero.zero_le _) zero_le_one (NeZero.ne _), one_pow,
    ← Valuation.map_pow, MulChar.pow_apply_coe, ← pow_mul', pow_mul, Omega_pow_eq_one, one_pow,
    Valuation.map_one]

theorem Val_Omega_zpow [P.LiesOver 𝒑] (a : ℤ) (x : (𝓞 K ⧸ P)ˣ) :
    Val L 𝓟 ((Omega p f P L ^ a) x) = 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [zpow_natCast, Val_Omega_pow]
  · rw [zpow_neg, zpow_natCast, MulChar.inv_apply, Ring.inverse_unit, Val_Omega_pow]

variable {p L} in
abbrev GSV [P.LiesOver 𝒑] (a : ℤ) := Val L 𝓟 (GaussSum p f P L hζ a)

theorem GSV_eq_one_of_dvd [P.LiesOver 𝒑] [𝓟.LiesOver P] (a : ℤ) (h : ↑(p ^ f - 1 : ℕ) ∣ a) :
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

theorem GSV_zero [P.LiesOver 𝒑] [𝓟.LiesOver P] : GSV f P 𝓟 hζ 0 = 1 := by
  apply GSV_eq_one_of_dvd
  exact Int.dvd_zero _

variable {f p P L 𝓟 hζ} in
theorem GSV_nonneg [P.LiesOver 𝒑] {a : ℤ} :
    0 ≤ GSV f P 𝓟 hζ a := WithZero.zero_le _

variable {f p P L 𝓟 hζ} in
theorem GSV_le_one [P.LiesOver 𝒑] {a : ℤ} :
    GSV f P 𝓟 hζ a ≤ 1 := intValuation_le_one _ _

/-- s(α + β) ≤ s(α) + s(β) -/
theorem GSV_mul_GSV_le [P.LiesOver 𝒑] [𝓟.LiesOver P] (a b : ℤ) :
    GSV f P 𝓟 hζ a * GSV f P 𝓟 hζ b ≤ GSV f P 𝓟 hζ (a + b) := by
  by_cases h : ↑(p ^ f - 1 : ℕ) ∣ a + b
  · rw [GSV_eq_one_of_dvd p f P L 𝓟 hζ (a + b) h]
    rw [← Valuation.map_mul]
    exact intValuation_le_one _ _
  · rw [← Valuation.map_mul, GaussSum_mul_gaussSum p f P L hζ h, Valuation.map_mul]
    exact mul_le_of_le_one_right GSV_nonneg (intValuation_le_one _ _)

/-- s(p * α) = s(α) -/
theorem GSV_p_mul [P.LiesOver 𝒑] (a : ℤ) :
    GSV f P 𝓟 hζ (p * a) = GSV f P 𝓟 hζ a := by
  unfold GSV
  rw [GaussSum_p_mul]

variable [hL : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

example [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1) ∣ a) :
    GSV f P 𝓟 hζ a * GSV f P 𝓟 hζ ((p ^ f - 1 : ℕ) - a) =
      Multiplicative.ofAdd ((p - 1 : ℤ) * f) := by
  classical
  unfold GSV
  rw [← Valuation.map_mul, GaussSum_pow_sub_one_sub, GaussSum_mul_GaussSum_neg _ _ _ _ _ _ ha,
    Valuation.map_mul, ← Units.coe_neg_one, Val_Omega_zpow, one_mul, Nat.cast_pow,
    Valuation.map_pow]
  have : Val L 𝓟 p = Multiplicative.ofAdd (p - 1 : ℤ) := by
    rw [intValuation_apply, intValuationDef_if_neg, ofAdd_neg, WithZero.coe_inv]
    rw [Associates.factors_mk, Associates.count_some,
      ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, Associates.map_subtype_coe_factors',
      Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := Ideal (𝓞 L)))]
    dsimp only
    have : span {(p : 𝓞 L)} = 𝒑.map (algebraMap ℤ (𝓞 L)) := by simp [map_span]
    rw [this, ← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count]
    let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := L) (p := p)
      (θ := (IsCyclotomicExtension.zeta_spec (p * (p ^ f - 1)) ℚ L).toInteger) sorry
    let Q := e ⟨𝓟, sorry⟩
    have := NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
      (K := L) (p := p) (θ := (IsCyclotomicExtension.zeta_spec (p * (p ^ f - 1)) ℚ L).toInteger)
      sorry Q.prop


    sorry
  rw [this, Int.ofAdd_mul, zpow_natCast, WithZero.coe_pow]













end GaussSums
