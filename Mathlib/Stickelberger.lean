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

variable (p f : ℕ) [NeZero (p ^ f - 1)] [NeZero f]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

variable {K : Type*} [Field K]

section Psi

variable {A : Type*} [CommRing A] (ζ : A) (hζ : IsPrimitiveRoot ζ p)

/-- Docstring. -/
abbrev T₀ : ℕ → A := fun a ↦ ζ ^ a

@[simp]
theorem T₀_apply (a : ℕ) :  T₀ ζ a = ζ ^ a := rfl

theorem T₀_add (a b : ℕ) : T₀ ζ (a + b) = (T₀ ζ a) * (T₀ ζ b) := by
  rw [T₀_apply, pow_add]

-- theorem T₀_neg (a : ℤ) : T₀ ζ (- a) = (T₀ ζ a)⁻¹ := by
-- rw [T₀_apply, T₀_apply, zpow_neg]

variable {ζ}

theorem T₀_eq_one_iff (hζ : IsPrimitiveRoot ζ p) {a : ℕ} : T₀ ζ a = 1 ↔ p ∣ a := by
  rw [T₀_apply, hζ.pow_eq_one_iff_dvd]

variable [NeZero p] [IsDomain A]

theorem T₀_ne_zero (hζ : IsPrimitiveRoot ζ p) {a : ℕ} : T₀ ζ a ≠ 0 :=
  pow_ne_zero a (hζ.ne_zero (NeZero.ne _))

-- theorem T₀_sub (hζ : IsPrimitiveRoot ζ p) (a b : ℤ) : T₀ ζ (a - b) = (T₀ ζ a) * (T₀ ζ b)⁻¹ := by
--   rw [sub_eq_add_neg, T₀_add p hζ, T₀_neg]

theorem T₀_eq_T₀_iff (hζ : IsPrimitiveRoot ζ p) {a b : ℕ} :
    T₀ ζ a = T₀ ζ b ↔ (p : ℤ) ∣ a - b := by
  have := hζ.isUnit_unit (NeZero.pos _)

  rw [T₀_apply, T₀_apply]
  rw [← (hζ.isUnit (NeZero.pos _)).unit_spec]
  have := (hζ.isUnit (NeZero.pos _)).unit_pow a


  -- ← mul_inv_eq_one₀]
  have : ζ = u.val := by
    rw [@IsUnit.unit_spec]
  have h := FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [← h.eq_iff, T₀_apply, T₀_apply, map_pow, map_pow]
  have : IsPrimitiveRoot (algebraMap A (FractionRing A) ζ) p := by
    refine IsPrimitiveRoot.map_of_injective hζ h
  have := this.pow_eq_one_iff_dvd
  rw [← mul_inv_eq_one₀]
  rw?

  -- rw [← mul_inv_eq_one₀ (T₀_ne_zero p hζ), ← T₀_sub p hζ, T₀_eq_one_iff p hζ]

/-- Docstring. -/
def T₁ (hζ : IsPrimitiveRoot ζ p) : ℤ ⧸ 𝒑 → A := by
  intro x
  refine Quotient.liftOn' x (fun x ↦ T₀ ζ x) fun a b h ↦ ?_
  rwa [Submodule.quotientRel_def, mem_span_singleton, ← T₀_eq_T₀_iff p hζ] at h

@[simp]
theorem T₁_apply (x : ℤ) : T₁ p hζ (Ideal.Quotient.mk 𝒑 x) = T₀ ζ x := rfl

theorem T₁_neg (a : ℤ ⧸ 𝒑) : T₁ p hζ (- a) = (T₁ p hζ a)⁻¹ := by
  rw [← Ideal.Quotient.mk_out a, T₁_apply, ← T₀_neg, ← T₁_apply p, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_neg, Ideal.Quotient.mk_eq_mk]

theorem T₁_add (a b : ℤ ⧸ 𝒑) : T₁ p hζ (a + b) = (T₁ p hζ a) * (T₁ p hζ b) := by
  rw [← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b, T₁_apply, T₁_apply, ← T₀_add p hζ,
    ← T₁_apply p, map_add]

theorem T₁_sub (a b : ℤ ⧸ 𝒑) : T₁ p hζ (a - b) = (T₁ p hζ a) * (T₁ p hζ b)⁻¹ := by
  rw [sub_eq_add_neg, T₁_add, T₁_neg]

theorem T₁_zero : T₁ p hζ 0 = 1 := by
  change T₁ p hζ (Ideal.Quotient.mk 𝒑 0) = 1
  rw [T₁_apply, T₀_eq_one_iff p hζ]
  exact Int.dvd_zero ↑p

theorem T₁_injective : Function.Injective (T₁ p hζ) := by
  intro a b h
  rwa [← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b, T₁_apply, T₁_apply, T₀_eq_T₀_iff p hζ,
    ← Ideal.mem_span_singleton, ← Submodule.Quotient.eq, Submodule.Quotient.mk_out,
    Submodule.Quotient.mk_out] at h

variable {K : Type*} [Field K] (P : Ideal (𝓞 K))

def Psi [P.LiesOver 𝒑] : AddChar ((𝓞 K) ⧸ P) A := {
  toFun := fun x ↦ T₁ p hζ <| Algebra.trace (ℤ ⧸ 𝒑) ((𝓞 K) ⧸ P) x
  map_zero_eq_one' := by simpa [map_zero] using T₁_zero p hζ
  map_add_eq_mul' a b := by rw [map_add, T₁_add] }

end Psi

variable [hp : Fact (p.Prime)] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
  (P : Ideal (𝓞 K)) [P.IsMaximal]

theorem inertiaDeg_eq [P.LiesOver 𝒑] : 𝒑.inertiaDeg P = f := by
  have : p.Coprime (p ^ f - 1) := by
    rw [← Nat.coprime_pow_left_iff (NeZero.pos f), Nat.coprime_self_sub_right NeZero.one_le]
    exact Nat.coprime_one_right _
  rw [IsCyclotomicExtension.Rat.inertiaDeg_of_coprime (p ^ f - 1) p _ this,
    ZMod.orderOf_mod_self_pow_sub_one (Nat.Prime.one_lt hp.out) (NeZero.pos f)]

theorem absNorm_eq [P.LiesOver 𝒑] : absNorm P = p ^ f := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp.out, inertiaDeg_eq p f]

local instance : Fintype ((𝓞 K) ⧸ P) := by
    have := Ideal.finiteQuotientOfFreeOfNeBot P ?_
    · exact Fintype.ofFinite (𝓞 K ⧸ P)
    refine Ring.ne_bot_of_isMaximal_of_not_isField inferInstance ?_
    exact RingOfIntegers.not_isField K

@[simps! apply]
def omega' [P.LiesOver 𝒑] : (rootsOfUnity (p ^ f - 1) (𝓞 K)) ≃* ((𝓞 K) ⧸ P)ˣ := by
  classical
  have hP : Fintype.card ((𝓞 K) ⧸ P)ˣ = p ^ f - 1 := by
    let _ := Ideal.Quotient.field P
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← absNorm_apply, absNorm_eq p f]
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

theorem omega_apply [P.LiesOver 𝒑] (x : ((𝓞 K) ⧸ P)ˣ) :
    Ideal.Quotient.mk P ((omega p f P x : (𝓞 K)ˣ) : 𝓞 K) = x := by
  convert congr_arg Units.val (omega'_apply p f P (omega p f P x)).symm
  exact (MulEquiv.symm_apply_apply (omega p f P) x).symm

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [hL : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] (𝓟 : Ideal (𝓞 L)) [𝓟.IsMaximal]

open Classical in
def Omega [P.LiesOver 𝒑] : MulChar ((𝓞 K) ⧸ P) L := {
  toFun := fun x ↦ if hx : IsUnit x then algebraMap (𝓞 K) L (omega p f P hx.unit).val else 0
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

def GaussSum [P.LiesOver 𝒑] (a : ℤ) : L := by
  have hζ : ∃ ζ : L, IsPrimitiveRoot ζ p := by
    apply hL.exists_prim_root_of_dvd
    exact ⟨p * (p ^ f - 1), rfl, NeZero.ne _, ⟨p ^ f - 1, rfl⟩⟩
  exact gaussSum (Omega p f P L ^ (- a)) (Psi p hζ.choose_spec P)














end GaussSums
