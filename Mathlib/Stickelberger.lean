import Mathlib
import Mathlib.Misc

noncomputable section

namespace Stickelberger

open MonoidAlgebra

variable (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
  [IsMulCommutative (K ≃ₐ[ℚ] K)]

local notation3 "G" => (K ≃ₐ[ℚ] K)

local notation3 "ℚ[G]" => MonoidAlgebra ℚ G

local notation3 "ℤ[G]" => MonoidAlgebra ℤ G

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
      rw [← finset_sum_single x] at hy
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
        ZMod.natCast_val, Finsupp.single_mul, sub_add_cancel, finset_sum_single]
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

open NumberField

variable {p f : ℕ} (hp : p.Prime) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
  (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver 𝒑]

example : 𝒑.inertiaDeg P = f := by
  sorry

end GaussSums
