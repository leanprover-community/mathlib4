/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!

## Monotonicity of adic-completeness

We show that if `I ≤ J` and `I` is fg,
then `M` is `J`-adic implies `M` is `I`-adic.

-/

variable {R : Type*} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J)
variable (M : Type*) [AddCommGroup M] [Module R M]

include hIJ in
lemma IsHausdorff.mono [IsHausdorff J M] : IsHausdorff I M := by
  refine ⟨fun x h ↦ IsHausdorff.haus ‹_› x fun n ↦ ((h n).mono ?_)⟩
  exact Submodule.smul_mono (pow_le_pow_left' hIJ _) le_rfl

include hIJ in
variable {M} in
lemma AdicCompletion.IsAdicCauchy.mono {f} (hf : IsAdicCauchy I M f) : IsAdicCauchy J M f :=
  fun _ _ h ↦ (hf h).mono (Submodule.smul_mono (pow_le_pow_left' hIJ _) le_rfl)

/-- The canonical map `lim M/IⁿM ⟶ lim M⧸JⁿM` if `I ≤ J`. -/
def AdicCompletion.homOfLE : AdicCompletion I M →ₗ[R] AdicCompletion J M where
  toFun v := ⟨fun i ↦ Submodule.mapQ _ _ .id
      (Submodule.smul_mono (pow_le_pow_left' hIJ i) le_rfl) (v.1 i), by
      intro m n hmn
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (v.1 n)
      simp [← v.2 hmn, ← hx]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp [AdicCompletion.val_smul]

@[simp]
lemma AdicCompletion.homOfLE_mk (x) :
    homOfLE hIJ M (.mk I M x) = .mk J M ⟨x.1, IsAdicCauchy.mono hIJ x.2⟩ := rfl

@[simp]
lemma AdicCompletion.homOfLE_of (x) :
    homOfLE hIJ M (.of I M x) = .of J M x := homOfLE_mk hIJ M (.of I M x)

open Pointwise in
lemma AdicCompletion.homOfLE_injective (hI : I.FG) [IsAdicComplete J M] :
    Function.Injective (homOfLE hIJ M) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, hf, rfl⟩ := AdicCompletion.exists_sum_range_eq a
  simp only [AdicCompletion.homOfLE_mk, AdicCompletion.ext_iff, AdicCompletion.mk_apply_coe,
    Submodule.mkQ_apply, AdicCompletion.val_zero, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero] at ha ⊢
  intro i
  replace hf := fun n ↦ hf (i + n)
  simp_rw [pow_add, mul_smul] at hf
  obtain ⟨s, hs⟩ := hI.pow i
  simp only [← hs, Submodule.span_smul_eq] at *
  simp_rw [Submodule.set_smul_eq_range] at hf
  choose v hv using hf
  simp only [Finset.coe_sort_coe, Module.toModuleEnd_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    Submodule.coe_subtype, Function.comp_apply, DistribMulAction.toLinearMap_apply, smul_zero,
    ZeroMemClass.coe_zero, implies_true, Finsupp.sum_fintype, Finset.univ_eq_attach,
    SetLike.val_smul] at hv
  let v' (i : s) : AdicCompletion J M := .mk _ _ ⟨_, isAdicCauchy_sum_range (fun n ↦ (v n i).1)
    fun n ↦ Submodule.smul_mono (pow_le_pow_left' hIJ _) le_rfl (v n i).2⟩
  let e := LinearEquiv.ofBijective _ (AdicCompletion.of_bijective J M)
  have : ∑ i ∈ Finset.range i, f i = - ∑ x ∈ s.attach, x.1 • e.symm (v' x) := by
    apply e.injective
    simp only [map_sum, map_neg, map_smul, LinearEquiv.apply_symm_apply]
    rw [← add_eq_zero_iff_eq_neg']
    ext j
    simp only [val_add, val_sum, Pi.add_apply, Finset.sum_apply, val_zero, Pi.zero_apply]
    simp only [Finset.coe_sort_coe, ← map_smul, ← map_sum, LinearEquiv.ofBijective_apply, val_add,
      Pi.add_apply, mk_apply_coe, of_apply, ← map_add, val_zero, Pi.zero_apply, v', e,
      AdicCauchySequence.smul_apply]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp_rw [Finset.smul_sum, Finset.sum_comm (s := s.attach), hv]
    rw [add_comm, ← Finset.sum_range_add]
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (j.le_add_left _)) le_rfl (ha _)
  rw [this]
  refine neg_mem (sum_mem fun n _ ↦ Submodule.mem_set_smul_of_mem_mem n.2 trivial)

include hIJ in
open AdicCompletion in
@[stacks 090T]
lemma IsAdicComplete.mono (hI : I.FG) [IsAdicComplete J M] : IsAdicComplete I M := by
  have := IsHausdorff.mono hIJ M
  have : IsPrecomplete I M := IsPrecomplete.iff_surjective.mpr fun x ↦
    have ⟨a, ha⟩ := of_surjective J M (homOfLE hIJ M x)
    ⟨a, homOfLE_injective hIJ M hI (by rw [homOfLE_of, ha])⟩
  constructor
