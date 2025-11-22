import Mathlib


open Submodule Module Basis

@[simps!]
noncomputable def LinearMap.kerComplementEquivRange {R M₁ M₂ : Type*} [Ring R] [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] (f : M₁ →ₗ[R] M₂) {C : Submodule R M₁}
    (h : IsCompl C (LinearMap.ker f)) : C ≃ₗ[R] range f :=
  .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
  ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
   by
    rintro ⟨-, x, rfl⟩
    use ((prodEquivOfIsCompl _ _ h).2 x).1
    ext
    simp only
    conv_rhs => rw [← Submodule.IsCompl.projection_add_projection_eq_self h x]
    rw [comp_codRestrict, LinearEquiv.invFun_eq_symm, codRestrict_apply, coe_comp,
      coe_subtype, Function.comp_apply, map_add, h.symm.projection_apply_mem x, add_zero]
    congr⟩
