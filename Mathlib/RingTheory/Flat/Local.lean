import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange

universe u v

open TensorProduct

namespace Module.Flat

variable (R : Type u) [CommRing R] [Small.{v} R]
variable (M : Type v) [AddCommGroup M] [Module R M]

instance localization (M : Submonoid R) : Module.Flat R (Localization M) := by
  refine ⟨fun I _ => ?_⟩

  let e1 : I ⊗[R] Localization M ≃ₗ[R] LocalizedModule M I :=

    sorry
  let e2 : Localization M ≃ₗ[R] LocalizedModule M R := sorry
  let g := LocalizedModule.lift M (g := LocalizedModule.mkLinearMap M _ ∘ₗ I.subtype) (by
    intro x
    refine ⟨⟨_, LocalizedModule.divBy x, ?_, ?_⟩, rfl⟩
    · ext a
      simp only [LinearMap.mul_apply, LocalizedModule.divBy_apply, algebraMap_end_apply,
        LinearMap.one_apply]
      induction a using LocalizedModule.induction_on with
      | h a m =>
        rw [LocalizedModule.liftOn_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [smul_eq_mul, one_smul]
        rw [mul_smul]
        congr
    · ext a
      simp only [LinearMap.mul_apply, algebraMap_end_apply, LinearMapClass.map_smul,
        LocalizedModule.divBy_apply, LinearMap.one_apply]
      induction a using LocalizedModule.induction_on with
      | h a m =>
        rw [LocalizedModule.liftOn_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [smul_eq_mul, one_smul]
        rw [mul_smul]
        congr)
  have eq : lift (LinearMap.lsmul R (Localization M) ∘ₗ Submodule.subtype I) =
    e2.symm.toLinearMap ∘ₗ g ∘ₗ e1.toLinearMap := sorry
  rw [eq]
  have inj1 : Function.Injective g := by
    intro x y h
    induction x using LocalizedModule.induction_on with
    | h a m =>
    induction y using LocalizedModule.induction_on with
    | h b n =>
      simp only [LocalizedModule.lift_mk, LinearMap.coe_comp, Submodule.coeSubtype,
        Function.comp_apply, LocalizedModule.mkLinearMap_apply, g] at h

      generalize_proofs _ _ h1 h2 at h
      apply_fun h1.unit.1 at h
      change (h1.unit * h1.unit⁻¹ : End R (LocalizedModule M R)) _ = _ at h
      rw [h1.unit.mul_inv, LinearMap.one_apply] at h
      simp only [IsUnit.unit_spec, algebraMap_end_apply] at h
      apply_fun h2.unit.1 at h
      rw [LinearMap.map_smul] at h
      change _ = (m : R) • (h2.unit * h2.unit⁻¹ : End R (LocalizedModule M R)) _ at h
      rw [h2.unit.mul_inv, LinearMap.one_apply] at h
      simp only [IsUnit.unit_spec, algebraMap_end_apply] at h
      rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h
      obtain ⟨x, hx⟩ := h
      simp only [smul_eq_mul, one_smul] at hx
      rw [LocalizedModule.mk_eq]
      exact ⟨x, Subtype.ext $ hx⟩

  exact e2.symm.injective.comp (inj1.comp e1.injective)


lemma iff_localization :
    Module.Flat R M ↔
    ∀ (p : Ideal R) [hp : p.IsPrime], Module.Flat R (LocalizedModule p.primeCompl M) := sorry

end Module.Flat

example :
    RingHom.PropertyIsLocal (fun {R S} ringR ringS f => @Algebra.Flat R S _ _ f.toAlgebra) where
  LocalizationPreserves := fun R S _ _ f M R' S' _ _ _ _ _ _ flat1 => by
    letI := f.toAlgebra
    letI f' : R' →+* S' := IsLocalization.map S' f M.le_comap_map
    letI := f'.toAlgebra
    refine ⟨?_⟩
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro M' N' _ _ _ _ l
    sorry
  OfLocalizationSpanTarget := sorry
  StableUnderComposition := fun R S T _ _ _ f g hf hg =>
    letI inst1 := f.toAlgebra
    letI inst2 := g.toAlgebra
    letI inst3 := (g.comp f).toAlgebra
    haveI : IsScalarTower R S T :=
      ⟨by intros; simp [Algebra.smul_def, _root_.map_mul, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
    Algebra.Flat.comp R S T
  HoldsForLocalizationAway := fun R S _ _ alg r loc => by
    have eq1 : alg = (algebraMap R S).toAlgebra := by
      ext r s
      simp only [Algebra.smul_def]
      rfl
    rw [← eq1]
    exact ⟨Module.Flat.of_linearEquiv R (Localization.Away r) _ $
      IsLocalization.algEquiv (Submonoid.powers r)  S (Localization.Away r) |>.toLinearEquiv⟩
