import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki

section IsNoetherian

lemma isNoetherian_of_tower_of_surjective {R S} (M) [CommSemiring R] [Semiring S]
  [AddCommMonoid M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  (h : Function.Surjective (algebraMap R S)) :
  IsNoetherian R M ↔ IsNoetherian S M := by
  refine ⟨isNoetherian_of_tower R, fun h' ↦ ?_⟩
  simp_rw [isNoetherian_iff'] at h' ⊢
  haveI : WellFoundedGT (Submodule S M) := h'
  exact (Submodule.orderIsoOfSurjective M h).symm.toOrderEmbedding.wellFoundedGT

lemma isArtinian_of_tower_of_surjective {R S} (M) [CommRing R] [CommRing S]
  [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  (h : Function.Surjective (algebraMap R S)) :
  IsArtinian R M ↔ IsArtinian S M := by
  refine ⟨isArtinian_of_tower R, ?_⟩
  simp_rw [isArtinian_iff]
  exact (Submodule.orderIsoOfSurjective M h).symm.toOrderEmbedding.wellFounded

end IsNoetherian

section Ideal

lemma isNoetherian_iff_IsArtinian_of_mul {R : Type*} [CommRing R] (I J : Ideal R) [I.IsMaximal]
  (H : IsNoetherian R (I * J : Submodule R R) ↔ IsArtinian R (I * J : Submodule R R)) :
  IsNoetherian R J ↔ IsArtinian R J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet R (J ⧸ IJ) I := by
    intro x ⟨y, hy⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective IJ x
    rw [Subtype.coe_mk, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show _ ∈ I * J
    simp [Ideal.mul_mem_mul hy hx]
  letI : Module (R ⧸ I) (J ⧸ IJ) := this.module
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : IsNoetherian R (J ⧸ IJ) ↔ IsArtinian R (J ⧸ IJ) := by
    rw [isNoetherian_of_tower_of_surjective (J ⧸ IJ) this,
        (IsArtinianRing.tfae (R ⧸ I) (J ⧸ IJ)).out 1 2,
        ← isArtinianOfTowerOfSurjective (J ⧸ IJ) this]
    sorry
  constructor
  · intro hNoetherianJ
    haveI := this.mp inferInstance
    haveI : IsArtinian R (I * J : Submodule R R) := H.mp (isNoetherian_of_le Ideal.mul_le_left)
    apply isArtinian_of_range_eq_ker
      (Submodule.inclusion Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
    simp [Submodule.range_inclusion]
    rfl
  · intro hArtinianJ
    haveI := this.mpr inferInstance
    haveI : IsNoetherian R (I * J : Submodule R R) := H.mpr (isArtinian_of_le Ideal.mul_le_left)
    apply isNoetherian_of_range_eq_ker
      (Submodule.inclusion Ideal.mul_le_left : (I * J : Submodule R R) →ₗ[R] J) IJ.mkQ
    simp [Submodule.range_inclusion]
    rfl

end Ideal

section Algebra

lemma isArtinian_of_isArtinian_of_mul_of_field (K : Type*) {R : Type*} [CommRing R] [Field K]
    [Algebra K R] [Algebra.FiniteType K R] (I J : Ideal R) [I.IsMaximal] [IsArtinian R J]
    (H : IsArtinian K (I * J : _)) : IsArtinian K J := by
  let IJ := Submodule.comap J.subtype (I * J)
  have : Module.IsTorsionBySet R (J ⧸ IJ) I := by
    intro x ⟨y, hy⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Subtype.coe_mk, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show _ ∈ I * J
    simpa using Ideal.mul_mem_mul hy hx
  letI : Module (R ⧸ I) (J ⧸ IJ) := this.module
  letI := Ideal.Quotient.field I
  have : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K (R ⧸ I) := (‹Algebra.FiniteType K R›).trans inferInstance
  haveI : Module.Finite K (R ⧸ I) := by
    -- `NOTE`: the theorem used here is in Mathlib.RingTheory.Jacobson.Ring, but
    -- such an import will cause build cycle

    -- need to use finite_of_finite_type_of_isJacobsonRing
    sorry
  have : IsArtinian R (J ⧸ IJ) ↔ IsArtinian K (J ⧸ IJ) := by
    rw [isArtinian_of_tower_of_surjective (J ⧸ IJ) (by aesop)]
    -- rw [(module.finite_length_tfae_of_field (R ⧸ I) (J ⧸ IJ)).out 2 0,
    --     (module.finite_length_tfae_of_field K (J ⧸ IJ)).out 2 0]
    -- exact (module.finite_of_tower K (R ⧸ I) (J ⧸ IJ)).symm
    sorry
  haveI := this.mp inferInstance
  refine isArtinian_of_range_eq_ker
    ((Submodule.inclusion (Ideal.mul_le_left) : (I * J : _) →ₗ[R] J).restrictScalars K)
    (IJ.mkQ.restrictScalars K) ?_
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ, range_restrictScalars,
    Submodule.range_inclusion]

end Algebra

end IsArtinianRing
