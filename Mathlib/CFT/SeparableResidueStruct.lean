/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Unramified.LocalRing

/-!

# Existence of local algebra with given residue field.

Let `(R, m, k)` be a local ring, `p : R[X]` be a monic polynomial
that is irreducible and separable in `k[X]` (See `SeparableResidueStruct`).
We show that `R[X]/p` is a finite etale local `R`-algebra with residue field `k[X]/p`.
Furthermore, it is a domain when `R` is a UFD, and is a DVR when `R` also is.

In particular if `p` is the minimal polynomial of a primitive element of some finite separable
extension `K` of `k`, then `R[X]/p` is a finite etale `R`-algebra with residue field `K`.
(See `SeparableResidueStruct.exists_of_isSeparable`)

-/

open IsLocalRing Polynomial TensorProduct KaehlerDifferential IntermediateField

variable {R : Type*} [CommRing R] [IsLocalRing R]

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

variable (R) in
/-- The structure of a monic polynomial over a local ring, whose image is irreducible
and separable in the residue field.

This is a separate structure because we would like to put instances on `AdjoinRoot p` depending
on these hypotheses. -/
structure SeparableResidueStruct : Type _ where
  /-- The polynomial of a `SeparableResidueStruct`. -/
  p : R[X]
  monic : p.Monic
  irreducible_map_residue : Irreducible (p.map (residue R))
  separable_map_residue : (p.map (residue R)).Separable

noncomputable section

namespace SeparableResidueStruct

variable (𝓟 : SeparableResidueStruct R)

/-- The ring extension `R[X]/p` corresponding to a `SeparableResidueStruct`.

This is a local ring, is finite etale over `R` and is a domain when `R` is a UFD. -/
protected abbrev Ring : Type _ := AdjoinRoot 𝓟.p

instance : Algebra R[X] 𝓟.Ring := inferInstanceAs (Algebra R[X] (R[X] ⧸ _))

instance : IsScalarTower R R[X] 𝓟.Ring := inferInstanceAs (IsScalarTower R R[X] (R[X] ⧸ _))

lemma algebraMap_polynomial : algebraMap R[X] 𝓟.Ring = AdjoinRoot.mk _ := rfl

instance : Module.Free R 𝓟.Ring := 𝓟.monic.free_adjoinRoot
instance : Module.Finite R 𝓟.Ring := 𝓟.monic.finite_adjoinRoot

/-- The map from `R[X]/p` to `κ[x]/p`. -/
def toResidueExt : 𝓟.Ring →ₐ[R] AdjoinRoot (𝓟.p.map (residue R)) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (.root _)
    (by simp [← aeval_def, ← aeval_map_algebraMap (A := 𝓀[R])]; simp)

@[simp]
lemma toResidueExt_mk (q) : 𝓟.toResidueExt (.mk _ q) = .mk _ (q.map (residue R)) := by
  change 𝓟.toResidueExt.comp (AdjoinRoot.mkₐ _) q =
      (((AdjoinRoot.mkₐ _).restrictScalars R).comp (Polynomial.mapAlg _ _)) q
  congr 1; ext; simp [toResidueExt, mapAlg]

@[simp]
lemma toResidueExt_root : 𝓟.toResidueExt (.root _) = .root _ := by
  rw [AdjoinRoot.root, toResidueExt_mk, AdjoinRoot.root, map_X]

lemma toResidueExt_eq : 𝓟.toResidueExt =
    (AdjoinRoot.quotEquivQuotMap _ _).toAlgHom.comp (Ideal.Quotient.mkₐ _ _) := by
  ext
  change _ = Ideal.Quotient.mk _ (X.map _)
  simp
  rfl

instance : Field (AdjoinRoot (𝓟.p.map (residue R))) :=
  haveI : Fact (Irreducible (𝓟.p.map (residue R))) := ⟨𝓟.irreducible_map_residue⟩
  inferInstance

instance : Algebra.IsSeparable 𝓀[R] (AdjoinRoot (𝓟.p.map (residue R))) := by
  let pb := AdjoinRoot.powerBasis (𝓟.monic.map (residue R)).ne_zero
  suffices Algebra.IsSeparable 𝓀[R] 𝓀[R]⟮pb.gen⟯ from
    .of_algHom _ _ pb.equivAdjoinSimple.symm.toAlgHom
  rw [isSeparable_adjoin_simple_iff_isSeparable, IsSeparable,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic (𝓟.monic.map (residue R))]
  exact 𝓟.separable_map_residue

lemma toResidueExt_surjective : Function.Surjective 𝓟.toResidueExt :=
  𝓟.toResidueExt_eq ▸ (AdjoinRoot.quotEquivQuotMap _ _).surjective.comp Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
lemma ker_toResidueExt : RingHom.ker 𝓟.toResidueExt.toRingHom = 𝓂[R].map (algebraMap _ _) := by
  rw [𝓟.toResidueExt_eq, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    RingHom.ker_comp_of_injective _ (AdjoinRoot.quotEquivQuotMap _ _).injective,
    Ideal.Quotient.mkₐ_ker, AdjoinRoot.algebraMap_eq]

instance isMaximal_map : (𝓂[R].map (algebraMap R 𝓟.Ring)).IsMaximal :=
  𝓟.ker_toResidueExt ▸ RingHom.ker_isMaximal_of_surjective _ 𝓟.toResidueExt_surjective

instance : IsLocalRing 𝓟.Ring := .of_unique_max_ideal ⟨_, 𝓟.isMaximal_map, fun J hJ ↦
    have := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) J)
    (𝓟.isMaximal_map.eq_of_le hJ.ne_top (Ideal.map_le_iff_le_comap.mpr this.ge)).symm⟩

lemma maximalIdeal_ring : 𝓂[𝓟.Ring] = 𝓂[R].map (algebraMap R 𝓟.Ring) :=
  (eq_maximalIdeal inferInstance).symm

lemma mk_mem_maximalIdeal_iff {q} :
    .mk 𝓟.p q ∈ 𝓂[𝓟.Ring] ↔ 𝓟.p.map (residue R) ∣ q.map (residue R) := by
  rw [maximalIdeal_ring, ← ker_toResidueExt, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, toResidueExt_mk, AdjoinRoot.mk_eq_zero]

/-- The residue field of `R[X]/p` is isomorphic to `κ[x]/p`. -/
def residueFieldEquiv : 𝓀[𝓟.Ring] ≃ₐ[𝓀[R]] AdjoinRoot (𝓟.p.map (residue R)) where
  __ := (Ideal.quotEquivOfEq (𝓟.maximalIdeal_ring.trans 𝓟.ker_toResidueExt.symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective 𝓟.toResidueExt_surjective).toRingEquiv
  commutes' := residue_surjective.forall.mpr fun x ↦ by
    change 𝓟.toResidueExt (.mk _ (C x)) = _
    simp [toResidueExt]
    rfl

instance : Algebra.FormallyUnramified R 𝓟.Ring := by
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]
  exact ⟨.of_algHom _ _ 𝓟.residueFieldEquiv.toAlgHom, 𝓟.maximalIdeal_ring.symm⟩

instance : Algebra.FormallySmooth R 𝓟.Ring := by
  let S := 𝓟.Ring
  let P : Algebra.Extension R S :=
  { Ring := R[X]
    σ := Function.surjInv Ideal.Quotient.mk_surjective
    algebraMap_σ := Function.surjInv_eq _ }
  have hPker : P.ker = .span {𝓟.p} := Ideal.mk_ker
  have hP : P.ker.FG := ⟨{𝓟.p}, Finset.coe_singleton _ ▸ hPker.symm⟩
  let eP : 𝓀[S] ⊗[S] P.CotangentSpace ≃ₗ[S] 𝓀[S] :=
    (TensorProduct.AlgebraTensorModule.congr (.refl _ _)
      ((TensorProduct.AlgebraTensorModule.congr (.refl _ _)
      (KaehlerDifferential.polynomialEquiv R)) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid _ _ _)) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid _ _ _
  have : Module.Free P.Ring Ω[P.Ring⁄R] := .of_equiv (KaehlerDifferential.polynomialEquiv R).symm
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P hP, injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨a, rfl⟩ := TensorProduct.mk_surjective S _ _ residue_surjective a
  obtain ⟨⟨a, ha'⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective a
  replace ha : (polynomialEquiv R (D _ _ a) • 1 : S) • 1 = eP 0 := DFunLike.congr_arg eP ha
  obtain ⟨q, rfl⟩ : 𝓟.p ∣ a := by rwa [hPker, Ideal.mem_span_singleton] at ha'
  rw [eP.map_zero, polynomialEquiv_D, smul_assoc, one_smul, ← Algebra.algebraMap_eq_smul_one,
    IsScalarTower.algebraMap_apply R[X] S 𝓀[S], ResidueField.algebraMap_eq,
    residue_eq_zero_iff, algebraMap_polynomial, derivative_mul, map_add, add_comm, map_mul,
    AdjoinRoot.mk_self, zero_mul, zero_add, map_mul] at ha
  have H : AdjoinRoot.mk 𝓟.p (derivative 𝓟.p) ∉ 𝓂[S] := 𝓟.mk_mem_maximalIdeal_iff.not.mpr fun h ↦
    𝓟.irreducible_map_residue.not_isUnit
      (𝓟.separable_map_residue.isUnit_of_dvd (derivative_map 𝓟.p (residue R) ▸ h))
  have : Algebra.Extension.Cotangent.mk (P := P) ⟨𝓟.p * q, ha'⟩ =
      AdjoinRoot.mk 𝓟.p q • .mk ⟨𝓟.p, hPker ▸ Ideal.mem_span_singleton_self _⟩ := by
    change Algebra.Extension.Cotangent.mk (P := P) ⟨𝓟.p * q, ha'⟩ = (show P.Ring from q) • .mk _
    ext
    rw [Algebra.Extension.Cotangent.val_smul']
    simp only [Algebra.Extension.Cotangent.val_mk, ← map_smul, SetLike.mk_smul_mk, smul_eq_mul]
    congr 2
    rw [mul_comm]
  dsimp
  rw [this, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    ResidueField.algebraMap_eq,
    (residue_eq_zero_iff _).mpr ((Ideal.IsPrime.mem_or_mem' ha).resolve_left H), zero_tmul]

instance : Algebra.FormallyEtale R 𝓟.Ring := .of_formallyUnramified_and_formallySmooth

instance : Algebra.Etale R 𝓟.Ring where

lemma irreducible [IsDomain R] : Irreducible 𝓟.p :=
  𝓟.monic.irreducible_of_irreducible_map _ _ 𝓟.irreducible_map_residue

instance [IsDomain R] [UniqueFactorizationMonoid R] : IsDomain 𝓟.Ring :=
  AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp 𝓟.irreducible)

instance [IsNoetherianRing R] : IsNoetherianRing 𝓟.Ring := .of_finite R _

instance {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (𝓟 : SeparableResidueStruct R) : IsDiscreteValuationRing 𝓟.Ring := by
  have : ¬ IsField 𝓟.Ring := mt (isField_of_isIntegral_of_isField
    (FaithfulSMul.algebraMap_injective R 𝓟.Ring)) (IsDiscreteValuationRing.not_isField R)
  refine ((IsDiscreteValuationRing.TFAE _ this).out 0 4).mpr ?_
  rw [maximalIdeal_ring]
  infer_instance

/-- If `R` is a local ring with residue field `κ`, and `K` is a finite separable extension of `κ`,
then there exists a finite etale local `R`-algebra whose residue field is `K`. -/
lemma exists_of_isSeparable {K : Type*} [Field K] [Algebra 𝓀[R] K]
    [FiniteDimensional 𝓀[R] K] [Algebra.IsSeparable 𝓀[R] K] :
    ∃ (𝓟 : SeparableResidueStruct R), Nonempty (𝓀[𝓟.Ring] ≃ₐ[𝓀[R]] K) := by
  letI := Algebra.compHom K (residue R)
  have : IsScalarTower R 𝓀[R] K := .of_algebraMap_eq' rfl
  obtain ⟨x, hx⟩ := Field.exists_primitive_element 𝓀[R] K
  have hx' := Algebra.IsIntegral.isIntegral (R := 𝓀[R]) x
  obtain ⟨p, hp, hpdeg, hpmon⟩ := lifts_and_degree_eq_and_monic ((Set.range_eq_univ.mpr
    (Polynomial.map_surjective _ residue_surjective)).ge (Set.mem_univ (minpoly 𝓀[R] x)))
    (minpoly.monic hx')
  have (eq := h𝓟) 𝓟 : SeparableResidueStruct R :=
    ⟨p, hpmon, hp ▸ minpoly.irreducible hx', hp ▸ Algebra.IsSeparable.isSeparable 𝓀[R] x⟩
  refine ⟨𝓟, ⟨𝓟.residueFieldEquiv.trans ?_⟩⟩
  refine (AdjoinRoot.powerBasis 𝓟.irreducible_map_residue.ne_zero).equivOfMinpoly
    (PowerBasis.ofAdjoinEqTop hx' (Algebra.adjoin_eq_top_of_intermediateField
      (fun _ _ ↦ Algebra.IsAlgebraic.isAlgebraic _) hx)) ?_
  rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (𝓟.monic.map _)]
  simp [h𝓟, hp]

end SeparableResidueStruct
