/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Residue field of primes in polynomial algebras

## Main results
- `Polynomial.residueFieldMapCAlgEquiv`: `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`
- `Polynomial.fiberEquivQuotient`: `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I`

-/

@[expose] public section

namespace Polynomial

open scoped nonZeroDivisors TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) [I.IsPrime] (J : Ideal R[X]) [J.IsPrime]

/-- `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`. -/
noncomputable
def residueFieldMapCAlgEquiv [J.LiesOver I] (hJ : J = I.map C) :
    J.ResidueField ≃ₐ[I.ResidueField] RatFunc I.ResidueField := by
  letI f : J.ResidueField →+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices ∃ i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r ↦ congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x ↦ ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : ∃ s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨⟨b, hb0⟩, hb⟩ := IsLocalization.integerNormalization_map_to_map (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using hb
    replace hx : r ∈ J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def, algebraMap_smul, ← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]

@[simp]
lemma residueFieldMapCAlgEquiv_algebraMap [J.LiesOver I] (hJ : J = I.map C) (p : R[X]) :
    residueFieldMapCAlgEquiv I J hJ (algebraMap _ _ p) =
      algebraMap _ _ (p.map (algebraMap R I.ResidueField)) := by
  simp [residueFieldMapCAlgEquiv]

@[simp]
lemma residueFieldMapCAlgEquiv_symm_C [J.LiesOver I] (hJ : J = I.map C) (r) :
    (residueFieldMapCAlgEquiv I J hJ).symm (.C r) = algebraMap _ _ r :=
  (residueFieldMapCAlgEquiv I J hJ).symm.commutes r

@[simp]
lemma residueFieldMapCAlgEquiv_symm_X [J.LiesOver I] (hJ : J = I.map C) :
    (residueFieldMapCAlgEquiv I J hJ).symm .X = algebraMap R[X] _ .X :=
  (residueFieldMapCAlgEquiv I J hJ).injective (by simp)

/-- `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I` -/
noncomputable
def fiberEquivQuotient (f : R[X] →ₐ[R] S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] :
    p.Fiber S ≃ₐ[p.ResidueField] p.ResidueField[X] ⧸
      ((RingHom.ker (f : R[X] →+* S)).map (mapRingHom (algebraMap R p.ResidueField))) := by
  refine .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (AlgHom.liftOfSurjective _ hf
    ((Ideal.Quotient.mkₐ _ _).comp (mapAlgHom (Algebra.ofId _ _))) ?_) fun _ _ ↦ .all _ _)
    (Ideal.Quotient.liftₐ _ (aeval (1 ⊗ₜ f .X)) ?_) ?_ ?_
  · simp [AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← Ideal.map_le_iff_le_comap]
  · change Ideal.map _ _ ≤ RingHom.ker (aeval _).toRingHom
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    have : ((aeval (1 ⊗ₜ[R] f X : p.Fiber S)).restrictScalars R).comp
        (mapAlgHom (Algebra.ofId R p.ResidueField)) =
        Algebra.TensorProduct.includeRight.comp f := by ext; simp
    exact .trans_eq (by intro; aesop) congr(RingHom.ker $this).symm
  · apply Ideal.Quotient.algHom_ext
    ext
    simp
  · ext x
    obtain ⟨x, rfl⟩ := hf x
    simpa using aeval_algHom_apply
      ((Algebra.TensorProduct.includeRight : S →ₐ[_] p.Fiber S).comp f) X x

end Polynomial
