/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Domain
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.KroneckerWeberAlgebraPrereqs
public import Mathlib.NumberTheory.NumberField.Cyclotomic.StickelbergerPrereqs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.QuadraticField.Basic
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Prerequisites for the Kronecker-Weber theorem

This file gathers results on number fields, CM fields, intermediate fields, Kummer extensions and
ramification that are used in the proof of the Kronecker-Weber theorem in
`Mathlib.NumberTheory.NumberField.Cyclotomic.KroneckerWeber`.
-/

@[expose] public section

section

/-- The discriminant of a quadratic field is not `1`. -/
theorem NumberField.QuadraticField.discr_ne_one (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] :
    NumberField.discr K ≠ 1 := fun h ↦ not_isSquare_discr K (h ▸ IsSquare.one)

end

section

/-- The compositum of two number fields is a number field. -/
instance NumberField.sup {E F : Type*} [Field E] [Field F] [Algebra E F]
    (K L : IntermediateField E F) [NumberField K] [NumberField L] :
    NumberField ↑(K ⊔ L) :=
  haveI : CharZero E := (algebraMap E K).charZero
  { to_charZero := IntermediateField.charZero (K ⊔ L)
    to_finiteDimensional := by
      have : FiniteDimensional ℚ E := Module.Finite.left ℚ E K
      have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
      have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
      exact FiniteDimensional.trans ℚ E _ }
open scoped NumberField

namespace NumberField.RingOfIntegers
variable {K L : Type*} [Field K] [Field L]

/-- The `ℤ`-algebra isomorphism `(𝓞 K) ≃ₐ[ℤ] (𝓞 L)` given by restricting a ring isomorphism
  `e : K ≃+* L` to `𝓞 K`. Unlike `RingOfIntegers.mapAlgEquiv`, whose base is `𝓞 k`, this has base
  `ℤ`, which is convenient when the natural common base of `K` and `L` is `ℚ` (as `𝓞 ℚ` is only
  isomorphic to, not equal to, `ℤ`). -/
def mapIntAlgEquiv (e : K ≃+* L) : (𝓞 K) ≃ₐ[ℤ] (𝓞 L) := (mapRingEquiv e).toIntAlgEquiv
end NumberField.RingOfIntegers

namespace NumberField
open InfinitePlace
variable {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

/-- In a Galois extension of `ℚ`, if one infinite place is real, then all are. -/
theorem InfinitePlace.isReal_of_isGalois {w : InfinitePlace K} (hw : w.IsReal)
    (w' : InfinitePlace K) :
    w'.IsReal := by
  obtain ⟨σ, rfl⟩ : ∃ σ, σ • w = w' := exists_smul_eq_of_comap_eq (k := ℚ) (Subsingleton.elim _ _)
  exact isReal_smul_iff.mpr hw

/-- A Galois extension of `ℚ` is totally complex if and only if it has a complex place. -/
theorem isTotallyComplex_iff_exists_isComplex [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ∃ w : InfinitePlace K, w.IsComplex := by
  refine ⟨fun h ↦ ⟨Classical.arbitrary _, h.isComplex _⟩, fun ⟨w, hw⟩ ↦ ⟨fun w' ↦ ?_⟩⟩
  exact not_isReal_iff_isComplex.mp fun h ↦ not_isReal_iff_isComplex.mpr hw (isReal_of_isGalois h w)

/-- A Galois extension of `ℚ` is totally complex if and only if it is not totally real. -/
theorem isTotallyComplex_iff_not_isTotallyReal [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ¬ IsTotallyReal K := by
  simp_rw [isTotallyComplex_iff_exists_isComplex, isTotallyReal_iff, not_forall,
    not_isReal_iff_isComplex]

/-- A Galois extension of `ℚ` is totally real if and only if it is not totally complex. -/
theorem isTotallyReal_iff_not_isTotallyComplex [Nonempty (InfinitePlace K)] :
    IsTotallyReal K ↔ ¬ IsTotallyComplex K := by
  rw [isTotallyComplex_iff_not_isTotallyReal, not_not]
end NumberField

end

section
open NumberField IsCMField Units

section Units

namespace NumberField.IsCMField
variable {K : Type*} [Field K]

/-- The power of a unit `u` by the index of the real units is a root of unity times a real
unit. -/
theorem exists_torsion_realunits_pow_indexRealUnits_eq_mul (u : (𝓞 K)ˣ) :
    ∃ ζ : Units.torsion K, ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ u ^ indexRealUnits K = ζ * v := by
  obtain ⟨⟨v, hv⟩, ζ, h⟩ :=
    Subgroup.mem_sup'.mp <| Subgroup.pow_index_mem (realUnits K ⊔ torsion K) u
  exact ⟨ζ, v, hv, by rwa [eq_comm, mul_comm]⟩
variable [CharZero K] [IsCMField K] [NumberField K]

/-- The `Units.val` of `unitsComplexConj` is `ringOfIntegersComplexConj` of the `Units.val`. Not a
`simp` lemma: `simp` rewrites the left-hand side further, through `Units.coe_mapEquiv`. -/
theorem coe_unitsComplexConj {K : Type*} [Field K] [CharZero K] [IsCMField K]
    [Algebra.IsIntegral ℚ K] (u : (𝓞 K)ˣ) :
    (unitsComplexConj K u).val = ringOfIntegersComplexConj K u.val := rfl
end NumberField.IsCMField
end Units

section RootsOfUnity

/-- A complex-conjugation-type automorphism sends a root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_pow_eq_one {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : ζ ^ n = 1) :
    σ ζ = ζ⁻¹ := by
  apply φ.injective
  rw [IsConj.eq hσ, RCLike.star_def, ← Complex.inv_eq_conj, map_inv₀]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne n)

/-- A complex-conjugation-type automorphism sends a primitive root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    σ ζ = ζ⁻¹ :=
  hσ.eq_inv_of_pow_eq_one hζ.pow_eq_one

/-- Complex conjugation of a CM field sends a primitive root of unity to its inverse. This is the
version of `NumberField.IsCMField.complexConj_torsion` for an arbitrary primitive root. -/
theorem NumberField.IsCMField.complexConj_eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    [NumberField K] [IsCMField K] {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    complexConj K ζ = ζ⁻¹ :=
  (isConj_complexConj K
    (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).eq_inv_of_isPrimitiveRoot hζ
end RootsOfUnity

section CMGaloisGroup

namespace NumberField.IsCMField

noncomputable section
variable (K : Type*) [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K

/-- Complex conjugation of the CM field `K`, as an element of `Gal(K/ℚ)`. -/
noncomputable def ratComplexConj : Gal(K/ℚ) :=
  (complexConj K).restrictScalars ℚ

/-- The element `ratComplexConj K` acts as complex conjugation. -/
@[simp]
theorem ratComplexConj_apply (x : K) : ratComplexConj K x = complexConj K x := rfl
variable {K}
variable (K)

omit [Algebra.IsIntegral ℚ K] in
/-- A CM field has twice the degree of its maximal real subfield. -/
theorem finrank_eq_two_mul :
    Module.finrank ℚ K = 2 * Module.finrank ℚ K⁺ := by
  rw [← Module.finrank_mul_finrank ℚ K⁺ K, Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K,
    mul_comm]

open IntermediateField in
/-- The subfield of a CM field fixed by complex conjugation is its maximal real subfield. -/
theorem toSubfield_fixedField_ratComplexConj :
    (fixedField (Subgroup.zpowers (ratComplexConj K))).toSubfield = maximalRealSubfield K := by
  ext x
  rw [Subfield.mem_mk, Subring.mem_mk, Subalgebra.mem_toSubsemiring, mem_toSubalgebra,
    mem_fixedField_iff, Subgroup.forall_mem_zpowers, ← complexConj_eq_self_iff]
  exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := ratComplexConj K)).trans <| by simp

open IntermediateField in
/-- The subfield of a CM field fixed by complex conjugation is totally real. -/
instance isTotallyReal_fixedField_ratComplexConj :
    IsTotallyReal (fixedField (Subgroup.zpowers (ratComplexConj K))) := by
  change IsTotallyReal (fixedField (Subgroup.zpowers (ratComplexConj K))).toSubfield
  rw [toSubfield_fixedField_ratComplexConj]
  infer_instance
end

section Subfields
variable {K L : Type*} [Field K] [Field L] [CharZero K] [Algebra.IsIntegral ℚ K] [CharZero L]
  [Algebra.IsIntegral ℚ L] [IsCMField K] [IsCMField L] [Algebra K L]
end Subfields
end NumberField.IsCMField
end CMGaloisGroup

end

section

/-- The fixing subgroup of an intermediate field `F` is a Galois group of `L / F`. This bridges
`IntermediateField.fixingSubgroup` to `IsGaloisGroup.intermediateField`, which is stated on the raw
`fixingSubgroup Gal(L/K) (↑F)`; instance search does not unfold the
  `IntermediateField.fixingSubgroup`
wrapper on its own, so without this the instance is not found for the `IntermediateField` form. -/
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) : IsGaloisGroup F.fixingSubgroup F L :=
  inferInstanceAs (IsGaloisGroup (fixingSubgroup Gal(L/K) (F : Set L)) F L)

open scoped NumberField in
/-- Ring-of-integers form of the previous instance. The generic `IsGaloisGroup G (𝓞 K) (𝓞 L)`
instance does not fire for `G = F.fixingSubgroup` on its own, so we bridge it explicitly (its body,
`IsGaloisGroup.of_isFractionRing`, uses the field instance above). Keying on `F.fixingSubgroup` (as
opposed to an arbitrary `G`) is essential: it pins the intermediate field `F`, which otherwise would
only be recoverable from `𝓞 ↑F` and hence left undetermined by instance search. -/
instance {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (F : IntermediateField K L) :
    IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ (𝓞 F) (𝓞 L) F L

open IntermediateField in
/-- In a finite Galois extension, two intermediate fields are equal iff they have the same fixing
subgroup. -/
theorem IsGalois.fixingSubgroup_inj {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {F₁ F₂ : IntermediateField K L} :
    F₁.fixingSubgroup = F₂.fixingSubgroup ↔ F₁ = F₂ :=
  ⟨fun h ↦ by rw [← fixedField_fixingSubgroup F₁, h, fixedField_fixingSubgroup], congr_arg _⟩

open IntermediateField in
/-- In a finite extension, two subgroups of the automorphism group are equal iff they have the same
fixed field. -/
theorem IsGalois.fixedField_inj {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {H₁ H₂ : Subgroup Gal(L/K)} :
    fixedField H₁ = fixedField H₂ ↔ H₁ = H₂ :=
  ⟨fun h ↦ by rw [← fixingSubgroup_fixedField H₁, h, fixingSubgroup_fixedField], congr_arg _⟩

open IntermediateField in
/-- `lift` preserves the degree over the base field: `[lift E : K] = [E : K]`. -/
theorem IntermediateField.finrank_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) :
    Module.finrank K (lift E) = Module.finrank K E :=
  (liftAlgEquiv E).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `restrict` preserves the degree over the base field: `[restrict h : K] = [F : K]`. -/
theorem IntermediateField.finrank_restrict {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} (h : F ≤ E) :
    Module.finrank K (restrict h) = Module.finrank K F :=
  (restrictAlgEquiv h).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `restrict` preserves finite-dimensionality over the base field. -/
instance IntermediateField.finiteDimensional_restrict {K L : Type*} [Field K] [Field L]
    [Algebra K L] {F E : IntermediateField K L} {h : F ≤ E} [FiniteDimensional K F] :
    FiniteDimensional K (restrict h) :=
  Module.Finite.equiv (restrictAlgEquiv h).toLinearEquiv

/-- Fixed-field is antitone (the Galois correspondence), so it sends `⊓` of subgroups to `⊔` of
fixed fields: `fixedField (A ⊓ B) = fixedField A ⊔ fixedField B`. -/
theorem FixedPoints.intermediateField_inf (G K L : Type*) [Group G] [Field K] [Field L]
    [Algebra K L] [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L] (A B : Subgroup G) :
    (FixedPoints.intermediateField ↑(A ⊓ B) : IntermediateField K L) =
      FixedPoints.intermediateField A ⊔ FixedPoints.intermediateField B := by
  rw [← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := A ⊓ B),
    ← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := A),
    ← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := B),
    toDual_inf, OrderIso.map_sup]

/-- For a Galois group `G` of `L/K` (`IsGaloisGroup G K L`), if
a normal subgroup `I` is complemented by the fixing subgroup of an intermediate field `F`
(`IsComplement' I (fixingSubgroup G (F : Set L))`), then the fixed field of `I` together with `F`
generates `L`, and the complement is `G ⧸ I`. Used both in the odd-prime ramification reduction and
in the `p = 2` (Lemmermeyer) case, each taking a fixed field of a subgroup this way. -/
theorem IsGaloisGroup.fixedPoints_sup_eq_top_of_isComplement (G K L : Type*) [Group G] [Field K]
    [Field L] [Algebra K L] [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L]
    {I : Subgroup G} [I.Normal] {F : IntermediateField K L}
    (h : Subgroup.IsComplement' I (fixingSubgroup G (F : Set L))) :
    FixedPoints.intermediateField I ⊔ F = ⊤ ∧
      Nonempty (G ⧸ I ≃* (fixingSubgroup G (F : Set L))) := by
  refine ⟨?_, ⟨h.symm.QuotientMulEquiv⟩⟩
  rw [← fixedPoints_fixingSubgroup G K L F, ← FixedPoints.intermediateField_inf,
    disjoint_iff.mp h.disjoint, fixedPoints_bot]

section restrictScalars
variable (K F E L : Type*) [Field K] [Field F] [Field E] [Field L]
  [Algebra K F] [Algebra K E] [Algebra K L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower K F E] [IsScalarTower K F L] [IsScalarTower K E L] [IsScalarTower F E L]
  [FiniteDimensional K L] [FiniteDimensional K E] [FiniteDimensional F L] [FiniteDimensional F E]
  [IsGalois K L] [IsGalois K E] [IsGalois F L] [IsGalois F E]
end restrictScalars

section restrictHom_eq
variable (G G' A B C A' B' C' : Type*) [Group G] [Group G'] [Finite G] [Finite G']
  [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [FaithfulSMul B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B]
  [CommRing A'] [CommRing B'] [CommRing C'] [IsDomain C'] [Algebra A' B'] [Algebra A' C']
  [Algebra B' C'] [IsScalarTower A' B' C'] [FaithfulSMul B' C']
  [MulSemiringAction G C'] [IsGaloisGroup G A' C'] [MulSemiringAction G' B']
  [IsGaloisGroup G' A' B']
  [Algebra B B'] [Algebra C C'] [Algebra B C'] [IsScalarTower B B' C'] [IsScalarTower B C C']
  [FaithfulSMul B B'] [SMulDistribClass G C C'] [SMulDistribClass G' B B']
end restrictHom_eq
universe u

open IntermediateField in
/-- Every finite-dimensional abelian Galois extension `K/F` is the compositum of cyclic
subextensions of prime power degree. (The character codomain is `AlgebraicClosure ℚ`, which has
enough roots of unity for the finite group `Gal(K/F)` regardless of the characteristic of `F`.) -/
lemma IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top
    (F : Type*) (K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsAbelianGalois F K] :
    ∃ (ι : Type u) (_ : Fintype ι) (C : ι → IntermediateField F K),
      (∀ i, IsGalois F (C i) ∧ IsCyclic Gal((C i)/F) ∧ IsPrimePow (Module.finrank F (C i))) ∧
        ⨆ i, C i = ⊤ := by
  classical
  let : CommGroup (K ≃ₐ[F] K) := IsMulCommutative.instCommGroup
  refine ⟨{χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ // IsPrimePow (orderOf χ)}, Fintype.ofFinite _,
    fun χ ↦ IntermediateField.fixedField χ.val.ker, fun ⟨χ, hχ⟩ ↦ ?_, ?_⟩
  · refine ⟨IsGalois.of_fixedField_normal_subgroup χ.ker, ?_, ?_⟩
    · exact isCyclic_of_injective (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom
        (MulEquiv.injective _)
    · have : IsGalois F (fixedField χ.ker) := IsGalois.of_fixedField_normal_subgroup χ.ker
      rw [← IsGalois.card_aut_eq_finrank]
      erw [Nat.card_congr (IsGalois.normalAutEquivQuotient χ.ker).symm.toEquiv]
      rwa [MonoidHom.card_quotient_ker_eq_orderOf χ]
  · simp only [← IsGalois.intermediateFieldEquivSubgroup.apply_eq_iff_eq, OrderIso.map_iSup,
      IsGalois.intermediateFieldEquivSubgroup_apply, fixingSubgroup_fixedField, OrderIso.map_top,
      ← toDual_iInf, OrderDual.toDual_eq_top]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
    by_contra! h
    have h_eq_one {ψ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ} : ψ g = 1 := by
      have : ψ ∈ Subgroup.closure
          {χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ| IsPrimePow (orderOf χ)} := by
        rw [CommGroup.closure_isPrimePow_orderOf_eq_top isMulTorsion_of_finite]
        exact Subgroup.mem_top ψ
      induction this using Subgroup.closure_induction with
      | mem η hη => exact Subgroup.mem_iInf.mp hg ⟨η, hη⟩
      | one => simp
      | mul η₁ η₂ _ _ h₁ h₂ => rw [MonoidHom.mul_apply, h₁, h₂, one_mul]
      | inv η _ hη => rw [MonoidHom.inv_apply, hη, inv_eq_one]
    obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(K/F)
      (AlgebraicClosure ℚ) h
    exact hψ h_eq_one

open IntermediateField Module in
/-- If `B / F` is a finite Galois extension and the compositum `A ⊔ B` is all of `E`, then the
relative degree `[E : A]` divides `[B : F]`. This is the ⊤-case: here `E` is genuinely an
`A`-algebra, so the divisibility can be stated directly (unlike the general compositum form
`finrank_sup_dvd_mul_of_isGalois`). It follows from the injection `Gal(E/A) ↪ Gal(B/F)` induced by
restriction and Lagrange's theorem. -/
theorem IntermediateField.finrank_dvd_finrank_of_isGalois_of_sup_eq_top {F E : Type*} [Field F]
    [Field E] [Algebra F E] (A B : IntermediateField F E)
    [FiniteDimensional A E] [FiniteDimensional F B] [IsGalois F B] (h : B ⊔ A = ⊤) :
    finrank A E ∣ finrank F B := by
  have : IsGalois A E := IsGalois.sup_right B A h
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_injective _ <| restrictRestrictAlgEquivMapHom_injective B A h

open Module in
/-- If `B / F` is a finite Galois extension, then for any finite `A`, the degree of the compositum
`A ⊔ B` over `F` divides `[A : F] * [B : F]`. (Equivalently, `[A ⊔ B : A] ∣ [B : F]`, which fails
without the Galois hypothesis on `B`.)

Remark: we cannot state this as `finrank A ↑(A ⊔ B) ∣ finrank F B` since `↑(A ⊔ B)` is not, by
default, an `A`-algebra; hence the product form `[A ⊔ B : F] ∣ [A : F] * [B : F]`. The ⊤-case
`finrank_dvd_finrank_of_isGalois_of_sup_eq_top` does not have this obstruction. -/
theorem IntermediateField.finrank_sup_dvd_mul_of_isGalois {F E : Type*} [Field F] [Field E]
    [Algebra F E] (A B : IntermediateField F E) [FiniteDimensional F A] [IsGalois F B]
    [FiniteDimensional F B] :
    finrank F ↑(A ⊔ B) ∣ finrank F A * finrank F B := by
  let A' : IntermediateField F ↑(A ⊔ B) := A.restrict le_sup_left
  let B' : IntermediateField F ↑(A ⊔ B) := B.restrict le_sup_right
  have : IsGalois F B' := IsGalois.of_algEquiv (restrictAlgEquiv le_sup_right)
  -- Speeds up instance search.
  have : Module.Free A' ↑(A ⊔ B) := Module.Free.of_divisionRing _ _
  have : B' ⊔ A' = ⊤ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top, sup_comm])
  have := mul_dvd_mul_left (finrank F A') <| finrank_dvd_finrank_of_isGalois_of_sup_eq_top A' B'
    this
  rwa [Module.finrank_mul_finrank, finrank_restrict, finrank_restrict] at this

/-- The lift of a finite supremum of intermediate fields is the supremum of their lifts. -/
theorem IntermediateField.lift_iSup (F E : Type*) [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) {ι : Type*} (S : Finset ι) (L : ι → IntermediateField F K) :
    lift (⨆ i ∈ S, L i) = ⨆ i ∈ S, lift (L i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i s _ hi => rw [Finset.iSup_insert, Finset.iSup_insert, lift_sup, hi]

namespace IntermediateField
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K : IntermediateField F E}
end IntermediateField

namespace IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- If `L / K` has prime degree, then any intermediate field between `K` and `L` is `K` or `L`. -/
theorem eq_or_eq_of_relfinrank_prime {K L M : IntermediateField F E} (hKM : K ≤ M) (hML : M ≤ L)
    (hp : (relfinrank K L).Prime) : M = K ∨ M = L := by
  rw [← relfinrank_mul_relfinrank hKM hML, Nat.prime_mul_iff] at hp
  obtain ⟨-, h⟩ | ⟨-, h⟩ := hp
  · exact .inr <| le_antisymm hML (relfinrank_eq_one_iff.mp h)
  · exact .inl <| le_antisymm (relfinrank_eq_one_iff.mp h) hKM
end IntermediateField

end

section
open IntermediateField Polynomial

section
open Polynomial IntermediateField

/-- If `ζ` is a primitive `n`-th root of unity and `x ^ n = α ^ n`, then `x = ζ ^ j * α`
for some `j < n`. Generalizes the implicit content of `IsPrimitiveRoot.nthRoots_eq`. -/
lemma IsPrimitiveRoot.eq_pow_mul_of_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} [NeZero n] {ζ α x : R}
    (hζ : IsPrimitiveRoot ζ n) (h : x ^ n = α ^ n) :
    ∃ j : ℕ, j < n ∧ x = ζ ^ j * α := by
  have hx : x ∈ nthRoots n (α ^ n) := (mem_nthRoots (NeZero.pos n)).mpr h
  simp only [hζ.nthRoots_eq rfl, Multiset.mem_map, Multiset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, hj, rfl⟩

/-- Version of `Algebra.adjoin_root_eq_top_of_isSplittingField` without the irreducibility of
`X ^ n - C a`. -/
lemma Algebra.adjoin_root_eq_top_of_isSplittingField' {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] {α : L} (hα : α ^ n = algebraMap K L a) :
    Algebra.adjoin K {α} = ⊤ := by
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero n := ⟨fun h ↦ by simp [h] at hζ⟩
  replace hζ := (isPrimitiveRoot_of_mem_primitiveRoots hζ).map_of_injective
    (algebraMap K L).injective
  rw [← top_le_iff, ← IsSplittingField.adjoin_rootSet L (X ^ n - C a), Algebra.adjoin_le_iff]
  intro x hx
  rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero (NeZero.pos n) a), aeval_sub, aeval_X_pow, aeval_C,
    sub_eq_zero, ← hα] at hx
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_mul_of_pow_eq hx
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _)
    (Algebra.self_mem_adjoin_singleton K α)

/-- Version of `IntermediateField.adjoin_root_eq_top_of_isSplittingField` without the
irreducibility of `X ^ n - C a`. -/
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField' {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] {α : L} (hα : α ^ n = algebraMap K L a) : K⟮α⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin _ _ _
    (Algebra.adjoin_root_eq_top_of_isSplittingField' hζ hα).symm).symm

/-- If `K` contains a primitive `n`-th root of unity and the splitting field `L` of `X ^ n - C a`
has degree `n` over `K`, then `X ^ n - C a` is irreducible. -/
lemma irreducible_X_pow_sub_C_of_isSplittingField {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] (hn : Module.finrank K L = n) :
    Irreducible (X ^ n - C a) := by
  have : NeZero n := ⟨fun h ↦ by simp [h] at hζ⟩
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C a)
  obtain ⟨α, hα⟩ : ∃ α : L, α ^ n = algebraMap K L a := ⟨_, rootOfSplitsXPowSubC_pow a L⟩
  have htop := IntermediateField.adjoin_root_eq_top_of_isSplittingField' hζ hα
  rw [← hn] at hα ⊢
  exact irreducible_X_pow_sub_C_of_root_adjoin_eq_top hα htop

/-- Kummer group characterization: let `K` be a field with a primitive `n`-th root of unity `ζ`,
`a ∈ Kˣ` with `X ^ n - a` irreducible, `α` a root of `X ^ n - a` in `L = K(α)`, and
`σ ∈ Gal(L/K)` the automorphism defined by `σ(α) = ζ * α`.
If `β ∈ L` satisfies `β ^ n ∈ Kˣ`, then `β = λ * α ^ j` for some `λ ∈ K` and `j < n`. -/
theorem exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (hK : (primitiveRoots n K).Nonempty) {L : Type*} [Field L] [Algebra K L] {a : K}
    (hIrr : Irreducible (X ^ n - C a)) [IsSplittingField K L (X ^ n - C a)] {α : L}
    (hα : α ^ n = algebraMap K L a) {β : L} {b : K} (hβ : β ^ n = algebraMap K L b) :
    ∃ (c : K) (j : ℕ), j < n ∧ β = algebraMap K L c * α ^ j := by
  classical
  have hmp : minpoly K α = X ^ n - C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr (by simp [hα])
      (monic_X_pow_sub_C a (NeZero.ne n))).symm
  have hint : IsIntegral K α := ⟨X ^ n - C a, monic_X_pow_sub_C a (NeZero.ne n),
    hmp ▸ minpoly.aeval K α⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_root_eq_top_of_isSplittingField hK hIrr hα
  obtain ⟨ζ, hζ⟩ := hK
  replace hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_of_mem_primitiveRoots hζ
  let σ := (autEquivZmod hIrr L hζ).symm (Multiplicative.ofAdd 1)
  have hσ : σ α = algebraMap K L ζ * α := by
    have := autEquivZmod_symm_apply_natCast hIrr L hα hζ 1
    rwa [pow_one, Algebra.smul_def, Nat.cast_one] at this
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective
  have hσβn : (σ β) ^ n = β ^ n := by rw [← map_pow, hβ, AlgEquiv.commutes]
  obtain ⟨j, hj, hσβ⟩ := hζL.eq_pow_mul_of_pow_eq hσβn
  let B := PowerBasis.ofAdjoinSimpleEqTop hint hgen
  have hsB {i} : σ (B.basis i) = algebraMap K L ζ ^ i.val * (B.basis i) := by
    simp [PowerBasis.coe_basis, B, hσ, mul_pow]
  have hdB : B.dim = n := by rw [PowerBasis.ofAdjoinSimpleEqTop_dim, hmp, natDegree_X_pow_sub_C]
  let j₀ : Fin B.dim := ⟨j, by rwa [hdB]⟩
  refine ⟨B.basis.equivFun β j₀, j, hj, ?_⟩
  have h₀ := B.basis.sum_equivFun β
  nth_rewrite 1 [← h₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have {i} (hi : i ∈ Finset.univ.erase j₀) : B.basis.equivFun β i = 0 := by
    have h₁ := (congr_arg σ h₀).trans hσβ
    nth_rewrite 2 [← h₀] at h₁
    simp_rw [map_sum, map_smul, hsB] at h₁
    rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
    simp_rw [Algebra.smul_def, ← mul_assoc, ← map_pow, ← map_mul, ← sub_mul, ← map_sub,
      ← Algebra.smul_def, mul_comm, ← sub_mul] at h₁
    have := linearIndependent_iff'.mp B.basis.linearIndependent _ _ h₁ i (Finset.mem_univ i)
    rwa [mul_eq_zero_iff_left] at this
    contrapose hi
    simpa [j₀, Fin.ext_iff] using hζ.pow_inj (Fin.val_lt_of_le i hdB.le) hj (sub_eq_zero.mp hi)
  simp +contextual [j₀, this, Algebra.smul_def, B]
variable {F : Type*} [Field F] {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra K F]
  [IsGalois K F] {μ : F} {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
open Module
end

/-- Version of `exists_root_adjoin_eq_top_of_isCyclic` with a nonzero root `α`. -/
theorem exists_root_adjoin_eq_top_of_isCyclic' (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    ∃ α : L, α ≠ 0 ∧ α ^ Module.finrank K L ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  obtain ⟨α, hα, hα'⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  obtain rfl | h := eq_or_ne α 0
  · rw [adjoin_zero] at hα'
    exact ⟨1, one_ne_zero, ⟨1, by simp⟩, by rwa [adjoin_one]⟩
  · exact ⟨α, h, hα, hα'⟩

end

section

namespace Ideal
open scoped Pointwise
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- An arithmetic Frobenius `σ` acts on the residue ring `S ⧸ Q` as the `N𝔭`-th power map, for any
action of `σ` on `S ⧸ Q` compatible with its action on `S` (`SMulDistribClass`, giving
`σ • mk x = mk (σ • x)` via `algebraMap.smul'`). -/
theorem _root_.IsArithFrobAt.smul_residue {M : Type*} [Monoid M] [MulSemiringAction M S]
    [SMulCommClass M R S] {Q : Ideal S} [MulDistribMulAction M (S ⧸ Q)]
    [SMulDistribClass M S (S ⧸ Q)] {σ : M} (H : IsArithFrobAt R σ Q) (c : S ⧸ Q) :
    σ • c = c ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← Ideal.Quotient.algebraMap_eq, ← algebraMap.smul']
  exact H.mk_apply x

/-- A subgroup element is an arithmetic Frobenius if its image in `G` is (the subgroup acts via the
inclusion, so the actions agree definitionally). -/
theorem _root_.IsArithFrobAt.of_coe {H : Subgroup G} {σ : H} {Q : Ideal S}
    (h : IsArithFrobAt R (σ : G) Q) : IsArithFrobAt R σ Q := h

variable (G) in
/-- The **tame character** `θ : I(Q) → (S ⧸ Q)ˣ`, the determinant of the `S ⧸ Q`-linear action of an
inertia element on the cotangent space `Q ⧸ Q ^ 2`. -/
noncomputable def tameCharacter (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) →* (S ⧸ Q)ˣ :=
  LinearEquiv.det.comp (DistribMulAction.toModuleAut (S ⧸ Q) Q.Cotangent)

/-- The value of the tame character at `τ` is the determinant of the action of `τ`. -/
theorem tameCharacter_apply (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q τ = (DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ).det := rfl
open Module

/-- If an inertia element `τ` satisfies `τ • x ≡ x mod Q ^ 2` for `x ∈ Q`, then it satisfies
`τ • x ≡ x mod Q ^ (n + 1)` for `x ∈ Q ^ n`. -/
theorem sub_mem_pow_of_sub_mem (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ x ∈ Q, τ • x - x ∈ Q ^ 2) (n : ℕ) {x : S} (hx : x ∈ Q ^ n) :
    τ • x - x ∈ Q ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
    simp_all only [pow_zero, one_eq_top, Submodule.mem_top, zero_add, pow_one]
    exact τ.prop x
  | succ n hind =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun x hx y hy ↦ ?_) fun x y hx hy ↦ ?_
      · rw [show τ • (x * y) - x * y = (τ • x - x) * τ • y + x * (τ • y - y)
          by rw [MulSemiringAction.smul_mul]; ring]
        refine Submodule.add_mem _ ?_ ?_
        · rw [add_right_comm, pow_add, pow_one]
          exact Submodule.mul_mem_mul (hind hx) (smul_mem_of_mem_stabilizer _ _ hy)
        · rw [show n + 1 + 1 = n + 2 by ring, pow_add]
          exact Submodule.mul_mem_mul hx (h _ hy)
      · rw [smul_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx hy

/-- If `τ` is inertia, fixes every graded piece, and has order prime to the residue
characteristic, then `τ • x ≡ x` modulo every power of `Q`. Proof: `τ ^ m = id + m·δ + …` with
`δ = τ - id`; since `m` is a unit in `S ⧸ Q`, the bound on `δ` improves by one at each power. -/
theorem sub_mem_pow_of_coprime (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q))
    (hstep : ∀ ⦃n : ℕ⦄, ∀ x ∈ Q ^ n, τ • x - x ∈ Q ^ (n + 1))
    (hord : ↑(orderOf τ) ∉ Q) (n : ℕ) (x : S) :
    τ • x - x ∈ Q ^ n := by
  set δ := τ • x - x with δ_def
  induction n with
  | zero => simp
  | succ n hind =>
      have h₁ {k : ℕ} : (τ ^ k • δ) - δ ∈ Q ^ (n + 1) := by
        induction k with
        | zero => simp
        | succ k hind' =>
            have : τ ^ k • (τ • δ - δ) + (τ ^ k • δ - δ) = τ ^ k • τ • δ - δ := by
              calc
                _ = τ ^ k • τ • δ - τ ^ k • δ + (τ ^k • δ - δ) := by rw [smul_sub]
                _ = τ ^ k • τ • δ - δ := by ring
            rw [pow_succ τ, ← smul_smul, ← this]
            exact Ideal.add_mem _ (smul_mem_pow_of_mem_stabilizer _ _ (hstep _ hind)) hind'
      simp_rw [← Quotient.mk_eq_mk_iff_sub_mem] at h₁
      have h₂ : ∑ k ∈ Finset.range (orderOf τ),
        Ideal.Quotient.mk (Q ^ (n + 1)) (τ ^ k • δ) = 0 := by
        simp only [δ_def, smul_sub, smul_smul, ← pow_succ]
        rw [← map_sum, Finset.sum_range_sub (fun k ↦ τ ^ k • x), pow_orderOf_eq_one τ, pow_zero,
          sub_self, map_zero]
      simp_rw [h₁, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h₂
      rwa [IsUnit.mul_right_eq_zero, Quotient.eq_zero_iff_mem] at h₂
      exact Quotient.isUnit_mk_pow_of_notMem _ hord

/-- The localization of a Dedekind domain at a nonzero maximal ideal is a discrete valuation ring.
A local instance so that `Ideal.finrank_cotangent_eq_one` applies to the cotangent line
  `Q ⧸ Q ^ 2`. -/
private instance [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q] :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S (NeZero.ne Q) _

/-- In dimension one, the cotangent action of an inertia element is the homothety by its tame
character: `cotangentInertiaAction G Q τ = θ(τ) • id`. -/
theorem cotangentInertiaAction_apply_eq_smul [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal]
    [NeZero Q] (τ : Q.inertia (MulAction.stabilizer G Q)) (v : Q.Cotangent) :
    τ • v = (tameCharacter G Q τ).val • v := by
  let := Ideal.Quotient.field Q
  rw [tameCharacter_apply, LinearEquiv.coe_det]
  exact LinearMap.apply_eq_det_smul_of_finrank_eq_one Q.finrank_cotangent_eq_one
    (DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ) v

/-- If `θ(τ) = 1` then `τ` fixes the cotangent line `Q ⧸ Q ^ 2`: for `x ∈ Q`,
`τ • x ≡ x mod Q ^ 2`. Uses that `Q ⧸ Q ^ 2` is one-dimensional over the field `S ⧸ Q`, so
`det = 1` forces the action to be the identity. -/
theorem sub_mem_sq_of_tameCharacter_eq_one [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal]
    [NeZero Q]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (h : tameCharacter G Q τ = 1) {x : S} (hx : x ∈ Q) :
    τ • x - x ∈ Q ^ 2 := by
  let := Ideal.Quotient.field Q
  have : DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ = 1 := by
    rw [← LinearEquiv.toLinearMap_inj, LinearEquiv.coe_toLinearMap_one,
      ← LinearMap.det_eq_one_iff_eq_id_of_finrank_eq_one Q.finrank_cotangent_eq_one,
      ← LinearEquiv.coe_det,
      ← tameCharacter_apply, h, Units.val_one]
  simpa [DistribMulAction.toLinearEquiv_apply, MulAction.subgroup_smul_def,
    smul_toCotangent, toCotangent_eq] using LinearEquiv.congr_fun this (Q.toCotangent ⟨x, hx⟩)

/-- An inertia element acting trivially on `S` is trivial. Uses Krull's intersection
theorem (`⋂ₙ Q ^ n = ⊥`) to pass from "trivial modulo every power" to "trivial", and faithfulness
of the action to conclude `τ = 1`. -/
theorem eq_one_of_forall_sub_mem_pow [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S)
    [hQ : Q.IsMaximal] (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ (n : ℕ) (x : S), τ • x - x ∈ Q ^ n) : τ = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ ?_
  simpa [iInf_pow_eq_bot_of_isDomain _ hQ.ne_top, sub_eq_zero] using mem_iInf.mpr fun i ↦ h i x

/-- An inertia element of order prime to the residue
characteristic on which the tame character vanishes is trivial. -/
theorem eq_one_of_tameCharacter_eq_one [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S)
    [Q.IsMaximal] [NeZero Q] (τ : Q.inertia (MulAction.stabilizer G Q)) (hord : ↑(orderOf τ) ∉ Q)
    (h : tameCharacter G Q τ = 1) : τ = 1 := by
  apply eq_one_of_forall_sub_mem_pow
  apply sub_mem_pow_of_coprime
  · apply sub_mem_pow_of_sub_mem
    exact fun x a ↦ sub_mem_sq_of_tameCharacter_eq_one Q τ h a
  · exact hord

variable (G) in
/-- The tame character is injective when the order of the inertia group is prime to the residue
characteristic. -/
theorem tameCharacter_injective [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal]
    [NeZero Q] (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Function.Injective (tameCharacter G Q) := by
  refine (injective_iff_map_eq_one _).mpr fun τ hτ ↦ eq_one_of_tameCharacter_eq_one _ _ ?_ hτ
  contrapose htame
  obtain ⟨q, hq⟩ := Nat.cast_dvd_cast (α := S) <| orderOf_dvd_natCard τ
  exact hq ▸ Ideal.mul_mem_right _ _ htame

attribute [local instance] Ideal.Quotient.field in
/-- Conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N 𝔭`-th power. (Conjugation lands back in inertia by
normality, via `MulAut.conjNormal`.) -/
theorem tameCharacter_conj [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (σ : MulAction.stabilizer G Q) (hσ : IsArithFrobAt R σ Q)
    (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q (MulAut.conjNormal σ τ) = tameCharacter G Q τ ^ Nat.card (R ⧸ Q.under R) := by
  suffices DistribSMul.toLinearMap (S ⧸ Q) Q.Cotangent (MulAut.conjNormal σ τ) =
      (σ • (tameCharacter G Q τ).val) • LinearMap.id by
    rw [Units.ext_iff, tameCharacter_apply, LinearEquiv.coe_det,
      DistribMulAction.coe_toLinearEquiv, congr_arg (LinearMap.det · ) this, hσ.smul_residue,
      LinearMap.det_smul, Q.finrank_cotangent_eq_one, pow_one, LinearMap.det_id, mul_one,
      Units.val_pow_eq_pow_val]
  ext v
  rw [DistribSMul.toLinearMap_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    show v = σ • (σ⁻¹ • v) by rw [smul_inv_smul], MulAction.subgroup_smul_def,
    MulAut.conjNormal_apply, ← smul_smul, inv_smul_smul, ← smul_smul,
    ← MulAction.subgroup_smul_def, cotangentInertiaAction_apply_eq_smul, stabilizer_smul_smul]

/-- If the order of the inertia group is prime to the residue
characteristic (tame ramification), the inertia group is cyclic. -/
theorem isCyclic_inertia [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [Finite (S ⧸ Q)] [FaithfulSMul G S]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    IsCyclic (Q.inertia (MulAction.stabilizer G Q)) :=
  isCyclic_of_injective _ (tameCharacter_injective G Q htame)

/-- For an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [FaithfulSMul G S] [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Nat.card (Q.inertia (MulAction.stabilizer G Q)) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp <| isCyclic_inertia Q htame
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant R G Q
  rw [← hτ, ← orderOf_injective _ (tameCharacter_injective G Q htame), ← Int.natCast_dvd_natCast,
    orderOf_dvd_iff_zpow_eq_one, Nat.cast_sub hσ.card_pos, Nat.cast_one, zpow_sub_one,
    zpow_natCast, ← tameCharacter_conj Q ⟨σ, hσ.mem_stabilizer⟩ hσ.of_coe τ,
    MulAut.conjNormal_apply_of_isMulCommutative, mul_inv_cancel]

variable (G) in
/-- Inertia computed inside the full group `G` agrees with inertia computed inside the decomposition
group `MulAction.stabilizer G Q`: every inertia element fixes `Q` (`inertia_le_stabilizer`), so the
inclusion of the decomposition group restricts to an isomorphism of inertia groups. -/
def inertiaStabilizerEquiv (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) ≃* Q.inertia G :=
  Subgroup.subgroupOfEquivOfLe Q.inertia_le_stabilizer

/-- Version of `isCyclic_inertia` for the full group `G`: tame inertia inside the full group `G`
(not merely inside the decomposition group) is cyclic. -/
theorem isCyclic_inertia' [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [Finite (S ⧸ Q)] [FaithfulSMul G S] (htame : ↑(Nat.card (Q.inertia G)) ∉ Q) :
      IsCyclic (Q.inertia G) :=
  (inertiaStabilizerEquiv G Q).isCyclic.mp <|
    isCyclic_inertia Q (by rwa [Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv])

/-- The tameness hypothesis `↑(Nat.card (Q.inertia G)) ∉ Q` used by `isCyclic_inertia'` is exactly
the classical tameness condition: the residue characteristic (`absNorm` of the prime `Q ∩ ℤ`) does
not divide the ramification index `e(Q)`. -/
theorem card_inertia_notMem_iff [IsDomain S] (Q : Ideal S) [Q.IsPrime] [Module.Finite ℤ S]
    [Module.Flat ℤ S] [IsGaloisGroup G ℤ S] [Finite G] :
    ↑(Nat.card (Q.inertia G)) ∉ Q ↔ ¬ (under ℤ Q).absNorm ∣ ramificationIdx Q ℤ := by
  rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, Int.natCast_dvd_natCast,
    card_inertia_eq_ramificationIdxIn (under ℤ Q), ramificationIdxIn_eq_ramificationIdx _ Q G]

/-- Version of `card_inertia_dvd_card_sub_one` for the full group `G`: for an abelian action, the
order of the inertia group (the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one' [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [FaithfulSMul G S] [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : ↑(Nat.card (Q.inertia G)) ∉ Q) :
    Nat.card (Q.inertia G) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  rw [← Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv]
  exact card_inertia_dvd_card_sub_one Q
    (by rwa [Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv])
end Ideal

end

section

/-- If `G` is a finite Galois group of `L/K`, then `L/K` is separable. -/
theorem IsGaloisGroup.isSeparable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L]
    [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L] : Algebra.IsSeparable K L :=
  have := IsGaloisGroup.isGalois G K L
  inferInstance

namespace Algebra
variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S']

/-- `Algebra.IsUnramifiedIn` transfers along an isomorphism of `R`-algebras. -/
theorem IsUnramifiedIn.of_algEquiv (e : S ≃ₐ[R] S') {𝔭 : Ideal R}
    (h : Algebra.IsUnramifiedIn S 𝔭) : Algebra.IsUnramifiedIn S' 𝔭 := by
  intro 𝔔 _ hlo
  have : IsUnramifiedAt R (𝔔.comap e) := h _ inferInstance inferInstance
  exact FormallyUnramified.of_equiv (Localization.localAlgEquiv (𝔔.comap e) 𝔔 e rfl)

/-- Unramifiedness descends to the bottom of a tower `R → S → T`: if a prime `𝔭` of `R` is
unramified in the top ring `T`, then it is unramified in the intermediate ring `S`. This is the
ring-tower generalisation of "a subfield of an extension unramified at `𝔭` is itself unramified
at `𝔭`". -/
theorem IsUnramifiedIn.tower_bot {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.EssFiniteType R S]
    [Algebra.EssFiniteType R T] [Algebra.IsIntegral S T] [FaithfulSMul S T]
    [Module.Flat S T] [IsDomain T]
    {𝔭 : Ideal R} (h : Algebra.IsUnramifiedIn T 𝔭) :
    Algebra.IsUnramifiedIn S 𝔭 := by
  intro P _ _
  obtain ⟨Q, hQ₁, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat P (B := T)
  have := h Q hQ₁ (Ideal.LiesOver.trans Q P 𝔭)
  exact Algebra.IsUnramifiedAt.of_liesOver _ P Q

/-- Let `K` and `L` be fraction fields of `R` and `S`. If `L/K` is separable, then `S` is
unramified over `R` at the zero ideal. -/
theorem isUnramifiedAt_bot_of_isSeparable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] [Algebra.IsSeparable K L] :
    IsUnramifiedAt R (⊥ : Ideal S) := by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  have : FormallyUnramified R K := .of_isLocalization (nonZeroDivisors R)
  have : FormallyUnramified K L := .of_isSeparable K L
  have : FormallyUnramified R L := .comp R K L
  exact .of_equiv ((IsLocalization.algEquiv (nonZeroDivisors S) _ L).restrictScalars R).symm
end Algebra

namespace Ideal.IsInertiaRing
open Ideal
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [Algebra C B] [IsScalarTower A C B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B] (P : Ideal B) [hP : P.IsPrime] {p : Ideal A} [P.LiesOver p]
  [hC : P.IsInertiaRing G C] [IsDomain A] [IsDomain B] [IsDomain C] [Module.Finite A B]
  [Module.Flat A B] [Module.Flat C B] [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B]
  [Algebra.EssFiniteType A C]

attribute [local instance] FractionRing.liftAlgebra in
include G in
/-- The prime of an inertia ring `C` of `P` lying under `P` is unramified over `A`. -/
theorem isUnramifiedAt : Algebra.IsUnramifiedAt A (P.under C) := by
  obtain rfl | hP := eq_or_ne P ⊥
  · have : FaithfulSMul A C := .tower_bot A C B
    have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
      let := IsFractionRing.mulSemiringAction G B (FractionRing B)
      exact (IsGaloisGroup.to_isFractionRing G A B _ _).isSeparable G _ _
    have : Algebra.IsSeparable (FractionRing A) (FractionRing C) :=
      Algebra.isSeparable_tower_bot_of_isSeparable _ _ (FractionRing B)
    simpa using Algebra.isUnramifiedAt_bot_of_isSeparable (R := A) (S := C)
      (FractionRing A) (FractionRing C)
  · have : Algebra.IsIntegral A C := .tower_bot B
    have : NeZero (under A (under C P)) := ⟨by simpa [under_under] using under_ne_bot _ hP⟩
    rw [← ramificationIdx_eq_one_iff]
    have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP inferInstance
    exact IsInertiaRing.ramificationIdx_eq G P C (under A P) (under C P) <| by
      simpa [under_under] using under_ne_bot A hP

include G in
/-- If the inertia group of `P` is normal (e.g. if `G` is commutative), then `p` is unramified in
an inertia ring `C` of `P`. -/
theorem isUnramifiedIn [(inertia G P).Normal] : Algebra.IsUnramifiedIn C p := by
  have : Algebra.IsIntegral C B := .tower_top A
  intro 𝓠 h𝓠₁ h𝓠₂
  obtain ⟨Q, ⟨_, hQ⟩⟩ := Ideal.nonempty_primesOver (S := B) 𝓠
  have : Q.IsInertiaRing G C := by
    have : Q.LiesOver p := LiesOver.trans Q 𝓠 p
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
    have : inertia G Q = inertia G P := by
      rw [← hσ, inertia_smul]
      exact Subgroup.Normal.conj_smul_eq_self σ _
    exact { toIsGaloisGroup := this ▸ hC.toIsGaloisGroup }
  rw [liesOver_iff] at hQ
  simp_rw [hQ]
  exact isUnramifiedAt G Q
end Ideal.IsInertiaRing
open NumberField Ideal IntermediateField

/-- `K/ℚ` is unramified outside `p`: every prime `q ≠ p` is unramified in `𝓞 K`. -/
def UnramifiedOutside (K : Type*) [Field K] (p : ℕ) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})
variable (p : ℕ)

open NumberField in
/-- The bottom of a tower `ℚ → K → L` inherits unramifiedness: if `L` is unramified outside `p`, so
is the subfield `K` (a sub-extension of an unramified-outside-`p` extension is unramified outside
`p`). -/
lemma UnramifiedOutside.tower_bot {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (h : UnramifiedOutside L p) : UnramifiedOutside K p :=
  fun q hq hqp ↦ (h q hq hqp).tower_bot

open NumberField in
/-- A cyclotomic extension `ℚ(ζ_n)` is unramified at every prime not dividing `n`. -/
lemma isUnramifiedIn_of_isCyclotomicExtension {K : Type*} [Field K] [NumberField K] {n : ℕ}
    [NeZero n] [IsCyclotomicExtension {n} ℚ K] [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun P _ hP ↦ ?_
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpn

/-- The cyclotomic field `ℚ(ζ_{p ^ k})` is unramified outside `p`. -/
lemma UnramifiedOutside.of_isCyclotomicExtension (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [hp : Fact p.Prime] [IsCyclotomicExtension {p ^ k} ℚ K] : UnramifiedOutside K p :=
  fun q hq hqp ↦
    have : Fact q.Prime := ⟨hq⟩
    isUnramifiedIn_of_isCyclotomicExtension q (n := p ^ k) fun h ↦
      hqp <| (Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h)

/-- The cyclotomic field `ℚ(ζ_{p})` is unramified outside `p`. -/
lemma UnramifiedOutside.of_isCyclotomicExtension' (K : Type*) [Field K] [NumberField K]
    [Fact p.Prime] [hK : IsCyclotomicExtension {p } ℚ K] : UnramifiedOutside K p := by
  rw [← pow_one p] at hK
  exact .of_isCyclotomicExtension p 1 K

open NumberField IntermediateField in
/-- Let `K` and `F` be subfields of `L`. If a nonzero ideal `p` of `ℤ` is unramified in `𝓞 K` and
in `𝓞 F`, then it is unramified in `𝓞 (K ⊔ F)`. -/
lemma isUnramifiedIn_sup {L : Type*} [Field L] [NumberField L] (K F : IntermediateField ℚ L)
    {p : Ideal ℤ} (hp : p ≠ ⊥) (hK : Algebra.IsUnramifiedIn (𝓞 K) p)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) p) :
    Algebra.IsUnramifiedIn (𝓞 ↥(K ⊔ F)) p := by
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun 𝓟 _ h𝓟 ↦ ?_
  have : p.IsPrime := 𝓟.isPrime_of_liesOver p
  have : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  have : 𝓟.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (ne_bot_of_liesOver_of_ne_bot hp 𝓟)
  obtain ⟨P, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝓟
  have : P.LiesOver p := LiesOver.trans P 𝓟 p
  have := LiesOver.tower_bot P (under (𝓞 K) P) p
  have := LiesOver.tower_bot P (under (𝓞 F) P) p
  exact ramificationIdx_sup_eq_one (A := ℤ) (p := p) ℚ L P K F (𝓞 ↥(K ⊔ F)) 𝓟
    (ramificationIdx_eq_one_iff.mpr (hK _ (IsPrime.under (𝓞 K) P) inferInstance))
    (ramificationIdx_eq_one_iff.mpr (hF _ (IsPrime.under (𝓞 F) P) inferInstance))

open NumberField IntermediateField in
/-- Let `K` and `F` be subfields of `L` with `K ⊔ F = ⊤`. If a nonzero ideal `p` of `ℤ` is
unramified in `𝓞 K` and in `𝓞 F`, then it is unramified in `𝓞 L`. -/
lemma isUnramifiedIn_sup' {L : Type*} [Field L] [NumberField L] (K F : IntermediateField ℚ L)
    (htop : K ⊔ F = ⊤) {p : Ideal ℤ} (hp : p ≠ ⊥) (hK : Algebra.IsUnramifiedIn (𝓞 K) p)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) p) :
    Algebra.IsUnramifiedIn (𝓞 L) p :=
  .of_algEquiv (RingOfIntegers.mapIntAlgEquiv
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toRingEquiv)
    (isUnramifiedIn_sup K F hp hK hF)

/-- Top-field version of `unramifiedOutside_sup`: if `K` and `F` are both unramified outside `p` and
together generate the whole field (`K ⊔ F = ⊤`), then `L` itself is unramified outside `p`. The
general form `unramifiedOutside_sup` (compositum inside an arbitrary ambient) reduces to this. -/
lemma unramifiedOutside_sup' {L : Type*} [Field L] [NumberField L] (K F : IntermediateField ℚ L)
    (hKram : UnramifiedOutside K p) (hFram : UnramifiedOutside F p) (htop : K ⊔ F = ⊤) :
    UnramifiedOutside L p := fun q hq hqp ↦
  isUnramifiedIn_sup' K F htop (by simpa using hq.ne_zero) (hKram q hq hqp) (hFram q hq hqp)

set_option backward.isDefEq.respectTransparency false in
/-- The compositum `K ⊔ F` of two number fields, each unramified outside `p`, is itself unramified
outside `p`. -/
lemma unramifiedOutside_sup {A : Type*} [Field A] [CharZero A] (K F : IntermediateField ℚ A)
    [NumberField K] [NumberField F] (hKram : UnramifiedOutside K p)
    (hFram : UnramifiedOutside F p) :
    UnramifiedOutside ↑(K ⊔ F) p := by
  let F' : IntermediateField ℚ ↑(K ⊔ F) := F.restrict le_sup_right
  let K' : IntermediateField ℚ ↑(K ⊔ F) := K.restrict le_sup_left
  refine unramifiedOutside_sup' p K' F' ?_ ?_
    (lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top]))
  · exact fun q hq hqp ↦ (hKram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrictAlgEquiv (le_sup_left : K ≤ K ⊔ F))).restrictScalars ℤ)
  · exact fun q hq hqp ↦ (hFram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrictAlgEquiv (le_sup_right : F ≤ K ⊔ F))).restrictScalars ℤ)

end

section

/-- A cyclotomic extension has a primitive root of unity. -/
theorem IsCyclotomicExtension.primitiveRoots_nonempty (n : ℕ) [NeZero n] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [hC : IsCyclotomicExtension {n} A B] :
    (primitiveRoots n B).Nonempty :=
  ⟨hC.zeta, (mem_primitiveRoots (NeZero.pos n)).mpr hC.zeta_spec⟩
open IntermediateField
open IsCyclotomicExtension.Rat NumberField

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat in
/-- An automorphism `σ` sends `ζ` to `ζ ^ k` exactly when `galEquivZMod` sends `σ` to `k`. -/
theorem IsCyclotomicExtension.Rat.apply_eq_pow_iff_galEquivZMod_eq {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] {σ : Gal(K/ℚ)}
    {k : ZMod n} {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    σ ζ = ζ ^ k.val ↔ galEquivZMod n K σ = k := by
  rw [galEquivZMod_apply_of_pow_eq n K σ hζ.pow_eq_one, ← (hζ.isUnit (NeZero.ne n)).unit_spec ,
    ←  Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.ext_iff, pow_eq_pow_iff_modEq,
    ← (hζ.isUnit_unit (NeZero.ne n)).eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

open IsCyclotomicExtension IsCyclotomicExtension.Rat in
/-- In a cyclotomic field, complex conjugation corresponds to `-1` under `galEquivZMod`. -/
theorem IsCyclotomicExtension.Rat.galEquivZMod_ratComplexConj (n : ℕ) [NeZero n] (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsCMField K] :
    galEquivZMod n K (IsCMField.ratComplexConj K) = -1 := by
  rw [Units.ext_iff, Units.val_neg, Units.val_one,
    show (-1 : ZMod n) = ((n - 1  : ℕ): ZMod n) by simp [Nat.cast_sub NeZero.one_le],
    ← apply_eq_pow_iff_galEquivZMod_eq (zeta_spec n ℚ K), IsCMField.ratComplexConj_apply,
    IsCMField.complexConj_eq_inv_of_isPrimitiveRoot (zeta_spec n ℚ K), ZMod.val_natCast,
    Nat.self_sub_mod, ← zpow_natCast, Nat.cast_sub NeZero.one_le, Nat.cast_one, zpow_sub_one₀
    ((zeta_spec n ℚ K).ne_zero (NeZero.ne n)), zpow_natCast, (zeta_spec n ℚ K).pow_eq_one, one_mul]

namespace IsCyclotomicExtension.Rat
open Ideal NumberField
variable (p k : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]

/-- The ideal generated by `ζ - 1` is maximal. -/
instance isMaximal_span_zeta_sub_one [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : IsMaximal (span {hζ.toInteger - 1}) :=
  (isPrime_span_zeta_sub_one p k hζ).isMaximal (span_zeta_sub_one_ne_bot p k hζ)
end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat
open NumberField IsCMField Units Ideal
variable (p k : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCMField K]

attribute [local instance] Ideal.Quotient.field in
/-- For an odd prime `p`, the units of `ℚ(ζ_{p^(k+1)})` are generated by the real units and the
roots of unity. -/
theorem indexRealUnits_eq_one [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] (hp₂ : p ≠ 2) :
    indexRealUnits K = 1 := by
  refine (indexRealUnits_eq_one_or_two K).resolve_right fun h ↦ ?_
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h
  set η := unitsMulComplexConjInv K u
  -- The generator `η` of the torsion has order `2 * p ^ (k + 1)`.
  have h₁ : orderOf η = p ^ (k + 1) * 2 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hu, ← torsionOrder, torsionOrder_eq (n := p ^ (k + 1)),
      ite_eq_right, mul_comm]
    rw [Nat.not_even_iff_odd, Nat.odd_pow_iff (NeZero.ne _)]
    exact hp.out.odd_of_ne_two hp₂
  -- Hence `η ^ p ^ (k + 1) = -1`.
  have h₂ : ((η ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) = (-1 : 𝓞 K):= by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    apply IsPrimitiveRoot.pow (by grind [hp.out.pos]) ?_ rfl
    rwa [IsPrimitiveRoot.iff_orderOf, orderOf_units, Subgroup.orderOf_coe]
  -- Complex conjugation is trivial modulo `ζ - 1`, so `η ≡ 1`.
  let hζ := zeta_spec (p ^ (k + 1)) ℚ K
  have h₃ : Ideal.Quotient.mk (span {hζ.toInteger - 1}) ((η : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [unitsMulComplexConjInv_apply, val_mul, map_mul, map_units_inv, coe_unitsComplexConj,
      ← RingHom.coe_coe (ringOfIntegersComplexConj K), quotientMk_span_zeta_sub_one_apply,
      mul_inv_cancel₀]
    exact fun h ↦ IsMaximal.ne_top inferInstance <|
      eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp h) u.isUnit
  -- Then `-1 ≡ 1`, so `ζ - 1` divides `2`.
  apply hζ.toInteger_sub_one_not_dvd_two hp₂
  have := congr_arg (· ^ p ^ (k + 1)) h₃
  rw [one_pow] at this
  rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← one_add_one_eq_two, map_add,
    ← eq_neg_iff_add_eq_zero, ← map_neg, map_one, ← this, ← h₂, SubmonoidClass.coe_pow,
    val_pow_eq_pow_val, map_pow]

/-- Version of `indexRealUnits_eq_one` for `ℚ(ζ_p)`. -/
theorem indexRealUnits_eq_one' [hK : IsCyclotomicExtension {p} ℚ K] (hp₂ : p ≠ 2) :
    indexRealUnits K = 1 := by
  rw [← pow_one p] at hK
  exact indexRealUnits_eq_one p 0 K hp₂
end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

section
variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

/-- The Galois group of `ℚ(ζₙ)` is cyclic iff `(ℤ/nℤ)ˣ` is cyclic. -/
theorem isCyclic_iff_isCyclic_units : IsCyclic Gal(K/ℚ) ↔ IsCyclic (ZMod n)ˣ :=
  (galEquivZMod n K).isCyclic
end
variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

/-- The Galois group of `ℚ(ζ_{p ^ k})` is cyclic for `p` an odd prime. -/
theorem isCyclic_of_prime_pow (k : ℕ) (hp' : p ≠ 2) [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclic Gal(K/ℚ) :=
  (isCyclic_iff_isCyclic_units (p ^ k) K).mpr (ZMod.isCyclic_units_of_prime_pow p hp.out hp' k)
end IsCyclotomicExtension.Rat

end
