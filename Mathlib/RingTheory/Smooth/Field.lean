/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.FieldTheory.TranscendentalSeparable

/-!

# Smooth algebras over fields

We show that separably generated extensions of fields are smooth.
In particular finitely generated field extensions over perfect fields are smooth.

-/

@[expose] public section

section

open Algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable {ιS ιT : Type*} (GS : Algebra.Generators R S ιS) (GT : Algebra.Generators R T ιT)

/-- Hom of generators obtained directly from element level. -/
noncomputable def Algebra.Generators.HomOfComm [Algebra S T] (f : ιS → ιT)
    (comm : GT.val ∘ f = algebraMap S T ∘ GS.val) : GS.Hom GT where
  val s := MvPolynomial.X (f s)
  aeval_val s := by simpa using congr_fun comm s

lemma Algebra.Generators.homOfComm_toAlgHom [Algebra S T] [IsScalarTower R S T]
    (f : ιS → ιT) (comm : GT.val ∘ f = algebraMap S T ∘ GS.val) :
    (GS.HomOfComm GT f comm).toExtensionHom.toAlgHom = MvPolynomial.rename f :=
  rfl

lemma Algebra.Generators.homOfComm_toExtensionHom_toAlgHom [Algebra S T] [IsScalarTower R S T]
    (f : ιS → ιT) (comm : GT.val ∘ f = algebraMap S T ∘ GS.val) :
    (GS.HomOfComm GT f comm).toExtensionHom.toAlgHom = MvPolynomial.rename f :=
  Algebra.Generators.homOfComm_toAlgHom GS GT f comm

variable (R S T) in
/-- AlgebraMap as hom of generators. -/
noncomputable abbrev Algebra.Generators.HomOfCommSelf [Algebra S T] :
    (Algebra.Generators.self R S).Hom (Algebra.Generators.self R T) :=
  Algebra.Generators.HomOfComm _ _ (algebraMap S T) rfl

lemma Algebra.Generators.homOfComm_cotangentSpace_map_eq [Algebra S T] [IsScalarTower R S T]
    (f : ιS → ιT) (comm : GT.val ∘ f = algebraMap S T ∘ GS.val) :
    Extension.CotangentSpace.map (Generators.HomOfComm GS GT f comm).toExtensionHom =
    ((GT.cotangentSpaceBasis.repr.symm.restrictScalars S).comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap S T)).comp (Finsupp.lmapDomain S S f))).comp
    GS.cotangentSpaceBasis.repr.toLinearMap := by
  rw [← LinearEquiv.comp_toLinearMap_symm_eq]
  ext i
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have : (Extension.CotangentSpace.map (GS.HomOfComm GT f comm).toExtensionHom)
    (GS.cotangentSpaceBasis i) = GT.cotangentSpaceBasis (f i) := by
    simp only [cotangentSpaceBasis_apply]
    apply (Algebra.Extension.CotangentSpace.map_tmul _ _ _).trans
    simp only [map_one]
    congr
    rw [Generators.homOfComm_toExtensionHom_toAlgHom]
    exact MvPolynomial.rename_X _ _
  simpa using this

variable (R S T) in
lemma Algebra.Generators.homOfComm_cotangentSpace_map_injective_of_injective [Algebra S T]
    [IsScalarTower R S T] (inj : Function.Injective (algebraMap S T)) : Function.Injective
    (Extension.CotangentSpace.map (Generators.HomOfCommSelf R S T).toExtensionHom) := by
  rw [Algebra.Generators.homOfComm_cotangentSpace_map_eq]
  have inj : Function.Injective ((Finsupp.mapRange.linearMap (Algebra.linearMap S T)).comp
    (Finsupp.lmapDomain S S (algebraMap S T))) :=
    (Finsupp.mapRange_injective _ (map_zero _) inj).comp (Finsupp.mapDomain_injective inj)
  exact ((self R T).cotangentSpaceBasis.repr.symm.injective.comp inj).comp
    (self R S).cotangentSpaceBasis.repr.injective

variable (R S T) in
lemma Algebra.h1Cotangent_eq_comap_of_algebraMap_injective [Algebra S T] [IsScalarTower R S T]
    (inj : Function.Injective (algebraMap S T)) :
    (Generators.self R S).toExtension.cotangentComplex.ker = Submodule.comap
      (Extension.Cotangent.map (Generators.HomOfCommSelf R S T).toExtensionHom)
        ((Generators.self R T).toExtension.cotangentComplex.ker.restrictScalars S) := by
  have inj' := Algebra.Generators.homOfComm_cotangentSpace_map_injective_of_injective R S T inj
  rw [← LinearMap.ker_restrictScalars, ← LinearMap.ker_comp,
    ← Algebra.Extension.CotangentSpace.map_comp_cotangentComplex, LinearMap.ker_comp,
    LinearMap.ker_eq_bot_of_injective inj', Submodule.comap_bot]

lemma Algebra.Extension.ker_eq_comap_of_subalgebra (S : Subalgebra R T) :
    (Generators.self R S).toExtension.ker = (Generators.self R T).toExtension.ker.comap
    (MvPolynomial.rename S.val) := by
  have algmap_eq : (algebraMap (Generators.self R T).toExtension.Ring T).comp
    (MvPolynomial.rename S.val).toRingHom = S.val.toRingHom.comp
    (algebraMap (Generators.self R S).toExtension.Ring S) :=
    RingHom.ext (fun x ↦ (MvPolynomial.aeval_rename _ _ _).trans
      (MvPolynomial.aeval_algebraMap_apply _ _root_.id _))
  exact ((RingHom.comap_ker _ _).trans ((congr_arg RingHom.ker algmap_eq).trans
    (RingHom.ker_comp_of_injective _ Subtype.val_injective))).symm

lemma Algebra.h1Cotangent_subsingleton_of_subalgebra
    (h : ∀ (s : Finset T), ∃ (S : Subalgebra R T),
      (s : Set T) ⊆ S ∧ Subsingleton (H1Cotangent R S)) :
    Subsingleton (H1Cotangent R T) := by
  by_contra! ntr
  obtain ⟨x, hx, ne0⟩ : ∃ x ∈ (Generators.self R T).toExtension.cotangentComplex.ker, x ≠ 0 :=
    (AddSubmonoid.nontrivial_iff_exists_ne_zero _).mp ntr
  rcases Extension.Cotangent.mk_surjective x with ⟨y, hy⟩
  rcases MvPolynomial.exists_finset_rename y.1 with ⟨s, ⟨y', hy'⟩⟩
  rcases h s with ⟨S, sub, hS⟩
  obtain ⟨z, hz⟩ : ∃ (z : MvPolynomial S R), MvPolynomial.rename S.val z = y.1 := by
    use MvPolynomial.rename (Set.inclusion sub) y'
    simp only [Subalgebra.coe_val, SetLike.coe_sort_coe, MvPolynomial.rename_rename,
      Generators.toExtension_Ring, hy']
    congr 1
  have eqcomap : (Generators.self R S).toExtension.ker = (Generators.self R T).toExtension.ker.comap
    (MvPolynomial.rename S.val) := Algebra.Extension.ker_eq_comap_of_subalgebra S
  have zmem : z ∈ (Generators.self R S).toExtension.ker := by
    simpa [eqcomap] using Ideal.mem_comap.mpr (hz ▸ y.2)
  let z' : (Generators.self R ↥S).toExtension.Cotangent := Ideal.toCotangent _ ⟨z, zmem⟩
  have mapeq : Extension.Cotangent.map (Generators.HomOfCommSelf R S T).toExtensionHom z' = x := by
    apply (Algebra.Extension.Cotangent.map_mk _ _).trans
    simp only [Generators.homOfComm_toExtensionHom_toAlgHom, ← hy]
    congr 1
    exact SetCoe.ext hz
  have z'mem : z' ∈ (Generators.self R S).toExtension.cotangentComplex.ker := by
    simpa [h1Cotangent_eq_comap_of_algebraMap_injective R S T Subtype.val_injective,
      Submodule.mem_comap, mapeq] using hx
  absurd hS
  have : (⟨z', z'mem⟩ : H1Cotangent R S) ≠ 0 := by
    simpa [ne_eq, Submodule.mk_eq_zero] using ne_zero_of_map (mapeq.trans_ne ne0)
  exact not_subsingleton_iff_nontrivial.mpr (nontrivial_of_ne _ _ this)

end

variable {K L ι : Type*} [Field L] [Field K] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) :
    Algebra.FormallySmooth K (IntermediateField.adjoin K (Set.range v)) := by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

/-- Purely transcendental extensions are formally smooth. -/
lemma Algebra.FormallySmooth.of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

/-- Separably generated extensions are formally smooth. -/
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
    {v : ι → L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _

variable (K L) in
lemma Algebra.FormallySmooth.of_isSeparablyGenerated [Algebra.IsSeparablyGenerated K L] :
    Algebra.FormallySmooth K L := by
  rcases ‹Algebra.IsSeparablyGenerated K L› with ⟨ι, f, isT, sep⟩
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable isT.1

instance (priority := low) Algebra.FormallySmooth.of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have : Algebra.IsSeparable (↥(IntermediateField.adjoin K (Set.range ((↑) : s → L)))) L := by
    convert H <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1

variable (K L) in
lemma Algebra.FormallySmooth.of_isTranscendentalSeparable [Algebra.IsTranscendentalSeparable K L] :
    Algebra.FormallySmooth K L := by
  refine (Algebra.formallySmooth_iff _ _).mpr ⟨inferInstance, ?_⟩
  refine Algebra.h1Cotangent_subsingleton_of_subalgebra (fun s ↦ ?_)
  use (IntermediateField.adjoin K (s : Set L)).toSubalgebra
  refine ⟨IntermediateField.subset_adjoin _ _, ?_⟩
  have fg : EssFiniteType K (IntermediateField.adjoin K (s : Set L)) :=
    IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
  have sep := Algebra.IsTranscendentalSeparable.forall_isSeparablyGenerated
    (IntermediateField.adjoin K (s : Set L)) fg
  exact (Algebra.FormallySmooth.of_isSeparablyGenerated K
    (IntermediateField.adjoin K (s : Set L))).2
