import Mathlib.CFT.SmoothFibers
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian

instance {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A] :
  Algebra.Unramified R A where

instance {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R A] [FaithfulSMul R A] [IsDomain A]
    [Algebra.FormallyUnramified R A] :
    Algebra.Etale R A := by
  have : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Free R A := Module.free_of_finite_type_torsion_free' ..
  exact .of_formallyUnramified_of_flat

instance {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)] :
    HenselianLocalRing R where
  is_henselian f hf a ha ha' := HenselianRing.is_henselian f hf a ha (ha'.map _)

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [IsLocalRing S] [Nontrivial T]
    [Algebra.IsIntegral R T] (f : S →ₐ[R] T) : IsLocalHom f.toRingHom := by
  have : Algebra.IsIntegral f.range T := Algebra.IsIntegral.tower_top R
  have : IsLocalHom f.rangeRestrict.toRingHom := .of_surjective _ f.rangeRestrict_surjective
  exact RingHom.isLocalHom_comp (algebraMap f.range T) f.rangeRestrict.toRingHom

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [IsLocalRing S] [Nontrivial T]
    [Algebra.IsIntegral R T] (f : S ≃ₐ[R] T) : IsLocalHom f.toRingHom :=
  inferInstanceAs (IsLocalHom f.toAlgHom.toRingHom)
