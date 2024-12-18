/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places and the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions
 - `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its infinite places.
 - `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
   the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of `K`.
 - `NumberField.AdeleRing K` is the adele ring of a number field `K`.
 - `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
   locally compact space.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion DedekindDomain IsDedekindDomain

open scoped Classical

variable (K : Type*) [Field K]

/-! ## The infinite adele ring

The infinite adele ring is the finite product of completions of a number field over its
infinite places. See `NumberField.InfinitePlace` for the definition of an infinite place and
`NumberField.InfinitePlace.Completion` for the associated completion.
-/

/-- The infinite adele ring of a number field. -/
def InfiniteAdeleRing := (v : InfinitePlace K) → v.Completion

namespace InfiniteAdeleRing

instance : CommRing (InfiniteAdeleRing K) := Pi.commRing

instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩

instance [NumberField K] : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace

instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _

@[simp]
theorem algebraMap_apply (x : K) (v : InfinitePlace K) :
    algebraMap K (InfiniteAdeleRing K) x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
abbrev ringEquiv_mixedSpace :
    InfiniteAdeleRing K ≃+* mixedEmbedding.mixedSpace K :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem ringEquiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbeddingOfIsReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl

/-- Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K _ x) := by
  ext v <;> simp only [ringEquiv_mixedSpace_apply, algebraMap_apply,
    ringEquivRealOfIsReal, ringEquivComplexOfIsComplex, extensionEmbedding,
    extensionEmbeddingOfIsReal, extensionEmbedding_of_comp, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.isUniformInducing_of_comp <| v.1.norm_embedding_of_isReal v.2).uniformContinuous x]
    exact mixedEmbedding.mixedEmbedding_apply_ofIsReal _ _ _
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.isUniformInducing_of_comp <| v.1.norm_embedding_eq).uniformContinuous x]
    exact mixedEmbedding.mixedEmbedding_apply_ofIsComplex _ _ _

end InfiniteAdeleRing

variable [NumberField K]

/-! ## The adele ring  -/

/-- The adele ring of a number field. -/
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K

namespace AdeleRing

instance : CommRing (AdeleRing K) := Prod.instCommRing

instance : Inhabited (AdeleRing K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing K) := instTopologicalSpaceProd

instance : TopologicalRing (AdeleRing K) := instTopologicalRingProd

instance : Algebra K (AdeleRing K) := Prod.algebra _ _ _

@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K (AdeleRing K) x).1 v = x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (AdeleRing K) x).2 v = x := rfl

theorem algebraMap_injective : Function.Injective (algebraMap K (AdeleRing K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup (AdeleRing K) := (algebraMap K _).range.toAddSubgroup

end AdeleRing

end NumberField
