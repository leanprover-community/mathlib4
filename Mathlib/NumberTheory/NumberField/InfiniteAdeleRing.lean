/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Ring.Equiv
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.NumberTheory.NumberField.Embeddings


/-!
# Infinite adele ring of a number field

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places. The definition of the completions are
formalised in [Mathlib.NumberTheory.NumberField.Completion](Completion.lean).

We show that the infinite adele ring is locally compact and that it is isomorphic to the
space `ℝ ^ r₁ × ℂ ^ r₂` used in
[Mathlib.NumberTheory.NumberField.mixedEmbedding](canonicalEmbedding/Basic.lean).

## Main definitions
 - `NumberField.infiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.
 - `NumberField.InfiniteAdeleRing.globalEmbedding` is the map sending `x ∈ K` to `(x)ᵥ`.
 - `NumberField.InfiniteAdeleRing.equiv_mixedSpace` is the ring isomorphism between
  the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature
  of `K`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space.
 - `NumberField.InfiniteAdeleRing.mixedEmbedding_eq_globalEmbedding_comp` : applying the
  ring isomorphism of `equiv_mixedSpace` to a globally embedded `(x)ᵥ` in the infinite adele
  ring, where `x ∈ K`, is the same as applying the embedding `K → ℝ ^ r₁ × ℂ ^ r₂` given by
  `NumberField.mixedEmbedding` to `x`.

## Tags
infinite adele ring, number field
-/

open scoped Classical

noncomputable section

namespace NumberField

open InfinitePlace InfinitePlace.Completion AbsoluteValue.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def infiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := Pi.topologicalSpace

instance topologicalRing : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (infiniteAdeleRing K) := Pi.algebra _ _

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
abbrev globalEmbedding : K →+* infiniteAdeleRing K := algebraMap K (infiniteAdeleRing K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding K x v = (x : v.completion) := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
abbrev equiv_mixedSpace :
    infiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodMap
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.equivReal_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.equivComplex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem equiv_mixedSpace_apply (x : infiniteAdeleRing K) :
    equiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => equivReal_of_isReal v.2 (x v),
        fun (v : {w : InfinitePlace K // IsComplex w}) => equivComplex_of_isComplex v.2 (x v)) := by
  simp only [equiv_mixedSpace, RingEquiv.piEquivPiSubtypeProd, RingEquiv.prodMap,
    RingEquiv.piCongrLeft, RingEquiv.coe_trans, Equiv.prodCongr_apply, EquivLike.coe_coe,
    Function.comp_apply, Prod.map_apply, RingEquiv.piCongrRight, Equiv.piEquivPiSubtypeProd,
    RingEquiv.piCongrLeft', Equiv.piCongrLeft', RingEquiv.symm_mk, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, Equiv.subtypeEquivRight_symm_apply_coe]

/-- Transports the global embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_globalEmbedding_comp {x : K} :
    mixedEmbedding K x = equiv_mixedSpace K (globalEmbedding K x) := by
  ext ⟨v, hv⟩ <;> simp only [equiv_mixedSpace_apply, globalEmbedding_apply,
    equivReal_of_isReal, equivComplex_of_isComplex, extensionEmbedding,
    extensionEmbedding_of_isReal, extensionEmbedding_of_comp, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_of_isReal_eq_comp hv).uniformContinuous x]
    rfl
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_eq_comp v).uniformContinuous x]
    rfl

end InfiniteAdeleRing

end NumberField
