/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.Basis.Exact
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Computation of Jacobian of presentations from basis of Cotangent

Let `P` be a presentation of an `R`-algebra `S` with kernel `I = (fᵢ)`.
In this file we provide lemmas to show that `P` is submersive when given suitable bases of
`I/I²` and `Ω[S⁄R]`.

We will later deduce from this a presentation-independent characterisation of standard
smooth algebras (TODO @chrisflav).

## Main results

- `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`:
  If the `fᵢ` form a basis of `I/I²` and the restricted cotangent complex
  `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective, `P` is submersive.
-/

universe t₂ t₁ u v

open KaehlerDifferential MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ κ : Type*}

namespace Algebra

namespace Generators

variable (P : Generators R S ι) {u : σ → ι} (hu : Function.Injective u)
  {v : κ → ι} (hv : Function.Injective v)

/--
If `H¹(L_{S/R}) = 0` and `R[xᵢ] → S` are generators indexed by `σ ⊕ κ` such that the images
of `dxₖ` for `k : κ` span `Ω[S⁄R]` and the span of the `dXₖ` for `k : κ` in
`S ⊗[R] Ω[R[Xᵢ⁄R]]` intersects the kernel of the projection trivially, then the restriction of
`I/I² → ⊕ S dxᵢ` to the direct sum indexed by `i : ι` is an isomorphism.

The assumptions are in particular satisfied if the `dsₖ` form an `S`-basis of `Ω[S⁄R]`,
see `Generators.disjoint_ker_toKaehler_of_linearIndependent` for one half.
Via `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`, this can be useful
to show a presentation is submersive.
-/
lemma cotangentRestrict_bijective_of_isCompl
    (huv : IsCompl (Set.range v) (Set.range u))
    (hm : Submodule.span S (.range fun i ↦ D R S (P.val (v i))) = ⊤)
    (hk : Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S (.range fun x ↦ P.cotangentSpaceBasis (v x))))
    [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  rw [cotangentRestrict, Finsupp.lcomapDomain_eq_linearProjOfIsCompl _ huv.symm]
  set f : _ →ₗ[S] (ι →₀ S) := P.cotangentSpaceBasis.repr ∘ₗ P.toExtension.cotangentComplex
  let g : (ι →₀ S) →ₗ[S] (Ω[S⁄R]) := P.toExtension.toKaehler ∘ₗ P.cotangentSpaceBasis.repr.symm
  have hfg : Function.Exact f g := by
    simp only [f, g, LinearEquiv.conj_exact_iff_exact]
    exact Extension.exact_cotangentComplex_toKaehler
  apply LinearMap.linearProjOfIsCompl_comp_bijective_of_exact hfg
  · exact P.cotangentSpaceBasis.repr.injective.comp <|
      (Extension.subsingleton_h1Cotangent P.toExtension).mp P.equivH1Cotangent.subsingleton
  · dsimp only [g]
    apply Submodule.map_injective_of_injective (f := P.cotangentSpaceBasis.repr.symm.toLinearMap)
      P.cotangentSpaceBasis.repr.symm.injective
    rw [Submodule.map_inf P.cotangentSpaceBasis.repr.symm.toLinearMap
        P.cotangentSpaceBasis.repr.symm.injective, Submodule.map_span, ← Set.range_comp,
        Function.comp_def, LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective]
    · simpa [← disjoint_iff]
    · exact P.cotangentSpaceBasis.repr.symm.surjective
  · simpa [g, Submodule.map_comp, Submodule.map_span, ← Set.range_comp, Function.comp_def]

lemma disjoint_ker_toKaehler_of_linearIndependent
    (h : LinearIndependent S (fun k ↦ D R S (P.val (v k)))) :
    Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S <| .range fun x ↦ P.cotangentSpaceBasis (v x)) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro x ⟨hx, hxs⟩
  rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at hxs
  obtain ⟨c, rfl⟩ := hxs
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_finsuppSum, map_smul,
    toKaehler_cotangentSpaceBasis] at hx
  obtain rfl := (linearIndependent_iff.mp h) c hx
  simp

end Generators

namespace PreSubmersivePresentation

open Generators

variable (P : PreSubmersivePresentation R S ι σ) [Finite σ]

/-- To show a pre-submersive presentation with kernel `I = (fᵢ)` is submersive, it suffices to show
that the images of the `fᵢ` form a basis of `I/I²` and that the restricted
cotangent complex `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective. -/
lemma isUnit_jacobian_of_cotangentRestrict_bijective
    (b : Module.Basis σ S P.toExtension.Cotangent)
    (hb : ∀ r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩)
    (h : Function.Bijective (P.cotangentRestrict P.map_inj)) :
    IsUnit P.jacobian := by
  have heq : (fun j i ↦ (aeval P.val) (pderiv (P.map i) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘ P.cotangentRestrict P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply, cotangentRestrict_mk]
  apply P.isUnit_jacobian_of_linearIndependent_of_span_eq_top
  · rw [heq]
    exact (b.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective h.injective)).map' _
      (Finsupp.linearEquivFunOnFinite S S σ).ker
  · rw [heq, Set.range_comp, Set.range_comp, ← Submodule.map_span, ← Submodule.map_span,
      b.span_eq, Submodule.map_top, LinearMap.range_eq_top_of_surjective _ h.surjective,
      Submodule.map_top, LinearEquivClass.range]

end PreSubmersivePresentation

end Algebra
