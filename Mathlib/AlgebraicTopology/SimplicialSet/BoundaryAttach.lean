/-
Copyright (c) 2026 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexAttach

/-!
# Single-cell boundary attachment to a subcomplex

`Skeleton.lean` attaches all nondegenerate `n`-simplices of a simplicial set
in one step, dimension by dimension. This file refines that picture to a
single cell along its boundary: for a nondegenerate `n`-simplex `x : X _⦋n⦌`
with `x ∉ A` and boundary already in `A`, the square
```
∂Δ[n] ──→ A
  │       │
  ↓       ↓
Δ[n]  ──→ A ⊔ ofSimplex x
```
is a pushout in `SSet`
(`Subcomplex.boundaryAttach_isPushout_of_nonDegenerate`).

The map `yonedaEquiv.symm x` need not be monic; injectivity off the
boundary is enough, and that follows from nondegeneracy by an
Eilenberg–Zilber argument
(`Subcomplex.injOn_compl_boundary_yonedaEquiv_symm`). The pushout then
follows from `Subcomplex.attachingMap_isPushout_of_injOn_compl` once the
preimage of `A` along `yonedaEquiv.symm x` is identified with `∂Δ[n]`
(`Subcomplex.preimage_yonedaEquiv_symm_eq_boundary`).

## References

* [E. Riehl and D. Verity, *Elements of ∞-Category Theory*][RiehlVerity2022],
  Section 1.1 (cellular structure of simplicial sets, Remark 1.1.27).
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet
namespace Subcomplex

/-- If the boundary of a nondegenerate `n`-simplex `x` already lies in `A` and
`x` itself does not, the preimage of `A` along the classifier of `x` is exactly
the boundary `∂Δ[n]`. -/
lemma preimage_yonedaEquiv_symm_eq_boundary {X : SSet.{u}} {n : ℕ}
    (A : X.Subcomplex) {x : X _⦋n⦌} (_hx : x ∈ X.nonDegenerate n)
    (hxA : x ∉ A.obj (op ⦋n⦌))
    (hboundary :
      (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).image (yonedaEquiv.symm x) ≤ A) :
    A.preimage (yonedaEquiv.symm x) = (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) := by
  classical
  ext ⟨⟨d⟩⟩ y
  refine ⟨fun hyA ↦ ?_, fun hybdry ↦ hboundary _ ⟨y, hybdry, rfl⟩⟩
  by_contra hybdry
  have hsurj : Function.Surjective (stdSimplex.asOrderHom y) := not_not.mp hybdry
  let f := stdSimplex.objEquiv y
  haveI : Epi f := by
    rw [SimplexCategory.epi_iff_surjective]
    simpa [f, stdSimplex.asOrderHom] using hsurj
  obtain ⟨⟨hsplit⟩⟩ := isSplitEpi_of_epi f
  apply hxA
  have hxA' :
      X.map hsplit.section_.op ((yonedaEquiv.symm x).app (op ⦋d⦌) y) ∈
        A.obj (op ⦋n⦌) :=
    A.map hsplit.section_.op hyA
  convert hxA' using 1
  calc
    x = X.map (𝟙 (op ⦋n⦌)) x := by simp
    _ = X.map (f.op ≫ hsplit.section_.op) x := by
      rw [← op_comp, hsplit.id]; simp
    _ = X.map hsplit.section_.op (X.map f.op x) := by simp [Functor.map_comp]
    _ = X.map hsplit.section_.op ((yonedaEquiv.symm x).app (op ⦋d⦌) y) := by
      rw [stdSimplex.map_objEquiv_op_apply]

/-- The classifier of a nondegenerate simplex is injective off the boundary,
even when it is not monic. This is the Eilenberg–Zilber input to single-cell
boundary attachment. -/
lemma injOn_compl_boundary_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ}
    {x : X _⦋n⦌} (hx : x ∈ X.nonDegenerate n) (d : SimplexCategoryᵒᵖ) :
    Set.InjOn ((yonedaEquiv.symm x).app d)
      ((∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).obj d)ᶜ := by
  classical
  obtain ⟨⟨d⟩⟩ := d
  intro y₁ hy₁ y₂ hy₂ h
  rw [Set.mem_compl_iff] at hy₁ hy₂
  let f₁ := stdSimplex.objEquiv y₁
  let f₂ := stdSimplex.objEquiv y₂
  have hsurj₁ : Function.Surjective (stdSimplex.asOrderHom y₁) := not_not.mp hy₁
  have hsurj₂ : Function.Surjective (stdSimplex.asOrderHom y₂) := not_not.mp hy₂
  haveI : Epi f₁ := by
    rw [SimplexCategory.epi_iff_surjective]
    simpa [f₁, stdSimplex.asOrderHom] using hsurj₁
  haveI : Epi f₂ := by
    rw [SimplexCategory.epi_iff_surjective]
    simpa [f₂, stdSimplex.asOrderHom] using hsurj₂
  have hf : f₁ = f₂ := by
    refine X.unique_nonDegenerate_map ((yonedaEquiv.symm x).app (op ⦋d⦌) y₁)
      f₁ ⟨x, hx⟩ ?_ f₂ ⟨x, hx⟩ ?_
    · simpa [f₁] using (stdSimplex.map_objEquiv_op_apply (X := X) x y₁).symm
    · calc
        (yonedaEquiv.symm x).app (op ⦋d⦌) y₁ =
            (yonedaEquiv.symm x).app (op ⦋d⦌) y₂ := h
        _ = X.map f₂.op x := by
          simpa [f₂] using (stdSimplex.map_objEquiv_op_apply (X := X) x y₂).symm
  exact stdSimplex.objEquiv.injective hf

/-- Single-cell boundary attachment as a pushout. If `x : X _⦋n⦌` is
nondegenerate with `x ∉ A` and its boundary already in `A`, then
`A ⊔ ofSimplex x` is the pushout of `∂Δ[n] ↪ Δ[n]` along the attaching map.
This is the per-cell counterpart to the `skeletonOfMono` filtration in
`Skeleton.lean`. -/
lemma boundaryAttach_isPushout_of_nonDegenerate {X : SSet.{u}} {n : ℕ}
    (A : X.Subcomplex) {x : X _⦋n⦌} (hx : x ∈ X.nonDegenerate n)
    (hxA : x ∉ A.obj (op ⦋n⦌))
    (hboundary :
      (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).image (yonedaEquiv.symm x) ≤ A) :
    IsPushout
      (attachingMap A (yonedaEquiv.symm x)
        (preimage_yonedaEquiv_symm_eq_boundary A hx hxA hboundary))
      (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι
      (homOfLE (show A ≤ A ⊔ ofSimplex x by simp))
      (lift (yonedaEquiv.symm x) (show range (yonedaEquiv.symm x) ≤ A ⊔ ofSimplex x by
        simp [Subcomplex.range_eq_ofSimplex])) := by
  have h := attachingMap_isPushout_of_injOn_compl A (yonedaEquiv.symm x)
    (preimage_yonedaEquiv_symm_eq_boundary A hx hxA hboundary)
    (injOn_compl_boundary_yonedaEquiv_symm hx)
  convert h using 2
  all_goals simp [Subcomplex.range_eq_ofSimplex]

end Subcomplex
end SSet
