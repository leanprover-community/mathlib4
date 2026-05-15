/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Weakly polyhedral like simplicial sets

In this file, we introduce a typeclass `SSet.IsWeaklyPolyhedralLike` for a
simplicial set `X : SSet`: it says that for any non-degenerate simplex
`x : X _⦋n⦌`, the corresponding morphism `Δ[n] ⟶ X` is a monomorphism.
This notion is useful in the context of the study of the subdivision
functor (TODO @joelriou).

The condition `IsWeaklyPolyhedralLike` is a weaker condition compared
to the notion of "polyhedral complex" which appears in the article
*Simplicial approximation* by Jardine, and which says that there
exists a monomorphism `X ⟶ nerve T` where `T` is a partially ordered type.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
class IsWeaklyPolyhedralLike where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] IsWeaklyPolyhedralLike.mono

lemma IsWeaklyPolyhedralLike.mono' [X.IsWeaklyPolyhedralLike]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) := mono ⟨x, hx⟩

lemma IsWeaklyPolyhedralLike.of_mono (f : X ⟶ Y) [Mono f] [Y.IsWeaklyPolyhedralLike] :
    X.IsWeaklyPolyhedralLike where
  mono := by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

lemma IsWeaklyPolyhedralLike.of_iso (e : X ≅ Y) [X.IsWeaklyPolyhedralLike] :
    Y.IsWeaklyPolyhedralLike :=
  .of_mono e.inv

instance (A : X.Subcomplex) [X.IsWeaklyPolyhedralLike] :
    (A : SSet).IsWeaklyPolyhedralLike :=
  .of_mono A.ι

instance (T : Type*) [PartialOrder T] : (nerve T).IsWeaklyPolyhedralLike where
  mono := by
    intro n ⟨x, hx⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective] at hx
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hx (congr_fun (congr_arg Functor.obj hij) l)

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).IsWeaklyPolyhedralLike :=
  IsWeaklyPolyhedralLike.of_iso (stdSimplex.isoNerve _).symm

instance (n m : SimplexCategory) :
    (stdSimplex.{u}.obj n ⊗ stdSimplex.obj m).IsWeaklyPolyhedralLike :=
  IsWeaklyPolyhedralLike.of_iso (prodStdSimplex.isoNerve _ _).symm

lemma nonDegenerate_δ [X.IsWeaklyPolyhedralLike]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _)
    (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have := IsWeaklyPolyhedralLike.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance

lemma IsWeaklyPolyhedralLike.δ_injective [X.IsWeaklyPolyhedralLike]
    {n : ℕ} (x : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  have := mono' x hx
  change
    (yonedaEquiv.symm x).app _
      (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) =
    (yonedaEquiv.symm x).app _
      (stdSimplex.objEquiv.symm (SimplexCategory.δ j)) at hij
  replace hij := injective_of_mono ((yonedaEquiv.symm x).app _) hij
  simp only [EmbeddingLike.apply_eq_iff_eq] at hij
  exact SimplexCategory.δ_injective hij

end SSet
