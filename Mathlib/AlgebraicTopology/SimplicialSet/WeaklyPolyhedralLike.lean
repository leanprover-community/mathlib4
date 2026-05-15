/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# ...

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

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

lemma IsWeaklyPolyhedralLike.of_iso (e : X ≅ Y) [X.IsWeaklyPolyhedralLike] :
    Y.IsWeaklyPolyhedralLike where
  mono := by
    intro n ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app _)).surjective y
    rw [nonDegenerate_iff_of_mono] at hy
    have := mono' x hy
    rw [← SSet.yonedaEquiv_symm_comp]
    infer_instance

lemma nonDegenerate_δ [X.IsWeaklyPolyhedralLike]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _)
    (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have : Mono (yonedaEquiv.symm x) := IsWeaklyPolyhedralLike.mono ⟨x, hx⟩
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance

lemma IsWeaklyPolyhedralLike.δ_injective [X.IsWeaklyPolyhedralLike]
    {n : ℕ} (x : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  have := mono' x hx
  change (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) =
    (yonedaEquiv.symm x).app _
      (stdSimplex.objEquiv.symm (SimplexCategory.δ j)) at hij
  replace hij := injective_of_mono ((yonedaEquiv.symm x).app _) hij
  simp only [EmbeddingLike.apply_eq_iff_eq] at hij
  exact SimplexCategory.δ_injective hij

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

end SSet
