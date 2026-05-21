/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Nonsingular simplicial sets

In this file, we introduce a typeclass `SSet.Nonsingular` for a
simplicial set `X : SSet`: it says that for any non-degenerate simplex
`x : X _⦋n⦌`, the corresponding morphism `Δ[n] ⟶ X` is a monomorphism.
This notion is useful in the context of the study of the subdivision
functor (TODO @joelriou).

The condition `SSet.Nonsingular` is a weaker condition compared
to the notion of "polyhedral complex" which appears in the article
*Simplicial approximation* by Jardine, and which says that there
exists a monomorphism `X ⟶ nerve T` where `T` is a partially ordered type.

## References
* [Vegard Fjellbo and John Rognes,
  *Exponentials of non-singular simplicial sets*][fjellbo-rognes-2022]
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
/-- A simplicial set `X` is nonsingular if for any
nondegenerate simplex `x` (of dimension `n`), the corresponding
morphism `Δ[n] ⟶ X` is a monomorphism. -/
@[kerodon 02MG]
class Nonsingular where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] Nonsingular.mono

lemma Nonsingular.mono' [X.Nonsingular]
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    Mono (yonedaEquiv.symm x) := mono ⟨x, hx⟩

@[kerodon 02MK]
lemma Nonsingular.of_mono (f : X ⟶ Y) [Mono f] [Y.Nonsingular] :
    X.Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [← nonDegenerate_iff_of_mono f] at hx
    have := mono' _ hx
    rw [← SSet.yonedaEquiv_symm_comp] at this
    exact mono_of_mono _ f

lemma Nonsingular.of_iso (e : X ≅ Y) [X.Nonsingular] : Y.Nonsingular :=
  .of_mono e.inv

instance (A : X.Subcomplex) [X.Nonsingular] : (A : SSet).Nonsingular :=
  .of_mono A.ι

@[kerodon 02MT]
instance (T : Type*) [PartialOrder T] : (nerve T).Nonsingular where
  mono := by
    intro n ⟨x, hx⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective] at hx
    simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hx (Functor.congr_obj hij l)

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Nonsingular :=
  Nonsingular.of_iso (stdSimplex.isoNerve _).symm

instance (n m : SimplexCategory) :
    (stdSimplex.{u}.obj n ⊗ stdSimplex.obj m).Nonsingular :=
  Nonsingular.of_iso (prodStdSimplex.isoNerve _ _).symm

@[kerodon 02MH]
lemma nonDegenerate_δ [X.Nonsingular]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _) (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have := Nonsingular.mono' x hx
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance

lemma Nonsingular.δ_injective [X.Nonsingular]
    {n : ℕ} (x : X _⦋n + 1⦌) (hx : x ∈ X.nonDegenerate _)
    (i j : Fin (n + 2)) (hij : X.δ i x = X.δ j x) : i = j := by
  apply SimplexCategory.δ_injective
  apply stdSimplex.objEquiv.symm.injective
  have := mono' x hx
  exact injective_of_mono ((yonedaEquiv.symm x).app _) hij

end SSet
