/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

/-!
# Connectedness of subsets of finite-dimensional vector spaces

`Submodule.connectedComponents_compl_equiv_bool_of_isClosed_of_rank_quotient_eq_one` shows that
  the complement of a closed submodule of codimension `1` has exactly two connected components
  (`ConnectedComponents _ ≃ Bool`).

`Submodule.zerothHomotopy_compl_equiv_bool_of_isClosed_of_rank_quotient_eq_one` is the analogous
  statement for path components (`ZerothHomotopy _ ≃ Bool`).

-/

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {E : Submodule ℝ F} (hcodim : Module.rank ℝ (F ⧸ E) = 1)

namespace Submodule

theorem connectedComponents_compl_card_eq_two_of_isClosed_of_rank_quotient_eq_one
    (hE : IsClosed (E : Set F)) (hcodim : Module.rank ℝ (F ⧸ E) = 1) :
    Nat.card (ConnectedComponents ↥((E : Set F)ᶜ)) = 2 :=
  have hfin : Module.finrank ℝ (F ⧸ E) = 1 := (Module.rank_eq_one_iff_finrank_eq_one).1 hcodim
  haveI : FiniteDimensional ℝ (F ⧸ E) := FiniteDimensional.of_finrank_eq_succ hfin
  let hecl : (F ⧸ E) ≃L[ℝ] ℝ :=
    ((Module.nonempty_linearEquiv_of_finrank_eq_one hfin).some.symm).toContinuousLinearEquiv
  let f : F →L[ℝ] ℝ := hecl.toContinuousLinearMap.comp <| ⟨E.mkQ, continuous_quot_mk⟩
  have hfker : LinearMap.ker f.toLinearMap = E := by simp [f, hecl]
  have hset : ((E : Set F)ᶜ) = ({x : F | f x = (0 : ℝ)}ᶜ) := by
    ext x
    simp [← hfker]
  hset ▸ f.connectedComponents_compl_hyperplane_card_eq_two 0
    (hecl.surjective.comp E.mkQ_surjective) |>.trans (by simp)

theorem connectedComponents_compl_card_eq_two_of_rank_quotient_eq_one [T2Space F]
    [FiniteDimensional ℝ F] (hcodim : Module.rank ℝ (F ⧸ E) = 1) :
    Nat.card (ConnectedComponents ↥((E : Set F)ᶜ)) = 2 :=
  connectedComponents_compl_card_eq_two_of_isClosed_of_rank_quotient_eq_one
    E.closed_of_finiteDimensional hcodim

theorem zerothHomotopy_compl_card_eq_two_of_isClosed_of_rank_quotient_eq_one
    (hE : IsClosed (E : Set F)) (hcodim : Module.rank ℝ (F ⧸ E) = 1) :
    Nat.card (ZerothHomotopy ↥((E : Set F)ᶜ)) = 2 :=
  have hfin : Module.finrank ℝ (F ⧸ E) = 1 := (Module.rank_eq_one_iff_finrank_eq_one).1 hcodim
  haveI : FiniteDimensional ℝ (F ⧸ E) := FiniteDimensional.of_finrank_eq_succ hfin
  let hecl : (F ⧸ E) ≃L[ℝ] ℝ :=
    ((Module.nonempty_linearEquiv_of_finrank_eq_one hfin).some.symm).toContinuousLinearEquiv
  let f : F →L[ℝ] ℝ := hecl.toContinuousLinearMap.comp <| ⟨E.mkQ, continuous_quot_mk⟩
  have hfker : LinearMap.ker f.toLinearMap = E := by simp [f, hecl]
  have hset : ((E : Set F)ᶜ) = ({x : F | f x = (0 : ℝ)}ᶜ) := by
    ext x
    simp [← hfker]
  hset ▸ f.zerothHomotopy_compl_hyperplane_card_eq_two 0
    (hecl.surjective.comp E.mkQ_surjective) |>.trans (by simp)

theorem zerothHomotopy_compl_card_eq_two_of_rank_quotient_eq_one [T2Space F]
    [FiniteDimensional ℝ F] (hcodim : Module.rank ℝ (F ⧸ E) = 1) :
    Nat.card (ZerothHomotopy ↥((E : Set F)ᶜ)) = 2 :=
  zerothHomotopy_compl_card_eq_two_of_isClosed_of_rank_quotient_eq_one E.closed_of_finiteDimensional
    hcodim

end Submodule
