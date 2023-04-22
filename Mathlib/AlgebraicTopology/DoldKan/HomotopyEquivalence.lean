/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.homotopy_equivalence
! leanprover-community/mathlib commit f951e201d416fb50cc7826171d80aa510ec20747
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.Normalized

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] (X : SimplicialObject C)

/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 =>
    by
    refine'
      Homotopy.trans (Homotopy.ofEq _)
        (Homotopy.trans
          (Homotopy.add (homotopy_P_to_id q) (Homotopy.compLeft (homotopy_Hσ_to_zero q) (P q)))
          (Homotopy.ofEq _))
    · unfold P
      simp only [comp_add, comp_id]
    · simp only [add_zero, comp_zero]
#align algebraic_topology.dold_kan.homotopy_P_to_id AlgebraicTopology.DoldKan.homotopyPToId

/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
def homotopyQToZero (q : ℕ) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm
#align algebraic_topology.dold_kan.homotopy_Q_to_zero AlgebraicTopology.DoldKan.homotopyQToZero

theorem homotopyPToId_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).Hom n (n + 1) : X _[n] ⟶ X _[n + 1]) =
      (homotopyPToId X q).Hom n (n + 1) :=
  by
  unfold homotopy_P_to_id
  simp only [homotopy_Hσ_to_zero, hσ'_eq_zero hqn (c_mk (n + 1) n rfl), Homotopy.trans_hom,
    Pi.add_apply, Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, eq_self_iff_true, dite_eq_ite, if_true,
    comp_zero, add_zero, zero_add]
#align algebraic_topology.dold_kan.homotopy_P_to_id_eventually_constant AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant

variable (X)

/-- Construction of the homotopy from `P_infty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
def homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _)
    where
  Hom i j := (homotopyPToId X (j + 1)).Hom i j
  zero' i j hij := Homotopy.zero _ i j hij
  comm n := by
    cases n
    ·
      simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, P_f_0_eq, zero_add,
        HomologicalComplex.id_f, P_infty_f] using (homotopy_P_to_id X 2).comm 0
    ·
      simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.id_f, P_infty_f, ← P_is_eventually_constant (rfl.le : n + 1 ≤ n + 1),
        homotopy_P_to_id_eventually_constant X (lt_add_one (n + 1))] using
        (homotopy_P_to_id X (n + 2)).comm (n + 1)
#align algebraic_topology.dold_kan.homotopy_P_infty_to_id AlgebraicTopology.DoldKan.homotopyPInftyToId

/-- The inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type _} [Category A]
    [Abelian A] {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y)
    where
  Hom := inclusionOfMooreComplexMap Y
  inv := pInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId :=
    Homotopy.trans
      (Homotopy.ofEq (pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToId Y)
#align algebraic_topology.dold_kan.homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

end DoldKan

end AlgebraicTopology

