/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.Normalized

#align_import algebraic_topology.dold_kan.homotopy_equivalence from "leanprover-community/mathlib"@"f951e201d416fb50cc7826171d80aa510ec20747"

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Preadditive Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C] (X : SimplicialObject C)

/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 => by
    refine'
      Homotopy.trans (Homotopy.ofEq _)
        (Homotopy.trans
          (Homotopy.add (homotopyPToId q) (Homotopy.compLeft (homotopyHσToZero q) (P q)))
          (Homotopy.ofEq _))
    · simp only [P_succ, comp_add, comp_id]
      -- 🎉 no goals
    · simp only [add_zero, comp_zero]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.homotopy_P_to_id AlgebraicTopology.DoldKan.homotopyPToId

/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
def homotopyQToZero (q : ℕ) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.homotopy_Q_to_zero AlgebraicTopology.DoldKan.homotopyQToZero

theorem homotopyPToId_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).hom n (n + 1) : X _[n] ⟶ X _[n + 1]) =
      (homotopyPToId X q).hom n (n + 1) := by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Nat.add_eq, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp_zero, zero_add, homotopyPToId]
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.homotopy_P_to_id_eventually_constant AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant

/-- Construction of the homotopy from `PInfty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
def homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where
  hom i j := (homotopyPToId X (j + 1)).hom i j
  zero i j hij := Homotopy.zero _ i j hij
  comm n := by
    rcases n with _|n
    -- ⊢ HomologicalComplex.Hom.f PInfty Nat.zero = ((↑(dNext Nat.zero) fun i j => Ho …
    · simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        PInfty_f, Nat.zero_eq, P_f_0_eq, zero_add] using (homotopyPToId X 2).comm 0
    · -- Porting note: this branch had been:
      -- simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
      --   HomologicalComplex.id_f, PInfty_f, ← P_is_eventually_constant (rfl.le : n + 1 ≤ n + 1),
      --   homotopyPToId_eventually_constant X (lt_add_one (n + 1))] using
      --   (homotopyPToId X (n + 2)).comm (n + 1)
      -- which fails on leanprover/lean4:nightly-2023-05-16 due to
      -- https://github.com/leanprover/lean4/pull/2146
      -- The `erw` below clunkily works around this.
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, PInfty_f,
        ← P_is_eventually_constant (rfl.le : n + 1 ≤ n + 1)]
      erw [homotopyPToId_eventually_constant X (lt_add_one (Nat.succ n))]
      -- ⊢ HomologicalComplex.Hom.f (P (n + 1 + 1)) (n + 1) = HomologicalComplex.d K[X] …
      have := (homotopyPToId X (n + 2)).comm (n + 1)
      -- ⊢ HomologicalComplex.Hom.f (P (n + 1 + 1)) (n + 1) = HomologicalComplex.d K[X] …
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at this
      -- ⊢ HomologicalComplex.Hom.f (P (n + 1 + 1)) (n + 1) = HomologicalComplex.d K[X] …
      exact this
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.homotopy_P_infty_to_id AlgebraicTopology.DoldKan.homotopyPInftyToId

/-- The inclusion of the Moore complex in the alternating face map complex
is a homotopy equivalence -/
@[simps]
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type*} [Category A]
    [Abelian A] {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y) where
  hom := inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId := Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToId Y)
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

end DoldKan

end AlgebraicTopology
