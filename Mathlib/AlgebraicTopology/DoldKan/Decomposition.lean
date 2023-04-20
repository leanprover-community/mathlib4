/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.decomposition
! leanprover-community/mathlib commit 9af20344b24ef1801b599d296aaed8b9fffdc360
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.PInfty

/-!

# Decomposition of the Q endomorphisms

In this file, we obtain a lemma `decomposition_Q` which expresses
explicitly the projection `(Q q).f (n+1) : X _[n+1] ⟶ X _[n+1]`
(`X : simplicial_object C` with `C` a preadditive category) as
a sum of terms which are postcompositions with degeneracies.

(TODO @joelriou: when `C` is abelian, define the degenerate
subcomplex of the alternating face map complex of `X` and show
that it is a complement to the normalized Moore complex.)

Then, we introduce an ad hoc structure `morph_components X n Z` which
can be used in order to define morphisms `X _[n+1] ⟶ Z` using the
decomposition provided by `decomposition_Q`. This shall play a critical
role in the proof that the functor
`N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive Opposite

open BigOperators Simplicial

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] {X X' : SimplicialObject C}

/-- In each positive degree, this lemma decomposes the idempotent endomorphism
`Q q` as a sum of morphisms which are postcompositions with suitable degeneracies.
As `Q q` is the complement projection to `P q`, this implies that in the case of
simplicial abelian groups, any $(n+1)$-simplex $x$ can be decomposed as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P q` and
the $y_i$ are in degree $n$. -/
theorem decomposition_q (n q : ℕ) :
    ((q q).f (n + 1) : X _[n + 1] ⟶ X _[n + 1]) =
      ∑ i : Fin (n + 1) in Finset.filter (fun i : Fin (n + 1) => (i : ℕ) < q) Finset.univ,
        (p i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ i.rev :=
  by
  induction' q with q hq
  ·
    simp only [Q_eq_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero, Finset.filter_False,
      Finset.sum_empty]
  · by_cases hqn : q + 1 ≤ n + 1
    swap
    · rw [Q_is_eventually_constant (show n + 1 ≤ q by linarith), hq]
      congr
      ext
      have hx := x.is_lt
      simp only [Nat.succ_eq_add_one]
      constructor <;> intro h <;> linarith
    · cases' Nat.le.dest (nat.succ_le_succ_iff.mp hqn) with a ha
      rw [Q_eq, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f, hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, nat.succ_le_iff.mp hqn⟩
      convert Finset.sum_insert (_ : q' ∉ _)
      · ext i
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and_iff,
          Nat.lt_succ_iff_lt_or_eq, Fin.ext_iff]
        tauto
      · have hnaq' : n = a + q := by linarith
        simpa only [Fin.val_mk, (higher_faces_vanish.of_P q n).comp_hσ_eq hnaq', q'.rev_eq hnaq',
          neg_neg]
      · simp only [Finset.mem_filter, Fin.val_mk, lt_self_iff_false, and_false_iff, not_false_iff]
#align algebraic_topology.dold_kan.decomposition_Q AlgebraicTopology.DoldKan.decomposition_q

variable (X)

/-- The structure `morph_components` is an ad hoc structure that is used in
the proof that `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _[n+1] ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`. -/
@[ext, nolint has_nonempty_instance]
structure MorphComponents (n : ℕ) (Z : C) where
  a : X _[n + 1] ⟶ Z
  b : Fin (n + 1) → (X _[n] ⟶ Z)
#align algebraic_topology.dold_kan.morph_components AlgebraicTopology.DoldKan.MorphComponents

namespace MorphComponents

variable {X} {n : ℕ} {Z Z' : C} (f : MorphComponents X n Z) (g : X' ⟶ X) (h : Z ⟶ Z')

/-- The morphism `X _[n+1] ⟶ Z ` associated to `f : morph_components X n Z`. -/
def φ {Z : C} (f : MorphComponents X n Z) : X _[n + 1] ⟶ Z :=
  pInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (p i).f (n + 1) ≫ X.δ i.rev.succ ≫ f.b i.rev
#align algebraic_topology.dold_kan.morph_components.φ AlgebraicTopology.DoldKan.MorphComponents.φ

variable (X n)

/-- the canonical `morph_components` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
def id : MorphComponents X n (X _[n + 1])
    where
  a := pInfty.f (n + 1)
  b i := X.σ i
#align algebraic_topology.dold_kan.morph_components.id AlgebraicTopology.DoldKan.MorphComponents.id

@[simp]
theorem id_φ : (id X n).φ = 𝟙 _ :=
  by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, P_infty_f, P_f_idem]
  · convert(decomposition_Q n (n + 1)).symm
    ext i
    simpa only [Finset.mem_univ, Finset.mem_filter, true_and_iff, true_iff_iff] using Fin.is_lt i
#align algebraic_topology.dold_kan.morph_components.id_φ AlgebraicTopology.DoldKan.MorphComponents.id_φ

variable {X n}

/-- A `morph_components` can be postcomposed with a morphism. -/
@[simps]
def postComp : MorphComponents X n Z' where
  a := f.a ≫ h
  b i := f.b i ≫ h
#align algebraic_topology.dold_kan.morph_components.post_comp AlgebraicTopology.DoldKan.MorphComponents.postComp

@[simp]
theorem postComp_φ : (f.postComp h).φ = f.φ ≫ h :=
  by
  unfold φ post_comp
  simp only [add_comp, sum_comp, assoc]
#align algebraic_topology.dold_kan.morph_components.post_comp_φ AlgebraicTopology.DoldKan.MorphComponents.postComp_φ

/-- A `morph_components` can be precomposed with a morphism of simplicial objects. -/
@[simps]
def preComp : MorphComponents X' n Z
    where
  a := g.app (op [n + 1]) ≫ f.a
  b i := g.app (op [n]) ≫ f.b i
#align algebraic_topology.dold_kan.morph_components.pre_comp AlgebraicTopology.DoldKan.MorphComponents.preComp

@[simp]
theorem preComp_φ : (f.preComp g).φ = g.app (op [n + 1]) ≫ f.φ :=
  by
  unfold φ pre_comp
  simp only [P_infty_f, comp_add]
  congr 1
  · simp only [P_f_naturality_assoc]
  · simp only [comp_sum, P_f_naturality_assoc, simplicial_object.δ_naturality_assoc]
#align algebraic_topology.dold_kan.morph_components.pre_comp_φ AlgebraicTopology.DoldKan.MorphComponents.preComp_φ

end MorphComponents

end DoldKan

end AlgebraicTopology

