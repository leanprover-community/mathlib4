/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.PInfty

/-!

# Decomposition of the Q endomorphisms

In this file, we obtain a lemma `decomposition_Q` which expresses
explicitly the projection `(Q q).f (n+1) : X _[n+1] ⟶ X _[n+1]`
(`X : SimplicialObject C` with `C` a preadditive category) as
a sum of terms which are postcompositions with degeneracies.

(TODO @joelriou: when `C` is abelian, define the degenerate
subcomplex of the alternating face map complex of `X` and show
that it is a complement to the normalized Moore complex.)

Then, we introduce an ad hoc structure `MorphComponents X n Z` which
can be used in order to define morphisms `X _[n+1] ⟶ Z` using the
decomposition provided by `decomposition_Q`. This shall play a critical
role in the proof that the functor
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  Opposite Simplicial

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C] {X X' : SimplicialObject C}

/-- In each positive degree, this lemma decomposes the idempotent endomorphism
`Q q` as a sum of morphisms which are postcompositions with suitable degeneracies.
As `Q q` is the complement projection to `P q`, this implies that in the case of
simplicial abelian groups, any $(n+1)$-simplex $x$ can be decomposed as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P q` and
the $y_i$ are in degree $n$. -/
theorem decomposition_Q (n q : ℕ) :
    ((Q q).f (n + 1) : X _[n + 1] ⟶ X _[n + 1]) =
      ∑ i ∈ Finset.filter (fun i : Fin (n + 1) => (i : ℕ) < q) Finset.univ,
        (P i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ (Fin.rev i) := by
  induction' q with q hq
  · simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_False, Finset.sum_empty]
  · by_cases hqn : q + 1 ≤ n + 1
    swap
    · rw [Q_is_eventually_constant (show n + 1 ≤ q by omega), hq]
      congr 1
      ext ⟨x, hx⟩
      simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · cases' Nat.le.dest (Nat.succ_le_succ_iff.mp hqn) with a ha
      rw [Q_succ, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f, hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.succ_le_iff.mp hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by omega
        simp only [Fin.val_mk, (HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq',
          q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp only [q', Nat.succ_eq_add_one, Nat.lt_succ_iff_lt_or_eq, Finset.mem_univ,
          forall_true_left, Finset.mem_filter, lt_self_iff_false, or_true, and_self, not_true,
          Finset.mem_erase, ne_eq, Fin.mk.injEq, true_and]
        aesop

variable (X)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): removed @[nolint has_nonempty_instance]
/-- The structure `MorphComponents` is an ad hoc structure that is used in
the proof that `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _[n+1] ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`. -/
@[ext]
structure MorphComponents (n : ℕ) (Z : C) where
  a : X _[n + 1] ⟶ Z
  b : Fin (n + 1) → (X _[n] ⟶ Z)

namespace MorphComponents

variable {X} {n : ℕ} {Z Z' : C} (f : MorphComponents X n Z) (g : X' ⟶ X) (h : Z ⟶ Z')

/-- The morphism `X _[n+1] ⟶ Z` associated to `f : MorphComponents X n Z`. -/
def φ {Z : C} (f : MorphComponents X n Z) : X _[n + 1] ⟶ Z :=
  PInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (P i).f (n + 1) ≫ X.δ i.rev.succ ≫
    f.b (Fin.rev i)

variable (X n)

/-- the canonical `MorphComponents` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
def id : MorphComponents X n (X _[n + 1]) where
  a := PInfty.f (n + 1)
  b i := X.σ i

@[simp]
theorem id_φ : (id X n).φ = 𝟙 _ := by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, PInfty_f, P_f_idem]
  · exact Eq.trans (by congr; simp) (decomposition_Q n (n + 1)).symm

variable {X n}

/-- A `MorphComponents` can be postcomposed with a morphism. -/
@[simps]
def postComp : MorphComponents X n Z' where
  a := f.a ≫ h
  b i := f.b i ≫ h

@[simp]
theorem postComp_φ : (f.postComp h).φ = f.φ ≫ h := by
  unfold φ postComp
  simp only [add_comp, sum_comp, assoc]

/-- A `MorphComponents` can be precomposed with a morphism of simplicial objects. -/
@[simps]
def preComp : MorphComponents X' n Z where
  a := g.app (op [n + 1]) ≫ f.a
  b i := g.app (op [n]) ≫ f.b i

@[simp]
theorem preComp_φ : (f.preComp g).φ = g.app (op [n + 1]) ≫ f.φ := by
  unfold φ preComp
  simp only [PInfty_f, comp_add]
  congr 1
  · simp only [P_f_naturality_assoc]
  · simp only [comp_sum, P_f_naturality_assoc, SimplicialObject.δ_naturality_assoc]

end MorphComponents

end DoldKan

end AlgebraicTopology
