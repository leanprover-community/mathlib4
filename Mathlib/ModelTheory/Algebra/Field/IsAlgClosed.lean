/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Satisfiability

/-!

# The First Order Theory of Algebraically Closed Fields

This file defines the theory of algebraically closed fields of characteristic `p`, as well
as proving completeness of the theory and the Lefschetz Principle.

## Main definitions

* `FirstOrder.Language.Theory.ACF p` : the theory of algebraically closed fields of characteristic
  `p` as a theory over the language of rings.
* `FirstOrder.Field.ACF_isComplete` : the theory of algebraically closed fields of characteristic
  `p` is complete whenever `p` is prime or zero.
* `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize` : the Lefschetz principle.

## Implementation details

To apply a theorem about the model theory of algebraically closed fields to a specific
algebraically closed field `K` which does not have a `Language.ring.Structure` instance,
you must introduce the local instance `compatibleRingOfRing K`. Theorems whose statement requires
both a `Language.ring.Structure` instance and a `Field` instance will all be stated with the
assumption `Field K`, `CharP K p`, `IsAlgClosed K` and `CompatibleRing K` and there are instances
defined saying that these assumptions imply `Theory.field.Model K` and `(Theory.ACF p).Model K`

## References

The first order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/

variable {K : Type*}

namespace FirstOrder

namespace Field

open Ring FreeCommRing Polynomial Language

/-- A generic monic polynomial of degree `n` as an element of the
free commutative ring in `n + 1` variables, with a variable for each
of the `n` non-leading coefficients of the polynomial and one variable (`Fin.last n`)
for `X`. -/
def genericMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
  of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : ℕ)

theorem lift_genericMonicPoly [CommRing K] [Nontrivial K] {n : ℕ} (v : Fin (n + 1) → K) :
    FreeCommRing.lift v (genericMonicPoly n) =
    (((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv).symm (v ∘ Fin.castSucc)).1.eval
      (v (Fin.last _)) := by
  simp [genericMonicPoly, monicEquivDegreeLT, degreeLTEquiv, eval_finset_sum]

/-- A sentence saying every monic polynomial of degree `n` has a root. -/
noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.ring.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genericMonicPolyHasRoot [Field K] [CompatibleRing K] (n : ℕ) :
    K ⊨ genericMonicPolyHasRoot n ↔
      ∀ p : { p : K[X] // p.Monic ∧ p.natDegree = n }, ∃ x, p.1.eval x = 0 := by
  let _ := Classical.decEq K
  rw [Equiv.forall_congr_left ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

/-- The theory of algebraically closed fields of characteristic `p` as a theory over
the language of rings -/
def _root_.FirstOrder.Language.Theory.ACF (p : ℕ) : Theory .ring :=
  Theory.fieldOfChar p ∪ genericMonicPolyHasRoot '' {n | 0 < n}

instance [Language.ring.Structure K] (p : ℕ) [h : (Theory.ACF p).Model K] :
    (Theory.fieldOfChar p).Model K :=
  Theory.Model.mono h Set.subset_union_left

instance [Field K] [CompatibleRing K] {p : ℕ} [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

theorem modelField_of_modelACF (p : ℕ) (K : Type*) [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Theory.field.Model K :=
  Theory.Model.mono h (Set.subset_union_of_subset_left Set.subset_union_left _)

/-- A model for the Theory of algebraically closed fields is a Field. After introducing
this as a local instance on a particular Type, you should usually also introduce
`modelField_of_modelACF p M`, `compatibleRingOfModelField` and `isAlgClosed_of_model_ACF` -/
@[reducible]
noncomputable def fieldOfModelACF (p : ℕ) (K : Type*)
    [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Field K := by
  have := modelField_of_modelACF p K
  exact fieldOfModelField K

theorem isAlgClosed_of_model_ACF (p : ℕ) (K : Type*)
    [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

theorem ACF_isSatisfiable {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsSatisfiable := by
  cases hp with
  | inl hp =>
    have : Fact p.Prime := ⟨hp⟩
    let _ := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    have : CharP (AlgebraicClosure (ZMod p)) p :=
      charP_of_injective_algebraMap
        (RingHom.injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) p
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    let _ := compatibleRingOfRing (AlgebraicClosure ℚ)
    have : CharP (AlgebraicClosure ℚ) 0 :=
      charP_of_injective_algebraMap
        (RingHom.injective (algebraMap ℚ (AlgebraicClosure ℚ))) 0
    exact ⟨⟨AlgebraicClosure ℚ⟩⟩

open Cardinal

/-- The Theory `Theory.ACF p` is `κ`-categorical whenever `κ` is an uncountable cardinal. -/
theorem ACF_categorical {p : ℕ} (κ : Cardinal) (hκ : ℵ₀ < κ) :
    Categorical κ (Theory.ACF p) := by
  rintro ⟨M⟩ ⟨N⟩ hM hN
  let _ := fieldOfModelACF p M
  have := modelField_of_modelACF p M
  let _ := compatibleRingOfModelField M
  have := isAlgClosed_of_model_ACF p M
  have := charP_of_model_fieldOfChar p M
  let _ := fieldOfModelACF p N
  have := modelField_of_modelACF p N
  let _ := compatibleRingOfModelField N
  have := isAlgClosed_of_model_ACF p N
  have := charP_of_model_fieldOfChar p N
  constructor
  refine languageEquivEquivRingEquiv.symm ?_
  apply Classical.choice
  refine IsAlgClosed.ringEquiv_of_equiv_of_char_eq p ?_ ?_
  · rw [hM]; exact hκ
  · rw [← Cardinal.eq, hM, hN]

theorem ACF_isComplete {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsComplete := by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _
    (ACF_categorical _ (Order.lt_succ _))
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    let _ := fieldOfModelACF p M
    have := modelField_of_modelACF p M
    let _ := compatibleRingOfModelField M
    have := isAlgClosed_of_model_ACF p M
    infer_instance

theorem finite_ACF_prime_not_realize_of_ACF_zero_realize
    (φ : Language.ring.Sentence) (h : Theory.ACF 0 ⊨ᵇ φ) :
    Set.Finite { p : Nat.Primes | ¬ Theory.ACF p ⊨ᵇ φ } := by
  rw [Theory.models_iff_finset_models] at h
  rcases h with ⟨T0, hT0, h⟩
  have f : ∀ ψ ∈ Theory.ACF 0,
      { s : Finset Nat.Primes // ∀ q : Nat.Primes, q ∉ s → Theory.ACF q ⊨ᵇ ψ } := by
    intro ψ hψ
    rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm, Set.mem_union, if_pos rfl,
      Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q _
      exact Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h)
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      rintro ⟨q, _⟩ hq ⟨K⟩ _ _
      have hqp : q ≠ p := by simpa [← Nat.Primes.coe_nat_inj] using hq
      let _ := fieldOfModelACF q K
      have := modelField_of_modelACF q K
      let _ := compatibleRingOfModelField K
      have := charP_of_model_fieldOfChar q K
      simp only [eqZero, Term.equal, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing, map_natCast,
        realize_zero, ← CharP.charP_iff_prime_eq_zero hp]
      intro _
      exact hqp <| CharP.eq K this inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : ∀ (p : Nat.Primes) ψ, ψ ∈ T0 → p ∉ s → Theory.ACF p ⊨ᵇ ψ := by
    intro p ψ hψ hpψ
    simp only [s, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, not_exists] at hpψ
    exact (f ψ (hT0 hψ)).2 p (hpψ _ hψ)
  refine Set.Finite.subset (Finset.finite_toSet s) (Set.compl_subset_comm.2 ?_)
  intro p hp
  exact Theory.models_of_models_theory (fun ψ hψ => hs p ψ hψ hp) h

/-- The **Lefschetz principle**. A first order sentence is modeled by the theory
of algebraically closed fields of characteristic zero if and only if it is modeled by
the theory of algebraically closed fields of characteristic `p` for infinitely many `p`. -/
theorem ACF_zero_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ } := by
  refine ⟨fun h => Set.infinite_of_finite_compl
      (finite_ACF_prime_not_realize_of_ACF_zero_realize φ h),
    not_imp_not.1 ?_⟩
  simpa [(ACF_isComplete (Or.inr rfl)).models_not_iff,
      fun p : Nat.Primes => (ACF_isComplete (Or.inl p.2)).models_not_iff] using
    finite_ACF_prime_not_realize_of_ACF_zero_realize φ.not

/-- Another statement of the **Lefschetz principle**. A first order sentence is modeled by the
theory of algebraically closed fields of characteristic zero if and only if it is modeled by the
theory of algebraically closed fields of characteristic `p` for all but finitely many primes `p`.
-/
theorem ACF_zero_realize_iff_finite_ACF_prime_not_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Finite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ }ᶜ :=
  ⟨fun h => finite_ACF_prime_not_realize_of_ACF_zero_realize φ h,
    fun h => ACF_zero_realize_iff_infinite_ACF_prime_realize.2
      (Set.infinite_of_finite_compl h)⟩


end Field

end FirstOrder
