/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Maps

/-!

# Gröbner Bases of ideals in the ring of polynomials over a field

-/
namespace MvPolynomial

variable {σ R α : Type*} [CommRing R]

class GeneralizedEuclideanNorm (R : Type*) (α : outParam (Type*))
    [CommRing R] [LinearOrder α] [OrderBot α]  where
  ( norm : R → α )
  ( norm_eq_bot_iff : ∀ {a : R}, norm a = ⊥ ↔ a = 0 )
  --( le_iff_mul_le_mul {a b c} : c ≠ 0 → norm a ≤ norm b ↔ norm (a *c) ≤ norm (b * c) )
  ( reduce : R → R → Option R )
  ( norm_reduce_lt : ∀ {a b r}, r ∈ reduce a b → norm r < norm a )
  ( reduce_eq_none_iff : ∀ {a b}, reduce a b = none ↔ a = 0 ∨ b = 0 ∨ norm a < norm b )
  ( dvd_sub_reduce : ∀ {a b r}, r ∈ reduce a b → b ∣ a - r )
  ( le_of_dvd : ∀ x y : R, y ≠ 0 → x ∣ y → norm x ≤ norm y )

namespace GeneralizedEuclideanNorm

attribute [simp] norm_eq_bot_iff reduce_eq_none_iff

variable [LinearOrder α] [OrderBot α] [GeneralizedEuclideanNorm R α]



-- @[simp]
-- theorem mul_le_mul_right_iff {m n p : R} (hp0 : p ≠ 0) :
--     norm (m * p) ≤ norm (n * p) ↔ norm m ≤ norm n :=
--   (norm.le_iff_mul_le_mul' hp0).symm

-- @[simp]
-- theorem mul_le_mul_left_iff {m n p : σ →₀ ℕ} :
--     norm (p * m) ≤ norm (p * n) ↔ norm m ≤ norm n := by
--   rw [add_comm, add_comm p n, add_le_add_right_iff]

@[simp]
theorem norm_zero : norm (0 : R) = ⊥ := by
  rw [norm_eq_bot_iff]


def IsReduced (G : Set R) (a : R) : Prop :=
  ∀ g ∈ G, g ≠ 0 → ¬ (norm g : α) ≤ norm a

theorem reduce_isSome_iff {a b : R} : (reduce a b).isSome ↔ a ≠ 0 ∧ b ≠ 0 ∧ norm b ≤ norm a := by
  rw [Option.isSome_iff_ne_none, Ne, reduce_eq_none_iff, not_or, not_or, not_lt]

structure IsGroebnerBasis (G : Set R) : Prop where
  ( exists_le_of_mem : ∀ (a : R), a ∈ Ideal.span G → a ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧
    (norm g : α) ≤ norm a )

variable {G : Set R}

theorem isGroebnerBasis_iff_exists_le_of_mem : IsGroebnerBasis G ↔
    ∀ a ∈ Ideal.span G, a ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ (norm g : α) ≤ norm a :=
  ⟨fun h => h.exists_le_of_mem, IsGroebnerBasis.mk⟩

theorem isGroebnerBasis_iff_isReduced_eq_zero  :
    IsGroebnerBasis G ↔ ∀ a ∈ Ideal.span G, IsReduced G a → a = 0 := by
  simp only [isGroebnerBasis_iff_exists_le_of_mem, IsReduced]
  refine forall_congr' fun a => forall_congr' fun ha => ?_
  rw [not_imp_comm, not_exists]
  simp only [ne_eq, not_and, not_le]

variable (G)

/-- This means that `p` lead reduces to `q` in a single step.  -/
def SingleStepReduction (a b : R) : Prop :=
  ∃ g ∈ G, b ∈ reduce a g

structure Reduction (a b : R) : Type _ where
  ( toList : List R )
  ( chain : toList.Chain (SingleStepReduction G) a )
  ( last_eq : (a::toList).getLast (List.cons_ne_nil _ _) = b )

variable {norm} {G}

@[refl]
def Reduction.refl (a : R) : Reduction G a a :=
  ⟨[], List.Chain.nil, rfl⟩

def Reduction.trans {a b c : R} (l : Reduction G a b)
    (l' : Reduction G b c) : Reduction G a c := by
  rcases l' with ⟨l', hl', rfl⟩
  rcases l with ⟨l, hl, rfl⟩
  refine ⟨l ++ l', ?_, ?_⟩
  · induction l generalizing a with
    | nil => simpa
    | cons a l ih =>
      simp only [List.cons_append]
      rw [List.chain_cons] at hl
      exact List.Chain.cons hl.1 (ih hl.2 hl')
  · cases l' <;> simp

theorem Reduction.sub_mem_span {a b :R} (l : Reduction G a b) :
    a - b ∈ Ideal.span G := by
  rcases l with ⟨l, hl, rfl⟩
  induction l generalizing a with
  | nil => simp
  | cons q l ih =>
    rw [List.chain_cons] at hl
    rw [← Ideal.add_mem_iff_left _ ((Ideal.neg_mem_iff _).2 (ih hl.2))]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons]
    rcases hl.1 with ⟨g, hgG, hgr⟩
    ring_nf
    exact Ideal.mem_of_dvd _ (dvd_sub_reduce hgr) (Ideal.subset_span hgG)

@[simp]
theorem Reduction.mem_span_iff {a b : R} {l : Reduction G a b} :
    a ∈ Ideal.span G ↔ b ∈ Ideal.span G := by
  rw [← Ideal.add_mem_iff_left _ ((Ideal.neg_mem_iff _).2 (sub_mem_span l)), ← l.last_eq]
  simp

section

attribute [local instance] WellFoundedLT.toWellFoundedRelation

theorem exists_leadReduction [WellFoundedLT α] : ∀ a : R,
    ∃ (b : R) (_l : Reduction G a b), IsReduced G b := by
  intro a
  by_cases ha : IsReduced G a
  · exact ⟨a, Reduction.refl a, ha⟩
  · simp only [IsReduced, ne_eq, not_forall, Classical.not_imp, Decidable.not_not] at ha
    rcases ha with ⟨g, hg, hg0, hgp⟩
    let r := (reduce a g).get (reduce_isSome_iff.2
      ⟨mt norm_eq_bot_iff.2 (fun _ => by simp_all), hg0, hgp⟩)
    have wf : norm r < norm a := norm_reduce_lt (Option.get_mem _)
    rcases exists_leadReduction r with ⟨q, l, hq⟩
    refine ⟨q, ?_, hq⟩
    refine ⟨r::l.toList, ?_, ?_⟩
    · rw [List.chain_cons]
      refine ⟨?_, l.2⟩
      refine ⟨g, hg, Option.get_mem _⟩
    · simp [l.3]
  termination_by a => norm a

end


theorem exists_leadingMonomial_mem_eqvGen_leadReduction

-- theorem Reduction.chain_norm_lt {p q : MvPolynomial σ R} (l : Reduction norm G p) :
--     l.toList.Chain (fun q r => r ≠ 0 → norm (norm.leadingMonomial r) <
--       norm (norm.leadingMonomial q)) p := by
--   have := l.chain
--   rw [← List.map_id l.toList] at this
--   refine List.chain_of_chain_map id ?_ this
--   rintro q r ⟨g, hg, r, hr, hgm, rfl⟩ h
--   refine norm_leadingMon_sub_lt ?_ ?_ ?_
-- theorem IsGrobnerSet.exists_complete_leadReduction_of_finite_vars
--     (hvars : Set.Finite (⋃ g ∈ G, (g.vars : Set σ))) {p : MvPolynomial σ R} :
--     ∃ l : Reduction norm G p, l.IsComplete := by
--   rw [isGroebnerSet_iff_leadingMonomial_le] at hG
--   rcases hG p hp with ⟨g, hg, hpg⟩

theorem eqvGen_leadReduction {p q : MvPolynomial σ R} :

end GeneralizedEuclideanNorm



end MvPolynomial
