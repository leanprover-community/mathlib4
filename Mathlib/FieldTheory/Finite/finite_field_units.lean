import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-
This file formalizes a classic result in field theory: the multiplicative group of units
in a finite field is cyclic. The proof follows these main steps:
1. Establish a bijection between the units group Fˣ and the set of unit values in F
2. Define a polynomial X^n - 1 where n is the exponent of Fˣ
3. Show that every unit value is a root of this polynomial
4. Use the fact that a polynomial of degree n has at most n roots
(the set of distinct roots has cardinality at most n)
5. Combine this with group theory results about exponents to prove that:
   exponent(Fˣ) = card(Fˣ), which implies Fˣ is cyclic

In particular, step 1 defines a new way to wrap units of a field as a subset
and previously step 4 was only established for roots as a multiset (count with multiplicities).
They fill gaps in the existing Mathlib library.

This result has important applications in number theory, cryptography, coding theory,
and algebraic geometry, as it guarantees the existence of primitive elements (generators)
in finite fields.
-/

variable {F : Type*} [Field F]

-- Define a mapping from a unit to its corresponding value in the field wrapped as a subtype
def unitsToSet (u : Fˣ) : {x : F | ∃ u : Fˣ, u.val = x} := ⟨u.val, u, rfl⟩

-- Prove that the mapping from units to their values is bijective
lemma units_bijective : Function.Bijective
  (fun u : Fˣ => ⟨u.val, u, rfl⟩ : Fˣ → {x : F | ∃ u : Fˣ, u.val = x}) := by {
  constructor
  · -- Injectivity: If two units map to the same value, they are equal
    intros u v h
    dsimp at h
    injection h with h_val
    apply Units.ext h_val
  · -- Surjectivity: Every element in the target set has a preimage
    intro x
    obtain ⟨u, hu⟩ := x.2
    exact ⟨u, Subtype.ext hu⟩
}

/-- The cardinality of Units F equals the cardinality of the corresponding set -/
theorem units_F_set_card_eq : Nat.card Fˣ = Nat.card {x : F | ∃ u : Fˣ, u.val = x}:= by {
  -- Two sets have the same cardinality if there is a bijection between them
  apply  Nat.card_eq_of_bijective  (fun u => ⟨u.val, u, rfl⟩)
  exact units_bijective
}

-- Prove that X^n - 1 is a non-zero polynomial when n > 0
lemma X_power_sub_C_non_zero {n : ℕ} (hn : n > 0) :
(Polynomial.X^n - 1 : Polynomial F) ≠ 0 := by {
  let p : Polynomial F := Polynomial.X^n - 1

  -- Show that p is monic (leading coefficient is 1)
  have h_p_monic: p.Monic := by {
    unfold p
    simp [Polynomial.monic_X_pow_sub, Polynomial.degree_one_le, hn]
  }

  -- A monic polynomial cannot be zero
  exact Polynomial.Monic.ne_zero h_p_monic
}

-- The number of roots of a polynomial is at most its degree
theorem roots_card_le_natDegree [DecidableEq F]{p : Polynomial F} :
Nat.card (p.rootSet F) ≤ p.natDegree := by {
  let roots : Set F := p.rootSet F

  -- The root set as a finset equals the roots multiset as a finset
  have h_roots_eq : roots.toFinset = p.roots.toFinset := by {
    ext x
    simp [Set.mem_toFinset, Multiset.mem_toFinset]
    rw [Polynomial.mem_rootSet]
    rfl
  }

  -- The cardinality of the root set equals the cardinality of the roots multiset as a finset
  have h_roots_card_eq : Nat.card roots = p.roots.toFinset.card := by {
    -- Nat.card roots = roots.toFinset.card
    rw [Nat.card_eq_card_toFinset roots]
    -- roots.toFinset.card = p.roots.toFinset.card
    rw [congrArg Finset.card h_roots_eq]
  }

  -- The cardinality of the root set is at most the degree of the polynomial
  have h_roots_card_le_natDegree : Nat.card roots ≤ p.natDegree := by {
    -- Nat.card roots = p.roots.toFinset.card
    rw [h_roots_card_eq]
    -- p.roots.toFinset.card ≤ p.roots.card ≤ p.degree
    trans p.roots.card
    -- p.roots.toFinset.card ≤ p.roots.card
    · exact Multiset.toFinset_card_le p.roots
    -- p.roots.card ≤ p.degree
    · exact Polynomial.card_roots' p
  }
  exact h_roots_card_le_natDegree
}

-- The exponent of a finite group divides the order of the group
theorem exp_dvd_card {F : Type*} [Field F] [Fintype F]:
Monoid.exponent Fˣ ∣ Nat.card Fˣ := by exact Group.exponent_dvd_nat_card

-- A group is cyclic if and only if its exponent equals its order
theorem iscyclic_exp_eq_card {F : Type*} [Field F] [Fintype F]
(h : Monoid.exponent Fˣ = Nat.card Fˣ) : IsCyclic Fˣ := by exact IsCyclic.of_exponent_eq_card h


-- Main theorem: The multiplicative group of a finite field is cyclic
theorem finite_field_units_cyclic (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
IsCyclic Fˣ := by {
  -- First, we establish that Fˣ is finite with positive cardinality
  have h_finite : Fintype Fˣ := by exact Fintype.ofFinite Fˣ
  have h_nat_card_pos : Nat.card Fˣ > 0 := by exact Nat.card_pos

  -- The exponent of Fˣ exists because it is finite
  have h_exp : Monoid.ExponentExists Fˣ := by
    exact Monoid.ExponentExists.of_finite

  -- Let n be the exponent of Fˣ (smallest positive integer such that u^n = 1 for all units u)
  let n := Monoid.exponent Fˣ

  -- The exponent is positive
  have h_n_positive: n > 0 :=by exact Monoid.ExponentExists.exponent_pos h_exp

  -- Every unit raised to the power n equals 1
  have h_roots : ∀ u : Units F, u^n = 1 := by
    exact fun u => Monoid.pow_exponent_eq_one u

  -- Define the polynomial p = X^n - 1
  let p : Polynomial F := Polynomial.X^n - 1

  -- The degree of p is n
  have h_p_deg : p.natDegree = Monoid.exponent Fˣ := by
    apply Polynomial.natDegree_X_pow_sub_C

  -- p is not the zero polynomial
  have h_p_non_zero : p ≠ 0 := by {
    unfold p
    exact X_power_sub_C_non_zero h_n_positive
  }

  -- Define the set of roots of p
  let roots : Set F := p.rootSet F

  -- The set of roots is finite
  have h_roots_finite : roots.Finite := by exact Polynomial.rootSet_finite p F

  -- Define the set of unit values in the field
  let units_F_set : Set F := {x : F | ∃ u : Units F,  u.val = x}

  -- The cardinality of Fˣ equals the cardinality of the set of unit values
  have h_card_eq : Nat.card Fˣ = Nat.card units_F_set := by exact units_F_set_card_eq

  -- Every unit value is a root of p = X^n - 1
  have h_subset : units_F_set ⊆ roots := by {
    -- Take an arbitrary element x in the set of unit values
    intro x hx
    -- Extract the unit u such that x = u.val
    rcases hx with ⟨u, hu⟩
    -- Rewrite x as u.val
    rw [←hu]

    -- Now we need to show u.val ∈ roots
    unfold roots
    simp [Polynomial.mem_rootSet]
    -- This simplifies to showing p.eval u.val = 0

    unfold p
    simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one]
    -- We need to show u.val^n - 1 = 0, which means u.val^n = 1
    -- First we need to relate u.val^n to (u^n).val
    have h_val_pow : (u.val)^n = (u^n).val := by exact rfl
    rw [h_val_pow]
    -- Now we have (u^n).val = 1
    rw [h_roots u]
    -- Finally, show that 1.val = 1
    simp [Units.val_one]
    -- Finish with p ≠ 0
    exact h_p_non_zero
  }

  -- The cardinality of the set of unit values is at most the cardinality of the root set
  have h_le : Nat.card units_F_set ≤ Nat.card roots := by
    exact Nat.card_mono h_roots_finite h_subset

  -- The exponent of Fˣ equals its cardinality
  have h_exp_eq_card : Monoid.exponent Fˣ = Nat.card Fˣ := by {
  apply le_antisymm
  · -- Prove Monoid.exponent Fˣ ≤ Nat.card Fˣ
    -- This follows from the fact that the exponent divides the order
    exact Nat.le_of_dvd h_nat_card_pos exp_dvd_card
  · -- Prove Nat.card Fˣ ≤ Monoid.exponent Fˣ
    trans (Nat.card roots)
    · -- First show Nat.card Fˣ ≤ Nat.card roots
      rw [h_card_eq]  -- Replace Nat.card units_F_set with Nat.card Fˣ
      exact h_le      -- Use the inequality Nat.card units_F_set ≤ Nat.card roots
    · -- Then show Nat.card roots ≤ Monoid.exponent Fˣ
      rw [←h_p_deg]   -- Replace Monoid.exponent Fˣ by p.natDegree
      exact roots_card_le_natDegree -- Use the inequality Nat.card roots ≤ p.natDegree
  }

  -- A group is cyclic when its exponent equals its cardinality
  exact iscyclic_exp_eq_card h_exp_eq_card
}
