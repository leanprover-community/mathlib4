/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Combinatorics.Optimization.ConstraintSatisfaction.Expressibility

/-!

# Hardness of General-Valued Constraint Satisfaction Problems

Here we prove that, if a VCSP template over `LinearOrderedCancelAddCommMonoid` can express Max-Cut,
then it cannot have any commutative fractional polymorphism.

-/

variable {D C : Type*}

/-- VCSP template `Γ` can express the Max-Cut problem via summation and minimization. -/
def ValuedCSP.CanExpressMaxCut [Fintype D] [Nonempty D] [LinearOrderedAddCommMonoid C]
    (Γ : ValuedCSP D C) : Prop :=
  ∃ f : (Fin 2 → D) → C, ⟨2, f⟩ ∈ Γ.expressivePower ∧ f.HasMaxCutProperty

lemma Function.HasMaxCutPropertyAt.rows_lt_aux [OrderedCancelAddCommMonoid C]
    {f : (Fin 2 → D) → C} {a b : D} (mcf : f.HasMaxCutPropertyAt a b) (hab : a ≠ b)
    {ω : FractionalOperation D 2} (symmega : ω.IsSymmetric)
    {r : Fin 2 → D} (rin : r ∈ (ω.tt ![![a, b], ![b, a]])) :
    f ![a, b] < f r := by
  rw [FractionalOperation.tt, Multiset.mem_map] at rin
  rw [show r = ![r 0, r 1] from List.ofFn_inj.mp rfl]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 ≠ r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [ha0, hb1] at hab
      exact hab
    · rw [ha1, hb0] at hab
      exact hab.symm
  apply asymm
  obtain ⟨o, in_omega, rfl⟩ := rin
  show o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
  convert symmega ![a, b] ![b, a] (List.Perm.swap b a []) o in_omega using 2 <;>
    simp [Matrix.const_fin1_eq]

lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
    [OrderedCancelAddCommMonoid C] {f : (Fin 2 → D) → C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two', ← mcfab.left, ← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun r => f r)).sum := by
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map (fun r => f r)).sum := by
      apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (mcfab.rows_lt_aux hab symmega rin)
      · obtain ⟨g, _⟩ := valid.contains
        have : (fun i => g ((Function.swap ![![a, b], ![b, a]]) i)) ∈ ω.tt ![![a, b], ![b, a]] := by
          simp only [FractionalOperation.tt, Multiset.mem_map]
          use g
        exact ⟨_, this, mcfab.rows_lt_aux hab symmega this⟩
    rw [two_nsmul, two_nsmul]
    exact add_lt_add half_sharp half_sharp
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < ω.size • 2 • f ![a, b] := by
    convert lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : ω.size • 2 • f ![a, b] = 2 • ω.size • f ![a, b] := nsmul_left_comm ..
  have distrib : (ω.map (fun _ => f ![a, b])).sum = ω.size • f ![a, b] := by simp
  rw [rhs_swap, distrib] at impos
  exact ne_of_lt impos rfl

/-- If a VCSP template can express Max-Cut, it cannot have any commutative fractional polymorphism
    (i.e., a symmetric fractional polymorphism of arity two). -/
theorem ValuedCSP.CanExpressMaxCut.forbids_commutativeFractionalPolymorphism
    [Fintype D] [Nonempty D] [LinearOrderedCancelAddCommMonoid C]
    {Γ : ValuedCSP D C} (expressMC : Γ.CanExpressMaxCut)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) :
    ¬ ω.IsSymmetricFractionalPolymorphismFor Γ := by
  rintro ⟨frpol, symme⟩
  obtain ⟨f, fin, fmc⟩ := expressMC
  apply fmc.forbids_commutativeFractionalPolymorphism valid symme
  exact frpol.expressivePower ⟨2, f⟩ fin
