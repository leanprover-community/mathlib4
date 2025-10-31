/-
Copyright (c) 2025 Zihui Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihui Bai, Zhengfeng Yang
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
## Main definitions and results

* `MulAction (Equiv.Perm X) (X → Y)`: action of permutations on colorings by precomposition.
* `coloringEquiv`: two colorings are equivalent if they lie in the same orbit.
* `coloringEquiv_equivalence`: this defines an equivalence relation.
* `orbit_size_eq_index`: the orbit–stabilizer theorem reformulated for colorings.

## Implementation notes

We model a coloring as a function `X → Y`, where `X` is a finite set of objects
and `Y` is a finite set of colors.
The permutation group `Equiv.Perm X` acts on colorings by precomposition.
-/

open scoped BigOperators
open MulAction Finset Equiv

namespace DistinctColorings

variable {X Y : Type*} (c : X → Y)

/--
A *coloring* is a function `X → Y`.
The permutation group `Equiv.Perm X` acts on colorings by precomposition:
`(g • c) x = c (g⁻¹ x)`.
-/
instance : MulAction (Equiv.Perm X) (X → Y) where
  smul g c := fun x ↦ c (g⁻¹ • x)
  one_smul := by
    intro c
    ext x
    simp [HSMul.hSMul]
    change c ((1 : Equiv.Perm X) • x) = c x
    rw [one_smul (Equiv.Perm X) x]
  mul_smul := by
    intro g g' f
    ext x
    simp [HSMul.hSMul]
    change f ((g'⁻¹ * g⁻¹) • x) = f (g'⁻¹ • (g⁻¹ • x))
    rw [mul_smul g'⁻¹ g⁻¹ x]

/--
For permutations `f, g : Equiv.Perm X`, the colorings `g • c` and `f • c`
are equal if and only if `f⁻¹ * g` belongs to the stabilizer of `c`.
-/
theorem smul_eq_iff_mem_stabilizer (f g : Equiv.Perm X) (c : X → Y) :
    g • c = f • c ↔ f⁻¹ * g ∈ MulAction.stabilizer (Equiv.Perm X) c := by
  constructor
  · intro h_eq
    simp [MulAction.stabilizer]
    ext x
    simp only [MulAction.mul_smul]
    rw [h_eq]
    change c (f⁻¹ • (f • x)) = c x
    rw [inv_smul_smul]
  · intro h
    simp [MulAction.stabilizer] at h
    rw [← h]
    simp [mul_smul]
    rw [mul_smul] at h
    exact h

/-- Two colorings are equivalent if they lie in the same orbit
under the action of `Equiv.Perm X`. -/
def coloringEquiv (c₁ c₂ : X → Y) : Prop :=
  ∃ f : Equiv.Perm X, f • c₁ = c₂

/-- The equivalence relation given by `coloringEquiv`. -/
theorem coloringEquiv_equivalence : Equivalence (coloringEquiv (X := X) (Y := Y)) where
  refl c := ⟨1, by simp⟩
  symm := by
    rintro c₁ c₂ ⟨f, h⟩
    use f⁻¹
    rw [← h]
    exact inv_smul_smul f c₁
  trans := by
    rintro c₁ c₂ c₃ ⟨f, h₁⟩ ⟨g, h₂⟩
    use g * f
    rw [← h₂, ← h₁]
    exact mul_smul g f c₁

/-- Reformulation of the orbit–stabilizer theorem for colorings. -/
theorem orbit_size_eq_index (c : X → Y)
  [Fintype (Equiv.Perm X)]
  [Fintype (MulAction.orbit (Equiv.Perm X) c)]
  [Fintype (MulAction.stabilizer (Equiv.Perm X) c)] :
  Fintype.card (MulAction.orbit (Equiv.Perm X) c)
    = Fintype.card (Equiv.Perm X) /
      Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm X) c

  have hb : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
    simpa using (Fintype.card_pos_iff.mpr ⟨1, by simp [MulAction.stabilizer]⟩)
  rw [← h]
  exact (Nat.mul_div_cancel _ hb).symm

end DistinctColorings

open MvPolynomial

open MulAction Finset Equiv BigOperators
section

namespace CyclesOfGroupElements
universe u v
variable (X : Type u) (Y : Type v)
variable [Fintype (Quotient (MulAction.orbitRel (Equiv.Perm X) (X → Y)))]

/-- The number of distinct colorings up to permutation of `X`. -/
abbrev numDistinctColorings [Fintype (Quotient (MulAction.orbitRel (Equiv.Perm X) (X → Y)))] : ℕ  :=
  Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm X) (X → Y)))

/-- **Burnside’s lemma**: the number of orbits of a finite group action equals
the average number of fixed points. -/
theorem MulAction.card_orbits_eq_avg_card_fixedBy
    [Fintype (Equiv.Perm X)]
    [∀ g : Equiv.Perm X, Fintype (MulAction.fixedBy (X → Y) g)] :
    numDistinctColorings X Y =
      (∑ g : Equiv.Perm X, Fintype.card (MulAction.fixedBy (X → Y) g))
        / Fintype.card (Equiv.Perm X) := by
  rw [numDistinctColorings, MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  aesop


variable (X : Type u) [Fintype X]


/-- The quotient type of the cycles of `g : Perm X`. -/
abbrev CyclesOfGroup (g : Equiv.Perm X) : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid g)

/-- The number of cycles of the permutation `g` on `X`. -/
abbrev numCyclesOfGroup
    (g : Equiv.Perm X) [Fintype (CyclesOfGroup X g)] : ℕ :=
  Fintype.card (CyclesOfGroup X g)

/-- The number of permutations of `X` having exactly `i` cycles. -/
abbrev numGroupOfNumCycles (X : Type u) [MulAction (Equiv.Perm X) X] [Fintype (Equiv.Perm X)]
  [∀ g : (Equiv.Perm X), Fintype (CyclesOfGroup X g)] (i : ℕ) : ℕ :=
  Finset.card {g : (Equiv.Perm X) | numCyclesOfGroup X g = i}

end CyclesOfGroupElements

namespace MulAction

open CyclesOfGroupElements

variable {X Y : Type*}

@[simp] lemma toPerm_zpow_smul (g : Equiv.Perm X) (n : Int) (a : X) :
  ((MulAction.toPerm g) ^ n) a = (g ^ n) • a := by
  exact rfl

@[simp] lemma smul_fun_apply (g : Equiv.Perm X) (c : X → Y) (x : X) :
  (g • c) x = c (g⁻¹ • x) := by
  rfl

/-- A coloring is fixed by `g` iff it is constant on the cycles of `g`. -/
lemma f_mem_fixedBy_iff_forall_eq_to_eq (g : (Equiv.Perm X)) (c : X → Y) :
  c ∈ (MulAction.fixedBy (X → Y) g) ↔ ∀ a b,
    (⟦a⟧ : Quotient (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g))) = ⟦b⟧ → c a = c b := by
  constructor
  · intro hc a b hqab
    have hab : Equiv.Perm.SameCycle (MulAction.toPerm g) a b :=
      Quotient.exact hqab
    rcases hab with ⟨n, hn⟩
    have hfix_pow : ∀ m : Int, (g ^ m) • c = c := by
      intro m
      have hg : g • c = c := hc
      have hg_inv : g⁻¹ • c = c := by
        rw[← hg]
        simp
        rw[hg]
      classical
      have : (g ^ m) = (if 0 ≤ m then g ^ Int.toNat m else (g⁻¹) ^ Int.toNat (-m)) := by
        by_cases hm : m ≥ 0
        · rw [if_pos hm]
          have hcoerce : (Int.toNat m : Int) = m := Int.toNat_of_nonneg hm
          nth_rw 1 [← hcoerce]
          rfl
        · rw [if_neg hm]
          set n := Int.toNat (-m) with hn
          have hm' : m = - (n : ℕ) := by
            rw [hn]
            simp at hm
            have hm'':m≤ 0:= by
              exact Int.le_of_lt hm
            simp
            have h0 : (0 : Int) ≤ -m := by
              omega
            have hmax : max (-m) (0 : Int) = -m := max_eq_left h0
            calc
              m = -(-m) := by simp [neg_neg]    -- -(-m) = m
              _ = -max (-m) (0 : Int) := by rw [hmax]
          rw [hm']
          rw [zpow_neg ]
          rw [inv_pow]
          exact rfl
      revert this
      refine Int.induction_on m ?base ?step ?stepNeg
      · intro hn
        exact rfl
      · intro k ih
        rw [zpow_add_one]
        simp only [mul_smul]
        nth_rw 2 [← ih]
        · rw[hg]
          simp
        exact rfl
      · intro k ih
        rw [zpow_sub_one]
        simp only [mul_smul]
        nth_rw 2 [← ih]
        · rw[hg_inv]
          exact fun this => rfl
        simp
        by_cases hk : k = 0
        · rw [hk]
          exact fun a => rfl
        · exact fun a => False.elim (hk a)
    have hb : b = (g ^ n) • a := by
      simpa [toPerm_zpow_smul] using hn.symm
    have h1 : ((g ^ n) • c) ((g ^ n) • a) = c a := by
      simp [smul_fun_apply]
    have h2 : ((g ^ n) • c) ((g ^ n) • a) = c ((g ^ n) • a) := by
      have := hfix_pow n
      simpa using congrArg (fun f => f ((g ^ n) • a)) this
    have : c ((g ^ n) • a) = c a := by
      rw[← h2]
      exact h1
    simp [hb]
    rw[← this]
    rfl
  · intro hconst
    refine ?_
    ext x
    have hab : (⟦g⁻¹ • x⟧ :Quotient (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g)))= ⟦x⟧ := by
      apply Quotient.sound
      refine ⟨(1 : Int), ?_⟩
      simp only [zpow_one, Perm.smul_def, toPerm_apply, Perm.apply_inv_self]
    have := hconst (g⁻¹ • x) x hab
    rw[← this]
    exact hconst (g⁻¹ • x) (g⁻¹ • x) rfl

/-- The set of colorings of the cycles of `g` is equivalent to the set of colorings fixed by `g`. -/
def fixedBy_cycle_equiv (g : Equiv.Perm X) :
    (CyclesOfGroup X g → Y) ≃ MulAction.fixedBy (X → Y) g :=
{ toFun := fun f =>
    ⟨fun x => f ⟦x⟧,
     by
       ext x
       simp [HSMul.hSMul]
       apply congrArg
       apply Quotient.sound
       simp [instHasEquivOfSetoid, Equiv.Perm.SameCycle.setoid]
       use 1
       change g • g⁻¹ • x = x
       exact smul_inv_smul g x
       ⟩,
  invFun := fun f =>
    Quotient.lift f
      (by intro a b h;
          exact (f_mem_fixedBy_iff_forall_eq_to_eq g f.1).1 f.2 a b (Quotient.sound h)),
  left_inv := by
    intro f; ext ⟨x⟩; rfl,
  right_inv := by
    intro f; ext x; rfl }

variable {X Y : Type*} [Fintype Y]

/-- For a permutation `g : Equiv.Perm X`, the number of colorings of `X`
fixed by `g` equals `|Y|` raised to the number of cycles of `g`. -/
theorem card_fixedBy_perm_eq_pow_card_cycles
    [∀ g : Equiv.Perm X, Fintype (MulAction.fixedBy (X → Y) g)]
    [∀ g : Equiv.Perm X, Fintype (CyclesOfGroup X g)]
    [∀ g : Equiv.Perm X, DecidableEq (CyclesOfGroup X g)]
    (g : Equiv.Perm X) :
    Fintype.card Y ^ numCyclesOfGroup X g =
      Fintype.card (MulAction.fixedBy (X → Y) g) := by
  rw [numCyclesOfGroup, ← Fintype.card_fun]
  exact Fintype.card_congr (fixedBy_cycle_equiv g)

end MulAction

end
