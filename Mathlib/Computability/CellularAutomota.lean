/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Computability.Language
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset


/-!
# Cellular Automota

This file contains definitions about cellular automota.
The set of cells is a group `G`.
The set of states on each cell is `SingleCellState`.
-/

variable {G : Type*} [Group G]
variable {SingleCellState : Type*}

section Definitions

/-- A configuration of a cellular automaton
assigns a state in `SingleCellState` to each cell. -/
public abbrev Configuration := G → SingleCellState

/-- The group action of `G` on configurations coming from its action on itself. -/
public instance ConfigIsGSet :
  MulAction G
  (Configuration (G := G) (SingleCellState := SingleCellState)) where
  smul g_on_all config := fun cell_pos => config (g_on_all⁻¹ * cell_pos)
  one_smul config := by
    funext cell_pos
    change config (1⁻¹ * cell_pos) = config cell_pos
    rw [inv_eq_of_mul_eq_one_right (mul_one (1 : G)), one_mul]
  mul_smul g₁ g₂ config := by
    funext cell_pos
    change config ((g₁ * g₂)⁻¹ * cell_pos) = config (g₂⁻¹ * (g₁⁻¹ * cell_pos))
    rw [mul_inv_rev, mul_assoc]

/-- A cellular automaton
consists of a neighborhood and a local update rule
that uses the current states of the cells in that neighborhood
of each cell to determine the new state of that cell. -/
public structure CellularAutomaton where
  /-- The neighborhood of a cell is given by
  a finite set of group elements.
  Often it is a symmetric set
  such as (0,0) (0,±1), (±1,0) (±1,±1) for
  the 8 (including diagonally) neighbors and itself. -/
  neighborhood : Finset G
  /-- The local update rule takes the states of the cells
  in the neighborhood and produces a new state. -/
  localUpdateRule : (neighborhood → SingleCellState) → SingleCellState

namespace CellularAutomaton

/--
Ignore the cells outside
of the old neighborhood and use the local update rule
of the old neighborhood to determine the new state of a cell.
In particular, do this to make sure
that the identity is in the neighborhood.
This is part of product structure
where the new state needs to be given
at least the option of having dependence on the
old state of the cell itself even if it does not actually does so.
-/
public def expandNbhd
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (new_nbhd : Finset G) (h : A.neighborhood ⊆ new_nbhd) :
  CellularAutomaton (G := G) (SingleCellState := SingleCellState) where
  neighborhood := new_nbhd
  localUpdateRule := fun new_nbhd_states =>
    A.localUpdateRule
      fun old_nbhd => (
        new_nbhd_states ⟨old_nbhd.val, h old_nbhd.2⟩
      )

/-- The underlying function for a single time step but without it's G equivariance. -/
private def stepOne
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState)) :
  Configuration (G := G) (SingleCellState := SingleCellState) :=
  fun cell_pos => A.localUpdateRule
    fun shift_by_g => config (cell_pos * shift_by_g.val)

private lemma stepOne_smul
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (g : G) (config : Configuration (G := G) (SingleCellState := SingleCellState)) :
  A.stepOne (g • config) = g • (A.stepOne config) := by
  funext cell_pos
  simp only [stepOne]
  congr 1
  funext shift_by_g
  change config (g⁻¹ * (cell_pos * shift_by_g.val)) = config (g⁻¹ * cell_pos * shift_by_g.val)
  rw [mul_assoc]

/-- A single time step bundled as a `G`-equivariant map on configurations. -/
public def stepOneHom
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState)) :
  Configuration (G := G) (SingleCellState := SingleCellState) →[G]
    Configuration (G := G) (SingleCellState := SingleCellState) where
  toFun := A.stepOne
  map_smul' := stepOne_smul A

end CellularAutomaton

end Definitions

section PerodicConfigs

/--
A configuration is periodic with respect to a (not necessarily normal) subgroup of `G`
if it is invariant under the action of that subgroup.
One can think of this as modding out by the subgroup
and having a configuration on the quotient set which still
has a `G`-action on it, though with stabilizers now. -/
public def periodicConfigs
  {PeriodicGroup : Subgroup G} :
  Set (Configuration (G := G) (SingleCellState := SingleCellState)) :=
  {config | ∀ p : PeriodicGroup, (p • config) = config}

/--
The time step was G equivariant,
so the periodicity of a configuration
is preserved under the time step.
-/
public lemma periodicConfigsStayPeriodic
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  {PeriodicGroup : Subgroup G}
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (hconfig : config ∈ periodicConfigs (PeriodicGroup := PeriodicGroup)) :
  A.stepOneHom config ∈ periodicConfigs (PeriodicGroup := PeriodicGroup) := by
  intro periodic_element
  have h : (periodic_element : G) • config = config := by
    exact hconfig periodic_element
  calc periodic_element • (A.stepOneHom config)
      = (periodic_element : G) • (A.stepOneHom config) := by
        exact Subgroup.smul_def periodic_element (A.stepOneHom config)
    _ = A.stepOneHom ((periodic_element : G) • config) := by
      exact (A.stepOneHom.map_smul (periodic_element : G) config).symm
    _ = A.stepOneHom config := by
      rw [h]

end PerodicConfigs

section EmptyWorld

/--
The local update rule if all the neighborhood
is `emptyState` gives the new cell as also `emptyState`.
-/
public abbrev emptyWorldProperty
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (emptyState : SingleCellState) : Prop :=
  A.localUpdateRule (fun _ => emptyState) = emptyState

/-- If the `CellularAutomoton` `A` has the `emptyWorldProperty`
then a world full of `emptyState` stays that way under one time step. -/
public lemma emptyWorldStatic
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (emptyState : SingleCellState) :
  emptyWorldProperty A emptyState ->
    A.stepOneHom (fun _ => emptyState) = (fun _ => emptyState) := by
    intro h
    funext x
    exact h

end EmptyWorld

namespace CellularAutomaton

section StepN

/-- Iterate the step function `n` times. -/
public def stepN
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (n : ℕ) :
  Configuration (G := G) (SingleCellState := SingleCellState) →[G]
    Configuration (G := G) (SingleCellState := SingleCellState) :=
  Nat.recOn n
    (MulActionHom.id G)
    fun _ => fun before => before.comp A.stepOneHom

private lemma stepN_zero
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState)) :
  A.stepN 0 = MulActionHom.id G := rfl

private lemma stepN_succ
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState)) (n : ℕ) :
  A.stepN (n + 1) = (A.stepN n).comp A.stepOneHom := rfl

private lemma stepN_add
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState)) (m n : ℕ) :
  A.stepN (m + n) = (A.stepN m).comp (A.stepN n) := by
  induction n with
  | zero => rw [Nat.add_zero, stepN_zero, MulActionHom.comp_id]
  | succ k ih =>
    calc A.stepN (m + (k + 1))
        = A.stepN (m + k + 1) := by rw [Nat.add_succ]
      _ = (A.stepN (m + k)).comp A.stepOneHom := stepN_succ A (m + k)
      _ = ((A.stepN m).comp (A.stepN k)).comp A.stepOneHom := by rw [ih]
      _ = (A.stepN m).comp ((A.stepN k).comp A.stepOneHom) :=
            (MulActionHom.comp_assoc (A.stepN m) (A.stepN k) A.stepOneHom).symm
      _ = (A.stepN m).comp (A.stepN (k + 1)) := by rw [← stepN_succ A k]

private lemma stepN_smul
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (n : ℕ) (g : G) (config : Configuration (G := G) (SingleCellState := SingleCellState)) :
  A.stepN n (g • config) = g • (A.stepN n config) :=
  (A.stepN n).map_smul g config

/-- The value at one cell influences another cell at a later time.
This is whether one is in the "light-cone" of another.
-/
public abbrev influencesAtT
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (timestep : ℕ) (cell1 cell2 : G) :=
  ∃ (word : List (A.neighborhood)) (_hword : word.length = timestep),
    cell1*List.foldl (1:G) (f := fun acc n => acc*n.val) word = cell2

/-- The influences relation for one time step is the neigborhood relation -/
public lemma influencesAtOne
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (cell1 : G) :
  ∀ nbhr : A.neighborhood, A.influencesAtT 1 cell1 (cell1*nbhr.val) := by
  intro nbhr
  unfold influencesAtT
  use [nbhr], by simp
  simp

end StepN

section Gliders

/--
A configuration `config` is a glider if
after `after_t_steps` steps it returns to the
same configuration shifted by `shifts_by`.
This definition includes the degenerate case of
after_t_steps = 0 and shifts_by = 1,
which is every configuration.
-/
public abbrev isGlider
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (shifts_by : G) (after_t_steps : ℕ) : Prop :=
  A.stepN after_t_steps config = shifts_by • config

/-- An existential glider does not explicitly have
- how many steps it takes
- how much it shifts
However for this it is not including the
degenerate case, so that this Prop
is not trivially true for every configuration.
-/
public abbrev isExistentialGlider
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState)) : Prop :=
  ∃ (shifts_by : G) (after_t_steps : ℕ) (_after_t_steps_pos : after_t_steps > 0),
    A.isGlider config shifts_by after_t_steps

/--
If a configuration is a glider for a given
number of time steps and shift,
then it is also a glider for any multiple of that
number of time steps and the corresponding power of that shift.
-/
public lemma gliderOtherSteps
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (shifts_by : G) (after_t_steps : ℕ)
  (repeat_this_many : ℕ) :
  A.isGlider config shifts_by after_t_steps →
  A.isGlider config (shifts_by^repeat_this_many) (after_t_steps*repeat_this_many) := by
  intro gliding
  unfold isGlider at gliding ⊢
  induction repeat_this_many with
  | zero => rw [Nat.mul_zero, pow_zero, one_smul, stepN_zero, MulActionHom.id_apply]
  | succ k ih =>
    rw [Nat.mul_succ, stepN_add, MulActionHom.comp_apply, gliding,
      (A.stepN (after_t_steps * k)).map_smul, ih, pow_succ', mul_smul]

/-- The other configurations
in the orbit of an glider are also gliders
with the same periodicity and shifts_by. -/
public lemma gliderSameOrbit
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (shifts_by : G) (after_t_steps : ℕ)
  (on_orbit : ℕ) :
  A.isGlider config shifts_by after_t_steps →
  A.isGlider (A.stepN on_orbit config) shifts_by after_t_steps := by
  intro gliding
  unfold isGlider
  rw [isGlider] at gliding
  rw [← MulActionHom.comp_apply, ← stepN_add, Nat.add_comm, stepN_add,
    MulActionHom.comp_apply, gliding]
  rw [stepN_smul]

/-- If a configuration is an existential glider with unspecified periodicity and shift,
then the other configurations in its orbit are also. -/
public lemma gliderSameOrbitExistential
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (on_orbit : ℕ) :
  A.isExistentialGlider config →
  A.isExistentialGlider (A.stepN on_orbit config) := by
    intro ⟨shifts_by, after_t_steps, after_t_steps_pos, gliding⟩
    have key := A.gliderSameOrbit config shifts_by after_t_steps on_orbit gliding
    use shifts_by
    use after_t_steps

/-- A still life is expressed as a glider that
returns to itself with no shift and does so immediately with
just one time step. -/
public abbrev isStillLife
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState)) : Prop :=
  isGlider A config 1 1

/-- If a configuration is a still life,
then it will return to itself with no shift at all times not just one step. -/
public lemma stillLifeOtherSteps
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (repeat_this_many : ℕ) :
  A.isStillLife config →
  A.isGlider config 1 repeat_this_many := by
  rw [isStillLife]
  have key := A.gliderOtherSteps config 1 1 repeat_this_many
  simp only [one_pow, Nat.one_mul] at key
  exact key


/-- An oscillator is expressed as a glider that
returns to itself with no shift and does so with some `periodicity`.
This includes the degenerate case of zero periodicity,
in which every configuration is an oscillator according to this
definition. -/
public abbrev isOscillator
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (periodicity : ℕ) : Prop :=
  isGlider A config 1 periodicity

/-- An existential oscillator does not explicitly have
how many steps it takes to return.
However to make this proposition nontrivial and not
always true for every `config`, periodicity must be positive here. -/
public abbrev isExistentialOscillator
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState)) : Prop :=
  ∃ (periodicity : ℕ) (_periodicity_pos : periodicity > 0), A.isOscillator config periodicity

/--
If a configuration is an oscillator for a given
number of time steps,
then it is also an oscillator for any multiple of that
number of time steps.
-/
public lemma oscillatorOtherSteps
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (periodicity : ℕ)
  (repeat_this_many : ℕ) :
  A.isOscillator config periodicity →
  A.isOscillator config (periodicity*repeat_this_many) := by
  intro oscillating
  unfold isOscillator at oscillating ⊢
  have key := A.gliderOtherSteps config 1 periodicity repeat_this_many
  simp only [one_pow] at key
  exact key oscillating

/-- The other configurations
in the orbit of an oscillator are also oscillators
with the same periodicity. -/
public lemma oscillatorSameOrbit
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (periodicity : ℕ)
  (on_orbit : ℕ) :
  A.isOscillator config periodicity →
  A.isOscillator (A.stepN on_orbit config) periodicity := by
  intro oscillating
  unfold isOscillator
  unfold isGlider
  rw [one_smul]
  rw [isOscillator, isGlider, one_smul] at oscillating
  rw [← MulActionHom.comp_apply, ← stepN_add, Nat.add_comm, stepN_add,
    MulActionHom.comp_apply, oscillating]

/-- If a configuration is an existential oscillator with unspecified periodicity,
then the other configurations in its orbit are also. -/
public lemma oscillatorSameOrbitExistential
  (A : CellularAutomaton (G := G) (SingleCellState := SingleCellState))
  (config : Configuration (G := G) (SingleCellState := SingleCellState))
  (on_orbit : ℕ) :
  A.isExistentialOscillator config →
  A.isExistentialOscillator (A.stepN on_orbit config) := by
  intro ⟨periodicity, ⟨periodicity_pos, oscillating⟩⟩
  have key := A.oscillatorSameOrbit config periodicity on_orbit oscillating
  use periodicity

end Gliders

end CellularAutomaton

section Product

variable {G1 : Type*} [Group G1]
variable {G2 : Type*} [Group G2]
variable {SingleCellState1 : Type*}
variable {SingleCellState2 : Type*}

/-- The product of two cellular automota
On the product of the groups as the set of cells.
The set of states on each cells is the product of the
corresponding state types.
The update rule is just the update rule of each
factor applied independently. -/
public def productCellularAutomaton
  (A₁ : CellularAutomaton (G := G1) (SingleCellState := SingleCellState1))
  (A₂ : CellularAutomaton (G := G2) (SingleCellState := SingleCellState2))
  (h1 : 1 ∈ A₁.neighborhood) (h2 : 1 ∈ A₂.neighborhood) :
  CellularAutomaton (G := G1 × G2) (SingleCellState := SingleCellState1 × SingleCellState2) where
  neighborhood := A₁.neighborhood ×ˢ A₂.neighborhood
  localUpdateRule := fun product_nbhd_states =>
    (
      A₁.localUpdateRule
        fun a1_nbhd => (
          product_nbhd_states ⟨
            (a1_nbhd.1, 1), Finset.mk_mem_product a1_nbhd.2 h2
          ⟩).1,
      A₂.localUpdateRule
        fun a2_nbhd => (
          product_nbhd_states ⟨
            (1, a2_nbhd.1), Finset.mk_mem_product h1 a2_nbhd.2
          ⟩).2
    )

end Product

section ElementaryCellularAutomaton

/--
A cellular automota on `Z` and the restriction
that level of locality is particularly on the nearest neighbors
and itself.
The `SingleCellState` can still be an arbitrary `Fintype` rather than `Bool`.
-/
public def elementaryCellularAutomaton_pre
  {SingleCellState : Type*} [Fintype SingleCellState]
  (localUpdateRuleNonGroup :
    SingleCellState × SingleCellState × SingleCellState
      → SingleCellState) :
  CellularAutomaton (G := ℤ) (SingleCellState := SingleCellState) where
  neighborhood := {-1,0,1}
  localUpdateRule := fun nbhd_states =>
    localUpdateRuleNonGroup
      (nbhd_states ⟨-1, by simp⟩,
       nbhd_states ⟨ 0, by simp⟩,
       nbhd_states ⟨ 1, by simp⟩)

/--
A traditional elementary cellular automota.
For convenience use `wolframRule` below
so that you can use the conventional number
to specify which rule rather than as a function
`localUpdateRuleNonGroup`
-/
public def elementaryCellularAutomaton
  (localUpdateRuleNonGroup :
    Bool × Bool × Bool
      → Bool) :
  CellularAutomaton (G := ℤ) (SingleCellState := Bool) :=
  elementaryCellularAutomaton_pre localUpdateRuleNonGroup

section BitHelpers

/--
For `n`=3, the `rule` is a number from 0 to 255
which is the Wolfram code for the elementary cellular automaton
and `pattern` is the values at cells left,center,right for inputs 0,1,2.
The final output is what happens to the center cell at the next time step.
This encapsulates the choices of how n booleans are interpreted
as a single `Fin 2^n`.
This also encapsulates how `Fin 2^n -> Fin 2` and `Fin 2^(2^n)`
are related with testBit over any other choices that could have been.

This is mostly so all endian-ness and bit-flip mistakes are confined to one place.
-/
def ruleTestBit
  (n : ℕ) (rule : Fin (2 ^ (2 ^ n))) (pattern : Fin n → Bool) : Bool :=
  (rule : ℕ).testBit ((List.ofFn pattern).foldl (fun acc b => 2 * acc + b.toNat) 0)

def threebitconfig
  (config_number : Fin 8) :
  ({-1, 0, 1} : Finset ℤ) -> Bool :=
  fun input =>
    match input.val with
      | -1 => (config_number : ℕ).testBit 2
      | 0 => (config_number : ℕ).testBit 1
      | 1 => (config_number : ℕ).testBit 0
      | _ => false

def threebitconfig2
  (config_number : Fin 8) :
  Fin 3-> Bool :=
  fun input =>
    match input with
      | 0 => (config_number : ℕ).testBit 2
      | 1 => (config_number : ℕ).testBit 1
      | 2 => (config_number : ℕ).testBit 0

lemma threebitconfig_eq_threebitconfig2 (i : Fin 8) :
    (fun j => match j with
      | 0 => threebitconfig i ⟨-1, by simp⟩
      | 1 => threebitconfig i ⟨0, by simp⟩
      | 2 => threebitconfig i ⟨1, by simp⟩) = threebitconfig2 i := by
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

lemma ruleTestBit_threebitconfig2 (rule : Fin 256) (i : Fin 8) :
    ruleTestBit 3 rule (threebitconfig2 i) = (rule : ℕ).testBit i := by
  fin_cases i <;> rfl

/-- Extracting bit `k` back out of the base-2 sum
built from 8 bits recover the `k`-th bit. -/
lemma bit8_testBit (a b c d e f g h : Bool) (k : Fin 8) :
    (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat +
      16 * e.toNat + 32 * f.toNat + 64 * g.toNat + 128 * h.toNat).testBit k =
      (match k with
        | 0 => a | 1 => b | 2 => c | 3 => d
        | 4 => e | 5 => f | 6 => g | 7 => h) := by
  fin_cases k <;>
    cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;>
    decide

/-- Extracting bit `k` back out of the base-2 sum
built from 3 bits recover the `k`-th bit. -/
lemma bit3_testBit (l c r : Bool) :
    (l.toNat * 4 + c.toNat * 2 + r.toNat).testBit 2 = l ∧
    (l.toNat * 4 + c.toNat * 2 + r.toNat).testBit 1 = c ∧
    (l.toNat * 4 + c.toNat * 2 + r.toNat).testBit 0 = r := by
  cases l <;> cases c <;> cases r <;> decide

lemma bitDiffer {n : ℕ} (x y : Fin (2 ^ n)) (hxy : x ≠ y) :
  ∃ j : Fin n, (x : ℕ).testBit j ≠ (y : ℕ).testBit j := by
  by_contra
  rw [not_exists] at this
  apply hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  rcases lt_or_ge i n with hi | hi
  · exact not_ne_iff.mp (this ⟨i, hi⟩)
  · rw [Nat.testBit_lt_two_pow (x.2.trans_le (Nat.pow_le_pow_right (by omega) hi)),
        Nat.testBit_lt_two_pow (y.2.trans_le (Nat.pow_le_pow_right (by omega) hi))]

end BitHelpers

/-- The elementary cellular automaton given by its Wolfram code `rule`. -/
public def wolframRule
  (rule : Fin 256) :
  CellularAutomaton (G := ℤ) (SingleCellState := Bool) :=
  elementaryCellularAutomaton
    fun (left, center, right) =>
      ruleTestBit 3 rule
        (fun i =>
          match i with
          | 0 => left
          | 1 => center
          | 2 => right
        )

/-- Rule 90 ignores the center cell and XORs the two neighbors -/
example (nbhd_states : ({-1, 0, 1} : Finset ℤ) → Bool) :
    (wolframRule 90).localUpdateRule nbhd_states =
      xor (nbhd_states ⟨-1, by simp⟩) (nbhd_states ⟨1, by simp⟩) := by
  rcases hl : nbhd_states ⟨-1, by simp⟩ with _ | _ <;>
  rcases hc : nbhd_states ⟨0, by simp⟩ with _ | _ <;>
  rcases hr : nbhd_states ⟨1, by simp⟩ with _ | _ <;>
  simp only [wolframRule, elementaryCellularAutomaton, elementaryCellularAutomaton_pre,
    ruleTestBit, hl, hc, hr] <;> decide

/-- Rule 170 just copies over the right neighbor -/
example (nbhd_states : ({-1, 0, 1} : Finset ℤ) → Bool) :
    (wolframRule 170).localUpdateRule nbhd_states =
      (nbhd_states ⟨1, by simp⟩) := by
  rcases hl : nbhd_states ⟨-1, by simp⟩ with _ | _ <;>
  rcases hc : nbhd_states ⟨0, by simp⟩ with _ | _ <;>
  rcases hr : nbhd_states ⟨1, by simp⟩ with _ | _ <;>
  simp only [wolframRule, elementaryCellularAutomaton, elementaryCellularAutomaton_pre,
    ruleTestBit, hl, hc, hr] <;> decide

lemma existsWolframNumber
  (A : CellularAutomaton (G := ℤ) (SingleCellState := Bool))
  (h_Alocal : A.neighborhood = {-1,0,1})
  : ∃ rule : Fin 256, A = wolframRule rule := by
  -- The 8 bits of which rule to use
  -- zzz for 0th, and so on up to ooo for the 7th
  set zzz := A.localUpdateRule (h_Alocal ▸ threebitconfig 0)
  set zzo := A.localUpdateRule (h_Alocal ▸ threebitconfig 1)
  set zoz := A.localUpdateRule (h_Alocal ▸ threebitconfig 2)
  set zoo := A.localUpdateRule (h_Alocal ▸ threebitconfig 3)
  set ozz := A.localUpdateRule (h_Alocal ▸ threebitconfig 4)
  set ozo := A.localUpdateRule (h_Alocal ▸ threebitconfig 5)
  set ooz := A.localUpdateRule (h_Alocal ▸ threebitconfig 6)
  set ooo := A.localUpdateRule (h_Alocal ▸ threebitconfig 7)
  set which_rule : Fin 256 := ⟨zzz.toNat + 2 * zzo.toNat + 4 * zoz.toNat + 8 * zoo.toNat +
      16 * ozz.toNat + 32 * ozo.toNat + 64 * ooz.toNat + 128 * ooo.toNat, by
        have hb : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
        have := hb zzz; have := hb zzo; have := hb zoz; have := hb zoo
        have := hb ozz; have := hb ozo; have := hb ooz; have := hb ooo
        omega⟩
  refine ⟨which_rule, ?_⟩
  simp only [wolframRule, elementaryCellularAutomaton, elementaryCellularAutomaton_pre]
  cases A with
  | mk nbhd rule_fn =>
    simp only at h_Alocal
    subst h_Alocal
    congr 1
    funext nbhd_states
    have hb : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
    have hnb : nbhd_states = threebitconfig
        ⟨(nbhd_states ⟨-1, by simp⟩).toNat * 4 + (nbhd_states ⟨0, by simp⟩).toNat * 2 +
          (nbhd_states ⟨1, by simp⟩).toNat, by
            have := hb (nbhd_states ⟨-1, by simp⟩)
            have := hb (nbhd_states ⟨0, by simp⟩)
            have := hb (nbhd_states ⟨1, by simp⟩)
            omega⟩ := by
      funext x
      fin_cases x
      · exact (bit3_testBit (nbhd_states ⟨-1, by simp⟩) (nbhd_states ⟨0, by simp⟩)
          (nbhd_states ⟨1, by simp⟩)).1.symm
      · exact (bit3_testBit (nbhd_states ⟨-1, by simp⟩) (nbhd_states ⟨0, by simp⟩)
          (nbhd_states ⟨1, by simp⟩)).2.1.symm
      · exact (bit3_testBit (nbhd_states ⟨-1, by simp⟩) (nbhd_states ⟨0, by simp⟩)
          (nbhd_states ⟨1, by simp⟩)).2.2.symm
    rw [hnb]
    generalize hi :
      (⟨(nbhd_states ⟨-1, by simp⟩).toNat * 4 + (nbhd_states ⟨0, by simp⟩).toNat * 2 +
          (nbhd_states ⟨1, by simp⟩).toNat, by
            have := hb (nbhd_states ⟨-1, by simp⟩)
            have := hb (nbhd_states ⟨0, by simp⟩)
            have := hb (nbhd_states ⟨1, by simp⟩)
            omega⟩ : Fin 8) = i at hnb ⊢
    simp only [threebitconfig_eq_threebitconfig2, ruleTestBit_threebitconfig2]
    unfold which_rule
    simp only [bit8_testBit]
    fin_cases i <;> rfl

/-- Any cellular automota on `ℤ` which only looks at nearest neighbors
for the update rule is a `wolframRule rule` for some unique `rule` -/
public lemma existsUniqueWolframNumber
  (A : CellularAutomaton (G := ℤ) (SingleCellState := Bool))
  (h_Alocal : A.neighborhood = {-1,0,1})
  : ∃! rule : Fin 256, A = wolframRule rule := by
  have key := existsWolframNumber A h_Alocal
  obtain ⟨rule_num, h_rulenum⟩ := key
  use rule_num
  refine And.intro ?hleft ?hright
  · exact h_rulenum
  · intro y hy
    rw [h_rulenum] at hy
    by_contra
    have bad_input := bitDiffer (n:=8) (x:=rule_num) (y:=y) (hxy := Ne.symm this)
    obtain ⟨bad_input,h_bad_input⟩ := bad_input
    set bad_nbhd := threebitconfig bad_input
    let rule_on_bad_nbhd := (wolframRule rule_num).localUpdateRule bad_nbhd
    let y_on_bad_nbhd := (wolframRule y).localUpdateRule bad_nbhd
    have on_bad_nbhd_eq : rule_on_bad_nbhd = y_on_bad_nbhd := by
      unfold rule_on_bad_nbhd
      unfold y_on_bad_nbhd
      simp only [wolframRule, elementaryCellularAutomaton, elementaryCellularAutomaton_pre] at hy ⊢
      injection hy with _ hy_rule
      exact congrFun hy_rule _
    have on_bad_nbhd_neq : rule_on_bad_nbhd ≠ y_on_bad_nbhd := by
      unfold rule_on_bad_nbhd
      unfold y_on_bad_nbhd
      simp only [wolframRule, elementaryCellularAutomaton, elementaryCellularAutomaton_pre,
        bad_nbhd, threebitconfig_eq_threebitconfig2, ruleTestBit_threebitconfig2]
      exact h_bad_input
    exact on_bad_nbhd_neq on_bad_nbhd_eq

end ElementaryCellularAutomaton

section ConwayLife

/-- The number of `a : α` for which `f a` is `true`. -/
private def count_true
  {α : Type*}
  [Fintype α]
  (f : α -> Bool) : ℕ :=
  ∑ a, (f a).toNat

private abbrev z2_nbhrs : Finset (Multiplicative (ℤ × ℤ)) :=
  {
    (-1,-1),(-1,0),(-1,1),
    (0,-1),(0,0),(0,1),
    (1,-1),(1,0),(1,1)
  }

private abbrev z2_origin : z2_nbhrs :=
  ⟨(0,0), Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))⟩

private lemma count_true_le_card
  {α : Type*}
  [Fintype α]
  (f : α -> Bool) : count_true f ≤ Fintype.card α := by
  unfold count_true
  calc ∑ a, (f a).toNat
      ≤ ∑ _a : α, 1 := Finset.sum_le_sum fun a _ => by cases f a <;> decide
    _ = Fintype.card α := by simp

public def ConwayLife
  (become_alive : Fin 10 -> Bool)
  (become_dead : Fin 10 -> Bool)
  : CellularAutomaton
    (G:=Multiplicative (ℤ × ℤ))
    (SingleCellState:=Bool)
  where
  neighborhood := z2_nbhrs
  localUpdateRule := fun nbhd => (
    let live_nbhrs : Fin 10 := ⟨count_true nbhd, by
      have key := count_true_le_card (α := z2_nbhrs) nbhd
      simp at key
      have hcard : z2_nbhrs.card = 9 := by decide
      omega
    ⟩
    if nbhd z2_origin then (
      if become_dead live_nbhrs then false else true
    ) else (
      if become_alive live_nbhrs then true else false
    )
  )

private abbrev ConwayLifeTypical := ConwayLife
  (fun alive_nbhrs => alive_nbhrs = 3)
  (fun alive_nbhrs => alive_nbhrs < 3 ∨ alive_nbhrs > 5)

/--
`ConwayLife` has `emptyWorldProperty`
as long as the `become_alive` says
that a dead cell with 0 living neighbors stays dead.
`ConwayLifeTypical` satisfies this.
-/
public lemma ConwayLife_emptyWorldProperty
  (become_alive become_dead : Fin 10 -> Bool)
  (h : become_alive 0 = false) :
  emptyWorldProperty (ConwayLife become_alive become_dead) false := by
  unfold emptyWorldProperty ConwayLife
  have count_true_all_false : count_true (α := ↥z2_nbhrs) (f := fun _ => false) = 0 := by
    simp [count_true]
  simp only [count_true_all_false]
  rw [ite_eq_right (show ¬ (false = true) by decide)]
  rw [Fin.mk_zero, h]
  rw [
    ite_eq_right (show ¬ (false = true) by decide)]

end ConwayLife

section Languages

set_option linter.checkUnivs false in
/--
A cellular autotomota
where one can load up words in an `Alphabet`
step for `timing (len w)` and then read
a `Bool` by evaluating a predicate `acceptingCriterion.2` on the state
of the cell at `acceptingCriterion.1`.
-/
public structure CellularAutomatonAcceptor where
  SingleCellState : Type*
  trivialState: SingleCellState
  G : Type*
  gdecide : DecidableEq G
  ggroup : Group G
  Alphabet: Type*
  automota: CellularAutomaton (G:=G) (SingleCellState:=SingleCellState)
  trivialStays: emptyWorldProperty automota trivialState
  loading: (ℕ ↪ G) × ((ℕ × Alphabet) -> SingleCellState)
  timing : ℕ -> ℕ
  acceptingCriterion : (ℕ → G) × (SingleCellState -> Bool)

/--
For the particular case of `G=ℤ` and the
way loading based on position in the list is just casting
from `ℕ` to `ℤ` -/
public def oneDimensional
  (SingleCellState : Type*)
  [Fintype SingleCellState]
  (trivialState : SingleCellState)
  (Alphabet : Type*)
  (update : SingleCellState × SingleCellState × SingleCellState -> SingleCellState)
  (trivialStays : emptyWorldProperty (elementaryCellularAutomaton_pre update) trivialState)
  (loading : Alphabet -> SingleCellState)
  (read_pos: ℕ -> ℤ)
  (cellPredicate : SingleCellState -> Bool)
  : CellularAutomatonAcceptor where
  SingleCellState := SingleCellState
  trivialState := trivialState
  G := Multiplicative ℤ
  gdecide := inferInstance
  ggroup := inferInstance
  Alphabet := Alphabet
  automota := elementaryCellularAutomaton_pre update
  trivialStays := trivialStays
  loading := (
    Nat.castEmbedding.trans Multiplicative.ofAdd.toEmbedding,
    fun (_, a) => loading a
  )
  timing := fun n => n
  acceptingCriterion := (
    read_pos,
    cellPredicate
  )

/--
For the particular case of `G=ℤ` and also
that the state space is just `Option Alphabet`
with the loading being obtained from the identity map. -/
public def oneDimensional_option
  (Alphabet : Type*)
  [Fintype (Option Alphabet)]
  (update : Option Alphabet × Option Alphabet × Option Alphabet -> Option Alphabet)
  (trivialStays : update (none,none,none) = none)
  (read_pos : ℕ -> ℤ)
  (cellPredicate : Option Alphabet -> Bool)
  : CellularAutomatonAcceptor :=
  oneDimensional (Option Alphabet) none Alphabet
    update trivialStays (loading:=some) read_pos cellPredicate

namespace CellularAutomatonAcceptor

/--
Providing a list of `Alphabet`
creates a configuration which each
entry loaded as a `SingleCellState` of a corresponding cell
according to `loading`.
Every other cell is in `trivialState`. -/
public def load
  (A : CellularAutomatonAcceptor)
:
  List A.Alphabet -> Configuration (G:=A.G) (SingleCellState:=A.SingleCellState) :=
  let emptyWorld : Configuration (G:=A.G) (SingleCellState:=_) :=
    fun (_) => A.trivialState
  haveI := A.gdecide
  fun word => (
    (word.zip (List.range (word.length))).foldl (
      fun curConfig (curLetter, pos_list) =>
        Function.update (f:=curConfig) (a' := A.loading.1 pos_list)
          (v := (A.loading).2 (pos_list,curLetter))
    )
    emptyWorld
  )

/--
A word in `Alphabet` is accepted if
when loaded and then time stepped
for `timing (word.length)` steps
results in a state where we can
readout the result of a predicate at
the chosen cell.
Both of those are provided in `acceptingCriterion`. -/
public def accepts
(A : CellularAutomatonAcceptor)
:
  List A.Alphabet -> Bool :=
  haveI := A.ggroup
  fun word => (
    let startingConfig := A.load word
    let endingConfig := A.automota.stepN (G:=A.G) (n:=A.timing (word.length)) startingConfig
    let endingConfigReadout := endingConfig (A.acceptingCriterion.1 word.length)
    A.acceptingCriterion.2 endingConfigReadout
  )

/-- The language is the set of accepted words. -/
public def language
(A : CellularAutomatonAcceptor)
:
  Language (α:=A.Alphabet) :=
  {word | A.accepts word}

end CellularAutomatonAcceptor


end Languages
