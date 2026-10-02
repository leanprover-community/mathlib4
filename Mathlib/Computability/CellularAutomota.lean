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
