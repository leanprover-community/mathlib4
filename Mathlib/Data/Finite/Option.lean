module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

@[simp]
theorem Option.finite_iff {α : Type*} : Finite (Option α) ↔ Finite α where
  mpr _ := instFiniteOption
  mp
  | @Finite.intro _ 0 e => (e none).elim0
  | @Finite.intro _ (n + 1) e => ⟨(e.trans (finSuccEquiv n)).removeNone⟩


#min_imports
