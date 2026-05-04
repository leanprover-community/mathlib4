import Mathlib.GroupTheory.FinitelyPresentedGroup

variable {G : Type*} [Group G] {N : Subgroup G}

protected theorem Subgroup.IsNormalClosureFG.of_fg' [N.Normal] (hN : N.FG) : IsNormalClosureFG N := by
  obtain ⟨S, rfl, hSfinite⟩ := (Subgroup.fg_iff N).mp hN
  exact ⟨S, hSfinite, by rw [← Subgroup.normalClosure_closure_eq_normalClosure, Subgroup.normalClosure_eq_self]⟩
