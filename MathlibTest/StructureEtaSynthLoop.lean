import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian.{v} C]

-- set_option trace.Meta.synthInstance true in
example (P R : C) : Sub (R ⟶ P) := by
  -- Fails with 256 lines of: [resume] propagating AddGroup ↑(AddMonCat.of (R ⟶ P)) to subgoal AddGroup (R ⟶ P) of AddGroup (R ⟶ P)
  fail_if_success infer_instance

  have : AddCommGroup (R ⟶ P) := inferInstance
  -- Still fails
  fail_if_success infer_instance

  have : AddGroup (R ⟶ P) := inferInstance
  infer_instance -- Succeeds!
