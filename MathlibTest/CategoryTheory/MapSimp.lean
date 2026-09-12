module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Tactic.CategoryTheory.Reassoc

open CategoryTheory

@[expose] public section

namespace Tests.MapSimp

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

def newF {x y : C} (f : x ⟶ y) : x ⟶ y := f

@[map (attr := reassoc (attr := simp))]
lemma comp_map_simp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    newF f ≫ newF g = f ≫ g := rfl

/--
info: Try this:
  [apply] simp only [comp_map_simp_map]
-/
#guard_msgs in
example {x y z : C} (f : x ⟶ y) (g : y ⟶ z) {D : Type*} [Category* D] (F : C ⥤ D) :
    F.map f ≫ F.map g = F.map (newF f) ≫ F.map (newF g) := by
  simp?

end Tests.MapSimp

open Lean Meta Elab Term Command

namespace Tests.MapSimpCheck

def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName

-- Test that simp attributes are added to all four generated lemmas with
-- `@[map (attr := reassoc (attr := simp))]`.
run_cmd liftTermElabM do
  let env ← getEnv
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_map
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_assoc
  guard <| hasSimpAttribute env ``Tests.MapSimp.comp_map_simp_map_assoc

end Tests.MapSimpCheck
