import Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]

class Foo (F : C₁ ⥤ C₂) where
  data : ℕ

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄)

/-!
The purpose of these tests is to prevent diamonds in the situation where
we have a typeclass (e.g. `Functor.Monoidal` or `Functor.CommShift`)
for functors such that an instance for a composition of functors
can be inferred from an instance from each of the functors.
Taking into account the placement of parentheses, we want to allow
`(F ⋙ G) ⋙ H` and `F ⋙ (G ⋙ H)` to have their own instances
(even though they are usually propositionally equal). The following
tests ensures that for the typeclass `Foo`, no instance
is inferred on `(F ⋙ G) ⋙ H` from an instance on `F ⋙ (G ⋙ H)`,
and vice versa.
-/

/--
error: failed to synthesize instance of type class
  Foo ((F ⋙ G) ⋙ H)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Foo (F ⋙ (G ⋙ H))] : Foo ((F ⋙ G) ⋙ H) := inferInstance

/--
error: failed to synthesize instance of type class
  Foo (F ⋙ G ⋙ H)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Foo ((F ⋙ G) ⋙ H)] : Foo (F ⋙ (G ⋙ H)) := inferInstance

end CategoryTheory
