import Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]

class Foo (F : C₁ ⥤ C₂) where
  data (F) : ℕ

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄)

/-!
The purpose of these tests is to prevent diamonds in the situation where
we have a typeclass (e.g. `Functor.Monoidal` or `Functor.CommShift`)
for functors such that an instance for a composition of functors
can be inferred from an instance for each of the functors.
Taking into account the placement of parentheses, we want to allow
`(F ⋙ G) ⋙ H` and `F ⋙ (G ⋙ H)` to have their own instances
(even though they are usually propositionally equal).
-/

/-! The two following tests ensure that for the typeclass `Foo`,
no instance is inferred on `(F ⋙ G) ⋙ H` from an instance on `F ⋙ (G ⋙ H)`,
and vice versa.
-/

/--
error: failed to synthesize instance of type class
  ((F ⋙ G) ⋙ H).Foo

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [(F ⋙ (G ⋙ H)).Foo] : ((F ⋙ G) ⋙ H).Foo := inferInstance

/--
error: failed to synthesize instance of type class
  (F ⋙ G ⋙ H).Foo

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [((F ⋙ G) ⋙ H).Foo] : (F ⋙ (G ⋙ H)).Foo := inferInstance

/-! Assuming a `Foo` instance for a composition of functors can be obtained from a
`Foo` instance on each functor (by taking the sum in `ℕ`), we check that the
instances obtained on `(F ⋙ G) ⋙ H` and `F ⋙ (G ⋙ H)` are equal,
but not defeq (because `Nat.assoc` is not a defeq in general). -/

instance [F.Foo] [G.Foo] : (F ⋙ G).Foo where
  data := Foo.data F + Foo.data G

/- This must succeed with `Nat.add_assoc` as a proof. It would be problematic
if `rfl` worked. -/
example [F.Foo] [G.Foo] [H.Foo] :
    Foo.data ((F ⋙ G) ⋙ H) = Foo.data (F ⋙ (G ⋙ H)) := by
  fail_if_success rfl
  exact Nat.add_assoc _ _ _

end CategoryTheory.Functor
