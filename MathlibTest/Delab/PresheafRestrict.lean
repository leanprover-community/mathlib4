module

public import Mathlib.AlgebraicGeometry.Scheme

/-! Tests for the notations `x |_ₕ i`, `x |_ₗ U ⟪e⟫`, and `x |_ U` for restrictions of sections. -/

open CategoryTheory TopologicalSpace Opposite

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {F : X.Presheaf C} {U V : Opens X} (h : U ⟶ V) (e : U ≤ V) (x : ToType (F.obj (op V)))

/-- info: (ConcreteCategory.hom (F.map h.op)) x : CC (F.obj (op U)) -/
#guard_msgs in
#check F.map h.op x

open AlgebraicGeometry

/-- info: x |_ₕ h : CC (F.obj (op U)) -/
#guard_msgs in
#check x |_ₕ h

/-- info: x |_ U : CC (F.obj (op U)) -/
#guard_msgs in
#check x |_ₗ U ⟪e⟫

/-- info: x |_ U : CC (F.obj (op U)) -/
#guard_msgs in
#check x |_ U

/-- info: x |_ U |_ U : CC (F.obj (op U)) -/
#guard_msgs in
#check x |_ U |_ U

/-- info: x |_ₗ U ⟪e⟫ : CC (F.obj (op U)) -/
#guard_msgs in
set_option pp.proofs true in
#check x |_ U

example : x |_ₕ h = F.map h.op x := rfl
example : x |_ₗ U ⟪e⟫ = F.map (homOfLE e).op x := rfl
example : x |_ U = F.map (homOfLE e).op x := rfl

/-- The type of `t` is only known after elaborating the statement. -/
example (G : X.Presheaf C) (T : F ⟶ G) : Prop :=
  ∀ (U t), ∃ (V : _) (_ : V ≤ U), ∃ s, T.app _ s = t |_ V

example {S : Scheme} {U V : S.Opens} (x : Γ(S, V)) (e : U ≤ V) :
    x |_ U * x |_ U = (x * x) |_ U := by
  simp
