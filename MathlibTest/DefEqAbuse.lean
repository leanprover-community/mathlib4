import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic.DefEqAbuse

private axiom test_sorry : ∀ {α}, α

/-- info: #defeq_abuse: tactic succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
example (a b : ℕ) (h : a = b) : a = b := by
  #defeq_abuse in rw [h]

/-- info: #defeq_abuse: command succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
#defeq_abuse in
def myTestFun (n : ℕ) : ℕ := n + 1

/-- warning: #defeq_abuse: tactic fails regardless of `backward.isDefEq.respectTransparency` setting. -/
#guard_msgs (warning, drop error) in
example (n : Nat) : n = n + 1 := by
  #defeq_abuse in rfl

section SetAliasAbuse
/-! ### Type alias with lattice instance diamond

In Mathlib, `Set α` is a type alias (`def Set (α) := α → Prop`) whose lattice instances
go through `Pi`. This caused `rw` failures when matching lemmas against goals where the
`PartialOrder`/`OrderBot` instances came through different paths. Detecting it with
`#defeq_abuse` looked like:

```lean
example (s : Set ℕ) (a : ℕ) (ha : a ∉ s) : Disjoint s {a} := by
  #defeq_abuse in rw [Set.disjoint_singleton_right]
  -- reported: ❌️ (i : ℕ) → (fun a => Prop) i =?= Set ℕ
  exact ha
```

The test below reproduces this pattern with `MyPred`, a type alias for `α → Prop`
with lattice instances inherited from `Pi`, just like `Set`. -/

/-- Type alias for `α → Prop`, analogous to `Set α`. -/
def MyPred (α : Type) := α → Prop

noncomputable instance myPredDistribLattice : DistribLattice (MyPred ℕ) where
  __ : DistribLattice (ℕ → Prop) := inferInstance
  le s t := ∀ x, s x → t x
  inf s t x := s x ∧ t x
  sup s t x := s x ∨ t x

noncomputable instance myPredBoundedOrder : BoundedOrder (MyPred ℕ) where
  __ : BoundedOrder (ℕ → Prop) := inferInstance
  bot _ := False
  top _ := True

instance : Membership ℕ (MyPred ℕ) where mem s a := s a
noncomputable instance : Singleton ℕ (MyPred ℕ) where singleton a x := x = a

lemma myPred_disjoint_singleton_right (s : MyPred ℕ) (a : ℕ) :
    Disjoint s {a} ↔ a ∉ s :=
  test_sorry

-- Defined AFTER the lemma, so the lemma's elaborated type uses the DistribLattice path,
-- while this provides PartialOrder/OrderBot through a different path (CompleteSemilatticeInf).
noncomputable instance myPredCompleteLattice : CompleteLattice (MyPred ℕ) where
  __ : CompleteLattice (ℕ → Prop) := inferInstance

/--
warning: #defeq_abuse: tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  ❌️ (i : ℕ) → (fun a => Prop) i =?= MyPred ℕ
-/
#guard_msgs in
noncomputable example (s : MyPred ℕ) (a : ℕ) (ha : a ∉ s) : Disjoint s {a} := by
  #defeq_abuse in rw [myPred_disjoint_singleton_right]
  exact ha

end SetAliasAbuse

section VirtualParentAbuse
/-! ### Virtual parent `def` causing synthesis failure

In Mathlib, `Submodule.toAddSubgroup` is a plain `def` that acts as a "virtual parent"
projection. Because it's opaque at instance transparency, synthesis of `Module ℝ ↥l`
for `l : Submodule ℝ V` failed when the `AddCommMonoid` instances arrived through
different paths (`toAddSubgroup` vs `toAddSubmonoid`). Detecting it with `#defeq_abuse`
looked like:

```lean
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l
-- reported:
--   ❌️ apply @Submodule.module to Module ℝ ↥l
--     ❌️ l.toAddSubgroup =?= l.toAddSubmonoid
```

The test below reproduces this pattern with `MySub₂`, a structure extending `AddSubmonoid`
with a plain `def MySub₂.toAddSubgroup` as a virtual parent. -/

structure MySub₂ (G : Type) [AddCommGroup G] extends AddSubmonoid G where
  neg_closed : ∀ {x}, x ∈ carrier → -x ∈ carrier

def MySub₂.toAddSubgroup {G : Type} [AddCommGroup G] (s : MySub₂ G) : AddSubgroup G :=
  { s.toAddSubmonoid with neg_mem' := s.neg_closed }

instance {G : Type} [AddCommGroup G] : CoeSort (MySub₂ G) Type where
  coe s := {x : G // x ∈ s.carrier}

instance mySub₂AddCommMonoid {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    AddCommMonoid s :=
  s.toAddSubmonoid.toAddCommMonoid

instance mySub₂AddCommGroup {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    AddCommGroup s := fast_instance%
  { s.toAddSubgroup.toAddCommGroup with }

class MyAction (R α : Type) [AddCommMonoid α] where
  mySmul : R → α → α

instance mySub₂MyAction {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    MyAction ℕ s where
  mySmul _n x := x

def myOp {α : Type} [AddCommGroup α] [MyAction ℕ α] (x : α) : α :=
  -(MyAction.mySmul (R := ℕ) 1 x)

-- The warning output contains fvar IDs that vary between runs, so we just check it produces
-- a warning (not info or error).
-- It should produce something like:
/-
warning: #defeq_abuse: command fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following synthesis applications fail due to transparency:
  ❌️ apply @mySub₂MyAction to MyAction ℕ ↥s
    ❌️ s.toAddSubgroup =?= s.1
    ❌️ s.toAddSubgroup =?= s.toAddSubmonoid
    ❌️ s.toAddSubgroup.1 =?= s.1
    ❌️ ↑s.toAddSubgroup =?= ↑s.toAddSubmonoid
-/
#guard_msgs (drop warning) in
#defeq_abuse in
def testVirtualParent {G : Type} [AddCommGroup G] (s : MySub₂ G) (x : s) : s :=
  myOp x

-- The fix: marking the virtual parent `def` as `@[implicit_reducible]` makes it
-- transparent enough for instance synthesis to unify the two `AddCommMonoid` paths.
attribute [implicit_reducible] MySub₂.toAddSubgroup

/-- info: #defeq_abuse: command succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
#defeq_abuse in
def testVirtualParentFixed {G : Type} [AddCommGroup G] (s : MySub₂ G) (x : s) : s :=
  myOp x

end VirtualParentAbuse
