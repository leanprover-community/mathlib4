import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic.DefEqAbuse

-- This test case relies on a known defeq abuse in the `Set` lattice instances
-- (going through `Pi` rather than `setOf`). It is fine to delete once that is fixed.
-- See the synthetic test cases below for self-contained tests that don't depend on
-- library defeq abuse.
/--
warning: #defeq_abuse: tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  ❌️ (i : ℕ) → (fun a => Prop) i =?= Set ℕ
-/
#guard_msgs in
example (s : Set ℕ) (a : ℕ) (ha : a ∉ s) : Disjoint s {a} := by
  #defeq_abuse in rw [Set.disjoint_singleton_right]
  exact ha

/-- info: #defeq_abuse: tactic succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
example (a b : ℕ) (h : a = b) : a = b := by
  #defeq_abuse in rw [h]

-- Command mode: no abuse detected
/-- info: #defeq_abuse: command succeeds with `backward.isDefEq.respectTransparency true`. No abuse detected. -/
#guard_msgs in
#defeq_abuse in
def myTestFun (n : ℕ) : ℕ := n + 1

-- Command mode: synthesis failure detected
-- This test case comes from https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/575690982
-- The warning output contains fvar IDs that vary between runs, so we just check it produces
-- a warning (not info or error).
-- We could convert this to a #guard_msgs if/when https://github.com/leanprover/lean4/pull/12688
-- is available
-- It should produce something like:
/-
warning: #defeq_abuse: command fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following synthesis applications fail due to transparency:
  ❌️ apply @Submodule.module to Module ℝ ↥_fvar.1076
    ❌️ l.toAddSubgroup =?= l.1
    ❌️ l.toAddSubgroup =?= l.toAddSubmonoid
    ❌️ l.toAddSubgroup.1 =?= l.1
    ❌️ ↑l.toAddSubgroup =?= ↑l.toAddSubmonoid
-/
#guard_msgs (drop warning) in
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l

-- Tactic mode: `simp` with `Zero` instance mismatch.
-- A lemma for generic `AddGroup α` has `0` as `@Zero.zero α (AddGroup.toZero)`.
-- When `simp` applies it to `ℤ`, it must match against `Int.ofNat 0`.
-- This tests that the tool filters out unrelated `simp` exploration failures
-- like `0 =?= a` and reports only the transparency-caused failure.
theorem sorriedResult.{u} : ∀ {α : Type u} [inst : AddGroup α] (a : α),
  0 = a ↔ a = a + a := sorry

/--
warning: #defeq_abuse: tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  ❌️ Zero.zero =?= Int.ofNat 0
-/
#guard_msgs in
theorem testSimpZero (a : ℤ) : 0 = a ↔ a = a + a := by
  #defeq_abuse in simp only [sorriedResult]

-- Tactic mode: fails regardless of transparency setting
/-- warning: #defeq_abuse: tactic fails regardless of `backward.isDefEq.respectTransparency` setting. -/
#guard_msgs (warning, drop error) in
example (n : Nat) : n = n + 1 := by
  #defeq_abuse in rfl

/-! ## Synthetic test cases

These do not depend on library defeq abuses and should remain stable even after
the upstream `Set` / `Submodule` issues are corrected.
-/

section SyntheticSetAbuse
/-! ### Synthetic tactic-mode test: type alias with lattice instance diamond

The pattern mirrors `Set α := α → Prop` whose lattice goes through `Pi`.
We define `MyPred α := α → Prop` and build lattice instances using the
`__ : DistribLattice (ℕ → Prop) := inferInstance` pattern (inheriting proofs
from Pi) while overriding the operations with `MyPred`-typed versions.
This is exactly what `Set.instDistribLattice` does.

The key to triggering the abuse in tactic mode is to create an **instance diamond**:
the lemma `myPred_disjoint_singleton_right` is elaborated with `PartialOrder` from
`myPredDistribLattice`, but a later `CompleteLattice` instance provides `PartialOrder`
through a different path. When `rw` tries to match the lemma's pattern against the goal,
the instances are syntactically different; verifying definitional equality requires
unfolding `MyPred`, which fails at instance transparency. -/

/-- Type alias for `α → Prop`, analogous to `Set α`. -/
def MyPred (α : Type) := α → Prop

-- Override operations while inheriting proof fields from Pi.
noncomputable instance myPredDistribLattice : DistribLattice (MyPred ℕ) where
  __ : DistribLattice (ℕ → Prop) := inferInstance
  le s t := ∀ x, s x → t x
  inf s t x := s x ∧ t x
  sup s t x := s x ∨ t x

noncomputable instance myPredBoundedOrder : BoundedOrder (MyPred ℕ) where
  __ : BoundedOrder (ℕ → Prop) := inferInstance
  bot _ := False
  top _ := True

-- MyPred-specific operations (like Set's Membership, Singleton)
instance : Membership ℕ (MyPred ℕ) where mem s a := s a
noncomputable instance : Singleton ℕ (MyPred ℕ) where singleton a x := x = a

-- Analogous to Set.disjoint_singleton_right.
-- The proof content doesn't matter for the abuse test; what matters is that
-- the elaborated type uses instances from myPredDistribLattice/myPredBoundedOrder.
lemma myPred_disjoint_singleton_right (s : MyPred ℕ) (a : ℕ) :
    Disjoint s {a} ↔ a ∉ s := by
  sorry

-- A higher-level instance that provides PartialOrder/OrderBot through a DIFFERENT path.
-- This mirrors Set's CompleteAtomicBooleanAlgebra providing PartialOrder through
-- CompleteSemilatticeInf rather than through DistribLattice.
-- Defined AFTER the lemma, so the lemma's elaborated type uses the DistribLattice path.
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

end SyntheticSetAbuse

section SyntheticVirtualParent
/-! ### Synthetic command-mode test: virtual parent `def`

The pattern mirrors `Submodule.toAddSubgroup` — a plain `def` that acts as a
"virtual parent" providing structure not in the actual extends-chain.

- `MySub₂ G` extends `AddSubmonoid G` (like `Submodule` extends `AddSubmonoid`)
- `MySub₂.toAddSubgroup` is a plain `def` (virtual parent, like `Submodule.toAddSubgroup`)
- `AddCommGroup ↥s` goes through `toAddSubgroup` (like `Submodule.addCommGroup`)
- `AddCommMonoid ↥s` goes through `toAddSubmonoid` (projection, always reduces)
- A class `SynAction` takes `[AddCommMonoid α]`, creating a diamond: the
  `AddCommMonoid` from `AddCommGroup` (via `toAddSubgroup`) must match the
  one from `SynAction` (via `toAddSubmonoid`), but `toAddSubgroup` is opaque
  under strict transparency.
-/

-- A simple structure extending AddSubmonoid with negation closure (like Submodule)
structure MySub₂ (G : Type) [AddCommGroup G] extends AddSubmonoid G where
  neg_closed : ∀ {x}, x ∈ carrier → -x ∈ carrier

-- Virtual parent: MySub₂ → AddSubgroup (plain def, like Submodule.toAddSubgroup)
def MySub₂.toAddSubgroup {G : Type} [AddCommGroup G] (s : MySub₂ G) : AddSubgroup G :=
  { s.toAddSubmonoid with neg_mem' := s.neg_closed }

-- Coercion to subtype (like Submodule's CoeSort)
instance {G : Type} [AddCommGroup G] : CoeSort (MySub₂ G) Type where
  coe s := {x : G // x ∈ s.carrier}

-- AddCommMonoid on the subtype via toAddSubmonoid (projection, always reduces)
instance mySub₂AddCommMonoid {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    AddCommMonoid s :=
  s.toAddSubmonoid.toAddCommMonoid

-- AddCommGroup on the subtype via toAddSubgroup (virtual parent def, the abuse!)
instance mySub₂AddCommGroup {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    AddCommGroup s := fast_instance%
  { s.toAddSubgroup.toAddCommGroup with }

-- A class with [AddCommMonoid α] prerequisite (like Module R M with [AddCommMonoid M])
class SynAction (R α : Type) [AddCommMonoid α] where
  synSmul : R → α → α

-- SynAction instance using mySub₂AddCommMonoid (the projection path)
instance mySub₂SynAction {G : Type} [AddCommGroup G] (s : MySub₂ G) :
    SynAction ℕ s where
  synSmul _n x := x

-- A function needing both AddCommGroup and SynAction
-- (like Module.Free.of_divisionRing which needs AddCommGroup and Module)
-- The AddCommGroup provides AddCommMonoid via toAddSubgroup path.
-- The SynAction uses AddCommMonoid from toAddSubmonoid path.
-- Lean needs these two AddCommMonoid instances to agree.
def synOp {α : Type} [AddCommGroup α] [SynAction ℕ α] (x : α) : α :=
  -(SynAction.synSmul (R := ℕ) 1 x)

-- The warning output contains fvar IDs that vary between runs, so we just check it produces
-- a warning (not info or error).
-- It should produce something like:
/-
warning: #defeq_abuse: command fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following synthesis applications fail due to transparency:
  ❌️ apply @mySub₂SynAction to SynAction ℕ ↥s
    ❌️ s.toAddSubgroup =?= s.1
    ❌️ s.toAddSubgroup =?= s.toAddSubmonoid
    ❌️ s.toAddSubgroup.1 =?= s.1
    ❌️ ↑s.toAddSubgroup =?= ↑s.toAddSubmonoid
-/
#guard_msgs (drop warning) in
#defeq_abuse in
def testSyntheticVP₂ {G : Type} [AddCommGroup G] (s : MySub₂ G) (x : s) : s :=
  synOp x

end SyntheticVirtualParent
