import Mathlib.Tactic.DeriveIsEmpty

namespace tests

-- for debugging, uncomment:
-- set_option trace.Elab.Deriving.isEmpty true

inductive Nomatch : Prop
  deriving IsEmpty

#synth IsEmpty Nomatch

inductive NomatchU : Type u
  deriving IsEmpty

#synth IsEmpty NomatchU

inductive Nomatch2 : Type 2
  deriving IsEmpty

#synth IsEmpty Nomatch2

inductive SelfLoop
  | intro1 : SelfLoop → SelfLoop
  | intro2 : Nat → SelfLoop → SelfLoop
  | intro3 : SelfLoop → Nat → SelfLoop → SelfLoop
  deriving IsEmpty

#synth IsEmpty SelfLoop

inductive ExistingIsEmpty : Prop
  | intro1 : Nat → Nomatch → ExistingIsEmpty
  | intro2 : Nat → Nomatch2 → ExistingIsEmpty
  deriving IsEmpty

#synth IsEmpty ExistingIsEmpty

inductive Args (α β : Type) {γ : Type 2} : Type 2
  | intro : α → γ → Empty → β → Args α β
  deriving IsEmpty

#synth IsEmpty (Args Unit Unit)

inductive Indices : (Type → Type) → Type → Type _
  | intro1 : ∀ α, Empty → Indices Id α
  | intro2 : ∀ m α, Indices m α → Indices m (m α)
  deriving IsEmpty

#synth IsEmpty (Indices Option Unit)

mutual
inductive MutualA
  | introA : MutualB → MutualA
inductive MutualB
  | introB : MutualA → MutualB
end
deriving instance IsEmpty for MutualA, MutualB

#synth IsEmpty MutualA
#synth IsEmpty MutualB

inductive AlwaysEmpty : Type → Type
  deriving IsEmpty

inductive UseAlwaysEmpty (α : Type)
  | intro : AlwaysEmpty α → UseAlwaysEmpty α
  deriving IsEmpty

#synth IsEmpty (UseAlwaysEmpty Nat)

end tests
