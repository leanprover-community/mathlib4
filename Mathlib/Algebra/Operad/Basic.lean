import Mathlib.Algebra.Group.Action.Defs

/-- A MultiComposable is a structure that allows composition from an m-arity object
 into a n-arity object at location p (in the range 0 to n-1) to produce an (n+m-1)
 arity object. `Operad` is the canonical example. -/
class MultiComposable  (A : ℕ → Type*) where
  /- Compose the (n+1)-arity object at location p on the m-arity object. -/
  compose {n m} : A n → Fin n → A m → A (n+m-1)

/-- A Superposable is a structure that allows "superposition": given an n-arity object
 and n many m-arity objects, they can all enter and share arguments to make a new m-arity
object. `Clone` is the canonical example. -/
class Superposable (A : ℕ → Type*) where
  /- Compose the (n+1)-arity object at location p on the m-arity object. -/
  superpose {n m} : A n → (Fin n → A m) → A m

/- Families that have a "one" at grading 1. -/
class OneGradedOne (A : ℕ → Type*) extends One (A 1) where

variable {A} {m : ℕ}

/- Upgrade MultiComposable.compose to an operation on Sigma types. -/
def composeAt [MultiComposable A] (x : Sigma A) (y : Sigma A) (p : Fin x.fst) : Sigma A :=
  ⟨_, MultiComposable.compose x.snd p y.snd⟩

/- Upgrade Superposable.superpose to an operation on Sigma types. -/
def superpose [Superposable A] (x : Sigma A) (y : Fin x.fst → A m) : Sigma A :=
  ⟨m, Superposable.superpose x.snd y⟩

notation:70 x:71 " ∘[ " p:70 " ] " y:70  => composeAt x y p

infixr:70 " ∘∈ " => Superposable.superpose
infixr:70 " σ∘∈ " => superpose

/-- `OneGradedOne` yields a `One (Sigma A)` -/
instance ComposableOne_toOne [OneGradedOne A] : One (Sigma A) :=
  ⟨⟨1, 1⟩⟩

@[simp]
theorem eq_id_sigma_id [OneGradedOne A] : (1 : Sigma A).snd = 1 :=
  rfl

@[simp]
theorem eq_id_sigma_one [OneGradedOne A] : (1 : Sigma A).fst = 1 :=
  rfl

section SigmaMul

variable {ι : Type*}

universe s t

/- A SigmaMulAction exists on two sigma types with the same domain,
and gives a MulAction at each matched level. -/
class SigmaMulAction (M : ι → Type s) (A : ι → Type t) [m : ∀ i, Monoid (M i)] where
  /- At each ι, there's a MulAction from M i on the type A i -/
  act_at (i : ι) : @MulAction (M i) (A i) (m i)

variable {M : ι → Type s} {A : ι → Type t}

def SigmaMul_smul {i : ι} [∀ i, Monoid (M i)] [SigmaMulAction M A] : M i → A i → A i :=
  (SigmaMulAction.act_at i).smul

-- General notation for a SigmaMul, where an instance is provided
notation:70 x:71 " •σ[ " inst:70 " ] " y:70  => @SigmaMul_smul _ _ _ _ _ inst x y

-- Shortcut notation, where the instance is just inferred
infixr:73 " •σ " => @SigmaMul_smul _ _ _ _ _ _

end SigmaMul
