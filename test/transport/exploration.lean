import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Hom.Ring
import Mathlib.Tactic.ApplyFun
import Mathlib.GroupTheory.Finiteness
import Mathlib.Data.Finset.Functor

def noZeroDivisors (R : Type _) [Ring R] := ∀ (x y : R), x * y = 0 → x = 0 ∨ y = 0

example [Ring R] [Ring S] (w : noZeroDivisors S) (f : R →+* S) (inj : Function.Injective f) :
    noZeroDivisors R := by
  -- transport along f
  -- "Notice we have have `NoZeroDivisors S`, and want `NoZeroDivisors R`."
  -- "Notice that the goal is a `∀`"
  -- "Update the transport goal to `∀ (x y : S), x * y = 0 → x = 0 ∨ y = 0` ~~~> `∀ (x y : R), x * y = 0 → x = 0 ∨ y = 0`
  unfold noZeroDivisors at w ⊢
  -- "Notice that the first argument of the `∀` is something we know how to transport!"
  -- "So: transport it, and specialize."
  intro x
  specialize w (f x)
  -- "Now the transport goal is `∀ (y : S), ↑f x * y = 0 → ↑f x = 0 ∨ y = 0` ~~~> `∀ (y : R), x * y = 0 → x = 0 ∨ y = 0`"
  -- "Notice that the first argument of the `∀` is something we know how to transport!"
  -- "So: transport it, and specialize."
  intro y
  specialize w (f y)
  -- "Now the transport goal is `↑f x * ↑f y = 0 → ↑f x = 0 ∨ ↑f y = 0` ~~~> `x * y = 0 → x = 0 ∨ y = 0`"
  -- "The first argument is something we know how to transport: namely a equality in the source of an injective function."
  intro p
  apply_fun f at p
  -- Try:
  -- specialize w p
  -- but it fails!
  simp at p
  specialize w p
  clear p
  -- "Now the transport goal is `↑f x = 0 ∨ ↑f y = 0` ~~~> `x = 0 ∨ y = 0`"
  -- "This is an `∨`, so we should be able to separately transport each branch."
  cases' w with wl wr
  · left
    -- "Now the transport goal is `↑f x = 0` ~~~> `x = 0`"
    -- "The goal is an equation in the source of an injective function"
    apply_fun f
    -- exact wl -- oops! that fails
    simpa using wl
  · right
    apply_fun f
    simpa using wr

example [Zero R] [Zero S] (f : ZeroHom R S) (x : R) (y : S) (h : f x = y) (w : x = 0) :
    y = 0 := by
  -- transport w along f using h
  -- "Notice we're meant to transport `x = 0` ~~~> `y = 0`"
  -- "We should apply `f` to `w`"
  apply_fun f at w
  -- exact w -- oops! that fails
  simpa [h] using w

example [Ring R] [Ring S] (f : R →+* S) (inj : Function.Injective f)
    (w : ∃ (n : ℕ) (r : R), r ≠ 0 ∧ r ^ n = 0) :
    ∃ (n : ℕ) (s : S), s ≠ 0 ∧ s ^ n = 0 := by
  -- transport w along f
  -- "It's an existential"
  -- "The witness is in ℕ before and after, which is not involved in our transport, so we should leave it alone."
  cases' w with n w
  use n
  -- "It's an existential, and we can transport just using the bare function."
  cases' w with r w
  use f r
  -- "It's a conjunction, so split."
  cases' w with wl wr
  constructor
  · clear wr
    -- We're trying to transport an `≠`, so switch to the contrapositive.
    intro p
    apply wl
    clear wl
    -- Now it's an equality in the domain of an injective function.
    apply_fun f
    simpa using p
  · clear wl
    apply_fun f at wr
    simpa using wr

open Classical
#check Submonoid.closure
example [Monoid M] [Monoid N] (f : M →* N) (sur : Function.Surjective f)
    (w : Monoid.FG M) : Monoid.FG N := by
  -- transport w along f
  -- "The goal is a structure."
  constructor
  cases' w with w
  -- Now it's an existential:
  unfold Submonoid.FG at w ⊢
  -- The witness is a `Finset M`, which we know how to transport, so transport it!
  cases' w with s w
  use Functor.map f s
  -- Here `w` is an equation in `Submonoid M`, and the goal is an equation in `Submonoid N`.
  -- Really we should think here about why `Submonoid` is functorial, and use that...
  -- Let's have a magic step here, where we cleverly realise that:
  rw [Submonoid.eq_top_iff'] at w ⊢
  -- It's a forall, but we need to pick a preimage.
  intro n
  rcases sur n with ⟨m, rfl⟩
  specialize w m
  -- It's a forall!
  intro r
  specialize w (f ⁻¹' r) -- How did we know to use `⁻¹'` here?
  -- It's a forall!
  intro p
  apply w
  clear w
  -- It's an existential!
  cases' p with W p
  use W.comap f



-- Postponing this one, to avoid dealing with structures/classes for now:
example [Ring R] [Ring S] [IsCancelMulZero S] (f : R →+* S) (inj : Function.Injective f) :
    IsCancelMulZero R := by
  -- transport along f
  -- "Notice we're trying to construct `IsCancelMulZero R`, and we have a `IsCancelMulZero S`."
  -- "IsCancelMulZero R" is a structure, so we should call `constructor`
  refine @IsCancelMulZero.mk _ _ _ ?_ ?_
