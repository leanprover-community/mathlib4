/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Control.Lawful
import Batteries.Tactic.Congr
import Batteries.Lean.Except
import Batteries.Control.OptionT

/-!
# Continuation Monad

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>
<https://hackage.haskell.org/package/transformers-0.6.2.0/docs/Control-Monad-Trans-Cont.html>
-/

universe u v w u₀ u₁ v₀ v₁

structure MonadCont.Label (α : Type w) (m : Type u → Type v) (β : Type u) where
  apply : α → m β

def MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x

/--
The class of continuation monads/type transformers.

These are monads that support continuation-passing style programming
by providing a way to call-with-current-continuation (callCC).
That is, for any types α, β (in a particular universe)
This provides a function of type
`((α → m β) → m α) → m α`

-/
class MonadCont (m : Type u → Type v) where
  callCC : ∀ {α β}, (MonadCont.Label α m β → m α) → m α

open MonadCont

class LawfulMonadCont (m : Type u → Type v) [Monad m] [MonadCont m] : Prop
    extends LawfulMonad m where
  callCC_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ → α → m ω) :
    (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
  callCC_bind_left {α} (β) (x : α) (dead : Label α m β → β → m α) :
    (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
  callCC_dummy {α β} (dummy : m α) : (callCC fun _ : Label α m β => dummy) = dummy

export LawfulMonadCont (callCC_bind_right callCC_bind_left callCC_dummy)

/--
The continuation transformer.

Given a return type `r`, a type transformer (typically a monad) `m`, and a type `α`,
it represents computations that take a continuation function from `α` to `m r` and return an `m r`.

This allows for continuation-passing style programming, where control flow can be manipulated by
capturing and invoking continuations.
-/
def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r

abbrev Cont (r : Type u) (α : Type w) :=
  ContT r id α

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u → Type v} {α β : Type w}

/-- Run a continuation computation by providing a continuation function. -/
def run : ContT r m α → (α → m r) → m r :=
  id

/-- Map a function over the final result of a continuation computation.
This composes the given function with the continuation computation. -/
def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x

theorem run_contT_map_contT (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl

/-- Transform the continuation of a computation.
Takes a function that transforms continuations and a computation, and returns a new computation
with the transformed continuation. -/
def withContT (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β := fun g => x <| f g

theorem run_withContT (f : (β → m r) → α → m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl

@[ext]
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by
  unfold ContT; ext; apply h

instance : Monad (ContT r m) where
  pure x f := f x
  bind x f g := x fun i => f i g

instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)

def monadLift [Monad m] {α} : m α → ContT r m α := fun x f => x >>= f

instance [Monad m] : MonadLift m (ContT r m) where
  monadLift := ContT.monadLift

theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  simp only [monadLift, (· ∘ ·), (· >>= ·), bind_assoc, id, run,
    ContT.monadLift]

instance : MonadCont (ContT r m) where
  callCC f g := f ⟨fun x _ => g x⟩ g

instance : LawfulMonadCont (ContT r m) where
  callCC_bind_right := by intros; ext; rfl
  callCC_bind_left := by intros; ext; rfl
  callCC_dummy := by intros; ext; rfl

/-- Note that `tryCatch` does not have correct behavior in this monad:
```
def foo : ContT Bool (Except String) Bool := do
  let x ← try
    pure true
  catch _ =>
    return false
  throw s!"oh no {x}"
#eval foo.run pure
-- `Except.ok false`, no error
```
Here, the `throwError` is being run inside the `try`.
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/MonadExcept.20in.20the.20ContT.20monad/near/375341221)
for further discussion.
-/
instance (ε) [MonadExcept ε m] : MonadExcept ε (ContT r m) where
  throw e _ := throw e
  tryCatch act h f := tryCatch (act f) fun e => h e f

end ContT

variable {m : Type u → Type v}

section
variable [Monad m]

def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β → Label α (ExceptT ε m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (Except.ok a)⟩

theorem ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ExceptT.mk (Except.ok <$> goto x (Except.ok i)) := by
  cases x; rfl

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β → ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))

instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where
  callCC := ExceptT.callCC

instance {ε} [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ExceptT ε m) where
  callCC_bind_right := by
    intros; simp only [callCC, ExceptT.callCC, ExceptT.run_bind, callCC_bind_right]; ext
    dsimp
    congr with ⟨⟩ <;> simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    simp only [callCC, ExceptT.callCC, ExceptT.goto_mkLabel, map_eq_bind_pure_comp, Function.comp,
      ExceptT.run_bind, ExceptT.run_mk, bind_assoc, pure_bind, @callCC_bind_left m _]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, ExceptT.callCC, @callCC_dummy m _]; ext; rfl

def OptionT.mkLabel {α β} : Label (Option.{u} α) m β → Label α (OptionT m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (some a)⟩

theorem OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (some a)) :=
  rfl

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))

@[simp]
lemma run_callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    (OptionT.callCC f).run = (callCC fun x => OptionT.run <| f (OptionT.mkLabel x)) := rfl

instance [MonadCont m] : MonadCont (OptionT m) where
  callCC := OptionT.callCC

instance [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (OptionT m) where
  callCC_bind_right := by
    refine fun _ _ => OptionT.ext ?_
    simpa [callCC, Option.elimM, callCC_bind_right] using
      bind_congr fun | some _ => rfl | none => by simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    simp only [callCC, OptionT.callCC, OptionT.goto_mkLabel, bind_pure_comp, OptionT.run_bind,
      OptionT.run_mk, Option.elimM_map, Option.elim_some, Function.comp_apply,
      @callCC_bind_left m _]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, OptionT.callCC, @callCC_dummy m _]; ext; rfl

/- Porting note: In Lean 3, `One ω` is required for `MonadLift (WriterT ω m)`. In Lean 4,
                 `EmptyCollection ω` or `Monoid ω` is required. So we give definitions for the both
                 instances. -/

def WriterT.mkLabel {α β ω} [EmptyCollection ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, ∅)⟩

def WriterT.mkLabel' {α β ω} [Monoid ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, 1)⟩

theorem WriterT.goto_mkLabel {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, ∅)) := by cases x; rfl

theorem WriterT.goto_mkLabel' {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel' x) i = monadLift (goto x (i, 1)) := by cases x; rfl

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <| callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β → m (α × ω))

def WriterT.callCC' [MonadCont m] {α β ω : Type _} [Monoid ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <|
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β → m (α × ω))

end

instance (ω) [Monad m] [EmptyCollection ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC

instance (ω) [Monad m] [Monoid ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC'

def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) → Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => StateT.mk (fun s => f (a, s))⟩

theorem StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = StateT.mk (fun s => goto x (i, s)) := by cases x; rfl

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β → StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)

instance {σ} [MonadCont m] : MonadCont (StateT σ m) where
  callCC := StateT.callCC

instance {σ} [Monad m] [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (StateT σ m) where
  callCC_bind_right := by
    intros
    simp only [callCC, StateT.callCC, StateT.run_bind, callCC_bind_right]; ext; rfl
  callCC_bind_left := by
    intros
    simp only [callCC, StateT.callCC, StateT.goto_mkLabel, StateT.run_bind, StateT.run_mk,
      callCC_bind_left]; ext; rfl
  callCC_dummy := by
    intros
    simp only [callCC, StateT.callCC, @callCC_dummy m _]
    ext; rfl

def ReaderT.mkLabel {α β} (ρ) : Label α m β → Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monadLift ∘ f⟩

theorem ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x; rfl

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β → ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)

instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where
  callCC := ReaderT.callCC

instance {ρ} [Monad m] [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ReaderT ρ m) where
  callCC_bind_right := by intros; simp only [callCC, ReaderT.callCC, ReaderT.run_bind,
                                    callCC_bind_right]; ext; rfl
  callCC_bind_left := by
    intros; simp only [callCC, ReaderT.callCC, ReaderT.goto_mkLabel, ReaderT.run_bind,
      ReaderT.run_monadLift, monadLift_self, callCC_bind_left]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, ReaderT.callCC, @callCC_dummy m _]; ext; rfl

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ where
  toFun f r := F <| f fun x => F.symm <| r <| G x
  invFun f r := F.symm <| f fun x => F <| r <| G.symm x
  left_inv f := by funext r; simp
  right_inv f := by funext r; simp

section Examples

/-!
## Examples

Ths section adapts the example(s) from the end of the Haskell documentation for `MonadCont`:
<https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#t:MonadCont>
-/

def runCont {r α} (x : Cont r α) (f : α → r) : r :=
  ContT.run (m := id) x f

/-!
### Example 1: Simple Continuation Usage

Calculating length of a list continuation-style:

```haskell
calculateLength :: [a] -> Cont r Int
calculateLength l = return (length l)
Here we use calculateLength by making it to pass its result to print:

main = do
  runCont (calculateLength "123") print
  -- result: 3
```

It is possible to chain Cont blocks with >>=.

```
double :: Int -> Cont r Int
double n = return (n * 2)

main = do
  runCont (calculateLength "123" >>= double) print
  -- result: 6
```
-/

def calculateLength {r α} (l : List α) : Cont r Int :=
  pure l.length

def example1a_main : IO Unit := do
  runCont (calculateLength ["1", "2", "3"]) IO.print

#eval example1a_main -- "3"

def double {r} (n : Int) : Cont r Int :=
  pure (n * 2)

def example1b_main : IO Unit := do
  runCont (calculateLength ["1", "2", "3"] >>= double) IO.print

#eval example1b_main -- "6"

/-!
### Example 2: Using `callCC`

This example gives a taste of how escape continuations work,
shows a typical pattern for their usage.

```haskell
-- Returns a string depending on the length of the name parameter.
-- If the provided string is empty, returns an error.
-- Otherwise, returns a welcome message.
whatsYourName :: String -> String
whatsYourName name =
  (`runCont` id) $ do                      -- 1
    response <- callCC $ \exit -> do       -- 2
      validateName name exit               -- 3
      return $ "Welcome, " ++ name ++ "!"  -- 4
    return response                        -- 5

validateName name exit = do
  when (null name) (exit "You forgot to tell me your name!")
```

Here is what this example does:

1. Runs an anonymous Cont block and extracts value from it with (`runCont` id).
   Here id is the continuation, passed to the Cont block.
2. Binds response to the result of the following callCC block, binds exit to the continuation.
3. Validates name. This approach illustrates advantage of using callCC over return.
   We pass the continuation to validateName,
  and interrupt execution of the Cont block from inside of validateName.
4. Returns the welcome message from the callCC block.
   This line is not executed if validateName fails.
5. Returns from the Cont block.

-/

def validateName (name : String) (exit : MonadCont.Label String (Cont String) Unit) :
    Cont String Unit :=
  if name.isEmpty then
    exit.apply "You forgot to tell me your name!"
  else
    pure ()

def whatsYourName (name : String) : String :=
  (runCont · id) (do
    let mut response ← callCC (fun exit => do
      validateName name exit
      pure <| "Welcome, " ++ name ++ "!")
    pure response)

#eval whatsYourName "Alice" -- "Welcome, Alice!"
#eval whatsYourName "" -- "You forgot to tell me your name!"

/-!
### Example 3: Using `ContT` Monad Transformer

`ContT` can be used to add continuation handling to other monads.
Here is an example how to combine it with IO monad:

```haskell
import Control.Monad.Cont
import System.IO

main = do
  hSetBuffering stdout NoBuffering
  runContT (callCC askString) reportResult

askString :: (String -> ContT () IO String) -> ContT () IO String
askString next = do
  liftIO $ putStrLn "Please enter a string"
  s <- liftIO $ getLine
  next s

reportResult :: String -> IO ()
reportResult s = do
  putStrLn ("You entered: " ++ s)
```

Action `askString` requests user to enter a string, and passes it to the continuation.
`askString` takes as a parameter a continuation taking a string parameter, and returning `IO ()`.
Compare its signature to `runContT` definition.

-/

-- Placeholder for IO operations
def IO.getLine : IO String := return "example input"

def askString (next : Label String (ContT Unit IO) String) : ContT Unit IO String := do
  IO.println "Please enter a string"
  let s ← IO.getLine
  next.apply s

def reportResult (s : String) : IO Unit := do
  IO.println s!"You entered: {s}"

def example3_main : IO Unit := do
  ContT.run (callCC askString) reportResult

#eval example3_main -- "You entered: example input"

end Examples
