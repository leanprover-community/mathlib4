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

def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r

abbrev Cont (r : Type u) (α : Type w) :=
  ContT r id α

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u → Type v} {α β : Type w}

def run : ContT r m α → (α → m r) → m r :=
  id

def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x

theorem run_contT_map_contT (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl

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
      OptionT.run_mk, Option.elimM_map, Option.elim_some, @callCC_bind_left m _]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, OptionT.callCC, @callCC_dummy m _]; ext; rfl

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
