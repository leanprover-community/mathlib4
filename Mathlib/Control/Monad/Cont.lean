/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>

! This file was ported from Lean 3 source module control.monad.cont
! leanprover-community/mathlib commit d6814c584384ddf2825ff038e868451a7c956f31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Writer

universe u v w u₀ u₁ v₀ v₁

structure MonadCont.Label (α : Type w) (m : Type u → Type v) (β : Type u) where
  apply : α → m β
#align monad_cont.label MonadCont.Label

def MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x
#align monad_cont.goto MonadCont.goto

class MonadCont (m : Type u → Type v) where
  callCc : ∀ {α β}, (MonadCont.Label α m β → m α) → m α
#align monad_cont MonadCont

open MonadCont

class IsLawfulMonadCont (m : Type u → Type v) [Monad m] [MonadCont m] extends LawfulMonad m where
  callCc_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ → α → m ω) :
    (callCc fun f => cmd >>= next f) = cmd >>= fun x => callCc fun f => next f x
  callCc_bind_left {α} (β) (x : α) (dead : Label α m β → β → m α) :
    (callCc fun f : Label α m β => goto f x >>= dead f) = pure x
  callCc_dummy {α β} (dummy : m α) : (callCc fun f : Label α m β => dummy) = dummy
#align is_lawful_monad_cont IsLawfulMonadCont

export IsLawfulMonadCont ()

def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r
#align cont_t ContT

@[reducible]
def Cont (r : Type u) (α : Type w) :=
  ContT r id α
#align cont Cont

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def run : ContT r m α → (α → m r) → m r :=
  id
#align cont_t.run ContT.run

def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x
#align cont_t.map ContT.map

theorem run_contT_map_contT (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl
#align cont_t.run_cont_t_map_cont_t ContT.run_contT_map_contT

def withContT (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β := fun g => x <| f g
#align cont_t.with_cont_t ContT.withContT

theorem run_withContT (f : (β → m r) → α → m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl
#align cont_t.run_with_cont_t ContT.run_withContT

@[ext]
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by ext <;> apply h
#align cont_t.ext ContT.ext

instance : Monad (ContT r m) where
  pure α x f := f x
  bind α β x f g := x fun i => f i g

instance : LawfulMonad (ContT r m) where
  id_map := by intros; rfl
  pure_bind := by intros; ext; rfl
  bind_assoc := by intros; ext; rfl

def monadLift [Monad m] {α} : m α → ContT r m α := fun x f => x >>= f
#align cont_t.monad_lift ContT.monadLift

instance [Monad m] : HasMonadLift m (ContT r m) where monadLift α := ContT.monadLift

theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  simp only [monad_lift, HasMonadLift.monadLift, (· ∘ ·), (· >>= ·), bind_assoc, id.def, run,
    ContT.monadLift]
#align cont_t.monad_lift_bind ContT.monadLift_bind

instance : MonadCont (ContT r m) where callCc α β f g := f ⟨fun x h => g x⟩ g

instance : IsLawfulMonadCont (ContT r m) where
  callCc_bind_right := by intros <;> ext <;> rfl
  callCc_bind_left := by intros <;> ext <;> rfl
  callCc_dummy := by intros <;> ext <;> rfl

instance (ε) [MonadExcept ε m] : MonadExcept ε (ContT r m) where
  throw x e f := throw e
  catch α act h f := catch (act f) fun e => h e f

instance : MonadRun (fun α => (α → m r) → ULift.{u, v} (m r)) (ContT.{u, v, u} r m)
    where run α f x := ⟨f x⟩

end ContT

variable {m : Type u → Type v} [Monad m]

def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β → Label α (ExceptT ε m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (Except.ok a)⟩
#align except_t.mk_label ExceptTₓ.mkLabel

theorem ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ⟨Except.ok <$> goto x (Except.ok i)⟩ := by cases x <;> rfl
#align except_t.goto_mk_label ExceptTₓ.goto_mkLabel

def ExceptT.callCc {ε} [MonadCont m] {α β : Type _} (f : Label α (ExceptT ε m) β → ExceptT ε m α) :
    ExceptT ε m α :=
  ExceptT.mk (callCc fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x) : m (Except ε α))
#align except_t.call_cc ExceptTₓ.callCc

instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where callCc α β := ExceptT.callCc

instance {ε} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ExceptT ε m) where
  callCc_bind_right := by
    intros; simp [call_cc, ExceptT.callCc, call_cc_bind_right]; ext; dsimp
    congr with ⟨⟩ <;> simp [ExceptT.bindCont, @call_cc_dummy m _]
  callCc_bind_left := by
    intros
    simp [call_cc, ExceptT.callCc, call_cc_bind_right, ExceptT.goto_mkLabel, map_eq_bind_pure_comp,
      bind_assoc, @call_cc_bind_left m _]
    ext; rfl
  callCc_dummy := by intros; simp [call_cc, ExceptT.callCc, @call_cc_dummy m _]; ext; rfl

def OptionT.mkLabel {α β} : Label (Option.{u} α) m β → Label α (OptionT m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (some a)⟩
#align option_t.mk_label OptionTₓ.mkLabel

theorem OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = ⟨some <$> goto x (some i)⟩ := by cases x <;> rfl
#align option_t.goto_mk_label OptionTₓ.goto_mkLabel

def OptionT.callCc [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCc fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))
#align option_t.call_cc OptionTₓ.callCc

instance [MonadCont m] : MonadCont (OptionT m) where callCc α β := OptionT.callCc

instance [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (OptionT m) where
  callCc_bind_right := by
    intros; simp [call_cc, OptionT.callCc, call_cc_bind_right]; ext; dsimp
    congr with ⟨⟩ <;> simp [OptionT.bindCont, @call_cc_dummy m _]
  callCc_bind_left := by
    intros;
    simp [call_cc, OptionT.callCc, call_cc_bind_right, OptionT.goto_mkLabel, map_eq_bind_pure_comp,
      bind_assoc, @call_cc_bind_left m _]
    ext; rfl
  callCc_dummy := by intros; simp [call_cc, OptionT.callCc, @call_cc_dummy m _]; ext; rfl

def WriterT.mkLabel {α β ω} [One ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, 1)⟩
#align writer_t.mk_label WriterTₓ.mkLabel

theorem WriterT.goto_mkLabel {α β ω : Type _} [One ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, 1)) := by cases x <;> rfl
#align writer_t.goto_mk_label WriterTₓ.goto_mkLabel

def WriterT.callCc [MonadCont m] {α β ω : Type _} [One ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  ⟨callCc (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β → m (α × ω))⟩
#align writer_t.call_cc WriterTₓ.callCc

instance (ω) [Monad m] [One ω] [MonadCont m] : MonadCont (WriterT ω m)
    where callCc α β := WriterT.callCc

def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) → Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => ⟨fun s => f (a, s)⟩⟩
#align state_t.mk_label StateTₓ.mkLabel

theorem StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = ⟨fun s => goto x (i, s)⟩ := by cases x <;> rfl
#align state_t.goto_mk_label StateTₓ.goto_mkLabel

def StateT.callCc {σ} [MonadCont m] {α β : Type _} (f : Label α (StateT σ m) β → StateT σ m α) :
    StateT σ m α :=
  ⟨fun r => callCc fun f' => (f <| StateT.mkLabel f').run r⟩
#align state_t.call_cc StateTₓ.callCc

instance {σ} [MonadCont m] : MonadCont (StateT σ m) where callCc α β := StateT.callCc

instance {σ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (StateT σ m) where
  callCc_bind_right := by
    intros
    simp [call_cc, StateT.callCc, call_cc_bind_right, (· >>= ·), StateT.bind]; ext; dsimp
    congr with ⟨x₀, x₁⟩; rfl
  callCc_bind_left := by
    intros;
    simp [call_cc, StateT.callCc, call_cc_bind_left, (· >>= ·), StateT.bind, StateT.goto_mkLabel]
    ext; rfl
  callCc_dummy := by
    intros;
    simp [call_cc, StateT.callCc, call_cc_bind_right, (· >>= ·), StateT.bind, @call_cc_dummy m _]
    ext; rfl

def ReaderT.mkLabel {α β} (ρ) : Label α m β → Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monadLift ∘ f⟩
#align reader_t.mk_label ReaderTₓ.mkLabel

theorem ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x <;> rfl
#align reader_t.goto_mk_label ReaderTₓ.goto_mkLabel

def ReaderT.callCc {ε} [MonadCont m] {α β : Type _} (f : Label α (ReaderT ε m) β → ReaderT ε m α) :
    ReaderT ε m α :=
  ⟨fun r => callCc fun f' => (f <| ReaderT.mkLabel _ f').run r⟩
#align reader_t.call_cc ReaderTₓ.callCc

instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where callCc α β := ReaderT.callCc

instance {ρ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ReaderT ρ m) where
  callCc_bind_right := by intros; simp [call_cc, ReaderT.callCc, call_cc_bind_right]; ext; rfl
  callCc_bind_left := by
    intros; simp [call_cc, ReaderT.callCc, call_cc_bind_left, ReaderT.goto_mkLabel]
    ext; rfl
  callCc_dummy := by intros; simp [call_cc, ReaderT.callCc, @call_cc_dummy m _]; ext; rfl

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ where
  toFun f r := F <| f fun x => F.symm <| r <| G x
  invFun f r := F.symm <| f fun x => F <| r <| G.symm x
  left_inv f := by funext r <;> simp
  right_inv f := by funext r <;> simp
#align cont_t.equiv ContT.equiv

