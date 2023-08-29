/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Init.Control.Lawful

#align_import control.monad.cont from "leanprover-community/mathlib"@"d6814c584384ddf2825ff038e868451a7c956f31"

/-!
# Continuation Monad

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>
-/

universe u v w u₀ u₁ v₀ v₁

structure MonadCont.Label (α : Type w) (m : Type u → Type v) (β : Type u) where
  apply : α → m β
#align monad_cont.label MonadCont.Label

def MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x
#align monad_cont.goto MonadCont.goto

class MonadCont (m : Type u → Type v) where
  callCC : ∀ {α β}, (MonadCont.Label α m β → m α) → m α
#align monad_cont MonadCont

open MonadCont

class LawfulMonadCont (m : Type u → Type v) [Monad m] [MonadCont m]
    extends LawfulMonad m : Prop where
  callCC_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ → α → m ω) :
    (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
  callCC_bind_left {α} (β) (x : α) (dead : Label α m β → β → m α) :
    (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
  callCC_dummy {α β} (dummy : m α) : (callCC fun _ : Label α m β => dummy) = dummy
#align is_lawful_monad_cont LawfulMonadCont

export LawfulMonadCont (callCC_bind_right callCC_bind_left callCC_dummy)

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
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by
  unfold ContT; ext; apply h
  -- ⊢ x = y
                -- ⊢ x x✝ = y x✝
                     -- 🎉 no goals
#align cont_t.ext ContT.ext

instance : Monad (ContT r m) where
  pure x f := f x
  bind x f g := x fun i => f i g

instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
                -- ⊢ id <$> x✝ = x✝
                        -- 🎉 no goals
  (pure_bind := by intros; ext; rfl)
                   -- ⊢ pure x✝ >>= f✝ = f✝ x✝
                           -- ⊢ run (pure x✝ >>= f✝¹) f✝ = run (f✝¹ x✝) f✝
                                -- 🎉 no goals
  (bind_assoc := by intros; ext; rfl)
                    -- ⊢ x✝ >>= f✝ >>= g✝ = x✝ >>= fun x => f✝ x >>= g✝
                            -- ⊢ run (x✝ >>= f✝¹ >>= g✝) f✝ = run (x✝ >>= fun x => f✝¹ x >>= g✝) f✝
                                 -- 🎉 no goals

def monadLift [Monad m] {α} : m α → ContT r m α := fun x f => x >>= f
#align cont_t.monad_lift ContT.monadLift

instance [Monad m] : MonadLift m (ContT r m) where
  monadLift := ContT.monadLift

theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  -- ⊢ run (monadLift (x >>= f)) f✝ = run (monadLift x >>= monadLift ∘ f) f✝
  simp only [monadLift, MonadLift.monadLift, (· ∘ ·), (· >>= ·), bind_assoc, id.def, run,
    ContT.monadLift]
#align cont_t.monad_lift_bind ContT.monadLift_bind

instance : MonadCont (ContT r m) where
  callCC f g := f ⟨fun x _ => g x⟩ g

instance : LawfulMonadCont (ContT r m) where
  callCC_bind_right := by intros; ext; rfl
                          -- ⊢ (callCC fun f => cmd✝ >>= next✝ f) = do
                                  -- ⊢ run (callCC fun f => cmd✝ >>= next✝ f) f✝ =
                                       -- 🎉 no goals
  callCC_bind_left := by intros; ext; rfl
                         -- ⊢ (callCC fun f => goto f x✝ >>= dead✝ f) = pure x✝
                                 -- ⊢ run (callCC fun f => goto f x✝ >>= dead✝ f) f✝ = run (pure x✝) f✝
                                      -- 🎉 no goals
  callCC_dummy := by intros; ext; rfl
                     -- ⊢ (callCC fun x => dummy✝) = dummy✝
                             -- ⊢ run (callCC fun x => dummy✝) f✝ = run dummy✝ f✝
                                  -- 🎉 no goals

instance (ε) [MonadExcept ε m] : MonadExcept ε (ContT r m) where
  throw e _ := throw e
  tryCatch act h f := tryCatch (act f) fun e => h e f

end ContT

variable {m : Type u → Type v} [Monad m]

def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β → Label α (ExceptT ε m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (Except.ok a)⟩
#align except_t.mk_label ExceptTₓ.mkLabel

theorem ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ExceptT.mk (Except.ok <$> goto x (Except.ok i)) := by
  cases x; rfl
  -- ⊢ goto (mkLabel { apply := apply✝ }) i = mk (Except.ok <$> goto { apply := app …
           -- 🎉 no goals
#align except_t.goto_mk_label ExceptTₓ.goto_mkLabel

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β → ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))
#align except_t.call_cc ExceptTₓ.callCC

instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where
  callCC := ExceptT.callCC

instance {ε} [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ExceptT ε m) where
  callCC_bind_right := by
    intros; simp [callCC, ExceptT.callCC, callCC_bind_right]; ext
    -- ⊢ (callCC fun f => cmd✝ >>= next✝ f) = do
            -- ⊢ (ExceptT.mk do
                                                              -- ⊢ ExceptT.run
    dsimp
    -- ⊢ (do
    congr with ⟨⟩ <;> simp [ExceptT.bindCont, @callCC_dummy m _]
                      -- 🎉 no goals
                      -- 🎉 no goals
  callCC_bind_left := by
    intros
    -- ⊢ (callCC fun f => goto f x✝ >>= dead✝ f) = pure x✝
    simp [callCC, ExceptT.callCC, callCC_bind_right, ExceptT.goto_mkLabel, map_eq_bind_pure_comp,
      bind_assoc, @callCC_bind_left m _, Function.comp]
    ext; rfl
    -- ⊢ ExceptT.run (ExceptT.mk (pure (Except.ok x✝))) = ExceptT.run (pure x✝)
         -- 🎉 no goals
  callCC_dummy := by intros; simp [callCC, ExceptT.callCC, @callCC_dummy m _]; ext; rfl
                     -- ⊢ (callCC fun x => dummy✝) = dummy✝
                             -- ⊢ ExceptT.mk (ExceptT.run dummy✝) = dummy✝
                                                                               -- ⊢ ExceptT.run (ExceptT.mk (ExceptT.run dummy✝)) = ExceptT.run dummy✝
                                                                                    -- 🎉 no goals

def OptionT.mkLabel {α β} : Label (Option.{u} α) m β → Label α (OptionT m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (some a)⟩
#align option_t.mk_label OptionTₓ.mkLabel

theorem OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (some a)) :=
  rfl
#align option_t.goto_mk_label OptionTₓ.goto_mkLabel

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))
#align option_t.call_cc OptionTₓ.callCC

instance [MonadCont m] : MonadCont (OptionT m) where
  callCC := OptionT.callCC

instance [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (OptionT m) where
  callCC_bind_right := by
    intros; simp [callCC, OptionT.callCC, callCC_bind_right]; ext
    -- ⊢ (callCC fun f => cmd✝ >>= next✝ f) = do
            -- ⊢ (OptionT.mk do
                                                              -- ⊢ OptionT.run
    dsimp
    -- ⊢ (do
    congr with ⟨⟩ <;> simp [@callCC_dummy m _]
                      -- 🎉 no goals
                      -- 🎉 no goals
  callCC_bind_left := by
    intros;
    -- ⊢ (callCC fun f => goto f x✝ >>= dead✝ f) = pure x✝
    simp [callCC, OptionT.callCC, callCC_bind_right, OptionT.goto_mkLabel, map_eq_bind_pure_comp,
      bind_assoc, @callCC_bind_left m _, Function.comp]
    ext; rfl
    -- ⊢ OptionT.run (OptionT.mk (pure (some x✝))) = OptionT.run (pure x✝)
         -- 🎉 no goals
  callCC_dummy := by intros; simp [callCC, OptionT.callCC, @callCC_dummy m _]; ext; rfl
                     -- ⊢ (callCC fun x => dummy✝) = dummy✝
                             -- ⊢ OptionT.mk (OptionT.run dummy✝) = dummy✝
                                                                               -- ⊢ OptionT.run (OptionT.mk (OptionT.run dummy✝)) = OptionT.run dummy✝
                                                                                    -- 🎉 no goals

/- Porting note: In Lean 3, `One ω` is required for `MonadLift (WriterT ω m)`. In Lean 4,
                 `EmptyCollection ω` or `Monoid ω` is required. So we give definitions for the both
                 instances. -/

def WriterT.mkLabel {α β ω} [EmptyCollection ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, ∅)⟩

def WriterT.mkLabel' {α β ω} [Monoid ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, 1)⟩
#align writer_t.mk_label WriterTₓ.mkLabel'

theorem WriterT.goto_mkLabel {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, ∅)) := by cases x; rfl
                                                                 -- ⊢ goto (mkLabel { apply := apply✝ }) i = monadLift (goto { apply := apply✝ } ( …
                                                                          -- 🎉 no goals

theorem WriterT.goto_mkLabel' {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel' x) i = monadLift (goto x (i, 1)) := by cases x; rfl
                                                                  -- ⊢ goto (mkLabel' { apply := apply✝ }) i = monadLift (goto { apply := apply✝ }  …
                                                                           -- 🎉 no goals
#align writer_t.goto_mk_label WriterTₓ.goto_mkLabel'

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <| callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β → m (α × ω))

def WriterT.callCC' [MonadCont m] {α β ω : Type _} [Monoid ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <|
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β → m (α × ω))
#align writer_t.call_cc WriterTₓ.callCC'

instance (ω) [Monad m] [EmptyCollection ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC

instance (ω) [Monad m] [Monoid ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC'

def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) → Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => StateT.mk (fun s => f (a, s))⟩
#align state_t.mk_label StateTₓ.mkLabel

theorem StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = StateT.mk (fun s => goto x (i, s)) := by cases x; rfl
                                                                         -- ⊢ goto (mkLabel { apply := apply✝ }) i = StateT.mk fun s => goto { apply := ap …
                                                                                  -- 🎉 no goals
#align state_t.goto_mk_label StateTₓ.goto_mkLabel

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β → StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)
#align state_t.call_cc StateTₓ.callCC

instance {σ} [MonadCont m] : MonadCont (StateT σ m) where
  callCC := StateT.callCC

instance {σ} [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (StateT σ m) where
  callCC_bind_right := by
    intros
    -- ⊢ (callCC fun f => cmd✝ >>= next✝ f) = do
    simp [callCC, StateT.callCC, callCC_bind_right]; ext; rfl
    -- ⊢ (StateT.mk fun r => do
                                                     -- ⊢ StateT.run
                                                          -- 🎉 no goals
  callCC_bind_left := by
    intros;
    -- ⊢ (callCC fun f => goto f x✝ >>= dead✝ f) = pure x✝
    simp [callCC, StateT.callCC, callCC_bind_left, StateT.goto_mkLabel]; ext; rfl
    -- ⊢ (StateT.mk fun r => pure (x✝, r)) = pure x✝
                                                                         -- ⊢ StateT.run (StateT.mk fun r => pure (x✝, r)) s✝ = StateT.run (pure x✝) s✝
                                                                              -- 🎉 no goals
  callCC_dummy := by
    intros;
    -- ⊢ (callCC fun x => dummy✝) = dummy✝
    simp [callCC, StateT.callCC, callCC_bind_right, @callCC_dummy m _]
    -- ⊢ (StateT.mk fun r => StateT.run dummy✝ r) = dummy✝
    ext; rfl
    -- ⊢ StateT.run (StateT.mk fun r => StateT.run dummy✝ r) s✝ = StateT.run dummy✝ s✝
         -- 🎉 no goals

def ReaderT.mkLabel {α β} (ρ) : Label α m β → Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monadLift ∘ f⟩
#align reader_t.mk_label ReaderTₓ.mkLabel

theorem ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x; rfl
                                                              -- ⊢ goto (mkLabel ρ { apply := apply✝ }) i = monadLift (goto { apply := apply✝ } …
                                                                       -- 🎉 no goals
#align reader_t.goto_mk_label ReaderTₓ.goto_mkLabel

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β → ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)
#align reader_t.call_cc ReaderTₓ.callCC

instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where
  callCC := ReaderT.callCC

instance {ρ} [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ReaderT ρ m) where
  callCC_bind_right := by intros; simp [callCC, ReaderT.callCC, callCC_bind_right]; ext; rfl
                          -- ⊢ (callCC fun f => cmd✝ >>= next✝ f) = do
                                  -- ⊢ (ReaderT.mk fun r => do
                                                                                    -- ⊢ ReaderT.run
                                                                                         -- 🎉 no goals
  callCC_bind_left := by
    intros; simp [callCC, ReaderT.callCC, callCC_bind_left, ReaderT.goto_mkLabel]
    -- ⊢ (callCC fun f => goto f x✝ >>= dead✝ f) = pure x✝
            -- ⊢ (ReaderT.mk fun r => pure x✝) = pure x✝
    ext; rfl
    -- ⊢ ReaderT.run (ReaderT.mk fun r => pure x✝) ctx✝ = ReaderT.run (pure x✝) ctx✝
         -- 🎉 no goals
  callCC_dummy := by intros; simp [callCC, ReaderT.callCC, @callCC_dummy m _]; ext; rfl
                     -- ⊢ (callCC fun x => dummy✝) = dummy✝
                             -- ⊢ (ReaderT.mk fun r => ReaderT.run dummy✝ r) = dummy✝
                                                                               -- ⊢ ReaderT.run (ReaderT.mk fun r => ReaderT.run dummy✝ r) ctx✝ = ReaderT.run du …
                                                                                    -- 🎉 no goals

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ where
  toFun f r := F <| f fun x => F.symm <| r <| G x
  invFun f r := F.symm <| f fun x => F <| r <| G.symm x
  left_inv f := by funext r; simp
                   -- ⊢ (fun f r => ↑F.symm (f fun x => ↑F (r (↑G.symm x)))) ((fun f r => ↑F (f fun  …
                             -- 🎉 no goals
  right_inv f := by funext r; simp
                    -- ⊢ (fun f r => ↑F (f fun x => ↑F.symm (r (↑G x)))) ((fun f r => ↑F.symm (f fun  …
                              -- 🎉 no goals
#align cont_t.equiv ContT.equiv
