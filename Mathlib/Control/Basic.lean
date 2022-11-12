/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/
import Mathlib.Control.Tmp
import Mathlib.Mathport.Rename
import Mathlib.Init.Control.Combinators

universe u v w

variable {α β γ : Type u}

-- mathport name: «expr $< »
notation:1 a " $< " f:1 => f a

section

end

section Functor

variable {f : Type u → Type v} [Functor f] [LawfulFunctor f]
@[functor_norm]
theorem Functor.map_map (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  (comp_map _ _ _).symm
#align functor.map_map Functor.map_map

attribute [simp] id_map'
#align id_map' id_map'

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

def mzipWith {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (ma₁ : List α₁) (ma₂ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> mzipWith f xs ys
  | _, _ => pure []
#align mzip_with mzipWith

def mzipWith' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> mzipWith' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit
#align mzip_with' mzipWith'

variable [LawfulApplicative F]

attribute [functor_norm] seq_assoc pure_seq

@[simp]
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x
#align pure_id'_seq pure_id'_seq

attribute [functor_norm] seq_assoc pure_seq

@[functor_norm]
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
  x <*> f <$> y = (· ∘ f) <$> x <*> y := by
  simp [← pure_seq]
  simp [seq_assoc, ← comp_map, (· ∘ ·)]
  simp [pure_seq]
#align seq_map_assoc seq_map_assoc

@[functor_norm]
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) :
  f <$> (x <*> y) = (f ∘ ·) <$> x <*> y := by
  simp [← pure_seq] <;> simp [seq_assoc]
#align map_seq map_seq

end Applicative

-- TODO: setup `functor_norm` for `monad` laws
attribute [functor_norm] pure_bind bind_assoc bind_pure

section Monad

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

open List

def List.mpartition {f : Type → Type} [Monad f] {α : Type} (p : α → f Bool) :
  List α → f (List α × List α)
  | [] => pure ([], [])
  | x :: xs => condM (p x)
    (Prod.map (cons x) id <$> List.mpartition p xs)
    (Prod.map id (cons x) <$> List.mpartition p xs)
#align list.mpartition List.mpartition

theorem map_bind (x : m α) {g : α → m β} {f : β → γ} :
  f <$> (x >>= g) = x >>= fun a => f <$> g a := by
  rw [← bind_pure_comp, bind_assoc] <;> simp [bind_pure_comp]
#align map_bind map_bind

theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} :
  f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f)
  by rw [← bind_pure_comp, bind_assoc] <;> simp [pure_bind, (· ∘ ·)]
#align seq_bind_eq seq_bind_eq

#align seq_eq_bind_map seq_eq_bind_map

--/-- This is the Kleisli composition -/
--@[reducible]
--def fish {m} [Monad m] {α β γ} (f : α → m β) (g : β → m γ) := fun x => f x >>= g
--#align fish fish
--
---- mathport name: «expr >=> »
--infixl:55
--  " >=> " =>-- >=> is already defined in the core library but it is unusable
--  -- because of its precedence (it is defined with precedence 2) and
--  -- because it is defined as a lambda instead of having a named
--  -- function
--  fish

@[functor_norm]
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by simp only [(· >=> ·), functor_norm]
#align fish_pure fish_pure

@[functor_norm]
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by simp only [(· >=> ·), functor_norm]
#align fish_pipe fish_pipe

@[functor_norm]
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) : f >=> g >=> h = f >=> (g >=> h) := by
  simp only [(· >=> ·), functor_norm]
#align fish_assoc fish_assoc

variable {β' γ' : Type v}

variable {m' : Type v → Type w} [Monad m']

def List.mmapAccumr (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mmapAccumr f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)
#align list.mmap_accumr List.mmapAccumr

def List.mmapAccuml (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mmapAccuml f a' xs
    pure (a'', y :: ys)
#align list.mmap_accuml List.mmapAccuml

end Monad

section

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

theorem joinM_map_map {α β : Type u} (f : α → β) (a : m (m α)) :
  joinM (Functor.map f <$> a) = f <$> joinM a := by
  simp only [joinM, (· ∘ ·), id.def, ← bind_pure_comp, bind_assoc, map_bind, pure_bind]
#align mjoin_map_map joinM_map_map

theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, (· ∘ ·), id.def, map_bind, ← bind_pure_comp, bind_assoc, pure_bind]
#align mjoin_map_mjoin joinM_map_joinM

@[simp]
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, (· ∘ ·), id.def, map_bind, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]
#align mjoin_map_pure joinM_map_pure

@[simp]
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id
#align mjoin_pure joinM_pure

end

section Alternative

variable {F : Type → Type v} [Alternative F]

#check Function.const

def succeeds {α} (x : F α) : F Bool :=
  (Function.const _ x) <$> true <|> pure false
#align succeeds succeeds

def mtry {α} (x : F α) : F Unit :=
  x $> () <|> pure ()
#align mtry mtry

@[simp]
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard]
#align guard_true guard_true

@[simp]
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by simp [guard]
#align guard_false guard_false

end Alternative

namespace Sum

variable {e : Type v}

/- warning: sum.bind -> Sum.bind is a dubious translation:
lean 3 declaration is
  forall {e : Type.{v}} {α : Type.{u_1}} {β : Type.{u_2}}, (Sum.{v u_1} e α) -> (α -> (Sum.{v u_2} e β)) -> (Sum.{v u_2} e β)
but is expected to have type
  forall {e : Type.{v}} {α : Type.{_aux_param_0}} {β : Type.{_aux_param_1}}, (Sum.{v _aux_param_0} e α) -> (α -> (Sum.{v _aux_param_1} e β)) -> (Sum.{v _aux_param_1} e β)
Case conversion may be inaccurate. Consider using '#align sum.bind Sum.bindₓ'. -/
protected def bind {α β} : Sum e α → (α → Sum e β) → Sum e β
  | inl x, _ => inl x
  | inr x, f => f x
#align sum.bind Sum.bind

instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e

instance : IsLawfulFunctor (Sum.{v, u} e) := by refine' { .. } <;> intros <;> casesm Sum _ _ <;> rfl

instance : LawfulMonad (Sum.{v, u} e) where
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp_eq_map := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map_eq_seq := by
    intros
    cases f <;> rfl

end Sum

class IsCommApplicative (m : Type _ → Type _) [Applicative m] extends LawfulApplicative m : Prop where
  commutative_prod : ∀ {α β} (a : m α) (b : m β), Prod.mk <$> a <*> b = (fun b a => (a, b)) <$> b <*> a
#align is_comm_applicative IsCommApplicative

open Functor

theorem IsCommApplicative.commutative_map {m : Type _ → Type _} [Applicative m] [IsCommApplicative m] {α β γ} (a : m α)
    (b : m β) {f : α → β → γ} : f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [IsCommApplicative.commutative_prod] <;> simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]

#align is_comm_applicative.commutative_map IsCommApplicative.commutative_map
