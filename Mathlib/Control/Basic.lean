/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Control.Combinators
import Mathlib.Init.Function
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Attr.Core

#align_import control.basic from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
Extends the theory on functors, applicatives and monads.
-/

universe u v w

variable {α β γ : Type u}

section Functor

variable {f : Type u → Type v} [Functor f] [LawfulFunctor f]
@[functor_norm]
theorem Functor.map_map (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  (comp_map _ _ _).symm
#align functor.map_map Functor.map_mapₓ
-- order of implicits

#align id_map' id_map'ₓ
-- order of implicits

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

/-- A generalization of `List.zipWith` which combines list elements with an `Applicative`. -/
def zipWithM {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (_ : List α₁) (_ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> zipWithM f xs ys
  | _, _ => pure []
#align mzip_with zipWithM

/-- Like `zipWithM` but evaluates the result as it traverses the lists using `*>`. -/
def zipWithM' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> zipWithM' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit
#align mzip_with' zipWithM'

variable [LawfulApplicative F]

@[simp]
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x
#align pure_id'_seq pure_id'_seq

@[functor_norm]
theorem seq_map_assoc (x : F (α → β)) (f : γ → α) (y : F γ) :
    x <*> f <$> y = (· ∘ f) <$> x <*> y := by
  simp only [← pure_seq]
  simp only [seq_assoc, Function.comp, seq_pure, ← comp_map]
  simp [pure_seq]
#align seq_map_assoc seq_map_assoc

@[functor_norm]
theorem map_seq (f : β → γ) (x : F (α → β)) (y : F α) :
    f <$> (x <*> y) = (f ∘ ·) <$> x <*> y := by
  simp only [← pure_seq]; simp [seq_assoc]
#align map_seq map_seq

end Applicative

section Monad

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

open List

#align list.mpartition List.partitionM

theorem map_bind (x : m α) {g : α → m β} {f : β → γ} :
    f <$> (x >>= g) = x >>= fun a => f <$> g a := by
  rw [← bind_pure_comp, bind_assoc]; simp [bind_pure_comp]
#align map_bind map_bind

theorem seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} :
    f <$> x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    rw [← bind_pure_comp, bind_assoc]
    simp [pure_bind, Function.comp_def]
#align seq_bind_eq seq_bind_eq

#align seq_eq_bind_map seq_eq_bind_mapₓ
-- order of implicits and `Seq.seq` has a lazily evaluated second argument using `Unit`

@[functor_norm]
theorem fish_pure {α β} (f : α → m β) : f >=> pure = f := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
#align fish_pure fish_pure

@[functor_norm]
theorem fish_pipe {α β} (f : α → m β) : pure >=> f = f := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
#align fish_pipe fish_pipe

-- note: in Lean 3 `>=>` is left-associative, but in Lean 4 it is right-associative.
@[functor_norm]
theorem fish_assoc {α β γ φ} (f : α → m β) (g : β → m γ) (h : γ → m φ) :
    (f >=> g) >=> h = f >=> g >=> h := by
  simp (config := { unfoldPartialApp := true }) only [(· >=> ·), functor_norm]
#align fish_assoc fish_assoc

variable {β' γ' : Type v}
variable {m' : Type v → Type w} [Monad m']

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the right (i.e., starting from the tail of the list). -/
def List.mapAccumRM (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapAccumRM f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)
#align list.mmap_accumr List.mapAccumRM

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the left (i.e., starting from the head of the list). -/
def List.mapAccumLM (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapAccumLM f a' xs
    pure (a'', y :: ys)
#align list.mmap_accuml List.mapAccumLM

end Monad

section

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

theorem joinM_map_map {α β : Type u} (f : α → β) (a : m (m α)) :
    joinM (Functor.map f <$> a) = f <$> joinM a := by
  simp only [joinM, (· ∘ ·), id, ← bind_pure_comp, bind_assoc, map_bind, pure_bind]
#align mjoin_map_map joinM_map_map

theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, (· ∘ ·), id, map_bind, ← bind_pure_comp, bind_assoc, pure_bind]
#align mjoin_map_mjoin joinM_map_joinM

@[simp]
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, (· ∘ ·), id, map_bind, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]
#align mjoin_map_pure joinM_map_pure

@[simp]
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id
#align mjoin_pure joinM_pure

end

section Alternative

variable {F : Type → Type v} [Alternative F]

-- [todo] add notation for `Functor.mapConst` and port `Functor.mapConstRev`
/-- Returns `pure true` if the computation succeeds and `pure false` otherwise. -/
def succeeds {α} (x : F α) : F Bool :=
  Functor.mapConst true x <|> pure false
#align succeeds succeeds

/-- Attempts to perform the computation, but fails silently if it doesn't succeed. -/
def tryM {α} (x : F α) : F Unit :=
  Functor.mapConst () x <|> pure ()
#align mtry tryM

/-- Attempts to perform the computation, and returns `none` if it doesn't succeed. -/
def try? {α} (x : F α) : F (Option α) :=
  some <$> x <|> pure none

@[simp]
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard, if_pos]
#align guard_true guard_true

@[simp]
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by
  simp [guard, if_neg not_false]
#align guard_false guard_false

end Alternative

namespace Sum

variable {e : Type v}

/-- The monadic `bind` operation for `Sum`. -/
protected def bind {α β} : Sum e α → (α → Sum e β) → Sum e β
  | inl x, _ => inl x
  | inr x, f => f x
#align sum.bind Sum.bind
-- incorrectly marked as a bad translation by mathport, so we do not mark with `ₓ`.

instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e

instance : LawfulFunctor (Sum.{v, u} e) := by
  refine' { .. } <;> intros <;> (try casesm Sum _ _) <;> rfl

instance : LawfulMonad (Sum.{v, u} e) where
  seqRight_eq := by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl

end Sum

/-- A `CommApplicative` functor `m` is a (lawful) applicative functor which behaves identically on
`α × β` and `β × α`, so computations can occur in either order. -/
class CommApplicative (m : Type u → Type v) [Applicative m] extends LawfulApplicative m : Prop where
  /-- Computations performed first on `a : α` and then on `b : β` are equal to those performed in
  the reverse order. -/
  commutative_prod : ∀ {α β} (a : m α) (b : m β),
    Prod.mk <$> a <*> b = (fun (b : β) a => (a, b)) <$> b <*> a
#align is_comm_applicative CommApplicative

open Functor

variable {m}

theorem CommApplicative.commutative_map {m : Type u → Type v} [h : Applicative m]
    [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
  f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map]; rfl
    _ = (fun b a => f a b) <$> b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map, (· ∘ ·)]
#align is_comm_applicative.commutative_map CommApplicative.commutative_map
