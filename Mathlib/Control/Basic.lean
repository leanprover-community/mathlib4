/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Control.SimpSet
import Mathlib.Tactic.CasesM
import Mathlib.Init.Control.Combinators

/-!
Extends the theory on functors, applicatives and monads.
-/

universe u v w

variable {α β γ : Type u}

-- mathport name: «expr $< »
-- notation:1 a " $< " f:1 => f a
/- the above notation doesn't appear *anywhere* in mathlib, and it is the same as the `|>` operator
in Lean 4, except with a different binding precedence, so we just remove it. -/

section Functor

/- warning: functor.map_map -> Functor.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{u}} {γ : Type.{u}} {f : Type.{u} -> Type.{v}} [_inst_1 : Functor.{u v} f] [_inst_2 : IsLawfulFunctor.{u v} f _inst_1] (m : α -> β) (g : β -> γ) (x : f α), Eq.{succ v} (f γ) (Functor.map.{u v} (fun {α : Type.{u}} => f α) _inst_1 β γ g (Functor.map.{u v} (fun {α : Type.{u}} => f α) _inst_1 α β m x)) (Functor.map.{u v} f _inst_1 α γ (Function.comp.{succ u succ u succ u} α β γ g m) x)
but is expected to have type
  forall (f : Type.{u} -> Type.{v}) [inst._@.Mathlib.Data.Equiv.Functor._hyg.22 : Functor.{u v} f] [inst._@.Mathlib.Data.Equiv.Functor._hyg.25 : LawfulFunctor.{u v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.22] {α : Type.{u}} {β : Type.{u}} {γ : Type.{u}} (m : α -> β) (g : β -> γ) (x : f α), Eq.{succ v} (f γ) (Functor.map.{u v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.22 β γ g (Functor.map.{u v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.22 α β m x)) (Functor.map.{u v} f inst._@.Mathlib.Data.Equiv.Functor._hyg.22 α γ (Function.comp.{succ u succ u succ u} α β γ g m) x)
Case conversion may be inaccurate. Consider using '#align functor.map_map Functor.map_mapₓ'. -/
variable {f : Type u → Type v} [Functor f] [LawfulFunctor f]
@[functor_norm]
theorem Functor.map_map (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  (comp_map _ _ _).symm
#align functor.map_map Functor.map_mapₓ

/- warning: id_map' -> id_map' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {f : Type.{u} -> Type.{v}} [_inst_1 : Functor.{u v} f] [_inst_2 : IsLawfulFunctor.{u v} f _inst_1] (x : f α), Eq.{succ v} (f α) (Functor.map.{u v} f _inst_1 α α (fun (a : α) => a) x) x
but is expected to have type
  forall {m : Type.{u_1} -> Type.{u_2}} {α : Type.{u_1}} [inst._@.Init.Control.Lawful._hyg.144 : Functor.{u_1 u_2} m] [inst._@.Init.Control.Lawful._hyg.147 : LawfulFunctor.{u_1 u_2} m inst._@.Init.Control.Lawful._hyg.144] (x : m α), Eq.{succ u_2} (m α) (Functor.map.{u_1 u_2} m inst._@.Init.Control.Lawful._hyg.144 α α (fun (a : α) => a) x) x
Case conversion may be inaccurate. Consider using '#align id_map' id_map'ₓ'. -/
attribute [simp] id_map'
#align id_map' id_map'ₓ

end Functor

section Applicative

variable {F : Type u → Type v} [Applicative F]

/-- A generalization of `List.zipWith` which combines list elements with an `Applicative`. -/
def zipMWith {α₁ α₂ φ : Type u} (f : α₁ → α₂ → F φ) : ∀ (_ : List α₁) (_ : List α₂), F (List φ)
  | x :: xs, y :: ys => (· :: ·) <$> f x y <*> zipMWith f xs ys
  | _, _ => pure []
#align mzip_with zipMWith

/-- Like `zipMWith` but evaluates the result as it traverses the lists using `*>`. -/
def zipMWith' (f : α → β → F γ) : List α → List β → F PUnit
  | x :: xs, y :: ys => f x y *> zipMWith' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit
#align mzip_with' zipMWith'

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

/-- A generalization of `List.partitionM` which partitions the list according to a monadic
predicate. `List.partition` corresponds to the case where `f = Id`. -/
def List.partitionM {f : Type → Type} [Monad f] {α : Type} (p : α → f Bool) :
  List α → f (List α × List α)
  | [] => pure ([], [])
  | x :: xs => condM (p x)
    (Prod.map (cons x) id <$> List.partitionM p xs)
    (Prod.map id (cons x) <$> List.partitionM p xs)
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

/- warning: seq_eq_bind_map -> seq_eq_bind_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{u}} {m : Type.{u} -> Type.{v}} [_inst_1 : Monad.{u v} m] [_inst_2 : LawfulMonad.{u v} m _inst_1] {x : m α} {f : m (α -> β)}, Eq.{succ v} (m β) (Seq.seq.{u v} m (Applicative.toHasSeq.{u v} m (Monad.toApplicative.{u v} m _inst_1)) α β f x) (Bind.bind.{u v} m (Monad.toHasBind.{u v} m _inst_1) (α -> β) β f (fun (_x : α -> β) => Functor.map.{u v} m (Applicative.toFunctor.{u v} m (Monad.toApplicative.{u v} m _inst_1)) α β _x x))
but is expected to have type
  forall {m : Type.{u} -> Type.{u_1}} {α : Type.{u}} {β : Type.{u}} [inst._@.Init.Control.Lawful._hyg.1037 : Monad.{u u_1} m] [inst._@.Init.Control.Lawful._hyg.1040 : LawfulMonad.{u u_1} m inst._@.Init.Control.Lawful._hyg.1037] (f : m (α -> β)) (x : m α), Eq.{succ u_1} (m β) (Seq.seq.{u u_1} m (Applicative.toSeq.{u u_1} m (Monad.toApplicative.{u u_1} m inst._@.Init.Control.Lawful._hyg.1037)) α β f (fun (x._@.Init.Control.Lawful._hyg.1063 : Unit) => x)) (Bind.bind.{u u_1} m (Monad.toBind.{u u_1} m inst._@.Init.Control.Lawful._hyg.1037) (α -> β) β f (fun (x._@.Init.Control.Lawful._hyg.1074 : α -> β) => Functor.map.{u u_1} m (Applicative.toFunctor.{u u_1} m (Monad.toApplicative.{u u_1} m inst._@.Init.Control.Lawful._hyg.1037)) α β x._@.Init.Control.Lawful._hyg.1074 x))
Case conversion may be inaccurate. Consider using '#align seq_eq_bind_map seq_eq_bind_mapₓ'. -/
#align seq_eq_bind_map seq_eq_bind_mapₓ

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

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the right (i.e., starting from the tail of the list). -/
def List.mapMAccumR (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapMAccumR f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)
#align list.mmap_accumr List.mapMAccumR

/-- Takes a value `β` and `List α` and accumulates pairs according to a monadic function `f`.
Accumulation occurs from the left (i.e., starting from the head of the list). -/
def List.mapMAccumL (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapMAccumL f a' xs
    pure (a'', y :: ys)
#align list.mmap_accuml List.mapMAccumL

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

-- [todo] add notation for `Functor.mapConst` and port `functor.map_const_rev`
/-- Returns `pure true` if the computatoin succeeds and `pure false` otherwise. -/
def succeeds {α} (x : F α) : F Bool :=
  Functor.mapConst true x <|> pure false
#align succeeds succeeds

/-- Attempts to perform the computation, but fails silently if it doesn't succeed. -/
def tryM {α} (x : F α) : F Unit :=
  Functor.mapConst () x <|> pure ()
#align mtry tryM

@[simp]
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard, if_pos]
#align guard_true guard_True

@[simp]
theorem guard_false {h : Decidable False} : @guard F _ False h = failure :=
  by simp [guard, if_neg not_false]
#align guard_false guard_False

end Alternative

namespace Sum

variable {e : Type v}

/- warning: sum.bind -> Sum.bind is a dubious translation:
lean 3 declaration is
  forall {e : Type.{v}} {α : Type.{u_1}} {β : Type.{u_2}}, (Sum.{v u_1} e α) -> (α -> (Sum.{v u_2} e β)) -> (Sum.{v u_2} e β)
but is expected to have type
  forall {e : Type.{v}} {α : Type.{_aux_param_0}} {β : Type.{_aux_param_1}}, (Sum.{v _aux_param_0} e α) -> (α -> (Sum.{v _aux_param_1} e β)) -> (Sum.{v _aux_param_1} e β)
Case conversion may be inaccurate. Consider using '#align sum.bind Sum.bindₓ'. -/
/-- The monadic `bind` operation for `Sum`. -/
protected def bind {α β} : Sum e α → (α → Sum e β) → Sum e β
  | inl x, _ => inl x
  | inr x, f => f x
#align sum.bind Sum.bindₓ

instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e

instance : LawfulFunctor (Sum.{v, u} e) := by refine' { .. } <;> intros <;> casesm Sum _ _ <;> rfl

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
class CommApplicative (m : Type _ → Type _) [Applicative m] extends LawfulApplicative m : Prop where
  /-- Computations performed first on `a : α` and then on `b : β` are equal to those performed in
  the reverse order. -/
  commutative_prod : ∀ {α β} (a : m α) (b : m β),
    Prod.mk <$> a <*> b = (fun b a => (a, b)) <$> b <*> a
#align is_comm_applicative CommApplicative

open Functor

theorem CommApplicative.commutative_map {m : Type _ → Type _} [h : Applicative m]
  [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
  f <$> a <*> b = flip f <$> b <*> a :=
  calc
    f <$> a <*> b = (fun p : α × β => f p.1 p.2) <$> (Prod.mk <$> a <*> b) :=
      by
        simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map] <;> rfl
    _ = (fun b a => f a b) <$> b <*> a :=
      by
        rw [@CommApplicative.commutative_prod m h] <;>
        simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map, (· ∘ ·)]

#align is_comm_applicative.commutative_map IsCommApplicative.commutative_map
