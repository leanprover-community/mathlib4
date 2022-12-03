import Mathlib.Mathport.Rename
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Data.List.Lemmas

universe u v w

def Vector (α : Type u) (n : Nat) :=
  { l : List α // l.length = n }
#align vector Vector

namespace Vector

variable {α : Type u} {β : Type v} {φ : Type w}

variable {n : Nat}

instance [DecidableEq α] : DecidableEq (Vector α n) := by
  unfold Vector
  infer_instance

@[match_pattern]
def nil : Vector α 0 :=
  ⟨[], rfl⟩
#align vector.nil Vector.nil

@[match_pattern]
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩
#align vector.cons Vector.cons

@[reducible]
def length (_ : Vector α n) : Nat :=
  n
#align vector.length Vector.length

open Nat

def head : Vector α (Nat.succ n) → α
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: _, _⟩ => a
#align vector.head Vector.head

theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl
#align vector.head_cons Vector.head_cons

def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩
#align vector.tail Vector.tail

theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl
#align vector.tail_cons Vector.tail_cons

@[simp]
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨a :: v, h⟩ => rfl
#align vector.cons_head_tail Vector.cons_head_tail

def toList (v : Vector α n) : List α :=
  v.1
#align vector.to_list Vector.toList

def nth : ∀ _ : Vector α n, Fin n → α
  | ⟨l, h⟩, i => l.nthLe i.1 (by rw [h] ; exact i.2)
#align vector.nth Vector.nth

def append {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
#align vector.append Vector.append

/- warning: vector.elim -> Vector.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {C : forall {n : Nat}, (Vector.{u_1} α n) -> Sort.{u}}, (forall (l : List.{u_1} α), C (List.length.{u_1} α l) (Subtype.mk.{succ u_1} (List.{u_1} α) (fun (l_1 : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l_1) (List.length.{u_1} α l)) l (Vector.Elim._proof_1.{u_1} α l))) -> (forall {n : Nat} (v : Vector.{u_1} α n), C n v)
but is expected to have type
  forall {α : Type.{_aux_param_0}} {C : forall {n : Nat}, (Vector.{_aux_param_0} α n) -> Sort.{u}}, (forall (l : List.{_aux_param_0} α), C (List.length.{_aux_param_0} α l) (Subtype.mk.{succ _aux_param_0} (List.{_aux_param_0} α) (fun (l_1 : List.{_aux_param_0} α) => Eq.{1} Nat (List.length.{_aux_param_0} α l_1) (List.length.{_aux_param_0} α l)) l (rfl.{1} Nat (List.length.{_aux_param_0} α l)))) -> (forall {n : Nat} (v : Vector.{_aux_param_0} α n), C n v)
Case conversion may be inaccurate. Consider using '#align vector.elim Vector.elimₓ'. -/
@[elab_as_elim]
def elim {α} {C : ∀ {n}, Vector α n → Sort u} (H : ∀ l : List α, C ⟨l, rfl⟩) {n : Nat} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l
#align vector.elim Vector.elim

-- map
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩
#align vector.map Vector.map

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl
#align vector.map_nil Vector.map_nil

theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl
#align vector.map_cons Vector.map_cons

def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.map₂ f x y, by simp [*]⟩
#align vector.map₂ Vector.map₂

def «repeat» (a : α) (n : Nat) : Vector α n :=
  ⟨List.repeat a n, List.length_repeat a n⟩
#align vector.repeat Vector.repeat

def drop (i : Nat) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩
#align vector.drop Vector.drop

def take (i : Nat) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩
#align vector.take Vector.take

def removeNth (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.removeNth l i.1, by rw [l.length_remove_nth i.1] <;> rw [p] ; exact i.2⟩
#align vector.remove_nth Vector.removeNth

def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i => f i.succ)
#align vector.of_fn Vector.ofFn

section Accum

open Prod

variable {σ : Type}

def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr Vector.mapAccumr

def mapAccumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ) : Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*]⟩
#align vector.map_accumr₂ Vector.mapAccumr₂

end Accum

protected theorem eq {n : Nat} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align vector.eq Vector.eq

protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)
#align vector.eq_nil Vector.eq_nil

@[simp]
theorem to_list_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl
#align vector.to_list_mk Vector.to_list_mk

@[simp]
theorem to_list_nil : toList nil = @List.nil α :=
  rfl
#align vector.to_list_nil Vector.to_list_nil

@[simp]
theorem to_list_length (v : Vector α n) : (toList v).length = n :=
  v.2
#align vector.to_list_length Vector.to_list_length

@[simp]
theorem to_list_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v
  rfl
#align vector.to_list_cons Vector.to_list_cons

@[simp]
theorem to_list_append {n m : Nat} (v : Vector α n) (w : Vector α m) : toList (append v w) = toList v ++ toList w := by
  cases v
  cases w
  rfl
#align vector.to_list_append Vector.to_list_append

@[simp]
theorem to_list_drop {n m : Nat} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl
#align vector.to_list_drop Vector.to_list_drop

@[simp]
theorem to_list_take {n m : Nat} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl
#align vector.to_list_take Vector.to_list_take

end Vector
