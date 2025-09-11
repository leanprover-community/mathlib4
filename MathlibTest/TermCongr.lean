import Mathlib.Tactic.TermCongr

/-!
`congr(...)` tests needing no additional imports
-/

namespace Tests

set_option autoImplicit true

--set_option trace.Elab.congr true

section congr_thms
/-! Tests that `congr(...)` subsumes `congr_arg`/`congr_fun`/`congr`.
Uses `(... :)` to make sure `congr(...)` is not seeing expected types. -/

example {α β : Sort _} (f : α → β) (x y : α) (h : x = y) :
    f x = f y := (congr(f $h) :)

example {α : Sort _} {β : α → Sort _} (f g : (x : α) → β x) (h : f = g) (x : α) :
    f x = g x := (congr($h x) :)

example {α β : Sort _} (f g : α → β) (hf : f = g) (x y : α) (hx : x = y) :
    f x = g y := (congr($hf $hx) :)

example {α β : Sort _} (f : α → β) (x y : α) (h : x = y) :
    congr_arg f h = congr(f $h) := rfl

example {α : Sort _} {β : α → Sort _} (f g : (x : α) → β x) (h : f = g) (x : α) :
    congr_fun h x = congr($h x) := rfl

example {α β : Sort _} (f g : α → β) (hf : f = g) (x y : α) (hx : x = y) :
    congr hf hx = congr($hf $hx) := rfl

end congr_thms

example (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by
  have h := congr(f $h) -- if `replace` instead of `have`, like `apply_fun f at h`
  guard_hyp h :ₛ f x = f y
  exact h

example (x y : Nat) (h : x = y) : 1 + x = 1 + y := congr(_ + $h)

example (x y : Nat) (h : x = y) : True := by
  have : 1 + x = _ := congr(_ + $h)
  guard_hyp this : 1 + x = 1 + y
  trivial

example : 0 + 1 = 1 := congr(_)

example : 0 + 1 = 1 := congr(_ + 1)

example [Decidable p] (x y : Nat) (h : x = y) : True := by
  have := congr(if p then 1 else $h)
  guard_hyp this :ₛ (if p then 1 else x) = (if p then 1 else y)
  trivial

example [Decidable p] (x y : Nat) (h : x = y) : True := by
  have := congr(if p then $h else 1)
  guard_hyp this :ₛ (if p then x else 1) = (if p then y else 1)
  trivial

example (x y z w : Nat) (h : x = y) (h' : z = w) : 1 + x * z^2 = 1 + y * w^2 := by
  refine congr(1 + $(?_) * $(?_)^2)
  · exact h
  · exact h'

example (x y z w : Nat) (h : x = y) (h' : z = w) : 1 + x * z^2 = 1 + y * w^2 := by
  refine congr(1 + $(?foo) * $(?bar)^2)
  case foo => exact h
  case bar => exact h'

example (p q : Prop) (h : p = q) : p ↔ q := congr($h)

example (p q : Prop) (h : p = q) : p ↔ q := by
  refine congr($(?_))
  guard_target = p ↔ q
  exact congr($h)

example (p p' q q' : Prop) (hp : p ↔ p') (hq : q ↔ q') : (p → q) ↔ (p' → q') :=
  congr($hp → $hq)

example (p q : Prop) (h : p = q) : Nonempty p = Nonempty q := congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p = Nonempty q := congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p ↔ Nonempty q := Iff.of_eq <| congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p ↔ Nonempty q := congr(Nonempty $h)

example (a b c d e f : Nat) (hab : a = b) (hcd : c = d) (hef : e = f) : True := by
  have := congr(1 + $hab + $hcd * $hef)
  guard_hyp this : 1 + a + c * e = 1 + b + d * f
  trivial

example (f g : Nat → Nat) (h : ∀ n, f n = g n) :
    (fun n => 1 + f n) = (fun n => 1 + g n) :=
  congr(fun n => 1 + $(h n))

example (f g : Nat → Nat) (h : ∀ n, f n = g n) :
    (fun n => 1 + f n) = (fun n => 1 + g n) := by
  refine congr(fun n => 1 + $(?_))
  guard_target = f n = g n
  apply h

structure Foo where
  (x y : Nat)

example (s : Foo) (h : 1 = 2) : True := by
  have := congr(({s with x := $h} : Foo))
  guard_hyp this : ({ x := 1, y := s.y } : Foo) = { x := 2, y := s.y }
  trivial

example {s t : α → Prop} (h : s = t) :
    (∀ (_ : Subtype s), True) ↔ (∀ (_ : Subtype t), True) :=
  congr(∀ (_ : Subtype $h), True)

example (f g : Nat → Nat → Prop) (h : f = g) :
    (∀ x, ∃ y, f x y) ↔ (∀ x, ∃ y, g x y) :=
  congr(∀ x, ∃ y, $h x y)

example (f g : Nat → Nat → Prop) (h : f = g) :
    (∀ x, ∃ y, f x y) ↔ (∀ x, ∃ y, g x y) :=
  congr(∀ _, ∃ _, $h _ _)

example (f g : Nat → Nat → Prop) (h : f = g) :
    (∀ x, ∃ y, f x y) ↔ (∀ x, ∃ y, g x y) :=
  congr(∀ _, ∃ _, $(by rw [h]))

namespace Overapplied
/-!
Overapplied functions need to be handled too. This one is for `Subtype.val`, which has arity 3,
but in examples (3) and (4) it's used with arity 4.
-/

def T1 (A : Nat → Type) := ∀ n, A n
def T2 (A : Nat → Type) := { f : ∀ n, A n // f = f }

example {A : Nat → Type} (f g : ∀ n, A n) (h : f = g) (n : Nat) : f n = g n := by
  have := congr($h n) -- (1) worked, not overapplied
  exact this

example {A : Nat → Type} (f g : T1 A) (h : f = g) (n : Nat) : f n = g n := by
  have := congr($h n) -- (2) worked, not overapplied
  exact this

example {A : Nat → Type} (f g : T2 A) (h : f = g) (n : Nat) : f.1 n = g.1 n := by
  have := congr($h.1 n) -- (3) didn't work, is overapplied
  exact this

example {A : Nat → Type} (f g : T2 A) (h : f = g) (n : Nat) : f.1 n = g.1 n := by
  have hh := congr($h.1) -- works
  have := congr($hh n) -- (4) didn't work, is overapplied
  exact this

/-!
A couple more over-applied functions.
-/
axiom fn {α : Type} (x : α) (h : x = x) : α

example (f g : Nat → Nat) (h : f = g) (m n : Nat) (h' : m = n) :
    fn f rfl m = fn g rfl n :=
  congr(fn $h _ $h')

example (f g : Nat → Nat) (h : f = g) (m n : Nat) (h' : m = n) :
    fn (fn f rfl) rfl m = fn (fn g rfl) rfl n :=
  congr(fn (fn $h _) _ $h')

end Overapplied

namespace SubsingletonDependence
/-!
The congruence theorem generator had a bug that leaked fvars.
Reported at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/what.20the.20heq.2C.20PosSemidef/near/434202080
-/

def f {α : Type} [DecidableEq α] (n : α) (_ : n = n) : α := n

lemma test (n n' : Nat) (h : n = n') (hn : n = n) (hn' : n' = n') :
    f n hn = f n' hn' := by
  have := congr(f $h ‹_›) -- without expected type
  guard_hyp this :ₛ f n hn = f n' hn'
  exact congr(f $h _) -- with expected type

/-!
Regression test for https://github.com/leanprover-community/mathlib4/issues/25851. Make sure hcongr doesn't force the final result to be an equality.
-/
example (a a' : Nat) (h : a = a') (n : Fin a) (n' : Fin a') (hn : HEq n n') :
    HEq (f n rfl) (f n' rfl) :=
  congr(f (α := Fin $h) $hn rfl)

end SubsingletonDependence

section limitations
/-! Tests to document current limitations. -/

/--
error: Cannot generate congruence because we need
  Subtype s
to be definitionally equal to
  Subtype t
-/
#guard_msgs in
example {s t : α → Prop} (h : s = t) :
    (fun (n : Subtype s) => true) ≍ (fun (n : Subtype t) => true) :=
  congr(fun (n : Subtype $h) => true)

/--
error: Cannot generate congruence because we need
  Subtype s
to be definitionally equal to
  Subtype t
-/
#guard_msgs in
example {s t : α → Prop} (h : s = t) (p : α → Prop) :
    (∀ (n : Subtype s), p n) ↔ (∀ (n : Subtype t), p n) :=
  congr(∀ (n : Subtype $h), p n)

end limitations

end Tests
