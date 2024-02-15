import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Core
import Mathlib.Tactic.FunTrans.Types

set_option trace.Meta.Tactic.fun_trans.attr true


variable {α β γ δ : Type _}

@[fun_trans]
opaque deriv {α β} (f : α → β) (x dx : α) : β := f x


@[fun_trans]
theorem deriv_id {α} : deriv (fun x : α => x) = fun x dx => dx := sorry

@[fun_trans]
theorem deriv_id_at {α} (x) : deriv (fun x : α => x) x = fun dx => dx := sorry

@[fun_trans]
theorem deriv_const {α β} [Zero β] (c : β)
  : deriv (fun _ : α => c) = fun x dx => 0 := sorry


@[fun_trans]
theorem deriv_comp {α β γ} (f : β → γ) (g : α → β)
  : deriv (fun x : α => f (g x)) = fun x dx => deriv f (g x) (deriv g x dx) := sorry


@[fun_trans]
theorem deriv_comp_at {α β γ} (f : β → γ) (g : α → β) (x : α)
  : deriv (fun x : α => f (g x)) x = fun dx => deriv f (g x) (deriv g x dx) := sorry


@[fun_trans]
theorem deriv_let {α β γ} (f : α → β → γ) (g : α → β) :
    deriv (fun x : α => let y := g x; f x y)
    =
    fun x dx =>
      let y := g x
      let dy := deriv g x dx
      deriv (fun (x,y) => f x y) (x,y) (dx, dy) := sorry

@[fun_trans]
theorem deriv_let_at {α β γ} (f : α → β → γ) (g : α → β) (x : α) :
    deriv (fun x : α => let y := g x; f x y) x
    =
    fun dx =>
      let y := g x
      let dy := deriv g x dx
      deriv (fun (x,y) => f x y) (x,y) (dx, dy) := sorry




@[fun_trans]
theorem deriv_prod_mk {α β} (f g : α → β) :
    deriv (fun x => (f x, g x))
    =
    fun x dx => (deriv f x dx, deriv g x dx) := sorry

@[fun_trans]
theorem deriv_prod_fst {α β γ} (f : α → β×γ) :
    deriv (fun x => (f x).1)
    =
    fun x dx => (deriv f x dx).1 := sorry

@[fun_trans]
theorem deriv_prod_snd {α β γ} (f : α → β×γ) :
    deriv (fun x => (f x).2)
    =
    fun x dx => (deriv f x dx).2 := sorry


@[fun_trans]
theorem deriv_add {α β} [Add β] (f g : α → β) :
    deriv (fun x => f x + g x)
    =
    fun x dx => deriv f x dx + deriv g x dx := sorry


@[fun_trans]
theorem deriv_add_at {α β} [Add β] (f g : α → β) (x : α) :
    deriv (fun x => f x + g x) x
    =
    fun dx => deriv f x dx + deriv g x dx := sorry


@[fun_trans]
theorem deriv_mul {α β} [Add β] [Mul β] (f g : α → β) :
    deriv (fun x => f x * g x)
    =
    fun x dx => deriv f x dx * g x + deriv g x dx * f x := sorry


-- @[fun_trans]
-- theorem deriv_mul_at {α β} [Add β] [Mul β] (f g : α → β) (x : α) :
--     deriv (fun x => f x * g x) x
--     =
--     fun dx => deriv f x dx * g x + deriv g x dx * f x := sorry



simproc_decl fun_trans (_) := Mathlib.Meta.FunTrans.funTransImpl

set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.unify true
set_option trace.Meta.Tactic.fun_trans.step true
set_option trace.Meta.Tactic.fun_trans.rewrite true
set_option trace.Meta.Tactic.fun_trans.discharge true

example : deriv (fun x : Nat => x) = fun x dx => dx := by
  conv =>
    lhs
    simp only [fun_trans]

example (x : Nat) : deriv (fun x : Nat => x) x = fun dx => dx := by
  conv =>
    lhs
    simp only [fun_trans]

example (x dx : Nat) : deriv (fun x : Nat => x) x dx = dx := by
  conv =>
    lhs
    simp only [fun_trans]


example (f : β → γ) (g : α → β) :
    deriv (fun x : α => f (g x)) = fun x dx => deriv f (g x) (deriv g x dx) := by

  conv =>
    lhs
    simp only [fun_trans]


example (f : β → γ) (g : α → β) (x) :
    deriv (fun x : α => f (g x)) x = fun dx => deriv f (g x) (deriv g x dx) := by

  conv =>
    lhs
    simp only [fun_trans]


example (f : β → γ) (g : α → β) (x dx) :
    deriv (fun x : α => f (g x)) x dx = deriv f (g x) (deriv g x dx) := by

  conv =>
    lhs
    simp only [fun_trans]



example [Add α] [Mul α] :
    deriv (fun x : α => let y1 := x * x; let y2 := x * y1; let y3 := x * y2; x * y3 )
    =
    fun x dx ↦ dx * (x * (x * (x * x))) + (dx * (x * (x * x)) + (dx * (x * x) + (dx * x + dx * x) * x) * x) * x := by

  conv =>
    lhs
    simp only [fun_trans]


example [Add α] [Mul α] :
    deriv (fun x : α => let y1 := x * x; let y2 := x * y1; let y3 := x * y2; x * y3 )
    =
    fun x dx ↦
        let y := x * x;
        let dy := dx * x + dx * x;
        let y_1 := x * y;
        let dy := dx * y + dy * x;
        let y := x * y_1;
        let dy := dx * y_1 + dy * x;
        dx * y + dy * x := by

  conv =>
    lhs
    simp (config := {zeta:=false}) only [fun_trans]


example (f : α → α → α) :
    deriv (fun x : α => let y1 := f x x; let y2 := f x y1; let y3 := f x y2; f x y3 )
    =
    fun x dx ↦
        let y := f x x;
        let dy := deriv (fun x0x1 ↦ f x0x1.fst x0x1.snd) (x, x) (dx, dx);
        let y_1 := f x y;
        let dy := deriv (fun x0x1 ↦ f x0x1.fst x0x1.snd) (x, y) (dx, dy);
        let y := f x y_1;
        let dy := deriv (fun x0x1 ↦ f x0x1.fst x0x1.snd) (x, y_1) (dx, dy);
        deriv (fun x0x1 ↦ f x0x1.fst x0x1.snd) (x, y) (dx, dy) := by

  conv =>
    lhs
    simp (config := {zeta:=false}) only [fun_trans]
