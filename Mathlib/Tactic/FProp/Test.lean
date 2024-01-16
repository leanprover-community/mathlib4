import Mathlib.Tactic.FProp.Elab
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap

open Mathlib Meta FProp


variable {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  {E : α → Type _} [∀ x, TopologicalSpace (E x)]


-- set_option trace.Meta.Tactic.fprop.attr true


@[fprop]
def Cont (f : α → β) : Prop := Continuous f


-- @[fprop (discharger := first | assumption | positivity | omega)] 
@[fprop] 
def ContAt (f : α → β) (x : α) := ContinuousAt f x


@[fprop]
theorem Cont_id : Cont (fun x : α => x) := 
by
  unfold Cont
  continuity

@[fprop]
theorem Cont_const (y : β) : Cont (fun x : α => y) := 
by
  unfold Cont
  continuity


@[fprop]
theorem Cont_proj (x : α) : Cont (fun f : α → β => f x) := 
by
  unfold Cont
  continuity


@[fprop]
theorem Cont_projDep (x : α) : Cont (fun f : (x' : α) → E x' => f x) := 
by
  unfold Cont
  continuity
 

@[fprop]
theorem Cont_comp (f : β → γ) (g : α → β) (hf : Cont f) (hg : Cont g) : Cont (fun x => f (g x)) := 
by
  unfold Cont
  continuity


@[fprop]
theorem Cont_let (f : α → β → γ) (g : α → β) (hf : Cont (fun (x,y) => f x y)) (hg : Cont g) : Cont (fun x => let y := g x; f x y) := 
by
  unfold Cont
  sorry

-- @[fprop]
-- theorem Cont_let' (f : α → β → γ) (g : α → β) (hf : Cont (fun (x,y) => f x y)) (hg : Cont g) : Cont (fun x => f x (g x)) := 
-- by
--   unfold Cont
--   sorry

@[fprop]
theorem Cont_pi {ι} (f : α → ι → γ) (hf : ∀ i, Cont (fun x => f x i)) : Cont (fun x i => f x i) := 
by
  unfold Cont
  continuity


variable {X} [NormedAddCommGroup X] 


@[fprop]
theorem add_Cont_in_xy (x y : α → X) (hx : Cont x) (hy : Cont y) : Cont (fun w => x w + y w) := 
by
  unfold Cont
  continuity


@[fprop]
theorem add_Cont_in_y_simple (c : X) : Cont (fun x : X => c + x) := 
by
  unfold Cont
  continuity


@[fprop]
theorem add_Cont_in_x_simple (c : X) : Cont (fun x : X => x + c) := 
by
  unfold Cont
  continuity


@[fprop]
theorem Cont_Prod_mk (fst : α → β) (snd : α → γ) (hfst : Cont fst) (hsnd : Cont snd) 
  : Cont fun x => (fst x, snd x) := by unfold Cont; continuity

@[fprop]
theorem Cont_fst (self : α → β×γ) (hself : Cont self) 
  : Cont fun x => (self x).1 := by unfold Cont; continuity

@[fprop]
theorem Cont_snd (self : α → β×γ) (hself : Cont self) 
  : Cont fun x => (self x).2 := by unfold Cont; continuity



set_option profiler true 
set_option profiler.threshold 10

example : Cont (fun x : α => x) := by fprop
example (y : β) : Cont (fun _ : α => y) := by fprop
example (x : α) : Cont (fun f : α → β => f x) := by (try fprop); sorry
example (x : α) : Cont (fun f : (x' : α) → E x' => f x) := by (try fprop); sorry
example (f : β → γ) (g : α → β) (hf : Cont f) (hg : Cont g) : Cont (fun x => f (g x)) := by fprop
example (f : α → β → γ) (g : α → β) (hf : Cont (fun (x,y) => f x y)) (hg : Cont g) : Cont (fun x => f x (g x)) := by fprop
example (f : α → β → γ) (g : α → β) (hf : Cont (fun (x,y) => f x y)) (hg : Cont g) : Cont (fun x => let y := g x; f x y) := by fprop
example {ι} (f : α → ι → γ) (hf : ∀ i, Cont (fun x => f x i)) : Cont (fun x i => f x i) := by fprop

-- set_option trace.Meta.Tactic.fprop.step true 
-- set_option trace.Meta.Tactic.fprop.cache true 
-- set_option trace.Meta.Tactic.fprop.unify true 
-- set_option trace.Meta.Tactic.fprop.discharge true 
-- set_option trace.Meta.Tactic.fprop.apply true 
-- set_option trace.Meta.isDefEq true in
example (x y : α → ℝ) (hx : Cont x) (hy : Cont y) : Cont (fun w => x w + y w) := by fprop

example (c : X) : Cont (fun x : X => c + x) := by fprop
example (c : X) : Cont (fun x : X => x + c) := by fprop


example : Cont (fun x : X => 
  let x₁ := x + x
  x₁) := by fprop

example : Cont (fun x : X => 
  let x₁ := x + x
  let x₂ := x₁ + x₁ + x
  x₂) := by fprop

example : Cont (fun x : X => 
  let x₁ := x + x
  let x₂ := x₁ + x₁ + x
  let x₃ := x₂ + x₂ + x
  x₃) := by fprop

example : Cont (fun x : X => 
  let x₁ := x + x
  let x₂ := x₁ + x₁ + x
  let x₃ := x₂ + x₂ + x
  let x₄ := x₃ + x₃ + x
  x₄) := by fprop

example : Cont (fun x : X => 
  let x₁ := x + x
  let x₂ := x₁ + x₁ + x
  let x₃ := x₂ + x₂ + x
  let x₄ := x₃ + x₃ + x
  let x₅ := x₄ + x₄ + x
  x₅) := by fprop


example : Cont (fun x : X => 
  let x₁ := x + x
  x₁) := by fprop

example : Cont (fun x : X => 
  let x₁ := x
  let x₂ := x₁ + x
  x₂) := by fprop

example : Cont (fun x : X => 
  let x₁ := x
  let x₂ := x₁ + x
  let x₃ := x₂ + x₁ + x
  x₃) := by fprop

example : Cont (fun x : X => 
  let x₁ := x
  let x₂ := x₁ + x
  let x₃ := x₂ + x₁ + x
  let x₄ := x₃ + x₂ + x₁ + x
  x₄) := by fprop

example : Cont (fun x : X => 
  let x₁ := x
  let x₂ := x₁ + x
  let x₃ := x₂ + x₁ + x
  let x₄ := x₃ + x₂ + x₁ + x
  let x₅ := x₄ + x₃ + x₂ + x₁ + x
  x₅) := by fprop
