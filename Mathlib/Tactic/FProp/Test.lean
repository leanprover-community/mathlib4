-- import Mathlib.Tactic.FProp.FPropTheorems
import Mathlib.Tactic.FProp.Elab
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap

open Mathlib Meta FProp


variable {α β γ} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  {E : α → Type _} [∀ x, TopologicalSpace (E x)]


set_option trace.Meta.Tactic.fprop.attr true

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


set_option trace.Meta.Tactic.fprop.step true 

example : Cont (fun x : α => x) := by (try fprop); sorry
example (y : β) : Cont (fun x : α => y) := by (try fprop); sorry
example (x : α) : Cont (fun f : α → β => f x) := by (try fprop); sorry
example (x : α) : Cont (fun f : (x' : α) → E x' => f x) := by (try fprop); sorry
example (f : β → γ) (g : α → β) (hf : Cont f) (hg : Cont g) : Cont (fun x => f (g x)) := by (try fprop); sorry
example (f : α → β → γ) (g : α → β) (hf : Cont (fun (x,y) => f x y)) (hg : Cont g) : Cont (fun x => let y := g x; f x y) := by (try fprop); sorry
example {ι} (f : α → ι → γ) (hf : ∀ i, Cont (fun x => f x i)) : Cont (fun x i => f x i) := by (try fprop); sorry

