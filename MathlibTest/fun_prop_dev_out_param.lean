/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FunProp
import Mathlib.Logic.Function.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Tactic.SuccessIfFailWithMsg
import Aesop

/-! # Tests for the `fun_prop` tactic

This file is designed for development of fun_prop and its new ability to have output parameters.
-/


set_option linter.style.longLine false

open Function

variable {α β γ δ ι : Type*} {E : α → Type*}

axiom silentSorry {α} : α
set_option linter.unusedVariables false

-- define function propositions --
----------------------------------

@[fun_prop] opaque HasDeriv {α β} (f : α → β) (f' : α → α → β) : Prop


@[fun_prop]
theorem had_deriv_id : HasDeriv (fun x : α => x) (fun x dx => dx) := silentSorry
@[fun_prop]
theorem had_deriv_const [Zero β] (y : β) : HasDeriv (fun x : α => y) (fun x dx => 0) := silentSorry
@[fun_prop]
theorem had_deriv_comp (f : β → γ) (g : α → β) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => f (g x)) (fun x dx => f' (g x) (g' x dx)) := silentSorry
@[fun_prop]
theorem had_deriv_apply (x : α) : HasDeriv (fun f : α → β => f x) (fun f df => df x) := silentSorry

-- For dependent pi-types
@[fun_prop]
theorem had_deriv_pi (f : β → (i : α) → E i) {f' : (i : α) → β → β → E i} (hf : ∀ i, HasDeriv (f · i) (f' i)) :
    HasDeriv f (fun y dy i => f' i y dy) := silentSorry

-- For non-dependent pi-types (regular curried functions)
@[fun_prop]
theorem had_deriv_pi_nodep (f : β → α → γ) {f' : α → β → β → γ} (hf : ∀ i, HasDeriv (f · i) (f' i)) :
    HasDeriv f (fun y dy i => f' i y dy) := silentSorry


@[fun_prop]
theorem has_deriv_prod_mk (f : α → β) (g : α → γ) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => (f x, g x)) (fun x dx => (f' x dx, g' x dx)) := silentSorry
@[fun_prop]
theorem has_deriv_fst (f : α → β×γ) {f'} (hf : HasDeriv f f') : HasDeriv (fun x => (f x).1) (fun x dx => (f' x dx).1) := silentSorry
@[fun_prop]
theorem has_deriv_snd (f : α → β×γ) {f'} (hf : HasDeriv f f') : HasDeriv (fun x => (f x).2) (fun x dx => (f' x dx).2) := silentSorry



variable
  (f : β → γ) {f'} (hf : HasDeriv f f')
  (g : α → β) {g'} (hg : HasDeriv g g')
  (h : α → α) {h'} (hh : HasDeriv h h')

set_option pp.proofs false

theorem prove_has_deriv (f : α → β) {f' f''} (deriv : HasDeriv f f'') (eq : f' = f'') : HasDeriv f f' := by rw[eq]; apply deriv

-- Basic tests with section variables
example : HasDeriv (fun x : α => x) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun x : α => g x) g' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun x : α => f (g x)) (fun x dx => f' (g x) (g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun x : α => h (h (h (h x)))) (fun x dx => h' (h (h (h x))) (h' (h (h x)) (h' (h x) (h' x dx)))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl


----------------------------------------------------------------------------------------------------
-- Extended tests adapted from fun_prop_dev.lean
----------------------------------------------------------------------------------------------------

-- Basic lambda calculus tests
example : HasDeriv (fun x : α => x) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example [Zero β] (y : β) : HasDeriv (fun _ : α => y) (fun x dx => 0) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (x : α) : HasDeriv (fun f : α → β => f x) (fun f df => df x) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (x : α) (y : β) : HasDeriv (fun f : α → β → γ => f x y) (fun f df => df x y) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Composition tests
example (f : β → γ) (g : α → β) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => f (g x)) (fun x dx => f' (g x) (g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) (g : α → β) {f' g'} (hf : HasDeriv (fun (x,y) => f x y) f') (hg : HasDeriv g g') :
    HasDeriv (fun x => f x (g x)) (fun x dx => f' (x, g x) (dx, g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) (g : α → β) {f' g'} (hf : HasDeriv (fun (x,y) => f x y) f') (hg : HasDeriv g g') :
    HasDeriv (fun x => let y := g x; f x y) (fun x dx => f' (x, g x) (dx, g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Pi type tests
example {ι : Type*} (f : α → ι → γ) {f' : ι → _} (hf : ∀ i, HasDeriv (fun x => f x i) (f' i)) :
    HasDeriv (fun x i => f x i) (fun y dy i => f' i y dy) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Tests with function application patterns
example : HasDeriv (fun (f : α → β → γ) x y => f x y) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun (f : α → β → γ) y x => f x y) (fun y dy i i_1 => dy i_1 i) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun (f : α → α → α → α → α) y x => f x y x y) (fun y dy i i_1 => dy i_1 i i_1 i) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Tests with local hypotheses in various forms
example (f : α → β → γ) {f'} (hf : HasDeriv f f') : HasDeriv f f' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv f f') : HasDeriv (fun x => f x) f' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv f f') : HasDeriv (fun x y => f x y) f' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv f f') (y) : HasDeriv (fun x => f x y) (fun x dx => f' x dx y) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

variable [Zero α] [Zero β] [Zero γ]

example (f : α → β → γ) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') (x) : HasDeriv (fun y => f x y) (fun x_1 dx => f' (x, x_1) (0, dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') (y) : HasDeriv (fun x => f x y) (fun x dx => f' (x, y) (dx, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv f (fun y dy i => f' (y, i) (dy, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv ↿f f') (x : α) : HasDeriv (fun y => f x y) (fun x_1 dx => f' (x, x_1) (0, dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv ↿f f') (y : β) : HasDeriv (fun x => f x y) (fun x dx => f' (x, y) (dx, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv ↿f f') : HasDeriv f (fun y dy i => f' (y, i) (dy, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f' : α → _} (hf : ∀ x, HasDeriv (fun y => f x y) (f' x)) (x) : HasDeriv (fun y => f x y) (f' x) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f' : α → _} (hf : ∀ x, HasDeriv (fun y => f x y) (f' x)) (x) : HasDeriv (f x) (f' x) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f' : β → _} (hf : ∀ y, HasDeriv (fun x => f x y) (f' y)) (y) : HasDeriv (fun x => f x y) (f' y) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f' : β → _} (hf : ∀ y, HasDeriv (fun x => f x y) (f' y)) : HasDeriv (fun x => f x) (fun y dy i => f' i y dy) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') (y) : HasDeriv (fun x => f x y) (fun x dx => f' (x, y) (dx, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv f (fun y dy i => f' (y, i) (dy, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → α → β) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv (fun x => f x x) (fun x dx => f' (x, x) (dx, dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ → δ) {f' : α → _} (hf : ∀ x, HasDeriv (fun (y,z) => f x y z) (f' x)) (x y) : HasDeriv (fun z => f x y z) (fun z dz => f' x (y, z) (0, dz)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ → δ) {f' : α → _} (hf : ∀ x, HasDeriv (fun (y,z) => f x y z) (f' x)) (x) : HasDeriv (fun z y => f x y z) (fun z dz y => f' x (y, z) (0, dz)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ → δ) {f' : α → _} (hf : ∀ x, HasDeriv (fun yz : β×γ => f x yz.1 yz.2) (f' x)) (x y) : HasDeriv (f x y) (fun z dz => f' x (y,z) (0, dz)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ → δ) {f' : α → _} (hf : ∀ x, HasDeriv (fun (y,z) => f x y z) (f' x)) (x) : HasDeriv (fun y => f x y) (fun y dy z => f' x (y,z) (dy,0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → Nat → Nat → β) {f' : Nat → Nat → _} (hf : ∀ i j, HasDeriv (f · i j) (f' i j)) : HasDeriv (fun x i j => f x (i+j) j) (fun x dx i j => f' (i + j) j x dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → Nat → Nat → β) {f' : Nat → Nat → _} (hf : ∀ i j, HasDeriv (f · i j) (f' i j)) (i j) : HasDeriv (fun x => f x (i+j) j) (fun x dx => f' (i + j) j x dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → Nat → Nat → β) {f'} (hf : HasDeriv f f') : HasDeriv (fun x i j => f x (i+j) j) (fun x dx i j => f' x dx (i + j) j) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → Nat → Nat → β) {f'} (hf : HasDeriv f f') (i j) : HasDeriv (fun x => f x (i+j) j) (fun x dx => f' x dx (i + j) j) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β → γ → δ) {f' : β → _} (hf : ∀ y, HasDeriv (fun (x,z) => f x y z) (f' y)) : HasDeriv f (fun x dx y z => f' y (x, z) (dx, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Tests with let expressions
example : let f := fun x : α => x; HasDeriv f (fun x dx => dx) := by
  intro _
  apply prove_has_deriv
  · fun_prop
  · rfl

example (x : α) : let f := fun x' : α => x'; HasDeriv (fun x' => f x') (fun x' dx' => dx') := by
  intro _
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Unfolding tests with id
example (f : α → β) {f'} (hf : HasDeriv f f') : HasDeriv (fun x => id f x) (fun x dx => f' (id x) dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β) {f'} (hf : HasDeriv f f') : HasDeriv (fun x => (id id) f x) (fun x dx => f' ((id id) x) dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → α → α) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv (fun x => id (id f x) x) (fun x dx => f' (x,x) (dx,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → α → α) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv (fun x => (id id) ((id id) f x) x) (fun x dx => f' (x,x) (dx,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → α → α) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') : HasDeriv (fun x : α×α => id (f x.1) x.2) (fun x dx => f' (x.1, x.2) (dx.1, dx.2)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Tests with pattern matching
example : HasDeriv (fun ((x, _, _) : α × α × α) => x) (fun x dx => dx.1) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun ((_, x, _) : α × α × α) => x) (fun x dx => dx.2.1) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example : HasDeriv (fun ((_, _, x) : α × α × α) => x) (fun x dx => dx.2.2) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Abbrev transparency test
abbrev my_id {α} (a : α) := a

example : HasDeriv (fun x : α => my_id x) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → β) {f'} (hf : HasDeriv (my_id f) f') : HasDeriv f f' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Test improved beta reduction with interleaved lambdas and lets
example (a : α) : HasDeriv (fun x0 : α =>
  (fun x =>
    let y := x
    fun z : α =>
      z) x0 a) (fun x0 dx0 => 0) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (a : α) :
  let f := (fun x : α =>
    let y := x
    fun z : α =>
      x)
  HasDeriv (fun x => f x a) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (a a' : α) : HasDeriv (fun x0 : α =>
  (fun x =>
    let y := x
    fun z : α =>
      let h := z
      fun w =>
        w) x0 a a') (fun x0 dx0 => 0) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- test that local function is being properly unfolded
example (a : α) :
  let f := (fun x : α =>
    let y := x
    fun z : α =>
      x)
  HasDeriv (fun x =>
    f x a) (fun x dx => dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl


-- Tests with Nat indices
example (f : α → Nat → β) {f' : Nat → _} (hf : ∀ i, HasDeriv (f · i) (f' i)) (i : Nat) :
    HasDeriv (fun x => f x i) (f' i) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α → Nat → Nat → β) {f' : Nat → Nat → _} (hf : ∀ i j, HasDeriv (f · i j) (f' i j)) (i j : Nat) :
    HasDeriv (fun x => f x i j) (f' i j) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

----------------------------------------------------------------------------------------------------
-- Additional comprehensive tests for output parameters
----------------------------------------------------------------------------------------------------

-- 1. More Product Type Operations
----------------------------------------------------------------------------------------------------

-- Product swapping
example (f : α × β → γ) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun (x,y) => f (y,x)) (fun (x,y) (dx,dy) => f' (y,x) (dy,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Diagonal/duplication
example (f : α × α → β) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => f (x,x)) (fun x dx => f' (x,x) (dx,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Nested products - association
example (f : α × (β × γ) → δ) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun ((x,y),z) => f (x,(y,z))) (fun ((x,y),z) ((dx,dy),dz) => f' (x,(y,z)) (dx,(dy,dz))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Product with const in different positions
example (f : α × β → γ) (b : β) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => f (x,b)) (fun x dx => f' (x,b) (dx,0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

example (f : α × β → γ) (a : α) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun y => f (a,y)) (fun y dy => f' (a,y) (0,dy)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 2. Unit Type Tests
----------------------------------------------------------------------------------------------------

-- Functions from Unit
example [Zero β] (y : β) : HasDeriv (fun (_ : Unit) => y) (fun _ _ => 0) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Product with Unit
example (f : α → β) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun p : α × Unit => f p.1) (fun p dp => f' p.1 dp.1) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 3. Multiple Uses of Same Argument
----------------------------------------------------------------------------------------------------

-- Tuple of applications
example (f g : α → β) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => (f x, g x)) (fun x dx => (f' x dx, g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Same function applied multiple times with different arguments
example (f : α → β → γ) (g h : α → β) {f' g' h'} (hf : HasDeriv (fun (x,y) => f x y) f')
    (hg : HasDeriv g g') (hh : HasDeriv h h') :
    HasDeriv (fun x => (f x (g x), f x (h x)))
             (fun x dx => (f' (x, g x) (dx, g' x dx), f' (x, h x) (dx, h' x dx))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Argument used multiple times in nested way
example (f : α → α → α) {f'} (hf : HasDeriv (fun (x,y) => f x y) f') :
    HasDeriv (fun x => f x (f x x)) (fun x dx => f' (x, f x x) (dx, f' (x, x) (dx, dx))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 4. Higher-Order Function Patterns
----------------------------------------------------------------------------------------------------

-- Function composition as operator
example (f : β → γ) (g : α → β) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => (f ∘ g) x) (fun x dx => f' (g x) (g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Constant function factory
example (y : β) : HasDeriv (fun (_ : α) => fun (_ : γ) => y) (fun _ _ => fun _ => 0) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Flip function
example (f : α → β → γ) {f'} (hf : HasDeriv (↿f) f') :
    HasDeriv (fun y x => f x y) (fun y dy x => f' (x,y) (0,dy)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 5. Dependent Type Patterns
----------------------------------------------------------------------------------------------------

-- Dependent function with fixed index
example {ι : Type*} {F : ι → Type*} (f : (i : ι) → α → F i) (i : ι) {f'} (hf : HasDeriv (f i) f') :
    HasDeriv (f i) f' := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 6. Complex Let Binding Patterns
----------------------------------------------------------------------------------------------------

-- Multiple let bindings
example (f : α → β → γ) (g : α → β) {f' g'} (hf : HasDeriv (fun (x,y) => f x y) f') (hg : HasDeriv g g') :
    HasDeriv (fun x => let y := g x; let z := f x y; z)
             (fun x dx => f' (x, g x) (dx, g' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 7. Symmetry and Permutation Tests
----------------------------------------------------------------------------------------------------

-- Symmetric function
example (f : α → α → β) {f'} (hf : HasDeriv (fun (x,y) => f x y) f')
    (sym : ∀ x y, f x y = f y x) :
    HasDeriv (fun (x,y) => f y x) (fun (x,y) (dx,dy) => f' (y,x) (dy,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Triple permutation
example (f : α → β → γ → δ) {f'} (hf : HasDeriv (fun (x,y,z) => f x y z) f') :
    HasDeriv (fun ((z,x),y) => f x y z) (fun ((z,x),y) ((dz,dx),dy) => f' (x,y,z) (dx,dy,dz)) := by
  apply prove_has_deriv
  · simp; fun_prop
  · rfl

-- 8. Edge Cases
----------------------------------------------------------------------------------------------------

-- Unused arguments at different positions
example (f : α → γ) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun (x : α) (_y : β) => f x) (fun x dx _ => f' x dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Constant in composition
example (f : α → β) (c : γ) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => (f x, c)) (fun x dx => (f' x dx, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Projection after construction
example (f : α → β) (g : α → γ) {f' g'} (hf : HasDeriv f f') (hg : HasDeriv g g') :
    HasDeriv (fun x => (f x, g x).1) (fun x dx => f' x dx) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 9. Realistic Mathematical Patterns
----------------------------------------------------------------------------------------------------

-- Bilinear-style map
example (f : α → β → γ → δ) {f'} (hf : HasDeriv (↿f) f')
    (g₁ : α → α) (g₂ : α → β) (h : α → γ) {g₁' g₂' h'}
    (hg₁ : HasDeriv g₁ g₁') (hg₂ : HasDeriv g₂ g₂') (hh : HasDeriv h h') :
    HasDeriv (fun x => f (g₁ x) (g₂ x) (h x))
             (fun x dx => f' (g₁ x, g₂ x, h x) (g₁' x dx, g₂' x dx, h' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Quadratic-like: x ↦ f(x,x)
example (f : α × α → β) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => f (x,x)) (fun x dx => f' (x,x) (dx,dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 10. More Composition Tests
----------------------------------------------------------------------------------------------------

-- Triple composition
example (f : γ → δ) (g : β → γ) (h : α → β) {f' g' h'}
    (hf : HasDeriv f f') (hg : HasDeriv g g') (hh : HasDeriv h h') :
    HasDeriv (fun x => f (g (h x))) (fun x dx => f' (g (h x)) (g' (h x) (h' x dx))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Composition with product
example (f : β × γ → δ) (g : α → β) (h : α → γ) {f' g' h'}
    (hf : HasDeriv f f') (hg : HasDeriv g g') (hh : HasDeriv h h') :
    HasDeriv (fun x => f (g x, h x)) (fun x dx => f' (g x, h x) (g' x dx, h' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 11. Swap and Curry Tests
----------------------------------------------------------------------------------------------------

-- Swap both input and arguments
example (f : α → β → γ) {f'} (hf : HasDeriv (↿f) f') :
    HasDeriv (fun (y,x) => f x y) (fun (y,x) (dy,dx) => f' (x,y) (dx, dy)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Uncurry
example (f : α → β → γ) {f'} (hf : HasDeriv (↿f) f') :
    HasDeriv (fun (x,y) => f x y) (fun (x,y) (dx,dy) => f' (x,y) (dx,dy)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 12. Nested Tuples
----------------------------------------------------------------------------------------------------

-- Deep nesting
example (f : (α × β) × (γ × δ) → ι) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun ((a,b),(c,d)) => f ((a,b),(c,d)))
             (fun ((a,b),(c,d)) ((da,db),(dc,dd)) => f' ((a,b),(c,d)) ((da,db),(dc,dd))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Projection from nested
example : HasDeriv (fun (((x,_),_) : (α × β) × γ) => x) (fun x dx => dx.1.1) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 13. Constant Propagation Tests
----------------------------------------------------------------------------------------------------

-- Constant in first position of pair
example [Zero α] (b : α) (f : β → γ) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun y => (b, f y)) (fun y dy => (0, f' y dy)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

instance : Zero (α × β) := ⟨0,0⟩

-- Multiple constants
example (b : β) (c : γ) :
    HasDeriv (fun (_ : α) => (b, c)) (fun _ _ => (0, 0)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 14. Self-Application Patterns
----------------------------------------------------------------------------------------------------

-- Function applied to itself
example (f : α → α) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => f (f x)) (fun x dx => f' (f x) (f' x dx)) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Double self-application
example (f : α → α) {f'} (hf : HasDeriv f f') :
    HasDeriv (fun x => f (f (f x))) (fun x dx => f' (f (f x)) (f' (f x) (f' x dx))) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- 15. Mixed Currying Tests
----------------------------------------------------------------------------------------------------

-- Partial application with different orders
example (f : α → β → γ → δ) {f'} (hf : HasDeriv f f') (b : β) :
    HasDeriv (fun x z => f x b z) (fun x dx z => f' x dx b z) := by
  apply prove_has_deriv
  · fun_prop
  · rfl

-- Multiple partial applications
example (f : α → β → γ → δ → ι) {f'} (hf : HasDeriv f f') (b : β) (d : δ) :
    HasDeriv (fun x z => f x b z d) (fun x dx z => f' x dx b z d) := by
  apply prove_has_deriv
  · fun_prop
  · rfl


-- 16. Arithmetics
----------------------------------------------------------------------------------------------------

section

variable
  [Add α] [Sub α] [Mul α] [Div α]
  (f : α → α) {f' : α → α → α} (hf : HasDeriv f f')
  (g : α → α) {g' : α → α → α} (hg : HasDeriv g g')

omit [Add α] in
@[fun_prop]
theorem has_deriv_div (hf : HasDeriv f f') (hg : HasDeriv g g') (hg' : ∀ x, g x ≠ 0) :
    HasDeriv (fun x => f x / g x)
      (fun x dx => (f' x dx * g x - f x * g' x dx) / ((g x)*(g x))) := silentSorry

set_option linter.unusedVariables false

-- intentionally incorrect theorem to confuse `fun_prop`
-- If not handled correctly, fun_prop will fill `?f'` with `fun x dx => dx` and thus it
-- then fails applying `has_deriv_div` after application `has_deriv_div_false` fails
omit [Zero α] [Add α] [Sub α] [Mul α] in
@[fun_prop]
theorem has_deriv_div_false (h : False) :
    HasDeriv (fun x => f x / g x)
      (fun x dx => dx) := silentSorry

example (hg' : ∀ x, g x ≠ 0) :
    HasDeriv (fun x => f x / g x)
      (fun x dx => (f' x dx * g x - f x * g' x dx) / ((g x)*(g x))) := by
  apply prove_has_deriv
  · fun_prop (disch:=assumption)
  · rfl

end
