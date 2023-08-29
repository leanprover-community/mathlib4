/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import Mathlib.Data.Part
import Mathlib.Data.Rel

#align_import data.pfun from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → Part β`.

## Definitions

* `PFun α β`: Type of partial functions from `α` to `β`. Defined as `α → Part β` and denoted
  `α →. β`.
* `PFun.Dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `PFun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `Dom`.
* `PFun.asSubtype`: Returns a partial function as a function from its `Dom`.
* `PFun.toSubtype`: Restricts the codomain of a function to a subtype.
* `PFun.evalOpt`: Returns a partial function with a decidable `Dom` as a function `a → Option β`.
* `PFun.lift`: Turns a function into a partial function.
* `PFun.id`: The identity as a partial function.
* `PFun.comp`: Composition of partial functions.
* `PFun.restrict`: Restriction of a partial function to a smaller `Dom`.
* `PFun.res`: Turns a function into a partial function with a prescribed domain.
* `PFun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `PFun.fix_induction`: A recursion principle for `PFun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `Rel` definitions to `PFun`:
* `PFun.image`: Image of a set under a partial function.
* `PFun.ran`: Range of a partial function.
* `PFun.preimage`: Preimage of a set under a partial function.
* `PFun.core`: Core of a set under a partial function.
* `PFun.graph`: Graph of a partial function `a →. β`as a `Set (α × β)`.
* `PFun.graph'`: Graph of a partial function `a →. β`as a `Rel α β`.

### `PFun α` as a monad

Monad operations:
* `PFun.pure`: The monad `pure` function, the constant `x` function.
* `PFun.bind`: The monad `bind` function, pointwise `Part.bind`
* `PFun.map`: The monad `map` function, pointwise `Part.map`.
-/


open Function

/-- `PFun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → Part β`. -/
def PFun (α β : Type*) :=
  α → Part β
#align pfun PFun

/-- `α →. β` is notation for the type `PFun α β` of partial functions from `α` to `β`.  -/
infixr:25 " →. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type*}

instance inhabited : Inhabited (α →. β) :=
  ⟨fun _ => Part.none⟩
#align pfun.inhabited PFun.inhabited

/-- The domain of a partial function -/
def Dom (f : α →. β) : Set α :=
  { a | (f a).Dom }
#align pfun.dom PFun.Dom

@[simp]
theorem mem_dom (f : α →. β) (x : α) : x ∈ Dom f ↔ ∃ y, y ∈ f x := by simp [Dom, Part.dom_iff_mem]
                                                                      -- 🎉 no goals
#align pfun.mem_dom PFun.mem_dom

@[simp]
theorem dom_mk (p : α → Prop) (f : ∀ a, p a → β) : (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl
#align pfun.dom_mk PFun.dom_mk

theorem dom_eq (f : α →. β) : Dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)
#align pfun.dom_eq PFun.dom_eq

/-- Evaluate a partial function -/
def fn (f : α →. β) (a : α) : Dom f a → β :=
  (f a).get
#align pfun.fn PFun.fn

@[simp]
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl
#align pfun.fn_apply PFun.fn_apply

/-- Evaluate a partial function to return an `Option` -/
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)
#align pfun.eval_opt PFun.evalOpt

/-- Partial function extensionality -/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)
#align pfun.ext' PFun.ext'

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)
#align pfun.ext PFun.ext

/-- Turns a partial function into a function out of its domain. -/
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2
#align pfun.as_subtype PFun.asSubtype

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : Subtype p → β)`. -/
def equivSubtype : (α →. β) ≃ Σp : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun f =>
    funext fun a => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr ⟩
                                                 -- ⊢ { fst := fun a => p a, snd := asSubtype fun x => { Dom := p x, get := fun h  …
                                                        -- 🎉 no goals
#align pfun.equiv_subtype PFun.equivSubtype

theorem asSubtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy
#align pfun.as_subtype_eq_of_mem PFun.asSubtype_eq_of_mem

/-- Turn a total function into a partial function. -/
@[coe]
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)
#align pfun.lift PFun.lift

instance coe : Coe (α → β) (α →. β) :=
  ⟨PFun.lift⟩
#align pfun.has_coe PFun.coe

@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl
#align pfun.coe_val PFun.coe_val

@[simp]
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.univ :=
  rfl
#align pfun.dom_coe PFun.dom_coe

theorem lift_injective : Injective (PFun.lift : (α → β) → α →. β) := fun _ _ h =>
  funext fun a => Part.some_injective <| congr_fun h a
#align pfun.coe_injective PFun.lift_injective

/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
def graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }
#align pfun.graph PFun.graph

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def graph' (f : α →. β) : Rel α β := fun x y => y ∈ f x
#align pfun.graph' PFun.graph'

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }
#align pfun.ran PFun.ran

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
  (f x).restrict (x ∈ p) (@H x)
#align pfun.restrict PFun.restrict

@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) :
    b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a := by simp [restrict]
                                               -- 🎉 no goals
#align pfun.mem_restrict PFun.mem_restrict

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (PFun.lift f).restrict s.subset_univ
#align pfun.res PFun.res

theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [res, @eq_comm _ b]
  -- 🎉 no goals
#align pfun.mem_res PFun.mem_res

theorem res_univ (f : α → β) : PFun.res f Set.univ = f :=
  rfl
#align pfun.res_univ PFun.res_univ

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem
#align pfun.dom_iff_graph PFun.dom_iff_graph

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
  show (∃ _ : True, f a = b) ↔ f a = b by simp
                                          -- 🎉 no goals
#align pfun.lift_graph PFun.lift_graph

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := fun _ => Part.some x
#align pfun.pure PFun.pure

/-- The monad `bind` function, pointwise `Part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a
#align pfun.bind PFun.bind

@[simp]
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl
#align pfun.bind_apply PFun.bind_apply

/-- The monad `map` function, pointwise `Part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f
#align pfun.map PFun.map

instance monad : Monad (PFun α) where
  pure := PFun.pure
  bind := PFun.bind
  map := PFun.map
#align pfun.monad PFun.monad

instance lawfulMonad : LawfulMonad (PFun α) := LawfulMonad.mk'
  (bind_pure_comp := fun f x => funext fun a => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
                         -- ⊢ (id <$> f) a = f a
                                   -- ⊢ Part.map id (f a) = f a
                                                                  -- ⊢ Part.map id { Dom := Dom✝, get := get✝ } = { Dom := Dom✝, get := get✝ }
                                                                             -- 🎉 no goals
  (pure_bind := fun x f => funext fun a => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)
#align pfun.is_lawful_monad PFun.lawfulMonad

theorem pure_defined (p : Set α) (x : β) : p ⊆ (@PFun.pure α _ x).Dom :=
  p.subset_univ
#align pfun.pure_defined PFun.pure_defined

theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom)
    (H2 : ∀ x, p ⊆ (g x).Dom) : p ⊆ (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)
#align pfun.bind_defined PFun.bind_defined

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. Sum β α) : α →. β := fun a =>
  Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a) $ fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom $ fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h
#align pfun.fix PFun.fix

theorem dom_of_mem_fix {f : α →. Sum β α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  -- ⊢ (f a).Dom
  rw [WellFounded.fixFEq] at h₂; exact h₂.fst.fst
  -- ⊢ (f a).Dom
                                 -- 🎉 no goals
#align pfun.dom_of_mem_fix PFun.dom_of_mem_fix

theorem mem_fix_iff {f : α →. Sum β α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    rw [WellFounded.fixFEq] at h₂
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    simp at h₂
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    cases' h₂ with h₂ h₃
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    split at h₃
    next e => simp at h₃; subst b; refine' Or.inl ⟨h₂, e⟩
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
    -- 🎉 no goals
   fun h => by
    simp [fix]
    -- ⊢ ∃ h,
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
        -- 🎉 no goals
      · rw [WellFounded.fixFEq]
        -- ⊢ b ∈
        -- Porting note: used to be simp [h₁, h₂]
        apply Part.mem_assert h₁
        -- ⊢ b ∈
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp [fix] at h₃
      -- ⊢ ∃ h,
      cases' h₃ with h₃ h₄
      -- ⊢ ∃ h,
      refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique h h' with e
        -- ⊢ Acc (fun x y => Sum.inr x ∈ f y) y
        exact e ▸ h₃
        -- 🎉 no goals
      · cases' h with h₁ h₂
        -- ⊢ b ∈
        rw [WellFounded.fixFEq]
        -- ⊢ b ∈
        -- Porting note: used to be simp [h₁, h₂, h₄]
        apply Part.mem_assert h₁
        -- ⊢ b ∈
        split
        next e =>
          injection h₂.symm.trans e
        next e =>
          injection h₂.symm.trans e; subst a'; exact h₄⟩
#align pfun.mem_fix_iff PFun.mem_fix_iff

/-- If advancing one step from `a` leads to `b : β`, then `f.fix a = b` -/
theorem fix_stop {f : α →. Sum β α} {b : β} {a : α} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a := by
  rw [PFun.mem_fix_iff]
  -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
  exact Or.inl hb
  -- 🎉 no goals
#align pfun.fix_stop PFun.fix_stop

/-- If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a'` -/
theorem fix_fwd_eq {f : α →. Sum β α} {a a' : α} (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' := by
  ext b; constructor
  -- ⊢ b ∈ fix f a ↔ b ∈ fix f a'
         -- ⊢ b ∈ fix f a → b ∈ fix f a'
  · intro h
    -- ⊢ b ∈ fix f a'
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    -- ⊢ b ∈ fix f a'
                                                   -- 🎉 no goals
                                                   -- ⊢ b ∈ fix f a'
    exact e'
    -- 🎉 no goals
  · intro h
    -- ⊢ b ∈ fix f a
    rw [PFun.mem_fix_iff]
    -- ⊢ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ fix f a'
    exact Or.inr ⟨a', ha', h⟩
    -- 🎉 no goals
#align pfun.fix_fwd_eq PFun.fix_fwd_eq

theorem fix_fwd {f : α →. Sum β α} {b : β} {a a' : α} (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) :
    b ∈ f.fix a' := by rwa [← fix_fwd_eq ha']
                       -- 🎉 no goals
#align pfun.fix_fwd PFun.fix_fwd

/-- A recursion principle for `PFun.fix`. -/
@[elab_as_elim]
def fixInduction {C : α → Sort*} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a := by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  -- ⊢ C a
  -- Porting note: revert/intro trick required to address `generalize_proofs` bug
  revert h₂
  -- ⊢ b ∈
  generalize_proofs h₁
  -- ⊢ b ∈
  intro h₂; clear h
  -- ⊢ C a
            -- ⊢ C a
  induction' h₁ with a ha IH
  -- ⊢ C a
  have h : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  -- ⊢ C a
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd
  -- 🎉 no goals
#align pfun.fix_induction PFun.fixInduction

theorem fixInduction_spec {C : α → Sort*} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun a' h' => fixInduction (fix_fwd h h') H := by
  unfold fixInduction
  -- ⊢ (let_fun h₂ :=
  -- Porting note: `generalize` required to address `generalize_proofs` bug
  generalize (Part.mem_assert_iff.1 h).fst = ha
  -- ⊢ (let_fun h₂ :=
  induction ha
  -- ⊢ (let_fun h₂ :=
  rfl
  -- 🎉 no goals
#align pfun.fix_induction_spec PFun.fixInduction_spec

/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_elim]
def fixInduction' {C : α → Sort*} {f : α →. Sum β α} {b : β} {a : α}
    (h : b ∈ f.fix a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a := by
  refine' fixInduction h fun a' h ih => _
  -- ⊢ C a'
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  -- ⊢ C a'
                                                             -- ⊢ C a'
                                                             -- ⊢ C a'
  · apply hbase
    -- ⊢ Sum.inl b ∈ f a'
    convert e
    -- ⊢ b = b'
    exact Part.mem_unique h (fix_stop e)
    -- 🎉 no goals
  · exact hind _ _ (fix_fwd h e) e (ih _ e)
    -- 🎉 no goals
#align pfun.fix_induction' PFun.fixInduction'

theorem fixInduction'_stop {C : α → Sort*} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (fa : Sum.inl b ∈ f a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa := by
  unfold fixInduction'
  -- ⊢ (fixInduction h fun a' h ih =>
  rw [fixInduction_spec]
  -- ⊢ Sum.casesOn (motive := fun x => Part.get (f a) (_ : (f a).Dom) = x → C a) (P …
  -- Porting note: the explicit motive required because `simp` behaves differently
  refine' Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y → C a) x _ _
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) _
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
  -- 🎉 no goals
#align pfun.fix_induction'_stop PFun.fixInduction'_stop

theorem fixInduction'_fwd {C : α → Sort*} {f : α →. Sum β α} {b : β} {a a' : α} (h : b ∈ f.fix a)
    (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) := by
  unfold fixInduction'
  -- ⊢ (fixInduction h fun a' h ih =>
  rw [fixInduction_spec]
  -- ⊢ Sum.casesOn (motive := fun x => Part.get (f a) (_ : (f a).Dom) = x → C a) (P …
  -- Porting note: the explicit motive required because `simp` behaves differently
  refine' Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y → C a) x _ _
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) _
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
  -- 🎉 no goals
#align pfun.fix_induction'_fwd PFun.fixInduction'_fwd

variable (f : α →. β)

/-- Image of a set under a partial function. -/
def image (s : Set α) : Set β :=
  f.graph'.image s
#align pfun.image PFun.image

theorem image_def (s : Set α) : f.image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl
#align pfun.image_def PFun.image_def

theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_image PFun.mem_image

theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  Rel.image_mono _ h
#align pfun.image_mono PFun.image_mono

theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  Rel.image_inter _ s t
#align pfun.image_inter PFun.image_inter

theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  Rel.image_union _ s t
#align pfun.image_union PFun.image_union

/-- Preimage of a set under a partial function. -/
def preimage (s : Set β) : Set α :=
  Rel.image (fun x y => x ∈ f y) s
#align pfun.preimage PFun.preimage

theorem Preimage_def (s : Set β) : f.preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl
#align pfun.preimage_def PFun.Preimage_def

@[simp]
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_preimage PFun.mem_preimage

theorem preimage_subset_dom (s : Set β) : f.preimage s ⊆ f.Dom := fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
#align pfun.preimage_subset_dom PFun.preimage_subset_dom

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
  Rel.preimage_mono _ h
#align pfun.preimage_mono PFun.preimage_mono

theorem preimage_inter (s t : Set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
  Rel.preimage_inter _ s t
#align pfun.preimage_inter PFun.preimage_inter

theorem preimage_union (s t : Set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
  Rel.preimage_union _ s t
#align pfun.preimage_union PFun.preimage_union

theorem preimage_univ : f.preimage Set.univ = f.Dom := by ext; simp [mem_preimage, mem_dom]
                                                          -- ⊢ x✝ ∈ preimage f Set.univ ↔ x✝ ∈ Dom f
                                                               -- 🎉 no goals
#align pfun.preimage_univ PFun.preimage_univ

theorem coe_preimage (f : α → β) (s : Set β) : (f : α →. β).preimage s = f ⁻¹' s := by ext; simp
                                                                                       -- ⊢ x✝ ∈ preimage (↑f) s ↔ x✝ ∈ f ⁻¹' s
                                                                                            -- 🎉 no goals
#align pfun.coe_preimage PFun.coe_preimage

/-- Core of a set `s : Set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def core (s : Set β) : Set α :=
  f.graph'.core s
#align pfun.core PFun.core

theorem core_def (s : Set β) : f.core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl
#align pfun.core_def PFun.core_def

@[simp]
theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl
#align pfun.mem_core PFun.mem_core

theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx
#align pfun.compl_dom_subset_core PFun.compl_dom_subset_core

theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  Rel.core_mono _ h
#align pfun.core_mono PFun.core_mono

theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  Rel.core_inter _ s t
#align pfun.core_inter PFun.core_inter

theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) :
    x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t := by simp [mem_core, mem_res]
                                                 -- 🎉 no goals
#align pfun.mem_core_res PFun.mem_core_res

section

open Classical

theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t := by
  ext x
  -- ⊢ x ∈ core (res f s) t ↔ x ∈ sᶜ ∪ f ⁻¹' t
  rw [mem_core_res]
  -- ⊢ x ∈ s → f x ∈ t ↔ x ∈ sᶜ ∪ f ⁻¹' t
  by_cases h : x ∈ s <;> simp [h]
  -- ⊢ x ∈ s → f x ∈ t ↔ x ∈ sᶜ ∪ f ⁻¹' t
                         -- 🎉 no goals
                         -- 🎉 no goals
#align pfun.core_res PFun.core_res

end

theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).core s = s.preimage f := by
  ext x; simp [core_def]
  -- ⊢ x ∈ core (↑f) s ↔ x ∈ f ⁻¹' s
         -- 🎉 no goals
#align pfun.core_restrict PFun.core_restrict

theorem preimage_subset_core (f : α →. β) (s : Set β) : f.preimage s ⊆ f.core s :=
  fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys
#align pfun.preimage_subset_core PFun.preimage_subset_core

theorem preimage_eq (f : α →. β) (s : Set β) : f.preimage s = f.core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore _ (Part.get_mem _)
    show x ∈ f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩
#align pfun.preimage_eq PFun.preimage_eq

theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.union_distrib_right, Set.union_comm (Dom f), Set.compl_union_self,
    Set.inter_univ, Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]
#align pfun.core_eq PFun.core_eq

theorem preimage_asSubtype (f : α →. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.preimage s := by
  ext x
  -- ⊢ x ∈ asSubtype f ⁻¹' s ↔ x ∈ Subtype.val ⁻¹' preimage f s
  simp only [Set.mem_preimage, Set.mem_setOf_eq, PFun.asSubtype, PFun.mem_preimage]
  -- ⊢ fn f ↑x (_ : ↑x ∈ Dom f) ∈ s ↔ ∃ y, y ∈ s ∧ y ∈ f ↑x
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  -- ⊢ fn f ↑x (_ : ↑x ∈ Dom f) ∈ s ↔ ∃ y, y ∈ s ∧ y ∈ f ↑x
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys
#align pfun.preimage_as_subtype PFun.preimage_asSubtype

/-- Turns a function into a partial function to a subtype. -/
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩
#align pfun.to_subtype PFun.toSubtype

@[simp]
theorem dom_toSubtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl
#align pfun.dom_to_subtype PFun.dom_toSubtype

@[simp]
theorem toSubtype_apply (p : β → Prop) (f : α → β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl
#align pfun.to_subtype_apply PFun.toSubtype_apply

theorem dom_toSubtype_apply_iff {p : β → Prop} {f : α → β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl
#align pfun.dom_to_subtype_apply_iff PFun.dom_toSubtype_apply_iff

theorem mem_toSubtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} :
    b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [toSubtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]
  -- 🎉 no goals
#align pfun.mem_to_subtype_iff PFun.mem_toSubtype_iff

/-- The identity as a partial function -/
protected def id (α : Type*) : α →. α :=
  Part.some
#align pfun.id PFun.id

@[simp]
theorem coe_id (α : Type*) : ((id : α → α) : α →. α) = PFun.id α :=
  rfl
#align pfun.coe_id PFun.coe_id

@[simp]
theorem id_apply (a : α) : PFun.id α a = Part.some a :=
  rfl
#align pfun.id_apply PFun.id_apply

/-- Composition of partial functions as a partial function. -/
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
#align pfun.comp PFun.comp

@[simp]
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl
#align pfun.comp_apply PFun.comp_apply

@[simp]
theorem id_comp (f : α →. β) : (PFun.id β).comp f = f :=
  ext fun _ _ => by simp
                    -- 🎉 no goals
#align pfun.id_comp PFun.id_comp

@[simp]
theorem comp_id (f : α →. β) : f.comp (PFun.id α) = f :=
  ext fun _ _ => by simp
                    -- 🎉 no goals
#align pfun.comp_id PFun.comp_id

@[simp]
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.preimage f.Dom := by
  ext
  -- ⊢ x✝ ∈ Dom (comp f g) ↔ x✝ ∈ preimage g (Dom f)
  simp_rw [mem_preimage, mem_dom, comp_apply, Part.mem_bind_iff, ← exists_and_right]
  -- ⊢ (∃ y a, a ∈ g x✝ ∧ y ∈ f a) ↔ ∃ y x, x ∈ f y ∧ y ∈ g x✝
  rw [exists_comm]
  -- ⊢ (∃ b a, b ∈ g x✝ ∧ a ∈ f b) ↔ ∃ y x, x ∈ f y ∧ y ∈ g x✝
  simp_rw [and_comm]
  -- 🎉 no goals
#align pfun.dom_comp PFun.dom_comp

@[simp]
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) :
    (f.comp g).preimage s = g.preimage (f.preimage s) := by
  ext
  -- ⊢ x✝ ∈ preimage (comp f g) s ↔ x✝ ∈ preimage g (preimage f s)
  simp_rw [mem_preimage, comp_apply, Part.mem_bind_iff, ← exists_and_right, ← exists_and_left]
  -- ⊢ (∃ y x, y ∈ s ∧ x ∈ g x✝ ∧ y ∈ f x) ↔ ∃ y x, (x ∈ s ∧ x ∈ f y) ∧ y ∈ g x✝
  rw [exists_comm]
  -- ⊢ (∃ b a, a ∈ s ∧ b ∈ g x✝ ∧ a ∈ f b) ↔ ∃ y x, (x ∈ s ∧ x ∈ f y) ∧ y ∈ g x✝
  simp_rw [and_assoc, and_comm]
  -- 🎉 no goals
#align pfun.preimage_comp PFun.preimage_comp

@[simp]
theorem Part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by
  ext c
  -- ⊢ c ∈ Part.bind a (comp f g) ↔ c ∈ Part.bind (Part.bind a g) f
  simp_rw [Part.mem_bind_iff, comp_apply, Part.mem_bind_iff, ← exists_and_right, ← exists_and_left]
  -- ⊢ (∃ a_1 x, a_1 ∈ a ∧ x ∈ g a_1 ∧ c ∈ f x) ↔ ∃ a_1 x, (x ∈ a ∧ a_1 ∈ g x) ∧ c  …
  rw [exists_comm]
  -- ⊢ (∃ b a_1, a_1 ∈ a ∧ b ∈ g a_1 ∧ c ∈ f b) ↔ ∃ a_1 x, (x ∈ a ∧ a_1 ∈ g x) ∧ c  …
  simp_rw [and_assoc]
  -- 🎉 no goals
#align part.bind_comp PFun.Part.bind_comp

@[simp]
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, Part.bind_comp]
                    -- 🎉 no goals
#align pfun.comp_assoc PFun.comp_assoc

-- This can't be `simp`
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]
                    -- 🎉 no goals
#align pfun.coe_comp PFun.coe_comp

/-- Product of partial functions. -/
def prodLift (f : α →. β) (g : α →. γ) : α →. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩
#align pfun.prod_lift PFun.prodLift

@[simp]
theorem dom_prodLift (f : α →. β) (g : α →. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl
#align pfun.dom_prod_lift PFun.dom_prodLift

theorem get_prodLift (f : α →. β) (g : α →. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl
#align pfun.get_prod_lift PFun.get_prodLift

@[simp]
theorem prodLift_apply (f : α →. β) (g : α →. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl
#align pfun.prod_lift_apply PFun.prodLift_apply

theorem mem_prodLift {f : α →. β} {g : α →. γ} {x : α} {y : β × γ} :
    y ∈ f.prodLift g x ↔ y.1 ∈ f x ∧ y.2 ∈ g x := by
  trans ∃ hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  -- ⊢ y ∈ prodLift f g x ↔ ∃ hp hq, Part.get (f x) hp = y.fst ∧ Part.get (g x) hq  …
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
    -- 🎉 no goals
  -- Porting note: was just `[exists_and_left, exists_and_right]`
  · simp only [exists_and_left, exists_and_right, (· ∈ ·), Part.Mem]
    -- 🎉 no goals
#align pfun.mem_prod_lift PFun.mem_prodLift

/-- Product of partial functions. -/
def prodMap (f : α →. γ) (g : β →. δ) : α × β →. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩
#align pfun.prod_map PFun.prodMap

@[simp]
theorem dom_prodMap (f : α →. γ) (g : β →. δ) :
    (f.prodMap g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl
#align pfun.dom_prod_map PFun.dom_prodMap

theorem get_prodMap (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
    (f.prodMap g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl
#align pfun.get_prod_map PFun.get_prodMap

@[simp]
theorem prodMap_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
    f.prodMap g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl
#align pfun.prod_map_apply PFun.prodMap_apply

theorem mem_prodMap {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
    y ∈ f.prodMap g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 := by
  trans ∃ hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  -- ⊢ y ∈ prodMap f g x ↔ ∃ hp hq, Part.get (f x.fst) hp = y.fst ∧ Part.get (g x.s …
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
    -- 🎉 no goals
  · simp only [exists_and_left, exists_and_right, (· ∈ ·), Part.Mem]
    -- 🎉 no goals
#align pfun.mem_prod_map PFun.mem_prodMap

@[simp]
theorem prodLift_fst_comp_snd_comp (f : α →. γ) (g : β →. δ) :
    prodLift (f.comp ((Prod.fst : α × β → α) : α × β →. α))
        (g.comp ((Prod.snd : α × β → β) : α × β →. β)) =
      prodMap f g :=
  ext fun a => by simp
                  -- 🎉 no goals
#align pfun.prod_lift_fst_comp_snd_comp PFun.prodLift_fst_comp_snd_comp

@[simp]
theorem prodMap_id_id : (PFun.id α).prodMap (PFun.id β) = PFun.id _ :=
  ext fun _ _ => by simp [eq_comm]
                    -- 🎉 no goals
#align pfun.prod_map_id_id PFun.prodMap_id_id

@[simp]
theorem prodMap_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
    (f₂.comp f₁).prodMap (g₂.comp g₁) = (f₂.prodMap g₂).comp (f₁.prodMap g₁) := -- by
  -- Porting note: was `by tidy`, below is a golf'd version of the `tidy?` proof
  ext $ λ ⟨_, _⟩ ⟨_, _⟩ =>
  ⟨λ ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   λ ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ => ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩
#align pfun.prod_map_comp_comp PFun.prodMap_comp_comp

end PFun
