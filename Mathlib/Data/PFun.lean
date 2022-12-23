/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.pfun
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Part
import Mathbin.Data.Rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → part β`.

## Definitions

* `pfun α β`: Type of partial functions from `α` to `β`. Defined as `α → part β` and denoted
  `α →. β`.
* `pfun.dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `pfun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `dom`.
* `pfun.as_subtype`: Returns a partial function as a function from its `dom`.
* `pfun.to_subtype`: Restricts the codomain of a function to a subtype.
* `pfun.eval_opt`: Returns a partial function with a decidable `dom` as a function `a → option β`.
* `pfun.lift`: Turns a function into a partial function.
* `pfun.id`: The identity as a partial function.
* `pfun.comp`: Composition of partial functions.
* `pfun.restrict`: Restriction of a partial function to a smaller `dom`.
* `pfun.res`: Turns a function into a partial function with a prescribed domain.
* `pfun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `pfun.fix_induction`: A recursion principle for `pfun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `rel` definitions to `pfun`:
* `pfun.image`: Image of a set under a partial function.
* `pfun.ran`: Range of a partial function.
* `pfun.preimage`: Preimage of a set under a partial function.
* `pfun.core`: Core of a set under a partial function.
* `pfun.graph`: Graph of a partial function `a →. β`as a `set (α × β)`.
* `pfun.graph'`: Graph of a partial function `a →. β`as a `rel α β`.

### `pfun α` as a monad

Monad operations:
* `pfun.pure`: The monad `pure` function, the constant `x` function.
* `pfun.bind`: The monad `bind` function, pointwise `part.bind`
* `pfun.map`: The monad `map` function, pointwise `part.map`.
-/


open Function

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → part β`. -/
def Pfun (α β : Type _) :=
  α → Part β
#align pfun Pfun

-- mathport name: «expr →. »
infixr:25 " →. " => Pfun

namespace Pfun

variable {α β γ δ ε ι : Type _}

instance : Inhabited (α →. β) :=
  ⟨fun a => Part.none⟩

/-- The domain of a partial function -/
def dom (f : α →. β) : Set α :=
  { a | (f a).Dom }
#align pfun.dom Pfun.dom

@[simp]
theorem mem_dom (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ y, y ∈ f x := by simp [dom, Part.dom_iff_mem]
#align pfun.mem_dom Pfun.mem_dom

@[simp]
theorem dom_mk (p : α → Prop) (f : ∀ a, p a → β) : (Pfun.dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl
#align pfun.dom_mk Pfun.dom_mk

theorem dom_eq (f : α →. β) : dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)
#align pfun.dom_eq Pfun.dom_eq

/-- Evaluate a partial function -/
def fn (f : α →. β) (a : α) : dom f a → β :=
  (f a).get
#align pfun.fn Pfun.fn

@[simp]
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl
#align pfun.fn_apply Pfun.fn_apply

/-- Evaluate a partial function to return an `option` -/
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)
#align pfun.eval_opt Pfun.evalOpt

/-- Partial function extensionality -/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ dom f ↔ a ∈ dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)
#align pfun.ext' Pfun.ext'

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)
#align pfun.ext Pfun.ext

/-- Turns a partial function into a function out of its domain. -/
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2
#align pfun.as_subtype Pfun.asSubtype

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equivSubtype : (α →. β) ≃ Σp : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun f =>
    funext fun a => Part.eta _, fun ⟨p, f⟩ => by dsimp <;> congr <;> funext a <;> cases a <;> rfl⟩
#align pfun.equiv_subtype Pfun.equivSubtype

theorem as_subtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy
#align pfun.as_subtype_eq_of_mem Pfun.as_subtype_eq_of_mem

/-- Turn a total function into a partial function. -/
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)
#align pfun.lift Pfun.lift

instance : Coe (α → β) (α →. β) :=
  ⟨Pfun.lift⟩

@[simp]
theorem lift_eq_coe (f : α → β) : Pfun.lift f = f :=
  rfl
#align pfun.lift_eq_coe Pfun.lift_eq_coe

@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl
#align pfun.coe_val Pfun.coe_val

@[simp]
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.univ :=
  rfl
#align pfun.dom_coe Pfun.dom_coe

theorem coe_injective : Injective (coe : (α → β) → α →. β) := fun f g h =>
  funext fun a => Part.some_injective <| congr_fun h a
#align pfun.coe_injective Pfun.coe_injective

/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
def graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }
#align pfun.graph Pfun.graph

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def graph' (f : α →. β) : Rel α β := fun x y => y ∈ f x
#align pfun.graph' Pfun.graph'

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }
#align pfun.ran Pfun.ran

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
  (f x).restrict (x ∈ p) (@H x)
#align pfun.restrict Pfun.restrict

@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) :
    b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a := by simp [restrict]
#align pfun.mem_restrict Pfun.mem_restrict

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (Pfun.lift f).restrict s.subset_univ
#align pfun.res Pfun.res

theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [res, @eq_comm _ b]
#align pfun.mem_res Pfun.mem_res

theorem res_univ (f : α → β) : Pfun.res f Set.univ = f :=
  rfl
#align pfun.res_univ Pfun.res_univ

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem
#align pfun.dom_iff_graph Pfun.dom_iff_graph

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
  show (∃ h : True, f a = b) ↔ f a = b by simp
#align pfun.lift_graph Pfun.lift_graph

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := fun _ => Part.some x
#align pfun.pure Pfun.pure

/-- The monad `bind` function, pointwise `part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a
#align pfun.bind Pfun.bind

@[simp]
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl
#align pfun.bind_apply Pfun.bind_apply

/-- The monad `map` function, pointwise `part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f
#align pfun.map Pfun.map

instance : Monad (Pfun α) where 
  pure := @Pfun.pure _
  bind := @Pfun.bind _
  map := @Pfun.map _

instance :
    LawfulMonad
      (Pfun
        α) where 
  bind_pure_comp_eq_map β γ f x := funext fun a => Part.bind_some_eq_map _ _
  id_map β f := by funext a <;> dsimp [Functor.map, Pfun.map] <;> cases f a <;> rfl
  pure_bind β γ x f := funext fun a => Part.bind_some.{u_1, u_2} _ (f x)
  bind_assoc β γ δ f g k := funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a

theorem pure_defined (p : Set α) (x : β) : p ⊆ (@Pfun.pure α _ x).Dom :=
  p.subset_univ
#align pfun.pure_defined Pfun.pure_defined

theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom)
    (H2 : ∀ x, p ⊆ (g x).Dom) : p ⊆ (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)
#align pfun.bind_defined Pfun.bind_defined

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. Sum β α) : α →. β := fun a =>
  (Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a)) fun h =>
    @WellFounded.fixF _ (fun x y => Sum.inr x ∈ f y) _
      (fun a IH =>
        (Part.assert (f a).Dom) fun hf => by
          cases' e : (f a).get hf with b a' <;> [exact Part.some b, exact IH _ ⟨hf, e⟩])
      a h
#align pfun.fix Pfun.fix

theorem dom_of_mem_fix {f : α →. Sum β α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fix_F_eq] at h₂ <;> exact h₂.fst.fst
#align pfun.dom_of_mem_fix Pfun.dom_of_mem_fix

theorem mem_fix_iff {f : α →. Sum β α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by 
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fix_F_eq] at h₂
    simp at h₂
    cases' h₂ with h₂ h₃
    cases' e : (f a).get h₂ with b' a' <;> simp [e] at h₃
    · subst b'
      refine' Or.inl ⟨h₂, e⟩
    · exact Or.inr ⟨a', ⟨_, e⟩, Part.mem_assert _ h₃⟩, fun h => by
    simp [fix]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fix_F_eq]
        simp [h₁, h₂]
    · simp [fix] at h₃
      cases' h₃ with h₃ h₄
      refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · cases' h with h₁ h₂
        rw [WellFounded.fix_F_eq]
        simp [h₁, h₂, h₄]⟩
#align pfun.mem_fix_iff Pfun.mem_fix_iff

/-- If advancing one step from `a` leads to `b : β`, then `f.fix a = b` -/
theorem fix_stop {f : α →. Sum β α} {b : β} {a : α} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a := by
  rw [Pfun.mem_fix_iff]
  exact Or.inl hb
#align pfun.fix_stop Pfun.fix_stop

/-- If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a'` -/
theorem fix_fwd_eq {f : α →. Sum β α} {a a' : α} (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' := by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [Pfun.mem_fix_iff]
    right
    use a'
    exact ⟨ha', h⟩
#align pfun.fix_fwd_eq Pfun.fix_fwd_eq

theorem fix_fwd {f : α →. Sum β α} {b : β} {a a' : α} (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) :
    b ∈ f.fix a' := by rwa [← fix_fwd_eq ha']
#align pfun.fix_fwd Pfun.fix_fwd

/-- A recursion principle for `pfun.fix`. -/
@[elab_as_elim]
def fixInduction {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a := by
  have h₂ := (Part.mem_assert_iff.1 h).snd; generalize_proofs h₁  at h₂; clear h
  induction' h₁ with a ha IH
  have h : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd
#align pfun.fix_induction Pfun.fixInduction

theorem fix_induction_spec {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun a' h' => fixInduction (fix_fwd h h') H := by
  unfold fix_induction
  generalize_proofs ha
  induction ha
  rfl
#align pfun.fix_induction_spec Pfun.fix_induction_spec

/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_elim]
def fixInduction' {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a := by
  refine' fix_induction h fun a' h ih => _
  cases' e : (f a').get (dom_of_mem_fix h) with b' a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  · apply hbase
    convert e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)
#align pfun.fix_induction' Pfun.fixInduction'

theorem fix_induction'_stop {C : α → Sort _} {f : α →. Sum β α} {b : β} {a : α} (h : b ∈ f.fix a)
    (fa : Sum.inl b ∈ f a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa := by
  unfold fix_induction'
  rw [fix_induction_spec]
  simp [Part.get_eq_of_mem fa]
#align pfun.fix_induction'_stop Pfun.fix_induction'_stop

theorem fix_induction'_fwd {C : α → Sort _} {f : α →. Sum β α} {b : β} {a a' : α} (h : b ∈ f.fix a)
    (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) := by
  unfold fix_induction'
  rw [fix_induction_spec]
  simpa [Part.get_eq_of_mem fa]
#align pfun.fix_induction'_fwd Pfun.fix_induction'_fwd

variable (f : α →. β)

/-- Image of a set under a partial function. -/
def image (s : Set α) : Set β :=
  f.graph'.image s
#align pfun.image Pfun.image

theorem image_def (s : Set α) : f.image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl
#align pfun.image_def Pfun.image_def

theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_image Pfun.mem_image

theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  Rel.image_mono _ h
#align pfun.image_mono Pfun.image_mono

theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  Rel.image_inter _ s t
#align pfun.image_inter Pfun.image_inter

theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  Rel.image_union _ s t
#align pfun.image_union Pfun.image_union

/-- Preimage of a set under a partial function. -/
def preimage (s : Set β) : Set α :=
  Rel.image (fun x y => x ∈ f y) s
#align pfun.preimage Pfun.preimage

theorem preimage_def (s : Set β) : f.Preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl
#align pfun.preimage_def Pfun.preimage_def

@[simp]
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.Preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl
#align pfun.mem_preimage Pfun.mem_preimage

theorem preimage_subset_dom (s : Set β) : f.Preimage s ⊆ f.Dom := fun x ⟨y, ys, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
#align pfun.preimage_subset_dom Pfun.preimage_subset_dom

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.Preimage s ⊆ f.Preimage t :=
  Rel.preimage_mono _ h
#align pfun.preimage_mono Pfun.preimage_mono

theorem preimage_inter (s t : Set β) : f.Preimage (s ∩ t) ⊆ f.Preimage s ∩ f.Preimage t :=
  Rel.preimage_inter _ s t
#align pfun.preimage_inter Pfun.preimage_inter

theorem preimage_union (s t : Set β) : f.Preimage (s ∪ t) = f.Preimage s ∪ f.Preimage t :=
  Rel.preimage_union _ s t
#align pfun.preimage_union Pfun.preimage_union

theorem preimage_univ : f.Preimage Set.univ = f.Dom := by ext <;> simp [mem_preimage, mem_dom]
#align pfun.preimage_univ Pfun.preimage_univ

theorem coe_preimage (f : α → β) (s : Set β) : (f : α →. β).Preimage s = f ⁻¹' s := by ext <;> simp
#align pfun.coe_preimage Pfun.coe_preimage

/-- Core of a set `s : set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def core (s : Set β) : Set α :=
  f.graph'.core s
#align pfun.core Pfun.core

theorem core_def (s : Set β) : f.core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl
#align pfun.core_def Pfun.core_def

@[simp]
theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl
#align pfun.mem_core Pfun.mem_core

theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx
#align pfun.compl_dom_subset_core Pfun.compl_dom_subset_core

theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  Rel.core_mono _ h
#align pfun.core_mono Pfun.core_mono

theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  Rel.core_inter _ s t
#align pfun.core_inter Pfun.core_inter

theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) :
    x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t := by simp [mem_core, mem_res]
#align pfun.mem_core_res Pfun.mem_core_res

section

open Classical

theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t := by
  ext
  rw [mem_core_res]
  by_cases h : x ∈ s <;> simp [h]
#align pfun.core_res Pfun.core_res

end

theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).core s = s.Preimage f := by
  ext x <;> simp [core_def]
#align pfun.core_restrict Pfun.core_restrict

theorem preimage_subset_core (f : α →. β) (s : Set β) : f.Preimage s ⊆ f.core s :=
  fun x ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys
#align pfun.preimage_subset_core Pfun.preimage_subset_core

theorem preimage_eq (f : α →. β) (s : Set β) : f.Preimage s = f.core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore _ (Part.get_mem _)
    show x ∈ f.Preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩
#align pfun.preimage_eq Pfun.preimage_eq

theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.Preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.union_distrib_right, Set.union_comm (dom f), Set.compl_union_self,
    Set.inter_univ, Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]
#align pfun.core_eq Pfun.core_eq

theorem preimage_as_subtype (f : α →. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.Preimage s := by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Pfun.asSubtype, Pfun.mem_preimage]
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys
#align pfun.preimage_as_subtype Pfun.preimage_as_subtype

/-- Turns a function into a partial function to a subtype. -/
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩
#align pfun.to_subtype Pfun.toSubtype

@[simp]
theorem dom_to_subtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl
#align pfun.dom_to_subtype Pfun.dom_to_subtype

@[simp]
theorem to_subtype_apply (p : β → Prop) (f : α → β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl
#align pfun.to_subtype_apply Pfun.to_subtype_apply

theorem dom_to_subtype_apply_iff {p : β → Prop} {f : α → β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl
#align pfun.dom_to_subtype_apply_iff Pfun.dom_to_subtype_apply_iff

theorem mem_to_subtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} :
    b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [to_subtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]
#align pfun.mem_to_subtype_iff Pfun.mem_to_subtype_iff

/-- The identity as a partial function -/
protected def id (α : Type _) : α →. α :=
  Part.some
#align pfun.id Pfun.id

@[simp]
theorem coe_id (α : Type _) : ((id : α → α) : α →. α) = Pfun.id α :=
  rfl
#align pfun.coe_id Pfun.coe_id

@[simp]
theorem id_apply (a : α) : Pfun.id α a = Part.some a :=
  rfl
#align pfun.id_apply Pfun.id_apply

/-- Composition of partial functions as a partial function. -/
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
#align pfun.comp Pfun.comp

@[simp]
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl
#align pfun.comp_apply Pfun.comp_apply

@[simp]
theorem id_comp (f : α →. β) : (Pfun.id β).comp f = f :=
  ext fun _ _ => by simp
#align pfun.id_comp Pfun.id_comp

@[simp]
theorem comp_id (f : α →. β) : f.comp (Pfun.id α) = f :=
  ext fun _ _ => by simp
#align pfun.comp_id Pfun.comp_id

@[simp]
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.Preimage f.Dom := by
  ext
  simp_rw [mem_preimage, mem_dom, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right]
  rw [exists_comm]
  simp_rw [and_comm]
#align pfun.dom_comp Pfun.dom_comp

@[simp]
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) :
    (f.comp g).Preimage s = g.Preimage (f.Preimage s) := by
  ext
  simp_rw [mem_preimage, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right, ←
    exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc', and_comm]
#align pfun.preimage_comp Pfun.preimage_comp

@[simp]
theorem Part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by 
  ext c
  simp_rw [Part.mem_bind_iff, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_right, ←
    exists_and_left]
  rw [exists_comm]
  simp_rw [and_assoc']
#align part.bind_comp Part.bind_comp

@[simp]
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, Part.bind_comp]
#align pfun.comp_assoc Pfun.comp_assoc

-- This can't be `simp`
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Part.bind_some]
#align pfun.coe_comp Pfun.coe_comp

/-- Product of partial functions. -/
def prodLift (f : α →. β) (g : α →. γ) : α →. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩
#align pfun.prod_lift Pfun.prodLift

@[simp]
theorem dom_prod_lift (f : α →. β) (g : α →. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl
#align pfun.dom_prod_lift Pfun.dom_prod_lift

theorem get_prod_lift (f : α →. β) (g : α →. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl
#align pfun.get_prod_lift Pfun.get_prod_lift

@[simp]
theorem prod_lift_apply (f : α →. β) (g : α →. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl
#align pfun.prod_lift_apply Pfun.prod_lift_apply

theorem mem_prod_lift {f : α →. β} {g : α →. γ} {x : α} {y : β × γ} :
    y ∈ f.prodLift g x ↔ y.1 ∈ f x ∧ y.2 ∈ g x := by
  trans ∃ hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prod_lift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simpa only [exists_and_left, exists_and_right]
#align pfun.mem_prod_lift Pfun.mem_prod_lift

/-- Product of partial functions. -/
def prodMap (f : α →. γ) (g : β →. δ) : α × β →. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩
#align pfun.prod_map Pfun.prodMap

@[simp]
theorem dom_prod_map (f : α →. γ) (g : β →. δ) :
    (f.prod_map g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl
#align pfun.dom_prod_map Pfun.dom_prod_map

theorem get_prod_map (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
    (f.prod_map g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl
#align pfun.get_prod_map Pfun.get_prod_map

@[simp]
theorem prod_map_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
    f.prod_map g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl
#align pfun.prod_map_apply Pfun.prod_map_apply

theorem mem_prod_map {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
    y ∈ f.prod_map g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 := by
  trans ∃ hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [Prod_map, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simpa only [exists_and_left, exists_and_right]
#align pfun.mem_prod_map Pfun.mem_prod_map

@[simp]
theorem prod_lift_fst_comp_snd_comp (f : α →. γ) (g : β →. δ) :
    prodLift (f.comp ((Prod.fst : α × β → α) : α × β →. α))
        (g.comp ((Prod.snd : α × β → β) : α × β →. β)) =
      prodMap f g :=
  ext fun a => by simp
#align pfun.prod_lift_fst_comp_snd_comp Pfun.prod_lift_fst_comp_snd_comp

@[simp]
theorem prod_map_id_id : (Pfun.id α).prod_map (Pfun.id β) = Pfun.id _ :=
  ext fun _ _ => by simp [eq_comm]
#align pfun.prod_map_id_id Pfun.prod_map_id_id

@[simp]
theorem prod_map_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
    (f₂.comp f₁).prod_map (g₂.comp g₁) = (f₂.prod_map g₂).comp (f₁.prod_map g₁) :=
  ext fun _ _ => by tidy
#align pfun.prod_map_comp_comp Pfun.prod_map_comp_comp

end Pfun

