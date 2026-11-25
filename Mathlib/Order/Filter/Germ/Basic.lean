/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Order.Filter.Tendsto

import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Pi
import Mathlib.Data.Nat.Cast.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : Filter α` is the equivalence class of `f`
with respect to the equivalence relation `EventuallyEq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `Filter.Germ l β` to be the space of germs of functions `α → β` at a filter `l : Filter α`;
* coercion from `α → β` to `Germ l β`: `(f : Germ l β)` is the germ of `f : α → β`
  at `l : Filter α`; this coercion is declared as `CoeTC`;
* `(const l c : Germ l β)` is the germ of the constant function `fun x : α ↦ c` at a filter `l`;
* coercion from `β` to `Germ l β`: `(↑c : Germ l β)` is the germ of the constant function
  `fun x : α ↦ c` at a filter `l`; this coercion is declared as `CoeTC`;
* `map (F : β → γ) (f : Germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : Germ l β) (g : Germ l γ)` to be the germ of `fun x ↦ F (f x) (g x)`
  at `l`;
* `f.Tendsto lb`: we say that a germ `f : Germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.compTendsto g hg` and `f.compTendsto' g hg`: given `f : Germ l β` and a function
  `g : γ → α` (resp., a germ `g : Germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `Germ.liftPred`, `Germ.liftRel`: lift a predicate or a relation to the space of germs:
  `(f : Germ l β).liftPred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.

We also define `map (F : β → γ) : Germ l β → Germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* one-operation algebraic structures up to `CommGroup`;
* `MulZeroClass`, `Distrib`, `Semiring`, `CommSemiring`, `Ring`, `CommRing`;
* `MulAction`, `DistribMulAction`, `Module`;
* `Preorder`, `PartialOrder`, and `Lattice` structures, as well as `BoundedOrder`;

## Tags

filter, germ
-/

@[expose] public section

assert_not_exists IsOrderedRing

open scoped Relator
namespace Filter

variable {α β γ δ : Type*} {l : Filter α}

/-- Setoid used to define the filter product. This is a dependent version of
  `Filter.germSetoid`. -/
@[instance_reducible]
def productSetoid (l : Filter α) (ε : α → Type*) : Setoid ((a : _) → ε a) where
  r f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩

/-- The filter product `(a : α) → ε a` at a filter `l`. This is a dependent version of
  `Filter.Germ`. -/
def Product (l : Filter α) (ε : α → Type*) : Type _ :=
  Quotient (productSetoid l ε)

namespace Product

variable {ε ζ η : α → Type*} {f g h : (x : α) → ε x}

@[coe]
def ofFun (f : (a : α) → ε a) : l.Product ε :=
  Quotient.mk (productSetoid l ε) f

instance coeTC : CoeTC ((a : α) → ε a) (l.Product ε) := ⟨ofFun⟩

instance instInhabited [(a : α) → Inhabited (ε a)] : Inhabited (l.Product ε) :=
  ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

@[elab_as_elim]
theorem inductionOn {motive : Product l ε → Prop} (t : Product l ε)
    (ofFun : ∀ f, motive (ofFun f)) : motive t :=
  Quotient.inductionOn t ofFun

@[elab_as_elim]
theorem inductionOn₂
    {motive : Product l ε → Product l ζ → Prop} (t₁ : Product l ε) (t₂ : Product l ζ)
    (ofFun : ∀ f g, motive (ofFun f) (ofFun g)) : motive t₁ t₂ :=
  inductionOn t₁ fun f => inductionOn t₂ (ofFun f)

@[elab_as_elim]
theorem inductionOn₃
    {motive : Product l ε → Product l ζ → Product l η → Prop}
    (t₁ : Product l ε) (t₂ : Product l ζ) (t₃ : Product l η)
    (ofFun : ∀ f g h, motive (ofFun f) (ofFun g) (ofFun h)) : motive t₁ t₂ t₃ :=
  inductionOn t₁ fun f => inductionOn₂ t₂ t₃ (ofFun f)

/-- Given a germ `f : Product l ε` and a function `F : ((x : α) → ε x) → γ`
sending eventually equal functions to the same value,
returns the value `F` takes on functions having germ `f` at `l`. -/
def liftOn {γ : Sort*} (f : Product l ε) (F : ((x : α) → ε x) → γ)
    (hF : ∀ p q, (∀ᶠ x in l, p x = q x) → F p = F q) : γ :=
  Quotient.liftOn' f F hF

@[simp]
theorem liftOn_ofFun {γ : Sort*} (f : (x : α) → ε x) (F : ((x : α) → ε x) → γ)
    (hF : ∀ p q, (∀ᶠ x in l, p x = q x) → F p = F q) : liftOn (ofFun f) F hF = F f :=
  (rfl)

@[simp]
theorem ofFun_eq : (ofFun f : Product l ε) = ofFun g ↔ ∀ᶠ x in l, f x = g x :=
  Quotient.eq

alias ⟨_, _root_.Filter.Eventually.product_eq⟩ := ofFun_eq

/-- Lift a function `∀ x, ε x → ζ x` to a function `Germ l ε → Germ l ζ`. -/
def map (op : ∀ x, ε x → ζ x) : Product l ε → Product l ζ :=
  fun f => liftOn f (fun f => ofFun (fun x => op x (f x))) fun _ _ hpq =>
    (hpq.mono fun x => congrArg (op x)).product_eq

@[simp]
theorem map_coe (op : ∀ x, ε x → ζ x) (f : (x : α) → ε x) :
    map op (ofFun f : Product l ε) = ofFun fun x => op x (f x) :=
  rfl

@[simp]
theorem map_id : map (fun _ => id) = (id : Product l ε → Product l ε) := by
  ext ⟨f⟩
  rfl

theorem map_map (op₁ : ∀ x, ζ x → η x) (op₂ : ∀ x, ε x → ζ x) (f : Product l ε) :
    map op₁ (map op₂ f) = map (fun i x => op₁ i (op₂ i x)) f :=
  inductionOn f fun _ => rfl

/-- Lift a binary function `∀ x, ε x → ζ x → η x` to a function
`Product l ε → Product l ζ → Product l η`. -/
def map₂ (op : ∀ x, ε x → ζ x → η x) : Product l ε → Product l ζ → Product l η :=
  fun f g => liftOn f (fun f => liftOn g (fun g => ofFun (fun x => op x (f x) (g x)))
    fun _ _ hpq => (hpq.mono fun x => congrArg (op x (f x))).product_eq) fun _ _ hpq =>
    inductionOn g fun g => (hpq.mono fun x hx => congr(op x $hx (g x))).product_eq

@[simp]
theorem map₂_coe (op : ∀ x, ε x → ζ x → η x) (f : (x : α) → ε x) (g : (x : α) → ζ x) :
    map₂ op (f : Product l ε) g = fun x => op x (f x) (g x) :=
  rfl

/-- Lift a predicate `∀ x, ε x → Prop` to `Product l ε`. -/
def LiftPred (p : ∀ x, ε x → Prop) (f : Product l ε) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p x (f x)) fun _f _g H =>
    propext <| eventually_congr <| H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]
theorem liftPred_coe {p : ∀ x, ε x → Prop} {f : (x : α) → ε x} :
    LiftPred p (f : Product l ε) ↔ ∀ᶠ x in l, p x (f x) :=
  Iff.rfl

/-- Lift a relation `r : ∀ x, ε x → ζ x → Prop` to `Product l ε → Product l ζ → Prop`. -/
def LiftRel (r : ∀ x, ε x → ζ x → Prop) (f : Product l ε) (g : Product l ζ) : Prop :=
  LiftPred (fun x c => r x c.1 c.2) (map₂ (fun _ => Prod.mk) f g)

@[simp]
theorem liftRel_coe {r : ∀ x, ε x → ζ x → Prop} {f : (x : α) → ε x} {g : (x : α) → ζ x} :
    LiftRel r (f : Product l ε) g ↔ ∀ᶠ x in l, r x (f x) (g x) :=
  Iff.rfl

end Product

/-- The space of germs of functions `α → β` at a filter `l`. -/
abbrev Germ (l : Filter α) (β : Type*) : Type _ := l.Product fun _ => β

namespace Germ

variable {f g h : α → β}

/-- The germ corresponding to a global function. -/
@[coe]
abbrev ofFun : (α → β) → Germ l β := (↑)

instance : CoeTC (α → β) (Germ l β) :=
  ⟨ofFun⟩

/-- Germ of the constant function `fun x : α ↦ c` at a filter `l`. -/
@[coe]
abbrev const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b

instance coeTail : CoeTail β (Germ l β) :=
  ⟨const⟩

/-- A germ `P` of functions `α → β` is constant w.r.t. `l`. -/
def IsConstant {l : Filter α} (P : Germ l β) : Prop :=
  P.liftOn (fun f ↦ ∃ b : β, f =ᶠ[l] (fun _ ↦ b)) <| by
    suffices ∀ f g : α → β, ∀ b : β, f =ᶠ[l] g → (f =ᶠ[l] fun _ ↦ b) → (g =ᶠ[l] fun _ ↦ b) from
      fun f g h ↦ propext ⟨fun ⟨b, hb⟩ ↦ ⟨b, this f g b h hb⟩,
        fun ⟨b, hb⟩ ↦ ⟨b, EventuallyEq.trans h hb⟩⟩
    exact fun f g b hfg hf ↦ (hfg.symm).trans hf

theorem isConstant_coe {l : Filter α} {b} (h : ∀ x', f x' = b) : (↑f : Germ l β).IsConstant :=
  ⟨b, Eventually.of_forall h⟩

@[simp]
theorem isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α ↦ b : Germ l β).IsConstant := by
  use b

/-- If `f : α → β` is constant w.r.t. `l` and `g : β → γ`, then `g ∘ f : α → γ` also is. -/
lemma isConstant_comp {l : Filter α} {f : α → β} {g : β → γ}
    (h : (f : Germ l β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant := by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩

@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl

@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) :
    @Quotient.mk' _ (productSetoid _ _) f = (f : Germ l β) :=
  rfl

@[elab_as_elim]
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn f h

@[elab_as_elim]
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂ f g h

@[elab_as_elim]
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃ f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `Germ l β` to `Germ lc δ`. -/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  Quotient.map' F hF

/-- Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
nonrec abbrev liftOn {γ : Sort*} (f : Germ l β) (F : (α → β) → γ)
    (hF : (l.EventuallyEq ⇒ (· = ·)) F F) : γ :=
  f.liftOn F hF

@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl

@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

/-- Lift a function `β → γ` to a function `Germ l β → Germ l γ`. -/
abbrev map (op : β → γ) : Germ l β → Germ l γ := Product.map fun _ => op

@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl

@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  rfl

theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun _ => rfl

/-- Lift a binary function `β → γ → δ` to a function `Germ l β → Germ l γ → Germ l δ`. -/
abbrev map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Product.map₂ fun _ => op

@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : Filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

/-- Given two germs `f : Germ l β`, and `g : Germ lc α`, where `l : Filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg

@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl

/-- Given a germ `f : Germ l β` and a function `g : γ → α`, where `l : Filter α`, if `g` tends
to `l` along `lc : Filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto

@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g :=
  rfl

@[simp]
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl

theorem _root_.Filter.Tendsto.congr_germ {f g : β → γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α → β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  EventuallyEq.germ_eq (h.comp_tendsto hφ)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Filter.Tendsto.congr_germ := Filter.Tendsto.congr_germ

lemma isConstant_comp_tendsto {lc : Filter γ} {g : γ → α}
    (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β) := by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩

/-- If a germ `f : Germ l β` is constant, where `l : Filter α`,
and a function `g : γ → α` tends to `l` along `lc : Filter γ`,
the germ of the composition `f ∘ g` is also constant. -/
lemma isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ → α}
    (hf : f.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant := by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg

@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq

@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl

@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl

@[simp]
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b :=
  rfl

@[simp]
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg

/-- Lift a predicate on `β` to `Germ l β`. -/
abbrev LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  Product.LiftPred (fun _ => p) f

@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl

theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  Eventually.of_forall fun _y => hx

@[simp]
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)

/-- Lift a relation `r : β → γ → Prop` to `Germ l β → Germ l γ → Prop`. -/
abbrev LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Product.LiftRel (fun _ => r) f g

@[simp]
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl

theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  Eventually.of_forall fun _ => h

@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)

instance instInhabited [Inhabited β] : Inhabited (Germ l β) := ⟨↑(default : β)⟩

end Germ

namespace Product

section Monoid

variable {G' M' : Type*} {G M : α → Type*}

@[to_additive] instance instMul [∀ i, Mul (M i)] : Mul (Product l M) where
  mul := map₂ fun _ x y => x * y

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [∀ i, Mul (M i)] (f g : (x : α) → M x) : ↑(f * g) = (f * g : Product l M) :=
  rfl

@[to_additive] instance instOne [∀ i, One (M i)] : One (Product l M) where
  one := ofFun fun _ => 1

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [∀ i, One (M i)] : ↑(1 : (x : α) → (M x)) = (1 : Product l M) :=
  rfl

@[to_additive]
instance instSemigroup [∀ i, Semigroup (M i)] : Semigroup (Product l M) where
  mul_assoc a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_mul, mul_assoc]

@[to_additive]
instance instCommSemigroup [∀ i, CommSemigroup (M i)] : CommSemigroup (Product l M) where
  mul_comm a b := by
    induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_mul, mul_comm]

@[to_additive]
instance instIsLeftCancelMul [∀ i, Mul (M i)] [∀ i, IsLeftCancelMul (M i)] :
    IsLeftCancelMul (Product l M) where
  mul_left_cancel a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_mul]

@[to_additive]
instance instIsRightCancelMul [∀ i, Mul (M i)] [∀ i, IsRightCancelMul (M i)] :
    IsRightCancelMul (Product l M) where
  mul_right_cancel a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_mul]

@[to_additive]
instance instIsCancelMul [∀ i, Mul (M i)] [∀ i, IsCancelMul (M i)] : IsCancelMul (Product l M) where

@[to_additive]
instance instLeftCancelSemigroup [∀ i, LeftCancelSemigroup (M i)] :
    LeftCancelSemigroup (Product l M) where

@[to_additive]
instance instRightCancelSemigroup [∀ i, RightCancelSemigroup (M i)] :
    RightCancelSemigroup (Product l M) where

@[to_additive]
instance instMulOneClass [∀ i, MulOneClass (M i)] : MulOneClass (Product l M) where
  one_mul a := by induction a using inductionOn with | ofFun a => simp [← coe_one, ← coe_mul]
  mul_one a := by induction a using inductionOn with | ofFun a => simp [← coe_one, ← coe_mul]

@[to_additive (attr := to_additive) instSMul]
instance instPow [∀ i, Pow (G i) M'] : Pow (Product l G) M' where
    pow f n := map (fun _ x => x ^ n) f

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [∀ i, SMul M' (G i)] (n : M') (f : (x : α) → G x) :
    ↑(n • f) = n • (f : Product l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem _root_.Filter.Germ.const_smul [SMul M' G'] (n : M') (a : G') :
    (↑(n • a) : Germ l G') = n • (↑a : Germ l G') :=
  rfl

@[to_additive existing coe_smul]
theorem coe_pow [∀ i, Pow (G i) M'] (f : (x : α) → G x) (n : M') :
    ↑(f ^ n) = (f : Product l G) ^ n :=
  rfl

@[to_additive existing const_smul]
theorem _root_.Filter.Germ.const_pow [Pow G' M'] (a : G') (n : M') :
    (↑(a ^ n) : Germ l G') = (↑a : Germ l G') ^ n :=
  rfl

@[to_additive]
instance instMonoid [∀ i, Monoid (M i)] : Monoid (Product l M) where
  npow_zero a := by induction a using inductionOn with | ofFun a => simp [← coe_pow]
  npow_succ n a := by induction a using inductionOn with | ofFun a => simp [← coe_pow, pow_succ]

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive /-- Coercion from functions to germs as an additive monoid homomorphism. -/]
def coeMulHom [∀ i, Monoid (M i)] (l : Filter α) : ((x : α) → M x) →* Product l M where
  toFun := ofFun
  map_one' := by simp
  map_mul' := by simp

@[to_additive (attr := simp)]
theorem coe_coeMulHom [∀ i, Monoid (M i)] : (coeMulHom l : ((x : α) → M x) → Product l M) = ofFun :=
  rfl

@[to_additive]
instance instCommMonoid [∀ i, CommMonoid (M i)] : CommMonoid (Product l M) where

instance instNatCast [∀ i, NatCast (M i)] : NatCast (Product l M) where
  natCast n := ofFun fun _ => n

@[simp]
theorem natCast_def [∀ i, NatCast (M i)] (n : ℕ) :
    ((fun _ ↦ n : (x : α) → M x) : Product l M) = n := rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_nat [NatCast M'] (n : ℕ) : ((n : M') : Germ l M') = n := rfl

@[simp, norm_cast]
theorem coe_ofNat [∀ i, NatCast (M i)] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : (x : α) → M x) : Product l M) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_ofNat [NatCast M'] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : M') : Germ l M') = ofNat(n) :=
  rfl

instance instIntCast [∀ i, IntCast (M i)] : IntCast (Product l M) where
  intCast n := ofFun fun _ => n

@[simp]
theorem intCast_def [∀ i, IntCast (M i)] (n : ℤ) :
    ((fun _ ↦ n : (x : α) → M x) : Product l M) = n := rfl

instance instAddMonoidWithOne [∀ i, AddMonoidWithOne (M i)] : AddMonoidWithOne (Product l M) where
  natCast_zero := by simp [← natCast_def, ← coe_zero]
  natCast_succ := by simp [← natCast_def, ← coe_one, ← coe_add]

instance instAddCommMonoidWithOne [∀ i, AddCommMonoidWithOne (M i)] :
    AddCommMonoidWithOne (Product l M) where

@[to_additive] instance instInv [∀ i, Inv (G i)] : Inv (Product l G) where
  inv := map fun _ x => x⁻¹

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [∀ i, Inv (G i)] (f : (x : α) → G x) : ↑f⁻¹ = (f⁻¹ : Product l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem _root_.Filter.Germ.const_inv [Inv G'] (a : G') : (↑(a⁻¹) : Germ l G') = (↑a)⁻¹ :=
  rfl

@[to_additive] instance instDiv [∀ i, Div (M i)] : Div (Product l M) where
  div := map₂ fun _ x y => x / y

@[to_additive (attr := simp, norm_cast)]
theorem coe_div [∀ i, Div (M i)] (f g : (x : α) → M x) : ↑(f / g) = (f / g : Product l M) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem _root_.Filter.Germ.const_div [Div M'] (a b : M') : (↑(a / b) : Germ l M') = ↑a / ↑b :=
  rfl

@[to_additive]
instance instInvolutiveInv [∀ i, InvolutiveInv (G i)] : InvolutiveInv (Product l G) where
  inv_inv a := by induction a using inductionOn with | ofFun a => simp [← coe_inv]

instance instHasDistribNeg [∀ i, Mul (G i)] [∀ i, HasDistribNeg (G i)] :
    HasDistribNeg (Product l G) where
  neg_mul a b := by
    induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_neg, ← coe_mul]
  mul_neg a b := by
    induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_neg, ← coe_mul]

@[to_additive]
instance instInvOneClass [∀ i, InvOneClass (G i)] : InvOneClass (Product l G) where
  inv_one := by simp [← coe_inv, ← coe_one]

@[to_additive instSubNegMonoid]
instance instDivInvMonoid [∀ i, DivInvMonoid (G i)] : DivInvMonoid (Product l G) where
  zpow_zero' a := by induction a using inductionOn with | ofFun a => simp [← coe_pow]
  zpow_succ' n a := by
    induction a using inductionOn with | ofFun a
    simp_rw [← coe_pow, zpow_natCast, pow_succ, coe_mul]
  zpow_neg' n a := by
    induction a using inductionOn with | ofFun a
    simp_rw [← coe_pow, zpow_negSucc, zpow_natCast, coe_inv]
  div_eq_mul_inv a b := by
    induction a, b using inductionOn₂ with | ofFun a b
    simp [← coe_div, ← coe_mul, ← coe_inv, div_eq_mul_inv]

@[to_additive]
instance instDivisionMonoid [∀ i, DivisionMonoid (G i)] : DivisionMonoid (Product l G) where
  mul_inv_rev a b := by
    induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_mul, ← coe_inv]
  inv_eq_of_mul a b := by
    induction a, b using inductionOn₂ with | ofFun a b
    simp_rw [← coe_mul, ← coe_one, ← coe_inv, ofFun_eq]
    intro h
    filter_upwards [h] with x
    rw [Pi.mul_apply, Pi.one_apply, Pi.inv_apply]
    exact inv_eq_of_mul_eq_one_right

@[to_additive]
instance instGroup [∀ i, Group (G i)] : Group (Product l G) where
  inv_mul_cancel a := by induction a using inductionOn with | ofFun a => simp [← coe_mul, ← coe_inv]

@[to_additive]
instance instCommGroup [∀ i, CommGroup (G i)] : CommGroup (Product l G) where

instance instAddGroupWithOne [∀ i, AddGroupWithOne (G i)] : AddGroupWithOne (Product l G) where
  intCast_ofNat := by simp [IntCast.intCast]
  intCast_negSucc := by simp [IntCast.intCast, ← coe_one, ← coe_neg, ← coe_add, ← natCast_def]

end Monoid

section Ring

variable {R : α → Type*}

instance instNontrivial [∀ i, Nontrivial (R i)] [NeBot l] : Nontrivial (Product l R) := by
  choose x y hxy using fun i => exists_pair_ne (R i)
  exact ⟨ofFun x, ofFun y, mt ofFun_eq.1 (not_eventually.2 (.of_forall hxy))⟩

instance instMulZeroClass [∀ i, MulZeroClass (R i)] : MulZeroClass (Product l R) where
  zero_mul a := by induction a using inductionOn with | ofFun a => simp [← coe_zero, ← coe_mul]
  mul_zero a := by induction a using inductionOn with | ofFun a => simp [← coe_zero, ← coe_mul]

instance instMulZeroOneClass [∀ i, MulZeroOneClass (R i)] : MulZeroOneClass (Product l R) where

instance instMonoidWithZero [∀ i, MonoidWithZero (R i)] : MonoidWithZero (Product l R) where

instance instDistrib [∀ i, Distrib (R i)] : Distrib (Product l R) where
  left_distrib a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_add, ← coe_mul, mul_add]
  right_distrib a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_add, ← coe_mul, add_mul]

instance instNonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiring (R i)] :
    NonUnitalNonAssocSemiring (Product l R) where

instance instNonUnitalSemiring [∀ i, NonUnitalSemiring (R i)] :
    NonUnitalSemiring (Product l R) where

instance instNonAssocSemiring [∀ i, NonAssocSemiring (R i)] : NonAssocSemiring (Product l R) where

instance instNonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing (R i)] :
    NonUnitalNonAssocRing (Product l R) where

instance instNonUnitalRing [∀ i, NonUnitalRing (R i)] : NonUnitalRing (Product l R) where

instance instNonAssocRing [∀ i, NonAssocRing (R i)] : NonAssocRing (Product l R) where

instance instSemiring [∀ i, Semiring (R i)] : Semiring (Product l R) where

instance instRing [∀ i, Ring (R i)] : Ring (Product l R) where

instance instNonUnitalCommSemiring [∀ i, NonUnitalCommSemiring (R i)] :
    NonUnitalCommSemiring (Product l R) where

instance instCommSemiring [∀ i, CommSemiring (R i)] : CommSemiring (Product l R) where

instance instNonUnitalCommRing [∀ i, NonUnitalCommRing (R i)] :
    NonUnitalCommRing (Product l R) where

instance instCommRing [∀ i, CommRing (R i)] : CommRing (Product l R) where

/-- Coercion `(α → R) → Germ l R` as a `RingHom`. -/
def coeRingHom [∀ i, Semiring (R i)] (l : Filter α) : ((x : α) → (R x)) →+* Product l R where
  toFun := ofFun
  __ := coeAddHom l
  __ := coeMulHom l

@[simp]
theorem coe_coeRingHom [∀ i, Semiring (R i)] :
    (coeRingHom l : ((x : α) → R x) → Product l R) = ofFun :=
  rfl

end Ring

section Module

variable {R' M' : Type*} {M N R ε : α → Type*}

@[to_additive]
instance instSMul' [∀ i, SMul (M i) (ε i)] : SMul (Product l M) (Product l ε) where
  smul := map₂ fun _ r x => r • x

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul' [∀ i, SMul (M i) (ε i)] (c : (x : α) → M x) (f : (x : α) → ε x) :
    ↑(c • f) = (c : Product l M) • (f : Product l ε) :=
  rfl

@[to_additive]
instance instMulAction [Monoid M'] [∀ i, MulAction M' (ε i)] :
    MulAction M' (Product l ε) where
  one_smul a := by induction a using inductionOn with | ofFun a => simp [← coe_smul]
  mul_smul x y a := by induction a using inductionOn with | ofFun a => simp [← coe_smul, mul_smul]

@[to_additive]
instance instMulAction' [∀ i, Monoid (M i)] [∀ i, MulAction (M i) (ε i)] :
    MulAction (Product l M) (Product l ε) where
  one_smul a := by induction a using inductionOn with | ofFun a => simp [← coe_smul', ← coe_one]
  mul_smul a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp [← coe_smul', ← coe_mul, mul_smul]

instance instDistribMulAction [Monoid M'] [∀ i, AddMonoid (N i)] [∀ i, DistribMulAction M' (N i)] :
    DistribMulAction M' (Product l N) where
  smul_add x a b := by
    induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_add, ← coe_smul]
  smul_zero := by simp [← coe_zero, ← coe_smul]

instance instDistribMulAction' [∀ i, Monoid (M i)] [∀ i, AddMonoid (N i)]
    [∀ i, DistribMulAction (M i) (N i)] : DistribMulAction (Product l M) (Product l N) where
  smul_add a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c => simp [← coe_add, ← coe_smul']
  smul_zero a := by induction a using inductionOn with | ofFun a => simp [← coe_zero, ← coe_smul']

instance instModule [Semiring R'] [∀ i, AddCommMonoid (M i)] [∀ i, Module R' (M i)] :
    Module R' (Product l M) where
  add_smul x y a := by
    induction a using inductionOn with | ofFun a => simp [← coe_smul, ← coe_add, add_smul]
  zero_smul a := by induction a using inductionOn with | ofFun a => simp [← coe_smul]

instance instModule' [∀ i, Semiring (R i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)] :
    Module (Product l R) (Product l M) where
  add_smul a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp [← coe_smul', ← coe_add, add_smul]
  zero_smul a := by induction a using inductionOn with | ofFun a => simp [← coe_smul', ← coe_zero]

end Module

section Order

variable {ε : α → Type*} {f g h : (x : α) → ε x}

instance instLE [∀ i, LE (ε i)] : LE (Product l ε) where
  le := LiftRel fun _ x y => x ≤ y

theorem le_def [∀ i, LE (ε i)] :
    (LE.le : Product l ε → Product l ε → Prop) = LiftRel fun _ x y => x ≤ y :=
  rfl

@[simp]
theorem coe_le [∀ i, LE (ε i)] : (f : Product l ε) ≤ g ↔ ∀ᶠ x in l, f x ≤ g x :=
  Iff.rfl

theorem coe_nonneg [∀ i, LE (ε i)] [∀ i, Zero (ε i)] : 0 ≤ (f : Product l ε) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl

theorem _root_.Filter.Germ.const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  Germ.liftRel_const

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  Germ.liftRel_const_iff

instance instPreorder [∀ i, Preorder (ε i)] : Preorder (Product l ε) where
  le_refl a := by induction a using inductionOn with | ofFun a => simp
  le_trans a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp_rw [coe_le]
    intro h₁ h₂
    filter_upwards [h₁, h₂] with x
    exact le_trans

instance instPartialOrder [∀ i, PartialOrder (ε i)] : PartialOrder (Product l ε) where
  le_antisymm a b := by
    induction a, b using inductionOn₂ with | ofFun a b
    simp_rw [coe_le, ofFun_eq]
    intro h₁ h₂
    filter_upwards [h₁, h₂] with x
    exact le_antisymm

instance instBot [∀ i, Bot (ε i)] : Bot (Product l ε) where bot := ofFun fun _ => ⊥
instance instTop [∀ i, Top (ε i)] : Top (Product l ε) where top := ofFun fun _ => ⊤

@[simp, norm_cast]
theorem coe_bot [∀ i, Bot (ε i)] : (↑(⊥ : (x : α) → ε x) : Product l ε) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem coe_top [∀ i, Top (ε i)] : (↑(⊤ : (x : α) → ε x) : Product l ε) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl

instance instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot_le f := inductionOn f fun _ => Eventually.of_forall fun _ => bot_le

instance instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  le_top f := inductionOn f fun _ => Eventually.of_forall fun _ => le_top

instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where
  __ := instOrderBot
  __ := instOrderTop

instance instSup [∀ i, Max (ε i)] : Max (Product l ε) where max := map₂ fun _ x y => x ⊔ y
instance instInf [∀ i, Min (ε i)] : Min (Product l ε) where min := map₂ fun _ x y => x ⊓ y

@[simp, norm_cast]
theorem coe_sup [∀ i, Max (ε i)] (a b : (x : α) → ε x) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Product l ε) :=
  rfl

@[simp, norm_cast]
theorem coe_inf [∀ i, Min (ε i)] (a b : (x : α) → ε x) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Product l ε) :=
  rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  rfl

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  rfl

instance instSemilatticeSup [∀ i, SemilatticeSup (ε i)] : SemilatticeSup (Product l ε) where
  sup := max
  le_sup_left a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_sup]
  le_sup_right a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_sup]
  sup_le a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp_rw [← coe_sup, coe_le]
    intro h₁ h₂
    filter_upwards [h₁, h₂] with x
    rw [Pi.sup_apply]
    exact sup_le

instance instSemilatticeInf [∀ i, SemilatticeInf (ε i)] : SemilatticeInf (Product l ε) where
  inf := min
  inf_le_left a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_inf]
  inf_le_right a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_inf]
  le_inf a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp_rw [← coe_inf, coe_le]
    intro h₁ h₂
    filter_upwards [h₁, h₂] with x
    rw [Pi.inf_apply]
    exact le_inf

instance instLattice [Lattice β] : Lattice (Germ l β) where

instance instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where
  le_sup_inf a b c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp [← coe_sup, ← coe_inf, sup_inf_left]

@[to_additive]
instance instExistsMulOfLE [∀ i, Mul (ε i)] [∀ i, LE (ε i)] [∀ i, ExistsMulOfLE (ε i)] :
    ExistsMulOfLE (Product l ε) where
  exists_mul_of_le {a b} := by
    induction a, b using inductionOn₂ with | ofFun a b
    rw [coe_le]
    intro hab
    classical
    choose c hc using fun x (hx : a x ≤ b x) ↦ exists_mul_of_le hx
    refine ⟨ofFun fun x ↦ if hx : a x ≤ b x then c x hx else a x, ofFun_eq.2 ?_⟩
    filter_upwards [hab] with x hx
    rw [dite_eq_left hx, hc]

end Order

end Product

end Filter
