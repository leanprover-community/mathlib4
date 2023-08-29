/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Module.Pi

#align_import order.filter.germ from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

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
* `OrderedCancelCommMonoid` and `OrderedCancelAddCommMonoid`.

## Tags

filter, germ
-/


namespace Filter

variable {α β γ δ : Type*} {l : Filter α} {f g h : α → β}

theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ _ in l, a = b) ↔ a = b :=
  eventually_const
#align filter.const_eventually_eq' Filter.const_eventuallyEq'

theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b
#align filter.const_eventually_eq Filter.const_eventuallyEq

theorem EventuallyEq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ}
    (hg : Tendsto g lc l) : f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H
#align filter.eventually_eq.comp_tendsto Filter.EventuallyEq.comp_tendsto

/-- Setoid used to define the space of germs. -/
def germSetoid (l : Filter α) (β : Type*) : Setoid (α → β) where
  r := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩
#align filter.germ_setoid Filter.germSetoid

/-- The space of germs of functions `α → β` at a filter `l`. -/
def Germ (l : Filter α) (β : Type*) : Type _ :=
  Quotient (germSetoid l β)
#align filter.germ Filter.Germ

/-- Setoid used to define the filter product. This is a dependent version of
  `Filter.germSetoid`. -/
def productSetoid (l : Filter α) (ε : α → Type*) : Setoid ((a : _) → ε a) where
  r f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => eventually_of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩
#align filter.product_setoid Filter.productSetoid

/-- The filter product `(a : α) → ε a` at a filter `l`. This is a dependent version of
  `Filter.Germ`. -/
-- Porting note: removed @[protected]
def Product (l : Filter α) (ε : α → Type*) : Type _ :=
  Quotient (productSetoid l ε)
#align filter.product Filter.Product

namespace Product

variable {ε : α → Type*}

instance coeTC : CoeTC ((a : _) → ε a) (l.Product ε) :=
  ⟨@Quotient.mk' _ (productSetoid _ ε)⟩

instance inhabited [(a : _) → Inhabited (ε a)] : Inhabited (l.Product ε) :=
  ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

end Product

namespace Germ

-- Porting note: added
@[coe]
def ofFun : (α → β) → (Germ l β) := @Quotient.mk' _ (germSetoid _ _)

instance : CoeTC (α → β) (Germ l β) :=
  ⟨ofFun⟩

@[coe] -- Porting note: removed `HasLiftT` instance
def const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b

instance coeTC : CoeTC β (Germ l β) :=
  ⟨const⟩

@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl
#align filter.germ.quot_mk_eq_coe Filter.Germ.quot_mk_eq_coe

@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) :
    @Quotient.mk' _ (germSetoid _ _) f = (f : Germ l β) :=
  rfl
#align filter.germ.mk'_eq_coe Filter.Germ.mk'_eq_coe

@[elab_as_elim]
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn' f h
#align filter.germ.induction_on Filter.Germ.inductionOn

@[elab_as_elim]
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h
#align filter.germ.induction_on₂ Filter.Germ.inductionOn₂

@[elab_as_elim]
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H
#align filter.germ.induction_on₃ Filter.Germ.inductionOn₃

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `Germ l β` to `Germ lc δ`. -/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  Quotient.map' F hF
#align filter.germ.map' Filter.Germ.map'

/-- Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def liftOn {γ : Sort*} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF
#align filter.germ.lift_on Filter.Germ.liftOn

@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl
#align filter.germ.map'_coe Filter.Germ.map'_coe

@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''
#align filter.germ.coe_eq Filter.Germ.coe_eq

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq
#align filter.eventually_eq.germ_eq Filter.EventuallyEq.germ_eq

/-- Lift a function `β → γ` to a function `Germ l β → Germ l γ`. -/
def map (op : β → γ) : Germ l β → Germ l γ :=
  map' ((· ∘ ·) op) fun _ _ H => H.mono fun _ H => congr_arg op H
#align filter.germ.map Filter.Germ.map

@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl
#align filter.germ.map_coe Filter.Germ.map_coe

@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  -- ⊢ map id (Quot.mk Setoid.r f) = id (Quot.mk Setoid.r f)
  rfl
  -- 🎉 no goals
#align filter.germ.map_id Filter.Germ.map_id

theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun _ => rfl
#align filter.germ.map_map Filter.Germ.map_map

/-- Lift a binary function `β → γ → δ` to a function `Germ l β → Germ l γ → Germ l δ`. -/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Quotient.map₂' (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]
                                       -- 🎉 no goals
#align filter.germ.map₂ Filter.Germ.map₂

@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl
#align filter.germ.map₂_coe Filter.Germ.map₂_coe

/-- A germ at `l` of maps from `α` to `β` tends to `lb : Filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)
#align filter.germ.tendsto Filter.Germ.Tendsto

@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl
#align filter.germ.coe_tendsto Filter.Germ.coe_tendsto

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto
#align filter.tendsto.germ_tendsto Filter.Tendsto.germ_tendsto

/-- Given two germs `f : Germ l β`, and `g : Germ lc α`, where `l : Filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg
#align filter.germ.comp_tendsto' Filter.Germ.compTendsto'

@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl
#align filter.germ.coe_comp_tendsto' Filter.Germ.coe_compTendsto'

/-- Given a germ `f : Germ l β` and a function `g : γ → α`, where `l : Filter α`, if `g` tends
to `l` along `lc : Filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto
#align filter.germ.comp_tendsto Filter.Germ.compTendsto

@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g :=
  rfl
#align filter.germ.coe_comp_tendsto Filter.Germ.coe_compTendsto

@[simp, nolint simpNF] -- Porting note: simp cannot prove this
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl
#align filter.germ.comp_tendsto'_coe Filter.Germ.compTendsto'_coe
@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq
#align filter.germ.const_inj Filter.Germ.const_inj

@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl
#align filter.germ.map_const Filter.Germ.map_const

@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl
#align filter.germ.map₂_const Filter.Germ.map₂_const

@[simp]
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b :=
  rfl
#align filter.germ.const_comp_tendsto Filter.Germ.const_compTendsto

@[simp]
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg
#align filter.germ.const_comp_tendsto' Filter.Germ.const_compTendsto'

/-- Lift a predicate on `β` to `Germ l β`. -/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun _f _g H =>
    propext <| eventually_congr <| H.mono fun _x hx => hx ▸ Iff.rfl
#align filter.germ.lift_pred Filter.Germ.LiftPred

@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl
#align filter.germ.lift_pred_coe Filter.Germ.liftPred_coe

theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  eventually_of_forall fun _y => hx
#align filter.germ.lift_pred_const Filter.Germ.liftPred_const

@[simp]
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)
#align filter.germ.lift_pred_const_iff Filter.Germ.liftPred_const_iff

/-- Lift a relation `r : β → γ → Prop` to `Germ l β → Germ l γ → Prop`. -/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => ∀ᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl
#align filter.germ.lift_rel Filter.Germ.LiftRel

@[simp]
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl
#align filter.germ.lift_rel_coe Filter.Germ.liftRel_coe

theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  eventually_of_forall fun _ => h
#align filter.germ.lift_rel_const Filter.Germ.liftRel_const

@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)
#align filter.germ.lift_rel_const_iff Filter.Germ.liftRel_const_iff

instance inhabited [Inhabited β] : Inhabited (Germ l β) :=
  ⟨↑(default : β)⟩

section Monoid

variable {M : Type*} {G : Type*}

@[to_additive]
instance mul [Mul M] : Mul (Germ l M) :=
  ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl
#align filter.germ.coe_mul Filter.Germ.coe_mul
#align filter.germ.coe_add Filter.Germ.coe_add

@[to_additive]
instance one [One M] : One (Germ l M) :=
  ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl
#align filter.germ.coe_one Filter.Germ.coe_one
#align filter.germ.coe_zero Filter.Germ.coe_zero

@[to_additive]
instance semigroup [Semigroup M] : Semigroup (Germ l M) :=
  Function.Surjective.semigroup ofFun (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive]
instance commSemigroup [CommSemigroup M] : CommSemigroup (Germ l M) :=
  Function.Surjective.commSemigroup ofFun (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive]
instance leftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) :=
  { Germ.semigroup with
    mul := (· * ·)
    mul_left_cancel := fun f₁ f₂ f₃ =>
      inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
        coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel) }

@[to_additive]
instance rightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) :=
  { Germ.semigroup with
    mul := (· * ·)
    mul_right_cancel := fun f₁ f₂ f₃ =>
      inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
        coe_eq.2 <| (coe_eq.1 H).mono fun _x => mul_right_cancel }

@[to_additive]
instance mulOneClass [MulOneClass M] : MulOneClass (Germ l M) :=
  Function.Surjective.mulOneClass ofFun (surjective_quot_mk _) rfl fun _ _ ↦ rfl

@[to_additive]
instance smul [SMul M G] : SMul M (Germ l G) :=
  ⟨fun n => map (n • ·)⟩

@[to_additive existing smul]
instance pow [Pow G M] : Pow (Germ l G) M :=
  ⟨fun f n => map (· ^ n) f⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = n • (f : Germ l G) :=
  rfl
#align filter.germ.coe_smul Filter.Germ.coe_smul
#align filter.germ.coe_vadd Filter.Germ.coe_vadd

@[to_additive (attr := simp, norm_cast)]
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : Germ l G) :=
  rfl
#align filter.germ.const_smul Filter.Germ.const_smul
#align filter.germ.const_vadd Filter.Germ.const_vadd

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n :=
  rfl
#align filter.germ.coe_pow Filter.Germ.coe_pow

@[to_additive (attr := simp, norm_cast)]
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n :=
  rfl
#align filter.germ.const_pow Filter.Germ.const_pow

@[to_additive]
instance monoid [Monoid M] : Monoid (Germ l M) :=
  Function.Surjective.monoid ofFun (surjective_quot_mk _) rfl (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive "Coercion from functions to germs as an additive monoid homomorphism."]
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M :=
  ⟨⟨ofFun, rfl⟩, fun _ _ => rfl⟩
#align filter.germ.coe_mul_hom Filter.Germ.coeMulHom
#align filter.germ.coe_add_hom Filter.Germ.coeAddHom

@[to_additive (attr := simp)]
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = ofFun :=
  rfl
#align filter.germ.coe_coe_mul_hom Filter.Germ.coe_coeMulHom
#align filter.germ.coe_coe_add_hom Filter.Germ.coe_coeAddHom

@[to_additive]
instance commMonoid [CommMonoid M] : CommMonoid (Germ l M) :=
  Function.Surjective.commMonoid ofFun (surjective_quot_mk _) rfl (fun _ _ => rfl) fun _ _ => rfl

instance [NatCast M] : NatCast (Germ l M) where
  natCast n := (n : α → M)

@[simp]
theorem coe_nat [NatCast M] (n : ℕ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl

@[simp, norm_cast]
theorem const_nat [NatCast M] (n : ℕ) : ((n : M) : Germ l M) = n := rfl

@[simp, norm_cast]
theorem coe_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : α → M) : Germ l M) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem const_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : M) : Germ l M) = OfNat.ofNat n :=
  rfl

instance [IntCast M] : IntCast (Germ l M) where
  intCast n := (n : α → M)

@[simp]
theorem coe_int [IntCast M] (n : ℤ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl

instance addMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) :=
  Function.Surjective.addMonoidWithOne ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ ↦ rfl

instance addCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (Germ l M) where
  toAddMonoidWithOne := addMonoidWithOne
  __ := addCommSemigroup


@[to_additive]
instance inv [Inv G] : Inv (Germ l G) :=
  ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl
#align filter.germ.coe_inv Filter.Germ.coe_inv
#align filter.germ.coe_neg Filter.Germ.coe_neg

@[to_additive (attr := simp, norm_cast)]
theorem const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹ :=
  rfl
#align filter.germ.const_inv Filter.Germ.const_inv
#align filter.germ.const_neg Filter.Germ.const_neg

@[to_additive]
instance div [Div M] : Div (Germ l M) :=
  ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl
#align filter.germ.coe_div Filter.Germ.coe_div
#align filter.germ.coe_sub Filter.Germ.coe_sub

@[to_additive (attr := simp, norm_cast)]
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl
#align filter.germ.const_div Filter.Germ.const_div
#align filter.germ.const_sub Filter.Germ.const_sub

@[to_additive]
instance involutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G) :=
  Function.Surjective.involutiveInv ofFun (surjective_quot_mk _) fun _ ↦ rfl

instance hasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G) :=
  Function.Surjective.hasDistribNeg ofFun (surjective_quot_mk _) (fun _ ↦ rfl) fun _ _ ↦ rfl

@[to_additive]
instance invOneClass [InvOneClass G] : InvOneClass (Germ l G) :=
  ⟨congr_arg ofFun inv_one⟩

@[to_additive subNegMonoid]
instance divInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) :=
  Function.Surjective.divInvMonoid ofFun (surjective_quot_mk _) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance divisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where
  inv_inv := inv_inv
  mul_inv_rev x y := inductionOn₂ x y fun _ _ ↦ congr_arg ofFun <| mul_inv_rev _ _
  inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h ↦ coe_eq.2 <| (coe_eq.1 h).mono fun _ ↦
    DivisionMonoid.inv_eq_of_mul _ _


@[to_additive]
instance group [Group G] : Group (Germ l G) :=
  Function.Surjective.group ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive]
instance commGroup [CommGroup G] : CommGroup (Germ l G) :=
  Function.Surjective.commGroup ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Monoid

section Ring

variable {R : Type*}

instance nontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩
#align filter.germ.nontrivial Filter.Germ.nontrivial

instance mulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R) :=
  Function.Surjective.mulZeroClass ofFun (surjective_quot_mk _) rfl fun _ _ ↦ rfl

instance mulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) :=
  Function.Surjective.mulZeroOneClass ofFun (surjective_quot_mk _) rfl rfl fun _ _ ↦ rfl

instance monoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) :=
  Function.Surjective.monoidWithZero ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

instance distrib [Distrib R] : Distrib (Germ l R) :=
  Function.Surjective.distrib ofFun (surjective_quot_mk _) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Germ l R) :=
  Function.Surjective.nonUnitalNonAssocSemiring ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R) :=
  Function.Surjective.nonUnitalSemiring ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) :=
  Function.Surjective.nonAssocSemiring ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ ↦ rfl

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Germ l R) :=
  Function.Surjective.nonUnitalNonAssocRing ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R) :=
  Function.Surjective.nonUnitalRing ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance nonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) :=
  Function.Surjective.nonAssocRing ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) fun _ ↦ rfl

instance semiring [Semiring R] : Semiring (Germ l R) :=
  Function.Surjective.semiring ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

instance ring [Ring R] : Ring (Germ l R) :=
  Function.Surjective.ring ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl)

instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Germ l R) :=
  Function.Surjective.nonUnitalCommSemiring ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance commSemiring [CommSemiring R] : CommSemiring (Germ l R) :=
  Function.Surjective.commSemiring ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R) :=
    Function.Surjective.nonUnitalCommRing ofFun (surjective_quot_mk _) rfl (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance commRing [CommRing R] : CommRing (Germ l R) :=
  Function.Surjective.commRing ofFun (surjective_quot_mk _) rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl)

/-- Coercion `(α → R) → Germ l R` as a `RingHom`. -/
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := ofFun }
#align filter.germ.coe_ring_hom Filter.Germ.coeRingHom

@[simp]
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = ofFun :=
  rfl
#align filter.germ.coe_coe_ring_hom Filter.Germ.coe_coeRingHom

end Ring

section Module

variable {M N R : Type*}

@[to_additive]
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩
#align filter.germ.has_smul' Filter.Germ.instSMul'
#align filter.germ.has_vadd' Filter.Germ.instVAdd'

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul' [SMul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl
#align filter.germ.coe_smul' Filter.Germ.coe_smul'
#align filter.germ.coe_vadd' Filter.Germ.coe_vadd'

@[to_additive]
instance mulAction [Monoid M] [MulAction M β] : MulAction M (Germ l β) where
  -- Porting note: `rfl` required.
  one_smul f :=
    inductionOn f fun f => by
      norm_cast
      -- ⊢ 1 • f =ᶠ[l] f
      simp only [one_smul]
      -- ⊢ f =ᶠ[l] f
      rfl
      -- 🎉 no goals
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      -- ⊢ (c₁ * c₂) • f =ᶠ[l] c₁ • c₂ • f
      simp only [mul_smul]
      -- ⊢ c₁ • c₂ • f =ᶠ[l] c₁ • c₂ • f
      rfl
      -- 🎉 no goals

@[to_additive]
instance mulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  -- Porting note: `rfl` required.
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
                                          -- 🎉 no goals
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      -- ⊢ (c₁ * c₂) • f =ᶠ[l] c₁ • c₂ • f
      simp only [mul_smul]
      -- ⊢ c₁ • c₂ • f =ᶠ[l] c₁ • c₂ • f
      rfl
      -- 🎉 no goals
#align filter.germ.mul_action' Filter.Germ.mulAction'
#align filter.germ.add_action' Filter.Germ.addAction'

instance distribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction M (Germ l N) where
  -- Porting note: `rfl` required.
  smul_add c f g :=
    inductionOn₂ f g fun f g => by
      norm_cast
      -- ⊢ c • (f + g) =ᶠ[l] c • f + c • g
      simp only [smul_add]
      -- ⊢ c • f + c • g =ᶠ[l] c • f + c • g
                    -- 🎉 no goals
      rfl
      -- 🎉 no goals
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

instance distribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  -- Porting note: `rfl` required.
  smul_add c f g :=
    inductionOn₃ c f g fun c f g => by
      norm_cast
      -- ⊢ c • (f + g) =ᶠ[l] c • f + c • g
      simp only [smul_add]
      -- ⊢ c • f + c • g =ᶠ[l] c • f + c • g
                                           -- 🎉 no goals
      rfl
      -- 🎉 no goals
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]
#align filter.germ.distrib_mul_action' Filter.Germ.distribMulAction'

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M) where
  -- Porting note: `rfl` required.
  add_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      -- ⊢ (c₁ + c₂) • f =ᶠ[l] c₁ • f + c₂ • f
      simp only [add_smul]
      -- ⊢ c₁ • f + c₂ • f =ᶠ[l] c₁ • f + c₂ • f
      rfl
      -- 🎉 no goals
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      -- ⊢ 0 • f =ᶠ[l] 0
      simp only [zero_smul, coe_zero]
      -- ⊢ 0 =ᶠ[l] 0
      rfl
      -- 🎉 no goals

instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module (Germ l R) (Germ l M) where
  -- Porting note: `rfl` required.
  add_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      -- ⊢ (c₁ + c₂) • f =ᶠ[l] c₁ • f + c₂ • f
      simp only [add_smul]
      -- ⊢ c₁ • f + c₂ • f =ᶠ[l] c₁ • f + c₂ • f
      rfl
      -- 🎉 no goals
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]
                                           -- 🎉 no goals
#align filter.germ.module' Filter.Germ.module'

end Module

instance le [LE β] : LE (Germ l β) :=
  ⟨LiftRel (· ≤ ·)⟩

theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl
#align filter.germ.le_def Filter.Germ.le_def

@[simp]
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl
#align filter.germ.coe_le Filter.Germ.coe_le

theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl
#align filter.germ.coe_nonneg Filter.Germ.coe_nonneg

theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  liftRel_const
#align filter.germ.const_le Filter.Germ.const_le

@[simp, norm_cast]
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  liftRel_const_iff
#align filter.germ.const_le_iff Filter.Germ.const_le_iff

instance preorder [Preorder β] : Preorder (Germ l β) where
  le := (· ≤ ·)
  le_refl f := inductionOn f <| EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ => EventuallyLE.trans

instance partialOrder [PartialOrder β] : PartialOrder (Germ l β) :=
  { Filter.Germ.preorder with
    le := (· ≤ ·)
    le_antisymm := fun f g =>
      inductionOn₂ f g fun _ _ h₁ h₂ => (EventuallyLE.antisymm h₁ h₂).germ_eq }

instance bot [Bot β] : Bot (Germ l β) :=
  ⟨↑(⊥ : β)⟩

instance top [Top β] : Top (Germ l β) :=
  ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl
#align filter.germ.const_bot Filter.Germ.const_bot

@[simp, norm_cast]
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl
#align filter.germ.const_top Filter.Germ.const_top

instance orderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot := ⊥
  bot_le f := inductionOn f fun _ => eventually_of_forall fun _ => bot_le

instance orderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  top := ⊤
  le_top f := inductionOn f fun _ => eventually_of_forall fun _ => le_top

instance [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) :=
  { Filter.Germ.orderBot, Filter.Germ.orderTop with }

instance sup [Sup β] : Sup (Germ l β) :=
  ⟨map₂ (· ⊔ ·)⟩

instance inf [Inf β] : Inf (Germ l β) :=
  ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
theorem const_sup [Sup β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  rfl
#align filter.germ.const_sup Filter.Germ.const_sup

@[simp, norm_cast]
theorem const_inf [Inf β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  rfl
#align filter.germ.const_inf Filter.Germ.const_inf

instance semilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) :=
  { Germ.partialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun f g =>
        inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => le_sup_left
    le_sup_right := fun f g =>
      inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => le_sup_right
    sup_le := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp <| h₁.mono fun _x => sup_le }

instance semilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) :=
  { Germ.partialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun f g =>
        inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => inf_le_left
    inf_le_right := fun f g =>
      inductionOn₂ f g fun _f _g => eventually_of_forall fun _x => inf_le_right
    le_inf := fun f₁ f₂ g =>
      inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp <| h₁.mono fun _x => le_inf }

instance lattice [Lattice β] : Lattice (Germ l β) :=
  { Germ.semilatticeSup, Germ.semilatticeInf with }

instance distribLattice [DistribLattice β] : DistribLattice (Germ l β) :=
  { Germ.semilatticeSup, Germ.semilatticeInf with
    le_sup_inf := fun f g h =>
      inductionOn₃ f g h fun _f _g _h => eventually_of_forall fun _ => le_sup_inf }

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid β] : OrderedCommMonoid (Germ l β) :=
  { Germ.partialOrder, Germ.commMonoid with
    mul_le_mul_left := fun f g =>
      inductionOn₂ f g fun _f _g H h =>
        inductionOn h fun _h => H.mono fun _x H => mul_le_mul_left' H _ }

@[to_additive]
instance orderedCancelCommMonoid [OrderedCancelCommMonoid β]  :
    OrderedCancelCommMonoid (Germ l β) :=
  { Germ.orderedCommMonoid with
    le_of_mul_le_mul_left := fun f g h =>
      inductionOn₃ f g h fun _f _g _h H => H.mono fun _x => le_of_mul_le_mul_left' }

@[to_additive]
instance orderedCommGroup [OrderedCommGroup β] : OrderedCommGroup (Germ l β) :=
  { Germ.orderedCancelCommMonoid, Germ.commGroup with }

@[to_additive]
instance existsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l β) where
  exists_mul_of_le {x y} := inductionOn₂ x y fun f g (h : f ≤ᶠ[l] g) ↦ by
    classical
    choose c hc using fun x (hx : f x ≤ g x) ↦ exists_mul_of_le hx
    refine ⟨ofFun <| fun x ↦ if hx : f x ≤ g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx, hc]

@[to_additive]
instance canonicallyOrderedMonoid [CanonicallyOrderedMonoid β] :
    CanonicallyOrderedMonoid (Germ l β) :=
  { orderedCommMonoid, orderBot, existsMulOfLE with
    le_self_mul := fun x y ↦ inductionOn₂ x y fun _ _ ↦ eventually_of_forall fun _ ↦ le_self_mul }

instance orderedSemiring [OrderedSemiring β] : OrderedSemiring (Germ l β) :=
  { Germ.semiring,
    Germ.orderedAddCommMonoid with
    zero_le_one := const_le zero_le_one
    mul_le_mul_of_nonneg_left := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
          hh.mp <| hfg.mono fun _a => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun x y z =>
      inductionOn₃ x y z fun _f _g _h hfg hh =>
          hh.mp <| hfg.mono fun _a => mul_le_mul_of_nonneg_right }

instance orderedCommSemiring [OrderedCommSemiring β] : OrderedCommSemiring (Germ l β) :=
  { Germ.orderedSemiring, Germ.commSemiring with }

instance orderedRing [OrderedRing β] : OrderedRing (Germ l β) :=
  { Germ.ring,
    Germ.orderedAddCommGroup with
    zero_le_one := const_le zero_le_one
    mul_nonneg := fun x y =>
      inductionOn₂ x y fun _f _g hf hg => hg.mp <| hf.mono fun _a => mul_nonneg }

instance orderedCommRing [OrderedCommRing β] : OrderedCommRing (Germ l β) :=
  { Germ.orderedRing, Germ.orderedCommSemiring with }

end Germ

end Filter
