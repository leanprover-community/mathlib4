/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.Data.Quot
import Mathlib.Logic.Relator

#align_import data.quot from "leanprover-community/mathlib"@"6ed6abbde29b8f630001a1b481603f657a3384f1"

/-!
# Quotient types
This module extends the core library's treatment of quotient types (`Init.Core`).
## Tags
quotient
-/

set_option autoImplicit true


variable {α : Sort*} {β : Sort*}

namespace Setoid

#align setoid.r Setoid.r

theorem ext {α : Sort*} : ∀ {s t : Setoid α},
    (∀ a b, @Setoid.r α s a b ↔ @Setoid.r α t a b) → s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
  by have : r = p := funext fun a ↦ funext fun b ↦ propext <| Eq a b
     -- ⊢ { r := r, iseqv := iseqv✝¹ } = { r := p, iseqv := iseqv✝ }
     subst this
     -- ⊢ { r := r, iseqv := iseqv✝¹ } = { r := r, iseqv := iseqv✝ }
     rfl
     -- 🎉 no goals
#align setoid.ext Setoid.ext

end Setoid

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort*}

-- mathport name: mk
@[inherit_doc]
local notation:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
protected theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q

instance (r : α → α → Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩

protected instance Subsingleton [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x ↦ Quot.induction_on x fun _ ↦ Quot.ind fun _ ↦ congr_arg _ (Subsingleton.elim _ _)⟩
#align quot.subsingleton Quot.Subsingleton

/-- Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → HEq (f a₁ b) (f a₂ b))
    (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → HEq (f a b₁) (f a b₂)) :
    φ qa qb :=
  Quot.hrecOn (motive := fun qa ↦ φ qa qb) qa
    (fun a ↦ Quot.hrecOn qb (f a) (fun b₁ b₂ pb ↦ cb pb))
    fun a₁ a₂ pa ↦
      Quot.induction_on qb fun b ↦
        have h₁ : HEq (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)) (f a₁ b) :=
          by simp [heq_self_iff_true]
             -- 🎉 no goals
        have h₂ : HEq (f a₂ b) (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _)) :=
          by simp [heq_self_iff_true]
             -- 🎉 no goals
        (h₁.trans (ca pa)).trans h₂
#align quot.hrec_on₂ Quot.hrecOn₂

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `Quot ra → Quot rb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  (Quot.lift fun x ↦ ⟦f x⟧) fun x y (h₁ : ra x y) ↦ Quot.sound <| h h₁
#align quot.map Quot.map

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `Quot ra → Quot ra'`. -/
protected def mapRight {ra' : α → α → Prop} (h : ∀ a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
    Quot ra → Quot ra' :=
  Quot.map id h
#align quot.map_right Quot.mapRight

/-- Weaken the relation of a quotient. This is the same as `Quot.map id`. -/
def factor {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) : Quot r → Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy ↦ Quot.sound (h x y rxy)
#align quot.factor Quot.factor

theorem factor_mk_eq {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl
#align quot.factor_mk_eq Quot.factor_mk_eq

variable {γ : Sort*} {r : α → α → Prop} {s : β → β → Prop}

-- Porting note: used to be an Alias of `quot.lift_beta`.
theorem lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_beta Quot.lift_mk
#align quot.lift_mk Quot.lift_mk

theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
  Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl
#align quot.lift_on_mk Quot.liftOn_mk

@[simp] theorem surjective_lift {f : α → γ} (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Function.Surjective (lift f h) ↔ Function.Surjective f :=
  ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩
#align quot.surjective_lift Quot.surjective_lift

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
-- porting note: removed `@[elab_as_elim]`, gave "unexpected resulting type γ"
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a ↦ Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha ↦ funext fun q ↦ Quot.induction_on q fun b ↦ hs a₁ a₂ b ha) q₁ q₂
#align quot.lift₂ Quot.lift₂

@[simp]
theorem lift₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    (a : α) (b : β) : Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl
#align quot.lift₂_mk Quot.lift₂_mk

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
-- porting note: removed `@[elab_as_elim]`, gave "unexpected resulting type γ"
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q
#align quot.lift_on₂ Quot.liftOn₂

@[simp]
theorem liftOn₂_mk (a : α) (b : β) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) :
    Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl
#align quot.lift_on₂_mk Quot.liftOn₂_mk

variable {t : γ → γ → Prop}

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` with values in a quotient of
`γ`. -/
protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b ↦ Quot.mk t <| f a b) (fun a b₁ b₂ hb ↦ Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha ↦ Quot.sound (hs a₁ a₂ b ha)) q₁ q₂
#align quot.map₂ Quot.map₂

@[simp]
theorem map₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl
#align quot.map₂_mk Quot.map₂_mk

/-- A binary version of `Quot.recOnSubsingleton`. -/
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort*}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quot.recOnSubsingleton _ r (fun q ↦ φ q q₂)
    (fun a ↦ Quot.ind (β := λ b => Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a ↦ Quot.recOnSubsingleton q₂ fun b ↦ f a b
#align quot.rec_on_subsingleton₂ Quot.recOnSubsingleton₂

@[elab_as_elim]
protected theorem induction_on₂ {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (β := λ a => δ a q₂) (fun a₁ ↦ Quot.ind (fun a₂ ↦ h a₁ a₂) q₂) q₁
#align quot.induction_on₂ Quot.induction_on₂

@[elab_as_elim]
protected theorem induction_on₃ {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r)
    (q₂ : Quot s) (q₃ : Quot t) (h : ∀ a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) :
    δ q₁ q₂ q₃ :=
  Quot.ind (β := λ a => δ a q₂ q₃) (fun a₁ ↦ Quot.ind (β := λ b => δ _ b q₃)
    (fun a₂ ↦ Quot.ind (fun a₃ ↦ h a₁ a₂ a₃) q₃) q₂) q₁
#align quot.induction_on₃ Quot.induction_on₃

instance lift.decidablePred (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) :=
  fun q ↦ Quot.recOnSubsingleton (motive := λ _ => Decidable _) q hf

/-- Note that this provides `DecidableRel (Quot.Lift₂ f ha hb)` when `α = β`. -/
instance lift₂.decidablePred (r : α → α → Prop) (s : β → β → Prop) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [hf : ∀ a, DecidablePred (f a)] (q₁ : Quot r) :
    DecidablePred (Quot.lift₂ f ha hb q₁) :=
  fun q₂ ↦ Quot.recOnSubsingleton₂ q₁ q₂ hf

instance (r : α → α → Prop) (q : Quot r) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [DecidablePred f] :
    Decidable (Quot.liftOn q f h) :=
  Quot.lift.decidablePred _ _ _ _

instance (r : α → α → Prop) (s : β → β → Prop) (q₁ : Quot r) (q₂ : Quot s) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [∀ a, DecidablePred (f a)] :
    Decidable (Quot.liftOn₂ q₁ q₂ f ha hb) :=
  Quot.lift₂.decidablePred _ _ _ _ _ _ _

end Quot

namespace Quotient

variable [sa : Setoid α] [sb : Setoid β]

variable {φ : Quotient sa → Quotient sb → Sort*}

-- Porting note: in mathlib3 this notation took the Setoid as an instance-implicit argument,
-- now it's explicit but left as a metavariable.
-- We have not yet decided which one works best, since the setoid instance can't always be
-- reliably found but it can't always be inferred from the expected type either.
-- See also: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
@[inherit_doc]
notation:arg "⟦" a "⟧" => Quotient.mk _ a

instance instInhabitedQuotient (s : Setoid α) [Inhabited α] : Inhabited (Quotient s) :=
  ⟨⟦default⟧⟩

instance instSubsingletonQuotient (s : Setoid α) [Subsingleton α] : Subsingleton (Quotient s) :=
  Quot.Subsingleton

instance {α : Type*} [Setoid α] : IsEquiv α (· ≈ ·) where
  refl := Setoid.refl
  symm _ _ := Setoid.symm
  trans _ _ _ := Setoid.trans

/-- Induction on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quotient sa) (qb : Quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun p ↦ c _ _ _ _ p (Setoid.refl _)) fun p ↦ c _ _ _ _ (Setoid.refl _) p
#align quotient.hrec_on₂ Quotient.hrecOn₂

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) : Quotient sa → Quotient sb :=
  Quot.map f h
#align quotient.map Quotient.map

@[simp]
theorem map_mk (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl
#align quotient.map_mk Quotient.map_mk

variable {γ : Sort*} [sc : Setoid γ]

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y ↦ ⟦f x y⟧) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂
#align quotient.map₂ Quotient.map₂

@[simp]
theorem map₂_mk (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  rfl
#align quotient.map₂_mk Quotient.map₂_mk

instance lift.decidablePred (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    DecidablePred (Quotient.lift f h) :=
  Quot.lift.decidablePred _ _ _

/-- Note that this provides `DecidableRel (Quotient.lift₂ f h)` when `α = β`. -/
instance lift₂.decidablePred (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    [hf : ∀ a, DecidablePred (f a)]
    (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ f h q₁) :=
  fun q₂ ↦ Quotient.recOnSubsingleton₂ q₁ q₂ hf

instance (q : Quotient sa) (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    Decidable (Quotient.liftOn q f h) :=
  Quotient.lift.decidablePred _ _ _

instance (q₁ : Quotient sa) (q₂ : Quotient sb) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

theorem Quot.eq {α : Type*} {r : α → α → Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ EqvGen r x y :=
  ⟨Quot.exact r, Quot.EqvGen_sound⟩
#align quot.eq Quot.eq

@[simp]
theorem Quotient.eq [r : Setoid α] {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem forall_quotient_iff {α : Type*} [r : Setoid α] {p : Quotient r → Prop} :
    (∀ a : Quotient r, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  ⟨fun h _ ↦ h _, fun h a ↦ a.induction_on h⟩
#align forall_quotient_iff forall_quotient_iff

@[simp]
theorem Quotient.lift_mk [s : Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk s x) = f x :=
rfl
#align quotient.lift_mk Quotient.lift_mk

@[simp]
theorem Quotient.lift_comp_mk [Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk _ = f :=
  rfl
#align quotient.lift_comp_mk Quotient.lift_comp_mk

@[simp]
theorem Quotient.lift₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} [Setoid α] [Setoid β]
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h (Quotient.mk _ a) (Quotient.mk _ b) = f a b :=
  rfl
#align quotient.lift₂_mk Quotient.lift₂_mk

theorem Quotient.liftOn_mk [s : Setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.liftOn (Quotient.mk s x) f h = f x :=
  rfl
#align quotient.lift_on_mk Quotient.liftOn_mk

@[simp]
theorem Quotient.liftOn₂_mk {α : Sort*} {β : Sort*} [Setoid α] (f : α → α → β)
    (h : ∀ a₁ a₂ b₁ b₂ : α, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x y : α) :
    Quotient.liftOn₂ (Quotient.mk _ x) (Quotient.mk _ y) f h = f x y :=
  rfl
#align quotient.lift_on₂_mk Quotient.liftOn₂_mk

/-- `Quot.mk r` is a surjective function. -/
theorem surjective_quot_mk (r : α → α → Prop) : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep
#align surjective_quot_mk surjective_quot_mk

/-- `Quotient.mk` is a surjective function. -/
theorem surjective_quotient_mk (α : Sort*) [s : Setoid α] :
    Function.Surjective (Quotient.mk _ : α → Quotient s) :=
  Quot.exists_rep
#align surjective_quotient_mk surjective_quotient_mk

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)
#align quot.out Quot.out

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
unsafe def Quot.unquot {r : α → α → Prop} : Quot r → α :=
  cast lcProof -- porting notes: was `unchecked_cast` before, which unfolds to `cast undefined`

@[simp]
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)
#align quot.out_eq Quot.out_eq

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quotient.out [s : Setoid α] : Quotient s → α :=
  Quot.out
#align quotient.out Quotient.out

@[simp]
theorem Quotient.out_eq [s : Setoid α] (q : Quotient s) : ⟦q.out⟧ = q :=
  Quot.out_eq q
#align quotient.out_eq Quotient.out_eq

theorem Quotient.mk_out [Setoid α] (a : α) : ⟦a⟧.out ≈ a :=
  Quotient.exact (Quotient.out_eq _)
#align quotient.mk_out Quotient.mk_out

theorem Quotient.mk_eq_iff_out [s : Setoid α] {x : α} {y : Quotient s} :
    ⟦x⟧ = y ↔ x ≈ Quotient.out y := by
  refine' Iff.trans _ Quotient.eq
  -- ⊢ Quotient.mk s x = y ↔ Quotient.mk s x = Quotient.mk s (out y)
  rw [Quotient.out_eq y]
  -- 🎉 no goals
#align quotient.mk_eq_iff_out Quotient.mk_eq_iff_out

theorem Quotient.eq_mk_iff_out [s : Setoid α] {x : Quotient s} {y : α} :
    x = ⟦y⟧ ↔ Quotient.out x ≈ y := by
  refine' Iff.trans _ Quotient.eq
  -- ⊢ x = Quotient.mk s y ↔ Quotient.mk s (out x) = Quotient.mk s y
  rw [Quotient.out_eq x]
  -- 🎉 no goals
#align quotient.eq_mk_iff_out Quotient.eq_mk_iff_out

@[simp]
theorem Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : x.out ≈ y.out ↔ x = y := by
  rw [← Quotient.eq_mk_iff_out, Quotient.out_eq]
  -- 🎉 no goals
#align quotient.out_equiv_out Quotient.out_equiv_out

theorem Quotient.out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
  fun _ _ h ↦ Quotient.out_equiv_out.1 <| h ▸ Setoid.refl _
#align quotient.out_injective Quotient.out_injective

@[simp]
theorem Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y :=
  ⟨fun h ↦ Quotient.out_injective h, fun h ↦ h ▸ rfl⟩
#align quotient.out_inj Quotient.out_inj

section Pi

instance piSetoid {ι : Sort*} {α : ι → Sort*} [∀ i, Setoid (α i)] : Setoid (∀ i, α i) where
  r a b := ∀ i, a i ≈ b i
  iseqv := ⟨fun _ _ ↦ Setoid.refl _,
            fun h _ ↦ Setoid.symm (h _),
            fun h₁ h₂ _ ↦ Setoid.trans (h₁ _) (h₂ _)⟩

/-- Given a function `f : Π i, Quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
noncomputable def Quotient.choice {ι : Type*} {α : ι → Type*} [S : ∀ i, Setoid (α i)]
    (f : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) (by infer_instance) :=
                             -- 🎉 no goals
  ⟦fun i ↦ (f i).out⟧
#align quotient.choice Quotient.choice

@[simp]
theorem Quotient.choice_eq {ι : Type*} {α : ι → Type*} [∀ i, Setoid (α i)] (f : ∀ i, α i) :
    (Quotient.choice fun i ↦ ⟦f i⟧) = ⟦f⟧ :=
  Quotient.sound fun _ ↦ Quotient.mk_out _
#align quotient.choice_eq Quotient.choice_eq

@[elab_as_elim]
theorem Quotient.induction_on_pi {ι : Type*} {α : ι → Sort*} [s : ∀ i, Setoid (α i)]
    {p : (∀ i, Quotient (s i)) → Prop} (f : ∀ i, Quotient (s i))
    (h : ∀ a : ∀ i, α i, p fun i ↦ ⟦a i⟧) : p f := by
  rw [← (funext fun i ↦ Quotient.out_eq (f i) : (fun i ↦ ⟦(f i).out⟧) = f)]
  -- ⊢ p fun i => Quotient.mk (s i) (out (f i))
  apply h
  -- 🎉 no goals
#align quotient.induction_on_pi Quotient.induction_on_pi

end Pi

theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ ↦ Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ ↦ ⟨⟦a⟧⟩⟩
#align nonempty_quotient_iff nonempty_quotient_iff

/-! ### Truncation -/


theorem true_equivalence : @Equivalence α fun _ _ ↦ True :=
  ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩
#align true_equivalence true_equivalence

/-- Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`. -/
def trueSetoid : Setoid α :=
  ⟨_, true_equivalence⟩
#align true_setoid trueSetoid

/-- `Trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `Nonempty α`, but unlike `Nonempty α`, `Trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quotient α trueSetoid
#align trunc Trunc

namespace Trunc

/-- Constructor for `Trunc α` -/
def mk (a : α) : Trunc α :=
  Quot.mk _ a
#align trunc.mk Trunc.mk

instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : Trunc α → β :=
  Quot.lift f fun a b _ ↦ c a b
#align trunc.lift Trunc.lift

theorem ind {β : Trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : Trunc α, β q :=
  Quot.ind
#align trunc.ind Trunc.ind

protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl
#align trunc.lift_mk Trunc.lift_mk

/-- Lift a constant function on `q : Trunc α`. -/
-- porting note: removed `@[elab_as_elim]` because it gave "unexpected eliminator resulting type"
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn (q : Trunc α) (f : α → β) (c : ∀ a b : α, f a = f b) : β :=
  lift f c q
#align trunc.lift_on Trunc.liftOn

@[elab_as_elim]
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  ind h q
#align trunc.induction_on Trunc.induction_on

theorem exists_rep (q : Trunc α) : ∃ a : α, mk a = q :=
  Quot.exists_rep q
#align trunc.exists_rep Trunc.exists_rep

@[elab_as_elim]
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ ↦ Trunc.induction_on q₂ (h a₁)
#align trunc.induction_on₂ Trunc.induction_on₂

protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun _ _ ↦ Quot.sound trivial
#align trunc.eq Trunc.eq

instance instSubsingletonTrunc : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

/-- The `bind` operator for the `Trunc` monad. -/
def bind (q : Trunc α) (f : α → Trunc β) : Trunc β :=
  Trunc.liftOn q f fun _ _ ↦ Trunc.eq _ _
#align trunc.bind Trunc.bind

/-- A function `f : α → β` defines a function `map f : Trunc α → Trunc β`. -/
def map (f : α → β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)
#align trunc.map Trunc.map

instance : Monad Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind

instance : LawfulMonad Trunc where
  id_map _ := Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  -- porting note: the fields below are new in Lean 4
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

variable {C : Trunc α → Sort*}

/-- Recursion/induction principle for `Trunc`. -/
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def rec (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
    (q : Trunc α) : C q :=
  Quot.rec f (fun a b _ ↦ h a b) q
#align trunc.rec Trunc.rec

/-- A version of `Trunc.rec` taking `q : Trunc α` as the first argument. -/
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOn (q : Trunc α) (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q
#align trunc.rec_on Trunc.recOn

/-- A version of `Trunc.recOn` assuming the codomain is a `Subsingleton`. -/
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOnSubsingleton [∀ a, Subsingleton (C (mk a))] (q : Trunc α) (f : ∀ a, C (mk a)) :
    C q :=
  Trunc.rec f (fun _ b ↦ Subsingleton.elim _ (f b)) q
#align trunc.rec_on_subsingleton Trunc.recOnSubsingleton

/-- Noncomputably extract a representative of `Trunc α` (using the axiom of choice). -/
noncomputable def out : Trunc α → α :=
  Quot.out
#align trunc.out Trunc.out

@[simp]
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _
#align trunc.out_eq Trunc.out_eq

protected theorem nonempty (q : Trunc α) : Nonempty α :=
  nonempty_of_exists q.exists_rep
#align trunc.nonempty Trunc.nonempty

end Trunc

/-! ### `Quotient` with implicit `Setoid` -/


namespace Quotient

variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `Setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/

-- TODO: this whole section can probably be replaced `Quotient.mk`, with explicit parameter

-- porting note: Quotient.mk' is the equivalent of Lean 3's `Quotient.mk`
/-- A version of `Quotient.mk` taking `{s : Setoid α}` as an implicit argument instead of an
instance argument. -/
protected def mk'' (a : α) : Quotient s₁ :=
  Quot.mk s₁.1 a
#align quotient.mk Quotient.mk'
#align quotient.mk' Quotient.mk''

/-- `Quotient.mk''` is a surjective function. -/
theorem surjective_Quotient_mk'' : Function.Surjective (Quotient.mk'' : α → Quotient s₁) :=
  Quot.exists_rep
#align quotient.surjective_quotient_mk' Quotient.surjective_Quotient_mk''

/-- A version of `Quotient.liftOn` taking `{s : Setoid α}` as an implicit argument instead of an
instance argument. -/
-- porting note: removed `@[elab_as_elim]` because it gave "unexpected eliminator resulting type"
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn' (q : Quotient s₁) (f : α → φ) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b) :
    φ :=
  Quotient.liftOn q f h
#align quotient.lift_on' Quotient.liftOn'

@[simp]
protected theorem liftOn'_mk'' (f : α → φ) (h) (x : α) :
    Quotient.liftOn' (@Quotient.mk'' _ s₁ x) f h = f x :=
  rfl

@[simp] lemma surjective_liftOn' {f : α → φ} (h) :
    Function.Surjective (λ x : Quotient s₁ => x.liftOn' f h) ↔ Function.Surjective f :=
  Quot.surjective_lift _
#align quotient.surjective_lift_on' Quotient.surjective_liftOn'

/-- A version of `Quotient.liftOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit arguments
instead of instance arguments. -/
-- porting note: removed `@[elab_as_elim]` because it gave "unexpected eliminator resulting type"
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn₂' (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → γ)
    (h : ∀ a₁ a₂ b₁ b₂, @Setoid.r α s₁ a₁ b₁ → @Setoid.r β s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
  Quotient.liftOn₂ q₁ q₂ f h
#align quotient.lift_on₂' Quotient.liftOn₂'

@[simp]
protected theorem liftOn₂'_mk'' (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (@Quotient.mk'' _ s₁ a) (@Quotient.mk'' _ s₂ b) f h = f a b :=
  rfl

/-- A version of `Quotient.ind` taking `{s : Setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_elim]
protected theorem ind' {p : Quotient s₁ → Prop} (h : ∀ a, p (Quotient.mk'' a)) (q : Quotient s₁) :
    p q :=
  Quotient.ind h q
#align quotient.ind' Quotient.ind'

/-- A version of `Quotient.ind₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_elim]
protected theorem ind₂' {p : Quotient s₁ → Quotient s₂ → Prop}
    (h : ∀ a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂))
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) : p q₁ q₂ :=
  Quotient.ind₂ h q₁ q₂
#align quotient.ind₂' Quotient.ind₂'

/-- A version of `Quotient.inductionOn` taking `{s : Setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_elim]
protected theorem inductionOn' {p : Quotient s₁ → Prop} (q : Quotient s₁)
    (h : ∀ a, p (Quotient.mk'' a)) : p q :=
  Quotient.inductionOn q h
#align quotient.induction_on' Quotient.inductionOn'

/-- A version of `Quotient.inductionOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_elim]
protected theorem inductionOn₂' {p : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (h : ∀ a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂)) : p q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h
#align quotient.induction_on₂' Quotient.inductionOn₂'

/-- A version of `Quotient.inductionOn₃` taking `{s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
protected theorem inductionOn₃' {p : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃)
    (h : ∀ a₁ a₂ a₃, p (Quotient.mk'' a₁) (Quotient.mk'' a₂) (Quotient.mk'' a₃)) :
    p q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h
#align quotient.induction_on₃' Quotient.inductionOn₃'

/-- A version of `Quotient.recOnSubsingleton` taking `{s₁ : Setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_elim]
protected def recOnSubsingleton' {φ : Quotient s₁ → Sort*} [∀ a, Subsingleton (φ ⟦a⟧)]
    (q : Quotient s₁)
    (f : ∀ a, φ (Quotient.mk'' a)) : φ q :=
  Quotient.recOnSubsingleton q f
#align quotient.rec_on_subsingleton' Quotient.recOnSubsingleton'

/-- A version of `Quotient.recOnSubsingleton₂` taking `{s₁ : Setoid α} {s₂ : Setoid α}`
as implicit arguments instead of instance arguments. -/
-- porting note: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOnSubsingleton₂' {φ : Quotient s₁ → Quotient s₂ → Sort*}
    [∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : ∀ a₁ a₂, φ (Quotient.mk'' a₁) (Quotient.mk'' a₂)) :
    φ q₁ q₂ :=
  Quotient.recOnSubsingleton₂ q₁ q₂ f
#align quotient.rec_on_subsingleton₂' Quotient.recOnSubsingleton₂'

/-- Recursion on a `Quotient` argument `a`, result type depends on `⟦a⟧`. -/
protected def hrecOn' {φ : Quotient s₁ → Sort*} (qa : Quotient s₁) (f : ∀ a, φ (Quotient.mk'' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂)) : φ qa :=
  Quot.hrecOn qa f c
#align quotient.hrec_on' Quotient.hrecOn'

@[simp]
theorem hrecOn'_mk'' {φ : Quotient s₁ → Sort*} (f : ∀ a, φ (Quotient.mk'' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → HEq (f a₁) (f a₂))
    (x : α) : (Quotient.mk'' x).hrecOn' f c = f x :=
  rfl
#align quotient.hrec_on'_mk' Quotient.hrecOn'_mk''

/-- Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂' {φ : Quotient s₁ → Quotient s₂ → Sort*} (qa : Quotient s₁)
    (qb : Quotient s₂) (f : ∀ a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) :
    φ qa qb :=
  Quotient.hrecOn₂ qa qb f c
#align quotient.hrec_on₂' Quotient.hrecOn₂'

@[simp]
theorem hrecOn₂'_mk'' {φ : Quotient s₁ → Quotient s₂ → Sort*}
    (f : ∀ a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) (x : α) (qb : Quotient s₂) :
    (Quotient.mk'' x).hrecOn₂' qb f c = qb.hrecOn' (f x) fun _ _ ↦ c _ _ _ _ (Setoid.refl _) :=
  rfl
#align quotient.hrec_on₂'_mk' Quotient.hrecOn₂'_mk''

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients. -/
protected def map' (f : α → β) (h : (s₁.r ⇒ s₂.r) f f) : Quotient s₁ → Quotient s₂ :=
  Quot.map f h
#align quotient.map' Quotient.map'

@[simp]
theorem map'_mk'' (f : α → β) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂) :=
  rfl

/-- A version of `Quotient.map₂` using curly braces and unification. -/
protected def map₂' (f : α → β → γ) (h : (s₁.r ⇒ s₂.r ⇒ s₃.r) f f) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.map₂ f h
#align quotient.map₂' Quotient.map₂'

@[simp]
theorem map₂'_mk'' (f : α → β → γ) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map₂' f h =
      (Quotient.map' (f x) (h (Setoid.refl x)) : Quotient s₂ → Quotient s₃) :=
  rfl

theorem exact' {a b : α} :
    (Quotient.mk'' a : Quotient s₁) = Quotient.mk'' b → @Setoid.r _ s₁ a b :=
  Quotient.exact
#align quotient.exact' Quotient.exact'

theorem sound' {a b : α} : @Setoid.r _ s₁ a b → @Quotient.mk'' α s₁ a = Quotient.mk'' b :=
  Quotient.sound
#align quotient.sound' Quotient.sound'

@[simp]
protected theorem eq' [s₁ : Setoid α] {a b : α} :
    @Quotient.mk' α s₁ a = @Quotient.mk' α s₁ b ↔ @Setoid.r _ s₁ a b :=
  Quotient.eq
#align quotient.eq Quotient.eq'

@[simp]
protected theorem eq'' {a b : α} : @Quotient.mk'' α s₁ a = Quotient.mk'' b ↔ @Setoid.r _ s₁ a b :=
  Quotient.eq
#align quotient.eq' Quotient.eq''

/-- A version of `Quotient.out` taking `{s₁ : Setoid α}` as an implicit argument instead of an
instance argument. -/
noncomputable def out' (a : Quotient s₁) : α :=
  Quotient.out a
#align quotient.out' Quotient.out'

@[simp]
theorem out_eq' (q : Quotient s₁) : Quotient.mk'' q.out' = q :=
  q.out_eq
#align quotient.out_eq' Quotient.out_eq'

theorem mk_out' (a : α) : @Setoid.r α s₁ (Quotient.mk'' a : Quotient s₁).out' a :=
  Quotient.exact (Quotient.out_eq _)
#align quotient.mk_out' Quotient.mk_out'

section

variable [s : Setoid α]

protected theorem mk''_eq_mk (x : α) : Quotient.mk'' x = Quotient.mk s x :=
  rfl

@[simp]
protected theorem liftOn'_mk (x : α) (f : α → β) (h) : (Quotient.mk s x).liftOn' f h = f x :=
  rfl
#align quotient.lift_on'_mk Quotient.liftOn'_mk

@[simp]
protected theorem liftOn₂'_mk [t : Setoid β] (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (Quotient.mk s a) (Quotient.mk t b) f h = f a b :=
  Quotient.liftOn₂'_mk'' _ _ _ _
#align quotient.lift_on₂'_mk Quotient.liftOn₂'_mk

@[simp]
theorem map'_mk [t : Setoid β] (f : α → β) (h) (x : α) :
    (Quotient.mk s x).map' f h = (Quotient.mk t (f x)) :=
  rfl
#align quotient.map'_mk Quotient.map'_mk

end

instance (q : Quotient s₁) (f : α → Prop) (h : ∀ a b, @Setoid.r α s₁ a b → f a = f b)
    [DecidablePred f] :
    Decidable (Quotient.liftOn' q f h) :=
  Quotient.lift.decidablePred _ _ q

instance (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, @Setoid.r α s₁ a₁ a₂ → @Setoid.r β s₂ b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂' q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ h _ _

end Quotient
