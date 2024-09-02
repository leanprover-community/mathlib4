/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yuyang Zhao
-/
import Mathlib.Init.Data.Quot
import Mathlib.Logic.Relator
import Mathlib.Logic.Unique
import Mathlib.Util.Notation3

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`Init.Core`).

## Tags

quotient
-/

variable {α : Sort*} {β : Sort*}

namespace Setoid

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``Setoid.r
    (some { numArgs := 2, coercee := 1, type := .coeFun })

instance : CoeFun (Setoid α) (fun _ ↦ α → α → Prop) where
  coe := @Setoid.r _

lemma equiv_iff_apply {r : Setoid α} {a b : α} : a ≈ b ↔ r a b :=
  Iff.rfl

instance decidableRel (r : Setoid α) [h : DecidableRel r.r] : DecidableRel r :=
  h

instance [r : Setoid α] [h : DecidableRel (α := α) (· ≈ ·)] : DecidableRel r :=
  h

@[ext]
theorem ext : ∀ {r s : Setoid α}, (∀ a b, r a b ↔ s a b) → r = s
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
  by have : r = p := funext fun a ↦ funext fun b ↦ propext <| Eq a b
     subst this
     rfl

end Setoid

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort*}

@[inherit_doc Quot.mk]
local notation3:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
protected theorem induction_on {α : Sort*} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q

instance (r : α → α → Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩

protected instance Subsingleton [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x ↦ Quot.induction_on x fun _ ↦ Quot.ind fun _ ↦ congr_arg _ (Subsingleton.elim _ _)⟩

@[deprecated (since := "2024-08-26")] alias recOn' := Quot.recOn
@[deprecated (since := "2024-08-26")] alias recOnSubsingleton' := Quot.recOnSubsingleton

instance [Unique α] : Unique (Quot ra) := Unique.mk' _

/-- Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → HEq (f a₁ b) (f a₂ b))
    (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → HEq (f a b₁) (f a b₂)) :
    φ qa qb :=
  Quot.hrecOn (motive := fun qa ↦ φ qa qb) qa
    (fun a ↦ Quot.hrecOn qb (f a) (fun b₁ b₂ pb ↦ cb pb))
    fun a₁ a₂ pa ↦
      Quot.induction_on qb fun b ↦
        have h₁ : HEq (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _)) (f a₁ b) := by
          simp [heq_self_iff_true]
        have h₂ : HEq (f a₂ b) (@Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _)) := by
          simp [heq_self_iff_true]
        (h₁.trans (ca pa)).trans h₂

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `Quot ra → Quot rb`. -/
protected def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  (Quot.lift fun x ↦ ⟦f x⟧) fun x y (h₁ : ra x y) ↦ Quot.sound <| h h₁

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `Quot ra → Quot ra'`. -/
protected def mapRight {ra' : α → α → Prop} (h : ∀ a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
    Quot ra → Quot ra' :=
  Quot.map id h

/-- Weaken the relation of a quotient. This is the same as `Quot.map id`. -/
def factor {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) : Quot r → Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy ↦ Quot.sound (h x y rxy)

theorem factor_mk_eq {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl

variable {γ : Sort*} {r : α → α → Prop} {s : β → β → Prop}

-- Porting note: used to be an Alias of `Quot.lift_mk`.
theorem lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl

theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl

@[simp] theorem surjective_lift {f : α → γ} (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Function.Surjective (lift f h) ↔ Function.Surjective f :=
  ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
-- Porting note: removed `@[elab_as_elim]`, gave "unexpected resulting type γ"
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a ↦ Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha ↦ funext fun q ↦ Quot.induction_on q fun b ↦ hs a₁ a₂ b ha) q₁ q₂

@[simp]
theorem lift₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    (a : α) (b : β) : Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
-- porting note (#11083): removed `@[elab_as_elim]`, gave "unexpected resulting type γ"
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q

@[simp]
theorem liftOn₂_mk (a : α) (b : β) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) :
    Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl

variable {t : γ → γ → Prop}

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` with values in a quotient of
`γ`. -/
protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b ↦ Quot.mk t <| f a b) (fun a b₁ b₂ hb ↦ Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha ↦ Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
theorem map₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl

/-- A binary version of `Quot.recOnSubsingleton`. -/
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort*}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quot.recOnSubsingleton _ r (fun q ↦ φ q q₂)
    (fun a ↦ Quot.ind (β := fun b ↦ Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a ↦ Quot.recOnSubsingleton q₂ fun b ↦ f a b

@[elab_as_elim]
protected theorem induction_on₂ {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (β := fun a ↦ δ a q₂) (fun a₁ ↦ Quot.ind (fun a₂ ↦ h a₁ a₂) q₂) q₁

@[elab_as_elim]
protected theorem induction_on₃ {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r)
    (q₂ : Quot s) (q₃ : Quot t) (h : ∀ a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) :
    δ q₁ q₂ q₃ :=
  Quot.ind (β := fun a ↦ δ a q₂ q₃) (fun a₁ ↦ Quot.ind (β := fun b ↦ δ _ b q₃)
    (fun a₂ ↦ Quot.ind (fun a₃ ↦ h a₁ a₂ a₃) q₃) q₂) q₁

instance lift.decidablePred (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) :=
  fun q ↦ Quot.recOnSubsingleton (motive := fun _ ↦ Decidable _) q hf

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

variable {sa : Setoid α} {sb : Setoid β}
variable {φ : Quotient sa → Quotient sb → Sort*}

-- Porting note: in mathlib3 this notation took the Setoid as an instance-implicit argument,
-- now it's explicit but left as a metavariable.
-- We have not yet decided which one works best, since the setoid instance can't always be
-- reliably found but it can't always be inferred from the expected type either.
-- See also: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
@[inherit_doc Quotient.mk]
notation3:arg "⟦" a "⟧" => Quotient.mk _ a

instance instInhabitedQuotient (s : Setoid α) [Inhabited α] : Inhabited (Quotient s) :=
  ⟨⟦default⟧⟩

instance instSubsingletonQuotient (s : Setoid α) [Subsingleton α] : Subsingleton (Quotient s) :=
  Quot.Subsingleton

instance instUniqueQuotient (s : Setoid α) [Unique α] : Unique (Quotient s) := Unique.mk' _

instance {α : Type*} [Setoid α] : IsEquiv α (· ≈ ·) where
  refl := Setoid.refl
  symm _ _ := Setoid.symm
  trans _ _ _ := Setoid.trans

instance {α : Type*} (s : Setoid α) : IsEquiv α s where
  refl := Setoid.refl
  symm _ _ := Setoid.symm
  trans _ _ _ := Setoid.trans

/-- Induction on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
protected def hrecOn₂ (qa : Quotient sa) (qb : Quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, sa a₁ a₂ → sb b₁ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun p ↦ c _ _ _ _ p (Setoid.refl _)) fun p ↦ c _ _ _ _ (Setoid.refl _) p

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : (sa ⇒ sb) f f) : Quotient sa → Quotient sb :=
  Quot.map f h

@[simp]
theorem map_mk (f : α → β) (h : (sa ⇒ sb) f f) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl

variable {γ : Sort*} {sc : Setoid γ}

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ) (h : (sa ⇒ sb ⇒ sc) f f) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y ↦ ⟦f x y⟧) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂

@[simp]
theorem map₂_mk (f : α → β → γ) (h : (sa ⇒ sb ⇒ sc) f f) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  rfl

instance lift.decidablePred (f : α → Prop) (h : ∀ a b, sa a b → f a = f b) [DecidablePred f] :
    DecidablePred (Quotient.lift f h) :=
  Quot.lift.decidablePred _ _ _

/-- Note that this provides `DecidableRel (Quotient.lift₂ f h)` when `α = β`. -/
instance lift₂.decidablePred (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, sa a₁ a₂ → sb b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    [hf : ∀ a, DecidablePred (f a)]
    (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ f h q₁) :=
  fun q₂ ↦ Quotient.recOnSubsingleton₂ q₁ q₂ hf

instance (q : Quotient sa) (f : α → Prop) (h : ∀ a b, sa a b → f a = f b) [DecidablePred f] :
    Decidable (Quotient.liftOn q f h) :=
  Quotient.lift.decidablePred _ _ _

instance (q₁ : Quotient sa) (q₂ : Quotient sb) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, sa a₁ a₂ → sb b₁ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

theorem Quot.eq {α : Type*} {r : α → α → Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ EqvGen r x y :=
  ⟨Quot.eqvGen_exact r, Quot.eqvGen_sound⟩

@[simp]
theorem Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotient s → Prop} :
    (∀ a, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  ⟨fun h _ ↦ h _, fun h a ↦ a.ind h⟩

theorem Quotient.exists {α : Sort*} {s : Setoid α} {p : Quotient s → Prop} :
    (∃ a, p a) ↔ ∃ a : α, p ⟦a⟧ :=
  ⟨fun ⟨q, hq⟩ ↦ q.ind (motive := (p · → _)) .intro hq, fun ⟨a, ha⟩ ↦ ⟨⟦a⟧, ha⟩⟩

@[simp]
theorem Quotient.lift_mk {s : Setoid α} (f : α → β) (h : ∀ a b : α, s a b → f a = f b) (x : α) :
    Quotient.lift f h ⟦x⟧ = f x :=
  rfl

@[simp]
theorem Quotient.lift_comp_mk {s : Setoid α} (f : α → β) (h : ∀ a b : α, s a b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk _ = f :=
  rfl

@[simp]
theorem Quotient.lift₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {sa : Setoid α} {sb : Setoid β}
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), sa a₁ b₁ → sb a₂ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h ⟦a⟧ ⟦b⟧ = f a b :=
  rfl

theorem Quotient.liftOn_mk {s : Setoid α} (f : α → β) (h : ∀ a b : α, s a b → f a = f b) (x : α) :
    Quotient.liftOn ⟦x⟧ f h = f x :=
  rfl

@[simp]
theorem Quotient.liftOn₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {sa : Setoid α} {sb : Setoid β}
    (f : α → β → γ)
    (h : ∀ a₁ a₂ b₁ b₂, sa a₁ b₁ → sb a₂ b₂ → f a₁ a₂ = f b₁ b₂) (x : α) (y : β) :
    Quotient.liftOn₂ ⟦x⟧ ⟦y⟧ f h = f x y :=
  rfl

@[simp]
theorem Quotient.hrecOn_mk {s : Setoid α} {φ : Quotient s → Sort*} (f : ∀ a, φ ⟦a⟧)
    (c : ∀ a₁ a₂, s a₁ a₂ → HEq (f a₁) (f a₂))
    (x : α) : ⟦x⟧.hrecOn f c = f x :=
  rfl

@[simp]
theorem Quotient.hrecOn₂_mk {sa : Setoid α} {sb : Setoid α} {φ : Quotient sa → Quotient sb → Sort*}
    (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, sa a₁ a₂ → sb b₁ b₂ → HEq (f a₁ b₁) (f a₂ b₂)) (x : α)
    (qb : Quotient sb) :
    ⟦x⟧.hrecOn₂ qb f c = qb.hrecOn (f x) fun _ _ ↦ c _ _ _ _ (sa.refl _) :=
  rfl

/-- `Quot.mk r` is a surjective function. -/
theorem Quot.surjective_mk {r : α → α → Prop} : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

/-- `Quotient.mk` is a surjective function. -/
theorem Quotient.surjective_mk {s : Setoid α} :
    Function.Surjective (Quotient.mk s) :=
  Quot.exists_rep

/-- `Quotient.mk` is a surjective function. -/
theorem Quotient.surjective_mk' [s : Setoid α] :
    Function.Surjective (Quotient.mk' : α → Quotient s) :=
  Quot.exists_rep

/-- `Quot.mk r` is a surjective function. -/
@[deprecated Quot.surjective_mk (since := "2024-08-29")]
theorem surjective_quot_mk (r : α → α → Prop) : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

/-- `Quotient.mk` is a surjective function. -/
@[deprecated Quotient.surjective_mk (since := "2024-08-29")]
theorem surjective_quotient_mk {α : Sort*} (s : Setoid α) :
    Function.Surjective (Quotient.mk s) :=
  Quot.exists_rep

@[deprecated (since := "2024-08-29")] alias surjective_quotient_mk' := Quotient.surjective_mk'

@[simp] lemma Quotient.surjective_liftOn {s : Setoid α} {f : α → β} (h) :
    Function.Surjective (fun x : Quotient s ↦ x.liftOn f h) ↔ Function.Surjective f :=
  Quot.surjective_lift _

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
unsafe def Quot.unquot {r : α → α → Prop} : Quot r → α :=
  cast lcProof -- Porting note: was `unchecked_cast` before, which unfolds to `cast undefined`

@[simp]
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
noncomputable def Quotient.out {s : Setoid α} : Quotient s → α :=
  Quot.out

@[simp]
theorem Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.out⟧ = q :=
  Quot.out_eq q

theorem Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quotient s).out a :=
  Quotient.exact (Quotient.out_eq _)

theorem Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y : Quotient s} :
    ⟦x⟧ = y ↔ s x y.out := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq y]

theorem Quotient.eq_mk_iff_out {s : Setoid α} {x : Quotient s} {y : α} :
    x = ⟦y⟧ ↔ s x.out y := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq x]

@[simp]
theorem Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : s x.out y.out ↔ x = y := by
  rw [← Quotient.eq_mk_iff_out, Quotient.out_eq]

theorem Quotient.out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
  fun _ _ h ↦ Quotient.out_equiv_out.1 <| h ▸ Setoid.refl _

@[simp]
theorem Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y :=
  ⟨fun h ↦ Quotient.out_injective h, fun h ↦ h ▸ rfl⟩

section Pi

instance piSetoid {ι : Sort*} {α : ι → Sort*} [∀ i, Setoid (α i)] : Setoid (∀ i, α i) where
  r a b := ∀ i, a i ≈ b i
  iseqv := ⟨fun _ _ ↦ Setoid.refl _,
            fun h _ ↦ Setoid.symm (h _),
            fun h₁ h₂ _ ↦ Setoid.trans (h₁ _) (h₂ _)⟩

/-- Given a function `f : Π i, Quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
noncomputable def Quotient.choice {ι : Type*} {α : ι → Type*} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) (by infer_instance) :=
  ⟦fun i ↦ (f i).out⟧

@[simp]
theorem Quotient.choice_eq {ι : Type*} {α : ι → Type*} {S : ∀ i, Setoid (α i)} (f : ∀ i, α i) :
    (Quotient.choice (S := S) fun i ↦ ⟦f i⟧) = ⟦f⟧ :=
  Quotient.sound fun _ ↦ Quotient.mk_out _

@[elab_as_elim]
theorem Quotient.induction_on_pi {ι : Type*} {α : ι → Sort*} {s : ∀ i, Setoid (α i)}
    {p : (∀ i, Quotient (s i)) → Prop} (f : ∀ i, Quotient (s i))
    (h : ∀ a : ∀ i, α i, p fun i ↦ ⟦a i⟧) : p f := by
  rw [← (funext fun i ↦ Quotient.out_eq (f i) : (fun i ↦ ⟦(f i).out⟧) = f)]
  apply h

end Pi

theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ ↦ Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ ↦ ⟨⟦a⟧⟩⟩

/-! ### Truncation -/


theorem true_equivalence : @Equivalence α fun _ _ ↦ True :=
  ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

/-- Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`. -/
def trueSetoid : Setoid α :=
  ⟨_, true_equivalence⟩

/-- `Trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `Nonempty α`, but unlike `Nonempty α`, `Trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quotient α trueSetoid

namespace Trunc

/-- Constructor for `Trunc α` -/
def mk (a : α) : Trunc α :=
  Quot.mk _ a

instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

/-- Any constant function lifts to a function out of the truncation -/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : Trunc α → β :=
  Quot.lift f fun a b _ ↦ c a b

theorem ind {β : Trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : Trunc α, β q :=
  Quot.ind

protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl

/-- Lift a constant function on `q : Trunc α`. -/
-- Porting note: removed `@[elab_as_elim]` because it gave "unexpected eliminator resulting type"
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
protected def liftOn (q : Trunc α) (f : α → β) (c : ∀ a b : α, f a = f b) : β :=
  lift f c q

@[elab_as_elim]
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  ind h q

theorem exists_rep (q : Trunc α) : ∃ a : α, mk a = q :=
  Quot.exists_rep q

@[elab_as_elim]
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ ↦ Trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun _ _ ↦ Quot.sound trivial

instance instSubsingletonTrunc : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

/-- The `bind` operator for the `Trunc` monad. -/
def bind (q : Trunc α) (f : α → Trunc β) : Trunc β :=
  Trunc.liftOn q f fun _ _ ↦ Trunc.eq _ _

/-- A function `f : α → β` defines a function `map f : Trunc α → Trunc β`. -/
def map (f : α → β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)

instance : Monad Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind

instance : LawfulMonad Trunc where
  id_map _ := Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  -- Porting note: the fields below are new in Lean 4
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

variable {C : Trunc α → Sort*}

/-- Recursion/induction principle for `Trunc`. -/
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def rec (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
    (q : Trunc α) : C q :=
  Quot.rec f (fun a b _ ↦ h a b) q

/-- A version of `Trunc.rec` taking `q : Trunc α` as the first argument. -/
-- porting note (#11083): removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOn (q : Trunc α) (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q

/-- A version of `Trunc.recOn` assuming the codomain is a `Subsingleton`. -/
-- porting note (#11083)s: removed `@[reducible]` because it caused extremely slow `simp`
@[elab_as_elim]
protected def recOnSubsingleton [∀ a, Subsingleton (C (mk a))] (q : Trunc α) (f : ∀ a, C (mk a)) :
    C q :=
  Trunc.rec f (fun _ b ↦ Subsingleton.elim _ (f b)) q

/-- Noncomputably extract a representative of `Trunc α` (using the axiom of choice). -/
noncomputable def out : Trunc α → α :=
  Quot.out

@[simp]
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _

protected theorem nonempty (q : Trunc α) : Nonempty α :=
  nonempty_of_exists q.exists_rep

end Trunc

/-! ### `Quotient` with implicit `Setoid` -/


namespace Quotient

variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-- A version of `Quotient.mk` taking `{s : Setoid α}` as an implicit argument instead of an
instance argument. -/
@[deprecated Quotient.mk (since := "2024-08-09")] protected abbrev mk'' (a : α) : Quotient s₁ :=
  Quotient.mk s₁ a

@[deprecated (since := "2024-08-09")] alias surjective_Quotient_mk'' := Quotient.surjective_mk
@[deprecated (since := "2024-08-09")] protected alias liftOn' := Quotient.liftOn
@[deprecated (since := "2024-08-09")] alias liftOn'_mk'' := liftOn_mk
@[deprecated (since := "2024-08-09")] alias surjective_liftOn' := surjective_liftOn
@[deprecated (since := "2024-08-09")] protected alias liftOn₂' := Quotient.liftOn₂
@[deprecated (since := "2024-08-09")] alias liftOn₂'_mk'' := liftOn₂_mk
@[deprecated (since := "2024-08-09")] protected alias ind' := Quotient.ind
@[deprecated (since := "2024-08-09")] protected alias ind₂' := Quotient.ind₂
@[deprecated (since := "2024-08-09")] protected alias inductionOn' := Quotient.inductionOn
@[deprecated (since := "2024-08-09")] protected alias inductionOn₂' := Quotient.inductionOn₂
@[deprecated (since := "2024-08-09")] protected alias inductionOn₃' := Quotient.inductionOn₃
@[deprecated (since := "2024-08-09")] protected alias recOnSubsingleton' :=
  Quotient.recOnSubsingleton
@[deprecated (since := "2024-08-09")] protected alias recOnSubsingleton₂' :=
  Quotient.recOnSubsingleton₂
@[deprecated (since := "2024-08-09")] protected alias hrecOn' := Quotient.hrecOn
@[deprecated (since := "2024-08-09")] alias hrecOn'_mk'' := hrecOn_mk
@[deprecated (since := "2024-08-09")] alias hrecOn₂' := Quotient.hrecOn₂
@[deprecated (since := "2024-08-09")] alias hrecOn₂'_mk'' := hrecOn₂_mk
@[deprecated (since := "2024-08-09")] protected alias map' := Quotient.map
@[deprecated (since := "2024-08-09")] alias map'_mk'' := Quotient.map_mk
@[deprecated (since := "2024-08-09")] protected alias map₂' := Quotient.map₂
@[deprecated (since := "2024-08-09")] alias map₂'_mk'' := map₂_mk
@[deprecated (since := "2024-08-09")] alias eq'' := eq
@[deprecated (since := "2024-08-09")] alias out' := out
@[deprecated (since := "2024-08-09")] alias out_eq' := out_eq
@[deprecated (since := "2024-08-09")] alias mk_out' := mk_out

theorem exact' {a b : α} :
    (⟦a⟧ : Quotient s₁) = ⟦b⟧ → s₁ a b :=
  Quotient.exact

theorem sound' {a b : α} : s₁ a b → (⟦a⟧ : Quotient s₁) = ⟦b⟧ :=
  Quotient.sound

@[simp]
protected theorem eq' [Setoid α] {a b : α} :
    Quotient.mk' a = Quotient.mk' b ↔ a ≈ b :=
  Quotient.eq

section

variable [s : Setoid α]

set_option linter.deprecated false in
@[deprecated (since := "2024-08-09")] protected theorem mk''_eq_mk :
    Quotient.mk'' = Quotient.mk s :=
  rfl

@[deprecated (since := "2024-08-09")] alias liftOn'_mk := liftOn_mk
@[deprecated (since := "2024-08-09")] alias liftOn₂'_mk := liftOn₂_mk
@[deprecated (since := "2024-08-09")] alias map'_mk := map_mk

end

end Quotient

@[simp]
lemma Equivalence.quot_mk_eq_iff {α : Type*} {r : α → α → Prop} (h : Equivalence r) (x y : α) :
    Quot.mk r x = Quot.mk r y ↔ r x y := by
  constructor
  · rw [Quot.eq]
    intro hxy
    induction hxy with
    | rel _ _ H => exact H
    | refl _ => exact h.refl _
    | symm _ _ _ H => exact h.symm H
    | trans _ _ _ _ _ h₁₂ h₂₃ => exact h.trans h₁₂ h₂₃
  · exact Quot.sound
