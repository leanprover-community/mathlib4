/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

! This file was ported from Lean 3 source module init.logic
! leanprover-community/lean commit 4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Core

universe u v w

#print optParam_eq /-
@[simp]
theorem optParam_eq (α : Sort u) (default : α) : optParam α default = α :=
  rfl
#align opt_param_eq optParam_eq
-/

#print id /-
@[inline]
def id {α : Sort u} (a : α) : α :=
  a
#align id id
-/

#print flip /-
def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ := fun b a => f a b
#align flip flip
-/

#print Implies /-
/-- implication -/
def Implies (a b : Prop) :=
  a → b
#align implies Implies
-/

#print Implies.trans /-
/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
@[trans]
theorem Implies.trans {p q r : Prop} (h₁ : Implies p q) (h₂ : Implies q r) : Implies p r :=
  fun hp => h₂ (h₁ hp)
#align implies.trans Implies.trans
-/

#print trivial /-
theorem trivial : True :=
  ⟨⟩
#align trivial trivial
-/

#print absurd /-
/-- We can't have `a` and `¬a`, that would be absurd!-/
@[inline]
def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b :=
  False.ndrec b (h₂ h₁)
#align absurd absurd
-/

#print Not.intro /-
theorem Not.intro {a : Prop} (h : a → False) : ¬a :=
  h
#align not.intro Not.intro
-/

#print mt /-
/-- Modus tollens. If an implication is true, then so is its contrapositive. -/
theorem mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a := fun ha : a => h₂ (h₁ ha)
#align mt mt
-/

/-! not -/


#print not_false /-
theorem not_false : ¬False :=
  id
#align not_false not_false
-/

#print NonContradictory /-
def NonContradictory (a : Prop) : Prop :=
  ¬¬a
#align non_contradictory NonContradictory
-/

#print not_not_intro /-
theorem not_not_intro {a : Prop} (ha : a) : ¬¬a := fun hna : ¬a => absurd ha hna
#align non_contradictory_intro not_not_intro
-/

/-! false -/


#print False.elim /-
@[inline]
def False.elim {C : Sort u} (h : False) : C :=
  False.ndrec C h
#align false.elim False.elim
-/

/-! eq -/


#print proof_irrel /-
-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ :=
  rfl
#align proof_irrel proof_irrel
-/

#print id.def /-
@[simp]
theorem id.def {α : Sort u} (a : α) : id a = a :=
  rfl
#align id.def id.def
-/

#print Eq.mp /-
@[inline]
def Eq.mp {α β : Sort u} : α = β → α → β :=
  Eq.recOn
#align eq.mp Eq.mp
-/

#print Eq.mpr /-
@[inline]
def Eq.mpr {α β : Sort u} : α = β → β → α := fun h₁ h₂ => Eq.recOn (Eq.symm h₁) h₂
#align eq.mpr Eq.mpr
-/

#print Eq.substr /-
@[elab_as_elim]
theorem Eq.substr {α : Sort u} {p : α → Prop} {a b : α} (h₁ : b = a) : p a → p b :=
  Eq.subst (Eq.symm h₁)
#align eq.substr Eq.substr
-/

#print congr /-
theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) :
    f₁ a₁ = f₂ a₂ :=
  Eq.subst h₁ (Eq.subst h₂ rfl)
#align congr congr
-/

#print congr_fun /-
theorem congr_fun {α : Sort u} {β : α → Sort v} {f g : ∀ x, β x} (h : f = g) (a : α) : f a = g a :=
  Eq.subst h (Eq.refl (f a))
#align congr_fun congr_fun
-/

#print congr_arg /-
theorem congr_arg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) : a₁ = a₂ → f a₁ = f a₂ :=
  congr rfl
#align congr_arg congr_arg
-/

#print trans_rel_left /-
theorem trans_rel_left {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) :
    r a c :=
  h₂ ▸ h₁
#align trans_rel_left trans_rel_left
-/

#print trans_rel_right /-
theorem trans_rel_right {α : Sort u} {a b c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) :
    r a c :=
  h₁.symm ▸ h₂
#align trans_rel_right trans_rel_right
-/

#print of_eq_true /-
theorem of_eq_true {p : Prop} (h : p = True) : p :=
  h.symm ▸ trivial
#align of_eq_true of_eq_true
-/

#print not_of_eq_false /-
theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp
#align not_of_eq_false not_of_eq_false
-/

#print cast /-
@[inline]
def cast {α β : Sort u} (h : α = β) (a : α) : β :=
  Eq.ndrec a h
#align cast cast
-/

#print cast_proof_irrel /-
theorem cast_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a :=
  rfl
#align cast_proof_irrel cast_proof_irrel
-/

#print cast_eq /-
theorem cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a :=
  rfl
#align cast_eq cast_eq
-/

/-! ne -/


#print Ne /-
@[reducible]
def Ne {α : Sort u} (a b : α) :=
  ¬a = b
#align ne Ne
-/

#print Ne.def /-
@[simp]
theorem Ne.def {α : Sort u} (a b : α) : (a ≠ b) = ¬a = b :=
  rfl
#align ne.def Ne.def
-/

namespace Ne

variable {α : Sort u}

variable {a b : α}

#print Ne.intro /-
theorem intro (h : a = b → False) : a ≠ b :=
  h
#align ne.intro Ne.intro
-/

#print Ne.elim /-
theorem elim (h : a ≠ b) : a = b → False :=
  h
#align ne.elim Ne.elim
-/

#print Ne.irrefl /-
theorem irrefl (h : a ≠ a) : False :=
  h rfl
#align ne.irrefl Ne.irrefl
-/

#print Ne.symm /-
theorem symm (h : a ≠ b) : b ≠ a := fun h₁ : b = a => h h₁.symm
#align ne.symm Ne.symm
-/

end Ne

#print false_of_ne /-
theorem false_of_ne {α : Sort u} {a : α} : a ≠ a → False :=
  Ne.irrefl
#align false_of_ne false_of_ne
-/

section

variable {p : Prop}

#print ne_false_of_self /-
theorem ne_false_of_self : p → p ≠ False := fun (hp : p) (heq : p = False) => HEq ▸ hp
#align ne_false_of_self ne_false_of_self
-/

#print ne_true_of_not /-
theorem ne_true_of_not : ¬p → p ≠ True := fun (hnp : ¬p) (heq : p = True) => (HEq ▸ hnp) trivial
#align ne_true_of_not ne_true_of_not
-/

#print true_ne_false /-
theorem true_ne_false : ¬True = False :=
  ne_false_of_self trivial
#align true_ne_false true_ne_false
-/

end

attribute [refl] HEq.refl

section

variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

#print HEq.elim /-
def HEq.elim {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : HEq a b) : p a → p b :=
  Eq.recOn (eq_of_hEq h₁)
#align heq.elim HEq.elim
-/

#print HEq.subst /-
theorem HEq.subst {p : ∀ T : Sort u, T → Prop} : HEq a b → p α a → p β b :=
  HEq.recOn
#align heq.subst HEq.subst
-/

#print HEq.symm /-
@[symm]
theorem HEq.symm (h : HEq a b) : HEq b a :=
  HEq.recOn h (HEq.refl a)
#align heq.symm HEq.symm
-/

theorem hEq_of_eq (h : a = a') : HEq a a' :=
  Eq.subst h (HEq.refl a)
#align heq_of_eq hEq_of_eq

#print HEq.trans /-
@[trans]
theorem HEq.trans (h₁ : HEq a b) (h₂ : HEq b c) : HEq a c :=
  HEq.subst h₂ h₁
#align heq.trans HEq.trans
-/

@[trans]
theorem hEq_of_hEq_of_eq (h₁ : HEq a b) (h₂ : b = b') : HEq a b' :=
  HEq.trans h₁ (hEq_of_eq h₂)
#align heq_of_heq_of_eq hEq_of_hEq_of_eq

@[trans]
theorem hEq_of_eq_of_hEq (h₁ : a = a') (h₂ : HEq a' b) : HEq a b :=
  HEq.trans (hEq_of_eq h₁) h₂
#align heq_of_eq_of_heq hEq_of_eq_of_hEq

theorem type_eq_of_hEq (h : HEq a b) : α = β :=
  HEq.recOn h (Eq.refl α)
#align type_eq_of_heq type_eq_of_hEq

end

theorem eq_rec_hEq {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} (h : a = a') (p : φ a), HEq (Eq.recOn h p : φ a') p
  | a, _, rfl, p => HEq.refl p
#align eq_rec_heq eq_rec_hEq

theorem hEq_of_eq_rec_left {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a = a') (h₂ : (Eq.recOn e p₁ : φ a') = p₂), HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h => Eq.recOn h (HEq.refl p₁)
#align heq_of_eq_rec_left hEq_of_eq_rec_left

theorem hEq_of_eq_rec_right {α : Sort u} {φ : α → Sort v} :
    ∀ {a a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a' = a) (h₂ : p₁ = Eq.recOn e p₂), HEq p₁ p₂
  | a, _, p₁, p₂, rfl, h =>
    have : p₁ = p₂ := h
    this ▸ HEq.refl p₁
#align heq_of_eq_rec_right hEq_of_eq_rec_right

theorem of_hEq_true {a : Prop} (h : HEq a True) : a :=
  of_eq_true (eq_of_hEq h)
#align of_heq_true of_hEq_true

#print eq_rec_compose /-
theorem eq_rec_compose :
    ∀ {α β φ : Sort u} (p₁ : β = φ) (p₂ : α = β) (a : α),
      (Eq.recOn p₁ (Eq.recOn p₂ a : β) : φ) = Eq.recOn (Eq.trans p₂ p₁) a
  | α, _, _, rfl, rfl, a => rfl
#align eq_rec_compose eq_rec_compose
-/

theorem cast_hEq : ∀ {α β : Sort u} (h : α = β) (a : α), HEq (cast h a) a
  | α, _, rfl, a => HEq.refl a
#align cast_heq cast_hEq

/-! and -/


variable {a b c d : Prop}

theorem And.elim (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
  And.ndrec h₂ h₁
#align and.elim And.elimₓ

/- warning: and.swap clashes with and.symm -> And.symm
Case conversion may be inaccurate. Consider using '#align and.swap And.symmₓ'. -/
#print And.symm /-
theorem And.symm : a ∧ b → b ∧ a := fun ⟨ha, hb⟩ => ⟨hb, ha⟩
#align and.swap And.symm
-/

#print And.symm /-
theorem And.symm : a ∧ b → b ∧ a :=
  And.symm
#align and.symm And.symm
-/

/-! or -/


namespace Or

#print Or.elim /-
theorem elim (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
  Or.ndrec h₂ h₃ h₁
#align or.elim Or.elim
-/

end Or

#print not_not_em /-
theorem not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun not_em : ¬(a ∨ ¬a) =>
  have neg_a : ¬a := fun pos_a : a => absurd (Or.inl pos_a) not_em
  absurd (Or.inr neg_a) not_em
#align non_contradictory_em not_not_em
-/

/- warning: or.swap clashes with or.symm -> Or.symm
Case conversion may be inaccurate. Consider using '#align or.swap Or.symmₓ'. -/
#print Or.symm /-
theorem Or.symm : a ∨ b → b ∨ a :=
  Or.ndrec Or.inr Or.inl
#align or.swap Or.symm
-/

#print Or.symm /-
theorem Or.symm : a ∨ b → b ∨ a :=
  Or.symm
#align or.symm Or.symm
-/

/-! xor -/


#print Xor' /-
def Xor' (a b : Prop) :=
  a ∧ ¬b ∨ b ∧ ¬a
#align xor Xor'
-/

/-! iff -/


#print Iff /-
/-- `iff P Q`, with notation `P ↔ Q`, is the proposition asserting that `P` and `Q` are equivalent,
that is, have the same truth value. -/
structure Iff (a b : Prop) : Prop where intro ::
  mp : a → b
  mpr : b → a
#align iff Iff
-/

theorem Iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c :=
  Iff.ndrec
#align iff.elim Iff.elimₓ

attribute [recursor 5] Iff.elim

/- warning: iff.elim_left clashes with iff.mp -> Iff.mp
Case conversion may be inaccurate. Consider using '#align iff.elim_left Iff.mpₓ'. -/
#print Iff.mp /-
theorem Iff.mp : (a ↔ b) → a → b :=
  Iff.mp
#align iff.elim_left Iff.mp
-/

/- warning: iff.elim_right clashes with iff.mpr -> Iff.mpr
Case conversion may be inaccurate. Consider using '#align iff.elim_right Iff.mprₓ'. -/
#print Iff.mpr /-
theorem Iff.mpr : (a ↔ b) → b → a :=
  Iff.mpr
#align iff.elim_right Iff.mpr
-/

#print iff_iff_implies_and_implies /-
theorem iff_iff_implies_and_implies (a b : Prop) : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  Iff.intro (fun h => And.intro h.mp h.mpr) fun h => Iff.intro h.left h.right
#align iff_iff_implies_and_implies iff_iff_implies_and_implies
-/

#print Iff.refl /-
@[refl]
theorem Iff.refl (a : Prop) : a ↔ a :=
  Iff.intro (fun h => h) fun h => h
#align iff.refl Iff.refl
-/

#print Iff.rfl /-
theorem Iff.rfl {a : Prop} : a ↔ a :=
  Iff.refl a
#align iff.rfl Iff.rfl
-/

#print Iff.trans /-
@[trans]
theorem Iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
  Iff.intro (fun ha => Iff.mp h₂ (Iff.mp h₁ ha)) fun hc => Iff.mpr h₁ (Iff.mpr h₂ hc)
#align iff.trans Iff.trans
-/

#print Iff.symm /-
@[symm]
theorem Iff.symm (h : a ↔ b) : b ↔ a :=
  Iff.intro (Iff.mpr h) (Iff.mp h)
#align iff.symm Iff.symm
-/

#print Iff.comm /-
theorem Iff.comm : (a ↔ b) ↔ (b ↔ a) :=
  Iff.intro Iff.symm Iff.symm
#align iff.comm Iff.comm
-/

#print Eq.to_iff /-
theorem Eq.to_iff {a b : Prop} (h : a = b) : a ↔ b :=
  Eq.recOn h Iff.rfl
#align eq.to_iff Eq.to_iff
-/

#print neq_of_not_iff /-
theorem neq_of_not_iff {a b : Prop} : ¬(a ↔ b) → a ≠ b := fun h₁ h₂ =>
  have : a ↔ b := Eq.subst h₂ (Iff.refl a)
  absurd this h₁
#align neq_of_not_iff neq_of_not_iff
-/

/- warning: not_iff_not_of_iff clashes with not_congr -> not_congr
Case conversion may be inaccurate. Consider using '#align not_iff_not_of_iff not_congrₓ'. -/
#print not_congr /-
theorem not_congr (h₁ : a ↔ b) : ¬a ↔ ¬b :=
  Iff.intro (fun (hna : ¬a) (hb : b) => hna (Iff.mpr h₁ hb)) fun (hnb : ¬b) (ha : a) =>
    hnb (Iff.mp h₁ ha)
#align not_iff_not_of_iff not_congr
-/

#print of_iff_true /-
theorem of_iff_true (h : a ↔ True) : a :=
  Iff.mp (Iff.symm h) trivial
#align of_iff_true of_iff_true
-/

#print not_of_iff_false /-
theorem not_of_iff_false : (a ↔ False) → ¬a :=
  Iff.mp
#align not_of_iff_false not_of_iff_false
-/

#print iff_true_intro /-
theorem iff_true_intro (h : a) : a ↔ True :=
  Iff.intro (fun hl => trivial) fun hr => h
#align iff_true_intro iff_true_intro
-/

#print iff_false_intro /-
theorem iff_false_intro (h : ¬a) : a ↔ False :=
  Iff.intro h (False.ndrec a)
#align iff_false_intro iff_false_intro
-/

#print not_not_not /-
theorem not_not_not (a : Prop) : ¬¬¬a ↔ ¬a :=
  Iff.intro (fun (hl : ¬¬¬a) (ha : a) => hl (not_not_intro ha)) absurd
#align not_non_contradictory_iff_absurd not_not_not
-/

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a → b ↔ c → d :=
  Iff.intro (fun hab hc => Iff.mp h₂ (hab (Iff.mpr h₁ hc))) fun hcd ha =>
    Iff.mpr h₂ (hcd (Iff.mp h₁ ha))
#align imp_congr imp_congrₓ

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : a → b ↔ c → d :=
  Iff.intro
    (fun hab hc =>
      have ha : a := Iff.mpr h₁ hc
      have hb : b := hab ha
      Iff.mp (h₂ hc) hb)
    fun hcd ha =>
    have hc : c := Iff.mp h₁ ha
    have hd : d := hcd hc
    Iff.mpr (h₂ hc) hd
#align imp_congr_ctx imp_congr_ctxₓ

theorem imp_congr_right (h : a → (b ↔ c)) : a → b ↔ a → c :=
  Iff.intro (fun hab ha => Iff.mp (h ha) (hab ha)) fun hab ha => Iff.mpr (h ha) (hab ha)
#align imp_congr_right imp_congr_rightₓ

/- warning: not_not_intro clashes with non_contradictory_intro -> not_not_intro
Case conversion may be inaccurate. Consider using '#align not_not_intro not_not_introₓ'. -/
#print not_not_intro /-
theorem not_not_intro (ha : a) : ¬¬a := fun hna : ¬a => hna ha
#align not_not_intro not_not_intro
-/

#print not_of_not_not_not /-
theorem not_of_not_not_not (h : ¬¬¬a) : ¬a := fun ha => absurd (not_not_intro ha) h
#align not_of_not_not_not not_of_not_not_not
-/

#print not_true /-
@[simp]
theorem not_true : ¬True ↔ False :=
  iff_false_intro (not_not_intro trivial)
#align not_true not_true
-/

#print not_false_iff /-
@[simp]
theorem not_false_iff : ¬False ↔ True :=
  iff_true_intro not_false
#align not_false_iff not_false_iff
-/

#print not_congr /-
@[congr]
theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b :=
  Iff.intro (fun h₁ h₂ => h₁ (Iff.mpr h h₂)) fun h₁ h₂ => h₁ (Iff.mp h h₂)
#align not_congr not_congr
-/

#print ne_self_iff_false /-
theorem ne_self_iff_false {α : Sort u} (a : α) : Not (a = a) ↔ False :=
  Iff.intro false_of_ne False.elim
#align ne_self_iff_false ne_self_iff_false
-/

#print eq_self_iff_true /-
@[simp]
theorem eq_self_iff_true {α : Sort u} (a : α) : a = a ↔ True :=
  iff_true_intro rfl
#align eq_self_iff_true eq_self_iff_true
-/

theorem hEq_self_iff_true {α : Sort u} (a : α) : HEq a a ↔ True :=
  iff_true_intro (HEq.refl a)
#align heq_self_iff_true hEq_self_iff_true

#print iff_not_self /-
@[simp]
theorem iff_not_self (a : Prop) : (a ↔ ¬a) ↔ False :=
  iff_false_intro fun h =>
    have h' : ¬a := fun ha => (Iff.mp h ha) ha
    h' (Iff.mpr h h')
#align iff_not_self iff_not_self
-/

#print not_iff_self /-
@[simp]
theorem not_iff_self (a : Prop) : (¬a ↔ a) ↔ False :=
  iff_false_intro fun h =>
    have h' : ¬a := fun ha => (Iff.mpr h ha) ha
    h' (Iff.mp h h')
#align not_iff_self not_iff_self
-/

#print true_iff_false /-
theorem true_iff_false : (True ↔ False) ↔ False :=
  iff_false_intro fun h => Iff.mp h trivial
#align true_iff_false true_iff_false
-/

#print false_iff_true /-
theorem false_iff_true : (False ↔ True) ↔ False :=
  iff_false_intro fun h => Iff.mpr h trivial
#align false_iff_true false_iff_true
-/

#print false_of_true_iff_false /-
theorem false_of_true_iff_false : (True ↔ False) → False := fun h => Iff.mp h trivial
#align false_of_true_iff_false false_of_true_iff_false
-/

#print false_of_true_eq_false /-
theorem false_of_true_eq_false : True = False → False := fun h => h ▸ trivial
#align false_of_true_eq_false false_of_true_eq_false
-/

#print true_eq_false_of_false /-
theorem true_eq_false_of_false : False → True = False :=
  False.elim
#align true_eq_false_of_false true_eq_false_of_false
-/

#print eq_comm /-
theorem eq_comm {α : Sort u} {a b : α} : a = b ↔ b = a :=
  ⟨Eq.symm, Eq.symm⟩
#align eq_comm eq_comm
-/

/-! and simp rules -/


#print And.imp /-
theorem And.imp (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d := fun ⟨ha, hb⟩ => ⟨hac ha, hbd hb⟩
#align and.imp And.imp
-/

theorem and_implies (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
  And.imp hac hbd
#align and_implies and_implies

#print and_congr /-
@[congr]
theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  Iff.intro (And.imp (Iff.mp h₁) (Iff.mp h₂)) (And.imp (Iff.mpr h₁) (Iff.mpr h₂))
#align and_congr and_congr
-/

#print and_congr_right /-
theorem and_congr_right (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c :=
  Iff.intro (fun ⟨ha, hb⟩ => ⟨ha, Iff.mp (h ha) hb⟩) fun ⟨ha, hc⟩ => ⟨ha, Iff.mpr (h ha) hc⟩
#align and_congr_right and_congr_right
-/

#print and_comm /-
theorem and_comm : a ∧ b ↔ b ∧ a :=
  Iff.intro And.symm And.symm
#align and.comm and_comm
-/

#print and_comm' /-
theorem and_comm' (a b : Prop) : a ∧ b ↔ b ∧ a :=
  and_comm
#align and_comm and_comm'
-/

#print and_assoc /-
theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  Iff.intro (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩) fun ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩
#align and.assoc and_assoc
-/

#print and_assoc' /-
theorem and_assoc' (a b : Prop) : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  and_assoc
#align and_assoc and_assoc'
-/

#print and_left_comm /-
theorem and_left_comm : a ∧ b ∧ c ↔ b ∧ a ∧ c :=
  Iff.trans (Iff.symm and_assoc) (Iff.trans (and_congr and_comm (Iff.refl c)) and_assoc)
#align and.left_comm and_left_comm
-/

theorem and_iff_left {a b : Prop} (hb : b) : a ∧ b ↔ a :=
  Iff.intro And.left fun ha => ⟨ha, hb⟩
#align and_iff_left and_iff_leftₓ

#print and_iff_right /-
theorem and_iff_right {a b : Prop} (ha : a) : a ∧ b ↔ b :=
  Iff.intro And.right (And.intro ha)
#align and_iff_right and_iff_right
-/

#print and_true_iff /-
@[simp]
theorem and_true_iff (a : Prop) : a ∧ True ↔ a :=
  and_iff_left trivial
#align and_true and_true_iff
-/

#print true_and_iff /-
@[simp]
theorem true_and_iff (a : Prop) : True ∧ a ↔ a :=
  and_iff_right trivial
#align true_and true_and_iff
-/

#print and_false_iff /-
@[simp]
theorem and_false_iff (a : Prop) : a ∧ False ↔ False :=
  iff_false_intro And.right
#align and_false and_false_iff
-/

#print false_and_iff /-
@[simp]
theorem false_and_iff (a : Prop) : False ∧ a ↔ False :=
  iff_false_intro And.left
#align false_and false_and_iff
-/

#print not_and_self_iff /-
@[simp]
theorem not_and_self_iff (a : Prop) : ¬a ∧ a ↔ False :=
  iff_false_intro fun h => And.elim h fun h₁ h₂ => absurd h₂ h₁
#align not_and_self not_and_self_iff
-/

#print and_not_self_iff /-
@[simp]
theorem and_not_self_iff (a : Prop) : a ∧ ¬a ↔ False :=
  iff_false_intro fun ⟨h₁, h₂⟩ => absurd h₁ h₂
#align and_not_self and_not_self_iff
-/

#print and_self_iff /-
@[simp]
theorem and_self_iff (a : Prop) : a ∧ a ↔ a :=
  Iff.intro And.left fun h => ⟨h, h⟩
#align and_self and_self_iff
-/

/-! or simp rules -/


theorem Or.imp (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
  Or.ndrec (fun h => Or.inl (h₂ h)) fun h => Or.inr (h₃ h)
#align or.imp Or.impₓ

#print Or.imp_left /-
theorem Or.imp_left (h : a → b) : a ∨ c → b ∨ c :=
  Or.imp h id
#align or.imp_left Or.imp_left
-/

#print Or.imp_right /-
theorem Or.imp_right (h : a → b) : c ∨ a → c ∨ b :=
  Or.imp id h
#align or.imp_right Or.imp_right
-/

#print or_congr /-
@[congr]
theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∨ b ↔ c ∨ d :=
  Iff.intro (Or.imp (Iff.mp h₁) (Iff.mp h₂)) (Or.imp (Iff.mpr h₁) (Iff.mpr h₂))
#align or_congr or_congr
-/

#print or_comm /-
theorem or_comm : a ∨ b ↔ b ∨ a :=
  Iff.intro Or.symm Or.symm
#align or.comm or_comm
-/

#print or_comm' /-
theorem or_comm' (a b : Prop) : a ∨ b ↔ b ∨ a :=
  or_comm
#align or_comm or_comm'
-/

#print or_assoc /-
theorem or_assoc : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  Iff.intro (Or.ndrec (Or.imp_right Or.inl) fun h => Or.inr (Or.inr h))
    (Or.ndrec (fun h => Or.inl (Or.inl h)) (Or.imp_left Or.inr))
#align or.assoc or_assoc
-/

#print or_assoc' /-
theorem or_assoc' (a b : Prop) : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  or_assoc
#align or_assoc or_assoc'
-/

/- warning: or.left_comm clashes with or_left_comm -> or_left_comm
Case conversion may be inaccurate. Consider using '#align or.left_comm or_left_commₓ'. -/
#print or_left_comm /-
theorem or_left_comm : a ∨ b ∨ c ↔ b ∨ a ∨ c :=
  Iff.trans (Iff.symm or_assoc) (Iff.trans (or_congr or_comm (Iff.refl c)) or_assoc)
#align or.left_comm or_left_comm
-/

#print or_iff_right_of_imp /-
theorem or_iff_right_of_imp (ha : a → b) : a ∨ b ↔ b :=
  Iff.intro (Or.ndrec ha id) Or.inr
#align or_iff_right_of_imp or_iff_right_of_imp
-/

theorem or_iff_left_of_imp (hb : b → a) : a ∨ b ↔ a :=
  Iff.intro (Or.ndrec id hb) Or.inl
#align or_iff_left_of_imp or_iff_left_of_impₓ

#print or_true_iff /-
@[simp]
theorem or_true_iff (a : Prop) : a ∨ True ↔ True :=
  iff_true_intro (Or.inr trivial)
#align or_true or_true_iff
-/

#print true_or_iff /-
@[simp]
theorem true_or_iff (a : Prop) : True ∨ a ↔ True :=
  iff_true_intro (Or.inl trivial)
#align true_or true_or_iff
-/

#print or_false_iff /-
@[simp]
theorem or_false_iff (a : Prop) : a ∨ False ↔ a :=
  Iff.intro (Or.ndrec id False.elim) Or.inl
#align or_false or_false_iff
-/

#print false_or_iff /-
@[simp]
theorem false_or_iff (a : Prop) : False ∨ a ↔ a :=
  Iff.trans or_comm (or_false_iff a)
#align false_or false_or_iff
-/

#print or_self_iff /-
@[simp]
theorem or_self_iff (a : Prop) : a ∨ a ↔ a :=
  Iff.intro (Or.ndrec id id) Or.inl
#align or_self or_self_iff
-/

#print not_or_of_not /-
theorem not_or_of_not {a b : Prop} : ¬a → ¬b → ¬(a ∨ b)
  | hna, hnb, Or.inl ha => absurd ha hna
  | hna, hnb, Or.inr hb => absurd hb hnb
#align not_or not_or_of_not
-/

/-! or resolution rulse -/


#print Or.resolve_left /-
theorem Or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬a) : b :=
  Or.elim h (fun ha => absurd ha na) id
#align or.resolve_left Or.resolve_left
-/

#print Or.neg_resolve_left /-
theorem Or.neg_resolve_left {a b : Prop} (h : ¬a ∨ b) (ha : a) : b :=
  Or.elim h (fun na => absurd ha na) id
#align or.neg_resolve_left Or.neg_resolve_left
-/

#print Or.resolve_right /-
theorem Or.resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬b) : a :=
  Or.elim h id fun hb => absurd hb nb
#align or.resolve_right Or.resolve_right
-/

#print Or.neg_resolve_right /-
theorem Or.neg_resolve_right {a b : Prop} (h : a ∨ ¬b) (hb : b) : a :=
  Or.elim h id fun nb => absurd hb nb
#align or.neg_resolve_right Or.neg_resolve_right
-/

/-! iff simp rules -/


#print iff_true_iff /-
@[simp]
theorem iff_true_iff (a : Prop) : (a ↔ True) ↔ a :=
  Iff.intro (fun h => Iff.mpr h trivial) iff_true_intro
#align iff_true iff_true_iff
-/

#print true_iff_iff /-
@[simp]
theorem true_iff_iff (a : Prop) : (True ↔ a) ↔ a :=
  Iff.trans Iff.comm (iff_true_iff a)
#align true_iff true_iff_iff
-/

#print iff_false_iff /-
@[simp]
theorem iff_false_iff (a : Prop) : (a ↔ False) ↔ ¬a :=
  Iff.intro Iff.mp iff_false_intro
#align iff_false iff_false_iff
-/

#print false_iff_iff /-
@[simp]
theorem false_iff_iff (a : Prop) : (False ↔ a) ↔ ¬a :=
  Iff.trans Iff.comm (iff_false_iff a)
#align false_iff false_iff_iff
-/

#print iff_self_iff /-
@[simp]
theorem iff_self_iff (a : Prop) : (a ↔ a) ↔ True :=
  iff_true_intro Iff.rfl
#align iff_self iff_self_iff
-/

@[congr]
theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
  (iff_iff_implies_and_implies a b).trans
    ((and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)).trans (iff_iff_implies_and_implies c d).symm)
#align iff_congr iff_congrₓ

/-! implies simp rule -/


#print imp_true_iff /-
@[simp]
theorem imp_true_iff (α : Sort u) : α → True ↔ True :=
  Iff.intro (fun h => trivial) fun ha h => trivial
#align implies_true_iff imp_true_iff
-/

#print false_imp_iff /-
theorem false_imp_iff (a : Prop) : False → a ↔ True :=
  Iff.intro (fun h => trivial) fun ha h => False.elim h
#align false_implies_iff false_imp_iff
-/

#print true_imp_iff /-
theorem true_imp_iff (α : Prop) : True → α ↔ α :=
  Iff.intro (fun h => h trivial) fun h h' => h
#align true_implies_iff true_imp_iff
-/

#print Exists /-
/-- The existential quantifier.

To prove a goal of the form `⊢ ∃ x, p x`, you can provide a witness `y` with the tactic `existsi y`.
If you are working in a project that depends on mathlib, then we recommend the `use` tactic
instead.
You'll then be left with the goal `⊢ p y`.

To extract a witness `x` and proof `hx : p x` from a hypothesis `h : ∃ x, p x`,
use the tactic `cases h with x hx`. See also the mathlib tactics `obtain` and `rcases`.
-/
inductive Exists {α : Sort u} (p : α → Prop) : Prop
  | intro (w : α) (h : p w) : Exists
#align Exists Exists
-/

attribute [intro] Exists.intro

/- warning: exists.intro clashes with Exists.intro -> Exists.intro
Case conversion may be inaccurate. Consider using '#align exists.intro Exists.introₓ'. -/
#print Exists.intro /-
-- This is a `def`, so that it can be used as pattern in the equation compiler.
@[match_pattern]
def Exists.intro {α : Sort u} {p : α → Prop} (w : α) (h : p w) : ∃ x, p x :=
  ⟨w, h⟩
#align exists.intro Exists.intro
-/

#print Exists.elim /-
theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ a : α, p a → b) :
    b :=
  Exists.ndrec h₂ h₁
#align exists.elim Exists.elim
-/

/-! exists unique -/


#print ExistsUnique /-
def ExistsUnique {α : Sort u} (p : α → Prop) :=
  ∃ x, p x ∧ ∀ y, p y → y = x
#align exists_unique ExistsUnique
-/

#print ExistsUnique.intro /-
@[intro]
theorem ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ y, p y → y = w) :
    ∃! x, p x :=
  Exists.intro w ⟨h₁, h₂⟩
#align exists_unique.intro ExistsUnique.intro
-/

#print ExistsUnique.elim /-
@[recursor 4]
theorem ExistsUnique.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₂ : ∃! x, p x)
    (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ fun w hw => h₁ w (And.left hw) (And.right hw)
#align exists_unique.elim ExistsUnique.elim
-/

theorem existsUnique_of_exists_of_unique {α : Sort u} {p : α → Prop} (hex : ∃ x, p x)
    (hunique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) : ∃! x, p x :=
  Exists.elim hex fun x px => ExistsUnique.intro x px fun y => fun this : p y => hunique y x this px
#align exists_unique_of_exists_of_unique existsUnique_of_exists_of_unique

#print ExistsUnique.exists /-
theorem ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
  Exists.elim h fun x hx => ⟨x, And.left hx⟩
#align exists_of_exists_unique ExistsUnique.exists
-/

#print ExistsUnique.unique /-
theorem ExistsUnique.unique {α : Sort u} {p : α → Prop} (h : ∃! x, p x) {y₁ y₂ : α} (py₁ : p y₁)
    (py₂ : p y₂) : y₁ = y₂ :=
  ExistsUnique.elim h fun x => fun this : p x => fun unique : ∀ y, p y → y = x =>
    show y₁ = y₂ from Eq.trans (Unique _ py₁) (Eq.symm (Unique _ py₂))
#align unique_of_exists_unique ExistsUnique.unique
-/

/-! exists, forall, exists unique congruences -/


#print forall_congr' /-
@[congr]
theorem forall_congr' {α : Sort u} {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
  Iff.intro (fun p a => Iff.mp (h a) (p a)) fun q a => Iff.mpr (h a) (q a)
#align forall_congr forall_congr'
-/

/- warning: exists_imp_exists clashes with Exists.imp -> Exists.imp
Case conversion may be inaccurate. Consider using '#align exists_imp_exists Exists.impₓ'. -/
#print Exists.imp /-
theorem Exists.imp {α : Sort u} {p q : α → Prop} (h : ∀ a, p a → q a) (p : ∃ a, p a) : ∃ a, q a :=
  Exists.elim p fun a hp => ⟨a, h a hp⟩
#align exists_imp_exists Exists.imp
-/

#print exists_congr /-
@[congr]
theorem exists_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a ↔ q a) : Exists p ↔ ∃ a, q a :=
  Iff.intro (Exists.imp fun a => Iff.mp (h a)) (Exists.imp fun a => Iff.mpr (h a))
#align exists_congr exists_congr
-/

@[congr]
theorem existsUnique_congr {α : Sort u} {p₁ p₂ : α → Prop} (h : ∀ x, p₁ x ↔ p₂ x) :
    ExistsUnique p₁ ↔ ∃! x, p₂ x :=
  --
    exists_congr
    fun x => and_congr (h x) (forall_congr' fun y => imp_congr (h y) Iff.rfl)
#align exists_unique_congr existsUnique_congr

#print forall_not_of_not_exists /-
theorem forall_not_of_not_exists {α : Sort u} {p : α → Prop} : (¬∃ x, p x) → ∀ x, ¬p x :=
  fun hne x hp => hne ⟨x, hp⟩
#align forall_not_of_not_exists forall_not_of_not_exists
-/

/-! decidable -/


#print Decidable.decide /-
def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  Decidable.casesOn h (fun h₁ => Bool.false) fun h₂ => Bool.true
#align decidable.to_bool Decidable.decide
-/

export Decidable (isTrue isFalse decide)

#print decide_True' /-
@[simp]
theorem decide_True' (h : Decidable True) : @decide True h = true :=
  Decidable.casesOn h (fun h => False.elim (Iff.mp not_true h)) fun _ => rfl
#align to_bool_true_eq_tt decide_True'
-/

#print decide_False' /-
@[simp]
theorem decide_False' (h : Decidable False) : @decide False h = false :=
  Decidable.casesOn h (fun h => rfl) fun h => False.elim h
#align to_bool_false_eq_ff decide_False'
-/

#print decidableTrue /-
instance decidableTrue : Decidable True :=
  isTrue trivial
#align decidable.true decidableTrue
-/

#print decidableFalse /-
instance decidableFalse : Decidable False :=
  isFalse not_false
#align decidable.false decidableFalse
-/

#print dite /-
-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[inline]
def dite {α : Sort u} (c : Prop) [h : Decidable c] : (c → α) → (¬c → α) → α := fun t e =>
  Decidable.recOn h e t
#align dite dite
-/

#print ite /-
/-- if-then-else -/
@[inline]
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.recOn h (fun hnc => e) fun hc => t
#align ite ite
-/

namespace Decidable

variable {p q : Prop}

#print Decidable.recOn_true /-
def recOn_true [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : p) (h₄ : h₁ h₃) :
    Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => False.ndrec _ (h h₃)) fun h => h₄
#align decidable.rec_on_true Decidable.recOn_true
-/

#print Decidable.recOn_false /-
def recOn_false [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) :
    Decidable.recOn h h₂ h₁ :=
  Decidable.recOn h (fun h => h₄) fun h => False.ndrec _ (h₃ h)
#align decidable.rec_on_false Decidable.recOn_false
-/

#print Decidable.byCases /-
def byCases {q : Sort u} [φ : Decidable p] : (p → q) → (¬p → q) → q :=
  dite _
#align decidable.by_cases Decidable.byCases
-/

#print Decidable.em /-
/-- Law of Excluded Middle. -/
theorem em (p : Prop) [Decidable p] : p ∨ ¬p :=
  byCases Or.inl Or.inr
#align decidable.em Decidable.em
-/

#print Decidable.by_contradiction /-
theorem by_contradiction [Decidable p] (h : ¬p → False) : p :=
  if h₁ : p then h₁ else False.ndrec _ (h h₁)
#align decidable.by_contradiction Decidable.by_contradiction
-/

#print Decidable.of_not_not /-
theorem of_not_not [Decidable p] : ¬¬p → p := fun hnn => by_contradiction fun hn => absurd hn hnn
#align decidable.of_not_not Decidable.of_not_not
-/

#print Decidable.not_not_iff /-
theorem not_not_iff (p) [Decidable p] : ¬¬p ↔ p :=
  Iff.intro of_not_not not_not_intro
#align decidable.not_not_iff Decidable.not_not_iff
-/

#print Decidable.not_and_iff_or_not /-
theorem not_and_iff_or_not (p q : Prop) [d₁ : Decidable p] [d₂ : Decidable q] :
    ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  Iff.intro
    (fun h =>
      match d₁ with
      | is_true h₁ =>
        match d₂ with
        | is_true h₂ => absurd (And.intro h₁ h₂) h
        | is_false h₂ => Or.inr h₂
      | is_false h₁ => Or.inl h₁)
    fun h ⟨hp, hq⟩ => Or.elim h (fun h => h hp) fun h => h hq
#align decidable.not_and_iff_or_not Decidable.not_and_iff_or_not
-/

#print Decidable.not_or_iff_and_not /-
theorem not_or_iff_and_not (p q) [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h =>
      match d₁ with
      | is_true h₁ => False.elim <| h (Or.inl h₁)
      | is_false h₁ =>
        match d₂ with
        | is_true h₂ => False.elim <| h (Or.inr h₂)
        | is_false h₂ => ⟨h₁, h₂⟩)
    fun ⟨np, nq⟩ h => Or.elim h np nq
#align decidable.not_or_iff_and_not Decidable.not_or_iff_and_not
-/

end Decidable

section

variable {p q : Prop}

#print decidable_of_decidable_of_iff /-
def decidable_of_decidable_of_iff (hp : Decidable p) (h : p ↔ q) : Decidable q :=
  if hp : p then isTrue (Iff.mp h hp) else isFalse (Iff.mp (not_congr h) hp)
#align decidable_of_decidable_of_iff decidable_of_decidable_of_iff
-/

#print decidable_of_decidable_of_eq /-
def decidable_of_decidable_of_eq (hp : Decidable p) (h : p = q) : Decidable q :=
  decidable_of_decidable_of_iff hp h.to_iff
#align decidable_of_decidable_of_eq decidable_of_decidable_of_eq
-/

#print Or.by_cases /-
/-- A version of `or.elim` in `Type`. If both `p` and `q` are true, `h₁` is used. -/
protected def Or.by_cases [Decidable p] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  if hp : p then h₁ hp else h₂ (h.resolve_left hp)
#align or.by_cases Or.by_cases
-/

end

section

variable {p q : Prop}

instance [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  if hp : p then if hq : q then isTrue ⟨hp, hq⟩ else isFalse fun h : p ∧ q => hq (And.right h)
  else isFalse fun h : p ∧ q => hp (And.left h)

instance [Decidable p] [Decidable q] : Decidable (p ∨ q) :=
  if hp : p then isTrue (Or.inl hp)
  else if hq : q then isTrue (Or.inr hq) else isFalse (Or.ndrec hp hq)

instance [Decidable p] : Decidable ¬p :=
  if hp : p then isFalse (absurd hp) else isTrue hp

instance Implies.decidable [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then if hq : q then isTrue fun h => hq else isFalse fun h : p → q => absurd (h hp) hq
  else isTrue fun h => absurd h hp
#align implies.decidable Implies.decidable

instance [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  if hp : p then if hq : q then isTrue ⟨fun _ => hq, fun _ => hp⟩ else isFalse fun h => hq (h.1 hp)
  else
    if hq : q then isFalse fun h => hp (h.2 hq)
    else isTrue <| ⟨fun h => absurd h hp, fun h => absurd h hq⟩

instance [Decidable p] [Decidable q] : Decidable (Xor' p q) :=
  if hp : p then
    if hq : q then
      isFalse (Or.ndrec (fun ⟨_, h⟩ => h hq : ¬(p ∧ ¬q)) (fun ⟨_, h⟩ => h hp : ¬(q ∧ ¬p)))
    else isTrue <| Or.inl ⟨hp, hq⟩
  else
    if hq : q then isTrue <| Or.inr ⟨hq, hp⟩
    else isFalse (Or.ndrec (fun ⟨h, _⟩ => hp h : ¬(p ∧ ¬q)) (fun ⟨h, _⟩ => hq h : ¬(q ∧ ¬p)))

instance existsPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] :
    Decidable (∃ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h) ⟨fun h2 => ⟨h, h2⟩, fun ⟨h', h2⟩ => h2⟩
  else isFalse (mt (fun ⟨h, _⟩ => h) h)
#align exists_prop_decidable existsPropDecidable

instance forallPropDecidable {p} (P : p → Prop) [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] :
    Decidable (∀ h, P h) :=
  if h : p then decidable_of_decidable_of_iff (DP h) ⟨fun h2 _ => h2, fun al => al h⟩
  else isTrue fun h2 => absurd h2 h
#align forall_prop_decidable forallPropDecidable

end

instance {α : Sort u} [DecidableEq α] (a b : α) : Decidable (a ≠ b) :=
  Implies.decidable

theorem Bool.false_ne_true : false = true → False :=
  fun.
#align bool.ff_ne_tt Bool.false_ne_true

#print IsDecEq /-
def IsDecEq {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ ⦃x y : α⦄, p x y = true → x = y
#align is_dec_eq IsDecEq
-/

#print IsDecRefl /-
def IsDecRefl {α : Sort u} (p : α → α → Bool) : Prop :=
  ∀ x, p x x = true
#align is_dec_refl IsDecRefl
-/

open Decidable

instance : DecidableEq Bool
  | ff, ff => isTrue rfl
  | ff, tt => isFalse Bool.false_ne_true
  | tt, ff => isFalse (Ne.symm Bool.false_ne_true)
  | tt, tt => isTrue rfl

#print decidableEq_of_bool_pred /-
def decidableEq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : IsDecEq p) (h₂ : IsDecRefl p) :
    DecidableEq α := fun x y : α =>
  if hp : p x y = true then isTrue (h₁ hp)
  else isFalse fun hxy : x = y => absurd (h₂ y) (@Eq.recOn _ _ (fun z => ¬p z y = true) _ hxy hp)
#align decidable_eq_of_bool_pred decidableEq_of_bool_pred
-/

#print decidableEq_inl_refl /-
theorem decidableEq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) :
    h a a = isTrue (Eq.refl a) :=
  match h a a with
  | is_true e => rfl
  | is_false n => absurd rfl n
#align decidable_eq_inl_refl decidableEq_inl_refl
-/

#print decidableEq_inr_neg /-
theorem decidableEq_inr_neg {α : Sort u} [h : DecidableEq α] {a b : α} :
    ∀ n : a ≠ b, h a b = isFalse n := fun n =>
  match h a b with
  | is_true e => absurd e n
  | is_false n₁ => proof_irrel n n₁ ▸ Eq.refl (isFalse n)
#align decidable_eq_inr_neg decidableEq_inr_neg
-/

/-! inhabited -/


#print Inhabited /-
class Inhabited (α : Sort u) where
  default : α
#align inhabited Inhabited
-/

export Inhabited (default)

/- warning: arbitrary clashes with inhabited.default -> Inhabited.default
Case conversion may be inaccurate. Consider using '#align arbitrary Inhabited.defaultₓ'. -/
#print Inhabited.default /-
@[inline]
irreducible_def Inhabited.default (α : Sort u) [Inhabited α] : α :=
  default
#align arbitrary Inhabited.default
-/

instance Prop.inhabited : Inhabited Prop :=
  ⟨True⟩
#align prop.inhabited Prop.inhabited

instance Pi.inhabited (α : Sort u) {β : α → Sort v} [∀ x, Inhabited (β x)] : Inhabited (∀ x, β x) :=
  ⟨fun a => default⟩
#align pi.inhabited Pi.inhabited

instance : Inhabited Bool :=
  ⟨false⟩

instance : Inhabited True :=
  ⟨trivial⟩

#print Nonempty /-
class inductive Nonempty (α : Sort u) : Prop
  | intro (val : α) : Nonempty
#align nonempty Nonempty
-/

#print Nonempty.elim /-
protected theorem Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  Nonempty.ndrec h₂ h₁
#align nonempty.elim Nonempty.elim
-/

#print instNonempty /-
instance (priority := 100) instNonempty {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩
#align nonempty_of_inhabited instNonempty
-/

#print nonempty_of_exists /-
theorem nonempty_of_exists {α : Sort u} {p : α → Prop} : (∃ x, p x) → Nonempty α
  | ⟨w, h⟩ => ⟨w⟩
#align nonempty_of_exists nonempty_of_exists
-/

/-! subsingleton -/


#print Subsingleton /-
class inductive Subsingleton (α : Sort u) : Prop
  | intro (h : ∀ a b : α, a = b) : Subsingleton
#align subsingleton Subsingleton
-/

#print Subsingleton.elim /-
protected theorem Subsingleton.elim {α : Sort u} [h : Subsingleton α] : ∀ a b : α, a = b :=
  Subsingleton.ndrec (fun p => p) h
#align subsingleton.elim Subsingleton.elim
-/

#print Subsingleton.helim /-
protected theorem Subsingleton.helim {α β : Sort u} [h : Subsingleton α] (h : α = β) :
    ∀ (a : α) (b : β), HEq a b :=
  Eq.recOn h fun a b : α => hEq_of_eq (Subsingleton.elim a b)
#align subsingleton.helim Subsingleton.helim
-/

instance subsingleton_prop (p : Prop) : Subsingleton p :=
  ⟨fun a b => proof_irrel a b⟩
#align subsingleton_prop subsingleton_prop

instance (p : Prop) : Subsingleton (Decidable p) :=
  Subsingleton.intro fun d₁ =>
    match d₁ with
    | is_true t₁ => fun d₂ =>
      match d₂ with
      | is_true t₂ => Eq.recOn (proof_irrel t₁ t₂) rfl
      | is_false f₂ => absurd t₁ f₂
    | is_false f₁ => fun d₂ =>
      match d₂ with
      | is_true t₂ => absurd t₂ f₁
      | is_false f₂ => Eq.recOn (proof_irrel f₁ f₂) rfl

#print rec_subsingleton /-
protected theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u}
    [h₃ : ∀ h : p, Subsingleton (h₁ h)] [h₄ : ∀ h : ¬p, Subsingleton (h₂ h)] :
    Subsingleton (Decidable.recOn h h₂ h₁) :=
  match h with
  | is_true h => h₃ h
  | is_false h => h₄ h
#align rec_subsingleton rec_subsingleton
-/

#print if_pos /-
theorem if_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t e : α} : ite c t e = t :=
  match h with
  | is_true hc => rfl
  | is_false hnc => absurd hc hnc
#align if_pos if_pos
-/

#print if_neg /-
theorem if_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t e : α} : ite c t e = e :=
  match h with
  | is_true hc => absurd hc hnc
  | is_false hnc => rfl
#align if_neg if_neg
-/

#print if_t_t /-
@[simp]
theorem if_t_t (c : Prop) [h : Decidable c] {α : Sort u} (t : α) : ite c t t = t :=
  match h with
  | is_true hc => rfl
  | is_false hnc => rfl
#align if_t_t if_t_t
-/

#print imp_of_if_pos /-
theorem imp_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t := fun hc =>
  Eq.recOn (if_pos hc : ite c t e = t) h
#align implies_of_if_pos imp_of_if_pos
-/

#print imp_of_if_neg /-
theorem imp_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e := fun hnc =>
  Eq.recOn (if_neg hnc : ite c t e = e) h
#align implies_of_if_neg imp_of_if_neg
-/

#print if_ctx_congr /-
theorem if_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x y u v : α} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)
#align if_ctx_congr if_ctx_congr
-/

#print if_congr /-
theorem if_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x y u v : α}
    (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  @if_ctx_congr α b c dec_b dec_c x y u v h_c (fun h => h_t) fun h => h_e
#align if_congr if_congr
-/

#print if_true /-
@[simp]
theorem if_true {α : Sort u} {h : Decidable True} (t e : α) : @ite α True h t e = t :=
  if_pos trivial
#align if_true if_true
-/

#print if_false /-
@[simp]
theorem if_false {α : Sort u} {h : Decidable False} (t e : α) : @ite α False h t e = e :=
  if_neg not_false
#align if_false if_false
-/

#print if_ctx_congr_prop /-
theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)
#align if_ctx_congr_prop if_ctx_congr_prop
-/

#print if_congr_prop /-
@[congr]
theorem if_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c)
    (h_t : x ↔ u) (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun h => h_t) fun h => h_e
#align if_congr_prop if_congr_prop
-/

#print if_ctx_simp_congr_prop /-
theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c)
    (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
    ite b x y ↔ @ite Prop c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e
#align if_ctx_simp_congr_prop if_ctx_simp_congr_prop
-/

#print if_simp_congr_prop /-
@[congr]
theorem if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : x ↔ u)
    (h_e : y ↔ v) : ite b x y ↔ @ite Prop c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @if_ctx_simp_congr_prop b c x y u v dec_b h_c (fun h => h_t) fun h => h_e
#align if_simp_congr_prop if_simp_congr_prop
-/

#print dif_pos /-
@[simp]
theorem dif_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} :
    dite c t e = t hc :=
  match h with
  | is_true hc => rfl
  | is_false hnc => absurd hc hnc
#align dif_pos dif_pos
-/

#print dif_neg /-
@[simp]
theorem dif_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} :
    dite c t e = e hnc :=
  match h with
  | is_true hc => absurd hc hnc
  | is_false hnc => rfl
#align dif_neg dif_neg
-/

#print dif_ctx_congr /-
@[congr]
theorem dif_ctx_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c)
    (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h) (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c dec_c u v :=
  match dec_b, dec_c with
  | is_false h₁, is_false h₂ => h_e h₂
  | is_true h₁, is_true h₂ => h_t h₂
  | is_false h₁, is_true h₂ => absurd h₂ (Iff.mp (not_congr h_c) h₁)
  | is_true h₁, is_false h₂ => absurd h₁ (Iff.mpr (not_congr h_c) h₂)
#align dif_ctx_congr dif_ctx_congr
-/

#print dif_ctx_simp_congr /-
theorem dif_ctx_simp_congr {α : Sort u} {b c : Prop} [dec_b : Decidable b] {x : b → α} {u : c → α}
    {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ h : c, x (Iff.mpr h_c h) = u h)
    (h_e : ∀ h : ¬c, y (Iff.mpr (not_congr h_c) h) = v h) :
    @dite α b dec_b x y = @dite α c (decidable_of_decidable_of_iff dec_b h_c) u v :=
  @dif_ctx_congr α b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e
#align dif_ctx_simp_congr dif_ctx_simp_congr
-/

#print dif_eq_if /-
-- Remark: dite and ite are "defally equal" when we ignore the proofs.
theorem dif_eq_if (c : Prop) [h : Decidable c] {α : Sort u} (t : α) (e : α) :
    (dite c (fun h => t) fun h => e) = ite c t e :=
  match h with
  | is_true hc => rfl
  | is_false hnc => rfl
#align dif_eq_if dif_eq_if
-/

instance {c t e : Prop} [d_c : Decidable c] [d_t : Decidable t] [d_e : Decidable e] :
    Decidable (if c then t else e) :=
  match d_c with
  | is_true hc => d_t
  | is_false hc => d_e

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [d_c : Decidable c] [d_t : ∀ h, Decidable (t h)]
    [d_e : ∀ h, Decidable (e h)] : Decidable (if h : c then t h else e h) :=
  match d_c with
  | is_true hc => d_t hc
  | is_false hc => d_e hc

#print AsTrue /-
def AsTrue (c : Prop) [Decidable c] : Prop :=
  if c then True else False
#align as_true AsTrue
-/

#print AsFalse /-
def AsFalse (c : Prop) [Decidable c] : Prop :=
  if c then False else True
#align as_false AsFalse
-/

#print AsTrue.get /-
theorem AsTrue.get {c : Prop} [h₁ : Decidable c] (h₂ : AsTrue c) : c :=
  match h₁, h₂ with
  | is_true h_c, h₂ => h_c
  | is_false h_c, h₂ => False.elim h₂
#align of_as_true AsTrue.get
-/

#print ULift /-
/-- Universe lifting operation -/
structure ULift.{r, s} (α : Type s) : Type max s r where up ::
  down : α
#align ulift ULift
-/

namespace ULift

#print ULift.up_down /-
/-- Bijection between α and ulift.{v} α -/
theorem up_down {α : Type u} : ∀ b : ULift.{v} α, up (down b) = b
  | up a => rfl
#align ulift.up_down ULift.up_down
-/

#print ULift.down_up /-
theorem down_up {α : Type u} (a : α) : down (up.{v} a) = a :=
  rfl
#align ulift.down_up ULift.down_up
-/

end ULift

#print PLift /-
/-- Universe lifting operation from Sort to Type -/
structure PLift (α : Sort u) : Type u where up ::
  down : α
#align plift PLift
-/

namespace PLift

#print PLift.up_down /-
/-- Bijection between α and plift α -/
theorem up_down {α : Sort u} : ∀ b : PLift α, up (down b) = b
  | up a => rfl
#align plift.up_down PLift.up_down
-/

#print PLift.down_up /-
theorem down_up {α : Sort u} (a : α) : down (up a) = a :=
  rfl
#align plift.down_up PLift.down_up
-/

end PLift

#print let_value_eq /-
/-- Equalities for rewriting let-expressions -/
theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ a₂ : α} (b : α → β) :
    a₁ = a₂ →
      (let x : α := a₁
        b x) =
        let x : α := a₂
        b x :=
  fun h => Eq.recOn h rfl
#align let_value_eq let_value_eq
-/

#print let_value_heq /-
theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ a₂ : α} (b : ∀ x : α, β x) :
    a₁ = a₂ →
      HEq
        (let x : α := a₁
        b x)
        (let x : α := a₂
        b x) :=
  fun h => Eq.recOn h (HEq.refl (b a₁))
#align let_value_heq let_value_heq
-/

#print let_body_eq /-
theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ b₂ : ∀ x : α, β x} :
    (∀ x, b₁ x = b₂ x) →
      (let x : α := a
        b₁ x) =
        let x : α := a
        b₂ x :=
  fun h => h a
#align let_body_eq let_body_eq
-/

#print let_eq /-
theorem let_eq {α : Sort v} {β : Sort u} {a₁ a₂ : α} {b₁ b₂ : α → β} :
    a₁ = a₂ →
      (∀ x, b₁ x = b₂ x) →
        (let x : α := a₁
          b₁ x) =
          let x : α := a₂
          b₂ x :=
  fun h₁ h₂ => Eq.recOn h₁ (h₂ a₁)
#align let_eq let_eq
-/

section Relation

variable {α : Sort u} {β : Sort v} (r : β → β → Prop)

local infixl:50 "≺" => r

#print Reflexive /-
def Reflexive :=
  ∀ x, x≺x
#align reflexive Reflexive
-/

#print Symmetric /-
def Symmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x
#align symmetric Symmetric
-/

#print Transitive /-
def Transitive :=
  ∀ ⦃x y z⦄, x≺y → y≺z → x≺z
#align transitive Transitive
-/

#print Equivalence /-
def Equivalence :=
  Reflexive r ∧ Symmetric r ∧ Transitive r
#align equivalence Equivalence
-/

#print Total /-
def Total :=
  ∀ x y, x≺y ∨ y≺x
#align total Total
-/

#print Equivalence.mk /-
theorem Equivalence.mk (rfl : Reflexive r) (symm : Symmetric r) (trans : Transitive r) :
    Equivalence r :=
  ⟨rfl, symm, trans⟩
#align mk_equivalence Equivalence.mk
-/

#print Irreflexive /-
def Irreflexive :=
  ∀ x, ¬x≺x
#align irreflexive Irreflexive
-/

#print AntiSymmetric /-
def AntiSymmetric :=
  ∀ ⦃x y⦄, x≺y → y≺x → x = y
#align anti_symmetric AntiSymmetric
-/

#print EmptyRelation /-
def EmptyRelation := fun a₁ a₂ : α => False
#align empty_relation EmptyRelation
-/

#print Subrelation /-
def Subrelation (q r : β → β → Prop) :=
  ∀ ⦃x y⦄, q x y → r x y
#align subrelation Subrelation
-/

#print InvImage /-
def InvImage (f : α → β) : α → α → Prop := fun a₁ a₂ => f a₁≺f a₂
#align inv_image InvImage
-/

#print InvImage.trans /-
theorem InvImage.trans (f : α → β) (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) => h h₁ h₂
#align inv_image.trans InvImage.trans
-/

#print InvImage.irreflexive /-
theorem InvImage.irreflexive (f : α → β) (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) => h (f a) h₁
#align inv_image.irreflexive InvImage.irreflexive
-/

end Relation

section Binary

variable {α : Type u} {β : Type v}

variable (f : α → α → α)

variable (inv : α → α)

variable (one : α)

local notation a "*" b => f a b

local notation a "⁻¹" => inv a

variable (g : α → α → α)

local notation a "+" b => g a b

#print Commutative /-
def Commutative :=
  ∀ a b, (a*b) = b*a
#align commutative Commutative
-/

#print Associative /-
def Associative :=
  ∀ a b c, ((a*b)*c) = a*b*c
#align associative Associative
-/

#print LeftIdentity /-
def LeftIdentity :=
  ∀ a, (one*a) = a
#align left_identity LeftIdentity
-/

#print RightIdentity /-
def RightIdentity :=
  ∀ a, (a*one) = a
#align right_identity RightIdentity
-/

#print RightInverse /-
def RightInverse :=
  ∀ a, (a*a⁻¹) = one
#align right_inverse RightInverse
-/

#print LeftCancelative /-
def LeftCancelative :=
  ∀ a b c, ((a*b) = a*c) → b = c
#align left_cancelative LeftCancelative
-/

#print RightCancelative /-
def RightCancelative :=
  ∀ a b c, ((a*b) = c*b) → a = c
#align right_cancelative RightCancelative
-/

#print LeftDistributive /-
def LeftDistributive :=
  ∀ a b c, (a*b+c) = (a*b)+a*c
#align left_distributive LeftDistributive
-/

#print RightDistributive /-
def RightDistributive :=
  ∀ a b c, ((a+b)*c) = (a*c)+b*c
#align right_distributive RightDistributive
-/

#print RightCommutative /-
def RightCommutative (h : β → α → β) :=
  ∀ b a₁ a₂, h (h b a₁) a₂ = h (h b a₂) a₁
#align right_commutative RightCommutative
-/

#print LeftCommutative /-
def LeftCommutative (h : α → β → β) :=
  ∀ a₁ a₂ b, h a₁ (h a₂ b) = h a₂ (h a₁ b)
#align left_commutative LeftCommutative
-/

#print left_comm /-
theorem left_comm : Commutative f → Associative f → LeftCommutative f := fun hcomm hassoc =>
  fun a b c =>
  calc
    (a*b*c) = (a*b)*c := Eq.symm (hassoc a b c)
    _ = (b*a)*c := (hcomm a b ▸ rfl)
    _ = b*a*c := hassoc b a c
#align left_comm left_comm
-/

#print right_comm /-
theorem right_comm : Commutative f → Associative f → RightCommutative f := fun hcomm hassoc =>
  fun a b c =>
  calc
    ((a*b)*c) = a*b*c := hassoc a b c
    _ = a*c*b := (hcomm b c ▸ rfl)
    _ = (a*c)*b := Eq.symm (hassoc a c b)
#align right_comm right_comm
-/

end Binary

