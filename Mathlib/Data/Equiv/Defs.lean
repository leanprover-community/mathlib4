/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Logic.Unique
import Mathlib.Data.FunLike.Equiv
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.Relation.Trans
import Mathlib.Tactic.Simps.Basic

/-!
# Equivalence between types

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

Many more such isomorphisms and operations are defined in `logic/equiv/basic`.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun

infixl:25 " ≃ " => Equiv

instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨fun f =>
    { toFun := f,
      invFun := EquivLike.inv f,
      left_inv := EquivLike.left_inv f,
      right_inv := EquivLike.right_inv f }⟩

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible]
def Equiv.Perm (α : Sort _) :=
  Equiv α α

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coe := toFun
  inv := invFun
  left_inv := left_inv
  right_inv := right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    cases e₁
    cases e₂
    congr

instance : CoeFun (α ≃ β) fun _ => α → β :=
  ⟨toFun⟩

/-- The map `(r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) (fun e => e) :=
  FunLike.coe_injective'

protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  @FunLike.coe_fn_eq _ _ _ _ e₁ e₂

@[ext]
theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g H

protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' → f x = f x' :=
  FunLike.congr_arg f

protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x

theorem ext_iff {f g : Equiv α β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[ext]
theorem Perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
  Equiv.ext H

protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg

protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x

theorem Perm.ext_iff {σ τ : Equiv.Perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
  Equiv.ext_iff

/-- Any type is equivalent to itself. -/
@[refl]
protected def refl (α : Sort _) : α ≃ α :=
  ⟨id, id, fun x => rfl, fun x => rfl⟩

instance inhabited' : Inhabited (α ≃ α) :=
  ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
-- Porting note: `symm` attribute rejects this lemma because of implicit arguments.
-- @[symm]
protected def symm (e : α ≃ β) : β ≃ α :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : α ≃ β) : β → α :=
  e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symmApply)

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
-- Porting note: `trans` attribute rejects this lemma because of implicit arguments.
-- @[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
theorem to_fun_as_coe (e : α ≃ β) : e.toFun = e :=
  rfl

@[simp]
theorem inv_fun_as_coe (e : α ≃ β) : e.invFun = e.symm :=
  rfl

protected theorem injective (e : α ≃ β) : Injective e :=
  EquivLike.injective e

protected theorem surjective (e : α ≃ β) : Surjective e :=
  EquivLike.surjective e

protected theorem bijective (e : α ≃ β) : Bijective e :=
  EquivLike.bijective e

protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.Injective.Subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.Injective.Subsingleton

theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun h => e.symm.subsingleton, fun h => e.subsingleton⟩

instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equiv.ext fun x => Subsingleton.elim _ _⟩

instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equiv.ext fun x => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)

theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.Injective.DecidableEq

theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β :=
  Nonempty.congr e e.symm

protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α :=
  e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [Inhabited β] (e : α ≃ β) : Inhabited α :=
  ⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [Unique β] (e : α ≃ β) : Unique α :=
  e.symm.Surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun x => by
    cases h
    rfl, fun x => by
    cases h
    rfl⟩

@[simp]
theorem coe_fn_symm_mk (f : α → β) (g l r) : ((Equiv.mk f g l r).symm : β → α) = g :=
  rfl

@[simp]
theorem coe_refl : ⇑(Equiv.refl α) = id :=
  rfl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `multiplicative.of_add` etc. -/
theorem Perm.coe_subsingleton {α : Type _} [Subsingleton α] (e : Perm α) : ⇑e = id := by
  rw [perm.subsingleton_eq_refl e, coe_refl]

theorem refl_apply (x : α) : Equiv.refl α x = x :=
  rfl

@[simp]
theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : ⇑(f.trans g) = g ∘ f :=
  rfl

theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x :=
  e.right_inv x

@[simp]
theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[simp]
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) : (f.trans g).symm a = f.symm (g.symm a) :=
  rfl

-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simp_nf]
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b :=
  rfl

theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y :=
  EquivLike.apply_eq_iff_eq f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_eq_iff_eq_symm_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [":" (Term.sort "Sort" [(Level.hole "_")])] "}")
        (Term.explicitBinder "(" [`f] [":" (Logic.Equiv.Defs.«term_≃_» `α " ≃ " `β)] [] ")")
        (Term.implicitBinder "{" [`x] [":" `α] "}")
        (Term.implicitBinder "{" [`y] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Term.app `f [`x]) "=" `y)
         "↔"
         («term_=_» `x "=" (Term.app (Term.proj `f "." `symm) [`y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `apply_symm_apply [`f `y]))] "]"))])))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_eq_iff_eq)] "]") [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `apply_symm_apply [`f `y]))] "]"))])))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_eq_iff_eq)] "]") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_eq_iff_eq)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `apply_eq_iff_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `apply_symm_apply [`f `y]))] "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `apply_symm_apply [`f `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `apply_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  apply_eq_iff_eq_symm_apply
  { α β : Sort _ } ( f : α ≃ β ) { x : α } { y : β } : f x = y ↔ x = f . symm y
  := by conv_lhs => rw [ ← apply_symm_apply f y ] rw [ apply_eq_iff_eq ]

@[simp]
theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x :=
  rfl

@[simp]
theorem cast_symm {α β} (h : α = β) : (Equiv.cast h).symm = Equiv.cast h.symm :=
  rfl

@[simp]
theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α :=
  rfl

@[simp]
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) : (Equiv.cast h).trans (Equiv.cast h2) = Equiv.cast (h.trans h2) :=
  ext fun x => by
    substs h h2
    rfl

theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ HEq a b := by
  subst h
  simp

theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩

theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
  (eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp]
theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by
  cases e
  rfl

@[simp]
theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e := by
  cases e
  rfl

@[simp]
theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α :=
  rfl

@[simp]
theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e := by
  cases e
  rfl

@[simp]
theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β :=
  ext (by simp)

@[simp]
theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α :=
  ext (by simp)

theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) : (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  Equiv.ext fun a => rfl

theorem left_inverse_symm (f : Equiv α β) : LeftInverse f.symm f :=
  f.left_inv

theorem right_inverse_symm (f : Equiv α β) : Function.RightInverse f.symm f :=
  f.right_inv

theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f

theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e

theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f

theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e

theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f

theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equivCongr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : α ≃ γ ≃ (β ≃ δ) :=
  ⟨fun ac => (ab.symm.trans ac).trans cd, fun bd => ab.trans <| bd.trans <| cd.symm, fun ac => by
    ext x
    simp, fun ac => by
    ext x
    simp⟩

@[simp]
theorem equiv_congr_refl {α β} : (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) := by
  ext
  rfl

@[simp]
theorem equiv_congr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by
  ext
  rfl

@[simp]
theorem equiv_congr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  ext
  rfl

@[simp]
theorem equiv_congr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) : (Equiv.refl α).equivCongr bg e = e.trans bg :=
  rfl

@[simp]
theorem equiv_congr_refl_right {α β} (ab e : α ≃ β) : ab.equivCongr (Equiv.refl β) e = ab.symm.trans e :=
  rfl

@[simp]
theorem equiv_congr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) :=
  rfl

section PermCongr

variable {α' β' : Type _} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def permCongr : Perm α' ≃ Perm β' :=
  equivCongr e e

theorem perm_congr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e :=
  rfl

@[simp]
theorem perm_congr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by simp [perm_congr_def]

@[simp]
theorem perm_congr_symm : e.permCongr.symm = e.symm.permCongr :=
  rfl

@[simp]
theorem perm_congr_apply (p : Equiv.Perm α') (x) : e.permCongr p x = e (p (e.symm x)) :=
  rfl

theorem perm_congr_symm_apply (p : Equiv.Perm β') (x) : e.permCongr.symm p x = e.symm (p (e x)) :=
  rfl

theorem perm_congr_trans (p p' : Equiv.Perm α') : (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') :=
  by
  ext
  simp

end PermCongr

/-- Two empty types are equivalent. -/
def equivOfIsEmpty (α β : Sort _) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty :=
  equivOfIsEmpty α _

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equivPempty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} :=
  equivOfIsEmpty α _

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.is_empty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun p => rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def propEquivPempty {p : Prop} (h : ¬p) : p ≃ PEmpty :=
  @equivPempty p <| IsEmpty.prop_iff.2 h

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
def equivOfUnique (α β : Sort _) [Unique α] [Unique β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` has a unique element, then it is equivalent to any `punit`. -/
def equivPunit (α : Sort _) [Unique α] : α ≃ PUnit.{v} :=
  equivOfUnique α _

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def propEquivPunit {p : Prop} (h : p) : p ≃ PUnit :=
  @equivPunit p <| uniqueProp h

/-- `ulift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, fun a => rfl⟩

/-- `plift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := false }) apply symmApply]
protected def plift : PLift α ≃ α :=
  ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩

/-- equivalence of propositions is the same as iff -/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q where
  toFun := h.mp
  invFun := h.mpr
  left_inv x := rfl
  right_inv y := rfl

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr, simps apply]
def arrowCongr {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := funext fun x => by simp
  right_inv f := funext fun x => by simp

theorem arrow_congr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁)
    (g : β₁ → γ₁) : arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by
  ext
  simp only [comp, arrow_congr_apply, eb.symm_apply_apply]

@[simp]
theorem arrow_congr_refl {α β : Sort _} : arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr, simps apply]
def arrowCongr' {α₁ β₁ α₂ β₂ : Type _} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ

@[simp]
theorem arrow_congr'_refl {α β : Type _} : arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr'_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) :=
  arrowCongr e e

@[simp]
theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) :=
  rfl

@[simp]
theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj :=
  rfl

@[simp]
theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
  rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by apply arrow_congr_comp

theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm

theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm

theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply

theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq

/-- `punit` sorts in any two universes are equivalent. -/
def punitEquivPunit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => PUnit.unit, fun _ => PUnit.unit, fun u => by
    cases u
    rfl, fun u => by
    cases u
    rfl⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def propEquivBool : Prop ≃ Bool :=
  ⟨fun p => @decide p (Classical.propDecidable _), fun b => b, fun p => by simp, fun b => by simp⟩

section

/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrowPunitEquivPunit (α : Sort _) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun f => PUnit.unit, fun u f => PUnit.unit, fun f => by
    funext x
    cases f x
    rfl, fun u => by
    cases u
    rfl⟩

/-- If `α` is `subsingleton` and `a : α`, then the type of dependent functions `Π (i : α), β
i` is equivalent to `β i`. -/
@[simps]
def piSubsingleton {α} (β : α → Sort _) [Subsingleton α] (a : α) : (∀ a', β a') ≃ β a where
  toFun := eval a
  invFun x b := cast (congr_arg β <| Subsingleton.elim a b) x
  left_inv f :=
    funext fun b => by
      rw [Subsingleton.elim b a]
      rfl
  right_inv b := rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (α β) [Unique α] : (α → β) ≃ β :=
  piSubsingleton _ default

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punitArrowEquiv (α : Sort _) : (PUnit.{u} → α) ≃ α :=
  funUnique _ _

/-- The sort of maps from `true` is equivalent to the codomain. -/
def trueArrowEquiv (α : Sort _) : (True → α) ≃ α :=
  funUnique _ _

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrowPunitOfIsEmpty (α β : Sort _) [IsEmpty α] : (α → β) ≃ PUnit.{u} :=
  ⟨fun f => PUnit.unit, fun u => isEmptyElim, fun f => funext isEmptyElim, fun u => by
    cases u
    rfl⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def emptyArrowEquivPunit (α : Sort _) : (Empty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pemptyArrowEquivPunit (α : Sort _) : (PEmpty → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

/-- The sort of maps from `false` is equivalent to `punit`. -/
def falseArrowEquivPunit (α : Sort _) : (False → α) ≃ PUnit.{u} :=
  arrowPunitOfIsEmpty _ _

end

section

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigma {α} (β : α → Type _) : (Σ'i, β i) ≃ Σi, β i :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigmaEquivSigmaPlift {α} (β : α → Sort _) : (Σ'i, β i) ≃ Σi : PLift α, PLift (β i.down) :=
  ⟨fun a => ⟨PLift.up a.1, PLift.up a.2⟩, fun a => ⟨a.1.down, a.2.down⟩, fun ⟨a, b⟩ => rfl, fun ⟨⟨a⟩, ⟨b⟩⟩ => rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigmaCongrRight {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ'a, β₁ a) ≃ Σ'a, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (PSigma.mk a) <| apply_symm_apply (F a) b⟩

@[simp]
theorem psigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) = psigmaCongrRight fun a => (F a).trans (G a) := by
  ext1 x
  cases x
  rfl

@[simp]
theorem psigma_congr_right_symm {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := by
  ext1 x
  cases x
  rfl

@[simp]
theorem psigma_congr_right_refl {α} {β : α → Sort _} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ'a, β a) := by
  ext1 x
  cases x
  rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σa, β₁ a) ≃ Σa, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| symm_apply_apply (F a) b, fun ⟨a, b⟩ =>
    congr_arg (Sigma.mk a) <| apply_symm_apply (F a) b⟩

@[simp]
theorem sigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) := by
  ext1 x
  cases x
  rfl

@[simp]
theorem sigma_congr_right_symm {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := by
  ext1 x
  cases x
  rfl

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Type _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) := by
  ext1 x
  cases x
  rfl

/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ'i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigmaPliftEquivSubtype {α : Type v} (P : α → Prop) : (Σi, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans (psigmaCongrRight fun a => Equiv.plift)).trans (psigmaEquivSubtype P)

/-- A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigmaUliftPliftEquivSubtype {α : Type v} (P : α → Prop) : (Σi, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun a => Equiv.ulift).trans (sigmaPliftEquivSubtype P)

namespace Perm

/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σa, β a) :=
  Equiv.sigmaCongrRight F

@[simp]
theorem sigma_congr_right_trans {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  Equiv.sigma_congr_right_trans F G

@[simp]
theorem sigma_congr_right_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  Equiv.sigma_congr_right_symm F

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) :=
  Equiv.sigma_congr_right_refl

end Perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigmaCongrLeft {α₁ α₂} {β : α₂ → Sort _} (e : α₁ ≃ α₂) : (Σa : α₁, β (e a)) ≃ Σa : α₂, β a :=
  ⟨fun a => ⟨e a.1, a.2⟩, fun a => ⟨e.symm a.1, @Eq.ndrec β a.2 (e.right_inv a.1).symm⟩, fun ⟨a, b⟩ =>
    match (motive := ∀ (a') (h : a' = a), @Sigma.mk _ (β ∘ e) _ (@Eq.ndrec β b (congr_arg e h.symm)) = ⟨a, b⟩)
      e.symm (e a), e.left_inv a with
    | _, rfl => rfl,
    fun ⟨a, b⟩ =>
    match (motive := ∀ (a') (h : a' = a), Sigma.mk a' (@Eq.ndrec β b h.symm) = ⟨a, b⟩) e (e.symm a), _ with
    | _, rfl => rfl⟩

/-- Transporting a sigma type through an equivalence of the base -/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) : (Σa : α₁, β a) ≃ Σa : α₂, β (f.symm a) :=
  (sigmaCongrLeft f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂) (F : ∀ a, β₁ a ≃ β₂ (f a)) :
    Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simps apply symmApply]
def sigmaEquivProd (α β : Type _) : (Σ_ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)

/-- Dependent product of types is associative up to an equivalence. -/
def sigmaAssoc {α : Type _} {β : α → Type _} (γ : ∀ a : α, β a → Type _) :
    (Σab : Σa : α, β a, γ ab.1 ab.2) ≃ Σa : α, Σb : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun ⟨⟨a, b⟩, c⟩ => rfl
  right_inv := fun ⟨a, ⟨b, c⟩⟩ => rfl

end

protected theorem exists_unique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) :
    (∃! x, p x) ↔ ∃! y, q y := by
  constructor
  · rintro ⟨a, ha₁, ha₂⟩
    exact ⟨f a, h.1 ha₁, fun b hb => f.symm_apply_eq.1 (ha₂ (f.symm b) (h.2 (by simpa using hb)))⟩

  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨f.symm b, h.2 (by simpa using hb₁), fun y hy => (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩


protected theorem exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) : (∃! x, p x) ↔ ∃! y, p (f.symm y) :=
  Equiv.exists_unique_congr f fun x => by simp

protected theorem exists_unique_congr_left {p : β → Prop} (f : α ≃ β) : (∃! x, p (f x)) ↔ ∃! y, p y :=
  (Equiv.exists_unique_congr_left' f.symm).symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `forall_congr [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`q] [":" (Term.arrow `β "→" (Term.prop "Prop"))] "}")
        (Term.explicitBinder "(" [`f] [":" (Logic.Equiv.Defs.«term_≃_» `α " ≃ " `β)] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [(Term.implicitBinder "{" [`x] [] "}")]
           []
           ","
           («term_↔_» (Term.app `p [`x]) "↔" (Term.app `q [(Term.app `f [`x])])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.forall "∀" [`x] [] "," (Term.app `p [`x]))
         "↔"
         (Term.forall "∀" [`y] [] "," (Term.app `q [`y])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`h₂ `x]))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `f.right_inv [`x]))] "]") [])
              [])
             (group (Tactic.apply "apply" `h.mp) [])
             (group (Tactic.apply "apply" `h₂) [])])
           []
           (Tactic.apply "apply" `h.mpr)
           []
           (Tactic.apply "apply" `h₂)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`h₂ `x]))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `f.right_inv [`x]))] "]") [])
             [])
            (group (Tactic.apply "apply" `h.mp) [])
            (group (Tactic.apply "apply" `h₂) [])])
          []
          (Tactic.apply "apply" `h.mpr)
          []
          (Tactic.apply "apply" `h₂)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h.mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mpr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `f.right_inv [`x]))] "]") [])
         [])
        (group (Tactic.apply "apply" `h.mp) [])
        (group (Tactic.apply "apply" `h₂) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.apply "apply" `h.mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `f.right_inv [`x]))] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.right_inv [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.right_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'patternIgnore'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    forall_congr
    { p : α → Prop } { q : β → Prop } ( f : α ≃ β ) ( h : ∀ { x } , p x ↔ q f x ) : ∀ x , p x ↔ ∀ y , q y
    := by constructor <;> intro h₂ x · rw [ ← f.right_inv x ] apply h.mp apply h₂ apply h.mpr apply h₂

protected theorem forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p (f.symm x) ↔ q x) :
    (∀ x, p x) ↔ ∀ y, q y :=
  (Equiv.forall_congr f.symm fun x => h.symm).symm

-- We next build some higher arity versions of `equiv.forall_congr`.
-- Although they appear to just be repeated applications of `equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
universe ua1 ua2 ub1 ub2 ug1 ug2

variable {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1} {γ₂ : Sort ug2}

protected theorem forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) : (∀ x y, p x y) ↔ ∀ x y, q x y := by
  apply Equiv.forall_congr
  intros
  apply Equiv.forall_congr
  intros
  apply h

protected theorem forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) : (∀ x y, p x y) ↔ ∀ x y, q x y :=
  (Equiv.forall₂_congr eα.symm eβ.symm fun x y => h.symm).symm

protected theorem forall₃_congr {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) : (∀ x y z, p x y z) ↔ ∀ x y z, q x y z := by
  apply Equiv.forall₂_congr
  intros
  apply Equiv.forall_congr
  intros
  apply h

protected theorem forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
    (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm fun x y z => h.symm).symm

protected theorem forall_congr_left' {p : α → Prop} (f : α ≃ β) : (∀ x, p x) ↔ ∀ y, p (f.symm y) :=
  Equiv.forall_congr f fun x => by simp

protected theorem forall_congr_left {p : β → Prop} (f : α ≃ β) : (∀ x, p (f x)) ↔ ∀ y, p y :=
  (Equiv.forall_congr_left' f.symm).symm

protected theorem exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} : (∃ a, p a) ↔ ∃ b, p (f.symm b) :=
  ⟨fun ⟨a, h⟩ => ⟨f a, by simpa using h⟩, fun ⟨b, h⟩ => ⟨_, h⟩⟩

end Equiv

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
    Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (Eq a₁ a₂).1
  invFun :=
    Quot.map e.symm fun b₁ b₂ h =>
      (Eq (e.symm b₁) (e.symm b₂)).2 ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by
    rintro ⟨a⟩
    dsimp only [Quot.map]
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a⟩
    dsimp only [Quot.map]
    simp only [Equiv.apply_symm_apply]

@[simp]
theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂))
    (a : α) : Quot.congr e Eq (Quot.mk ra a) = Quot.mk rb (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quot r ≃ Quot r' :=
  Quot.congr (Equiv.refl α) Eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) : Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  @Quot.congr α β r (fun b b' => r (e.symm b) (e.symm b')) e fun a₁ a₂ => by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, @Setoid.R α ra a₁ a₂ ↔ @Setoid.R β rb (e a₁) (e a₂)) : Quotient ra ≃ Quotient rb :=
  Quot.congr e Eq

@[simp]
theorem congr_mk {ra : Setoid α} {rb : Setoid β} (e : α ≃ β) (eq : ∀ a₁ a₂ : α, Setoid.R a₁ a₂ ↔ Setoid.R (e a₁) (e a₂))
    (a : α) : Quotient.congr e Eq (Quotient.mk a) = Quotient.mk (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : Setoid α} (eq : ∀ a₁ a₂, @Setoid.R α r a₁ a₂ ↔ @Setoid.R α r' a₁ a₂) :
    Quotient r ≃ Quotient r' :=
  Quot.congrRight Eq

end Quotient
