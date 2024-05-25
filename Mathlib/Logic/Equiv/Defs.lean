/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Quot
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Logic.Unique
import Mathlib.Tactic.Substs
import Mathlib.Tactic.Conv

#align_import logic.equiv.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Equivalence between types

In this file we define two types:

* `Equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `Equiv.Perm α`: the group of permutations `α ≃ α`. More lemmas about `Equiv.Perm` can be found in
  `GroupTheory.Perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `Equiv.refl α` is the identity map interpreted as `α ≃ α`;

* operations on equivalences: e.g.,

  - `Equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `Equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `Equiv.inhabited` takes `e : α ≃ β` and `[Inhabited β]` and returns `Inhabited α`;
  - `Equiv.unique` takes `e : α ≃ β` and `[Unique β]` and returns `Unique α`;
  - `Equiv.decidableEq` takes `e : α ≃ β` and `[DecidableEq β]` and returns `DecidableEq α`.

  More definitions of this kind can be found in other files. E.g., `Data.Equiv.TransferInstance`
  does it for many algebraic type classes like `Group`, `Module`, etc.

Many more such isomorphisms and operations are defined in `Logic.Equiv.Basic`.

## Tags

equivalence, congruence, bijective map
-/

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α : Sort*) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun
  protected right_inv : RightInverse invFun toFun
#align equiv Equiv

@[inherit_doc]
infixl:25 " ≃ " => Equiv

/-- Turn an element of a type `F` satisfying `EquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
def EquivLike.toEquiv {F} [EquivLike F α β] (f : F) : α ≃ β where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f

/-- Any type satisfying `EquivLike` can be cast into `Equiv` via `EquivLike.toEquiv`. -/
instance {F} [EquivLike F α β] : CoeTC F (α ≃ β) :=
  ⟨EquivLike.toEquiv⟩

/-- `Perm α` is the type of bijections from `α` to itself. -/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α
#align equiv.perm Equiv.Perm

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coe := Equiv.toFun
  inv := Equiv.invFun
  left_inv := Equiv.left_inv
  right_inv := Equiv.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by cases e₁; cases e₂; congr

/-- Helper instance when inference gets stuck on following the normal chain
`EquivLike → FunLike`.

TODO: this instance doesn't appear to be necessary: remove it (after benchmarking?)
-/
instance : FunLike (α ≃ β) α β where
  coe := Equiv.toFun
  coe_injective' := DFunLike.coe_injective

@[simp, norm_cast]
lemma _root_.EquivLike.coe_coe {F} [EquivLike F α β] (e : F) :
    ((e : α ≃ β) : α → β) = e := rfl

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (Equiv.mk f g l r : α → β) = f :=
  rfl
#align equiv.coe_fn_mk Equiv.coe_fn_mk

/-- The map `(r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) (fun e => e) :=
  DFunLike.coe_injective'
#align equiv.coe_fn_injective Equiv.coe_fn_injective

protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  @DFunLike.coe_fn_eq _ _ _ _ e₁ e₂
#align equiv.coe_inj Equiv.coe_inj

@[ext] theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g := DFunLike.ext f g H
#align equiv.ext Equiv.ext

protected theorem congr_arg {f : Equiv α β} {x x' : α} : x = x' → f x = f x' :=
  DFunLike.congr_arg f
#align equiv.congr_arg Equiv.congr_arg

protected theorem congr_fun {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
#align equiv.congr_fun Equiv.congr_fun

theorem ext_iff {f g : Equiv α β} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff
#align equiv.ext_iff Equiv.ext_iff

@[ext] theorem Perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ := Equiv.ext H
#align equiv.perm.ext Equiv.Perm.ext

protected theorem Perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg
#align equiv.perm.congr_arg Equiv.Perm.congr_arg

protected theorem Perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x
#align equiv.perm.congr_fun Equiv.Perm.congr_fun

theorem Perm.ext_iff {σ τ : Equiv.Perm α} : σ = τ ↔ ∀ x, σ x = τ x := Equiv.ext_iff
#align equiv.perm.ext_iff Equiv.Perm.ext_iff

/-- Any type is equivalent to itself. -/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
#align equiv.refl Equiv.refl

instance inhabited' : Inhabited (α ≃ α) := ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
#align equiv.symm Equiv.symm

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : α ≃ β) : β → α := e.symm
#align equiv.simps.symm_apply Equiv.Simps.symm_apply

initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

-- Porting note:
-- Added these lemmas as restatements of `left_inv` and `right_inv`,
-- which use the coercions.
-- We might even consider switching the names, and having these as a public API.
theorem left_inv' (e : α ≃ β) : Function.LeftInverse e.symm e := e.left_inv
theorem right_inv' (e : α ≃ β) : Function.RightInverse e.symm e := e.right_inv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩
#align equiv.trans Equiv.trans

@[simps]
instance : Trans Equiv Equiv Equiv where
  trans := Equiv.trans

-- Porting note: this is not a syntactic tautology any more because
-- the coercion from `e` to a function is now `DFunLike.coe` not `e.toFun`
@[simp, mfld_simps] theorem toFun_as_coe (e : α ≃ β) : e.toFun = e := rfl
#align equiv.to_fun_as_coe Equiv.toFun_as_coe

@[simp, mfld_simps] theorem invFun_as_coe (e : α ≃ β) : e.invFun = e.symm := rfl
#align equiv.inv_fun_as_coe Equiv.invFun_as_coe

protected theorem injective (e : α ≃ β) : Injective e := EquivLike.injective e
#align equiv.injective Equiv.injective

protected theorem surjective (e : α ≃ β) : Surjective e := EquivLike.surjective e
#align equiv.surjective Equiv.surjective

protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e
#align equiv.bijective Equiv.bijective

protected theorem subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.injective.subsingleton
#align equiv.subsingleton Equiv.subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.injective.subsingleton
#align equiv.subsingleton.symm Equiv.subsingleton.symm

theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun _ => e.symm.subsingleton, fun _ => e.subsingleton⟩
#align equiv.subsingleton_congr Equiv.subsingleton_congr

instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f _ => Equiv.ext fun _ => @Subsingleton.elim _ (Equiv.subsingleton.symm f) _ _⟩

instance permUnique [Subsingleton α] : Unique (Perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)

theorem Perm.subsingleton_eq_refl [Subsingleton α] (e : Perm α) : e = Equiv.refl α :=
  Subsingleton.elim _ _
#align equiv.perm.subsingleton_eq_refl Equiv.Perm.subsingleton_eq_refl

/-- Transfer `DecidableEq` across an equivalence. -/
protected def decidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidableEq
#align equiv.decidable_eq Equiv.decidableEq

theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β := Nonempty.congr e e.symm
#align equiv.nonempty_congr Equiv.nonempty_congr

protected theorem nonempty (e : α ≃ β) [Nonempty β] : Nonempty α := e.nonempty_congr.mpr ‹_›
#align equiv.nonempty Equiv.nonempty

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [Inhabited β] (e : α ≃ β) : Inhabited α := ⟨e.symm default⟩
#align equiv.inhabited Equiv.inhabited

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique
#align equiv.unique Equiv.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm, fun _ => by cases h; rfl, fun _ => by cases h; rfl⟩
#align equiv.cast Equiv.cast

@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((Equiv.mk f g l r).symm : β → α) = g := rfl
#align equiv.coe_fn_symm_mk Equiv.coe_fn_symm_mk

@[simp] theorem coe_refl : (Equiv.refl α : α → α) = id := rfl
#align equiv.coe_refl Equiv.coe_refl

/-- This cannot be a `simp` lemmas as it incorrectly matches against `e : α ≃ synonym α`, when
`synonym α` is semireducible. This makes a mess of `Multiplicative.ofAdd` etc. -/
theorem Perm.coe_subsingleton {α : Type*} [Subsingleton α] (e : Perm α) : (e : α → α) = id := by
  rw [Perm.subsingleton_eq_refl e, coe_refl]
#align equiv.perm.coe_subsingleton Equiv.Perm.coe_subsingleton

-- Porting note: marking this as `@[simp]` because `simp` doesn't fire on `coe_refl`
-- in an expression such as `Equiv.refl a x`
@[simp] theorem refl_apply (x : α) : Equiv.refl α x = x := rfl
#align equiv.refl_apply Equiv.refl_apply

@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g : α → γ) = g ∘ f := rfl
#align equiv.coe_trans Equiv.coe_trans

-- Porting note: marking this as `@[simp]` because `simp` doesn't fire on `coe_trans`
-- in an expression such as `Equiv.trans f g x`
@[simp] theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) := rfl
#align equiv.trans_apply Equiv.trans_apply

@[simp] theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x := e.right_inv x
#align equiv.apply_symm_apply Equiv.apply_symm_apply

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x := e.left_inv x
#align equiv.symm_apply_apply Equiv.symm_apply_apply

@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply
#align equiv.symm_comp_self Equiv.symm_comp_self

@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply
#align equiv.self_comp_symm Equiv.self_comp_symm

@[simp] lemma _root_.EquivLike.apply_coe_symm_apply {F} [EquivLike F α β] (e : F) (x : β) :
    e ((e : α ≃ β).symm x) = x :=
  (e : α ≃ β).apply_symm_apply x

@[simp] lemma _root_.EquivLike.coe_symm_apply_apply {F} [EquivLike F α β] (e : F) (x : α) :
    (e : α ≃ β).symm (e x) = x :=
  (e : α ≃ β).symm_apply_apply x

@[simp] lemma _root_.EquivLike.coe_symm_comp_self {F} [EquivLike F α β] (e : F) :
    (e : α ≃ β).symm ∘ e = id :=
  (e : α ≃ β).symm_comp_self

@[simp] lemma _root_.EquivLike.self_comp_coe_symm {F} [EquivLike F α β] (e : F) :
    e ∘ (e : α ≃ β).symm = id :=
  (e : α ≃ β).self_comp_symm

@[simp] theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl
#align equiv.symm_trans_apply Equiv.symm_trans_apply

-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `Equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simpNF] theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl
#align equiv.symm_symm_apply Equiv.symm_symm_apply

theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f
#align equiv.apply_eq_iff_eq Equiv.apply_eq_iff_eq

theorem apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : α ≃ β) : f x = y ↔ x = f.symm y := by
  conv_lhs => rw [← apply_symm_apply f y]
  rw [apply_eq_iff_eq]
#align equiv.apply_eq_iff_eq_symm_apply Equiv.apply_eq_iff_eq_symm_apply

@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x := rfl
#align equiv.cast_apply Equiv.cast_apply

@[simp] theorem cast_symm {α β} (h : α = β) : (Equiv.cast h).symm = Equiv.cast h.symm := rfl
#align equiv.cast_symm Equiv.cast_symm

@[simp] theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α := rfl
#align equiv.cast_refl Equiv.cast_refl

@[simp] theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
    (Equiv.cast h).trans (Equiv.cast h2) = Equiv.cast (h.trans h2) :=
  ext fun x => by substs h h2; rfl
#align equiv.cast_trans Equiv.cast_trans

theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ HEq a b := by
  subst h; simp [coe_refl]
#align equiv.cast_eq_iff_heq Equiv.cast_eq_iff_heq

theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun H => by simp [H.symm], fun H => by simp [H]⟩
#align equiv.symm_apply_eq Equiv.symm_apply_eq

theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
  (eq_comm.trans e.symm_apply_eq).trans eq_comm
#align equiv.eq_symm_apply Equiv.eq_symm_apply

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by cases e; rfl
#align equiv.symm_symm Equiv.symm_symm

theorem symm_bijective : Function.Bijective (Equiv.symm : (α ≃ β) → β ≃ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp] theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e := by cases e; rfl
#align equiv.trans_refl Equiv.trans_refl

@[simp] theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α := rfl
#align equiv.refl_symm Equiv.refl_symm

@[simp] theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e := by cases e; rfl
#align equiv.refl_trans Equiv.refl_trans

@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β := ext <| by simp
#align equiv.symm_trans_self Equiv.symm_trans_self

@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α := ext <| by simp
#align equiv.self_trans_symm Equiv.self_trans_symm

theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := Equiv.ext fun _ => rfl
#align equiv.trans_assoc Equiv.trans_assoc

theorem leftInverse_symm (f : Equiv α β) : LeftInverse f.symm f := f.left_inv
#align equiv.left_inverse_symm Equiv.leftInverse_symm

theorem rightInverse_symm (f : Equiv α β) : Function.RightInverse f.symm f := f.right_inv
#align equiv.right_inverse_symm Equiv.rightInverse_symm

theorem injective_comp (e : α ≃ β) (f : β → γ) : Injective (f ∘ e) ↔ Injective f :=
  EquivLike.injective_comp e f
#align equiv.injective_comp Equiv.injective_comp

theorem comp_injective (f : α → β) (e : β ≃ γ) : Injective (e ∘ f) ↔ Injective f :=
  EquivLike.comp_injective f e
#align equiv.comp_injective Equiv.comp_injective

theorem surjective_comp (e : α ≃ β) (f : β → γ) : Surjective (f ∘ e) ↔ Surjective f :=
  EquivLike.surjective_comp e f
#align equiv.surjective_comp Equiv.surjective_comp

theorem comp_surjective (f : α → β) (e : β ≃ γ) : Surjective (e ∘ f) ↔ Surjective f :=
  EquivLike.comp_surjective f e
#align equiv.comp_surjective Equiv.comp_surjective

theorem bijective_comp (e : α ≃ β) (f : β → γ) : Bijective (f ∘ e) ↔ Bijective f :=
  EquivLike.bijective_comp e f
#align equiv.bijective_comp Equiv.bijective_comp

theorem comp_bijective (f : α → β) (e : β ≃ γ) : Bijective (e ∘ f) ↔ Bijective f :=
  EquivLike.comp_bijective f e
#align equiv.comp_bijective Equiv.comp_bijective

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equivCongr {δ : Sort*} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) where
  toFun ac := (ab.symm.trans ac).trans cd
  invFun bd := ab.trans <| bd.trans <| cd.symm
  left_inv ac := by ext x; simp only [trans_apply, comp_apply, symm_apply_apply]
  right_inv ac := by ext x; simp only [trans_apply, comp_apply, apply_symm_apply]
#align equiv.equiv_congr Equiv.equivCongr

@[simp] theorem equivCongr_refl {α β} :
    (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) := by ext; rfl
#align equiv.equiv_congr_refl Equiv.equivCongr_refl

@[simp] theorem equivCongr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
    (ab.equivCongr cd).symm = ab.symm.equivCongr cd.symm := by ext; rfl
#align equiv.equiv_congr_symm Equiv.equivCongr_symm

@[simp] theorem equivCongr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
    (ab.equivCongr de).trans (bc.equivCongr ef) = (ab.trans bc).equivCongr (de.trans ef) := by
  ext; rfl
#align equiv.equiv_congr_trans Equiv.equivCongr_trans

@[simp] theorem equivCongr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
    (Equiv.refl α).equivCongr bg e = e.trans bg := rfl
#align equiv.equiv_congr_refl_left Equiv.equivCongr_refl_left

@[simp] theorem equivCongr_refl_right {α β} (ab e : α ≃ β) :
    ab.equivCongr (Equiv.refl β) e = ab.symm.trans e := rfl
#align equiv.equiv_congr_refl_right Equiv.equivCongr_refl_right

@[simp] theorem equivCongr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
    ab.equivCongr cd e x = cd (e (ab.symm x)) := rfl
#align equiv.equiv_congr_apply_apply Equiv.equivCongr_apply_apply

section permCongr

variable {α' β' : Type*} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `Perm α` is equivalent to `Perm β`. -/
def permCongr : Perm α' ≃ Perm β' := equivCongr e e
#align equiv.perm_congr Equiv.permCongr

theorem permCongr_def (p : Equiv.Perm α') : e.permCongr p = (e.symm.trans p).trans e := rfl
#align equiv.perm_congr_def Equiv.permCongr_def

@[simp] theorem permCongr_refl : e.permCongr (Equiv.refl _) = Equiv.refl _ := by
  simp [permCongr_def]
#align equiv.perm_congr_refl Equiv.permCongr_refl

@[simp] theorem permCongr_symm : e.permCongr.symm = e.symm.permCongr := rfl
#align equiv.perm_congr_symm Equiv.permCongr_symm

@[simp] theorem permCongr_apply (p : Equiv.Perm α') (x) : e.permCongr p x = e (p (e.symm x)) := rfl
#align equiv.perm_congr_apply Equiv.permCongr_apply

theorem permCongr_symm_apply (p : Equiv.Perm β') (x) :
    e.permCongr.symm p x = e.symm (p (e x)) := rfl
#align equiv.perm_congr_symm_apply Equiv.permCongr_symm_apply

theorem permCongr_trans (p p' : Equiv.Perm α') :
    (e.permCongr p).trans (e.permCongr p') = e.permCongr (p.trans p') := by
  ext; simp only [trans_apply, comp_apply, permCongr_apply, symm_apply_apply]
#align equiv.perm_congr_trans Equiv.permCongr_trans

end permCongr

/-- Two empty types are equivalent. -/
def equivOfIsEmpty (α β : Sort*) [IsEmpty α] [IsEmpty β] : α ≃ β :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩
#align equiv.equiv_of_is_empty Equiv.equivOfIsEmpty

/-- If `α` is an empty type, then it is equivalent to the `Empty` type. -/
def equivEmpty (α : Sort u) [IsEmpty α] : α ≃ Empty := equivOfIsEmpty α _
#align equiv.equiv_empty Equiv.equivEmpty

/-- If `α` is an empty type, then it is equivalent to the `PEmpty` type in any universe. -/
def equivPEmpty (α : Sort v) [IsEmpty α] : α ≃ PEmpty.{u} := equivOfIsEmpty α _
#align equiv.equiv_pempty Equiv.equivPEmpty

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equivEmptyEquiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.isEmpty e, @equivEmpty α, fun e => ext fun x => (e x).elim, fun _ => rfl⟩
#align equiv.equiv_empty_equiv Equiv.equivEmptyEquiv

/-- The `Sort` of proofs of a false proposition is equivalent to `PEmpty`. -/
def propEquivPEmpty {p : Prop} (h : ¬p) : p ≃ PEmpty := @equivPEmpty p <| IsEmpty.prop_iff.2 h
#align equiv.prop_equiv_pempty Equiv.propEquivPEmpty

/-- If both `α` and `β` have a unique element, then `α ≃ β`. -/
def equivOfUnique (α β : Sort _) [Unique.{u} α] [Unique.{v} β] : α ≃ β where
  toFun := default
  invFun := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align equiv.equiv_of_unique Equiv.equivOfUnique

/-- If `α` has a unique element, then it is equivalent to any `PUnit`. -/
def equivPUnit (α : Sort u) [Unique α] : α ≃ PUnit.{v} := equivOfUnique α _
#align equiv.equiv_punit Equiv.equivPUnit

/-- The `Sort` of proofs of a true proposition is equivalent to `PUnit`. -/
def propEquivPUnit {p : Prop} (h : p) : p ≃ PUnit.{0} := @equivPUnit p <| uniqueProp h
#align equiv.prop_equiv_punit Equiv.propEquivPUnit

/-- `ULift α` is equivalent to `α`. -/
@[simps (config := .asFn) apply]
protected def ulift {α : Type v} : ULift.{u} α ≃ α :=
  ⟨ULift.down, ULift.up, ULift.up_down, ULift.down_up.{v, u}⟩
#align equiv.ulift Equiv.ulift
#align equiv.ulift_apply Equiv.ulift_apply

/-- `PLift α` is equivalent to `α`. -/
@[simps (config := .asFn) apply]
protected def plift : PLift α ≃ α := ⟨PLift.down, PLift.up, PLift.up_down, PLift.down_up⟩
#align equiv.plift Equiv.plift
#align equiv.plift_apply Equiv.plift_apply

/-- equivalence of propositions is the same as iff -/
def ofIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q := ⟨h.mp, h.mpr, fun _ => rfl, fun _ => rfl⟩
#align equiv.of_iff Equiv.ofIff

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
-- Porting note: removing `congr` attribute
@[simps apply]
def arrowCongr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) where
  toFun f := e₂ ∘ f ∘ e₁.symm
  invFun f := e₂.symm ∘ f ∘ e₁
  left_inv f := funext fun x => by simp only [comp_apply, symm_apply_apply]
  right_inv f := funext fun x => by simp only [comp_apply, apply_symm_apply]
#align equiv.arrow_congr_apply Equiv.arrowCongr_apply
#align equiv.arrow_congr Equiv.arrowCongr

theorem arrowCongr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ → β₁) (g : β₁ → γ₁) :
    arrowCongr ea ec (g ∘ f) = arrowCongr eb ec g ∘ arrowCongr ea eb f := by
  ext; simp only [comp, arrowCongr_apply, eb.symm_apply_apply]
#align equiv.arrow_congr_comp Equiv.arrowCongr_comp

@[simp] theorem arrowCongr_refl {α β : Sort*} :
    arrowCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl
#align equiv.arrow_congr_refl Equiv.arrowCongr_refl

@[simp] theorem arrowCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := rfl
#align equiv.arrow_congr_trans Equiv.arrowCongr_trans

@[simp] theorem arrowCongr_symm {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := rfl
#align equiv.arrow_congr_symm Equiv.arrowCongr_symm

/-- A version of `Equiv.arrowCongr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `Equiv.arrowCongr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
-- Porting note: removing `congr` attribute
@[simps! apply]
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ
#align equiv.arrow_congr' Equiv.arrowCongr'
#align equiv.arrow_congr'_apply Equiv.arrowCongr'_apply

@[simp] theorem arrowCongr'_refl {α β : Type*} :
    arrowCongr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) := rfl
#align equiv.arrow_congr'_refl Equiv.arrowCongr'_refl

@[simp] theorem arrowCongr'_trans {α₁ α₂ β₁ β₂ α₃ β₃ : Type*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl
#align equiv.arrow_congr'_trans Equiv.arrowCongr'_trans

@[simp] theorem arrowCongr'_symm {α₁ α₂ β₁ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm := rfl
#align equiv.arrow_congr'_symm Equiv.arrowCongr'_symm

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps! apply] def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrowCongr e e
#align equiv.conj Equiv.conj
#align equiv.conj_apply Equiv.conj_apply

@[simp] theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) := rfl
#align equiv.conj_refl Equiv.conj_refl

@[simp] theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl
#align equiv.conj_symm Equiv.conj_symm

@[simp] theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (e₁.trans e₂).conj = e₁.conj.trans e₂.conj := rfl
#align equiv.conj_trans Equiv.conj_trans

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := fun x ↦ x`. This causes nontermination.
theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ := by
  apply arrowCongr_comp
#align equiv.conj_comp Equiv.conj_comp

theorem eq_comp_symm {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : f = g ∘ e.symm ↔ f ∘ e = g :=
  (e.arrowCongr (Equiv.refl γ)).symm_apply_eq.symm
#align equiv.eq_comp_symm Equiv.eq_comp_symm

theorem comp_symm_eq {α β γ} (e : α ≃ β) (f : β → γ) (g : α → γ) : g ∘ e.symm = f ↔ g = f ∘ e :=
  (e.arrowCongr (Equiv.refl γ)).eq_symm_apply.symm
#align equiv.comp_symm_eq Equiv.comp_symm_eq

theorem eq_symm_comp {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : f = e.symm ∘ g ↔ e ∘ f = g :=
  ((Equiv.refl γ).arrowCongr e).eq_symm_apply
#align equiv.eq_symm_comp Equiv.eq_symm_comp

theorem symm_comp_eq {α β γ} (e : α ≃ β) (f : γ → α) (g : γ → β) : e.symm ∘ g = f ↔ g = e ∘ f :=
  ((Equiv.refl γ).arrowCongr e).symm_apply_eq
#align equiv.symm_comp_eq Equiv.symm_comp_eq

/-- `PUnit` sorts in any two universes are equivalent. -/
def punitEquivPUnit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => .unit, fun _ => .unit, fun ⟨⟩ => rfl, fun ⟨⟩ => rfl⟩
#align equiv.punit_equiv_punit Equiv.punitEquivPUnit

/-- `Prop` is noncomputably equivalent to `Bool`. -/
noncomputable def propEquivBool : Prop ≃ Bool where
  toFun p := @decide p (Classical.propDecidable _)
  invFun b := b
  left_inv p := by simp [@Bool.decide_iff p (Classical.propDecidable _)]
  right_inv b := by cases b <;> simp
#align equiv.Prop_equiv_bool Equiv.propEquivBool

section

/-- The sort of maps to `PUnit.{v}` is equivalent to `PUnit.{w}`. -/
def arrowPUnitEquivPUnit (α : Sort*) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun _ => .unit, fun _ _ => .unit, fun _ => rfl, fun _ => rfl⟩
#align equiv.arrow_punit_equiv_punit Equiv.arrowPUnitEquivPUnit

/-- The equivalence `(∀ i, β i) ≃ β ⋆` when the domain of `β` only contains `⋆` -/
@[simps (config := .asFn)]
def piUnique [Unique α] (β : α → Sort*) : (∀ i, β i) ≃ β default where
  toFun f := f default
  invFun := uniqueElim
  left_inv f := by ext i; cases Unique.eq_default i; rfl
  right_inv x := rfl

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps! (config := .asFn) apply symm_apply]
def funUnique (α β) [Unique.{u} α] : (α → β) ≃ β := piUnique _
#align equiv.fun_unique Equiv.funUnique
#align equiv.fun_unique_apply Equiv.funUnique_apply

/-- The sort of maps from `PUnit` is equivalent to the codomain. -/
def punitArrowEquiv (α : Sort*) : (PUnit.{u} → α) ≃ α := funUnique PUnit.{u} α
#align equiv.punit_arrow_equiv Equiv.punitArrowEquiv

/-- The sort of maps from `True` is equivalent to the codomain. -/
def trueArrowEquiv (α : Sort*) : (True → α) ≃ α := funUnique _ _
#align equiv.true_arrow_equiv Equiv.trueArrowEquiv

/-- The sort of maps from a type that `IsEmpty` is equivalent to `PUnit`. -/
def arrowPUnitOfIsEmpty (α β : Sort*) [IsEmpty α] : (α → β) ≃ PUnit.{u} where
  toFun _ := PUnit.unit
  invFun _ := isEmptyElim
  left_inv _ := funext isEmptyElim
  right_inv _ := rfl
#align equiv.arrow_punit_of_is_empty Equiv.arrowPUnitOfIsEmpty

/-- The sort of maps from `Empty` is equivalent to `PUnit`. -/
def emptyArrowEquivPUnit (α : Sort*) : (Empty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.empty_arrow_equiv_punit Equiv.emptyArrowEquivPUnit

/-- The sort of maps from `PEmpty` is equivalent to `PUnit`. -/
def pemptyArrowEquivPUnit (α : Sort*) : (PEmpty → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.pempty_arrow_equiv_punit Equiv.pemptyArrowEquivPUnit

/-- The sort of maps from `False` is equivalent to `PUnit`. -/
def falseArrowEquivPUnit (α : Sort*) : (False → α) ≃ PUnit.{u} := arrowPUnitOfIsEmpty _ _
#align equiv.false_arrow_equiv_punit Equiv.falseArrowEquivPUnit

end

section

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps apply symm_apply]
def psigmaEquivSigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_sigma Equiv.psigmaEquivSigma
#align equiv.psigma_equiv_sigma_symm_apply Equiv.psigmaEquivSigma_symm_apply
#align equiv.psigma_equiv_sigma_apply Equiv.psigmaEquivSigma_apply

/-- A `PSigma`-type is equivalent to the corresponding `Sigma`-type. -/
@[simps apply symm_apply]
def psigmaEquivSigmaPLift {α} (β : α → Sort*) : (Σ' i, β i) ≃ Σ i : PLift α, PLift (β i.down) where
  toFun a := ⟨PLift.up a.1, PLift.up a.2⟩
  invFun a := ⟨a.1.down, a.2.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_sigma_plift Equiv.psigmaEquivSigmaPLift
#align equiv.psigma_equiv_sigma_plift_symm_apply Equiv.psigmaEquivSigmaPLift_symm_apply
#align equiv.psigma_equiv_sigma_plift_apply Equiv.psigmaEquivSigmaPLift_apply

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigmaCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv | ⟨a, b⟩ => congr_arg (PSigma.mk a) <| symm_apply_apply (F a) b
  right_inv | ⟨a, b⟩ => congr_arg (PSigma.mk a) <| apply_symm_apply (F a) b
#align equiv.psigma_congr_right Equiv.psigmaCongrRight
#align equiv.psigma_congr_right_apply Equiv.psigmaCongrRight_apply

-- Porting note (#10618): simp can now simplify the LHS, so I have removed `@[simp]`
theorem psigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Sort*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (psigmaCongrRight F).trans (psigmaCongrRight G) =
      psigmaCongrRight fun a => (F a).trans (G a) := rfl
#align equiv.psigma_congr_right_trans Equiv.psigmaCongrRight_trans

-- Porting note (#10618): simp can now simplify the LHS, so I have removed `@[simp]`
theorem psigmaCongrRight_symm {α} {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (psigmaCongrRight F).symm = psigmaCongrRight fun a => (F a).symm := rfl
#align equiv.psigma_congr_right_symm Equiv.psigmaCongrRight_symm

-- Porting note (#10618): simp can now prove this, so I have removed `@[simp]`
theorem psigmaCongrRight_refl {α} {β : α → Sort*} :
    (psigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ' a, β a) := rfl
#align equiv.psigma_congr_right_refl Equiv.psigmaCongrRight_refl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigmaCongrRight {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun a := ⟨a.1, F a.1 a.2⟩
  invFun a := ⟨a.1, (F a.1).symm a.2⟩
  left_inv | ⟨a, b⟩ => congr_arg (Sigma.mk a) <| symm_apply_apply (F a) b
  right_inv | ⟨a, b⟩ => congr_arg (Sigma.mk a) <| apply_symm_apply (F a) b
#align equiv.sigma_congr_right Equiv.sigmaCongrRight
#align equiv.sigma_congr_right_apply Equiv.sigmaCongrRight_apply

-- Porting note (#10618): simp can now simplify the LHS, so I have removed `@[simp]`
theorem sigmaCongrRight_trans {α} {β₁ β₂ β₃ : α → Type*}
    (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) =
      sigmaCongrRight fun a => (F a).trans (G a) := rfl
#align equiv.sigma_congr_right_trans Equiv.sigmaCongrRight_trans

-- Porting note (#10618): simp can now simplify the LHS, so I have removed `@[simp]`
theorem sigmaCongrRight_symm {α} {β₁ β₂ : α → Type*} (F : ∀ a, β₁ a ≃ β₂ a) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm := rfl
#align equiv.sigma_congr_right_symm Equiv.sigmaCongrRight_symm

-- Porting note (#10618): simp can now prove this, so I have removed `@[simp]`
theorem sigmaCongrRight_refl {α} {β : α → Type*} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) := rfl
#align equiv.sigma_congr_right_refl Equiv.sigmaCongrRight_refl

/-- A `PSigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigmaEquivSubtype {α : Type v} (P : α → Prop) : (Σ' i, P i) ≃ Subtype P where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.psigma_equiv_subtype Equiv.psigmaEquivSubtype

/-- A `Sigma` with `PLift` fibers is equivalent to the subtype. -/
def sigmaPLiftEquivSubtype {α : Type v} (P : α → Prop) : (Σ i, PLift (P i)) ≃ Subtype P :=
  ((psigmaEquivSigma _).symm.trans
    (psigmaCongrRight fun _ => Equiv.plift)).trans (psigmaEquivSubtype P)
#align equiv.sigma_plift_equiv_subtype Equiv.sigmaPLiftEquivSubtype

/-- A `Sigma` with `fun i ↦ ULift (PLift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigmaPLiftEquivSubtype`.
-/
def sigmaULiftPLiftEquivSubtype {α : Type v} (P : α → Prop) :
    (Σ i, ULift (PLift (P i))) ≃ Subtype P :=
  (sigmaCongrRight fun _ => Equiv.ulift).trans (sigmaPLiftEquivSubtype P)
#align equiv.sigma_ulift_plift_equiv_subtype Equiv.sigmaULiftPLiftEquivSubtype

namespace Perm

/-- A family of permutations `Π a, Perm (β a)` generates a permutation `Perm (Σ a, β₁ a)`. -/
abbrev sigmaCongrRight {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) : Perm (Σ a, β a) :=
  Equiv.sigmaCongrRight F
#align equiv.perm.sigma_congr_right Equiv.Perm.sigmaCongrRight

@[simp] theorem sigmaCongrRight_trans {α} {β : α → Sort _}
    (F : ∀ a, Perm (β a)) (G : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).trans (sigmaCongrRight G) = sigmaCongrRight fun a => (F a).trans (G a) :=
  Equiv.sigmaCongrRight_trans F G
#align equiv.perm.sigma_congr_right_trans Equiv.Perm.sigmaCongrRight_trans

@[simp] theorem sigmaCongrRight_symm {α} {β : α → Sort _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F).symm = sigmaCongrRight fun a => (F a).symm :=
  Equiv.sigmaCongrRight_symm F
#align equiv.perm.sigma_congr_right_symm Equiv.Perm.sigmaCongrRight_symm

@[simp] theorem sigmaCongrRight_refl {α} {β : α → Sort _} :
    (sigmaCongrRight fun a => Equiv.refl (β a)) = Equiv.refl (Σ a, β a) :=
  Equiv.sigmaCongrRight_refl
#align equiv.perm.sigma_congr_right_refl Equiv.Perm.sigmaCongrRight_refl

end Perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply] def sigmaCongrLeft {α₁ α₂ : Type*} {β : α₂ → Sort _} (e : α₁ ≃ α₂) :
    (Σ a : α₁, β (e a)) ≃ Σ a : α₂, β a where
  toFun a := ⟨e a.1, a.2⟩
  invFun a := ⟨e.symm a.1, (e.right_inv' a.1).symm ▸ a.2⟩
  -- Porting note: this was a pretty gnarly match already, and it got worse after porting
  left_inv := fun ⟨a, b⟩ =>
    match (motive := ∀ a' (h : a' = a), Sigma.mk _ (congr_arg e h.symm ▸ b) = ⟨a, b⟩)
      e.symm (e a), e.left_inv a with
    | _, rfl => rfl
  right_inv := fun ⟨a, b⟩ =>
    match (motive := ∀ a' (h : a' = a), Sigma.mk a' (h.symm ▸ b) = ⟨a, b⟩)
      e (e.symm a), e.apply_symm_apply _ with
    | _, rfl => rfl
#align equiv.sigma_congr_left_apply Equiv.sigmaCongrLeft_apply
#align equiv.sigma_congr_left Equiv.sigmaCongrLeft

/-- Transporting a sigma type through an equivalence of the base -/
def sigmaCongrLeft' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) :
    (Σ a : α₁, β a) ≃ Σ a : α₂, β (f.symm a) := (sigmaCongrLeft f.symm).symm
#align equiv.sigma_congr_left' Equiv.sigmaCongrLeft'

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigmaCongr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂)
    (F : ∀ a, β₁ a ≃ β₂ (f a)) : Sigma β₁ ≃ Sigma β₂ :=
  (sigmaCongrRight F).trans (sigmaCongrLeft f)
#align equiv.sigma_congr Equiv.sigmaCongr

/-- `Sigma` type with a constant fiber is equivalent to the product. -/
@[simps (config := { attrs := [`mfld_simps] }) apply symm_apply]
def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
#align equiv.sigma_equiv_prod_apply Equiv.sigmaEquivProd_apply
#align equiv.sigma_equiv_prod_symm_apply Equiv.sigmaEquivProd_symm_apply
#align equiv.sigma_equiv_prod Equiv.sigmaEquivProd

/-- If each fiber of a `Sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigmaEquivProdOfEquiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigmaCongrRight F).trans (sigmaEquivProd α β)
#align equiv.sigma_equiv_prod_of_equiv Equiv.sigmaEquivProdOfEquiv

/-- Dependent product of types is associative up to an equivalence. -/
def sigmaAssoc {α : Type*} {β : α → Type*} (γ : ∀ a : α, β a → Type*) :
    (Σ ab : Σ a : α, β a, γ ab.1 ab.2) ≃ Σ a : α, Σ b : β a, γ a b where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.sigma_assoc Equiv.sigmaAssoc

end

protected theorem exists_unique_congr {p : α → Prop} {q : β → Prop}
    (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) : (∃! x, p x) ↔ ∃! y, q y := by
  constructor
  · rintro ⟨a, ha₁, ha₂⟩
    exact ⟨f a, h.1 ha₁, fun b hb => f.symm_apply_eq.1 (ha₂ (f.symm b) (h.2 (by simpa using hb)))⟩
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨f.symm b, h.2 (by simpa using hb₁), fun y hy => (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩
#align equiv.exists_unique_congr Equiv.exists_unique_congr

protected theorem exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) :
    (∃! x, p x) ↔ ∃! y, p (f.symm y) := Equiv.exists_unique_congr f fun {_} => by simp
#align equiv.exists_unique_congr_left' Equiv.exists_unique_congr_left'

protected theorem exists_unique_congr_left {p : β → Prop} (f : α ≃ β) :
    (∃! x, p (f x)) ↔ ∃! y, p y := (Equiv.exists_unique_congr_left' f.symm).symm
#align equiv.exists_unique_congr_left Equiv.exists_unique_congr_left

protected theorem forall_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
    (h : ∀ {x}, p x ↔ q (f x)) : (∀ x, p x) ↔ (∀ y, q y) := by
  constructor <;> intro h₂ x
  · rw [← f.right_inv x]; exact h.mp (h₂ _)
  · exact h.mpr (h₂ _)
#align equiv.forall_congr Equiv.forall_congr

protected theorem forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β)
    (h : ∀ {x}, p (f.symm x) ↔ q x) : (∀ x, p x) ↔ ∀ y, q y :=
  (Equiv.forall_congr f.symm h.symm).symm
#align equiv.forall_congr' Equiv.forall_congr'

-- We next build some higher arity versions of `Equiv.forall_congr`.
-- Although they appear to just be repeated applications of `Equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)

protected theorem forall₂_congr {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) :
    (∀ x y, p x y) ↔ ∀ x y, q x y :=
  Equiv.forall_congr _ <| Equiv.forall_congr _ h
#align equiv.forall₂_congr Equiv.forall₂_congr

protected theorem forall₂_congr' {α₁ α₂ β₁ β₂ : Sort*} {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
    (∀ x y, p x y) ↔ ∀ x y, q x y := (Equiv.forall₂_congr eα.symm eβ.symm h.symm).symm
#align equiv.forall₂_congr' Equiv.forall₂_congr'

protected theorem forall₃_congr
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  Equiv.forall₂_congr _ _ <| Equiv.forall_congr _ h
#align equiv.forall₃_congr Equiv.forall₃_congr

protected theorem forall₃_congr'
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*} {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
    (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm h.symm).symm
#align equiv.forall₃_congr' Equiv.forall₃_congr'

protected theorem forall_congr_left' {p : α → Prop} (f : α ≃ β) : (∀ x, p x) ↔ ∀ y, p (f.symm y) :=
  Equiv.forall_congr f <| by simp
#align equiv.forall_congr_left' Equiv.forall_congr_left'

protected theorem forall_congr_left {p : β → Prop} (f : α ≃ β) : (∀ x, p (f x)) ↔ ∀ y, p y :=
  (Equiv.forall_congr_left' f.symm).symm
#align equiv.forall_congr_left Equiv.forall_congr_left

protected theorem exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} :
    (∃ a, p a) ↔ ∃ b, p (f.symm b) :=
  ⟨fun ⟨a, h⟩ => ⟨f a, by simpa using h⟩, fun ⟨b, h⟩ => ⟨_, h⟩⟩
#align equiv.exists_congr_left Equiv.exists_congr_left

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def ofBijective (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := surjInv hf.surjective
  left_inv := leftInverse_surjInv hf
  right_inv := rightInverse_surjInv _
#align equiv.of_bijective Equiv.ofBijective
#align equiv.of_bijective_apply Equiv.ofBijective_apply

lemma ofBijective_apply_symm_apply (f : α → β) (hf : Bijective f) (x : β) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x
#align equiv.of_bijective_apply_symm_apply Equiv.ofBijective_apply_symm_apply

@[simp]
lemma ofBijective_symm_apply_apply (f : α → β) (hf : Bijective f) (x : α) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x
#align equiv.of_bijective_symm_apply_apply Equiv.ofBijective_symm_apply_apply

end Equiv

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) : Quot ra ≃ Quot rb where
  toFun := Quot.map e fun a₁ a₂ => (eq a₁ a₂).1
  invFun := Quot.map e.symm fun b₁ b₂ h =>
    (eq (e.symm b₁) (e.symm b₂)).2
      ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)
  left_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.symm_apply_apply]
  right_inv := by rintro ⟨a⟩; simp only [Quot.map, Equiv.apply_symm_apply]
#align quot.congr Quot.congr

@[simp] theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
    Quot.congr e eq (Quot.mk ra a) = Quot.mk rb (e a) := rfl
#align quot.congr_mk Quot.congr_mk

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
    Quot r ≃ Quot r' := Quot.congr (Equiv.refl α) eq
#align quot.congr_right Quot.congrRight

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congrLeft {r : α → α → Prop} (e : α ≃ β) :
    Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  Quot.congr e fun _ _ => by simp only [e.symm_apply_apply]
#align quot.congr_left Quot.congrLeft

end Quot

namespace Quotient

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂)`. -/
protected def congr {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂, @Setoid.r α ra a₁ a₂ ↔ @Setoid.r β rb (e a₁) (e a₂)) :
    Quotient ra ≃ Quotient rb := Quot.congr e eq
#align quotient.congr Quotient.congr

@[simp] theorem congr_mk {ra : Setoid α} {rb : Setoid β} (e : α ≃ β)
    (eq : ∀ a₁ a₂ : α, Setoid.r a₁ a₂ ↔ Setoid.r (e a₁) (e a₂)) (a : α) :
    Quotient.congr e eq (Quotient.mk ra a) = Quotient.mk rb (e a) := rfl
#align quotient.congr_mk Quotient.congr_mk

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congrRight {r r' : Setoid α}
    (eq : ∀ a₁ a₂, @Setoid.r α r a₁ a₂ ↔ @Setoid.r α r' a₁ a₂) : Quotient r ≃ Quotient r' :=
  Quot.congrRight eq
#align quotient.congr_right Quotient.congrRight

end Quotient
