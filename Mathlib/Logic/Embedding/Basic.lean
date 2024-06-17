/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Option.Basic
import Mathlib.Data.Prod.PProd
import Mathlib.Logic.Equiv.Basic

#align_import logic.embedding.basic from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Injective functions
-/

universe u v w x

namespace Function

-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
/-- `α ↪ β` is a bundled injective function. -/
structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun
#align function.embedding Function.Embedding

/-- An embedding, a.k.a. a bundled injective function. -/
infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : FunLike (α ↪ β) α β where
  coe := Embedding.toFun
  coe_injective' f g h := by { cases f; cases g; congr }

instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β where
  injective' := Embedding.inj'

initialize_simps_projections Embedding (toFun → apply)

-- Porting note: this needs `tactic.lift`.
--instance {α β : Sort*} : CanLift (α → β) (α ↪ β) coeFn Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩

theorem exists_surjective_iff {α β : Sort*} :
    (∃ f : α → β, Surjective f) ↔ Nonempty (α → β) ∧ Nonempty (β ↪ α) :=
  ⟨fun ⟨f, h⟩ ↦ ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ ↦ (nonempty_fun.mp h).elim
    (fun _ ↦ ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ ↦ ⟨_, invFun_surjective e.inj'⟩⟩

instance {α β : Sort*} : CanLift (α → β) (α ↪ β) (↑) Injective where
  prf _ h := ⟨⟨_, h⟩, rfl⟩

end Function

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `Equiv.coeEmbedding`.
The explicit `Equiv.toEmbedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f.toEmbedding = s.map f := by simp
-- Error, `f` has type `Fin 3 ≃ Fin 3` but is expected to have type `Fin 3 ↪ ?m_1 : Type ?`
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f = s.map f.toEmbedding := by simp
```
-/
protected def Equiv.toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩
#align equiv.to_embedding Equiv.toEmbedding

@[simp]
theorem Equiv.coe_toEmbedding : (f.toEmbedding : α → β) = f :=
  rfl
#align equiv.coe_to_embedding Equiv.coe_toEmbedding

theorem Equiv.toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl
#align equiv.to_embedding_apply Equiv.toEmbedding_apply

theorem Equiv.toEmbedding_injective : Function.Injective (Equiv.toEmbedding : (α ≃ β) → (α ↪ β)) :=
  fun _ _ h ↦ by rwa [DFunLike.ext'_iff] at h ⊢

instance Equiv.coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩
#align equiv.coe_embedding Equiv.coeEmbedding

@[instance] abbrev Equiv.Perm.coeEmbedding : Coe (Equiv.Perm α) (α ↪ α) :=
  Equiv.coeEmbedding
#align equiv.perm.coe_embedding Equiv.Perm.coeEmbedding

-- Porting note : `theorem Equiv.coe_eq_to_embedding : ↑f = f.toEmbedding` is a
-- syntactic tautology in Lean 4

end Equiv

namespace Function

namespace Embedding

theorem coe_injective {α β} : @Injective (α ↪ β) (α → β) (fun f ↦ ↑f) :=
  DFunLike.coe_injective
#align function.embedding.coe_injective Function.Embedding.coe_injective

@[ext]
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
#align function.embedding.ext Function.Embedding.ext

instance {α β : Sort*} [IsEmpty α] : Unique (α ↪ β) where
  default := ⟨isEmptyElim, Function.injective_of_subsingleton _⟩
  uniq := by intro; ext v; exact isEmptyElim v

-- Porting note : in Lean 3 `DFunLike.ext_iff.symm` works
theorem ext_iff {α β} {f g : Embedding α β} : (∀ x, f x = g x) ↔ f = g :=
  Iff.symm (DFunLike.ext_iff)
#align function.embedding.ext_iff Function.Embedding.ext_iff

@[simp]
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl
#align function.embedding.to_fun_eq_coe Function.Embedding.toFun_eq_coe

@[simp]
theorem coeFn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl
#align function.embedding.coe_fn_mk Function.Embedding.coeFn_mk

@[simp]
theorem mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f :=
  rfl
#align function.embedding.mk_coe Function.Embedding.mk_coe

protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f
#align function.embedding.injective Function.Embedding.injective

theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f
#align function.embedding.apply_eq_iff_eq Function.Embedding.apply_eq_iff_eq

/-- The identity map as a `Function.Embedding`. -/
@[refl, simps (config := { simpRhs := true })]
protected def refl (α : Sort*) : α ↪ α :=
  ⟨id, injective_id⟩
#align function.embedding.refl Function.Embedding.refl
#align function.embedding.refl_apply Function.Embedding.refl_apply

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps (config := { simpRhs := true })]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩
#align function.embedding.trans Function.Embedding.trans
#align function.embedding.trans_apply Function.Embedding.trans_apply

instance : Trans Embedding Embedding Embedding := ⟨Embedding.trans⟩

@[simp]
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  ext
  simp
#align function.embedding.equiv_to_embedding_trans_symm_to_embedding Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding

@[simp]
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  ext
  simp
#align function.embedding.equiv_symm_to_embedding_trans_to_embedding Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

/-- Transfer an embedding along a pair of equivalences. -/
@[simps! (config := { fullyApplied := false, simpRhs := true })]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)
#align function.embedding.congr Function.Embedding.congr
#align function.embedding.congr_apply Function.Embedding.congr_apply

/-- A right inverse `surjInv` of a surjective function as an `Embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩
#align function.embedding.of_surjective Function.Embedding.ofSurjective

/-- Convert a surjective `Embedding` to an `Equiv` -/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.injective, hf⟩
#align function.embedding.equiv_of_surjective Function.Embedding.equivOfSurjective

/-- There is always an embedding from an empty type. -/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩
#align function.embedding.of_is_empty Function.Embedding.ofIsEmpty

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def setValue {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y (h : ite _ _ _ = ite _ _ _)
    -- TODO: once we have `cc` we can avoid all the manual cases below by doing
    -- split_ifs at h <;> (try subst b) <;> (try simp only [f.injective.eq_iff] at *) <;> cc
    split_ifs at h with h₁ h₂ _ _ h₅ h₆ <;>
        (try subst b) <;>
        (try simp only [f.injective.eq_iff, not_true_eq_false] at *)
    · rw [h₁,h₂]
    · rw [h₁,h]
    · rw [h₅, ← h]
    · exact h₆.symm
    · exfalso; exact h₅ h.symm
    · exfalso; exact h₁ h
    · exact h ⟩
#align function.embedding.set_value Function.Embedding.setValue

@[simp]
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a = b := by
  simp [setValue]
#align function.embedding.set_value_eq Function.Embedding.setValue_eq

@[simp]
theorem setValue_eq_iff {α β} (f : α ↪ β) {a a' : α} {b : β} [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a' = b ↔ a' = a :=
  (setValue f a b).injective.eq_iff' <| setValue_eq ..

/-- Embedding into `Option α` using `some`. -/
@[simps (config := .asFn)]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩
#align function.embedding.some Function.Embedding.some
#align function.embedding.some_apply Function.Embedding.some_apply

-- Porting note: Lean 4 unfolds coercion `α → Option α` to `some`, so there is no separate
-- `Function.Embedding.coeOption`.
#align function.embedding.coe_option Function.Embedding.some

/-- A version of `Option.map` for `Function.Embedding`s. -/
@[simps (config := .asFn)]
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.injective⟩
#align function.embedding.option_map Function.Embedding.optionMap
#align function.embedding.option_map_apply Function.Embedding.optionMap_apply

/-- Embedding of a `Subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩
#align function.embedding.subtype Function.Embedding.subtype

@[simp]
theorem coe_subtype {α} (p : α → Prop) : ↑(subtype p) = Subtype.val :=
  rfl
#align function.embedding.coe_subtype Function.Embedding.coe_subtype

/-- `Quotient.out` as an embedding. -/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩
#align function.embedding.quotient_out Function.Embedding.quotientOut

@[simp]
theorem coe_quotientOut (α) [Setoid α] : ↑(quotientOut α) = Quotient.out :=
  rfl
#align function.embedding.coe_quotient_out Function.Embedding.coe_quotientOut

/-- Choosing an element `b : β` gives an embedding of `PUnit` into `β`. -/
def punit {β : Sort*} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩
#align function.embedding.punit Function.Embedding.punit

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩
#align function.embedding.sectl Function.Embedding.sectl
#align function.embedding.sectl_apply Function.Embedding.sectl_apply

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩
#align function.embedding.sectr Function.Embedding.sectr
#align function.embedding.sectr_apply Function.Embedding.sectr_apply

/-- If `e₁` and `e₂` are embeddings, then so is `Prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩
#align function.embedding.prod_map Function.Embedding.prodMap

@[simp]
theorem coe_prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    e₁.prodMap e₂ = Prod.map e₁ e₂ :=
  rfl
#align function.embedding.coe_prod_map Function.Embedding.coe_prodMap

/-- If `e₁` and `e₂` are embeddings,
  then so is `fun ⟨a, b⟩ ↦ ⟨e₁ a, e₂ b⟩ : PProd α γ → PProd β δ`. -/
def pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩
#align function.embedding.pprod_map Function.Embedding.pprodMap

section Sum

open Sum

/-- If `e₁` and `e₂` are embeddings, then so is `Sum.map e₁ e₂`. -/
def sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, e₁.injective.sum_map e₂.injective⟩
#align function.embedding.sum_map Function.Embedding.sumMap

@[simp]
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : sumMap e₁ e₂ = Sum.map e₁ e₂ :=
  rfl
#align function.embedding.coe_sum_map Function.Embedding.coe_sumMap

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type*} : α ↪ Sum α β :=
  ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩
#align function.embedding.inl Function.Embedding.inl
#align function.embedding.inl_apply Function.Embedding.inl_apply

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type*} : β ↪ Sum α β :=
  ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩
#align function.embedding.inr Function.Embedding.inr
#align function.embedding.inr_apply Function.Embedding.inr_apply

end Sum

section Sigma

variable {α α' : Type*} {β : α → Type*} {β' : α' → Type*}

/-- `Sigma.mk` as a `Function.Embedding`. -/
@[simps apply]
def sigmaMk (a : α) : β a ↪ Σx, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩
#align function.embedding.sigma_mk Function.Embedding.sigmaMk
#align function.embedding.sigma_mk_apply Function.Embedding.sigmaMk_apply

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `Sigma.map f g` is an embedding. -/
@[simps apply]
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σa, β a) ↪ Σa', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩
#align function.embedding.sigma_map Function.Embedding.sigmaMap
#align function.embedding.sigma_map_apply Function.Embedding.sigmaMap_apply

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `fun a ↦ e a (f a)`. -/
@[simps]
def piCongrRight {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩
#align function.embedding.Pi_congr_right Function.Embedding.piCongrRight
#align function.embedding.Pi_congr_right_apply Function.Embedding.piCongrRight_apply

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e
#align function.embedding.arrow_congr_right Function.Embedding.arrowCongrRight

@[simp]
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ → α) :
    arrowCongrRight e f = e ∘ f :=
  rfl
#align function.embedding.arrow_congr_right_apply Function.Embedding.arrowCongrRight_apply

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩
#align function.embedding.arrow_congr_left Function.Embedding.arrowCongrLeft

/-- Restrict both domain and codomain of an embedding. -/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩
#align function.embedding.subtype_map Function.Embedding.subtypeMap

open Set

theorem swap_apply {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.injective.swap_apply x y z
#align function.embedding.swap_apply Function.Embedding.swap_apply

theorem swap_comp {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  f.injective.swap_comp x y
#align function.embedding.swap_comp Function.Embedding.swap_comp

end Embedding

end Function

namespace Equiv

open Function Embedding

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps!]
def asEmbedding {β α : Sort*} {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  e.toEmbedding.trans (subtype p)
#align equiv.as_embedding Equiv.asEmbedding
#align equiv.as_embedding_apply Equiv.asEmbedding_apply

/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtypeInjectiveEquivEmbedding (α β : Sort*) :
    { f : α → β // Injective f } ≃ (α ↪ β) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align equiv.subtype_injective_equiv_embedding Equiv.subtypeInjectiveEquivEmbedding

-- Porting note: in Lean 3 this had `@[congr]`
/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[simps apply]
def embeddingCongr {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
#align equiv.embedding_congr Equiv.embeddingCongr
#align equiv.embedding_congr_apply Equiv.embeddingCongr_apply

@[simp]
theorem embeddingCongr_refl {α β : Sort*} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) :=
  rfl
#align equiv.embedding_congr_refl Equiv.embeddingCongr_refl

@[simp]
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl
#align equiv.embedding_congr_trans Equiv.embeddingCongr_trans

@[simp]
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl
#align equiv.embedding_congr_symm Equiv.embeddingCongr_symm

theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) := by
  ext
  simp
#align equiv.embedding_congr_apply_trans Equiv.embeddingCongr_apply_trans

@[simp]
theorem refl_toEmbedding {α : Type*} : (Equiv.refl α).toEmbedding = Embedding.refl α :=
  rfl
#align equiv.refl_to_embedding Equiv.refl_toEmbedding

@[simp]
theorem trans_toEmbedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl
#align equiv.trans_to_embedding Equiv.trans_toEmbedding

end Equiv

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩
#align subtype_or_left_embedding subtypeOrLeftEmbedding

theorem subtypeOrLeftEmbedding_apply_left {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx
#align subtype_or_left_embedding_apply_left subtypeOrLeftEmbedding_apply_left

theorem subtypeOrLeftEmbedding_apply_right {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
  dif_neg hx
#align subtype_or_left_embedding_apply_right subtypeOrLeftEmbedding_apply_right

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps]
def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩
#align subtype.imp_embedding Subtype.impEmbedding
#align subtype.imp_embedding_apply_coe Subtype.impEmbedding_apply_coe

end Subtype
