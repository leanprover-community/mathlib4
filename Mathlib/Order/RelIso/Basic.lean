/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Order.RelClasses

/-!
# Relation homomorphisms, embeddings, isomorphisms

This file defines relation homomorphisms, embeddings, isomorphisms and order embeddings and
isomorphisms.

## Main declarations

* `RelHom`: Relation homomorphism. A `RelHom r s` is a function `f : α → β` such that
  `r a b → s (f a) (f b)`.
* `RelEmbedding`: Relation embedding. A `RelEmbedding r s` is an embedding `f : α ↪ β` such that
  `r a b ↔ s (f a) (f b)`.
* `RelIso`: Relation isomorphism. A `RelIso r s` is an equivalence `f : α ≃ β` such that
  `r a b ↔ s (f a) (f b)`.
* `sumLexCongr`, `prodLexCongr`: Creates a relation homomorphism between two `Sum.Lex` or two
  `Prod.Lex` from relation homomorphisms between their arguments.

## Notation

* `→r`: `RelHom`
* `↪r`: `RelEmbedding`
* `≃r`: `RelIso`
-/

@[expose] public section

open Function

universe u v w

variable {α β γ δ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop} {u : δ → δ → Prop}

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
infixl:25 " →r " => RelHom

section

/-- `RelHomClass F r s` asserts that `F` is a type of functions such that all `f : F`
satisfy `r a b → s (f a) (f b)`.

The relations `r` and `s` are `outParam`s since figuring them out from a goal is a higher-order
matching problem that Lean usually can't do unaided.
-/
class RelHomClass (F : Type*) {α β : outParam Type*} (r : outParam <| α → α → Prop)
  (s : outParam <| β → β → Prop) [FunLike F α β] : Prop where
  /-- A `RelHomClass` sends related elements to related elements -/
  map_rel : ∀ (f : F) {a b}, r a b → s (f a) (f b)

export RelHomClass (map_rel)

end

namespace RelHomClass

variable {F : Type*} [FunLike F α β]

protected theorem irrefl [RelHomClass F r s] (f : F) : ∀ [Std.Irrefl s], Std.Irrefl r
  | ⟨H⟩ => ⟨fun _ h => H _ (map_rel f h)⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelHomClass.irrefl

protected theorem asymm [RelHomClass F r s] (f : F) : ∀ [Std.Asymm s], Std.Asymm r
  | ⟨H⟩ => ⟨fun _ _ h₁ h₂ => H _ _ (map_rel f h₁) (map_rel f h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelHomClass.asymm

protected theorem acc [RelHomClass F r s] (f : F) (a : α) : Acc s (f a) → Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩

protected theorem wellFounded [RelHomClass F r s] (f : F) : WellFounded s → WellFounded r
  | ⟨H⟩ => ⟨fun _ => RelHomClass.acc f _ (H _)⟩

protected theorem isWellFounded [RelHomClass F r s] (f : F) [IsWellFounded β s] :
    IsWellFounded α r :=
  ⟨RelHomClass.wellFounded f IsWellFounded.wf⟩

end RelHomClass

namespace RelHom

instance : FunLike (r →r s) α β where
  coe o := o.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

instance : RelHomClass (r →r s) r s where
  map_rel := map_rel'

initialize_simps_projections RelHom (toFun → apply)

protected theorem map_rel (f : r →r s) {a b} : r a b → s (f a) (f b) :=
  f.map_rel'

@[simp]
theorem coe_fn_toFun (f : r →r s) : f.toFun = (f : α → β) :=
  rfl

@[simp]
theorem coeFn_mk (f : α → β) (h : ∀ {a b}, r a b → s (f a) (f b)) :
    RelHom.mk f @h = f :=
  rfl

/-- The map `coe_fn : (r →r s) → (α → β)` is injective. -/
theorem coe_fn_injective : Injective fun (f : r →r s) => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Identity map is a relation homomorphism. -/
@[refl, simps]
protected def id (r : α → α → Prop) : r →r r :=
  ⟨fun x => x, fun x => x⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[simps]
protected def comp (g : s →r t) (f : r →r s) : r →r t :=
  ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩

theorem comp_assoc (h : r →r s) (g : s →r t) (f : t →r u) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp]
theorem comp_id (f : r →r s) : f.comp (RelHom.id r) = f := rfl

@[simp]
theorem id_comp (f : r →r s) : (RelHom.id s).comp f = f := rfl

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
@[simps]
protected def swap (f : r →r s) : swap r →r swap s :=
  ⟨f, f.map_rel⟩

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
@[simps]
def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s :=
  ⟨f, id⟩

end RelHom

/-- An increasing function is injective -/
theorem injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [Std.Trichotomous r]
    [Std.Irrefl s] (f : α → β) (hf : ∀ {x y}, r x y → s (f x) (f y)) : Injective f := by
  intro x y hxy
  rcases trichotomous_of r x y with (h | h | h)
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this
  · exact h
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this

/-- An increasing function is injective -/
theorem RelHom.injective_of_increasing [Std.Trichotomous r] [Std.Irrefl s] (f : r →r s) :
    Injective f :=
  _root_.injective_of_increasing r s f f.map_rel

theorem Function.Surjective.wellFounded_iff {f : α → β} (hf : Surjective f)
    (o : ∀ {a b}, r a b ↔ s (f a) (f b)) :
    WellFounded r ↔ WellFounded s :=
  Iff.intro
    (RelHomClass.wellFounded (⟨surjInv hf,
      fun h => by simpa only [o, surjInv_eq hf] using h⟩ : s →r r))
    (RelHomClass.wellFounded (⟨f, o.1⟩ : r →r s))

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure RelEmbedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β where
  /-- Elements are related iff they are related after apply a `RelEmbedding` -/
  map_rel_iff' : ∀ {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
infixl:25 " ↪r " => RelEmbedding

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop} (hs : Equivalence s) :
    Equivalence (f ⁻¹'o s) :=
  ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩

namespace RelEmbedding

/-- A relation embedding is also a relation homomorphism -/
@[reducible]
def toRelHom (f : r ↪r s) : r →r s where
  toFun := f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr

instance : Coe (r ↪r s) (r →r s) :=
  ⟨toRelHom⟩

instance : FunLike (r ↪r s) α β where
  coe x := x.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr

instance : RelHomClass (r ↪r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)

initialize_simps_projections RelEmbedding (toFun → apply)

instance : EmbeddingLike (r ↪r s) α β where
  injective' f := f.inj'

@[simp]
theorem coe_toEmbedding {f : r ↪r s} : ((f : r ↪r s).toEmbedding : α → β) = f :=
  rfl

theorem coe_toRelHom {f : r ↪r s} : ((f : r ↪r s).toRelHom : α → β) = f :=
  rfl

theorem toEmbedding_injective : Injective (toEmbedding : r ↪r s → (α ↪ β)) := by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]
theorem toEmbedding_inj {f g : r ↪r s} : f.toEmbedding = g.toEmbedding ↔ f = g :=
  toEmbedding_injective.eq_iff

theorem injective (f : r ↪r s) : Injective f :=
  f.inj'

theorem inj (f : r ↪r s) {a b} : f a = f b ↔ a = b := f.injective.eq_iff

theorem map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
theorem coe_mk {f} {h} : ⇑(⟨f, h⟩ : r ↪r s) = f :=
  rfl

/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. -/
theorem coe_fn_injective : Injective fun f : r ↪r s => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Identity map is a relation embedding. -/
@[refl, simps!]
protected def refl (r : α → α → Prop) : r ↪r r :=
  ⟨Embedding.refl _, Iff.rfl⟩

/-- Composition of two relation embeddings is a relation embedding. -/
protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩

instance (r : α → α → Prop) : Inhabited (r ↪r r) :=
  ⟨RelEmbedding.refl _⟩

theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
theorem coe_trans (f : r ↪r s) (g : s ↪r t) : (f.trans g) = g ∘ f :=
  rfl

theorem trans_assoc (f : r ↪r s) (g : s ↪r t) (h : t ↪r u) :
  (f.trans g).trans h = f.trans (g.trans h) := rfl

@[simp]
theorem trans_refl (f : r ↪r s) : f.trans (.refl s) = f := rfl

@[simp]
theorem refl_trans (f : r ↪r s) : .trans (.refl r) f = f := rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

@[simp]
theorem swap_apply (f : r ↪r s) (a : α) : f.swap a = f a := rfl

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s :=
  ⟨f, Iff.rfl⟩

@[simp]
theorem preimage_apply (f : α ↪ β) (s : β → β → Prop) (a : α) : preimage f s a = f a := rfl

theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s := by
  ext a b
  exact f.map_rel_iff.symm

protected theorem irrefl (f : r ↪r s) [Std.Irrefl s] : Std.Irrefl r :=
  ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelEmbedding.irrefl

protected theorem stdRefl (f : r ↪r s) [Std.Refl s] : Std.Refl r :=
  ⟨fun _ => f.map_rel_iff.1 <| refl _⟩

@[deprecated (since := "2026-01-08")] protected alias isRefl := RelEmbedding.stdRefl

protected theorem symm (f : r ↪r s) [Std.Symm s] : Std.Symm r :=
  ⟨fun _ _ => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

@[deprecated (since := "2026-01-06")] protected alias isSymm := RelEmbedding.symm

protected theorem asymm (f : r ↪r s) [Std.Asymm s] : Std.Asymm r :=
  ⟨fun _ _ h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelEmbedding.asymm

protected theorem antisymm : ∀ (_ : r ↪r s) [Std.Antisymm s], Std.Antisymm r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ h₁ h₂ => f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := RelEmbedding.antisymm

protected theorem isTrans : ∀ (_ : r ↪r s) [IsTrans β s], IsTrans α r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ _ h₁ h₂ => o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩

protected theorem total : ∀ (_ : r ↪r s) [Std.Total s], Std.Total r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ => (or_congr o o).1 (H _ _)⟩

@[deprecated (since := "2026-01-09")] protected alias isTotal := RelEmbedding.total

protected theorem isPreorder : ∀ (_ : r ↪r s) [IsPreorder β s], IsPreorder α r
  | f, _ => { f.stdRefl, f.isTrans with }

protected theorem isPartialOrder : ∀ (_ : r ↪r s) [IsPartialOrder β s], IsPartialOrder α r
  | f, _ => { f.isPreorder, f.antisymm with }

protected theorem isLinearOrder : ∀ (_ : r ↪r s) [IsLinearOrder β s], IsLinearOrder α r
  | f, _ => { f.isPartialOrder, f.total with }

protected theorem isStrictOrder : ∀ (_ : r ↪r s) [IsStrictOrder β s], IsStrictOrder α r
  | f, _ => { f.irrefl, f.isTrans with }

protected theorem trichotomous : ∀ (_ : r ↪r s) [Std.Trichotomous s], Std.Trichotomous r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ hab hba ↦ f.injective <| H _ _ (o.not.mpr hab) (o.not.mpr hba)⟩

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := RelEmbedding.trichotomous

protected theorem isStrictTotalOrder : ∀ (_ : r ↪r s) [IsStrictTotalOrder β s],
    IsStrictTotalOrder α r
  | f, _ => { f.trichotomous, f.isStrictOrder with }

protected theorem acc (f : r ↪r s) (a : α) : Acc s (f a) → Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩

protected theorem wellFounded : ∀ (_ : r ↪r s) (_ : WellFounded s), WellFounded r
  | f, ⟨H⟩ => ⟨fun _ => f.acc _ (H _)⟩

protected theorem isWellFounded (f : r ↪r s) [IsWellFounded β s] : IsWellFounded α r :=
  ⟨f.wellFounded IsWellFounded.wf⟩

protected theorem isWellOrder : ∀ (_ : r ↪r s) [IsWellOrder β s], IsWellOrder α r
  | f, H => { f.isStrictTotalOrder with wf := f.wellFounded H.wf }

end RelEmbedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
@[simps!]
def Subtype.relEmbedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
    (Subtype.val : Subtype p → X) ⁻¹'o r ↪r r :=
  ⟨Embedding.subtype p, Iff.rfl⟩

instance Subtype.wellFoundedLT [LT α] [WellFoundedLT α] (p : α → Prop) :
    WellFoundedLT (Subtype p) :=
  (Subtype.relEmbedding (· < ·) p).isWellFounded

instance Subtype.wellFoundedGT [LT α] [WellFoundedGT α] (p : α → Prop) :
    WellFoundedGT (Subtype p) :=
  (Subtype.relEmbedding (· > ·) p).isWellFounded

/-- `Quotient.mk` as a relation homomorphism between the relation and the lift of a relation. -/
@[simps]
def Quotient.mkRelHom {_ : Setoid α} {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : r →r Quotient.lift₂ r H :=
  ⟨Quotient.mk _, id⟩

/-- `Quotient.out` as a relation embedding between the lift of a relation and the relation. -/
@[simps!]
noncomputable def Quotient.outRelEmbedding {_ : Setoid α} {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : Quotient.lift₂ r H ↪r r :=
  ⟨Embedding.quotientOut α, fun {x y} ↦ by
    induction x, y using Quotient.inductionOn₂
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩

@[simp]
theorem acc_lift₂_iff {_ : Setoid α} {r : α → α → Prop}
    {H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂} {a} :
    Acc (Quotient.lift₂ r H) ⟦a⟧ ↔ Acc r a := by
  constructor
  · exact RelHomClass.acc (Quotient.mkRelHom H) a
  · intro ac
    induction ac with | intro _ _ IH => ?_
    refine ⟨_, fun q h => ?_⟩
    obtain ⟨a', rfl⟩ := q.exists_rep
    exact IH a' h

@[simp]
theorem acc_liftOn₂'_iff {s : Setoid α} {r : α → α → Prop} {H} {a} :
    Acc (fun x y => Quotient.liftOn₂' x y r H) (Quotient.mk'' a : Quotient s) ↔ Acc r a :=
  acc_lift₂_iff (H := H)

/-- A relation is well founded iff its lift to a quotient is. -/
@[simp]
theorem wellFounded_lift₂_iff {_ : Setoid α} {r : α → α → Prop}
    {H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂} :
    WellFounded (Quotient.lift₂ r H) ↔ WellFounded r := by
  constructor
  · exact RelHomClass.wellFounded (Quotient.mkRelHom H)
  · refine fun wf => ⟨fun q => ?_⟩
    obtain ⟨a, rfl⟩ := q.exists_rep
    exact acc_lift₂_iff.2 (wf.apply a)

alias ⟨WellFounded.of_quotient_lift₂, WellFounded.quotient_lift₂⟩ := wellFounded_lift₂_iff

@[simp]
theorem wellFounded_liftOn₂'_iff {s : Setoid α} {r : α → α → Prop} {H} :
    (WellFounded fun x y : Quotient s => Quotient.liftOn₂' x y r H) ↔ WellFounded r :=
  wellFounded_lift₂_iff (H := H)

alias ⟨WellFounded.of_quotient_liftOn₂', WellFounded.quotient_liftOn₂'⟩ := wellFounded_liftOn₂'_iff

namespace RelEmbedding

/-- To define a relation embedding from an antisymmetric relation `r` to a reflexive relation `s`
it suffices to give a function together with a proof that it satisfies `s (f a) (f b) ↔ r a b`.
-/
def ofMapRelIff (f : α → β) [Std.Antisymm r] [Std.Refl s] (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    r ↪r s where
  toFun := f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _

@[simp]
theorem ofMapRelIff_coe (f : α → β) [Std.Antisymm r] [Std.Refl s]
    (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    (ofMapRelIff f hf : r ↪r s) = f :=
  rfl

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def ofMonotone [Std.Trichotomous r] [Std.Asymm s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) :
    r ↪r s := by
  refine ⟨⟨f, fun a b e => ?_⟩, @fun a b => ⟨fun h => ?_, H _ _⟩⟩
  · apply Std.Trichotomous.trichotomous (r := r) a b
    · exact fun h => irrefl (r := s) (f a) (by simpa [e] using H _ _ h)
    · exact fun h => irrefl (r := s) (f b) (by simpa [e] using H _ _ h)
  · refine Not.imp_symm (Std.Trichotomous.trichotomous a b · fun h' ↦ asymm (H _ _ h') h) ?_
    exact (irrefl _ <| · ▸ h)

@[simp]
theorem ofMonotone_coe [Std.Trichotomous r] [Std.Asymm s] (f : α → β) (H) :
    (@ofMonotone _ _ r s _ _ f H : α → β) = f :=
  rfl

/-- A relation embedding from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ↪r s :=
  ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩

/-- `Sum.inl` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
def sumLiftRelInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.LiftRel r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
def sumLiftRelInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.LiftRel r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.LiftRel` relations. -/
@[simps]
def sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `Sum.inl` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
def sumLexInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.Lex r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
def sumLexInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.Lex r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.Lex` relations. -/
@[simps]
def sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `fun b ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
def prodLexMkLeft (s : β → β → Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r s where
  toFun := Prod.mk a
  inj' := Prod.mk_right_injective a
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `fun a ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
def prodLexMkRight (r : α → α → Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r s where
  toFun a := (a, b)
  inj' := Prod.mk_left_injective b
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `Prod.map` as a relation embedding. -/
@[simps]
def prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u where
  toFun := Prod.map f g
  inj' := f.injective.prodMap g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]

end RelEmbedding

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure RelIso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β where
  /-- Elements are related iff they are related after apply a `RelIso` -/
  map_rel_iff' : ∀ {a b}, s (toEquiv a) (toEquiv b) ↔ r a b

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
infixl:25 " ≃r " => RelIso

namespace RelIso

/-- Convert a `RelIso` to a `RelEmbedding`. This function is also available as a coercion
but often it is easier to write `f.toRelEmbedding` than to write explicitly `r` and `s`
in the target type. -/
@[reducible]
def toRelEmbedding (f : r ≃r s) : r ↪r s :=
  ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩

theorem toEquiv_injective : Injective (toEquiv : r ≃r s → α ≃ β)
  | ⟨e₁, o₁⟩, ⟨e₂, _⟩, h => by congr

instance : CoeOut (r ≃r s) (r ↪r s) :=
  ⟨toRelEmbedding⟩

instance : FunLike (r ≃r s) α β where
  coe x := x
  coe_injective := Equiv.coe_fn_injective.comp toEquiv_injective

instance : RelHomClass (r ≃r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)

instance : EquivLike (r ≃r s) α β where
  coe f := f
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ hf _ := DFunLike.ext' hf

theorem coe_toRelEmbedding (f : r ≃r s) : (f.toRelEmbedding : α → β) = f :=
  rfl

theorem coe_toEmbedding (f : r ≃r s) : (f.toEmbedding : α → β) = f :=
  rfl

theorem map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, s (f a) (f b) ↔ r a b) :
    (RelIso.mk f @o : α → β) = f :=
  rfl

@[simp]
theorem coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α → β) = f :=
  rfl

/-- The map `DFunLike.coe : (r ≃r s) → (α → β)` is injective. -/
theorem coe_fn_injective : Injective fun f : r ≃r s => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
protected def symm (f : r ≃r s) : s ≃r r :=
  ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because `RelIso` defines custom coercions other than the ones given by `DFunLike`. -/
def Simps.apply (h : r ≃r s) : α → β :=
  h

/-- See Note [custom simps projection]. -/
def Simps.symm_apply (h : r ≃r s) : β → α :=
  h.symm

initialize_simps_projections RelIso (toFun → apply, invFun → symm_apply)

/-- Identity map is a relation isomorphism. -/
@[refl, simps! apply]
protected def refl (r : α → α → Prop) : r ≃r r :=
  ⟨Equiv.refl _, Iff.rfl⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[simps! apply]
protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩

instance (r : α → α → Prop) : Inhabited (r ≃r r) :=
  ⟨RelIso.refl _⟩

@[simp]
theorem default_def (r : α → α → Prop) : default = RelIso.refl r :=
  rfl

@[simp] lemma apply_symm_apply (e : r ≃r s) (x : β) : e (e.symm x) = x := e.right_inv x
@[simp] lemma symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x := e.left_inv x

@[simp] lemma symm_comp_self (e : r ≃r s) : e.symm ∘ e = id := funext e.symm_apply_apply
@[simp] lemma self_comp_symm (e : r ≃r s) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp] lemma symm_trans_apply (f : r ≃r s) (g : s ≃r t) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

lemma symm_symm_apply (f : r ≃r s) (b : α) : f.symm.symm b = f b := rfl

lemma apply_eq_iff_eq (f : r ≃r s) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f

lemma apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : r ≃r s) : f x = y ↔ x = f.symm y := by
  conv_lhs => rw [← apply_symm_apply f y]
  rw [apply_eq_iff_eq]

lemma symm_apply_eq (e : r ≃r s) {x y} : e.symm x = y ↔ x = e y := e.toEquiv.symm_apply_eq
lemma eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ e y = x := e.toEquiv.eq_symm_apply

@[simp] lemma symm_symm (e : r ≃r s) : e.symm.symm = e := rfl

lemma symm_bijective : Bijective (.symm : (r ≃r s) → s ≃r r) :=
  bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp] lemma refl_symm : (RelIso.refl r).symm = .refl _ := rfl
@[simp] lemma trans_refl (e : r ≃r s) : e.trans (.refl _) = e := rfl
@[simp] lemma refl_trans (e : r ≃r s) : .trans (.refl _) e = e := rfl

@[simp] lemma symm_trans_self (e : r ≃r s) : e.symm.trans e = .refl _ := ext <| by simp
@[simp] lemma self_trans_symm (e : r ≃r s) : e.trans e.symm = .refl _ := ext <| by simp

lemma trans_assoc {δ : Type*} {u : δ → δ → Prop} (ab : r ≃r s) (bc : s ≃r t) (cd : t ≃r u) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := rfl

/-- A relation isomorphism between equal relations on equal types. -/
@[simps! toEquiv apply]
protected def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : r ≃r s :=
  ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩

protected theorem cast_symm {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : (RelIso.cast h₁ h₂).symm = RelIso.cast h₁.symm h₂.symm :=
  rfl

protected theorem cast_refl {α : Type u} {r : α → α → Prop} (h₁ : α = α := rfl)
    (h₂ : r ≍ r := HEq.rfl) : RelIso.cast h₁ h₂ = RelIso.refl r :=
  rfl

protected theorem cast_trans {α β γ : Type u} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (h₁ : α = β) (h₁' : β = γ) (h₂ : r ≍ s) (h₂' : s ≍ t) :
    (RelIso.cast h₁ h₂).trans (RelIso.cast h₁' h₂') = RelIso.cast (h₁.trans h₁') (h₂.trans h₂') :=
  ext fun x => by subst h₁; rfl

/-- A relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap (f : r ≃r s) : swap r ≃r swap s :=
  ⟨f, f.map_rel_iff⟩

/-- A relation isomorphism is also a relation isomorphism between complemented relations. -/
@[simps!]
protected def compl (f : r ≃r s) : rᶜ ≃r sᶜ :=
  ⟨f, f.map_rel_iff.not⟩

@[simp]
theorem coe_fn_symm_mk (f o) : ((@RelIso.mk _ _ r s f @o).symm : β → α) = f.symm :=
  rfl

theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y := by
  rw [← e.map_rel_iff, e.apply_symm_apply]

theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) := by
  rw [← e.map_rel_iff, e.apply_symm_apply]

protected theorem bijective (e : r ≃r s) : Bijective e :=
  e.toEquiv.bijective

protected theorem injective (e : r ≃r s) : Injective e :=
  e.toEquiv.injective

protected theorem surjective (e : r ≃r s) : Surjective e :=
  e.toEquiv.surjective

theorem eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

/-- Copy of a `RelIso` with a new `toFun` and `invFun` equal to the old ones.
Useful to fix definitional equalities. -/
def copy (e : r ≃r s) (f : α → β) (g : β → α) (hf : f = e) (hg : g = e.symm) : r ≃r s where
  toFun := f
  invFun := g
  left_inv _ := by simp [hf, hg]
  right_inv _ := by simp [hf, hg]
  map_rel_iff' := by simp [hf, e.map_rel_iff]

@[simp, norm_cast]
lemma coe_copy (e : r ≃r s) (f : α → β) (g : β → α) (hf hg) : e.copy f g hf hg = f := rfl

lemma copy_eq (e : r ≃r s) (f : α → β) (g : β → α) (hf hg) : e.copy f g hf hg = e :=
  DFunLike.coe_injective hf

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s :=
  ⟨f, Iff.rfl⟩

-- `simps` crashes if asked to generate these
@[simp]
theorem preimage_apply (f : α ≃ β) (s : β → β → Prop) (a : α) : RelIso.preimage f s a = f a := rfl

@[simp]
theorem preimage_symm_apply (f : α ≃ β) (s : β → β → Prop) (a : β) :
    (RelIso.preimage f s).symm a = f.symm a := rfl

instance IsWellOrder.preimage {α : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    IsWellOrder β (f ⁻¹'o r) :=
  @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _

instance IsWellOrder.ulift {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (ULift α) (ULift.down ⁻¹'o r) :=
  IsWellOrder.preimage r Equiv.ulift

/-- A surjective relation embedding is a relation isomorphism. -/
@[simps! apply]
noncomputable def ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s :=
  ⟨f.toEmbedding.equivOfSurjective H, f.map_rel_iff⟩

/-- Surjective relation embeddings are equivalent to relation isomorphisms. -/
@[simps]
noncomputable def embeddingSurjectiveEquivIso :
    { f : r ↪r s // Function.Surjective f } ≃ (r ≃r s) where
  toFun f := ofSurjective f f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- Transport a `RelHom` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.arrowCongr` for `RelHom`. -/
@[simps apply symm_apply]
def relHomCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ →r s₁) ≃ (r₂ →r s₂) where
  toFun f₁ := e₂.toRelEmbedding.toRelHom.comp <| f₁.comp e₁.symm.toRelEmbedding.toRelHom
  invFun f₂ := e₂.symm.toRelEmbedding.toRelHom.comp <| f₂.comp e₁.toRelEmbedding.toRelHom
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relHomCongr

/-- Transport a `RelEmbedding` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.embeddingCongr` for `RelEmbedding`. -/
@[simps apply symm_apply]
def relEmbeddingCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ↪r s₁) ≃ (r₂ ↪r s₂) where
  toFun f₁ := (e₁.symm.toRelEmbedding.trans f₁).trans e₂.toRelEmbedding
  invFun f₂ := (e₁.toRelEmbedding.trans f₂).trans e₂.symm.toRelEmbedding
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relEmbeddingCongr

/-- Transport a `RelIso` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.equivCongr` for `RelIso`. -/
@[simps apply symm_apply]
def relIsoCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ≃r s₁) ≃ (r₂ ≃r s₂) where
  toFun f₁ := (e₁.symm.trans f₁).trans e₂
  invFun f₂ := (e₁.trans f₂).trans e₂.symm
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relIsoCongr

/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
def sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂ :=
  ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    obtain ⟨f, hf⟩ := e₁; obtain ⟨g, hg⟩ := e₂; cases a <;> cases b <;> simp [hf, hg]⟩

/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
def prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂ :=
  ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩

/-- Two relations on empty types are isomorphic. -/
def relIsoOfIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] [IsEmpty β] : r ≃r s :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

/-- The lexicographic sum of `r` plus an empty relation is isomorphic to `r`. -/
@[simps!]
def sumLexEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty β] : Sum.Lex r s ≃r r :=
  ⟨Equiv.sumEmpty _ _, by simp⟩

/-- The lexicographic sum of an empty relation plus `s` is isomorphic to `s`. -/
@[simps!]
def emptySumLex (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : Sum.Lex r s ≃r s :=
  ⟨Equiv.emptySum _ _, by simp⟩

/-- Two irreflexive relations on a unique type are isomorphic. -/
def ofUniqueOfIrrefl (r : α → α → Prop) (s : β → β → Prop) [Std.Irrefl r]
    [Std.Irrefl s] [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩

/-- Two reflexive relations on a unique type are isomorphic. -/
def ofUniqueOfRefl (r : α → α → Prop) (s : β → β → Prop) [Std.Refl r] [Std.Refl s]
    [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩

end RelIso
