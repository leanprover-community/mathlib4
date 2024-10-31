/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Data.Sum.Order
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Set
import Mathlib.Order.WellFounded
/-!
# Initial and principal segments

This file defines initial and principal segments.

## Main definitions

* `InitialSeg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `PrincipalSeg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

The lemmas `Ordinal.type_le_iff` and `Ordinal.type_lt_iff` tell us that `≼i` corresponds to the `≤`
relation on ordinals, while `≺i` corresponds to the `<` relation. This prompts us to think of
`PrincipalSeg` as a "strict" version of `InitialSeg`.

## Notations

These notations belong to the `InitialSeg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
* `α ≤i β` is an abbreviation for `(· < ·) ≼i (· < ·)`.
* `α <i β` is an abbreviation for `(· < ·) ≺i (· < ·)`.
-/


/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`InitialSeg r s`, and denoted by `r ≼i s`.
-/

variable {α : Type*} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

open Function

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure InitialSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The order embedding is an initial segment -/
  mem_range_of_rel' : ∀ a b, s b (toRelEmbedding a) → b ∈ Set.range toRelEmbedding

-- Porting note: Deleted `scoped[InitialSeg]`
@[inherit_doc]
infixl:25 " ≼i " => InitialSeg

/-- An `InitialSeg` between the `<` relations of two types. -/
notation:25 α:24 " ≤i " β:25 => @InitialSeg α β (· < ·) (· < ·)

namespace InitialSeg

instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩

instance : FunLike (r ≼i s) α β where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x

instance : EmbeddingLike (r ≼i s) α β where
  injective' f := f.inj'

/-- An initial segment embedding between the `<` relations of two partial orders is an order
embedding. -/
def toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α ≤i β) : α ↪o β :=
  f.orderEmbeddingOfLTEmbedding

@[simp]
theorem toOrderEmbedding_apply [PartialOrder α] [PartialOrder β] (f : α ≤i β) (x : α) :
    f.toOrderEmbedding x = f x :=
  rfl

@[simp]
theorem coe_toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α ≤i β) :
    (f.toOrderEmbedding : α → β) = f :=
  rfl

instance [PartialOrder α] [PartialOrder β] : OrderHomClass (α ≤i β) α β where
  map_rel f := f.toOrderEmbedding.map_rel_iff.2

@[ext] lemma ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f :=
  rfl

theorem mem_range_of_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) → b ∈ Set.range f :=
  f.mem_range_of_rel' _ _

@[deprecated mem_range_of_rel (since := "2024-09-21")]
alias init := mem_range_of_rel

theorem map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

theorem inj (f : r ≼i s) {a b : α} : f a = f b ↔ a = b :=
  f.toRelEmbedding.inj

theorem exists_eq_iff_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨_, e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

@[deprecated exists_eq_iff_rel (since := "2024-09-21")]
alias init_iff := exists_eq_iff_rel

/-- An order isomorphism is an initial segment -/
def ofIso (f : r ≃r s) : r ≼i s :=
  ⟨f, fun _ b _ => ⟨f.symm b, RelIso.apply_symm_apply f _⟩⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl]
protected def refl (r : α → α → Prop) : r ≼i r :=
  ⟨RelEmbedding.refl _, fun _ _ _ => ⟨_, rfl⟩⟩

instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp only [RelEmbedding.coe_trans, coe_coe_fn, comp_apply] at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩

@[simp]
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl

@[simp]
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl

instance subsingleton_of_trichotomous_of_irrefl [IsTrichotomous β s] [IsIrrefl β s]
    [IsWellFounded α r] : Subsingleton (r ≼i s) :=
  ⟨fun f g => by
    ext a
    refine IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => ?_
    rw [f.exists_eq_iff_rel, g.exists_eq_iff_rel]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl⟩

instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => by let _ := a.isWellFounded; exact Subsingleton.elim a⟩

protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

private theorem antisymm_aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  (f.trans g).eq (InitialSeg.refl _)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  have := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, antisymm_aux f g, antisymm_aux g f⟩, f.map_rel_iff'⟩

@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl

@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl

theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, x ∈ Set.range f ↔ s x b := by
  apply or_iff_not_imp_right.2
  intro h b
  push_neg at h
  apply IsWellFounded.induction s b
  intro x IH
  obtain ⟨y, ⟨hy, hs⟩ | ⟨hy, hs⟩⟩ := h x
  · obtain (rfl | h) := (trichotomous y x).resolve_left hs
    · exact hy
    · obtain ⟨z, rfl⟩ := hy
      exact f.mem_range_of_rel h
  · obtain ⟨z, rfl⟩ := IH y hs
    cases hy (Set.mem_range_self z)

/-- Restrict the codomain of an initial segment -/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.mem_range_of_rel h
    ⟨a', by subst e; rfl⟩⟩

@[simp]
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- Initial segment from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def leAdd (r : α → α → Prop) (s : β → β → Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩

@[simp]
theorem leAdd_apply (r : α → α → Prop) (s : β → β → Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl

protected theorem acc (f : r ≼i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  ⟨by
    refine fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => ?_
    obtain ⟨a', rfl⟩ := f.mem_range_of_rel hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩

end InitialSeg

/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`PrincipalSeg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/


/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
structure PrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The supremum of the principal segment -/
  top : β
  /-- The range of the order embedding is the set of elements `b` such that `s b top` -/
  mem_range_iff_rel' : ∀ b, b ∈ Set.range toRelEmbedding ↔ s b top

-- Porting note: deleted `scoped[InitialSeg]`
@[inherit_doc]
infixl:25 " ≺i " => PrincipalSeg

/-- A `PrincipalSeg` between the `<` relations of two types. -/
notation:25 α:24 " <i " β:25 => @PrincipalSeg α β (· < ·) (· < ·)

namespace PrincipalSeg

instance : CoeOut (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩

@[simp]
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl

theorem mem_range_iff_rel (f : r ≺i s) : ∀ {b : β}, b ∈ Set.range f ↔ s b f.top :=
  f.mem_range_iff_rel' _

@[deprecated mem_range_iff_rel (since := "2024-10-07")]
theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b :=
  f.mem_range_iff_rel.symm

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.mem_range_iff_rel.1 ⟨_, rfl⟩

theorem mem_range_of_rel_top (f : r ≺i s) {b : β} (h : s b f.top) : b ∈ Set.range f :=
  f.mem_range_iff_rel.2 h

theorem mem_range_of_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) :
    b ∈ Set.range f :=
  f.mem_range_of_rel_top <| _root_.trans h <| f.lt_top _

@[deprecated mem_range_of_rel (since := "2024-09-21")]
alias init := mem_range_of_rel

theorem surjOn (f : r ≺i s) : Set.SurjOn f Set.univ { b | s b f.top } := by
  intro b h
  simpa using mem_range_of_rel_top _ h

/-- A principal segment is in particular an initial segment. -/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.mem_range_of_rel⟩⟩

theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl

theorem exists_eq_iff_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} :
    s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.exists_eq_iff_rel α β r s f a b

@[deprecated exists_eq_iff_rel (since := "2024-09-21")]
alias init_iff := exists_eq_iff_rel

/-- A principal segment is the same as a non-surjective initial segment. -/
noncomputable def _root_.InitialSeg.toPrincipalSeg [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) : r ≺i s :=
  ⟨f, _, Classical.choose_spec (f.eq_or_principal.resolve_left hf)⟩

@[simp]
theorem _root_.InitialSeg.toPrincipalSeg_apply [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) (x : α) : f.toPrincipalSeg hf x = f x :=
  rfl

theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False := by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq (↑f) (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h

instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

/-- Composition of a principal segment with an initial segment, as a principal segment -/
def ltLe (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp [g.exists_eq_iff_rel, ← PrincipalSeg.mem_range_iff_rel, exists_swap, ← exists_and_left]⟩

@[simp]
theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.ltLe g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _

@[simp]
theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.ltLe g).top = g f.top :=
  rfl

/-- Composition of two principal segments as a principal segment -/
@[trans]
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  ltLe f g

@[simp]
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
  lt_le_apply _ _ _

@[simp]
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl

/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equivLT (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c =>
    suffices (∃ a, g a = c) ↔ ∃ a, g (f a) = c by simp [← PrincipalSeg.mem_range_iff_rel]
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : r ≺i s) (g : s ≃r t) :
    r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, by
    intro x
    rw [← g.apply_symm_apply x, g.map_rel_iff, ← f.mem_range_iff_rel]
    exact exists_congr <| fun _ ↦ ⟨fun h => g.toEquiv.bijective.1 h, congr_arg g⟩⟩

@[simp]
theorem equivLT_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equivLT f g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _

@[simp]
theorem equivLT_top (f : r ≃r s) (g : s ≺i t) : (equivLT f g).top = g.top :=
  rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) :=
  ⟨fun f g => by
    have ef : (f : α → β) = g := by
      show ((f : r ≼i s) : α → β) = (g : r ≼i s)
      rw [@Subsingleton.elim _ _ (f : r ≼i s) g]
    have et : f.top = g.top := by
      refine extensional_of_trichotomous_of_irrefl s fun x => ?_
      simp only [← PrincipalSeg.mem_range_iff_rel, ef]
    cases f
    cases g
    have := RelEmbedding.coe_fn_injective ef; congr ⟩

protected theorem eq [IsWellOrder β s] (f g : r ≺i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)]; rfl

theorem top_rel_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : r ≺i s) (g : s ≺i t) (h : r ≺i t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

@[deprecated top_rel_top (since := "2024-10-10")]
alias topLTTop := top_rel_top

/-- Any element of a well order yields a principal segment -/
def ofElement {α : Type*} (r : α → α → Prop) (a : α) : Subrel r { b | r b a } ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun ⟨⟨_, h⟩, rfl⟩ => h, fun h => ⟨⟨_, h⟩, rfl⟩⟩⟩

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem ofElement_apply {α : Type*} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl

@[simp]
theorem ofElement_top {α : Type*} (r : α → α → Prop) (a : α) : (ofElement r a).top = a :=
  rfl

/-- For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic to `r`. -/
@[simps! symm_apply]
noncomputable def subrelIso (f : r ≺i s) : Subrel s {b | s b f.top} ≃r r :=
  RelIso.symm
  { toEquiv := ((Equiv.ofInjective f f.injective).trans (Equiv.setCongr
      (funext fun _ ↦ propext f.mem_range_iff_rel))),
    map_rel_iff' := f.map_rel_iff }

-- This lemma was always bad, but the linter only noticed after lean4#2644
attribute [nolint simpNF] PrincipalSeg.subrelIso_symm_apply

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem apply_subrelIso (f : r ≺i s) (b : {b | s b f.top}) :
    f (f.subrelIso b) = b :=
  Equiv.apply_ofInjective_symm f.injective _

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem subrelIso_apply (f : r ≺i s) (a : α) : f.subrelIso ⟨f a, f.lt_top a⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/-- Restrict the codomain of a principal segment -/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ => by simp [← f.mem_range_iff_rel]⟩

@[simp]
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl

@[simp]
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl

/-- Principal segment from an empty type into a type with a minimal element. -/
def ofIsEmpty (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    mem_range_iff_rel' := by simp [H] }

@[simp]
theorem ofIsEmpty_top (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl

/-- Principal segment from the empty relation on `PEmpty` to the empty relation on `PUnit`. -/
abbrev pemptyToPunit : @EmptyRelation PEmpty ≺i @EmptyRelation PUnit :=
  (@ofIsEmpty _ _ EmptyRelation _ _ PUnit.unit) fun _ => not_false

protected theorem acc [IsTrans β s] (f : r ≺i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  (f : r ≼i s).acc a

end PrincipalSeg

theorem wellFounded_iff_principalSeg.{u} {β : Type u} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ (α : Type u) (r : α → α → Prop) (_ : r ≺i s), WellFounded r :=
  ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩

/-! ### Properties of initial and principal segments -/


namespace InitialSeg

/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
noncomputable def ltOrEq [IsWellOrder β s] (f : r ≼i s) : (r ≺i s) ⊕ (r ≃r s) := by
  by_cases h : Surjective f
  · exact Sum.inr (RelIso.ofSurjective f h)
  · exact Sum.inl (f.toPrincipalSeg h)

theorem ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) : g a = f a :=
  @InitialSeg.eq α β r s _ g f a

theorem ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) : r ≺i t :=
  match f.ltOrEq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g

@[simp]
theorem leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLT g) a = g (f a) := by
  rw [InitialSeg.leLT]
  obtain f' | f' := f.ltOrEq
  · rw [PrincipalSeg.trans_apply, f.ltOrEq_apply_left]
  · rw [PrincipalSeg.equivLT_apply, f.ltOrEq_apply_right]

end InitialSeg

/-- The function in `collapse`. -/
private noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : Π a, { b // ¬s (f a) b } :=
  (RelEmbedding.isWellFounded f).fix _ fun a IH =>
    have H : f a ∈ { b | ∀ a h, s (IH a h).1 b } :=
      fun b h => trans_trichotomous_left (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ ⟨_, H⟩ H⟩

private theorem collapseF_lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a') (collapseF f a) := by
  show _ ∈ { b | ∀ a', r a' a → s (collapseF f a') b }
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _

private theorem collapseF_not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a', r a' a → s (collapseF f a') b) : ¬s b (collapseF f a) := by
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ _ _ h

/-- Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That is, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been used yet.

This construction is guaranteed to work as long as there exists some relation embedding `r ↪r s`. -/
noncomputable def RelEmbedding.collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h ↦ by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h ↦ ?_) lt).elim
      by_contra hn
      exact hm' _ hn h
    · rfl
    · exact (hm gt).elim⟩

/-- For any two well orders, one is an initial segment of the other. -/
noncomputable def InitialSeg.total (r s) [IsWellOrder α r] [IsWellOrder β s] :
    (r ≼i s) ⊕ (s ≼i r) :=
  match (leAdd r s).ltOrEq, (RelEmbedding.sumLexInr r s).collapse.ltOrEq with
  | Sum.inl f, Sum.inr g => Sum.inl <| f.ltEquiv g.symm
  | Sum.inr f, Sum.inl g => Sum.inr <| g.ltEquiv f.symm
  | Sum.inr f, Sum.inr g => Sum.inl <| InitialSeg.ofIso (f.trans g.symm)
  | Sum.inl f, Sum.inl g => Classical.choice <| by
      obtain h | h | h := trichotomous_of (Sum.Lex r s) f.top g.top
      · exact ⟨Sum.inl <| (f.codRestrict {x | Sum.Lex r s x g.top}
          (fun a => _root_.trans (f.lt_top a) h) h).ltEquiv g.subrelIso⟩
      · let f := f.subrelIso
        rw [h] at f
        exact ⟨Sum.inl <| InitialSeg.ofIso (f.symm.trans g.subrelIso)⟩
      · exact ⟨Sum.inr <| (g.codRestrict {x | Sum.Lex r s x f.top}
          (fun a => _root_.trans (g.lt_top a) h) h).ltEquiv f.subrelIso⟩

attribute [nolint simpNF] PrincipalSeg.ofElement_apply PrincipalSeg.subrelIso_symm_apply
  PrincipalSeg.apply_subrelIso PrincipalSeg.subrelIso_apply

/-! ### Initial or principal segments with `<` -/

namespace InitialSeg

variable [PartialOrder β] {a a' : α} {b : β}

theorem mem_range_of_le [Preorder α] (f : α ≤i β) (h : b ≤ f a) : b ∈ Set.range f := by
  obtain rfl | hb := h.eq_or_lt
  exacts [⟨a, rfl⟩, f.mem_range_of_rel hb]

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
theorem le_iff_le [PartialOrder α] (f : α ≤i β) : f a ≤ f a' ↔ a ≤ a' :=
  f.toOrderEmbedding.le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
theorem lt_iff_lt [PartialOrder α] (f : α ≤i β) : f a < f a' ↔ a < a' :=
  f.toOrderEmbedding.lt_iff_lt

theorem monotone [PartialOrder α] (f : α ≤i β) : Monotone f :=
  f.toOrderEmbedding.monotone

theorem strictMono [PartialOrder α] (f : α ≤i β) : StrictMono f :=
  f.toOrderEmbedding.strictMono

theorem le_apply_iff [LinearOrder α] (f : α ≤i β) : b ≤ f a ↔ ∃ c ≤ a, f c = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_le h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.le_iff_le] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.monotone hc

theorem lt_apply_iff [LinearOrder α] (f : α ≤i β) : b < f a ↔ ∃ a' < a, f a' = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_rel h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.lt_iff_lt] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.strictMono hc

end InitialSeg

namespace PrincipalSeg

variable [PartialOrder β] {a a' : α} {b : β}

theorem mem_range_of_le [Preorder α] (f : α <i β) (h : b ≤ f a) : b ∈ Set.range f :=
  (f : α ≤i β).mem_range_of_le h

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
theorem le_iff_le [PartialOrder α] (f : α <i β) : f a ≤ f a' ↔ a ≤ a' :=
  (f : α ≤i β).le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
theorem lt_iff_lt [PartialOrder α] (f : α <i β) : f a < f a' ↔ a < a' :=
  (f : α ≤i β).lt_iff_lt

theorem monotone [PartialOrder α] (f : α <i β) : Monotone f :=
  (f : α ≤i β).monotone

theorem strictMono [PartialOrder α] (f : α <i β) : StrictMono f :=
  (f : α ≤i β).strictMono

theorem le_apply_iff [LinearOrder α] (f : α <i β) : b ≤ f a ↔ ∃ c ≤ a, f c = b :=
  (f : α ≤i β).le_apply_iff

theorem lt_apply_iff [LinearOrder α] (f : α <i β) : b < f a ↔ ∃ a' < a, f a' = b :=
  (f : α ≤i β).lt_apply_iff

end PrincipalSeg
