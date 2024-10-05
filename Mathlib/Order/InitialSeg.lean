/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Set
import Mathlib.Order.WellFounded
import Mathlib.Data.Sum.Order
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

## Notations

These notations belong to the `InitialSeg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
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
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
infixl:25 " ≼i " => InitialSeg

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

theorem exists_eq_iff_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨a', e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

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

theorem Antisymm.aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  InitialSeg.eq (f.trans g) (InitialSeg.refl _)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  haveI := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, Antisymm.aux f g, Antisymm.aux g f⟩, f.map_rel_iff'⟩

@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl

@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl

theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
  or_iff_not_imp_right.2 fun h b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b) fun x _ IH =>
      not_forall_not.1 fun hn =>
        h
          ⟨x, fun y =>
            ⟨IH _, fun ⟨a, e⟩ => by
              rw [← e]
              exact (trichotomous _ _).resolve_right
                (not_or_intro (hn a) fun hl => not_exists.2 hn (f.mem_range_of_rel hl))⟩⟩

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
  /-- The image of the order embedding is the set of elements `b` such that `s b top` -/
  down' : ∀ b, s b top ↔ ∃ a, toRelEmbedding a = b

-- Porting note: deleted `scoped[InitialSeg]`
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
infixl:25 " ≺i " => PrincipalSeg

namespace PrincipalSeg

instance : CoeOut (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩

@[simp]
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl

theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b :=
  f.down' _

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.down.2 ⟨_, rfl⟩

theorem mem_range_of_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) :
    b ∈ Set.range f :=
  f.down.1 <| _root_.trans h <| f.lt_top _

@[deprecated mem_range_of_rel (since := "2024-09-21")]
alias init := mem_range_of_rel

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
  letI H := f.eq_or_principal.resolve_left hf
  ⟨f, Classical.choose H, Classical.choose_spec H⟩

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
    simp only [g.exists_eq_iff_rel, PrincipalSeg.down, exists_and_left.symm, exists_swap,
        RelEmbedding.trans_apply, exists_eq_right', InitialSeg.coe_coe_fn]⟩

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
    suffices (∃ a : β, g a = c) ↔ ∃ a : α, g (f a) = c by simpa [PrincipalSeg.down]
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : PrincipalSeg r s)
    (g : s ≃r t) : PrincipalSeg r t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, by
    intro x
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr]
    intro y; exact ⟨congr_arg g, fun h => g.toEquiv.bijective.1 h⟩⟩

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
      simp only [PrincipalSeg.down, ef]
    cases f
    cases g
    have := RelEmbedding.coe_fn_injective ef; congr ⟩

theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)]; rfl

theorem topLTTop {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : PrincipalSeg r s) (g : PrincipalSeg s t) (h : PrincipalSeg r t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

/-- Any element of a well order yields a principal segment -/
def ofElement {α : Type*} (r : α → α → Prop) (a : α) : Subrel r { b | r b a } ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨⟨_, h⟩, rfl⟩ => h⟩⟩

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
      (funext fun _ ↦ propext f.down.symm))),
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
theorem subrelIso_apply (f : r ≺i s) (a : α) :
    f.subrelIso ⟨f a, f.down.mpr ⟨a, rfl⟩⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/-- Restrict the codomain of a principal segment -/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ =>
    f.down.trans <|
      exists_congr fun a => show (⟨f a, H a⟩ : p).1 = _ ↔ _ from ⟨Subtype.eq, congr_arg _⟩⟩

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
    down' := by simp [H] }

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

/-- A relation is well-founded iff every principal segment of it is well-founded.

In this lemma we use `Subrel` to indicate its principal segments because it's usually more
convenient to use.
-/
theorem wellFounded_iff_wellFounded_subrel {β : Type*} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ b, WellFounded (Subrel s { b' | s b' b }) := by
  refine
    ⟨fun wf b => ⟨fun b' => ((PrincipalSeg.ofElement _ b).acc b').mpr (wf.apply b')⟩, fun wf =>
      ⟨fun b => Acc.intro _ fun b' hb' => ?_⟩⟩
  let f := PrincipalSeg.ofElement s b
  obtain ⟨b', rfl⟩ := f.down.mp ((PrincipalSeg.ofElement_top s b).symm ▸ hb' : s b' f.top)
  exact (f.acc b').mp ((wf b).apply b')

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

theorem ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  @InitialSeg.eq α β r s _ g f a

theorem ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) :
    g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.ltOrEq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g

@[simp]
theorem leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLT g) a = g (f a) := by
  delta InitialSeg.leLT; cases' f.ltOrEq with f' f'
  · simp only [PrincipalSeg.trans_apply, f.ltOrEq_apply_left]
  · simp only [PrincipalSeg.equivLT_apply, f.ltOrEq_apply_right]

end InitialSeg

namespace RelEmbedding

/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : ∀ a, { b // ¬s (f a) b } :=
  (RelEmbedding.wellFounded f <| IsWellFounded.wf).fix fun a IH => by
    let S := { b | ∀ a h, s (IH a h).1 b }
    have : f a ∈ S := fun a' h =>
      ((trichotomous _ _).resolve_left fun h' =>
            (IH a' h).2 <| _root_.trans (f.map_rel_iff.2 h) h').resolve_left
        fun h' => (IH a' h).2 <| h' ▸ f.map_rel_iff.2 h
    exact ⟨_, IsWellFounded.wf.not_lt_min _ ⟨_, this⟩ this⟩

theorem collapseF.lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a').1 (collapseF f a).1 := @fun a => by
  revert a
  show (collapseF f a).1 ∈ { b | ∀ (a') (_ : r a' a), s (collapseF f a').1 b }
  unfold collapseF; rw [WellFounded.fix_eq]
  dsimp only
  apply WellFounded.min_mem _ _

theorem collapseF.not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a' (_ : r a' a), s (collapseF f a').1 b) : ¬s b (collapseF f a).1 := by
  unfold collapseF; rw [WellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ _ _ h

/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
noncomputable def collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  haveI := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone (fun a => (collapseF f a).1) fun a b => collapseF.lt f, fun a b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b)
      (fun b _ _ a h => by
        rcases (@IsWellFounded.wf _ r).has_min { a | ¬s (collapseF f a).1 b }
          ⟨_, asymm h⟩ with ⟨m, hm, hm'⟩
        refine ⟨m, ((@trichotomous _ s _ _ _).resolve_left hm).resolve_right
          (collapseF.not_lt f _ fun a' h' => ?_)⟩
        by_contra hn
        exact hm' _ hn h')
      a⟩

theorem collapse_apply [IsWellOrder β s] (f : r ↪r s) (a) : collapse f a = (collapseF f a).1 :=
  rfl

end RelEmbedding

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
