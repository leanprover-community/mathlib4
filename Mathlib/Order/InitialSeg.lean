/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Set
import Mathlib.Order.WellFounded
/-!
# Initial and principal segments

This file defines initial and principal segment embeddings.

An initial segment within a well order is any downwards closed subset. A principal segment is an
initial segment other than `Set.univ`.

An initial segment embedding `r ≼i s` is an order embedding `r ↪ s` such that its range is an
initial segment. Likewise, a principal segment embedding `r ≺i s` has a principal segment for a
range.

## Main definitions

* `InitialSeg r s`: Type of initial segment embeddings of `r` into `s` , denoted by `r ≼i s`.
* `PrincipalSeg r s`: Type of principal segment embeddings of `r` into `s` , denoted by `r ≺i s`.

## Notations

These notations belong to the `InitialSeg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
-/

/-! ### Initial segment embeddings -/

variable {α : Type*} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

open Function

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose `Set.range` is downwards closed. That is, whenever `b < f a` in `β` then `b` is in
the range of `f`. -/
structure InitialSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The range of the embedding is downwards closed. -/
  init' : ∀ a b, s b (toRelEmbedding a) → b ∈ Set.range toRelEmbedding

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose `Set.range` is downwards closed. That is, whenever `b < f a` in `β` then `b` is in
the range of `f`. -/
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

/-- The property characterizing initial segment embeddings. -/
theorem init (f : r ≼i s) {a : α} {b : β} : s b (f a) → b ∈ Set.range f :=
  f.init' _ _

theorem map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.init h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨a', e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

/-- An order isomorphism is an initial segment embedding. -/
def ofIso (f : r ≃r s) : r ≼i s :=
  ⟨f, fun _ b _ => ⟨f.symm b, RelIso.apply_symm_apply f _⟩⟩

/-- The identity function shows that `≼i` is reflexive. -/
@[refl]
protected def refl (r : α → α → Prop) : r ≼i r :=
  ⟨RelEmbedding.refl _, fun _ _ _ => ⟨_, rfl⟩⟩

instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive. -/
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
    rw [f.init_iff, g.init_iff]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl⟩

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => by let _ := a.isWellFounded; exact Subsingleton.elim a⟩

protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

private theorem antisymm_aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  InitialSeg.eq (f.trans g) (InitialSeg.refl _)

/-- If we have order embeddings between `α` and `β` whose ranges are initial segments, and `β` is a
well order, then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  haveI := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, antisymm_aux f g, antisymm_aux g f⟩, f.map_rel_iff'⟩

@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl

@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl

/-- An initial segment embedding is either an isomorphism, or a principal segment embedding.

See also `InitialSeg.ltOrEq`. -/
theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x := by
  apply or_iff_not_imp_right.2
  intro h b
  push_neg at h
  apply IsWellFounded.induction s b
  intro x IH
  obtain ⟨y, ⟨hs, hy⟩ | ⟨hs, hy⟩⟩ := h x
  · obtain ⟨z, rfl⟩ := IH y hs
    exact (hy z rfl).elim
  · obtain (rfl | h) := (trichotomous y x).resolve_left hs
    · exact hy
    · obtain ⟨z, rfl⟩ := hy
      exact f.init h

/-- Restrict the codomain of an initial segment -/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.init h
    ⟨a', by subst e; rfl⟩⟩

@[simp]
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- Initial segment embedding from an empty type. -/
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
    obtain ⟨a', rfl⟩ := f.init hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩

end InitialSeg

/-! ### Principal segments -/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an initial
segment embedding that isn't surjective. We express this via the existence of `top` such that the
range of `f` is `Iio top`. -/
structure PrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The supremum of the principal segment. -/
  top : β
  /-- The range of the order embedding is `Iio top`. -/
  down' : ∀ a, s a top ↔ a ∈ Set.range toRelEmbedding

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an initial
segment embedding that isn't surjective. We express this via the existence of `top` such that the
range of `f` is `Iio top`. -/
infixl:25 " ≺i " => PrincipalSeg

namespace PrincipalSeg

instance : CoeOut (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩

@[simp]
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl

/-- The property characterizing principal segment embeddings. -/
theorem down (f : r ≺i s) : ∀ {a : β}, s a f.top ↔ a ∈ Set.range f :=
  f.down' _

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.down.2 ⟨_, rfl⟩

theorem init [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : b ∈ Set.range f :=
  f.down.1 <| _root_.trans h <| f.lt_top _

/-- A principal segment embedding is in particular an initial segment embedding. -/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.init⟩⟩

theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl

theorem init_iff [IsTrans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.init_iff α β r s f a b

theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False := by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq (↑f) (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h

instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

/-- Composition of a principal segment with an initial segment, as a principal segment. -/
def ltLe (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp only [g.init_iff, PrincipalSeg.down, exists_and_left.symm, exists_swap,
        RelEmbedding.trans_apply, exists_eq_right', InitialSeg.coe_coe_fn, Set.mem_range]⟩

@[simp]
theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.ltLe g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _

@[simp]
theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.ltLe g).top = g f.top :=
  rfl

/-- Composition of two principal segments as a principal segment. -/
@[trans]
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  ltLe f g

@[simp]
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
  lt_le_apply _ _ _

@[simp]
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl

/-- Composition of an order isomorphism with a principal segment, as a principal segment. -/
def equivLT (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c =>
    suffices (∃ a : β, g a = c) ↔ ∃ a : α, g (f a) = c by simp [PrincipalSeg.down]
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩

/-- Composition of a principal segment with an order isomorphism, as a principal segment. -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : PrincipalSeg r s)
    (g : s ≃r t) : PrincipalSeg r t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, by
    intro x
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', Set.mem_range, Set.mem_range, exists_congr]
    intro y; exact ⟨congr_arg g, fun h => g.toEquiv.bijective.1 h⟩⟩

@[simp]
theorem equivLT_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equivLT f g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _

@[simp]
theorem equivLT_top (f : r ≃r s) (g : s ≺i t) : (equivLT f g).top = g.top :=
  rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) := by
  constructor
  intro f g
  have ef : (f : α → β) = g := by
    show ((f : r ≼i s) : α → β) = (g : r ≼i s)
    rw [@Subsingleton.elim _ _ (f : r ≼i s) g]
  have et : f.top = g.top := by
    refine extensional_of_trichotomous_of_irrefl s fun x => ?_
    simp only [PrincipalSeg.down, ef]
  cases f
  cases g
  have := RelEmbedding.coe_fn_injective ef
  congr

theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)]; rfl

theorem topLTTop {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : PrincipalSeg r s) (g : PrincipalSeg s t) (h : PrincipalSeg r t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

/-- Build a principal segment embedding from a principal segment defined by a given `a : α`. -/
-- The explicit typing is required in order for `simp` to work properly.
def ofElement {α : Type*} (r : α → α → Prop) (a : α) :
    @PrincipalSeg (Subtype fun b => r b a) α (Subrel r _) r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨⟨_, h⟩, rfl⟩ => h⟩⟩

@[simp]
theorem ofElement_apply {α : Type*} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl

@[simp]
theorem ofElement_top {α : Type*} (r : α → α → Prop) (a : α) : (ofElement r a).top = a :=
  rfl

/-- For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic to `r`. -/
-- The explicit typing is required in order for `simp` to work properly.
@[simps! symm_apply]
noncomputable def subrelIso (f : r ≺i s) :
    @RelIso (Subtype fun b => s b f.top) α (Subrel s _) r :=
  RelIso.symm
  { toEquiv := ((Equiv.ofInjective f f.injective).trans (Equiv.setCongr
      (funext fun _ ↦ propext f.down.symm))),
    map_rel_iff' := f.map_rel_iff }

@[simp]
theorem apply_subrelIso (f : r ≺i s) (b : {b | s b f.top}) : f (f.subrelIso b) = b :=
  Equiv.apply_ofInjective_symm f.injective _

@[simp]
theorem subrelIso_apply (f : r ≺i s) (a : α) : f.subrelIso ⟨f a, f.down.mpr ⟨a, rfl⟩⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/-- Restrict the codomain of a principal segment. -/
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

/-- A relation is well-founded iff every principal segment of it is well-founded. -/
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

/-- Every initial segment embedding into a well order can be turned into an isomorphism if
surjective, or into a principal segment embedding if not. -/
noncomputable def InitialSeg.ltOrEq [IsWellOrder β s] (f : r ≼i s) : (r ≺i s) ⊕ (r ≃r s) := by
  by_cases h : Surjective f
  · exact Sum.inr (RelIso.ofSurjective f h)
  · have h' : _ := (InitialSeg.eq_or_principal f).resolve_left h
    exact Sum.inl ⟨f, Classical.choose h', Classical.choose_spec h'⟩

theorem InitialSeg.ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  @InitialSeg.eq α β r s _ g f a

theorem InitialSeg.ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) :
    g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def InitialSeg.leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.ltOrEq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g

@[simp]
theorem InitialSeg.leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLT g) a = g (f a) := by
  delta InitialSeg.leLT; cases' f.ltOrEq with f' f'
  · simp only [PrincipalSeg.trans_apply, f.ltOrEq_apply_left]
  · simp only [PrincipalSeg.equivLT_apply, f.ltOrEq_apply_right]

namespace RelEmbedding

/-- The function in `collapse`. -/
private noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : Π a, { b // ¬s (f a) b } :=
  (RelEmbedding.isWellFounded f).fix fun a IH =>
    have H : f a ∈ { b | ∀ a h, s (IH a h).1 b } :=
      fun b h => trans_le_lt (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ ⟨_, H⟩ H⟩

private theorem collapseF.lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a').1 (collapseF f a).1 := @fun a => by
  revert a
  show _ ∈ { b | ∀ a', r a' a → s (collapseF f a').1 b }
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _

private theorem collapseF.not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a', r a' a → s (collapseF f a').1 b) : ¬s b (collapseF f a).1 := by
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ _ _ h

/-- Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That is, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been used yet.

This construction is guaranteed to work as long as there exists some order embedding `r ↪r s`. -/
noncomputable def collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  haveI := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF.lt f, by
    intro a b h
    rcases (@IsWellFounded.wf _ r).has_min { a | ¬s _ b } ⟨_, asymm h⟩ with ⟨m, hm, hm'⟩
    use m
    rcases @trichotomous β s _ b (collapseF f m).1 with (lt | rfl | gt)
    · apply (collapseF.not_lt f m ?_ lt).elim
      intro c h
      by_contra hn
      exact hm' _ hn h
    · rfl
    · exact (hm gt).elim⟩

end RelEmbedding
