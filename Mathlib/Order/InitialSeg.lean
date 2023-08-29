/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Set
import Mathlib.Order.WellFounded

#align_import order.initial_seg from "leanprover-community/mathlib"@"8ea5598db6caeddde6cb734aa179cc2408dbd345"
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

set_option autoImplicit true


variable {α : Type*} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

open Function

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
structure InitialSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The order embedding is an initial segment -/
  init' : ∀ a b, s b (toRelEmbedding a) → ∃ a', toRelEmbedding a' = b
#align initial_seg InitialSeg

-- Porting notes: Deleted `scoped[InitialSeg]`
/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
infixl:25 " ≼i " => InitialSeg

namespace InitialSeg

instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩

instance : EmbeddingLike (r ≼i s) α β :=
  { coe := fun f => f.toFun
    coe_injective' := by
      rintro ⟨f, hf⟩ ⟨g, hg⟩ h
      -- ⊢ { toRelEmbedding := f, init' := hf } = { toRelEmbedding := g, init' := hg }
      congr with x
      -- ⊢ ↑f x = ↑g x
      exact congr_fun h x,
      -- 🎉 no goals
    injective' := fun f => f.inj' }

@[ext] lemma ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align initial_seg.ext InitialSeg.ext

@[simp]
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
#align initial_seg.coe_coe_fn InitialSeg.coe_coe_fn

theorem init (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
  f.init' _ _
#align initial_seg.init InitialSeg.init

theorem map_rel_iff (f : r ≼i s) : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'
#align initial_seg.map_rel_iff InitialSeg.map_rel_iff

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.init h with ⟨a', rfl⟩
    -- ⊢ ∃ a'_1, ↑f a'_1 = ↑f a' ∧ r a'_1 a
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    -- 🎉 no goals
    fun ⟨a', e, h⟩ => e ▸ f.map_rel_iff.2 h⟩
#align initial_seg.init_iff InitialSeg.init_iff

/-- An order isomorphism is an initial segment -/
def ofIso (f : r ≃r s) : r ≼i s :=
  ⟨f, fun _ b _ => ⟨f.symm b, RelIso.apply_symm_apply f _⟩⟩
#align initial_seg.of_iso InitialSeg.ofIso

/-- The identity function shows that `≼i` is reflexive -/
@[refl]
protected def refl (r : α → α → Prop) : r ≼i r :=
  ⟨RelEmbedding.refl _, fun _ _ _ => ⟨_, rfl⟩⟩
#align initial_seg.refl InitialSeg.refl

instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp at h ⊢
    -- ⊢ ∃ a', ↑g (↑f a') = c
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    -- ⊢ ∃ a', ↑g (↑f a') = ↑g.toRelEmbedding b
                                    -- ⊢ ∃ a', ↑g (↑f a') = ↑g.toRelEmbedding b
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩
    -- ⊢ ∃ a'_1, ↑g (↑f a'_1) = ↑g.toRelEmbedding (↑f.toRelEmbedding a')
                                     -- 🎉 no goals
#align initial_seg.trans InitialSeg.trans

@[simp]
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl
#align initial_seg.refl_apply InitialSeg.refl_apply

@[simp]
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl
#align initial_seg.trans_apply InitialSeg.trans_apply

instance subsingleton_of_trichotomous_of_irrefl [IsTrichotomous β s] [IsIrrefl β s]
    [IsWellFounded α r] : Subsingleton (r ≼i s) :=
  ⟨fun f g => by
    ext a
    -- ⊢ ↑f a = ↑g a
    refine' IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => _
    rw [f.init_iff, g.init_iff]
    -- ⊢ (∃ a', ↑f a' = x ∧ r a' b) ↔ ∃ a', ↑g a' = x ∧ r a' b
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl⟩
    -- 🎉 no goals
#align initial_seg.subsingleton_of_trichotomous_of_irrefl InitialSeg.subsingleton_of_trichotomous_of_irrefl

instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => by let _ := a.isWellFounded; exact Subsingleton.elim a⟩
               -- ⊢ ∀ (b : r ≼i s), a = b
                                         -- 🎉 no goals

protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]
  -- 🎉 no goals
#align initial_seg.eq InitialSeg.eq

theorem Antisymm.aux [IsWellOrder α r] (f : r ≼i s) (g : s ≼i r) : LeftInverse g f :=
  InitialSeg.eq (f.trans g) (InitialSeg.refl _)
#align initial_seg.antisymm.aux InitialSeg.Antisymm.aux

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  haveI := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, Antisymm.aux f g, Antisymm.aux g f⟩, f.map_rel_iff'⟩
#align initial_seg.antisymm InitialSeg.antisymm

@[simp]
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl
#align initial_seg.antisymm_to_fun InitialSeg.antisymm_toFun

@[simp]
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl
#align initial_seg.antisymm_symm InitialSeg.antisymm_symm

theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
  or_iff_not_imp_right.2 fun h b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b) fun x _ IH =>
      not_forall_not.1 fun hn =>
        h
          ⟨x, fun y =>
            ⟨IH _, fun ⟨a, e⟩ => by
              rw [← e];
              -- ⊢ s (↑f a) x
                exact
                  (trichotomous _ _).resolve_right
                    (not_or_of_not (hn a) fun hl => not_exists.2 hn (f.init hl))⟩⟩
#align initial_seg.eq_or_principal InitialSeg.eq_or_principal

/-- Restrict the codomain of an initial segment -/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.init h
    ⟨a', by subst e; rfl⟩⟩
            -- ⊢ ↑(RelEmbedding.codRestrict p f.toRelEmbedding H) a' = { val := ↑f a', proper …
                     -- 🎉 no goals
#align initial_seg.cod_restrict InitialSeg.codRestrict

@[simp]
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align initial_seg.cod_restrict_apply InitialSeg.codRestrict_apply

/-- Initial segment from an empty type. -/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩
#align initial_seg.of_is_empty InitialSeg.ofIsEmpty

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def leAdd (r : α → α → Prop) (s : β → β → Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩
    -- 🎉 no goals
#align initial_seg.le_add InitialSeg.leAdd

@[simp]
theorem leAdd_apply (r : α → α → Prop) (s : β → β → Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl
#align initial_seg.le_add_apply InitialSeg.leAdd_apply

protected theorem acc (f : r ≼i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  ⟨by
    refine' fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => _
    -- ⊢ Acc s b
    obtain ⟨a', rfl⟩ := f.init hb
    -- ⊢ Acc s (↑f a')
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩
    -- 🎉 no goals
#align initial_seg.acc InitialSeg.acc

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
#align principal_seg PrincipalSeg

-- Porting notes: deleted `scoped[InitialSeg]`
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
#align principal_seg.coe_fn_mk PrincipalSeg.coe_fn_mk

theorem down (f : r ≺i s) : ∀ {b : β}, s b f.top ↔ ∃ a, f a = b :=
  f.down' _
#align principal_seg.down PrincipalSeg.down

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.down.2 ⟨_, rfl⟩
#align principal_seg.lt_top PrincipalSeg.lt_top

theorem init [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
  f.down.1 <| _root_.trans h <| f.lt_top _
#align principal_seg.init PrincipalSeg.init

/-- A principal segment is in particular an initial segment. -/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.init⟩⟩
#align principal_seg.has_coe_initial_seg PrincipalSeg.hasCoeInitialSeg

theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl
#align principal_seg.coe_coe_fn' PrincipalSeg.coe_coe_fn'

theorem init_iff [IsTrans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.init_iff α β r s f a b
#align principal_seg.init_iff PrincipalSeg.init_iff

theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False := by
  have h := f.lt_top f.top
  -- ⊢ False
  rw [show f f.top = f.top from InitialSeg.eq (↑f) (InitialSeg.refl r) f.top] at h
  -- ⊢ False
  exact _root_.irrefl _ h
  -- 🎉 no goals
#align principal_seg.irrefl PrincipalSeg.irrefl

instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

/-- Composition of a principal segment with an initial segment, as a principal segment -/
def ltLe (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp only [g.init_iff, PrincipalSeg.down, exists_and_left.symm, exists_swap,
        RelEmbedding.trans_apply, exists_eq_right', InitialSeg.coe_coe_fn]⟩
#align principal_seg.lt_le PrincipalSeg.ltLe

@[simp]
theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.ltLe g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.lt_le_apply PrincipalSeg.lt_le_apply

@[simp]
theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.ltLe g).top = g f.top :=
  rfl
#align principal_seg.lt_le_top PrincipalSeg.lt_le_top

/-- Composition of two principal segments as a principal segment -/
@[trans]
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  ltLe f g
#align principal_seg.trans PrincipalSeg.trans

@[simp]
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
  lt_le_apply _ _ _
#align principal_seg.trans_apply PrincipalSeg.trans_apply

@[simp]
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl
#align principal_seg.trans_top PrincipalSeg.trans_top

/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equivLT (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c =>
    suffices (∃ a : β, g a = c) ↔ ∃ a : α, g (f a) = c by simpa [PrincipalSeg.down]
                                                          -- 🎉 no goals
                                 -- 🎉 no goals
    ⟨fun ⟨b, h⟩ => ⟨f.symm b, by simp only [h, RelIso.apply_symm_apply]⟩,
      fun ⟨a, h⟩ => ⟨f a, h⟩⟩⟩
#align principal_seg.equiv_lt PrincipalSeg.equivLT

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def ltEquiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f : PrincipalSeg r s)
    (g : s ≃r t) : PrincipalSeg r t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, by
    intro x
    -- ⊢ t x (↑g f.top) ↔ ∃ a, ↑(RelEmbedding.trans f.toRelEmbedding (RelIso.toRelEmb …
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr]
    -- ⊢ ∀ (a : α), ↑f.toRelEmbedding a = ↑(RelIso.symm g) x ↔ ↑(RelEmbedding.trans f …
    intro y; exact ⟨congr_arg g, fun h => g.toEquiv.bijective.1 h⟩⟩
    -- ⊢ ↑f.toRelEmbedding y = ↑(RelIso.symm g) x ↔ ↑(RelEmbedding.trans f.toRelEmbed …
             -- 🎉 no goals
#align principal_seg.lt_equiv PrincipalSeg.ltEquiv

@[simp]
theorem equivLT_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equivLT f g) a = g (f a) :=
  RelEmbedding.trans_apply _ _ _
#align principal_seg.equiv_lt_apply PrincipalSeg.equivLT_apply

@[simp]
theorem equivLT_top (f : r ≃r s) (g : s ≺i t) : (equivLT f g).top = g.top :=
  rfl
#align principal_seg.equiv_lt_top PrincipalSeg.equivLT_top

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) :=
  ⟨fun f g => by
    have ef : (f : α → β) = g := by
      show ((f : r ≼i s) : α → β) = (g : r ≼i s)
      rw [@Subsingleton.elim _ _ (f : r ≼i s) g]
    have et : f.top = g.top := by
      refine' extensional_of_trichotomous_of_irrefl s fun x => _
      simp only [PrincipalSeg.down, ef]
    cases f
    -- ⊢ { toRelEmbedding := toRelEmbedding✝, top := top✝, down' := down'✝ } = g
    cases g
    -- ⊢ { toRelEmbedding := toRelEmbedding✝¹, top := top✝¹, down' := down'✝¹ } = { t …
    have := RelEmbedding.coe_fn_injective ef; congr ⟩
    -- ⊢ { toRelEmbedding := toRelEmbedding✝¹, top := top✝¹, down' := down'✝¹ } = { t …
                                              -- 🎉 no goals

theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.equivLT e g)]; rfl
  -- ⊢ (equivLT e g).top = g.top
                                                       -- 🎉 no goals
#align principal_seg.top_eq PrincipalSeg.top_eq

theorem topLTTop {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : PrincipalSeg r s) (g : PrincipalSeg s t) (h : PrincipalSeg r t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  -- ⊢ t (PrincipalSeg.trans f g).top g.top
  apply PrincipalSeg.lt_top
  -- 🎉 no goals
#align principal_seg.top_lt_top PrincipalSeg.topLTTop

/-- Any element of a well order yields a principal segment -/
def ofElement {α : Type*} (r : α → α → Prop) (a : α) : Subrel r { b | r b a } ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨⟨_, h⟩, rfl⟩ => h⟩⟩
#align principal_seg.of_element PrincipalSeg.ofElement

@[simp]
theorem ofElement_apply {α : Type*} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl
#align principal_seg.of_element_apply PrincipalSeg.ofElement_apply

@[simp]
theorem ofElement_top {α : Type*} (r : α → α → Prop) (a : α) : (ofElement r a).top = a :=
  rfl
#align principal_seg.of_element_top PrincipalSeg.ofElement_top

/-- For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic to `r`. -/
@[simps! symm_apply]
noncomputable def subrelIso (f : r ≺i s) : Subrel s {b | s b f.top} ≃r r :=
  RelIso.symm
  { toEquiv := ((Equiv.ofInjective f f.injective).trans (Equiv.setCongr
      (funext fun _ ↦ propext f.down.symm))),
    map_rel_iff' := f.map_rel_iff }

@[simp]
theorem apply_subrelIso (f : r ≺i s) (b : {b | s b f.top}) :
    f (f.subrelIso b) = b :=
  Equiv.apply_ofInjective_symm f.injective _

@[simp]
theorem subrelIso_apply (f : r ≺i s) (a : α) :
    f.subrelIso ⟨f a, f.down.mpr ⟨a, rfl⟩⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/-- Restrict the codomain of a principal segment -/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i Subrel s p :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ =>
    f.down.trans <|
      exists_congr fun a => show (⟨f a, H a⟩ : p).1 = _ ↔ _ from ⟨Subtype.eq, congr_arg _⟩⟩
#align principal_seg.cod_restrict PrincipalSeg.codRestrict

@[simp]
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl
#align principal_seg.cod_restrict_apply PrincipalSeg.codRestrict_apply

@[simp]
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl
#align principal_seg.cod_restrict_top PrincipalSeg.codRestrict_top

/-- Principal segment from an empty type into a type with a minimal element. -/
def ofIsEmpty (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    down' := by simp [H] }
                -- 🎉 no goals
#align principal_seg.of_is_empty PrincipalSeg.ofIsEmpty

@[simp]
theorem ofIsEmpty_top (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl
#align principal_seg.of_is_empty_top PrincipalSeg.ofIsEmpty_top

/-- Principal segment from the empty relation on `PEmpty` to the empty relation on `PUnit`. -/
@[reducible]
def pemptyToPunit : @EmptyRelation PEmpty ≺i @EmptyRelation PUnit :=
  (@ofIsEmpty _ _ EmptyRelation _ _ PUnit.unit) fun _ => not_false
#align principal_seg.pempty_to_punit PrincipalSeg.pemptyToPunit

protected theorem acc [IsTrans β s] (f : r ≺i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  (f : r ≼i s).acc a
#align principal_seg.acc PrincipalSeg.acc

end PrincipalSeg

/-- A relation is well-founded iff every principal segment of it is well-founded.

In this lemma we use `Subrel` to indicate its principal segments because it's usually more
convenient to use.
-/
theorem wellFounded_iff_wellFounded_subrel {β : Type*} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ b, WellFounded (Subrel s { b' | s b' b }) := by
  refine'
    ⟨fun wf b => ⟨fun b' => ((PrincipalSeg.ofElement _ b).acc b').mpr (wf.apply b')⟩, fun wf =>
      ⟨fun b => Acc.intro _ fun b' hb' => _⟩⟩
  let f := PrincipalSeg.ofElement s b
  -- ⊢ Acc s b'
  obtain ⟨b', rfl⟩ := f.down.mp ((PrincipalSeg.ofElement_top s b).symm ▸ hb' : s b' f.top)
  -- ⊢ Acc s (↑f.toRelEmbedding b')
  exact (f.acc b').mp ((wf b).apply b')
  -- 🎉 no goals
#align well_founded_iff_well_founded_subrel wellFounded_iff_wellFounded_subrel

theorem wellFounded_iff_principalSeg.{u} {β : Type u} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ (α : Type u) (r : α → α → Prop) (_ : r ≺i s), WellFounded r :=
  ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩
#align well_founded_iff_principal_seg wellFounded_iff_principalSeg

/-! ### Properties of initial and principal segments -/


/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
noncomputable def InitialSeg.ltOrEq [IsWellOrder β s] (f : r ≼i s) : Sum (r ≺i s) (r ≃r s) := by
  by_cases h : Surjective f
  -- ⊢ (r ≺i s) ⊕ (r ≃r s)
  · exact Sum.inr (RelIso.ofSurjective f h)
    -- 🎉 no goals
  · have h' : _ := (InitialSeg.eq_or_principal f).resolve_left h
    -- ⊢ (r ≺i s) ⊕ (r ≃r s)
    exact Sum.inl ⟨f, Classical.choose h', Classical.choose_spec h'⟩
    -- 🎉 no goals
#align initial_seg.lt_or_eq InitialSeg.ltOrEq

theorem InitialSeg.ltOrEq_apply_left [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  @InitialSeg.eq α β r s _ g f a
#align initial_seg.lt_or_eq_apply_left InitialSeg.ltOrEq_apply_left

theorem InitialSeg.ltOrEq_apply_right [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) :
    g a = f a :=
  InitialSeg.eq (InitialSeg.ofIso g) f a
#align initial_seg.lt_or_eq_apply_right InitialSeg.ltOrEq_apply_right

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
noncomputable def InitialSeg.leLT [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.ltOrEq with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.equivLT f' g
#align initial_seg.le_lt InitialSeg.leLT

@[simp]
theorem InitialSeg.leLT_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    (f.leLT g) a = g (f a) := by
  delta InitialSeg.leLT; cases' h : f.ltOrEq with f' f'
  -- ⊢ ↑(match ltOrEq f with
  · simp only [PrincipalSeg.trans_apply, f.ltOrEq_apply_left]
    -- 🎉 no goals
  · simp only [PrincipalSeg.equivLT_apply, f.ltOrEq_apply_right]
    -- 🎉 no goals
#align initial_seg.le_lt_apply InitialSeg.leLT_apply

namespace RelEmbedding

/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : ∀ a, { b // ¬s (f a) b } :=
  (RelEmbedding.wellFounded f <| IsWellFounded.wf).fix fun a IH => by
    let S := { b | ∀ a h, s (IH a h).1 b }
    -- ⊢ { b // ¬s (↑f a) b }
    have : f a ∈ S := fun a' h =>
      ((trichotomous _ _).resolve_left fun h' =>
            (IH a' h).2 <| _root_.trans (f.map_rel_iff.2 h) h').resolve_left
        fun h' => (IH a' h).2 <| h' ▸ f.map_rel_iff.2 h
    exact ⟨_, IsWellFounded.wf.not_lt_min _ ⟨_, this⟩ this⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align rel_embedding.collapse_F RelEmbedding.collapseF

theorem collapseF.lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a').1 (collapseF f a).1 := @fun a => by
  revert a
  -- ⊢ ∀ (a_1 : α), r a_1 a → s ↑(collapseF f a_1) ↑(collapseF f a)
  show (collapseF f a).1 ∈ { b | ∀ (a') (_ : r a' a), s (collapseF f a').1 b }
  -- ⊢ ↑(collapseF f a) ∈ {b | ∀ (a' : α), r a' a → s (↑(collapseF f a')) b}
  unfold collapseF; rw [WellFounded.fix_eq]
  -- ⊢ ↑(WellFounded.fix (_ : WellFounded r)
                    -- ⊢ ↑(let S :=
  dsimp only
  -- ⊢ WellFounded.min (_ : WellFounded s) {b | ∀ (a_1 : α), r a_1 a → s (↑(WellFou …
  apply WellFounded.min_mem _ _
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align rel_embedding.collapse_F.lt RelEmbedding.collapseF.lt

theorem collapseF.not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a' (_ : r a' a), s (collapseF f a').1 b) : ¬s b (collapseF f a).1 := by
  unfold collapseF; rw [WellFounded.fix_eq]
  -- ⊢ ¬s b
                    -- ⊢ ¬s b
  dsimp only
  -- ⊢ ¬s b (WellFounded.min (_ : WellFounded s) {b | ∀ (a_1 : α), r a_1 a → s (↑(W …
  exact WellFounded.not_lt_min _ _ _ h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align rel_embedding.collapse_F.not_lt RelEmbedding.collapseF.not_lt

/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
noncomputable def collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  haveI := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone (fun a => (collapseF f a).1) fun a b => collapseF.lt f, fun a b =>
    Acc.recOn (IsWellFounded.wf.apply b : Acc s b)
      (fun b _ _ a h => by
        rcases (@IsWellFounded.wf _ r).has_min { a | ¬s (collapseF f a).1 b }
          ⟨_, asymm h⟩ with ⟨m, hm, hm'⟩
        refine' ⟨m, ((@trichotomous _ s _ _ _).resolve_left hm).resolve_right
          (collapseF.not_lt f _ fun a' h' => _)⟩
        by_contra hn
        -- ⊢ False
        exact hm' _ hn h')
        -- 🎉 no goals
      a⟩
#align rel_embedding.collapse RelEmbedding.collapse

theorem collapse_apply [IsWellOrder β s] (f : r ↪r s) (a) : collapse f a = (collapseF f a).1 :=
  rfl
#align rel_embedding.collapse_apply RelEmbedding.collapse_apply

end RelEmbedding
