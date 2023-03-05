/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.PathCategory
import Mathlib.CategoryTheory.Quotient


/-!
# Universal Groupoid

This file defines the Universal Groupoid of a Groupoid along a function.

-/

namespace CategoryTheory
namespace Groupoid
namespace Universal

universe u v u' v' u'' v''

variable {V : Type u} [Groupoid V] {V' : Type u'} (σ : V → V')

scoped postfix:50 " * " => fun σ => Quiver.Push.of σ ⋙q Paths.of

@[simp]
def _root_.Quiver.Path.asHom {X Y : Quiver.Push σ} (f : Quiver.Path X Y) :
    Paths.of.obj X ⟶ Paths.of.obj Y := f

@[simp]
def Hom.push {X Y : V} (f : X ⟶ Y) : (σ *).obj X ⟶ (σ *).obj Y := (σ *).map f

@[simp]
lemma PathsPush_id_eq (X : Paths $ Quiver.Push σ) : 𝟙 X = Quiver.Path.nil := rfl

@[simp]
lemma PathsPush_comp_eq {X Y Z : Paths $ Quiver.Push σ} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = Quiver.Path.comp f g := rfl

@[simp]
def _root_.Quiver.Hom.rev {σ : V → V'} {X Y : Paths $ Quiver.Push σ} (f : X ⟶ Y) : Y ⟶ X :=
  f.reverse.asHom

@[simp]
lemma Hom.push_rev {X Y : V} (f : X ⟶ Y) : (Hom.push σ f).rev = Hom.push σ (inv f) := rfl

set_option quotPrecheck false in
  scoped infixl:100 " † " => Hom.push

/-- Two reduction steps possible: compose composable arrows, or drop identity arrows -/
inductive red.atomic_step : HomRel (Paths (Quiver.Push σ))
  /-- Pushing a composite is the same as composing the pushes -/
  | comp (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
      red.atomic_step (σ † f ≫ σ † g) (σ † (f ≫ g))
  /-- Pushing the id is the id path -/
  | id (X : V) :
      red.atomic_step (σ † 𝟙 X) (𝟙 $ (σ *).obj X) -- ugly

@[simp]
def red.step {X Y : Paths $ Quiver.Push σ} (p q : X ⟶ Y) :=
  Quotient.CompClosure (red.atomic_step σ) p q

abbrev red.step' (σ : V → V') {X Y : Paths $ Quiver.Push σ} (p q : X ⟶ Y) :=
  @red.step _ _ _ σ X Y p q

lemma red.atomic_step.reverse : {X Y : Paths $ Quiver.Push σ} → (f g : X ⟶ Y) →
  red.atomic_step σ f g → red.atomic_step σ f.rev g.rev
  | _, _, _, _, .comp X Y Z f g => by
    simp [Quiver.Push.of_obj, Quiver.Path.reverse, ←Prefunctor.map_reverse, reverse_eq_inv,
               inv_eq_inv, Quiver.Path.comp_nil, IsIso.inv_comp, Quiver.Hom.rev]
    apply red.atomic_step.comp
  | _, _, _, _, .id X => by
    simp only [Quiver.Push.of_obj, Quiver.Path.reverse, ←Prefunctor.map_reverse, reverse_eq_inv,
               inv_eq_inv, IsIso.inv_id, Quiver.Path.comp_nil, Quiver.Hom.rev]
    apply red.atomic_step.id X

/-- The underlying vertices of the Universal Groupoid -/
def _root_.CategoryTheory.Groupoid.UniversalGroupoid
  {V : Type u} [Groupoid V] {V' : Type u'} (σ : V → V') := Quotient (red.atomic_step σ)

instance : Category (UniversalGroupoid σ) := Quotient.category (red.atomic_step σ)

lemma red.step.reverse : {X Y : Paths $ Quiver.Push σ} → (p q : X ⟶ Y) →
    red.step σ p q → red.step σ (p.reverse) (q.reverse)
  | A, B, _, _, .intro f _ _ g hr => by
    convert Quotient.CompClosure.intro (g.rev) _ _ (f.rev) hr.reverse
    · simp
    · simp

lemma Quot_mk_self_comp_reverse {X} : ∀ {Y : Paths $ Quiver.Push σ} (p : X ⟶ Y),
    Quot.mk (red.step' σ) (p ≫ p.rev) = Quot.mk (red.step' σ) (𝟙 X)
  | _, .nil => by simp
  | _, .cons p ⟨e⟩ => by
    let pp := p.asHom
    let pr := Quiver.Hom.rev pp
    calc Quot.mk (red.step' σ) ((p.cons _).asHom ≫ Quiver.Hom.rev (p.cons ⟨e⟩).asHom)
       = Quot.mk _ (pp ≫ (σ † e) ≫ (σ † e).rev ≫ pr) := by
          congr 1
          simp only [Paths.of_obj, Quiver.Path.asHom, Quiver.Hom.rev, Quiver.Path.reverse,
                    Quiver.Hom.toPath,PathsPush_comp_eq, Prefunctor.comp_obj, Quiver.Push.of_obj,
                    Hom.push, Prefunctor.comp_map, Paths.of_map, Quiver.Path.comp_nil,
                    Quiver.Path.cons_comp, Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
          rfl
     _ = Quot.mk _ (pp ≫ ((σ † e) ≫ (σ † e).rev) ≫ pr) := by simp
     _ = Quot.mk _ (pp ≫ (σ † (𝟙 _)) ≫ pr) := by
          apply Quot.sound (Quotient.CompClosure.intro _ _ _ _ _)
          convert @red.atomic_step.comp _ _ _ σ _ _ _ e (inv e)
          simp only [inv_eq_inv, IsIso.hom_inv_id]
     _ = Quot.mk _ (pp ≫ 𝟙 _ ≫ pr) :=
          Quot.sound (Quotient.CompClosure.intro _ _ _ _ $ @red.atomic_step.id _ _ _ σ _)
     _ = Quot.mk _ (pp ≫ pr) := by
           simp only [Paths.of_obj, Quiver.Path.asHom, PathsPush_id_eq, Quiver.Hom.rev,
                      PathsPush_comp_eq, Quiver.Path.nil_comp]
     _ = Quot.mk _ (𝟙 _) := Quot_mk_self_comp_reverse p

lemma Quot_mk_reverse_comp_self {X Y : Paths $ Quiver.Push σ} (p : X ⟶ Y) :
    Quot.mk (red.step' σ) (p.rev ≫ p) = Quot.mk (red.step' σ) (𝟙 Y) := by
  simpa using Quot_mk_self_comp_reverse σ p.rev


/-- The inverse of an arrow in the Universal Groupoid -/
def Quot_inv {X Y : UniversalGroupoid σ} (f : X ⟶ Y) : Y ⟶ X :=
Quot.liftOn f
            (fun pp ↦ Quot.mk _ $ pp.rev)
            (fun _ _ con ↦ Quot.sound $ red.step.reverse σ _ _ con)

instance : Groupoid (UniversalGroupoid σ) :=
{ inv       := fun {X Y : UniversalGroupoid σ} (f : X ⟶ Y) ↦ Quot_inv σ f,
  inv_comp := fun p ↦ Quot.inductionOn p $ fun pp ↦ Quot_mk_reverse_comp_self σ pp,
  comp_inv := fun p ↦ Quot.inductionOn p $ fun pp ↦ Quot_mk_self_comp_reverse σ pp }

/-- The extension of `σ` to a functor -/
def extend : V ⥤ (UniversalGroupoid σ) where
  obj X := ⟨σ X⟩
  map f := Quot.mk _ (σ † f)
  map_id X := Quot.sound $ Quotient.CompClosure.of _ _ _ (red.atomic_step.id X)
  map_comp f g := Eq.symm $ Quot.sound $
    Quotient.CompClosure.of _ _ _ (red.atomic_step.comp _ _ _ f g)

/-- Get the original vertex. -/
abbrev as (x : UniversalGroupoid σ) : V' := x.as

lemma extend_eq : (extend σ).toPrefunctor =
  ((Quiver.Push.of σ) ⋙q Paths.of) ⋙q (Quotient.functor $ red.atomic_step σ).toPrefunctor := rfl

section ump

variable {V'' : Type _} [Groupoid V''] (θ : V ⥤ V'') (τ₀ : V' → V'') (hτ₀ : ∀ x, θ.obj x = τ₀ (σ x))

/--
Any functor `θ` from `V` to a Groupoid `V''` with `θ.obj` factoring through `σ`
defines a functor from `V'`.
 -/
noncomputable def lift : UniversalGroupoid σ ⥤ V'' :=
Quotient.lift _
  ( Paths.lift $ Quiver.Push.lift σ θ.toPrefunctor τ₀ hτ₀ )
  ( fun _ _ _ _ h => by
      dsimp only [Paths.lift, Quiver.Push.lift]
      induction h
      · dsimp [Quiver.Push.of, CategoryStruct.comp, CategoryStruct.id, Quiver.Hom.toPath]
        simp [Functor.map_comp, cast_cast, Category.id_comp, hτ₀]
      · dsimp [Quiver.Push.of, CategoryStruct.comp, CategoryStruct.id, Quiver.Hom.toPath]
        simp [Functor.map_id, cast_cast, Category.id_comp, hτ₀] )

lemma lift_spec_obj : (lift σ θ τ₀ hτ₀).obj = τ₀ ∘ (as σ) := rfl

lemma lift_spec_comp : extend σ ⋙ lift σ θ τ₀ hτ₀ = θ := by
  rw [Functor.toPrefunctor_ext,←Functor.toPrefunctor_comp, extend_eq]
  dsimp only [lift]
  rw [Prefunctor.comp_assoc, Functor.toPrefunctor_comp, Quotient.lift_spec,
      Prefunctor.comp_assoc, Paths.lift_spec, Quiver.Push.lift_comp]

lemma lift_unique (Φ : UniversalGroupoid σ ⥤ V'')
    (Φ₀ : Φ.obj = τ₀ ∘ (as σ)) (Φc : extend σ ⋙ Φ = θ) : Φ = lift σ θ τ₀ hτ₀ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  apply Quiver.Push.lift_unique
  · ext
    simp [Φ₀]
  · simpa only [Functor.toPrefunctor_ext, ←Functor.toPrefunctor_comp] using Φc

end ump

/-

section reduced_words

open Relation

variables {X Y : Paths $ Quiver.Push σ} (p q r : X ⟶ Y)

abbrev red.step_refl (p q : X ⟶ Y) : Prop := ReflGen (red.step σ) p q
abbrev red (p q : X ⟶ Y) : Prop := ReflTransGen (red.step σ) p q
abbrev red.symm (p q : X ⟶ Y) : Prop := Join (red σ) p q

lemma red_step_iff :
  red.atomic_step σ p q ↔
  (∃ (x z y : V) (f : x ⟶ z) (g : z ⟶ y) (xX : σ x = X) (yY : σ y = Y),
    q = (eq_to_hom xX.symm) ≫ (σ † (f ≫ g)) ≫ (eq_to_hom yY) ∧
    p = (eq_to_hom xX.symm) ≫ ((σ †  f) ≫ (σ †  g)) ≫ (eq_to_hom yY)) ∨
  (∃ (x : V) (xX : σ x = X) (XY : X = Y),
    q = eq_to_hom XY ∧
    p = (eq_to_hom xX.symm) ≫ ((σ *).map $ 𝟙 x).to_path ≫ (eq_to_hom $ xX.trans XY))  :=
begin
  split,
  {
    rintros (⟨x, z, y, f, g⟩|(x)),
    { left, use [x,z,y,f,g,rfl,rfl],
      dsimp [Quiver.Push.of, Quiver.hom.to_path],
      simp only [Category.comp_id, Category.id_comp, eq_self_iff_true, true_and], refl, },
    { right, use [x,rfl,rfl],
      dsimp [Quiver.Push.of, Quiver.hom.to_path],
      simp only [Category.comp_id, Category.id_comp, eq_self_iff_true, and_true], refl, }, },
  { rintros (⟨x, z, y, f, g, rfl, rfl, rfl, rfl⟩|⟨x, rfl, rfl, rfl, rfl⟩),
    { simp only [eq_to_hom_refl, Category.comp_id, Category.id_comp], constructor, },
    { constructor, }, },
end

lemma red.atomic_step_length (h : red.atomic_step σ p q) :
  p.length = q.length.succ := by { cases h; refl, }

lemma red.step_length (h : red.step σ p q ) : p.length = q.length.succ :=
begin
  cases h,
  simp only [Quiver.path.length_comp, Category_struct.comp, red.atomic_step_length σ _ _ h_h,
             nat.succ_add],
  refl,
end

lemma red.step_length_lt (h : red.step σ p q) : q.length < p.length := by
{ rw red.step_length σ p q h, exact lt_add_one (Quiver.path.length q), }

lemma red.step_not_nil (s t : X ⟶ X) : red.step σ s t → s ≠ Quiver.path.nil :=
begin
  rintro h, cases h, cases h_h;
  { rintro h,
    let := congr_arg (Quiver.path.length) h,
    simpa [Category_struct.comp] using this, },
end

section diamond_helper

open Quiver.path

lemma red.step_diamond_comp_comp :
∀ {a b : Paths $ Quiver.Push σ} {X Y Z : V} {X' Y' Z' : V}
  {pre : a ⟶ σ X} {f : X ⟶ Y} {g : Y ⟶ Z} {suf : σ Z ⟶ b}
  {pre' : a ⟶ σ X'} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {suf' : σ Z' ⟶ b},
  pre ≫ ((σ † f) ≫ (σ † g)) ≫ suf = pre' ≫ ((σ † f') ≫ (σ † g')) ≫ suf'
→ pre ≫ (σ † (f ≫ g)) ≫ suf = pre' ≫ (σ † (f' ≫ g')) ≫ suf' ∨
  ∃ p, red.step σ (pre ≫ (σ † (f ≫ g)) ≫ suf) p ∧
       red.step σ (pre' ≫ (σ † (f' ≫ g')) ≫ suf') p := sorry

lemma red.step_diamond_comp_nil : ∀ {a b : Paths $ Quiver.Push σ} {X Y Z W : V}
  {pre : a ⟶ σ X} {f : X ⟶ Y} {g : Y ⟶ Z} {suf : σ Z ⟶ b}
  {pre' : a ⟶ σ W} {suf' : σ W ⟶ b},
  pre ≫ ((σ † f) ≫ (σ † g)) ≫ suf = pre' ≫ (σ † 𝟙 W) ≫ suf'
→ ∃ p, red.step σ (pre ≫ (σ † (f ≫ g)) ≫ suf) p ∧
       red.step σ (pre' ≫ (𝟙 $ σ W) ≫ suf') p := sorry

lemma red.step_diamond_nil_nil : ∀ {a b : Paths $ Quiver.Push σ} {W W' : V}
  {pre : a ⟶ σ W} {suf : σ W ⟶ b}
  {pre' : a ⟶ σ W'} {suf' : σ W' ⟶ b},
  pre ≫ (σ † 𝟙 W) ≫ suf = pre' ≫ (σ † 𝟙 W') ≫ suf' →
  pre ≫ (𝟙 $ σ W) ≫ suf = pre' ≫ (𝟙 $ σ W') ≫ suf' ∨
  ∃ p, red.step σ (pre ≫ (𝟙 $ σ _) ≫ suf) p ∧
       red.step σ (pre' ≫ (𝟙 $ σ _) ≫ suf') p :=
begin
  rintros a b W W' pre suf pre' suf',
  induction' pre,
end

end diamond_helper

lemma diamond : ∀ {X Y} (r p q : X ⟶ Y),
  red.step σ r p → red.step σ r q → p = q ∨ ∃ s, red.step σ p s ∧ red.step σ q s :=
begin
  rintro X Y r p q ⟨ap,bp,prep,mp,mp',sufp,hp⟩ rq,
  induction' rq with aq bq preq mq mq' sufq hq,
  induction' hp,
  { induction' hq,
    { obtain e|⟨h,r⟩ := red.step_diamond_comp_comp σ induction_eq_4,
      { left, exact e.symm, },
      { right, exact ⟨h,r.symm⟩, }, },
    { right, exact red.step_diamond_comp_nil σ induction_eq_4.symm, }, },
  { induction' hq,
    { right,
      obtain ⟨h,l,r⟩:= red.step_diamond_comp_nil σ induction_eq_4,
      exact ⟨h,r,l⟩, },
    { obtain e|⟨h,r,l⟩ := red.step_diamond_nil_nil σ induction_eq_4,
      { left, exact e.symm, },
      { right, exact ⟨h,l,r⟩, }, }  },
end

lemma diamond' : red.step σ r p → red.step σ r q → ∃ s, red.step_refl σ p s ∧ red σ q s :=
begin
  rintro pq pr,
  rcases diamond σ _ _ _ pq pr with (rfl|⟨s,qs,rs⟩),
  { use p, split, constructor, constructor, },
  { exact ⟨s,refl_gen.single qs,refl_trans_gen.single rs⟩, },
end

lemma church_rosser : red σ r p → red σ r q → ∃ s, red σ p s ∧ red σ q s :=
begin
  refine church_rosser _,
  rintro p q r pq pr,
  exact diamond' σ _ _ _ pq pr,
end

def is_reduced := ¬ ∃ (q : X ⟶ Y), red.step σ p q

lemma red.equal_of_is_reduced : red σ p q → is_reduced σ p → p = q :=
begin
  rintro pq pred,
  rcases pq.cases_head with (rfl|⟨r,pr,rq⟩),
  { refl, },
  { apply (pred ⟨r,pr⟩).elim, },
end

-- maybe should be done using `wf.fix` ?
 lemma red.exists_is_reduced : ∀ (p : X ⟶ Y), ∃ (r : X ⟶ Y), (red σ p r ∧ is_reduced σ r)
| p := if h : is_reduced σ p then ⟨p, by {apply refl_trans_gen.refl}, h⟩ else by
  { dsimp [is_reduced] at h, push_neg at h,
    obtain ⟨q,qp⟩ := h,
    let : q.length < p.length := red.step_length_lt σ p q qp, -- hint for well-foundedness
    obtain ⟨r, rq, rred⟩ := red.exists_is_reduced q,
    refine ⟨r, _, rred⟩,
    exact refl_trans_gen.trans (refl_trans_gen.single qp) rq, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (f : X ⟶ Y), f.length)⟩] }

lemma red.unique_reduced : red σ p q → red σ p r → is_reduced σ q → is_reduced σ r → q = r :=
begin
  rintros pq pr qred rred,
  obtain ⟨s,qs,rs⟩ := church_rosser σ _ _ _ pq pr,
  rcases qs.cases_head with (rfl|⟨t,qt,ts⟩);
  rcases rs.cases_head with (rfl|⟨u,ru,us⟩),
  { refl, },
  { apply (rred ⟨u,ru⟩).elim, },
  { apply (qred ⟨t,qt⟩).elim, },
  { apply (qred ⟨t,qt⟩).elim, },
end

lemma red.symm_of_eqv_gen : eqv_gen (red.step σ) p q → red.symm  σ p q :=
begin
  rintro h,
  have equiv : _root_.equivalence (@red.symm  _ _ _ σ X Y) :=
    equivalence_join_refl_trans_gen (λ a b c, diamond' σ _ _ _),
  have le : ∀ (f g : X ⟶ Y), red.step σ f g → red.symm  σ f g := λ f g h',
    join_of_single reflexive_refl_trans_gen (refl_trans_gen.single h'),
  let h' := eqv_gen.mono le h,
  rw (equivalence.eqv_gen_eq equiv) at h',
  exact h',
end

lemma red.eqv_gen : red σ p q → eqv_gen (red.step σ) p q :=
begin
  rintro h,
  induction h with _ _ _ r ih,
  { apply eqv_gen.refl p, },
  { apply eqv_gen.trans, exact ih, apply eqv_gen.rel, exact r, },
end

lemma unique_reduced' : eqv_gen (red.step σ) p q → is_reduced σ p → is_reduced σ q → p = q :=
begin
  rintro h pred qred,
  have h' : red.symm  σ p q := red.symm_of_eqv_gen σ p q h,
  rcases h' with ⟨d,pd,qd⟩,
  rw [red.equal_of_is_reduced σ _ _ pd pred, red.equal_of_is_reduced σ _ _ qd qred],
end

lemma unique_reduced {X Y : UniversalGroupoid σ} (p : X ⟶ Y) :
  ∃! (f : X.as ⟶ Y.as), is_reduced σ f ∧ quot.mk _ f = p :=
begin
  apply quot.induction_on p,
  rintro f, apply exists_unique_of_exists_of_unique,
  { let g := (red.exists_is_reduced σ f).some,
    obtain ⟨fg, gred⟩ := (red.exists_is_reduced σ f).some_spec,
    refine ⟨g,gred,_⟩,
    apply quot.eqv_gen_sound,
    apply eqv_gen.symm,
    apply red.eqv_gen,
    exact fg, },
  { rintros g h ⟨gred,geq⟩ ⟨hred,heq⟩,
    have := quot.exact _ (geq.trans heq.symm),
    exact unique_reduced' σ g h this gred hred, },
end

lemma push_arrow_red {x y : V} (f : x ⟶ y) :
  (∃ q, red.step σ (σ † f) q) → (∃ h : x = y, f = eq_to_hom h) :=
begin
  rintro ⟨q,fq⟩,
  induction' fq,
  induction' h;
  simp [Quiver.hom.to_path, Category_struct.comp, Quiver.path.comp] at induction_eq_4;
  let := congr_arg Quiver.path.length induction_eq_4;
  simp [Quiver.path.length_cons] at this,
  { sorry, /- `this` is impossible -/ },
  { sorry,/- the equality of length should force `f` to be nil-/}
end

lemma push_arrow_is_reduced {x y : V} (f : x ⟶ y) (hf : ¬ ∃ h : x = y, f = eq_to_hom h) :
  is_reduced σ (σ † f) :=
begin
  rintro ⟨q,fq⟩,
  let := red.step_length σ _ _ fq,
  simp [Quiver.hom.to_path, Quiver.path.length, nat.succ_eq_one_add] at this,
  let := Quiver.path.nil_of_length_zero _ this,

  induction fq with a b pre p q suf rs,
  rw red_step_iff at rs,
  rcases rs with ⟨a,b,c,d,e,f,g,h,i⟩|⟨a,b,c,d,e⟩,
  { sorry, },
  { sorry, },
end


end reduced_words

lemma of_very_faithful {x y z w : V} (p : x ⟶ y) (q : z ⟶ w)
  (xz : (extend σ).obj x = (extend σ).obj z) (yw : (extend σ).obj y = (extend σ).obj w) :
  (extend σ).map p ≫ (eq_to_hom yw) = (eq_to_hom xz) ≫ (extend σ).map q →
  ∃ (h : x = y) (k : z = w) (l : x = y), p = eq_to_hom h ∧ q = eq_to_hom k :=
begin
  intro he,
  by_contra, push_neg at h, sorry
end
-/
end Universal
end Groupoid
end CategoryTheory
