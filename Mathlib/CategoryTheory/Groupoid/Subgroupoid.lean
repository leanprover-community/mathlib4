/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Order.GaloisConnection

#align_import category_theory.groupoid.subgroupoid from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Subgroupoid

This file defines subgroupoids as `structure`s containing the subsets of arrows and their
stability under composition and inversion.
Also defined are:

* containment of subgroupoids is a complete lattice;
* images and preimages of subgroupoids under a functor;
* the notion of normality of subgroupoids and its stability under intersection and preimage;
* compatibility of the above with `CategoryTheory.Groupoid.vertexGroup`.


## Main definitions

Given a type `C` with associated `groupoid C` instance.

* `CategoryTheory.Subgroupoid C` is the type of subgroupoids of `C`
* `CategoryTheory.Subgroupoid.IsNormal` is the property that the subgroupoid is stable under
  conjugation by arbitrary arrows, _and_ that all identity arrows are contained in the subgroupoid.
* `CategoryTheory.Subgroupoid.comap` is the "preimage" map of subgroupoids along a functor.
* `CategoryTheory.Subgroupoid.map` is the "image" map of subgroupoids along a functor _injective on
  objects_.
* `CategoryTheory.Subgroupoid.vertexSubgroup` is the subgroup of the `vertex group` at a given
  vertex `v`, assuming `v` is contained in the `CategoryTheory.Subgroupoid` (meaning, by definition,
  that the arrow `𝟙 v` is contained in the subgroupoid).

## Implementation details

The structure of this file is copied from/inspired by `Mathlib/GroupTheory/Subgroup/Basic.lean`
and `Mathlib/Combinatorics/SimpleGraph/Subgraph.lean`.

## TODO

* Equivalent inductive characterization of generated (normal) subgroupoids.
* Characterization of normal subgroupoids as kernels.
* Prove that `CategoryTheory.Subgroupoid.full` and `CategoryTheory.Subgroupoid.disconnect` preserve
  intersections (and `CategoryTheory.Subgroupoid.disconnect` also unions)

## Tags

category theory, groupoid, subgroupoid
-/


namespace CategoryTheory

open Set Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- A sugroupoid of `C` consists of a choice of arrows for each pair of vertices, closed
under composition and inverses.
-/
@[ext]
structure Subgroupoid (C : Type u) [Groupoid C] where
  arrows : ∀ c d : C, Set (c ⟶ d)
  protected inv : ∀ {c d} {p : c ⟶ d}, p ∈ arrows c d → Groupoid.inv p ∈ arrows d c
  protected mul : ∀ {c d e} {p}, p ∈ arrows c d → ∀ {q}, q ∈ arrows d e → p ≫ q ∈ arrows c e
#align category_theory.subgroupoid CategoryTheory.Subgroupoid

namespace Subgroupoid

variable (S : Subgroupoid C)

theorem inv_mem_iff {c d : C} (f : c ⟶ d) :
    Groupoid.inv f ∈ S.arrows d c ↔ f ∈ S.arrows c d := by
  constructor
  -- ⊢ Groupoid.inv f ∈ arrows S d c → f ∈ arrows S c d
  · intro h
    -- ⊢ f ∈ arrows S c d
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
    -- 🎉 no goals
  · apply S.inv
    -- 🎉 no goals
#align category_theory.subgroupoid.inv_mem_iff CategoryTheory.Subgroupoid.inv_mem_iff

theorem mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f ∈ S.arrows c d) :
    f ≫ g ∈ S.arrows c e ↔ g ∈ S.arrows d e := by
  constructor
  -- ⊢ f ≫ g ∈ arrows S c e → g ∈ arrows S d e
  · rintro h
    -- ⊢ g ∈ arrows S d e
    suffices Groupoid.inv f ≫ f ≫ g ∈ S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    · apply S.mul (S.inv hf) h
      -- 🎉 no goals
  · apply S.mul hf
    -- 🎉 no goals
#align category_theory.subgroupoid.mul_mem_cancel_left CategoryTheory.Subgroupoid.mul_mem_cancel_left

theorem mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g ∈ S.arrows d e) :
    f ≫ g ∈ S.arrows c e ↔ f ∈ S.arrows c d := by
  constructor
  -- ⊢ f ≫ g ∈ arrows S c e → f ∈ arrows S c d
  · rintro h
    -- ⊢ f ∈ arrows S c d
    suffices (f ≫ g) ≫ Groupoid.inv g ∈ S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    · apply S.mul h (S.inv hg)
      -- 🎉 no goals
  · exact fun hf => S.mul hf hg
    -- 🎉 no goals
#align category_theory.subgroupoid.mul_mem_cancel_right CategoryTheory.Subgroupoid.mul_mem_cancel_right

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def objs : Set C :=
  {c : C | (S.arrows c c).Nonempty}
#align category_theory.subgroupoid.objs CategoryTheory.Subgroupoid.objs

theorem mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : c ∈ S.objs :=
  ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩
#align category_theory.subgroupoid.mem_objs_of_src CategoryTheory.Subgroupoid.mem_objs_of_src

theorem mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : d ∈ S.objs :=
  ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩
#align category_theory.subgroupoid.mem_objs_of_tgt CategoryTheory.Subgroupoid.mem_objs_of_tgt

theorem id_mem_of_nonempty_isotropy (c : C) : c ∈ objs S → 𝟙 c ∈ S.arrows c c := by
  rintro ⟨γ, hγ⟩
  -- ⊢ 𝟙 c ∈ arrows S c c
  convert S.mul hγ (S.inv hγ)
  -- ⊢ 𝟙 c = γ ≫ Groupoid.inv γ
  simp only [inv_eq_inv, IsIso.hom_inv_id]
  -- 🎉 no goals
#align category_theory.subgroupoid.id_mem_of_nonempty_isotropy CategoryTheory.Subgroupoid.id_mem_of_nonempty_isotropy

theorem id_mem_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 c ∈ S.arrows c c :=
  id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)
#align category_theory.subgroupoid.id_mem_of_src CategoryTheory.Subgroupoid.id_mem_of_src

theorem id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 d ∈ S.arrows d d :=
  id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)
#align category_theory.subgroupoid.id_mem_of_tgt CategoryTheory.Subgroupoid.id_mem_of_tgt

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def asWideQuiver : Quiver C :=
  ⟨fun c d => Subtype <| S.arrows c d⟩
#align category_theory.subgroupoid.as_wide_quiver CategoryTheory.Subgroupoid.asWideQuiver

/-- The coercion of a subgroupoid as a groupoid -/
@[simps comp_coe, simps (config := .lemmasOnly) inv_coe]
instance coe : Groupoid S.objs where
  Hom a b := S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩
#align category_theory.subgroupoid.coe CategoryTheory.Subgroupoid.coe

@[simp]
theorem coe_inv_coe' {c d : S.objs} (p : c ⟶ d) :
    (CategoryTheory.inv p).val = CategoryTheory.inv p.val := by
  simp only [← inv_eq_inv, coe_inv_coe]
  -- 🎉 no goals
#align category_theory.subgroupoid.coe_inv_coe' CategoryTheory.Subgroupoid.coe_inv_coe'

/-- The embedding of the coerced subgroupoid to its parent-/
def hom : S.objs ⥤ C where
  obj c := c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl
#align category_theory.subgroupoid.hom CategoryTheory.Subgroupoid.hom

theorem hom.inj_on_objects : Function.Injective (hom S).obj := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  -- ⊢ { val := c, property := hc } = { val := d, property := hd }
  simp only [Subtype.mk_eq_mk]; exact hcd
  -- ⊢ c = d
                                -- 🎉 no goals
#align category_theory.subgroupoid.hom.inj_on_objects CategoryTheory.Subgroupoid.hom.inj_on_objects

theorem hom.faithful : ∀ c d, Function.Injective fun f : c ⟶ d => (hom S).map f := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.eq hfg
  -- ⊢ { val := f, property := hf } = { val := g, property := hg }
                                              -- 🎉 no goals
#align category_theory.subgroupoid.hom.faithful CategoryTheory.Subgroupoid.hom.faithful

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertexSubgroup {c : C} (hc : c ∈ S.objs) : Subgroup (c ⟶ c) where
  carrier := S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf
#align category_theory.subgroupoid.vertex_subgroup CategoryTheory.Subgroupoid.vertexSubgroup

/-- The set of all arrows of a subgroupoid, as a set in `Σ c d : C, c ⟶ d`. -/
@[coe] def toSet (S : Subgroupoid C) : Set (Σ c d : C, c ⟶ d) :=
  {F | F.2.2 ∈ S.arrows F.1 F.2.1}

instance : SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d) where
  coe := toSet
  coe_injective' := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩
                                                    -- ⊢ f ∈ arrows { arrows := S, inv := inv✝¹, mul := mul✝¹ } c d ↔ f ∈ arrows { ar …
                                                               -- 🎉 no goals

theorem mem_iff (S : Subgroupoid C) (F : Σ c d, c ⟶ d) : F ∈ S ↔ F.2.2 ∈ S.arrows F.1 F.2.1 :=
  Iff.rfl
#align category_theory.subgroupoid.mem_iff CategoryTheory.Subgroupoid.mem_iff

theorem le_iff (S T : Subgroupoid C) : S ≤ T ↔ ∀ {c d}, S.arrows c d ⊆ T.arrows c d := by
  rw [SetLike.le_def, Sigma.forall]; exact forall_congr' fun c => Sigma.forall
  -- ⊢ (∀ (a : C) (b : (d : C) × (a ⟶ d)), { fst := a, snd := b } ∈ S → { fst := a, …
                                     -- 🎉 no goals
#align category_theory.subgroupoid.le_iff CategoryTheory.Subgroupoid.le_iff

instance : Top (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => Set.univ
      mul := by intros; trivial
                -- ⊢ p✝ ≫ q✝ ∈ (fun x x_1 => univ) c✝ e✝
                -- ⊢ Groupoid.inv p✝ ∈ (fun x x_1 => univ) d✝ c✝
                        -- 🎉 no goals
                        -- 🎉 no goals
      inv := by intros; trivial }⟩

theorem mem_top {c d : C} (f : c ⟶ d) : f ∈ (⊤ : Subgroupoid C).arrows c d :=
  trivial
#align category_theory.subgroupoid.mem_top CategoryTheory.Subgroupoid.mem_top

theorem mem_top_objs (c : C) : c ∈ (⊤ : Subgroupoid C).objs := by
  dsimp [Top.top, objs]
  -- ⊢ Set.Nonempty univ
  simp only [univ_nonempty]
  -- 🎉 no goals
#align category_theory.subgroupoid.mem_top_objs CategoryTheory.Subgroupoid.mem_top_objs

instance : Bot (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩

instance : Inhabited (Subgroupoid C) :=
  ⟨⊤⟩

instance : Inf (Subgroupoid C) :=
  ⟨fun S T =>
    { arrows := fun c d => S.arrows c d ∩ T.arrows c d
      inv := fun hp ↦ ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq ↦ ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

instance : InfSet (Subgroupoid C) :=
  ⟨fun s =>
    { arrows := fun c d => ⋂ S ∈ s, Subgroupoid.arrows S c d
      inv := fun hp ↦ by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
                         -- ⊢ ∀ (i : Subgroupoid C), i ∈ s → Groupoid.inv p✝ ∈ arrows i d✝ c✝
                                                   -- 🎉 no goals
      mul := fun hp _ hq ↦ by
        rw [mem_iInter₂] at hp hq ⊢;
        -- ⊢ ∀ (i : Subgroupoid C), i ∈ s → p✝ ≫ x✝ ∈ arrows i c✝ e✝
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩
        -- 🎉 no goals

-- porting note: new lemma
theorem mem_sInf_arrows {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d} :
    p ∈ (sInf s).arrows c d ↔ ∀ S ∈ s, p ∈ S.arrows c d :=
  mem_iInter₂

theorem mem_sInf {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d} :
    p ∈ sInf s ↔ ∀ S ∈ s, p ∈ S :=
  mem_sInf_arrows

instance : CompleteLattice (Subgroupoid C) :=
  { completeLatticeOfInf (Subgroupoid C) (by
      refine' fun s => ⟨fun S Ss F => _, fun T Tl F fT => _⟩ <;> simp only [mem_sInf]
      -- ⊢ F ∈ sInf s → F ∈ S
                                                                 -- ⊢ (∀ (S : Subgroupoid C), S ∈ s → F ∈ S) → F ∈ S
                                                                 -- ⊢ ∀ (S : Subgroupoid C), S ∈ s → F ∈ S
      exacts [fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
      -- 🎉 no goals
    bot := ⊥
    bot_le := fun S => empty_subset _
    top := ⊤
    le_top := fun S => subset_univ _
    inf := (· ⊓ ·)
    le_inf := fun R S T RS RT _ pR => ⟨RS pR, RT pR⟩
    inf_le_left := fun R S _ => And.left
    inf_le_right := fun R S _ => And.right }

theorem le_objs {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⊆ T.objs := fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩
#align category_theory.subgroupoid.le_objs CategoryTheory.Subgroupoid.le_objs

/-- The functor associated to the embedding of subgroupoids -/
def inclusion {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⥤ T.objs where
  obj s := ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl
#align category_theory.subgroupoid.inclusion CategoryTheory.Subgroupoid.inclusion

theorem inclusion_inj_on_objects {S T : Subgroupoid C} (h : S ≤ T) :
    Function.Injective (inclusion h).obj := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id
  -- 🎉 no goals
#align category_theory.subgroupoid.inclusion_inj_on_objects CategoryTheory.Subgroupoid.inclusion_inj_on_objects

theorem inclusion_faithful {S T : Subgroupoid C} (h : S ≤ T) (s t : S.objs) :
    Function.Injective fun f : s ⟶ t => (inclusion h).map f := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id
  -- ⊢ { val := f, property := (_ : { fst := ↑s, snd := { fst := ↑t, snd := ↑{ val  …
                          -- ⊢ f = g → f = g
                                                                   -- 🎉 no goals
#align category_theory.subgroupoid.inclusion_faithful CategoryTheory.Subgroupoid.inclusion_faithful

theorem inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _
#align category_theory.subgroupoid.inclusion_refl CategoryTheory.Subgroupoid.inclusion_refl

theorem inclusion_trans {R S T : Subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
    inclusion (k.trans h) = inclusion k ⋙ inclusion h :=
  rfl
#align category_theory.subgroupoid.inclusion_trans CategoryTheory.Subgroupoid.inclusion_trans

theorem inclusion_comp_embedding {S T : Subgroupoid C} (h : S ≤ T) : inclusion h ⋙ T.hom = S.hom :=
  rfl
#align category_theory.subgroupoid.inclusion_comp_embedding CategoryTheory.Subgroupoid.inclusion_comp_embedding

/-- The family of arrows of the discrete groupoid -/
inductive Discrete.Arrows : ∀ c d : C, (c ⟶ d) → Prop
  | id (c : C) : Discrete.Arrows c c (𝟙 c)
#align category_theory.subgroupoid.discrete.arrows CategoryTheory.Subgroupoid.Discrete.Arrows

/-- The only arrows of the discrete groupoid are the identity arrows. -/
def discrete : Subgroupoid C where
  arrows c d := {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
            -- ⊢ Groupoid.inv (𝟙 c✝) ∈ (fun c d => {p | Discrete.Arrows c d p}) c✝ c✝
                             -- ⊢ 𝟙 c✝ ∈ {p | Discrete.Arrows c✝ c✝ p}
                                                                   -- 🎉 no goals
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor
            -- ⊢ 𝟙 c✝ ≫ 𝟙 c✝ ∈ (fun c d => {p | Discrete.Arrows c d p}) c✝ c✝
                                    -- ⊢ 𝟙 c✝ ∈ (fun c d => {p | Discrete.Arrows c d p}) c✝ c✝
                                                           -- 🎉 no goals
#align category_theory.subgroupoid.discrete CategoryTheory.Subgroupoid.discrete

theorem mem_discrete_iff {c d : C} (f : c ⟶ d) :
    f ∈ discrete.arrows c d ↔ ∃ h : c = d, f = eqToHom h :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩
      -- ⊢ ∃ h, 𝟙 c = eqToHom h
                 -- 🎉 no goals
                                      -- ⊢ eqToHom (_ : c = c) ∈ arrows discrete c c
                                                         -- 🎉 no goals
#align category_theory.subgroupoid.mem_discrete_iff CategoryTheory.Subgroupoid.mem_discrete_iff

/-- A subgroupoid is wide if its carrier set is all of `C`-/
structure IsWide : Prop where
  wide : ∀ c, 𝟙 c ∈ S.arrows c c
#align category_theory.subgroupoid.is_wide CategoryTheory.Subgroupoid.IsWide

theorem isWide_iff_objs_eq_univ : S.IsWide ↔ S.objs = Set.univ := by
  constructor
  -- ⊢ IsWide S → objs S = univ
  · rintro h
    -- ⊢ objs S = univ
    ext x; constructor <;> simp only [top_eq_univ, mem_univ, imp_true_iff, forall_true_left]
    -- ⊢ x ∈ objs S ↔ x ∈ univ
           -- ⊢ x ∈ objs S → x ∈ univ
                           -- 🎉 no goals
                           -- ⊢ x ∈ objs S
    apply mem_objs_of_src S (h.wide x)
    -- 🎉 no goals
  · rintro h
    -- ⊢ IsWide S
    refine' ⟨fun c => _⟩
    -- ⊢ 𝟙 c ∈ arrows S c c
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ ⊆ S.objs) (Set.mem_univ c)
    -- ⊢ 𝟙 c ∈ arrows S c c
    exact id_mem_of_src S γS
    -- 🎉 no goals
#align category_theory.subgroupoid.is_wide_iff_objs_eq_univ CategoryTheory.Subgroupoid.isWide_iff_objs_eq_univ

theorem IsWide.id_mem {S : Subgroupoid C} (Sw : S.IsWide) (c : C) : 𝟙 c ∈ S.arrows c c :=
  Sw.wide c
#align category_theory.subgroupoid.is_wide.id_mem CategoryTheory.Subgroupoid.IsWide.id_mem

theorem IsWide.eqToHom_mem {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d) :
    eqToHom h ∈ S.arrows c d := by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c
                                   -- ⊢ eqToHom (_ : c = c) ∈ arrows S c c
                                            -- ⊢ 𝟙 c ∈ arrows S c c
                                                                      -- 🎉 no goals
#align category_theory.subgroupoid.is_wide.eq_to_hom_mem CategoryTheory.Subgroupoid.IsWide.eqToHom_mem

/-- A subgroupoid is normal if it is wide and satisfies the expected stability under conjugacy. -/
structure IsNormal extends IsWide S : Prop where
  conj : ∀ {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ ∈ S.arrows c c → Groupoid.inv p ≫ γ ≫ p ∈ S.arrows d d
#align category_theory.subgroupoid.is_normal CategoryTheory.Subgroupoid.IsNormal

theorem IsNormal.conj' {S : Subgroupoid C} (Sn : IsNormal S) :
    ∀ {c d} (p : d ⟶ c) {γ : c ⟶ c}, γ ∈ S.arrows c c → p ≫ γ ≫ Groupoid.inv p ∈ S.arrows d d :=
  fun p γ hs => by convert Sn.conj (Groupoid.inv p) hs; simp
                   -- ⊢ p = Groupoid.inv (Groupoid.inv p)
                                                        -- 🎉 no goals
#align category_theory.subgroupoid.is_normal.conj' CategoryTheory.Subgroupoid.IsNormal.conj'

theorem IsNormal.conjugation_bij (Sn : IsNormal S) {c d} (p : c ⟶ d) :
    Set.BijOn (fun γ : c ⟶ c => Groupoid.inv p ≫ γ ≫ p) (S.arrows c c) (S.arrows d d) := by
  refine' ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => _, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, _⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc]
#align category_theory.subgroupoid.is_normal.conjugation_bij CategoryTheory.Subgroupoid.IsNormal.conjugation_bij

theorem top_isNormal : IsNormal (⊤ : Subgroupoid C) :=
  { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }
#align category_theory.subgroupoid.top_is_normal CategoryTheory.Subgroupoid.top_isNormal

theorem sInf_isNormal (s : Set <| Subgroupoid C) (sn : ∀ S ∈ s, IsNormal S) : IsNormal (sInf s) :=
  { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
               -- ⊢ ∀ (c : C) (i : Subgroupoid C), i ∈ s → 𝟙 c ∈ arrows i c c
                                            -- 🎉 no goals
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }
               -- ⊢ ∀ {c d : C} (p : c ⟶ d) {γ : c ⟶ c}, (∀ (i : Subgroupoid C), i ∈ s → γ ∈ arr …
                                            -- 🎉 no goals
#align category_theory.subgroupoid.Inf_is_normal CategoryTheory.Subgroupoid.sInf_isNormal

theorem discrete_isNormal : (@discrete C _).IsNormal :=
  { wide := fun c => by constructor
                        -- 🎉 no goals
    conj := fun f γ hγ => by
      cases hγ
      -- ⊢ Groupoid.inv f ≫ 𝟙 c✝ ≫ f ∈ arrows discrete d✝ d✝
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }
      -- ⊢ 𝟙 d✝ ∈ arrows discrete d✝ d✝
                                                                  -- 🎉 no goals
#align category_theory.subgroupoid.discrete_is_normal CategoryTheory.Subgroupoid.discrete_isNormal

theorem IsNormal.vertexSubgroup (Sn : IsNormal S) (c : C) (cS : c ∈ S.objs) :
    (S.vertexSubgroup cS).Normal where
  conj_mem x hx y := by rw [mul_assoc]; exact Sn.conj' y hx
                        -- ⊢ y * (x * y⁻¹) ∈ Subgroupoid.vertexSubgroup S cS
                                        -- 🎉 no goals
#align category_theory.subgroupoid.is_normal.vertex_subgroup CategoryTheory.Subgroupoid.IsNormal.vertexSubgroup

section GeneratedSubgroupoid

-- TODO: proof that generated is just "words in X" and generatedNormal is similarly
variable (X : ∀ c d : C, Set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : Subgroupoid C :=
  sInf {S : Subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}
#align category_theory.subgroupoid.generated CategoryTheory.Subgroupoid.generated

theorem subset_generated (c d : C) : X c d ⊆ (generated X).arrows c d := by
  dsimp only [generated, sInf]
  -- ⊢ X c d ⊆ ⋂ (S : Subgroupoid C) (_ : S ∈ {S | ∀ (c d : C), X c d ⊆ arrows S c  …
  simp only [subset_iInter₂_iff]
  -- ⊢ ∀ (i : Subgroupoid C), i ∈ {S | ∀ (c d : C), X c d ⊆ arrows S c d} → X c d ⊆ …
  exact fun S hS f fS => hS _ _ fS
  -- 🎉 no goals
#align category_theory.subgroupoid.subset_generated CategoryTheory.Subgroupoid.subset_generated

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generatedNormal : Subgroupoid C :=
  sInf {S : Subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.IsNormal}
#align category_theory.subgroupoid.generated_normal CategoryTheory.Subgroupoid.generatedNormal

theorem generated_le_generatedNormal : generated X ≤ generatedNormal X := by
  apply @sInf_le_sInf (Subgroupoid C) _
  -- ⊢ {S | (∀ (c d : C), X c d ⊆ arrows S c d) ∧ IsNormal S} ⊆ {S | ∀ (c d : C), X …
  exact fun S ⟨h, _⟩ => h
  -- 🎉 no goals
#align category_theory.subgroupoid.generated_le_generated_normal CategoryTheory.Subgroupoid.generated_le_generatedNormal

theorem generatedNormal_isNormal : (generatedNormal X).IsNormal :=
  sInf_isNormal _ fun _ h => h.right
#align category_theory.subgroupoid.generated_normal_is_normal CategoryTheory.Subgroupoid.generatedNormal_isNormal

theorem IsNormal.generatedNormal_le {S : Subgroupoid C} (Sn : S.IsNormal) :
    generatedNormal X ≤ S ↔ ∀ c d, X c d ⊆ S.arrows c d := by
  constructor
  -- ⊢ generatedNormal X ≤ S → ∀ (c d : C), X c d ⊆ arrows S c d
  · rintro h c d
    -- ⊢ X c d ⊆ arrows S c d
    have h' := generated_le_generatedNormal X
    -- ⊢ X c d ⊆ arrows S c d
    rw [le_iff] at h h'
    -- ⊢ X c d ⊆ arrows S c d
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
    -- 🎉 no goals
  · rintro h
    -- ⊢ generatedNormal X ≤ S
    apply @sInf_le (Subgroupoid C) _
    -- ⊢ S ∈ {S | (∀ (c d : C), X c d ⊆ arrows S c d) ∧ IsNormal S}
    exact ⟨h, Sn⟩
    -- 🎉 no goals
#align category_theory.subgroupoid.is_normal.generated_normal_le CategoryTheory.Subgroupoid.IsNormal.generatedNormal_le

end GeneratedSubgroupoid

section Hom

variable {D : Type*} [Groupoid D] (φ : C ⥤ D)

/-- A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/
def comap (S : Subgroupoid D) : Subgroupoid C where
  arrows c d := {f : c ⟶ d | φ.map f ∈ S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_setOf, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
               -- ⊢ Groupoid.inv (φ.map p✝) ∈ arrows S (φ.obj d✝) (φ.obj c✝)
                                                                    -- 🎉 no goals
  mul := by
    intros
    -- ⊢ p✝ ≫ q✝ ∈ (fun c d => {f | φ.map f ∈ arrows S (φ.obj c) (φ.obj d)}) c✝ e✝
    simp only [mem_setOf, Functor.map_comp]
    -- ⊢ φ.map p✝ ≫ φ.map q✝ ∈ arrows S (φ.obj c✝) (φ.obj e✝)
    apply S.mul <;> assumption
    -- ⊢ φ.map p✝ ∈ arrows S (φ.obj c✝) (φ.obj d✝)
                    -- 🎉 no goals
                    -- 🎉 no goals
#align category_theory.subgroupoid.comap CategoryTheory.Subgroupoid.comap

theorem comap_mono (S T : Subgroupoid D) : S ≤ T → comap φ S ≤ comap φ T := fun ST _ =>
  @ST ⟨_, _, _⟩
#align category_theory.subgroupoid.comap_mono CategoryTheory.Subgroupoid.comap_mono

theorem isNormal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S) where
  wide c := by rw [comap, mem_setOf, Functor.map_id]; apply Sn.wide
               -- ⊢ 𝟙 (φ.obj c) ∈ arrows S (φ.obj c) (φ.obj c)
                                                      -- 🎉 no goals
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_setOf, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    -- ⊢ Groupoid.inv (φ.map f) ≫ φ.map γ ≫ φ.map f ∈ arrows S (φ.obj d✝) (φ.obj d✝)
    exact Sn.conj _ hγ
    -- 🎉 no goals
#align category_theory.subgroupoid.is_normal_comap CategoryTheory.Subgroupoid.isNormal_comap

@[simp]
theorem comap_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ ∘ comap ψ :=
  rfl
#align category_theory.subgroupoid.comap_comp CategoryTheory.Subgroupoid.comap_comp

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : Subgroupoid C :=
  comap φ discrete
#align category_theory.subgroupoid.ker CategoryTheory.Subgroupoid.ker

theorem mem_ker_iff {c d : C} (f : c ⟶ d) :
    f ∈ (ker φ).arrows c d ↔ ∃ h : φ.obj c = φ.obj d, φ.map f = eqToHom h :=
  mem_discrete_iff (φ.map f)
#align category_theory.subgroupoid.mem_ker_iff CategoryTheory.Subgroupoid.mem_ker_iff

theorem ker_isNormal : (ker φ).IsNormal :=
  isNormal_comap φ discrete_isNormal
#align category_theory.subgroupoid.ker_is_normal CategoryTheory.Subgroupoid.ker_isNormal

@[simp]
theorem ker_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) :=
  rfl
#align category_theory.subgroupoid.ker_comp CategoryTheory.Subgroupoid.ker_comp

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive Map.Arrows (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : ∀ c d : D, (c ⟶ d) → Prop
  | im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)
#align category_theory.subgroupoid.map.arrows CategoryTheory.Subgroupoid.Map.Arrows

theorem Map.arrows_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    Map.Arrows φ hφ S c d f ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  constructor
  -- ⊢ Arrows φ hφ S c d f → ∃ a b g ha hb _hg, f = eqToHom (_ : c = φ.obj a) ≫ φ.m …
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
    -- ⊢ ∃ a b g_1 ha hb _hg, φ.map g = eqToHom (_ : φ.obj c✝ = φ.obj a) ≫ φ.map g_1  …
                    -- 🎉 no goals
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg
    -- ⊢ Arrows φ hφ S (φ.obj a) (φ.obj b) (eqToHom (_ : φ.obj a = φ.obj a) ≫ φ.map g …
                                         -- ⊢ Arrows φ hφ S (φ.obj a) (φ.obj b) (φ.map g)
                                                                 -- ⊢ g ∈ arrows S a b
                                                                              -- 🎉 no goals
#align category_theory.subgroupoid.map.arrows_iff CategoryTheory.Subgroupoid.Map.arrows_iff

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  arrows c d := {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    -- ⊢ Groupoid.inv (φ.map f✝) ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj  …
    rw [inv_eq_inv, ← Functor.map_inv, ← inv_eq_inv]
    -- ⊢ φ.map (Groupoid.inv f✝) ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj  …
    constructor; apply S.inv; assumption
    -- ⊢ Groupoid.inv f✝ ∈ arrows S d✝ c✝
                 -- ⊢ f✝ ∈ arrows S c✝ d✝
                              -- 🎉 no goals
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    -- ⊢ φ.map f ≫ q ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj c✝) e✝
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    -- ⊢ φ.map f ≫ q ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj c✝) (φ.obj c₄)
    cases hφ he; rw [gq, ← eq_conj_eqToHom, ← φ.map_comp]
    -- ⊢ φ.map f ≫ q ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj c✝) (φ.obj c₄)
                 -- ⊢ φ.map (f ≫ g) ∈ (fun c d => {x | Map.Arrows φ hφ S c d x}) (φ.obj c✝) (φ.obj …
    constructor; exact S.mul hf hg
    -- ⊢ f ≫ g ∈ arrows S c✝ c₄
                 -- 🎉 no goals
#align category_theory.subgroupoid.map CategoryTheory.Subgroupoid.map

theorem mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    f ∈ (map φ hφ S).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  Map.arrows_iff φ hφ S f
#align category_theory.subgroupoid.mem_map_iff CategoryTheory.Subgroupoid.mem_map_iff

theorem galoisConnection_map_comap (hφ : Function.Injective φ.obj) :
    GaloisConnection (map φ hφ) (comap φ) := by
  rintro S T; simp_rw [le_iff]; constructor
  -- ⊢ map φ hφ S ≤ T ↔ S ≤ comap φ T
              -- ⊢ (∀ {c d : D}, arrows (map φ hφ S) c d ⊆ arrows T c d) ↔ ∀ {c d : C}, arrows  …
                                -- ⊢ (∀ {c d : D}, arrows (map φ hφ S) c d ⊆ arrows T c d) → ∀ {c d : C}, arrows  …
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
    -- 🎉 no goals
  · rintro h _ _ g ⟨a, gφS⟩
    -- ⊢ φ.map a ∈ arrows T (φ.obj c✝) (φ.obj d✝)
    exact h gφS
    -- 🎉 no goals
#align category_theory.subgroupoid.galois_connection_map_comap CategoryTheory.Subgroupoid.galoisConnection_map_comap

theorem map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) :
    S ≤ T → map φ hφ S ≤ map φ hφ T := fun h => (galoisConnection_map_comap φ hφ).monotone_l h
#align category_theory.subgroupoid.map_mono CategoryTheory.Subgroupoid.map_mono

theorem le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) :
    S ≤ comap φ (map φ hφ S) :=
  (galoisConnection_map_comap φ hφ).le_u_l S
#align category_theory.subgroupoid.le_comap_map CategoryTheory.Subgroupoid.le_comap_map

theorem map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) :
    map φ hφ (comap φ T) ≤ T :=
  (galoisConnection_map_comap φ hφ).l_u_le T
#align category_theory.subgroupoid.map_comap_le CategoryTheory.Subgroupoid.map_comap_le

theorem map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
    (T : Subgroupoid D) : map φ hφ S ≤ T ↔ S ≤ comap φ T :=
  (galoisConnection_map_comap φ hφ).le_iff_le
#align category_theory.subgroupoid.map_le_iff_le_comap CategoryTheory.Subgroupoid.map_le_iff_le_comap

theorem mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (map φ hφ S).objs ↔ ∃ c ∈ S.objs, φ.obj c = d := by
  dsimp [objs, map]
  -- ⊢ Set.Nonempty {x | Map.Arrows φ hφ S d d x} ↔ ∃ c, Set.Nonempty (arrows S c c …
  constructor
  -- ⊢ Set.Nonempty {x | Map.Arrows φ hφ S d d x} → ∃ c, Set.Nonempty (arrows S c c …
  · rintro ⟨f, hf⟩
    -- ⊢ ∃ c, Set.Nonempty (arrows S c c) ∧ φ.obj c = d
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    -- ⊢ ∃ c, Set.Nonempty (arrows S c c) ∧ φ.obj c = d
                                          -- ⊢ ∃ c, Set.Nonempty (arrows S c c) ∧ φ.obj c = d
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    -- ⊢ ∃ c, Set.Nonempty (arrows S c c) ∧ φ.obj c = d✝
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
    -- 🎉 no goals
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    -- ⊢ Set.Nonempty {x | Map.Arrows φ hφ S (φ.obj c) (φ.obj c) x}
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩
    -- 🎉 no goals
#align category_theory.subgroupoid.mem_map_objs_iff CategoryTheory.Subgroupoid.mem_map_objs_iff

@[simp]
theorem map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).objs = φ.obj '' S.objs := by
  ext x; convert mem_map_objs_iff S φ hφ x
  -- ⊢ x ∈ objs (map φ hφ S) ↔ x ∈ φ.obj '' objs S
         -- 🎉 no goals
#align category_theory.subgroupoid.map_objs_eq CategoryTheory.Subgroupoid.map_objs_eq

/-- The image of a functor injective on objects -/
def im (hφ : Function.Injective φ.obj) :=
  map φ hφ ⊤
#align category_theory.subgroupoid.im CategoryTheory.Subgroupoid.im

theorem mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) :
    f ∈ (im φ hφ).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  by convert Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]
     -- ⊢ f = eqToHom (_ : c = φ.obj x✝⁴) ≫ φ.map x✝² ≫ eqToHom x✝ ↔ ∃ _hg, f = eqToHo …
                                      -- 🎉 no goals
#align category_theory.subgroupoid.mem_im_iff CategoryTheory.Subgroupoid.mem_im_iff

theorem mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (im φ hφ).objs ↔ ∃ c : C, φ.obj c = d := by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]
  -- 🎉 no goals
#align category_theory.subgroupoid.mem_im_objs_iff CategoryTheory.Subgroupoid.mem_im_objs_iff

theorem obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) :
    Function.Surjective φ.obj := by
  rintro d
  -- ⊢ ∃ a, φ.obj a = d
  rw [← mem_im_objs_iff, hφ']
  -- ⊢ d ∈ objs ⊤
  apply mem_top_objs
  -- 🎉 no goals
#align category_theory.subgroupoid.obj_surjective_of_im_eq_top CategoryTheory.Subgroupoid.obj_surjective_of_im_eq_top

theorem isNormal_map (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal) :
    (map φ hφ S).IsNormal :=
  { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      -- ⊢ 𝟙 (φ.obj c) ∈ arrows (map φ hφ S) (φ.obj c) (φ.obj c)
      change Map.Arrows φ hφ S _ _ (𝟙 _); rw [← Functor.map_id]
      -- ⊢ Map.Arrows φ hφ S (φ.obj c) (φ.obj c) (𝟙 (φ.obj c))
                                          -- ⊢ Map.Arrows φ hφ S (φ.obj c) (φ.obj c) (φ.map (𝟙 c))
      constructor; exact Sn.wide c
      -- ⊢ 𝟙 c ∈ arrows S c c
                   -- 🎉 no goals
    conj := fun {d d'} g δ hδ => by
      rw [mem_map_iff] at hδ
      -- ⊢ Groupoid.inv g ≫ δ ≫ g ∈ arrows (map φ hφ S) d' d'
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ; subst_vars; cases hφ cd'
      -- ⊢ Groupoid.inv g ≫ δ ≫ g ∈ arrows (map φ hφ S) d' d'
                                                -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
                                                            -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      have : d' ∈ (im φ hφ).objs := by rw [hφ']; apply mem_top_objs
      -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      rw [mem_im_objs_iff] at this
      -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      obtain ⟨c', rfl⟩ := this
      -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      have : g ∈ (im φ hφ).arrows (φ.obj c) (φ.obj c') := by rw [hφ']; trivial
      -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      rw [mem_im_iff] at this
      -- ⊢ Groupoid.inv g ≫ (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map γ ≫ eqToHom cd') ≫ …
      obtain ⟨b, b', f, hb, hb', _, hf⟩ := this; subst_vars; cases hφ hb; cases hφ hb'
      -- ⊢ Groupoid.inv (eqToHom (_ : φ.obj c = φ.obj b) ≫ φ.map f ≫ eqToHom hb') ≫ (eq …
                                                 -- ⊢ Groupoid.inv (eqToHom (_ : φ.obj c = φ.obj b) ≫ φ.map f ≫ eqToHom hb') ≫ (eq …
                                                             -- ⊢ Groupoid.inv (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map f ≫ eqToHom hb') ≫ (eq …
                                                                          -- ⊢ Groupoid.inv (eqToHom (_ : φ.obj c = φ.obj c) ≫ φ.map f ≫ eqToHom hb') ≫ (eq …
      change Map.Arrows φ hφ S (φ.obj c') (φ.obj c') _
      -- ⊢ Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (Groupoid.inv (eqToHom (_ : φ.obj c  …
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp, inv_eq_inv]
      -- ⊢ Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (inv (φ.map f) ≫ φ.map γ ≫ φ.map f)
      suffices Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map <| Groupoid.inv f ≫ γ ≫ f) by
        simp only [inv_eq_inv, Functor.map_comp, Functor.map_inv] at this; exact this
      · constructor; apply Sn.conj f γS }
        -- ⊢ Groupoid.inv f ≫ γ ≫ f ∈ arrows S c' c'
                     -- 🎉 no goals
#align category_theory.subgroupoid.is_normal_map CategoryTheory.Subgroupoid.isNormal_map

end Hom

section Thin

/-- A subgroupoid is thin (`CategoryTheory.Subgroupoid.IsThin`) if it has at most one arrow between
any two vertices. -/
abbrev IsThin :=
  Quiver.IsThin S.objs
#align category_theory.subgroupoid.is_thin CategoryTheory.Subgroupoid.IsThin

nonrec theorem isThin_iff : S.IsThin ↔ ∀ c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _
#align category_theory.subgroupoid.is_thin_iff CategoryTheory.Subgroupoid.isThin_iff

end Thin

section Disconnected

/-- A subgroupoid `IsTotallyDisconnected` if it has only isotropy arrows. -/
nonrec abbrev IsTotallyDisconnected :=
  IsTotallyDisconnected S.objs
#align category_theory.subgroupoid.is_totally_disconnected CategoryTheory.Subgroupoid.IsTotallyDisconnected

theorem isTotallyDisconnected_iff :
    S.IsTotallyDisconnected ↔ ∀ c d, (S.arrows c d).Nonempty → c = d := by
  constructor
  -- ⊢ IsTotallyDisconnected S → ∀ (c d : C), Set.Nonempty (arrows S c d) → c = d
  · rintro h c d ⟨f, fS⟩
    -- ⊢ c = d
    have := h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
    -- ⊢ c = d
    exact congr_arg Subtype.val this
    -- 🎉 no goals
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    -- ⊢ { val := c, property := hc } = { val := d, property := hd }
    simp only [Subtype.mk_eq_mk]
    -- ⊢ c = d
    exact h c d ⟨f, fS⟩
    -- 🎉 no goals
#align category_theory.subgroupoid.is_totally_disconnected_iff CategoryTheory.Subgroupoid.isTotallyDisconnected_iff

/-- The isotropy subgroupoid of `S` -/
def disconnect : Subgroupoid C where
  arrows c d := {f | c = d ∧ f ∈ S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
            -- ⊢ Groupoid.inv p✝ ∈ (fun c d => {f | c = d ∧ f ∈ arrows S c d}) c✝ c✝
                                   -- 🎉 no goals
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩
            -- ⊢ p✝ ≫ q✝ ∈ (fun c d => {f | c = d ∧ f ∈ arrows S c d}) c✝ c✝
                                                 -- 🎉 no goals
#align category_theory.subgroupoid.disconnect CategoryTheory.Subgroupoid.disconnect

theorem disconnect_le : S.disconnect ≤ S := by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption
                                               -- ⊢ ∀ {c d : C}, arrows (disconnect S) c d ⊆ arrows S c d
                                                            -- ⊢ a✝ ∈ arrows S c✝ d✝
                                                                             -- 🎉 no goals
#align category_theory.subgroupoid.disconnect_le CategoryTheory.Subgroupoid.disconnect_le

theorem disconnect_normal (Sn : S.IsNormal) : S.disconnect.IsNormal :=
  { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }
#align category_theory.subgroupoid.disconnect_normal CategoryTheory.Subgroupoid.disconnect_normal

@[simp]
theorem mem_disconnect_objs_iff {c : C} : c ∈ S.disconnect.objs ↔ c ∈ S.objs :=
  ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩
#align category_theory.subgroupoid.mem_disconnect_objs_iff CategoryTheory.Subgroupoid.mem_disconnect_objs_iff

theorem disconnect_objs : S.disconnect.objs = S.objs := Set.ext fun _ ↦ mem_disconnect_objs_iff _
#align category_theory.subgroupoid.disconnect_objs CategoryTheory.Subgroupoid.disconnect_objs

theorem disconnect_isTotallyDisconnected : S.disconnect.IsTotallyDisconnected := by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h
  -- ⊢ ∀ (c d : C), Set.Nonempty (arrows (disconnect S) c d) → c = d
                                  -- 🎉 no goals
#align category_theory.subgroupoid.disconnect_is_totally_disconnected CategoryTheory.Subgroupoid.disconnect_isTotallyDisconnected

end Disconnected

section Full

variable (D : Set C)

/-- The full subgroupoid on a set `D : Set C` -/
def full : Subgroupoid C where
  arrows c d := {_f | c ∈ D ∧ d ∈ D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
            -- ⊢ Groupoid.inv p✝ ∈ (fun c d => {_f | c ∈ D ∧ d ∈ D}) d✝ c✝
                             -- ⊢ d✝ ∈ D
                                             -- 🎉 no goals
                                             -- 🎉 no goals
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption
            -- ⊢ p✝ ≫ q✝ ∈ (fun c d => {_f | c ∈ D ∧ d ∈ D}) c✝ e✝
                                    -- ⊢ c✝ ∈ D
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align category_theory.subgroupoid.full CategoryTheory.Subgroupoid.full

theorem full_objs : (full D).objs = D :=
  Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩
#align category_theory.subgroupoid.full_objs CategoryTheory.Subgroupoid.full_objs

@[simp]
theorem mem_full_iff {c d : C} {f : c ⟶ d} : f ∈ (full D).arrows c d ↔ c ∈ D ∧ d ∈ D :=
  Iff.rfl
#align category_theory.subgroupoid.mem_full_iff CategoryTheory.Subgroupoid.mem_full_iff

@[simp]
theorem mem_full_objs_iff {c : C} : c ∈ (full D).objs ↔ c ∈ D := by rw [full_objs]
                                                                    -- 🎉 no goals
#align category_theory.subgroupoid.mem_full_objs_iff CategoryTheory.Subgroupoid.mem_full_objs_iff

@[simp]
theorem full_empty : full ∅ = (⊥ : Subgroupoid C) := by
  ext
  -- ⊢ x✝ ∈ arrows (full ∅) x✝² x✝¹ ↔ x✝ ∈ arrows ⊥ x✝² x✝¹
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]
  -- 🎉 no goals
#align category_theory.subgroupoid.full_empty CategoryTheory.Subgroupoid.full_empty

@[simp]
theorem full_univ : full Set.univ = (⊤ : Subgroupoid C) := by
  ext
  -- ⊢ x✝ ∈ arrows (full univ) x✝² x✝¹ ↔ x✝ ∈ arrows ⊤ x✝² x✝¹
  simp only [mem_full_iff, mem_univ, mem_top]
  -- 🎉 no goals
#align category_theory.subgroupoid.full_univ CategoryTheory.Subgroupoid.full_univ

theorem full_mono {D E : Set C} (h : D ≤ E) : full D ≤ full E := by
  rw [le_iff]
  -- ⊢ ∀ {c d : C}, arrows (full D) c d ⊆ arrows (full E) c d
  rintro c d f
  -- ⊢ f ∈ arrows (full D) c d → f ∈ arrows (full E) c d
  simp only [mem_full_iff]
  -- ⊢ c ∈ D ∧ d ∈ D → c ∈ E ∧ d ∈ E
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩
  -- 🎉 no goals
#align category_theory.subgroupoid.full_mono CategoryTheory.Subgroupoid.full_mono

-- porting note: using `.1` instead of `↑`
theorem full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} :
    f = g ↔ (f.1 : c.val ⟶ d.val) = g.1 :=
  Subtype.ext_iff
#align category_theory.subgroupoid.full_arrow_eq_iff CategoryTheory.Subgroupoid.full_arrow_eq_iff

end Full

end Subgroupoid

end CategoryTheory
