/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Set.Lattice

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
* `CategoryTheory.Subgroupoid.vertexSubgroup` is the subgroup of the *vertex group* at a given
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
  /-- The arrow choice for each pair of vertices -/
  arrows : ∀ c d : C, Set (c ⟶ d)
  protected inv : ∀ {c d} {p : c ⟶ d}, p ∈ arrows c d → Groupoid.inv p ∈ arrows d c
  protected mul : ∀ {c d e} {p}, p ∈ arrows c d → ∀ {q}, q ∈ arrows d e → p ≫ q ∈ arrows c e

namespace Subgroupoid

variable (S : Subgroupoid C)

theorem inv_mem_iff {c d : C} (f : c ⟶ d) :
    Groupoid.inv f ∈ S.arrows d c ↔ f ∈ S.arrows c d := by
  constructor
  · intro h
    simpa only [inv_eq_inv, IsIso.inv_inv] using S.inv h
  · apply S.inv

theorem mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f ∈ S.arrows c d) :
    f ≫ g ∈ S.arrows c e ↔ g ∈ S.arrows d e := by
  constructor
  · rintro h
    suffices Groupoid.inv f ≫ f ≫ g ∈ S.arrows d e by
      simpa only [inv_eq_inv, IsIso.inv_hom_id_assoc] using this
    apply S.mul (S.inv hf) h
  · apply S.mul hf

theorem mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g ∈ S.arrows d e) :
    f ≫ g ∈ S.arrows c e ↔ f ∈ S.arrows c d := by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ Groupoid.inv g ∈ S.arrows c d by
      simpa only [inv_eq_inv, IsIso.hom_inv_id, Category.comp_id, Category.assoc] using this
    apply S.mul h (S.inv hg)
  · exact fun hf => S.mul hf hg

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def objs : Set C :=
  {c : C | (S.arrows c c).Nonempty}

theorem mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : c ∈ S.objs :=
  ⟨f ≫ Groupoid.inv f, S.mul h (S.inv h)⟩

theorem mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : d ∈ S.objs :=
  ⟨Groupoid.inv f ≫ f, S.mul (S.inv h) h⟩

theorem id_mem_of_nonempty_isotropy (c : C) : c ∈ objs S → 𝟙 c ∈ S.arrows c c := by
  rintro ⟨γ, hγ⟩
  convert S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, IsIso.hom_inv_id]

theorem id_mem_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 c ∈ S.arrows c c :=
  id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

theorem id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.arrows c d) : 𝟙 d ∈ S.arrows d d :=
  id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def asWideQuiver : Quiver C :=
  ⟨fun c d => Subtype <| S.arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
@[simps comp_coe, simps -isSimp inv_coe]
instance coe : Groupoid S.objs where
  Hom a b := S.arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.prop⟩
  comp p q := ⟨p.val ≫ q.val, S.mul p.prop q.prop⟩
  inv p := ⟨Groupoid.inv p.val, S.inv p.prop⟩

@[simp]
theorem coe_inv_coe' {c d : S.objs} (p : c ⟶ d) :
    (CategoryTheory.inv p).val = CategoryTheory.inv p.val := by
  simp only [← inv_eq_inv, coe_inv_coe]

/-- The embedding of the coerced subgroupoid to its parent -/
def hom : S.objs ⥤ C where
  obj c := c.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

theorem hom.inj_on_objects : Function.Injective (hom S).obj := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]; exact hcd

theorem hom.faithful : ∀ c d, Function.Injective fun f : c ⟶ d => (hom S).map f := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg; exact Subtype.ext hfg

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertexSubgroup {c : C} (hc : c ∈ S.objs) : Subgroup (c ⟶ c) where
  carrier := S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

/-- The set of all arrows of a subgroupoid, as a set in `Σ c d : C, c ⟶ d`. -/
@[coe] def toSet (S : Subgroupoid C) : Set (Σ c d : C, c ⟶ d) :=
  {F | F.2.2 ∈ S.arrows F.1 F.2.1}

instance : SetLike (Subgroupoid C) (Σ c d : C, c ⟶ d) where
  coe := toSet
  coe_injective' := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by ext c d f; apply Set.ext_iff.1 h ⟨c, d, f⟩

theorem mem_iff (S : Subgroupoid C) (F : Σ c d, c ⟶ d) : F ∈ S ↔ F.2.2 ∈ S.arrows F.1 F.2.1 :=
  Iff.rfl

theorem le_iff (S T : Subgroupoid C) : S ≤ T ↔ ∀ {c d}, S.arrows c d ⊆ T.arrows c d := by
  rw [SetLike.le_def, Sigma.forall]; exact forall_congr' fun c => Sigma.forall

instance : Top (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => Set.univ
      mul := by intros; trivial
      inv := by intros; trivial }⟩

theorem mem_top {c d : C} (f : c ⟶ d) : f ∈ (⊤ : Subgroupoid C).arrows c d :=
  trivial

theorem mem_top_objs (c : C) : c ∈ (⊤ : Subgroupoid C).objs := by
  dsimp [Top.top, objs]
  simp only [univ_nonempty]

instance : Bot (Subgroupoid C) :=
  ⟨{  arrows := fun _ _ => ∅
      mul := False.elim
      inv := False.elim }⟩

instance : Inhabited (Subgroupoid C) :=
  ⟨⊤⟩

instance : Min (Subgroupoid C) :=
  ⟨fun S T =>
    { arrows := fun c d => S.arrows c d ∩ T.arrows c d
      inv := fun hp ↦ ⟨S.inv hp.1, T.inv hp.2⟩
      mul := fun hp _ hq ↦ ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

instance : InfSet (Subgroupoid C) :=
  ⟨fun s =>
    { arrows := fun c d => ⋂ S ∈ s, Subgroupoid.arrows S c d
      inv := fun hp ↦ by rw [mem_iInter₂] at hp ⊢; exact fun S hS => S.inv (hp S hS)
      mul := fun hp _ hq ↦ by
        rw [mem_iInter₂] at hp hq ⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩

theorem mem_sInf_arrows {s : Set (Subgroupoid C)} {c d : C} {p : c ⟶ d} :
    p ∈ (sInf s).arrows c d ↔ ∀ S ∈ s, p ∈ S.arrows c d :=
  mem_iInter₂

theorem mem_sInf {s : Set (Subgroupoid C)} {p : Σ c d : C, c ⟶ d} :
    p ∈ sInf s ↔ ∀ S ∈ s, p ∈ S :=
  mem_sInf_arrows

instance : CompleteLattice (Subgroupoid C) :=
  { completeLatticeOfInf (Subgroupoid C) (by
      refine fun s => ⟨fun S Ss F => ?_, fun T Tl F fT => ?_⟩ <;> simp only [mem_sInf]
      exacts [fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
    bot := ⊥
    bot_le := fun _ => empty_subset _
    top := ⊤
    le_top := fun _ => subset_univ _
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ RS RT _ pR => ⟨RS pR, RT pR⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

theorem le_objs {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⊆ T.objs := fun s ⟨γ, hγ⟩ =>
  ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

/-- The functor associated to the embedding of subgroupoids -/
def inclusion {S T : Subgroupoid C} (h : S ≤ T) : S.objs ⥤ T.objs where
  obj s := ⟨s.val, le_objs h s.prop⟩
  map f := ⟨f.val, @h ⟨_, _, f.val⟩ f.prop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem inclusion_inj_on_objects {S T : Subgroupoid C} (h : S ≤ T) :
    Function.Injective (inclusion h).obj := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
  simpa only [inclusion, Subtype.mk_eq_mk] using id

theorem inclusion_faithful {S T : Subgroupoid C} (h : S ≤ T) (s t : S.objs) :
    Function.Injective fun f : s ⟶ t => (inclusion h).map f := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  -- Porting note: was `...; simpa only [Subtype.mk_eq_mk] using id`
  dsimp only [inclusion]; rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]; exact id

theorem inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.objs :=
  Functor.hext (fun _ => rfl) fun _ _ _ => HEq.refl _

theorem inclusion_trans {R S T : Subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
    inclusion (k.trans h) = inclusion k ⋙ inclusion h :=
  rfl

theorem inclusion_comp_embedding {S T : Subgroupoid C} (h : S ≤ T) : inclusion h ⋙ T.hom = S.hom :=
  rfl

/-- The family of arrows of the discrete groupoid -/
inductive Discrete.Arrows : ∀ c d : C, (c ⟶ d) → Prop
  | id (c : C) : Discrete.Arrows c c (𝟙 c)

/-- The only arrows of the discrete groupoid are the identity arrows. -/
def discrete : Subgroupoid C where
  arrows c d := {p | Discrete.Arrows c d p}
  inv := by rintro _ _ _ ⟨⟩; simp only [inv_eq_inv, IsIso.inv_id]; constructor
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; rw [Category.comp_id]; constructor

theorem mem_discrete_iff {c d : C} (f : c ⟶ d) :
    f ∈ discrete.arrows c d ↔ ∃ h : c = d, f = eqToHom h :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, by rintro ⟨rfl, rfl⟩; constructor⟩

/-- A subgroupoid is wide if its carrier set is all of `C`. -/
structure IsWide : Prop where
  wide : ∀ c, 𝟙 c ∈ S.arrows c c

theorem isWide_iff_objs_eq_univ : S.IsWide ↔ S.objs = Set.univ := by
  constructor
  · rintro h
    ext x; constructor <;> simp only [mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
  · rintro h
    refine ⟨fun c => ?_⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ ⊆ S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS

theorem IsWide.id_mem {S : Subgroupoid C} (Sw : S.IsWide) (c : C) : 𝟙 c ∈ S.arrows c c :=
  Sw.wide c

theorem IsWide.eqToHom_mem {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d) :
    eqToHom h ∈ S.arrows c d := by cases h; simp only [eqToHom_refl]; apply Sw.id_mem c

/-- A subgroupoid is normal if it is wide and satisfies the expected stability under conjugacy. -/
structure IsNormal : Prop extends IsWide S where
  conj : ∀ {c d} (p : c ⟶ d) {γ : c ⟶ c}, γ ∈ S.arrows c c → Groupoid.inv p ≫ γ ≫ p ∈ S.arrows d d

theorem IsNormal.conj' {S : Subgroupoid C} (Sn : IsNormal S) :
    ∀ {c d} (p : d ⟶ c) {γ : c ⟶ c}, γ ∈ S.arrows c c → p ≫ γ ≫ Groupoid.inv p ∈ S.arrows d d :=
  fun p γ hs => by convert Sn.conj (Groupoid.inv p) hs; simp

theorem IsNormal.conjugation_bij (Sn : IsNormal S) {c d} (p : c ⟶ d) :
    Set.BijOn (fun γ : c ⟶ c => Groupoid.inv p ≫ γ ≫ p) (S.arrows c c) (S.arrows d d) := by
  refine ⟨fun γ γS => Sn.conj p γS, fun γ₁ _ γ₂ _ h => ?_, fun δ δS =>
    ⟨p ≫ δ ≫ Groupoid.inv p, Sn.conj' p δS, ?_⟩⟩
  · simpa only [inv_eq_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using p ≫= h =≫ inv p
  · simp only [inv_eq_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc]

theorem top_isNormal : IsNormal (⊤ : Subgroupoid C) :=
  { wide := fun _ => trivial
    conj := fun _ _ _ => trivial }

theorem sInf_isNormal (s : Set <| Subgroupoid C) (sn : ∀ S ∈ s, IsNormal S) : IsNormal (sInf s) :=
  { wide := by simp_rw [sInf, mem_iInter₂]; exact fun c S Ss => (sn S Ss).wide c
    conj := by simp_rw [sInf, mem_iInter₂]; exact fun p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }

theorem discrete_isNormal : (@discrete C _).IsNormal :=
  { wide := fun c => by constructor
    conj := fun f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, Category.id_comp, IsIso.inv_hom_id]; constructor }

theorem IsNormal.vertexSubgroup (Sn : IsNormal S) (c : C) (cS : c ∈ S.objs) :
    (S.vertexSubgroup cS).Normal where
  conj_mem x hx y := by rw [mul_assoc]; exact Sn.conj' y hx

section GeneratedSubgroupoid

-- TODO: proof that generated is just "words in X" and generatedNormal is similarly
variable (X : ∀ c d : C, Set (c ⟶ d))

/-- The subgroupoid generated by the set of arrows `X` -/
def generated : Subgroupoid C :=
  sInf {S : Subgroupoid C | ∀ c d, X c d ⊆ S.arrows c d}

theorem subset_generated (c d : C) : X c d ⊆ (generated X).arrows c d := by
  dsimp only [generated, sInf]
  simp only [subset_iInter₂_iff]
  exact fun S hS f fS => hS _ _ fS

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generatedNormal : Subgroupoid C :=
  sInf {S : Subgroupoid C | (∀ c d, X c d ⊆ S.arrows c d) ∧ S.IsNormal}

theorem generated_le_generatedNormal : generated X ≤ generatedNormal X := by
  apply @sInf_le_sInf (Subgroupoid C) _
  exact fun S ⟨h, _⟩ => h

theorem generatedNormal_isNormal : (generatedNormal X).IsNormal :=
  sInf_isNormal _ fun _ h => h.right

theorem IsNormal.generatedNormal_le {S : Subgroupoid C} (Sn : S.IsNormal) :
    generatedNormal X ≤ S ↔ ∀ c d, X c d ⊆ S.arrows c d := by
  constructor
  · rintro h c d
    have h' := generated_le_generatedNormal X
    rw [le_iff] at h h'
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
  · rintro h
    apply @sInf_le (Subgroupoid C) _
    exact ⟨h, Sn⟩

end GeneratedSubgroupoid

section Hom

variable {D : Type*} [Groupoid D] (φ : C ⥤ D)

/-- A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
-/
def comap (S : Subgroupoid D) : Subgroupoid C where
  arrows c d := {f : c ⟶ d | φ.map f ∈ S.arrows (φ.obj c) (φ.obj d)}
  inv hp := by rw [mem_setOf, inv_eq_inv, φ.map_inv, ← inv_eq_inv]; exact S.inv hp
  mul := by
    intros
    simp only [mem_setOf, Functor.map_comp]
    apply S.mul <;> assumption

theorem comap_mono (S T : Subgroupoid D) : S ≤ T → comap φ S ≤ comap φ T := fun ST _ =>
  @ST ⟨_, _, _⟩

theorem isNormal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S) where
  wide c := by rw [comap, mem_setOf, Functor.map_id]; apply Sn.wide
  conj f γ hγ := by
    simp_rw [inv_eq_inv f, comap, mem_setOf, Functor.map_comp, Functor.map_inv, ← inv_eq_inv]
    exact Sn.conj _ hγ

@[simp]
theorem comap_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ ∘ comap ψ :=
  rfl

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : Subgroupoid C :=
  comap φ discrete

theorem mem_ker_iff {c d : C} (f : c ⟶ d) :
    f ∈ (ker φ).arrows c d ↔ ∃ h : φ.obj c = φ.obj d, φ.map f = eqToHom h :=
  mem_discrete_iff (φ.map f)

theorem ker_isNormal : (ker φ).IsNormal :=
  isNormal_comap φ discrete_isNormal

@[simp]
theorem ker_comp {E : Type*} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) :=
  rfl

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive Map.Arrows (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : ∀ c d : D, (c ⟶ d) → Prop
  | im {c d : C} (f : c ⟶ d) (hf : f ∈ S.arrows c d) : Map.Arrows hφ S (φ.obj c) (φ.obj d) (φ.map f)

theorem Map.arrows_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    Map.Arrows φ hφ S c d f ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eqToHom _⟩
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩; rw [← eq_conj_eqToHom]; constructor; exact hg

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  arrows c d := {x | Map.Arrows φ hφ S c d x}
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv, ← Functor.map_inv, ← inv_eq_inv]
    constructor; apply S.inv; assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (Map.arrows_iff φ hφ S q).mp hq
    cases hφ he; rw [gq, ← eq_conj_eqToHom, ← φ.map_comp]
    constructor; exact S.mul hf hg

theorem mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    f ∈ (map φ hφ S).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d) (_hg : g ∈ S.arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  Map.arrows_iff φ hφ S f

theorem galoisConnection_map_comap (hφ : Function.Injective φ.obj) :
    GaloisConnection (map φ hφ) (comap φ) := by
  rintro S T; simp_rw [le_iff]; constructor
  · exact fun h c d f fS => h (Map.Arrows.im f fS)
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS

theorem map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) :
    S ≤ T → map φ hφ S ≤ map φ hφ T := fun h => (galoisConnection_map_comap φ hφ).monotone_l h

theorem le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) :
    S ≤ comap φ (map φ hφ S) :=
  (galoisConnection_map_comap φ hφ).le_u_l S

theorem map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) :
    map φ hφ (comap φ T) ≤ T :=
  (galoisConnection_map_comap φ hφ).l_u_le T

theorem map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C)
    (T : Subgroupoid D) : map φ hφ S ≤ T ↔ S ≤ comap φ T :=
  (galoisConnection_map_comap φ hφ).le_iff_le

theorem mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (map φ hφ S).objs ↔ ∃ c ∈ S.objs, φ.obj c = d := by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change Map.Arrows φ hφ S d d f at hf; rw [Map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩

@[simp]
theorem map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).objs = φ.obj '' S.objs := by
  ext x; convert mem_map_objs_iff S φ hφ x

/-- The image of a functor injective on objects -/
def im (hφ : Function.Injective φ.obj) :=
  map φ hφ ⊤

theorem mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) :
    f ∈ (im φ hφ).arrows c d ↔
      ∃ (a b : C) (g : a ⟶ b) (ha : φ.obj a = c) (hb : φ.obj b = d),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb := by
  convert Map.arrows_iff φ hφ ⊤ f; simp only [Top.top, mem_univ, exists_true_left]

theorem mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) :
    d ∈ (im φ hφ).objs ↔ ∃ c : C, φ.obj c = d := by
  simp only [im, mem_map_objs_iff, mem_top_objs, true_and]

theorem obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) :
    Function.Surjective φ.obj := by
  rintro d
  rw [← mem_im_objs_iff _ hφ, hφ']
  apply mem_top_objs

theorem isNormal_map (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal) :
    (map φ hφ S).IsNormal :=
  { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      change Map.Arrows φ hφ S _ _ (𝟙 _); rw [← Functor.map_id]
      constructor; exact Sn.wide c
    conj := fun {d d'} g δ hδ => by
      rw [mem_map_iff] at hδ
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ; subst_vars; cases hφ cd'
      have : d' ∈ (im φ hφ).objs := by rw [hφ']; apply mem_top_objs
      rw [mem_im_objs_iff] at this
      obtain ⟨c', rfl⟩ := this
      have : g ∈ (im φ hφ).arrows (φ.obj c) (φ.obj c') := by rw [hφ']; trivial
      rw [mem_im_iff] at this
      obtain ⟨b, b', f, hb, hb', _, hf⟩ := this; cases hφ hb; cases hφ hb'
      change Map.Arrows φ hφ S (φ.obj c') (φ.obj c') _
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp, inv_eq_inv]
      suffices Map.Arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map <| Groupoid.inv f ≫ γ ≫ f) by
        simp only [inv_eq_inv, Functor.map_comp, Functor.map_inv] at this; exact this
      constructor; apply Sn.conj f γS }

end Hom

section Thin

/-- A subgroupoid is thin (`CategoryTheory.Subgroupoid.IsThin`) if it has at most one arrow between
any two vertices. -/
abbrev IsThin :=
  Quiver.IsThin S.objs

nonrec theorem isThin_iff : S.IsThin ↔ ∀ c : S.objs, Subsingleton (S.arrows c c) := isThin_iff _

end Thin

section Disconnected

/-- A subgroupoid `IsTotallyDisconnected` if it has only isotropy arrows. -/
nonrec abbrev IsTotallyDisconnected :=
  IsTotallyDisconnected S.objs

theorem isTotallyDisconnected_iff :
    S.IsTotallyDisconnected ↔ ∀ c d, (S.arrows c d).Nonempty → c = d := by
  constructor
  · rintro h c d ⟨f, fS⟩
    exact congr_arg Subtype.val <| h ⟨c, mem_objs_of_src S fS⟩ ⟨d, mem_objs_of_tgt S fS⟩ ⟨f, fS⟩
  · rintro h ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, fS⟩
    simp only [Subtype.mk_eq_mk]
    exact h c d ⟨f, fS⟩

/-- The isotropy subgroupoid of `S` -/
def disconnect : Subgroupoid C where
  arrows c d := {f | c = d ∧ f ∈ S.arrows c d}
  inv := by rintro _ _ _ ⟨rfl, h⟩; exact ⟨rfl, S.inv h⟩
  mul := by rintro _ _ _ _ ⟨rfl, h⟩ _ ⟨rfl, h'⟩; exact ⟨rfl, S.mul h h'⟩

theorem disconnect_le : S.disconnect ≤ S := by rw [le_iff]; rintro _ _ _ ⟨⟩; assumption

theorem disconnect_normal (Sn : S.IsNormal) : S.disconnect.IsNormal :=
  { wide := fun c => ⟨rfl, Sn.wide c⟩
    conj := fun _ _ ⟨_, h'⟩ => ⟨rfl, Sn.conj _ h'⟩ }

@[simp]
theorem mem_disconnect_objs_iff {c : C} : c ∈ S.disconnect.objs ↔ c ∈ S.objs :=
  ⟨fun ⟨γ, _, γS⟩ => ⟨γ, γS⟩, fun ⟨γ, γS⟩ => ⟨γ, rfl, γS⟩⟩

theorem disconnect_objs : S.disconnect.objs = S.objs := Set.ext fun _ ↦ mem_disconnect_objs_iff _

theorem disconnect_isTotallyDisconnected : S.disconnect.IsTotallyDisconnected := by
  rw [isTotallyDisconnected_iff]; exact fun c d ⟨_, h, _⟩ => h

end Disconnected

section Full

variable (D : Set C)

/-- The full subgroupoid on a set `D : Set C` -/
def full : Subgroupoid C where
  arrows c d := {_f | c ∈ D ∧ d ∈ D}
  inv := by rintro _ _ _ ⟨⟩; constructor <;> assumption
  mul := by rintro _ _ _ _ ⟨⟩ _ ⟨⟩; constructor <;> assumption

theorem full_objs : (full D).objs = D :=
  Set.ext fun _ => ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨𝟙 _, h, h⟩⟩

@[simp]
theorem mem_full_iff {c d : C} {f : c ⟶ d} : f ∈ (full D).arrows c d ↔ c ∈ D ∧ d ∈ D :=
  Iff.rfl

@[simp]
theorem mem_full_objs_iff {c : C} : c ∈ (full D).objs ↔ c ∈ D := by rw [full_objs]

@[simp]
theorem full_empty : full ∅ = (⊥ : Subgroupoid C) := by
  ext
  simp only [Bot.bot, mem_full_iff, mem_empty_iff_false, and_self_iff]

@[simp]
theorem full_univ : full Set.univ = (⊤ : Subgroupoid C) := by
  ext
  simp only [mem_full_iff, mem_univ, and_self, mem_top]

theorem full_mono {D E : Set C} (h : D ≤ E) : full D ≤ full E := by
  rw [le_iff]
  rintro c d f
  simp only [mem_full_iff]
  exact fun ⟨hc, hd⟩ => ⟨h hc, h hd⟩

theorem full_arrow_eq_iff {c d : (full D).objs} {f g : c ⟶ d} :
    f = g ↔ f.1 = g.1 :=
  Subtype.ext_iff

end Full

end Subgroupoid

end CategoryTheory
