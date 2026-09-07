/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Presieves

A presieve on an object `X` of a category `C` is an arbitrary predicate on morphisms with codomain
`X`. Unlike a sieve, a presieve is not required to be closed under precomposition. Presieves are
useful for specifying generating families of arrows before passing to the sieve they generate.

This file develops the basic theory of presieves. It defines singleton presieves and presieves
`Presieve.ofArrows` associated to indexed families of arrows, together with binding and
pullback constructions. It also defines pullback and pushforward along a fixed morphism, the
associated Galois connection, and the category, diagram, and cocone determined by a presieve.
Finally, `Presieve.uncurry` realizes a presieve as a set in a sigma type.

Functorial operations induced by a functor between categories are developed in
`Mathlib.CategoryTheory.Sites.Sieves.Functoriality`.

## Tags

presieve, pullback
-/

@[expose] public section


universe w v₁ v₂ u₁

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y Z : C} (f : Y ⟶ X)

/-- A predicate on arrows with codomain `X`. -/
@[implicit_reducible]
def Presieve (X : C) :=
  ∀ ⦃Y⦄, (Y ⟶ X) → Prop
deriving CompleteLattice, Inhabited

@[simp]
lemma top_apply (f : Y ⟶ X) : (⊤ : Presieve X) f :=
  trivial

@[simp]
lemma bot_apply (f : Y ⟶ X) : (⊥ : Presieve X) f ↔ False :=
  .rfl

namespace Presieve

/-- The full subcategory of the over category `C/X` consisting of arrows which belong to a
    presieve on `X`. -/
abbrev category {X : C} (P : Presieve X) :=
  ObjectProperty.FullSubcategory fun f : Over X => P f.hom

/-- Construct an object of `P.category`. -/
abbrev categoryMk {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f) : P.category :=
  ⟨Over.mk f, hf⟩

/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
abbrev diagram (S : Presieve X) : S.category ⥤ C :=
  ObjectProperty.ι _ ⋙ Over.forget X

/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (ObjectProperty.ι _)

/-- Given a presieve `S` on `X`, and presieve `R` on `Y` for each
`f : Y ⟶ X` in `S`, produce a presieve on `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

/-- Structure which contains the data and properties for a morphism `h` satisfying
`Presieve.bind S R h`. -/
structure BindStruct (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y)
    {Z : C} (h : Z ⟶ X) where
  /-- the intermediate object -/
  Y : C
  /-- a morphism in the family of presieves `R` -/
  g : Z ⟶ Y
  /-- a morphism in the presieve `S` -/
  f : Y ⟶ X
  hf : S f
  hg : R hf g
  fac : g ≫ f = h

attribute [reassoc (attr := simp)] BindStruct.fac

/-- If a morphism `h` satisfies `Presieve.bind S R h`, this is a choice of a structure
in `BindStruct S R h`. -/
noncomputable def bind.bindStruct {S : Presieve X} {R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y}
    {Z : C} {h : Z ⟶ X} (H : bind S R h) : BindStruct S R h :=
  Nonempty.some (by
    obtain ⟨Y, g, f, hf, hg, fac⟩ := H
    exact ⟨{ hf := hf, hg := hg, fac := fac, .. }⟩)

lemma BindStruct.bind {S : Presieve X} {R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y}
    {Z : C} {h : Z ⟶ X} (b : BindStruct S R h) : bind S R h :=
  ⟨b.Y, b.g, b.f, b.hf, b.hg, b.fac⟩

@[simp]
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩

-- Note we can't make this into `HasSingleton` because of the out-param.
/-- The singleton presieve. -/
inductive singleton : Presieve X
  | mk : singleton f

@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk

theorem singleton_self : singleton f f :=
  singleton.mk

@[simp]
lemma singleton_le_iff {R : Presieve X} :
    singleton f ≤ R ↔ R f :=
  ⟨fun hf ↦ hf _ _ ⟨⟩, by rintro hf _ _ ⟨⟩; exact hf⟩

/-- A presieve `R` has pullbacks along `f` if for every `h` in `R`, the pullback
with `f` exists. -/
protected class HasPullbacks (R : Presieve X) {Y : C} (f : Y ⟶ X) : Prop where
  hasPullback (f) {Z : C} {h : Z ⟶ X} : R h → Limits.HasPullback h f

protected alias hasPullback := HasPullbacks.hasPullback

instance [HasPullbacks C] (R : Presieve X) {Y : C} (f : Y ⟶ X) : R.HasPullbacks f where
  hasPullback _ := inferInstance

instance (g : Z ⟶ X) [HasPullback g f] : (singleton g).HasPullbacks f where
  hasPullback {Z} h := by
    intro ⟨⟩
    infer_instance

/-- Pullback a presieve along a fixed map, by taking the pullback in the
category.
This is not the same as the underlying presieve of `Sieve.pullback`, but there is a relation between
them in `pullbackArrows_comm`.
-/
inductive pullbackArrows (R : Presieve X) [R.HasPullbacks f] : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) (hRh : R h) :
    haveI := R.hasPullback f hRh
    pullbackArrows _ (pullback.snd h f)

theorem pullback_singleton (g : Z ⟶ X) [HasPullback g f] :
    pullbackArrows f (singleton g) = singleton (pullback.snd g f) := by
  funext W
  ext h
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullbackArrows.mk Z g singleton.mk

/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
inductive ofArrows {ι : Type*} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : ofArrows _ _ (f i)

lemma ofArrows.mk' {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
    (i : ι) (h : Z = Y i) (hg : g = eqToHom h ≫ f i) :
    ofArrows Y f g := by
  subst h
  simp only [eqToHom_refl, id_comp] at hg
  subst hg
  constructor

instance {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    [∀ i, HasPullback (g i) f] : (ofArrows Z g).HasPullbacks f where
  hasPullback {_} _ := fun ⟨i⟩ ↦ inferInstance

theorem ofArrows_pullback {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    [∀ i, HasPullback (g i) f] :
    (ofArrows (fun i => pullback (g i) f) fun _ => pullback.snd _ _) =
      pullbackArrows f (ofArrows Z g) := by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, ⟨_⟩⟩
    apply ofArrows.mk

theorem ofArrows_bind {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    (j : ∀ ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f → Type*) (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C)
    (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((ofArrows Z g).bind fun _ f H => ofArrows (W f H) (k f H)) =
      ofArrows (fun i : Σ i, j _ (ofArrows.mk i) => W (g i.1) _ i.2) fun ij =>
        k (g ij.1) _ ij.2 ≫ g ij.1 := by
  funext Y
  ext f
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact ofArrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)

theorem ofArrows_surj {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
    (hg : ofArrows Y f g) : ∃ (i : ι) (h : Y i = Z),
    g = eqToHom h.symm ≫ f i := by
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩

lemma exists_eq_ofArrows (R : Presieve X) :
    ∃ (ι : Type (max u₁ v₁)) (Y : ι → C) (f : ∀ i, Y i ⟶ X), R = .ofArrows Y f := by
  let ι := { x : Σ Z, (Z ⟶ X) // R x.2 }
  use ι, fun x ↦ x.1.1, fun x ↦ x.1.2
  exact le_antisymm (fun Z g hg ↦ .mk (⟨⟨_, _⟩, hg⟩ : ι)) fun Z g ⟨x⟩ ↦ x.2

lemma ofArrows_category {S : C} (R : Presieve S) :
    Presieve.ofArrows _ (fun (f : R.category) ↦ f.obj.hom) = R := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨X, h⟩
    exact h
  · rintro X g hg
    exact .mk (ι := R.category) ⟨Over.mk g, hg⟩

/-- If `g : Y ⟶ S` is in the presieve given by the indexed family `fᵢ`, this is a choice
of index such that `g = fᵢ` modulo `eqToHom`.
Note: This should generally not be used! If possible, use the induction principle
for the type `Presieve.ofArrows` instead (using e.g., `rintro / obtain`). -/
noncomputable
def ofArrows.idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : Presieve.ofArrows X f g) : ι :=
  (ofArrows_surj _ _ hf).choose

lemma ofArrows.obj_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : X hf.idx = Y :=
  (ofArrows_surj _ _ hf).choose_spec.1

lemma ofArrows.eq_eqToHom_comp_hom_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C}
    {g : Y ⟶ S} (hf : ofArrows X f g) : g = eqToHom hf.obj_idx.symm ≫ f hf.idx :=
  (Presieve.ofArrows_surj _ _ hf).choose_spec.2

lemma ofArrows.hom_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : f hf.idx = eqToHom hf.obj_idx ≫ g := by
  simp [eq_eqToHom_comp_hom_idx hf]

lemma ofArrows_comp_le {X : C} {ι σ : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) (a : σ → ι) :
    ofArrows (Y ∘ a) (fun i ↦ f (a i)) ≤ ofArrows Y f := by
  rintro - - ⟨i⟩
  use a i

lemma ofArrows_comp_eq_of_surjective {X : C} {ι σ : Type*} {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) {a : σ → ι} (ha : a.Surjective) :
    ofArrows (Y ∘ a) (fun i ↦ f (a i)) = ofArrows Y f := by
  refine le_antisymm (ofArrows_comp_le f a) ?_
  rintro - - ⟨i⟩
  obtain ⟨j, rfl⟩ := ha i
  use j

lemma ofArrows_le_iff {X : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {R : Presieve X} :
    Presieve.ofArrows Y f ≤ R ↔ ∀ i, R (f i) :=
  ⟨fun hle i ↦ hle _ _ ⟨i⟩, fun h _ g ⟨i⟩ ↦ h i⟩

lemma ofArrows_of_unique {X : C} {ι : Type*} [Unique ι] {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = singleton (f default) := by
  refine le_antisymm ?_ fun Y _ ⟨⟩ ↦ ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp

theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit.{w + 1} => f) = singleton f := by
  rw [ofArrows_of_unique]

@[grind =]
lemma ofArrows_of_isEmpty {X : C} {ι : Type*} [IsEmpty ι] {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = ⊥ := by
  rw [eq_bot_iff, ofArrows_le_iff]
  simp

/-- A convenient constructor for a refinement of a presieve of the form `Presieve.ofArrows`.
This contains a sieve obtained by `Sieve.bind` and `Sieve.ofArrows`, see
`Presieve.bind_ofArrows_le_bindOfArrows`, but has better definitional properties. -/
inductive bindOfArrows {ι : Type*} {X : C} (Y : ι → C)
    (f : ∀ i, Y i ⟶ X) (R : ∀ i, Presieve (Y i)) : Presieve X
  | mk (i : ι) {Z : C} (g : Z ⟶ Y i) (hg : R i g) : bindOfArrows Y f R (g ≫ f i)

lemma bindOfArrows_ofArrows {ι : Type*} {S : C} {X : ι → C} (f : (i : ι) → X i ⟶ S)
    {σ : ι → Type*} {Y : (i : ι) → σ i → C} (g : (i : ι) → (j : σ i) → Y i j ⟶ X i) :
    Presieve.bindOfArrows X f (fun i ↦ .ofArrows (Y i) (g i)) =
      Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) := by
  refine le_antisymm ?_ (fun _ _ ⟨p⟩ ↦ ⟨p.1, _, ⟨p.2⟩⟩)
  rintro W u ⟨i, v, ⟨j⟩⟩
  exact ⟨Sigma.mk i j⟩

/-- Compose a presieve on the right with a morphism. -/
def pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) : Presieve Y :=
  fun Z fg ↦ ∃ (g : Z ⟶ X), g ≫ f = fg ∧ R g

@[grind .]
lemma pushforward_apply_comp {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩

lemma pushforward_ofArrows {ι : Type*} {U : ι → C} {X Y : C} (g : ∀ i, U i ⟶ X)
    (f : X ⟶ Y) : (ofArrows _ g).pushforward f = ofArrows _ (g · ≫ f) := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨u, rfl, ⟨i⟩⟩
    exact ⟨i⟩
  · rw [ofArrows_le_iff]
    intro i
    use g i, rfl
    exact ⟨i⟩

lemma pushforward_singleton {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (singleton f).pushforward g = .singleton (f ≫ g) := by
  rw [← ofArrows_pUnit.{0}, pushforward_ofArrows, ofArrows_pUnit.{0}]

/-- The pullback of a presieve `R` on `Y` along a morphism `f : X ⟶ Y` is the presieve on `X`
given by all morphisms `g : Z ⟶ X` such that `g ≫ f` is in `R`. -/
def pullback {X Y : C} (f : X ⟶ Y) (R : Presieve Y) : Presieve X :=
  fun _ g ↦ R (g ≫ f)

variable {f} in
@[simp, grind =]
lemma pullback_iff {R : Presieve X} {Z : C} {g : Z ⟶ Y} :
    R.pullback f g ↔ R (g ≫ f) :=
  .rfl

lemma pushforward_le_iff_le_pullback (R : Presieve Y) (T : Presieve X) :
    R.pushforward f ≤ T ↔ R ≤ T.pullback f := by
  refine ⟨fun hle Z g hg ↦ hle _ _ (pushforward_apply_comp hg), ?_⟩
  rintro hle Z - ⟨g, rfl, hg⟩
  exact hle _ _ hg

lemma galoisConnection_pushforward_pullback :
    GaloisConnection (pushforward f) (pullback f) :=
  pushforward_le_iff_le_pullback f

lemma monotone_pushforward : Monotone (pushforward f) :=
  (galoisConnection_pushforward_pullback f).monotone_l

lemma monotone_pullback : Monotone (pullback f) :=
  (galoisConnection_pushforward_pullback f).monotone_u

lemma pushforward_pullback_le (R : Presieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection_pushforward_pullback f).l_u_le _

lemma le_pullback_pushforward (R : Presieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection_pushforward_pullback f).le_u_l _

@[simp]
lemma pullback_id (R : Presieve X) : R.pullback (𝟙 X) = R := by
  funext
  simp

lemma pullback_comp (R : Presieve Z) (g : X ⟶ Z) :
    R.pullback (f ≫ g) = (R.pullback g).pullback f := by
  funext
  simp

@[simp]
lemma pushforward_id (R : Presieve X) : R.pushforward (𝟙 X) = R := by
  funext
  simp [pushforward]

lemma pushforward_comp (R : Presieve Y) (g : X ⟶ Z) :
    R.pushforward (f ≫ g) = (R.pushforward f).pushforward g := by
  funext
  simp [pushforward]

/-- Given a presieve `R` on `X`, the predicate `R.HasPairwisePullbacks` means that for all arrows
`f` and `g` in `R`, the pullback of `f` and `g` exists. -/
class HasPairwisePullbacks (R : Presieve X) : Prop where
  /-- For all arrows `f` and `g` in `R`, the pullback of `f` and `g` exists. -/
  has_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g

instance (R : Presieve X) [HasPullbacks C] : R.HasPairwisePullbacks := ⟨fun _ _ ↦ inferInstance⟩

instance {α : Type v₂} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.HasPairwisePullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

section uncurry

variable (s : Presieve X)

/-- Uncurry a presieve to one set over the sigma type. -/
def uncurry : Set (Σ Y, Y ⟶ X) :=
  { u | s u.snd }

@[simp] theorem uncurry_singleton {Y : C} (u : Y ⟶ X) : (singleton u).uncurry = { ⟨Y, u⟩ } := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff, Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor

@[simp] theorem uncurry_pullbackArrows [HasPullbacks C] {B : C} (b : B ⟶ X) :
    (pullbackArrows b s).uncurry =
      (fun f ↦ ⟨Limits.pullback f.2 b, pullback.snd _ _⟩) '' s.uncurry := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩

@[simp] theorem uncurry_bind (t : ⦃Y : C⦄ → (f : Y ⟶ X) → s f → Presieve Y) :
    (s.bind t).uncurry = ⋃ i ∈ s.uncurry,
      Sigma.map id (fun Z g ↦ (g ≫ i.2 : Z ⟶ X)) '' (t i.2 ‹_›).uncurry := by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨_, _, _, _, hg, rfl⟩

@[simp] theorem uncurry_ofArrows {ι : Type*} (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    (ofArrows Y f).uncurry = Set.range fun i : ι ↦ ⟨_, f i⟩ := by
  ext ⟨Z, v⟩; simp only [Set.mem_range, Sigma.mk.injEq]; constructor
  · rintro ⟨i⟩; exact ⟨_, rfl, HEq.refl _⟩
  · rintro ⟨i, rfl, h⟩; rw [← eq_of_heq h]; exact ⟨i⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma ofArrows_eq_ofArrows_uncurry {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) :
    ofArrows X f = ofArrows _ (fun i : (Presieve.ofArrows X f).uncurry ↦ f i.2.idx) := by
  refine le_antisymm (fun Z g hg ↦ ?_) fun Z g ⟨i⟩ ↦ .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

end uncurry

end Presieve

end CategoryTheory
