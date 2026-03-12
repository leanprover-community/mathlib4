/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `Sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the Yoneda embedding of `X`.

## Tags

sieve, pullback
-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {X Y Z : C} (f : Y ⟶ X)

/-- A predicate on arrows with codomain `X`. -/
def Presieve (X : C) :=
  ∀ ⦃Y⦄, (Y ⟶ X) → Prop -- deriving CompleteLattice

instance : CompleteLattice (Presieve X) := by
  dsimp [Presieve]
  infer_instance

@[simp]
lemma top_apply (f : Y ⟶ X) : (⊤ : Presieve X) f :=
  trivial

@[simp]
lemma bot_apply (f : Y ⟶ X) : (⊥ : Presieve X) f ↔ False :=
  .rfl

namespace Presieve

noncomputable instance : Inhabited (Presieve X) :=
  ⟨⊤⟩

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

@[deprecated (since := "2025-08-22")] alias singleton' := singleton

@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk

theorem singleton_self : singleton f f :=
  singleton.mk

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

theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit => f) = singleton f := by
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

/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)

@[simp]
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl

@[simp]
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl

/-- Given a presieve `R` on `X`, the predicate `R.HasPairwisePullbacks` means that for all arrows
`f` and `g` in `R`, the pullback of `f` and `g` exists. -/
class HasPairwisePullbacks (R : Presieve X) : Prop where
  /-- For all arrows `f` and `g` in `R`, the pullback of `f` and `g` exists. -/
  has_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g

@[deprecated (since := "2025-08-28")]
alias hasPullbacks := HasPairwisePullbacks

instance (R : Presieve X) [HasPullbacks C] : R.HasPairwisePullbacks := ⟨fun _ _ ↦ inferInstance⟩

instance {α : Type v₂} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.HasPairwisePullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/-- Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

variable {F} in
lemma functorPushforward_monotone {X : C} :
    Monotone (Presieve.functorPushforward (X := X) F) :=
  fun _ _ hle _ _ ⟨Z, g, u, hg, hf⟩ ↦ ⟨Z, g, u, hle _ _ hg, hf⟩

/-- An auxiliary definition in order to fix the choice of the preimages between various definitions.
-/
structure FunctorPushforwardStructure (S : Presieve X) {Y} (f : Y ⟶ F.obj X) where
  /-- an object in the source category -/
  preobj : C
  /-- a map in the source category which has to be in the presieve -/
  premap : preobj ⟶ X
  /-- the morphism which appear in the factorisation -/
  lift : Y ⟶ F.obj preobj
  /-- the condition that `premap` is in the presieve -/
  cover : S premap
  /-- the factorisation of the morphism -/
  fac : f = lift ≫ F.map premap

/-- The fixed choice of a preimage. -/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩

theorem functorPushforward_comp (R : Presieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  funext x
  ext f
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩

theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩

/-- This presieve generates `functorPushforward`.
See `arrows_generate_map_eq_functorPushforward`. -/
inductive map (s : Presieve X) : Presieve (F.obj X) where
  | of {Y : C} {u : Y ⟶ X} (h : s u) : map s (F.map u)

section

variable {F}

@[grind ←]
lemma map_map {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f) : R.map F (F.map f) :=
  ⟨hf⟩

lemma map_iff {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X} :
    R.map F f ↔ ∃ (Z : C) (h : F.obj Z = Y) (g : Z ⟶ X), R g ∧ F.map g = eqToHom h ≫ f := by
  refine ⟨fun (.of (u := u) hu) ↦ ⟨_, rfl, u, hu, by simp⟩, fun ⟨Z, h, g, hg, heq⟩ ↦ ?_⟩
  subst h
  rw [eqToHom_refl, Category.id_comp] at heq
  simp [← heq, map_map hg]

@[simp]
lemma map_ofArrows {X : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    (ofArrows Y f).map F = ofArrows _ (fun i ↦ F.map (f i)) := by
  refine le_antisymm (fun Z g hg ↦ ?_) fun _ _ ⟨i⟩ ↦ map_map ⟨i⟩
  obtain ⟨hu⟩ := hg
  obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj _ _ hu
  simpa using ofArrows.mk i

@[simp]
lemma map_singleton {X Y : C} (f : X ⟶ Y) : (singleton f).map F = singleton (F.map f) := by
  rw [← ofArrows_pUnit.{_, _, 0}, map_ofArrows, ofArrows_pUnit]

lemma map_le_iff_le_functorPullback {R : Presieve X} {S : Presieve (F.obj X)} :
    R.map F ≤ S ↔ R ≤ S.functorPullback F :=
  ⟨fun h _ _ hf ↦ h _ _ (.of hf), fun h _ f ⟨hu⟩ ↦ h _ _ hu⟩

variable (F) in
lemma galoisConnection_map_functorPullback (X : C) :
    GaloisConnection (Presieve.map F (X := X)) (Presieve.functorPullback F) :=
  fun _ _ ↦ Presieve.map_le_iff_le_functorPullback

lemma map_functorPullback {X : C} (R : Presieve (F.obj X)) : (R.functorPullback F).map F ≤ R :=
  (galoisConnection_map_functorPullback _ _).l_u_le _

lemma le_functorPullback_map {X : C} (R : Presieve X) : R ≤ (R.map F).functorPullback F :=
  (galoisConnection_map_functorPullback _ _).le_u_l _

@[simp]
lemma map_functorPullback_map {X : C} (R : Presieve X) :
    Presieve.map F (Presieve.functorPullback F (R.map F)) = R.map F :=
  (galoisConnection_map_functorPullback _ _).l_u_l_eq_l _

@[simp]
lemma functorPullback_map_functorPullback {X : C} (R : Presieve (F.obj X)) :
    Presieve.functorPullback F (Presieve.map F (R.functorPullback F)) = R.functorPullback F :=
  (galoisConnection_map_functorPullback _ _).u_l_u_eq_u _

@[simp]
lemma map_id {X : C} (R : Presieve X) : R.map (𝟭 C) = R :=
  le_antisymm (fun _ _ ⟨hg⟩ ↦ hg) fun _ _ hg ↦ ⟨hg⟩

lemma map_monotone : Monotone (map (X := X) F) :=
  (galoisConnection_map_functorPullback _ _).monotone_l

lemma functorPullback_monotone {X : C} : Monotone (Presieve.functorPullback (X := X) F) :=
  (Presieve.galoisConnection_map_functorPullback F X).monotone_u

end

end FunctorPushforward

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
    (pullbackArrows b s).uncurry = (fun f ↦ ⟨pullback f.2 b, pullback.snd _ _⟩) '' s.uncurry := by
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

lemma ofArrows_eq_ofArrows_uncurry {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) :
    ofArrows X f = ofArrows _ (fun i : (Presieve.ofArrows X f).uncurry ↦ f i.2.idx) := by
  refine le_antisymm (fun Z g hg ↦ ?_) fun Z g ⟨i⟩ ↦ .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

end uncurry

end Presieve

/--
For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to `X` which is closed
under left-composition.
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  /-- the underlying presieve -/
  arrows : Presieve X
  /-- stability by precomposition -/
  downward_closed : ∀ {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)

namespace Sieve

instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows → apply)

variable {S R : Sieve X}

attribute [simp] downward_closed

theorem arrows_ext : ∀ {R S : Sieve X}, R.arrows = S.arrows → R = S := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

@[ext]
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun _ => funext fun f => propext <| h f

open Lattice

/-- The supremum of a collection of sieves: the union of them all. -/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := ∃ S ∈ 𝒮, Sieve.arrows S f
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := ∀ S ∈ 𝒮, Sieve.arrows S f
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g

/-- The union of two sieves is a sieve. -/
protected def union (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]

/-- Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the Galois insertion for nicer definitional properties.
-/
instance : CompleteLattice (Sieve X) where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl _ _ _ := id
  le_trans _ _ _ S₁₂ S₂₃ _ _ h := S₂₃ _ (S₁₂ _ h)
  le_antisymm _ _ p q := Sieve.ext fun _ _ => ⟨p _, q _⟩
  top :=
    { arrows := ⊤
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := ⊥
      downward_closed := False.elim }
  sup := Sieve.union
  inf := Sieve.inter
  sSup := Sieve.sup
  sInf := Sieve.inf
  le_sSup _ S hS _ _ hf := ⟨S, hS, hf⟩
  sSup_le := fun _ _ ha _ _ ⟨b, hb, hf⟩ => (ha b hb) _ hf
  sInf_le _ _ hS _ _ h := h _ hS
  le_sInf _ _ hS _ _ hf _ hR := hS _ hR _ hf
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ h₁ h₂ _ f := by
    rintro (hf | hf)
    · exact h₁ _ hf
    · exact h₂ _ hf
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim

/-- The maximal sieve always exists. -/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩

@[simp]
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ ∀ (S : Sieve X) (_ : S ∈ Ss), S f :=
  Iff.rfl

@[simp]
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ ∃ (S : Sieve X) (_ : S ∈ Ss), S f := by
  simp [sSup, Sieve.sup]

@[simp]
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl

@[simp]
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl

theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial

@[simp]
theorem bot_apply (f : Y ⟶ X) : (⊥ : Sieve X) f ↔ False :=
  .rfl

@[simp]
lemma arrows_top : (⊤ : Sieve X).arrows = ⊤ := rfl

lemma arrows_eq_top_iff {S : Sieve X} : S.arrows = ⊤ ↔ S = ⊤ :=
  ⟨fun h ↦ arrows_ext (h ▸ arrows_top), fun h ↦ h ▸ arrows_top⟩

@[simp]
lemma arrows_bot : (⊥ : Sieve X).arrows = ⊥ := rfl

lemma arrows_eq_bot_iff {S : Sieve X} : S.arrows = ⊥ ↔ S = ⊥ :=
  ⟨fun h ↦ arrows_ext (h ▸ arrows_bot), fun h ↦ h ▸ arrows_bot⟩

instance : Nontrivial (Sieve X) where
  exists_pair_ne := ⟨⊤, ⊥, fun h ↦ by simp [← bot_apply (𝟙 X), ← h]⟩

/-- Generate the smallest sieve containing the given presieve. -/
@[simps]
def generate (R : Presieve X) : Sieve X where
  arrows Z f := ∃ (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩

theorem arrows_generate_map_eq_functorPushforward {s : Presieve X} :
    (generate (s.map F)).arrows = s.functorPushforward F := by
  refine funext fun Z ↦ funext fun u ↦ propext ⟨?_, ?_⟩
  · rintro ⟨_, _, _, ⟨hu⟩, rfl⟩; exact ⟨_, _, _, hu, rfl⟩
  · rintro ⟨_, _, _, hu, rfl⟩; exact ⟨_, _, _, ⟨hu⟩, rfl⟩

/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X where
  arrows := S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

/-- Structure which contains the data and properties for a morphism `h` satisfying
`Sieve.bind S R h`. -/
abbrev BindStruct (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    {Z : C} (h : Z ⟶ X) :=
  Presieve.BindStruct S (fun _ _ hf ↦ R hf) h

open Order Lattice

theorem generate_le_iff (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z _ hg) f⟩

/-- Show that there is a Galois insertion (generate, underlying presieve). -/
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) arrows where
  gc := generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩

theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R

@[simp]
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S

lemma generate_mono : Monotone (generate : Presieve X → _) :=
  (giGenerate (X := X)).gc.monotone_l

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

/-- If a presieve contains a split epi, it generates the maximal sieve. -/
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)

@[simp]
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩

@[simp]
lemma generate_bot : generate (⊥ : Presieve X) = ⊥ := by
  simp only [eq_bot_iff, generate_le_iff, bot_le]

@[simp]
lemma generate_eq_bot_iff (R : Presieve X) : generate R = ⊥ ↔ R = ⊥ := by
  simp [giGenerate.gc.l_eq_bot]

@[simp]
lemma comp_mem_iff (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) :
    S (i ≫ f) ↔ S f := by
  refine ⟨fun H ↦ ?_, fun H ↦ S.downward_closed H _⟩
  convert S.downward_closed H (inv i)
  simp

section

variable {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X)

/-- The sieve of `X` generated by family of morphisms `Y i ⟶ X`. -/
abbrev ofArrows : Sieve X := generate (Presieve.ofArrows Y f)

lemma ofArrows_mk (i : I) : ofArrows Y f (f i) :=
  ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩

lemma mem_ofArrows_iff {W : C} (g : W ⟶ X) :
    ofArrows Y f g ↔ ∃ (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)

variable {Y f} {W : C} {g : W ⟶ X} (hg : ofArrows Y f g)

include hg in
lemma ofArrows.exists : ∃ (i : I) (h : W ⟶ Y i), g = h ≫ f i := by
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, h, rfl⟩

/-- When `hg : Sieve.ofArrows Y f g`, this is a choice of `i` such that `g`
factors through `f i`. -/
noncomputable def ofArrows.i : I := (ofArrows.exists hg).choose

/-- When `hg : Sieve.ofArrows Y f g`, this is a morphism `h : W ⟶ Y (i hg)` such
that `h ≫ f (i hg) = g`. -/
noncomputable def ofArrows.h : W ⟶ Y (i hg) := (ofArrows.exists hg).choose_spec.choose

@[reassoc (attr := simp)]
lemma ofArrows.fac : h hg ≫ f (i hg) = g :=
  (ofArrows.exists hg).choose_spec.choose_spec.symm

end

/-- The sieve generated by the morphisms in `R.category`
for a presieve `R` is the sieve generated by `R`. -/
lemma ofArrows_category' {S : C} (R : Presieve S) :
    Sieve.ofArrows _ (fun (f : R.category) ↦ f.obj.hom) = generate R := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨f, hf⟩
    exact ⟨_, 𝟙 _, f.hom, hf, by simp⟩
  · rintro _ _ ⟨_, a, b, h, rfl⟩
    exact ⟨_, _, _, .mk (ι := R.category) ⟨Over.mk b, h⟩, rfl⟩

lemma ofArrows_category {S : C} (R : Sieve S) :
    Sieve.ofArrows _ (fun (f : R.arrows.category) ↦ f.obj.hom) = R := by
  rw [ofArrows_category', generate_sieve]

lemma exists_eq_ofArrows (R : Sieve X) :
    ∃ (I : Type max u₁ v₁) (Y : I → C) (f : ∀ i, Y i ⟶ X),
      R = Sieve.ofArrows _ f :=
  ⟨_, _, _, (ofArrows_category R).symm⟩

/-- The sieve generated by two morphisms. -/
abbrev ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X :=
  Sieve.ofArrows (Y := pairFunction U V) (fun k ↦ WalkingPair.casesOn k i j)

/-- The sieve of `X : C` that is generated by a family of objects `Y : I → C`:
it consists of morphisms to `X` which factor through at least one of the `Y i`. -/
def ofObjects {I : Type*} (Y : I → C) (X : C) : Sieve X where
  arrows Z _ := ∃ (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩

lemma mem_ofObjects_iff {I : Type*} (Y : I → C) {Z X : C} (g : Z ⟶ X) :
    ofObjects Y X g ↔ ∃ (i : I), Nonempty (Z ⟶ Y i) := by rfl

lemma ofArrows_le_ofObjects
    {I : Type*} (Y : I → C) {X : C} (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ≤ Sieve.ofObjects Y X := by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩

lemma ofArrows_eq_ofObjects {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = ofObjects Y X := by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff, mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩

lemma ofObjects_mono {I : Type*} {X : I → C} {I' : Type*} {X' : I' → C} {Y : C}
    (h : Set.range X ⊆ Set.range X') :
    Sieve.ofObjects X Y ≤ Sieve.ofObjects X' Y := by
  rintro Z f ⟨i, ⟨g⟩⟩
  obtain ⟨i', h⟩ := h ⟨i, rfl⟩
  exact ⟨i', ⟨h ▸ g⟩⟩

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
as the inverse image of S with `_ ≫ h`. That is, `Sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where
  arrows _ sl := S (sl ≫ h)
  downward_closed g := by simp [g]

@[simp]
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [Sieve.ext_iff]

@[simp]
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ _ => id

theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [Sieve.ext_iff]

@[simp]
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [Sieve.ext_iff]

lemma pullback_ofArrows_of_iso
    {I : Type*} {X : C} (Z : I → C) (f : ∀ i, Z i ⟶ X) {X' : C} (e : X' ≅ X) :
    pullback e.hom (Sieve.ofArrows _ f) =
      Sieve.ofArrows _ (fun i ↦ f i ≫ e.inv) := by
  rw [Sieve.ext_iff]
  intro W a
  constructor
  · rintro ⟨T, b, c, ⟨i⟩, fac⟩
    exact ⟨_, b, _, ⟨i⟩, by simp [reassoc_of% fac]⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, a, _, ⟨i⟩, by simp⟩

theorem mem_iff_pullback_eq_top (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]

theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (mem_iff_pullback_eq_top f).1

lemma pullback_ofObjects_eq_top
    {I : Type*} (Y : I → C) {X : C} {i : I} (g : X ⟶ Y i) :
    ofObjects Y X = ⊤ := by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff]
  exact ⟨i, ⟨h ≫ g⟩⟩

@[simp]
lemma pullback_ofObjects {I : Type*} (X : I → C) {Y Z : C} (f : Z ⟶ Y) :
    (ofObjects X Y).pullback f = ofObjects X Z := by
  ext
  simp [Sieve.ofObjects]

/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where
  arrows _ gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩

theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩

theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩

theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩

theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u

theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l

theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _

theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection f).l_u_le _

theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup

@[simp]
lemma pullback_bot (f : Y ⟶ X) : (⊥ : Sieve X).pullback f = ⊥ :=
  rfl

@[simp]
lemma pushforward_bot (f : Y ⟶ X) : (⊥ : Sieve Y).pushforward f = ⊥ :=
  (galoisConnection f).l_bot

lemma pushforward_eq_bot_iff {f : Y ⟶ X} {S : Sieve Y} : S.pushforward f = ⊥ ↔ S = ⊥ := by
  simp [(galoisConnection f).l_eq_bot]

theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f ≤ bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩

theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h ≤ (bind S R).pullback f := by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩

theorem pullbackArrows_comm {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f] :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f := by
  ext W g
  constructor
  · rintro ⟨_, h, k, ⟨W, g, hg⟩, rfl⟩
    have := R.hasPullback f hg
    rw [Sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W _ hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, comm⟩
    have := R.hasPullback f hk
    exact ⟨_, _, _, Presieve.pullbackArrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩

section Functor

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
If `R` is a sieve, then the `CategoryTheory.Presieve.functorPullback` of `R` is actually a sieve.
-/
@[simps]
def functorPullback (R : Sieve (F.obj X)) : Sieve X where
  arrows := Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl

@[simp]
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R := by
  ext
  rfl

theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F := by
  ext
  rfl

lemma generate_functorPullback_le {X : C} (R : Presieve (F.obj X)) :
     generate (R.functorPullback F) ≤ functorPullback F (generate R) := by
  rw [generate_le_iff]
  intro Z g hg
  exact le_generate _ _ _ hg

lemma functorPullback_pullback {X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) :
    functorPullback F (pullback (F.map f) S) = pullback f (functorPullback F S) := by
  ext
  simp

theorem functorPushforward_extend_eq {R : Presieve X} :
    (generate R).arrows.functorPushforward F = R.functorPushforward F := by
  funext Y
  ext f
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ _ h₁, h₂⟩

/-- The sieve generated by the image of `R` under `F`. -/
@[simps]
def functorPushforward (R : Sieve X) : Sieve (F.obj X) where
  arrows := R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩

theorem generate_map_eq_functorPushforward {s : Presieve X} :
    generate (s.map F) = (generate s).functorPushforward F := by
  ext
  rw [arrows_generate_map_eq_functorPushforward]
  simp [functorPushforward_extend_eq]

@[simp]
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R := by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩

theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  ext
  simp [R.arrows.functorPushforward_comp F G]

theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine ⟨X, f, 𝟙 _, hf, ?_⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply Sieve.downward_closed S
    exact hle g hg

lemma functorPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Sieve (F.obj X)) :
    S.functorPushforward F ≤ R ↔ S ≤ R.functorPullback F :=
  (Sieve.functor_galoisConnection F X).le_iff_le

theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galoisConnection F X).monotone_u

theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l

theorem le_functorPushforward_pullback (R : Sieve X) :
    R ≤ (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _

theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F ≤ R :=
  (functor_galoisConnection F X).l_u_le _

theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup

theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl

theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl

@[simp]
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot

@[simp]
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ := by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl

@[simp]
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl

theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩

lemma functorPushforward_pullback_le {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    (S.pullback f).functorPushforward F ≤ (S.functorPushforward F).pullback (F.map f) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback, Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

/-- When `F` is essentially surjective and full, the Galois connection is a Galois insertion. -/
def essSurjFullFunctorGaloisInsertion [F.EssSurj] [F.Full] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf

/-- When `F` is fully faithful, the Galois connection is a Galois coinsertion. -/
def fullyFaithfulFunctorGaloisCoinsertion [F.Full] [F.Faithful] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h, ← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _

lemma functorPullback_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Faithful] :
    Sieve.functorPullback F (Sieve.functorPushforward F S) = S :=
  (Sieve.fullyFaithfulFunctorGaloisCoinsertion _ _).u_l_eq _

set_option backward.isDefEq.respectTransparency false in
lemma functorPushforward_functor (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.functor = (S.pullback (e.unitInv.app X)).functorPullback e.inverse := by
  ext Y iYX
  constructor
  · rintro ⟨Z, iZX, iYZ, hiZX, rfl⟩
    simpa using S.downward_closed hiZX (e.inverse.map iYZ ≫ e.unitInv.app Z)
  · intro H
    exact ⟨_, e.inverse.map iYX ≫ e.unitInv.app X, e.counitInv.app Y, by simpa using H, by simp⟩

@[simp]
lemma mem_functorPushforward_functor {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X} :
    S.functorPushforward e.functor f ↔ S (e.inverse.map f ≫ e.unitInv.app X) :=
  congr($(S.functorPushforward_functor e).arrows f)

lemma functorPushforward_inverse {X : D} (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.inverse = (S.pullback (e.counit.app X)).functorPullback e.functor :=
  Sieve.functorPushforward_functor S e.symm

@[simp]
lemma mem_functorPushforward_inverse {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X} :
    S.functorPushforward e.inverse f ↔ S (e.functor.map f ≫ e.counit.app X) :=
  congr($(S.functorPushforward_inverse e).arrows f)

variable (e : C ≌ D)

set_option backward.isDefEq.respectTransparency false in
lemma functorPushforward_equivalence_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by ext; simp

set_option backward.isDefEq.respectTransparency false in
lemma pullback_functorPushforward_equivalence_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by ext; simp

lemma mem_functorPushforward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) :
    (R.arrows.functorPushforward F) f ↔ ∃ (g : Y ⟶ X), F.map g = f ∧ R g := by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ ↦ ?_, fun ⟨g, hcomp, hg⟩ ↦ ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]

lemma mem_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful]
    {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.arrows.functorPushforward F) (F.map f) ↔ R f := by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ ↦ ?_, fun hf ↦ ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]

lemma functorPushforward_ofObjects_le
    {I : Type*} (X : I → C) (Y : C) :
    (ofObjects X Y).functorPushforward F ≤ ofObjects (F.obj ∘ X) (F.obj Y) := by
  rintro Z f ⟨W, g₁, g₂, ⟨i, ⟨g₃⟩⟩, hf⟩
  exact ⟨i, ⟨g₂ ≫ F.map g₃⟩⟩

end Functor

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f g := ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.functor ⟶ T.functor where app _ f := ⟨f.1, h _ f.2⟩

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where app _ f := f.1

/-- Any component `f : Y ⟶ X` of the sieve `S` induces a natural transformation from `yoneda.obj Y`
to the presheaf induced by `S`. -/
@[simps]
def toFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : yoneda.obj Y ⟶ S.functor where
  app Z g := ⟨g ≫ f, S.downward_closed hf g⟩

theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff] using congr_fun (NatTrans.congr_app h Y) y⟩

-- TODO: Show that when `f` is mono, this is right inverse to `functorInclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functorInclusion`, shown in `sieveOfSubfunctor_functorInclusion`.
-/
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    rw [FunctorToTypes.naturality _ _ f]
    simp

theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun _ a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩

/-- A variant of `Sieve.functor` with universe lifting. -/
abbrev uliftFunctor (S : Sieve X) : Cᵒᵖ ⥤ Type max w v₁ :=
  S.functor ⋙ CategoryTheory.uliftFunctor

/-- A variant of `Sieve.natTransOfLe` with universe lifting. -/
@[simps]
def uliftNatTransOfLe {S T : Sieve X} (h : S ≤ T) :
    Sieve.uliftFunctor.{w} S ⟶ Sieve.uliftFunctor.{w} T where
  app _ f := ⟨f.down.1, h _ f.down.2⟩

/-- A variant of `Sieve.functorInclusion` with universe lifting. -/
@[simps! app]
def uliftFunctorInclusion (S : Sieve X) :
    S.uliftFunctor ⟶ uliftYoneda.obj.{w} X :=
  Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

/-- A variant of `Sieve.toFunctor` with universe lifting. -/
@[simps]
def toUliftFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) :
    uliftYoneda.obj.{w} Y ⟶ Sieve.uliftFunctor.{w} S where
  app Z g := ⟨g.down ≫ f, S.downward_closed hf g.down⟩

theorem uliftNatTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    uliftNatTransOfLe.{w} h ≫ uliftFunctorInclusion.{w} _ = uliftFunctorInclusion.{w} _ :=
  rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance uliftFunctorInclusion_is_mono (S : Sieve X) :
    Mono (Sieve.uliftFunctorInclusion.{w} S) :=
  ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_fun (NatTrans.congr_app h Y) y⟩

/-- A variant of `Sieve.sieveOfSubfunctor` with universe lifting. -/
@[simps]
def sieveOfUliftSubfunctor {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.obj.{w} X) :
    Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [FunctorToTypes.naturality _ _ f, ht]

theorem sieveOfUliftSubfunctor_uliftFunctorInclusion {S : Sieve X} :
    Sieve.sieveOfUliftSubfunctor.{w} (S.uliftFunctorInclusion) = S := by
  cat_disch

instance uliftFunctorInclusion_top_isIso : IsIso (Sieve.uliftFunctorInclusion.{w} (⊤ : Sieve X)) :=
  ⟨⟨{ app := fun _ a => ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩

lemma ofArrows_eq_pullback_of_isPullback {ι : Type*} {S : C} {X : ι → C} (f : (i : ι) → X i ⟶ S)
    {Y : C} {g : Y ⟶ S} {P : ι → C} {p₁ : (i : ι) → P i ⟶ Y} {p₂ : (i : ι) → P i ⟶ X i}
    (h : ∀ (i : ι), IsPullback (p₁ i) (p₂ i) g (f i)) :
    Sieve.ofArrows P p₁ = Sieve.pullback g (Sieve.ofArrows X f) := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    use X i, p₂ i, f i, ⟨i⟩
    exact (h i).w.symm
  · rintro W u ⟨Z, v, s, ⟨i⟩, heq⟩
    use P i, (h i).lift u v heq.symm, p₁ i, ⟨i⟩
    simp

end Sieve

lemma Presieve.functorPullback_arrows {X : C} (S : Sieve (F.obj X)) :
    Presieve.functorPullback F S.arrows = Sieve.functorPullback F S :=
  rfl

lemma Presieve.bind_ofArrows_le_bindOfArrows {ι : Type*} {X : C} (Z : ι → C)
    (f : ∀ i, Z i ⟶ X) (R : ∀ i, Presieve (Z i)) :
    Sieve.bind (Sieve.ofArrows Z f)
      (fun _ _ hg ↦ Sieve.pullback
        (Sieve.ofArrows.h hg) (.generate <| R (Sieve.ofArrows.i hg))) ≤
    Sieve.generate (Presieve.bindOfArrows Z f R) := by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv', ← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

lemma Presieve.functorPushforward_overForget
    {S : C} {X : Over S} (R : Presieve X) :
    Presieve.functorPushforward (Over.forget S) R =
      (Sieve.generate (Presieve.map (Over.forget S) R)).arrows :=
  (Sieve.arrows_generate_map_eq_functorPushforward (Over.forget S)).symm

end CategoryTheory
