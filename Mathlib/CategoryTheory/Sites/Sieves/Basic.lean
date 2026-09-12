/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Sieves.Presieve

/-!
# Sieves

For an object `X` of a category `C`, a sieve on `X` is a presieve on `X`, i.e. a predicate on
morphisms with codomain `X`, with the additional property of being closed under precomposition.
Thus a sieve records a collection of arrows into `X` that is stable under passing to further
refinements.

This file develops the basic theory of sieves. It gives `Sieve X` its complete lattice structure
and defines `Sieve.generate`, the smallest sieve containing a presieve. Generation and the
underlying-arrow presieve form a Galois insertion. The file also constructs sieves from indexed
families of arrows or objects, and defines pullback and pushforward along a fixed morphism together
with their Galois connection.

Operations induced by functors between categories are developed in
`Mathlib.CategoryTheory.Sites.Sieves.Functoriality`, while the presheaf associated to a sieve is
developed in `Mathlib.CategoryTheory.Sites.Sieves.Presheaf`.

## Tags

sieve, pullback
-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y Z : C} (f : Y ⟶ X)

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
  isLUB_sSup _ := ⟨fun S hS _ _ hf ↦ ⟨S, hS, hf⟩, fun _ ha _ _ ⟨b, hb, hf⟩ ↦ ha hb _ hf⟩
  isGLB_sInf _ := ⟨fun S hS _ _ h ↦ h _ hS, fun _ hS _ _ hf _ hR ↦ hS hR _ hf⟩
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

@[gcongr]
theorem generate_mono : Monotone (generate : Presieve X → Sieve X) := giGenerate.gc.monotone_l

@[gcongr]
theorem arrows_mono : Monotone (arrows : Sieve X → Presieve X) := giGenerate.gc.monotone_u

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
  convert! S.downward_closed H (inv i)
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
it consists of morphisms `p : Z ⟶ X` such that there exists a morphism `Z ⟶ Y i`
for some `i` (note that this does not depend on `p`, only on the object `Z`). -/
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

@[simp]
lemma ofObjects_id (X : C) : Sieve.ofObjects id X = ⊤ :=
  Sieve.pullback_ofObjects_eq_top _ (𝟙 _)

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

lemma pullback_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve Y) :
    (S.pullback f).arrows = S.arrows.pullback f :=
  rfl

lemma pushforward_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve X) :
    (S.pushforward f).arrows = S.arrows.pushforward f :=
  rfl

lemma generate_pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) :
    generate (R.pushforward f) = (generate R).pushforward f := by
  ext
  grind [generate_apply, Presieve.pushforward, pushforward_apply]


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

lemma Presieve.bind_ofArrows_le_bindOfArrows {ι : Type*} {X : C} (Z : ι → C)
    (f : ∀ i, Z i ⟶ X) (R : ∀ i, Presieve (Z i)) :
    Sieve.bind (Sieve.ofArrows Z f)
      (fun _ _ hg ↦ Sieve.pullback
        (Sieve.ofArrows.h hg) (.generate <| R (Sieve.ofArrows.i hg))) ≤
    Sieve.generate (Presieve.bindOfArrows Z f R) := by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv', ← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

end CategoryTheory
