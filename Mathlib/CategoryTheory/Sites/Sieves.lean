/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathlib.Order.CompleteLattice
import Mathlib.CategoryTheory.Over
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.Data.Set.Lattice

#align_import category_theory.sites.sieves from "leanprover-community/mathlib"@"239d882c4fb58361ee8b3b39fb2091320edef10a"

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `Sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `Sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

variable {X Y Z : C} (f : Y ⟶ X)

/-- A set of arrows all with codomain `X`. -/
def Presieve (X : C) :=
  ∀ ⦃Y⦄, Set (Y ⟶ X)-- deriving CompleteLattice
#align category_theory.presieve CategoryTheory.Presieve

instance : CompleteLattice (Presieve X) := by
  dsimp [Presieve]
  -- ⊢ CompleteLattice (⦃Y : C⦄ → Set (Y ⟶ X))
  infer_instance
  -- 🎉 no goals

namespace Presieve

noncomputable instance : Inhabited (Presieve X) :=
  ⟨⊤⟩

/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
abbrev diagram (S : Presieve X) : (FullSubcategory fun f : Over X => S f.hom) ⥤ C :=
  fullSubcategoryInclusion _ ⋙ Over.forget X
#align category_theory.presieve.diagram CategoryTheory.Presieve.diagram

/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (fullSubcategoryInclusion _)
#align category_theory.presieve.cocone CategoryTheory.Presieve.cocone

/-- Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h
#align category_theory.presieve.bind CategoryTheory.Presieve.bind

@[simp]
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩
#align category_theory.presieve.bind_comp CategoryTheory.Presieve.bind_comp

-- porting note: it seems the definition of `Presieve` must be unfolded in order to define
--   this inductive type, it was thus renamed `singleton'`
-- Note we can't make this into `HasSingleton` because of the out-param.
/-- The singleton presieve.  -/
inductive singleton' : ⦃Y : C⦄ → (Y ⟶ X) → Prop
  | mk : singleton' f

/-- The singleton presieve.  -/
def singleton : Presieve X := singleton' f

lemma singleton.mk {f : Y ⟶ X} : singleton f f := singleton'.mk

#align category_theory.presieve.singleton CategoryTheory.Presieve.singleton

@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  -- ⊢ singleton f g → f = g
  · rintro ⟨a, rfl⟩
    -- ⊢ f = f
    rfl
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ singleton f f
    apply singleton.mk
    -- 🎉 no goals
#align category_theory.presieve.singleton_eq_iff_domain CategoryTheory.Presieve.singleton_eq_iff_domain

theorem singleton_self : singleton f f :=
  singleton.mk
#align category_theory.presieve.singleton_self CategoryTheory.Presieve.singleton_self

/-- Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `Sieve.pullback`, but there is a relation between them
in `pullbackArrows_comm`.
-/
inductive pullbackArrows [HasPullbacks C] (R : Presieve X) : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) : R h → pullbackArrows _ (pullback.snd : pullback h f ⟶ Y)
#align category_theory.presieve.pullback_arrows CategoryTheory.Presieve.pullbackArrows

theorem pullback_singleton [HasPullbacks C] (g : Z ⟶ X) :
    pullbackArrows f (singleton g) = singleton (pullback.snd : pullback g f ⟶ _) := by
  funext W
  -- ⊢ pullbackArrows f (singleton g) = singleton pullback.snd
  ext h
  -- ⊢ h ∈ pullbackArrows f (singleton g) ↔ h ∈ singleton pullback.snd
  constructor
  -- ⊢ h ∈ pullbackArrows f (singleton g) → h ∈ singleton pullback.snd
  · rintro ⟨W, _, _, _⟩
    -- ⊢ pullback.snd ∈ singleton pullback.snd
    exact singleton.mk
    -- 🎉 no goals
  · rintro ⟨_⟩
    -- ⊢ pullback.snd ∈ pullbackArrows f (singleton g)
    exact pullbackArrows.mk Z g singleton.mk
    -- 🎉 no goals
#align category_theory.presieve.pullback_singleton CategoryTheory.Presieve.pullback_singleton

/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
inductive ofArrows {ι : Type*} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : ofArrows _ _ (f i)
#align category_theory.presieve.of_arrows CategoryTheory.Presieve.ofArrows

theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit => f) = singleton f := by
  funext Y
  -- ⊢ (ofArrows (fun x => Y✝) fun x => f) = singleton f
  ext g
  -- ⊢ (g ∈ ofArrows (fun x => Y✝) fun x => f) ↔ g ∈ singleton f
  constructor
  -- ⊢ (g ∈ ofArrows (fun x => Y✝) fun x => f) → g ∈ singleton f
  · rintro ⟨_⟩
    -- ⊢ f ∈ singleton f
    apply singleton.mk
    -- 🎉 no goals
  · rintro ⟨_⟩
    -- ⊢ f ∈ ofArrows (fun x => Y✝) fun x => f
    exact ofArrows.mk PUnit.unit
    -- 🎉 no goals
#align category_theory.presieve.of_arrows_punit CategoryTheory.Presieve.ofArrows_pUnit

theorem ofArrows_pullback [HasPullbacks C] {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X) :
    (ofArrows (fun i => pullback (g i) f) fun i => pullback.snd) =
      pullbackArrows f (ofArrows Z g) := by
  funext T
  -- ⊢ (ofArrows (fun i => pullback (g i) f) fun i => pullback.snd) = pullbackArrow …
  ext h
  -- ⊢ (h ∈ ofArrows (fun i => pullback (g i) f) fun i => pullback.snd) ↔ h ∈ pullb …
  constructor
  -- ⊢ (h ∈ ofArrows (fun i => pullback (g i) f) fun i => pullback.snd) → h ∈ pullb …
  · rintro ⟨hk⟩
    -- ⊢ pullback.snd ∈ pullbackArrows f (ofArrows Z g)
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
    -- 🎉 no goals
  · rintro ⟨W, k, hk₁⟩
    -- ⊢ pullback.snd ∈ ofArrows (fun i => pullback (g i) f) fun i => pullback.snd
    cases' hk₁ with i hi
    -- ⊢ pullback.snd ∈ ofArrows (fun i => pullback (g i) f) fun i => pullback.snd
    apply ofArrows.mk
    -- 🎉 no goals
#align category_theory.presieve.of_arrows_pullback CategoryTheory.Presieve.ofArrows_pullback

theorem ofArrows_bind {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    (j : ∀ ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f → Type*) (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C)
    (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((ofArrows Z g).bind fun Y f H => ofArrows (W f H) (k f H)) =
      ofArrows (fun i : Σi, j _ (ofArrows.mk i) => W (g i.1) _ i.2) fun ij =>
        k (g ij.1) _ ij.2 ≫ g ij.1 := by
  funext Y
  -- ⊢ (bind (ofArrows Z g) fun Y f H => ofArrows (W f H) (k f H)) = ofArrows (fun  …
  ext f
  -- ⊢ (f ∈ bind (ofArrows Z g) fun Y f H => ofArrows (W f H) (k f H)) ↔ f ∈ ofArro …
  constructor
  -- ⊢ (f ∈ bind (ofArrows Z g) fun Y f H => ofArrows (W f H) (k f H)) → f ∈ ofArro …
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    -- ⊢ k (g i) (_ : ofArrows Z g (g i)) i' ≫ g i ∈ ofArrows (fun i => W (g i.fst) ( …
    exact ofArrows.mk (Sigma.mk _ _)
    -- 🎉 no goals
  · rintro ⟨i⟩
    -- ⊢ k (g i.fst) (_ : ofArrows Z g (g i.fst)) i.snd ≫ g i.fst ∈ bind (ofArrows Z  …
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)
    -- 🎉 no goals
#align category_theory.presieve.of_arrows_bind CategoryTheory.Presieve.ofArrows_bind

/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)
#align category_theory.presieve.functor_pullback CategoryTheory.Presieve.functorPullback

@[simp]
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl
#align category_theory.presieve.functor_pullback_mem CategoryTheory.Presieve.functorPullback_mem

@[simp]
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl
#align category_theory.presieve.functor_pullback_id CategoryTheory.Presieve.functorPullback_id

/-- Given a presieve `R` on `X`, the predicate `R.hasPullbacks` means that for all arrows `f` and
    `g` in `R`, the pullback of `f` and `g` exists. -/
class hasPullbacks (R : Presieve X) : Prop where
  /-- For all arrows `f` and `g` in `R`, the pullback of `f` and `g` exists. -/
  has_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g

instance (R : Presieve X) [HasPullbacks C] : R.hasPullbacks := ⟨fun _ _ ↦ inferInstance⟩

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/-- Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g
#align category_theory.presieve.functor_pushforward CategoryTheory.Presieve.functorPushforward

--porting note: removed @[nolint hasNonemptyInstance]
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
#align category_theory.presieve.functor_pushforward_structure CategoryTheory.Presieve.FunctorPushforwardStructure

/-- The fixed choice of a preimage. -/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  -- ⊢ FunctorPushforwardStructure F S f
  exact ⟨Z, f', g, h₁, h⟩
  -- 🎉 no goals
#align category_theory.presieve.get_functor_pushforward_structure CategoryTheory.Presieve.getFunctorPushforwardStructure

theorem functorPushforward_comp (R : Presieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  funext x
  -- ⊢ functorPushforward (F ⋙ G) R = functorPushforward G (functorPushforward F R)
  ext f
  -- ⊢ f ∈ functorPushforward (F ⋙ G) R ↔ f ∈ functorPushforward G (functorPushforw …
  constructor
  -- ⊢ f ∈ functorPushforward (F ⋙ G) R → f ∈ functorPushforward G (functorPushforw …
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    -- ⊢ g₁ ≫ (F ⋙ G).map f₁ ∈ functorPushforward G (functorPushforward F R)
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
    -- 🎉 no goals
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    -- ⊢ g₁ ≫ G.map (g₂ ≫ F.map f₂) ∈ functorPushforward (F ⋙ G) R
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩
    -- 🎉 no goals
#align category_theory.presieve.functor_pushforward_comp CategoryTheory.Presieve.functorPushforward_comp

theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩
                    -- 🎉 no goals
#align category_theory.presieve.image_mem_functor_pushforward CategoryTheory.Presieve.image_mem_functorPushforward

end FunctorPushforward

end Presieve

/--
For an object `X` of a category `C`, a `Sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  /-- the underlying presieve -/
  arrows : Presieve X
  /-- stability by precomposition -/
  downward_closed : ∀ {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)
#align category_theory.sieve CategoryTheory.Sieve

attribute [pp_dot] Sieve.arrows

namespace Sieve

instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows → apply)

variable {S R : Sieve X}

attribute [simp] downward_closed

theorem arrows_ext : ∀ {R S : Sieve X}, R.arrows = S.arrows → R = S := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  -- ⊢ { arrows := arrows✝, downward_closed := downward_closed✝¹ } = { arrows := {  …
  rfl
  -- 🎉 no goals
#align category_theory.sieve.arrows_ext CategoryTheory.Sieve.arrows_ext

@[ext]
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun _ => funext fun f => propext <| h f
#align category_theory.sieve.ext CategoryTheory.Sieve.ext

protected theorem ext_iff {R S : Sieve X} : R = S ↔ ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f :=
  ⟨fun h _ _ => h ▸ Iff.rfl, Sieve.ext⟩
#align category_theory.sieve.ext_iff CategoryTheory.Sieve.ext_iff

open Lattice

/-- The supremum of a collection of sieves: the union of them all. -/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X
    where
  arrows Y := { f | ∃ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    -- ⊢ setOf (fun f => ∃ S, S ∈ 𝒮 ∧ S.arrows f) (x✝ ≫ f)
    exact ⟨S, hS, S.downward_closed hf _⟩
    -- 🎉 no goals
#align category_theory.sieve.Sup CategoryTheory.Sieve.sup

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X
    where
  arrows _ := { f | ∀ S ∈ 𝒮, Sieve.arrows S f }
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g
#align category_theory.sieve.Inf CategoryTheory.Sieve.inf

/-- The union of two sieves is a sieve. -/
protected def union (S R : Sieve X) : Sieve X
    where
  arrows Y f := S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]
                        -- ⊢ S.arrows (g ≫ f✝) ∨ R.arrows (g ≫ f✝)
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
#align category_theory.sieve.union CategoryTheory.Sieve.union

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : Sieve X) : Sieve X
    where
  arrows Y f := S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    -- ⊢ S.arrows (g ≫ f✝) ∧ R.arrows (g ≫ f✝)
    simp [h₁, h₂]
    -- 🎉 no goals
#align category_theory.sieve.inter CategoryTheory.Sieve.inter

/-- Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
instance : CompleteLattice (Sieve X)
    where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl S f q := id
  le_trans S₁ S₂ S₃ S₁₂ S₂₃ Y f h := S₂₃ _ (S₁₂ _ h)
  le_antisymm S R p q := Sieve.ext fun Y f => ⟨p _, q _⟩
  top :=
    { arrows := fun _ => Set.univ
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := fun _ => ∅
      downward_closed := False.elim }
  sup := Sieve.union
  inf := Sieve.inter
  sSup := Sieve.sup
  sInf := Sieve.inf
  le_sSup 𝒮 S hS Y f hf := ⟨S, hS, hf⟩
  sSup_le := fun s a ha Y f ⟨b, hb, hf⟩ => (ha b hb) _ hf
  sInf_le _ _ hS _ _ h := h _ hS
  le_sInf _ _ hS _ _ hf _ hR := hS _ hR _ hf
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ h₁ h₂ _ f := by--ℰ S hS Y f := by
    rintro (hf | hf)
    -- ⊢ x✝¹.arrows f
    · exact h₁ _ hf
      -- 🎉 no goals
    · exact h₂ _ hf
      -- 🎉 no goals
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim

/-- The maximal sieve always exists. -/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩
#align category_theory.sieve.sieve_inhabited CategoryTheory.Sieve.sieveInhabited

@[simp]
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ ∀ (S : Sieve X) (_ : S ∈ Ss), S f :=
  Iff.rfl
#align category_theory.sieve.Inf_apply CategoryTheory.Sieve.sInf_apply

@[simp]
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ ∃ (S : Sieve X) (_ : S ∈ Ss), S f := by
  simp [sSup, Sieve.sup, setOf]
  -- 🎉 no goals
#align category_theory.sieve.Sup_apply CategoryTheory.Sieve.sSup_apply

@[simp]
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl
#align category_theory.sieve.inter_apply CategoryTheory.Sieve.inter_apply

@[simp]
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl
#align category_theory.sieve.union_apply CategoryTheory.Sieve.union_apply

@[simp]
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial
#align category_theory.sieve.top_apply CategoryTheory.Sieve.top_apply

/-- Generate the smallest sieve containing the given set of arrows. -/
@[simps]
def generate (R : Presieve X) : Sieve X
    where
  arrows Z f := ∃ (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    -- ⊢ ∃ Y_1 h_1 g_1, R g_1 ∧ h_1 ≫ g_1 = h ≫ g ≫ f
    exact ⟨_, h ≫ g, _, hf, by simp⟩
    -- 🎉 no goals
#align category_theory.sieve.generate CategoryTheory.Sieve.generate

/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X
    where
  arrows := S.bind fun Y f h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    -- ⊢ Presieve.bind S (fun Y f h => (R h).arrows) (g ≫ f ≫ h)
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩
    -- 🎉 no goals
#align category_theory.sieve.bind CategoryTheory.Sieve.bind

open Order Lattice

theorem sets_iff_generate (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H Y g hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    -- ⊢ S.arrows (f ≫ g)
    exact S.downward_closed (ss Z hg) f⟩
    -- 🎉 no goals
#align category_theory.sieve.sets_iff_generate CategoryTheory.Sieve.sets_iff_generate

/-- Show that there is a galois insertion (generate, set_over). -/
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) arrows
    where
  gc := sets_iff_generate
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩
#align category_theory.sieve.gi_generate CategoryTheory.Sieve.giGenerate

theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R
#align category_theory.sieve.le_generate CategoryTheory.Sieve.le_generate

@[simp]
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S
#align category_theory.sieve.generate_sieve CategoryTheory.Sieve.generate_sieve

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩
                                       -- 🎉 no goals
#align category_theory.sieve.id_mem_iff_eq_top CategoryTheory.Sieve.id_mem_iff_eq_top

/-- If an arrow set contains a split epi, it generates the maximal sieve. -/
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  -- ⊢ (generate R).arrows (𝟙 X)
  exact ⟨_, section_ f, f, hf, by simp⟩
  -- 🎉 no goals
#align category_theory.sieve.generate_of_contains_is_split_epi CategoryTheory.Sieve.generate_of_contains_isSplitEpi

@[simp]
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)
#align category_theory.sieve.generate_of_singleton_is_split_epi CategoryTheory.Sieve.generate_of_singleton_isSplitEpi

@[simp]
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩
#align category_theory.sieve.generate_top CategoryTheory.Sieve.generate_top

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `Sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y
    where
  arrows Y sl := S (sl ≫ h)
  downward_closed g := by simp [g]
                          -- 🎉 no goals
#align category_theory.sieve.pullback CategoryTheory.Sieve.pullback

@[simp]
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [Sieve.ext_iff]
                                                 -- 🎉 no goals
#align category_theory.sieve.pullback_id CategoryTheory.Sieve.pullback_id

@[simp]
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ _ => id
#align category_theory.sieve.pullback_top CategoryTheory.Sieve.pullback_top

theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [Sieve.ext_iff]
                                                         -- 🎉 no goals
#align category_theory.sieve.pullback_comp CategoryTheory.Sieve.pullback_comp

@[simp]
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [Sieve.ext_iff]
                                                           -- 🎉 no goals
#align category_theory.sieve.pullback_inter CategoryTheory.Sieve.pullback_inter

theorem pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]
  -- 🎉 no goals
#align category_theory.sieve.pullback_eq_top_iff_mem CategoryTheory.Sieve.pullback_eq_top_iff_mem

theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (pullback_eq_top_iff_mem f).1
#align category_theory.sieve.pullback_eq_top_of_mem CategoryTheory.Sieve.pullback_eq_top_of_mem

/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X
    where
  arrows Z gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩
                                                   -- 🎉 no goals
                                                                -- 🎉 no goals
#align category_theory.sieve.pushforward CategoryTheory.Sieve.pushforward

theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩
#align category_theory.sieve.pushforward_apply_comp CategoryTheory.Sieve.pushforward_apply_comp

theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
                                      -- 🎉 no goals
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩
             -- ⊢ y ≫ f = h ∧ R.arrows z
                                        -- 🎉 no goals
#align category_theory.sieve.pushforward_comp CategoryTheory.Sieve.pushforward_comp

theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩
#align category_theory.sieve.galois_connection CategoryTheory.Sieve.galoisConnection

theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u
#align category_theory.sieve.pullback_monotone CategoryTheory.Sieve.pullback_monotone

theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l
#align category_theory.sieve.pushforward_monotone CategoryTheory.Sieve.pushforward_monotone

theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _
#align category_theory.sieve.le_pushforward_pullback CategoryTheory.Sieve.le_pushforward_pullback

theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection f).l_u_le _
#align category_theory.sieve.pullback_pushforward_le CategoryTheory.Sieve.pullback_pushforward_le

theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup
#align category_theory.sieve.pushforward_union CategoryTheory.Sieve.pushforward_union

theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f ≤ bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  -- ⊢ (bind S R).arrows (g ≫ f)
  exact ⟨_, g, f, h, hg, rfl⟩
  -- 🎉 no goals
#align category_theory.sieve.pushforward_le_bind_of_mem CategoryTheory.Sieve.pushforward_le_bind_of_mem

theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h ≤ (bind S R).pullback f := by
  rw [← galoisConnection f]
  -- ⊢ pushforward f (R h) ≤ bind S R
  apply pushforward_le_bind_of_mem
  -- 🎉 no goals
#align category_theory.sieve.le_pullback_bind CategoryTheory.Sieve.le_pullback_bind

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisCoinsertion
  -- ⊢ ∀ (a : Sieve Y), pullback f (pushforward f a) ≤ a
  rintro S Z g ⟨g₁, hf, hg₁⟩
  -- ⊢ S.arrows g
  rw [cancel_mono f] at hf
  -- ⊢ S.arrows g
  rwa [← hf]
  -- 🎉 no goals
#align category_theory.sieve.galois_coinsertion_of_mono CategoryTheory.Sieve.galoisCoinsertionOfMono

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisInsertion
  -- ⊢ ∀ (b : Sieve X), b ≤ pushforward f (pullback f b)
  intro S Z g hg
  -- ⊢ (pushforward f (pullback f S)).arrows g
  refine' ⟨g ≫ section_ f, by simpa⟩
  -- 🎉 no goals
#align category_theory.sieve.galois_insertion_of_is_split_epi CategoryTheory.Sieve.galoisInsertionOfIsSplitEpi

theorem pullbackArrows_comm [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (R : Presieve X) :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f := by
  ext W g
  -- ⊢ (generate (Presieve.pullbackArrows f R)).arrows g ↔ (pullback f (generate R) …
  constructor
  -- ⊢ (generate (Presieve.pullbackArrows f R)).arrows g → (pullback f (generate R) …
  · rintro ⟨_, h, k, hk, rfl⟩
    -- ⊢ (pullback f (generate R)).arrows (h ≫ k)
    cases' hk with W g hg
    -- ⊢ (pullback f (generate R)).arrows (h ≫ pullback.snd)
    change (Sieve.generate R).pullback f (h ≫ pullback.snd)
    -- ⊢ (pullback f (generate R)).arrows (h ≫ pullback.snd)
    rw [Sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    -- ⊢ (generate R).arrows ((h ≫ pullback.fst) ≫ g)
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W hg) (h ≫ pullback.fst)
    -- 🎉 no goals
  · rintro ⟨W, h, k, hk, comm⟩
    -- ⊢ (generate (Presieve.pullbackArrows f R)).arrows g
    exact ⟨_, _, _, Presieve.pullbackArrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩
    -- 🎉 no goals
#align category_theory.sieve.pullback_arrows_comm CategoryTheory.Sieve.pullbackArrows_comm

section Functor

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
If `R` is a sieve, then the `CategoryTheory.Presieve.functorPullback` of `R` is actually a sieve.
-/
@[simps]
def functorPullback (R : Sieve (F.obj X)) : Sieve X
    where
  arrows := Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    -- ⊢ Presieve.functorPullback F R.arrows (g ≫ f)
    unfold Presieve.functorPullback
    -- ⊢ R.arrows (F.map (g ≫ f))
    rw [F.map_comp]
    -- ⊢ R.arrows (F.map g ≫ F.map f)
    exact R.downward_closed hf (F.map g)
    -- 🎉 no goals
#align category_theory.sieve.functor_pullback CategoryTheory.Sieve.functorPullback

@[simp]
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_arrows CategoryTheory.Sieve.functorPullback_arrows

@[simp]
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R := by
  ext
  -- ⊢ (functorPullback (𝟭 C) R).arrows f✝ ↔ R.arrows f✝
  rfl
  -- 🎉 no goals
#align category_theory.sieve.functor_pullback_id CategoryTheory.Sieve.functorPullback_id

theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F := by
  ext
  -- ⊢ (functorPullback (F ⋙ G) R).arrows f✝ ↔ (functorPullback F (functorPullback  …
  rfl
  -- 🎉 no goals
#align category_theory.sieve.functor_pullback_comp CategoryTheory.Sieve.functorPullback_comp

theorem functorPushforward_extend_eq {R : Presieve X} :
    (generate R).arrows.functorPushforward F = R.functorPushforward F := by
  funext Y
  -- ⊢ Presieve.functorPushforward F (generate R).arrows = Presieve.functorPushforw …
  ext f
  -- ⊢ f ∈ Presieve.functorPushforward F (generate R).arrows ↔ f ∈ Presieve.functor …
  constructor
  -- ⊢ f ∈ Presieve.functorPushforward F (generate R).arrows → f ∈ Presieve.functor …
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    -- ⊢ f' ≫ F.map (g' ≫ f'') ∈ Presieve.functorPushforward F R
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
    -- 🎉 no goals
  · rintro ⟨X', g, f', h₁, h₂⟩
    -- ⊢ f ∈ Presieve.functorPushforward F (generate R).arrows
    exact ⟨X', g, f', le_generate R _ h₁, h₂⟩
    -- 🎉 no goals
#align category_theory.sieve.functor_pushforward_extend_eq CategoryTheory.Sieve.functorPushforward_extend_eq

/-- The sieve generated by the image of `R` under `F`. -/
@[simps]
def functorPushforward (R : Sieve X) : Sieve (F.obj X)
    where
  arrows := R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    -- ⊢ Presieve.functorPushforward F R.arrows (g ≫ f)
    obtain ⟨X, α, β, hα, rfl⟩ := h
    -- ⊢ Presieve.functorPushforward F R.arrows (g ≫ β ≫ F.map α)
    exact ⟨X, α, g ≫ β, hα, by simp⟩
    -- 🎉 no goals
#align category_theory.sieve.functor_pushforward CategoryTheory.Sieve.functorPushforward

@[simp]
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R := by
  ext X f
  -- ⊢ (functorPushforward (𝟭 C) R).arrows f ↔ R.arrows f
  constructor
  -- ⊢ (functorPushforward (𝟭 C) R).arrows f → R.arrows f
  · intro hf
    -- ⊢ R.arrows f
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    -- ⊢ R.arrows (h ≫ (𝟭 C).map g)
    exact R.downward_closed hg h
    -- 🎉 no goals
  · intro hf
    -- ⊢ (functorPushforward (𝟭 C) R).arrows f
    exact ⟨X, f, 𝟙 _, hf, by simp⟩
    -- 🎉 no goals
#align category_theory.sieve.functor_pushforward_id CategoryTheory.Sieve.functorPushforward_id

theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  ext
  -- ⊢ (functorPushforward (F ⋙ G) R).arrows f✝ ↔ (functorPushforward G (functorPus …
  simp [R.arrows.functorPushforward_comp F G]
  -- 🎉 no goals
#align category_theory.sieve.functor_pushforward_comp CategoryTheory.Sieve.functorPushforward_comp

theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  intro R S
  -- ⊢ functorPushforward F R ≤ S ↔ R ≤ functorPullback F S
  constructor
  -- ⊢ functorPushforward F R ≤ S → R ≤ functorPullback F S
  · intro hle X f hf
    -- ⊢ (functorPullback F S).arrows f
    apply hle
    -- ⊢ (functorPushforward F R).arrows (F.map f)
    refine' ⟨X, f, 𝟙 _, hf, _⟩
    -- ⊢ F.map f = 𝟙 (F.obj X) ≫ F.map f
    rw [id_comp]
    -- 🎉 no goals
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    -- ⊢ S.arrows (h ≫ F.map g)
    apply Sieve.downward_closed S
    -- ⊢ S.arrows (F.map g)
    exact hle g hg
    -- 🎉 no goals
#align category_theory.sieve.functor_galois_connection CategoryTheory.Sieve.functor_galoisConnection

theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galoisConnection F X).monotone_u
#align category_theory.sieve.functor_pullback_monotone CategoryTheory.Sieve.functorPullback_monotone

theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l
#align category_theory.sieve.functor_pushforward_monotone CategoryTheory.Sieve.functorPushforward_monotone

theorem le_functorPushforward_pullback (R : Sieve X) :
    R ≤ (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _
#align category_theory.sieve.le_functor_pushforward_pullback CategoryTheory.Sieve.le_functorPushforward_pullback

theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F ≤ R :=
  (functor_galoisConnection F X).l_u_le _
#align category_theory.sieve.functor_pullback_pushforward_le CategoryTheory.Sieve.functorPullback_pushforward_le

theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup
#align category_theory.sieve.functor_pushforward_union CategoryTheory.Sieve.functorPushforward_union

theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_union CategoryTheory.Sieve.functorPullback_union

theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl
#align category_theory.sieve.functor_pullback_inter CategoryTheory.Sieve.functorPullback_inter

@[simp]
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot
#align category_theory.sieve.functor_pushforward_bot CategoryTheory.Sieve.functorPushforward_bot

@[simp]
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ := by
  refine' (generate_sieve _).symm.trans _
  -- ⊢ generate (functorPushforward F ⊤).arrows = ⊤
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  -- ⊢ (functorPushforward F ⊤).arrows (𝟙 (F.obj X))
  refine' ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩
  -- 🎉 no goals
#align category_theory.sieve.functor_pushforward_top CategoryTheory.Sieve.functorPushforward_top

@[simp]
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl
#align category_theory.sieve.functor_pullback_bot CategoryTheory.Sieve.functorPullback_bot

@[simp]
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl
#align category_theory.sieve.functor_pullback_top CategoryTheory.Sieve.functorPullback_top

theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩
                    -- 🎉 no goals
#align category_theory.sieve.image_mem_functor_pushforward CategoryTheory.Sieve.image_mem_functorPushforward

/-- When `F` is essentially surjective and full, the galois connection is a galois insertion. -/
def essSurjFullFunctorGaloisInsertion [EssSurj F] [Full F] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisInsertion
  -- ⊢ ∀ (b : Sieve (F.obj X)), b ≤ functorPushforward F (functorPullback F b)
  intro S Y f hf
  -- ⊢ (functorPushforward F (functorPullback F S)).arrows f
  refine' ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, _⟩
  -- ⊢ (functorPullback F S).arrows (F.preimage ((Functor.objObjPreimageIso F Y).ho …
  simpa using S.downward_closed hf _
  -- 🎉 no goals
#align category_theory.sieve.ess_surj_full_functor_galois_insertion CategoryTheory.Sieve.essSurjFullFunctorGaloisInsertion

/-- When `F` is fully faithful, the galois connection is a galois coinsertion. -/
def fullyFaithfulFunctorGaloisCoinsertion [Full F] [Faithful F] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  -- ⊢ ∀ (a : Sieve X), functorPullback F (functorPushforward F a) ≤ a
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  -- ⊢ S.arrows f
  rw [← F.image_preimage h, ← F.map_comp] at h₂
  -- ⊢ S.arrows f
  rw [F.map_injective h₂]
  -- ⊢ S.arrows (F.preimage h ≫ g)
  exact S.downward_closed h₁ _
  -- 🎉 no goals
#align category_theory.sieve.fully_faithful_functor_galois_coinsertion CategoryTheory.Sieve.fullyFaithfulFunctorGaloisCoinsertion

end Functor

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁
    where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f g := ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩
#align category_theory.sieve.functor CategoryTheory.Sieve.functor

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.functor ⟶ T.functor where app Y f := ⟨f.1, h _ f.2⟩
#align category_theory.sieve.nat_trans_of_le CategoryTheory.Sieve.natTransOfLe

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where app Y f := f.1
#align category_theory.sieve.functor_inclusion CategoryTheory.Sieve.functorInclusion

theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl
#align category_theory.sieve.nat_trans_of_le_comm CategoryTheory.Sieve.natTransOfLe_comm

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun f g h => by
    ext Y y
    -- ⊢ NatTrans.app f Y y = NatTrans.app g Y y
    simpa [Subtype.ext_iff_val] using congr_fun (NatTrans.congr_app h Y) y⟩
    -- 🎉 no goals
#align category_theory.sieve.functor_inclusion_is_mono CategoryTheory.Sieve.functorInclusion_is_mono

-- TODO: Show that when `f` is mono, this is right inverse to `functorInclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functorInclusion`, shown in `sieveOfSubfunctor_functorInclusion`.
-/
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X
    where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    -- ⊢ ∃ t_1, NatTrans.app f (Opposite.op Z) t_1 = g ≫ NatTrans.app f (Opposite.op  …
    refine' ⟨R.map g.op t, _⟩
    -- ⊢ NatTrans.app f (Opposite.op Z) (R.map g.op t) = g ≫ NatTrans.app f (Opposite …
    rw [FunctorToTypes.naturality _ _ f]
    -- ⊢ (yoneda.obj X).map g.op (NatTrans.app f (Opposite.op Y) t) = g ≫ NatTrans.ap …
    simp
    -- 🎉 no goals
#align category_theory.sieve.sieve_of_subfunctor CategoryTheory.Sieve.sieveOfSubfunctor

theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  -- ⊢ (sieveOfSubfunctor (functorInclusion S)).arrows f✝ ↔ S.arrows f✝
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  -- ⊢ (∃ t, ↑t = f✝) ↔ S.arrows f✝
  constructor
  -- ⊢ (∃ t, ↑t = f✝) → S.arrows f✝
  · rintro ⟨⟨f, hf⟩, rfl⟩
    -- ⊢ S.arrows ↑{ val := f, property := hf }
    exact hf
    -- 🎉 no goals
  · intro hf
    -- ⊢ ∃ t, ↑t = f✝
    exact ⟨⟨_, hf⟩, rfl⟩
    -- 🎉 no goals
#align category_theory.sieve.sieve_of_subfunctor_functor_inclusion CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion

instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun Y a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩
#align category_theory.sieve.functor_inclusion_top_is_iso CategoryTheory.Sieve.functorInclusion_top_isIso

end Sieve

end CategoryTheory
