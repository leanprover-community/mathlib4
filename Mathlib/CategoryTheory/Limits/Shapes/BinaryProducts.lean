/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import category_theory.limits.shapes.binary_products from "leanprover-community/mathlib"@"fec1d95fc61c750c1ddbb5b1f7f48b8e811a80d7"

/-!
# Binary (co)products

We define a category `WalkingPair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/


noncomputable section

universe v u u₂

open CategoryTheory

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited
#align category_theory.limits.walking_pair CategoryTheory.Limits.WalkingPair

open WalkingPair

/-- The equivalence swapping left and right.
-/
def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun j := WalkingPair.recOn j right left
  invFun j := WalkingPair.recOn j right left
  left_inv j := by cases j; repeat rfl
  right_inv j := by cases j; repeat rfl
#align category_theory.limits.walking_pair.swap CategoryTheory.Limits.WalkingPair.swap

@[simp]
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl
#align category_theory.limits.walking_pair.swap_apply_left CategoryTheory.Limits.WalkingPair.swap_apply_left

@[simp]
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl
#align category_theory.limits.walking_pair.swap_apply_right CategoryTheory.Limits.WalkingPair.swap_apply_right

@[simp]
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl
#align category_theory.limits.walking_pair.swap_symm_apply_tt CategoryTheory.Limits.WalkingPair.swap_symm_apply_tt

@[simp]
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl
#align category_theory.limits.walking_pair.swap_symm_apply_ff CategoryTheory.Limits.WalkingPair.swap_symm_apply_ff

/-- An equivalence from `WalkingPair` to `Bool`, sometimes useful when reindexing limits.
-/
def WalkingPair.equivBool : WalkingPair ≃ Bool where
  toFun j := WalkingPair.recOn j true false
  -- to match equiv.sum_equiv_sigma_bool
  invFun b := Bool.recOn b right left
  left_inv j := by cases j; repeat rfl
  right_inv b := by cases b; repeat rfl
#align category_theory.limits.walking_pair.equiv_bool CategoryTheory.Limits.WalkingPair.equivBool

@[simp]
theorem WalkingPair.equivBool_apply_left : WalkingPair.equivBool left = true :=
  rfl
#align category_theory.limits.walking_pair.equiv_bool_apply_left CategoryTheory.Limits.WalkingPair.equivBool_apply_left

@[simp]
theorem WalkingPair.equivBool_apply_right : WalkingPair.equivBool right = false :=
  rfl
#align category_theory.limits.walking_pair.equiv_bool_apply_right CategoryTheory.Limits.WalkingPair.equivBool_apply_right

@[simp]
theorem WalkingPair.equivBool_symm_apply_true : WalkingPair.equivBool.symm true = left :=
  rfl
#align category_theory.limits.walking_pair.equiv_bool_symm_apply_tt CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_true

@[simp]
theorem WalkingPair.equivBool_symm_apply_false : WalkingPair.equivBool.symm false = right :=
  rfl
#align category_theory.limits.walking_pair.equiv_bool_symm_apply_ff CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_false

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y
#align category_theory.limits.pair_function CategoryTheory.Limits.pairFunction

@[simp]
theorem pairFunction_left (X Y : C) : pairFunction X Y left = X :=
  rfl
#align category_theory.limits.pair_function_left CategoryTheory.Limits.pairFunction_left

@[simp]
theorem pairFunction_right (X Y : C) : pairFunction X Y right = Y :=
  rfl
#align category_theory.limits.pair_function_right CategoryTheory.Limits.pairFunction_right

variable [Category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y
#align category_theory.limits.pair CategoryTheory.Limits.pair

@[simp]
theorem pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X :=
  rfl
#align category_theory.limits.pair_obj_left CategoryTheory.Limits.pair_obj_left

@[simp]
theorem pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y :=
  rfl
#align category_theory.limits.pair_obj_right CategoryTheory.Limits.pair_obj_right

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩)
  (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- The natural transformation between two functors out of the
 walking pair, specified by its components. -/
def mapPair : F ⟶ G where
  app j := Discrete.recOn j fun j => WalkingPair.casesOn j f g
  naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by aesop_cat
#align category_theory.limits.map_pair CategoryTheory.Limits.mapPair

@[simp]
theorem mapPair_left : (mapPair f g).app ⟨left⟩ = f :=
  rfl
#align category_theory.limits.map_pair_left CategoryTheory.Limits.mapPair_left

@[simp]
theorem mapPair_right : (mapPair f g).app ⟨right⟩ = g :=
  rfl
#align category_theory.limits.map_pair_right CategoryTheory.Limits.mapPair_right

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps!]
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j => Discrete.recOn j fun j => WalkingPair.casesOn j f g)
    (fun ⟨⟨u⟩⟩ => by aesop_cat)
#align category_theory.limits.map_pair_iso CategoryTheory.Limits.mapPairIso

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps!]
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) :
    F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)
#align category_theory.limits.diagram_iso_pair CategoryTheory.Limits.diagramIsoPair

section

variable {D : Type u} [Category.{v} D]

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _
#align category_theory.limits.pair_comp CategoryTheory.Limits.pairComp

end

/-- A binary fan is just a cone on a diagram indexing a product. -/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)
#align category_theory.limits.binary_fan CategoryTheory.Limits.BinaryFan

/-- The first projection of a binary fan. -/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩
#align category_theory.limits.binary_fan.fst CategoryTheory.Limits.BinaryFan.fst

/-- The second projection of a binary fan. -/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩
#align category_theory.limits.binary_fan.snd CategoryTheory.Limits.BinaryFan.snd

@[simp]
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl
#align category_theory.limits.binary_fan.π_app_left CategoryTheory.Limits.BinaryFan.π_app_left

@[simp]
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl
#align category_theory.limits.binary_fan.π_app_right CategoryTheory.Limits.BinaryFan.π_app_right

/-- A convenient way to show that a binary fan is a limit. -/
def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y)
    (lift : ∀ {T : C} (_ : T ⟶ X) (_ : T ⟶ Y), T ⟶ s.pt)
    (hl₁ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.fst = f)
    (hl₂ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.snd = g)
    (uniq :
      ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt) (_ : m ≫ s.fst = f) (_ : m ≫ s.snd = g),
        m = lift f g) :
    IsLimit s :=
  Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun t m h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)
#align category_theory.limits.binary_fan.is_limit.mk CategoryTheory.Limits.BinaryFan.IsLimit.mk

theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂
#align category_theory.limits.binary_fan.is_limit.hom_ext CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
abbrev BinaryCofan (X Y : C) := Cocone (pair X Y)
#align category_theory.limits.binary_cofan CategoryTheory.Limits.BinaryCofan

/-- The first inclusion of a binary cofan. -/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.left⟩
#align category_theory.limits.binary_cofan.inl CategoryTheory.Limits.BinaryCofan.inl

/-- The second inclusion of a binary cofan. -/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩
#align category_theory.limits.binary_cofan.inr CategoryTheory.Limits.BinaryCofan.inr

@[simp]
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.left⟩ = s.inl := rfl
#align category_theory.limits.binary_cofan.ι_app_left CategoryTheory.Limits.BinaryCofan.ι_app_left

@[simp]
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.right⟩ = s.inr := rfl
#align category_theory.limits.binary_cofan.ι_app_right CategoryTheory.Limits.BinaryCofan.ι_app_right

/-- A convenient way to show that a binary cofan is a colimit. -/
def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y)
    (desc : ∀ {T : C} (_ : X ⟶ T) (_ : Y ⟶ T), s.pt ⟶ T)
    (hd₁ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inl ≫ desc f g = f)
    (hd₂ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inr ≫ desc f g = g)
    (uniq :
      ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶ T) (_ : s.inl ≫ m = f) (_ : s.inr ≫ m = g),
        m = desc f g) :
    IsColimit s :=
  Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun t m h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)
#align category_theory.limits.binary_cofan.is_colimit.mk CategoryTheory.Limits.BinaryCofan.IsColimit.mk

theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
    {f g : s.pt ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂
#align category_theory.limits.binary_cofan.is_colimit.hom_ext CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext

variable {X Y : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- Porting note: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps pt]
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  pt := P
  π :=
    { app := fun ⟨j⟩ => by cases j <;> simpa }
#align category_theory.limits.binary_fan.mk CategoryTheory.Limits.BinaryFan.mk

/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
@[simps pt]
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  pt := P
  ι :=
    { app := fun ⟨j⟩ => by cases j <;> simpa }
#align category_theory.limits.binary_cofan.mk CategoryTheory.Limits.BinaryCofan.mk

end

@[simp]
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl
#align category_theory.limits.binary_fan.mk_fst CategoryTheory.Limits.BinaryFan.mk_fst

@[simp]
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl
#align category_theory.limits.binary_fan.mk_snd CategoryTheory.Limits.BinaryFan.mk_snd

@[simp]
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl
#align category_theory.limits.binary_cofan.mk_inl CategoryTheory.Limits.BinaryCofan.mk_inl

@[simp]
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl
#align category_theory.limits.binary_cofan.mk_inr CategoryTheory.Limits.BinaryCofan.mk_inr

/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
    Cones.ext (Iso.refl _) fun j => by cases' j with l; cases l; repeat simp
#align category_theory.limits.iso_binary_fan_mk CategoryTheory.Limits.isoBinaryFanMk

/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocones.ext (Iso.refl _) fun j => by cases' j with l; cases l; repeat simp
#align category_theory.limits.iso_binary_cofan_mk CategoryTheory.Limits.isoBinaryCofanMk

/-- This is a more convenient formulation to show that a `BinaryFan` constructed using
`BinaryFan.mk` is a limit cone.
-/
def BinaryFan.isLimitMk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : ∀ s : BinaryFan X Y, s.pt ⟶ W)
    (fac_left : ∀ s : BinaryFan X Y, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : BinaryFan X Y, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : BinaryFan X Y) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (BinaryFan.mk fst snd) :=
  { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }
#align category_theory.limits.binary_fan.is_limit_mk CategoryTheory.Limits.BinaryFan.isLimitMk

/-- This is a more convenient formulation to show that a `BinaryCofan` constructed using
`BinaryCofan.mk` is a colimit cocone.
-/
def BinaryCofan.isColimitMk {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
    (desc : ∀ s : BinaryCofan X Y, W ⟶ s.pt)
    (fac_left : ∀ s : BinaryCofan X Y, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : BinaryCofan X Y, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : BinaryCofan X Y) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (BinaryCofan.mk inl inr) :=
  { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }
#align category_theory.limits.binary_cofan.is_colimit_mk CategoryTheory.Limits.BinaryCofan.isColimitMk

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
    `g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
    -/
@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩
#align category_theory.limits.binary_fan.is_limit.lift' CategoryTheory.Limits.BinaryFan.IsLimit.lift'

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
    -/
@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩
#align category_theory.limits.binary_cofan.is_colimit.desc' CategoryTheory.Limits.BinaryCofan.IsColimit.desc'

/-- Binary products are symmetric. -/
def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => hc.lift (BinaryFan.mk s.snd s.fst)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.right⟩).symm)
#align category_theory.limits.binary_fan.is_limit_flip CategoryTheory.Limits.BinaryFan.isLimitFlip

theorem BinaryFan.isLimit_iff_isIso_fst {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.fst := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.IsLimit.mk _ (fun f _ => f ≫ inv c.fst) (fun _ _ => by simp)
          (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ => by simp [← e]⟩
#align category_theory.limits.binary_fan.is_limit_iff_is_iso_fst CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_fst

theorem BinaryFan.isLimit_iff_isIso_snd {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.snd := by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩
#align category_theory.limits.binary_fan.is_limit_iff_is_iso_snd CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_snd

/-- If `X' ≅ X`, then `X × Y` also is the product of `X'` and `Y`. -/
noncomputable def BinaryFan.isLimitCompLeftIso {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk (c.fst ≫ f) c.snd) := by
  fapply BinaryFan.isLimitMk
  · exact fun s => h.lift (BinaryFan.mk (s.fst ≫ inv f) s.snd)
  · intro s -- Porting note: simp timed out here
    simp only [Category.comp_id,BinaryFan.π_app_left,IsIso.inv_hom_id,
      BinaryFan.mk_fst,IsLimit.fac_assoc,eq_self_iff_true,Category.assoc]
  · intro s -- Porting note: simp timed out here
    simp only [BinaryFan.π_app_right,BinaryFan.mk_snd,eq_self_iff_true,IsLimit.fac]
  · intro s m e₁ e₂
     -- Porting note: simpa timed out here also
    apply BinaryFan.IsLimit.hom_ext h
    · simpa only
      [BinaryFan.π_app_left,BinaryFan.mk_fst,Category.assoc,IsLimit.fac,IsIso.eq_comp_inv]
    · simpa only [BinaryFan.π_app_right,BinaryFan.mk_snd,IsLimit.fac]
#align category_theory.limits.binary_fan.is_limit_comp_left_iso CategoryTheory.Limits.BinaryFan.isLimitCompLeftIso

/-- If `Y' ≅ Y`, then `X x Y` also is the product of `X` and `Y'`. -/
noncomputable def BinaryFan.isLimitCompRightIso {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk c.fst (c.snd ≫ f)) :=
  BinaryFan.isLimitFlip <| BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)
#align category_theory.limits.binary_fan.is_limit_comp_right_iso CategoryTheory.Limits.BinaryFan.isLimitCompRightIso

/-- Binary coproducts are symmetric. -/
def BinaryCofan.isColimitFlip {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inr c.inl) :=
  BinaryCofan.isColimitMk (fun s => hc.desc (BinaryCofan.mk s.inr s.inl)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm)
#align category_theory.limits.binary_cofan.is_colimit_flip CategoryTheory.Limits.BinaryCofan.isColimitFlip

theorem BinaryCofan.isColimit_iff_isIso_inl {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inl := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (·≫inl c) hl
    rwa [Category.assoc,Category.id_comp] at e
  · intro
    exact
      ⟨BinaryCofan.IsColimit.mk _ (fun f _ => inv c.inl ≫ f)
          (fun _ _ => IsIso.hom_inv_id_assoc _ _) (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ =>
          (IsIso.eq_inv_comp _).mpr e⟩
#align category_theory.limits.binary_cofan.is_colimit_iff_is_iso_inl CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inl

theorem BinaryCofan.isColimit_iff_isIso_inr {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inr := by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩
#align category_theory.limits.binary_cofan.is_colimit_iff_is_iso_inr CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inr

/-- If `X' ≅ X`, then `X ⨿ Y` also is the coproduct of `X'` and `Y`. -/
noncomputable def BinaryCofan.isColimitCompLeftIso {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk (f ≫ c.inl) c.inr) := by
  fapply BinaryCofan.isColimitMk
  · exact fun s => h.desc (BinaryCofan.mk (inv f ≫ s.inl) s.inr)
  · intro s
    -- Porting note: simp timed out here too
    simp only [IsColimit.fac,BinaryCofan.ι_app_left,eq_self_iff_true,
      Category.assoc,BinaryCofan.mk_inl,IsIso.hom_inv_id_assoc]
  · intro s
    -- Porting note: simp timed out here too
    simp only [IsColimit.fac,BinaryCofan.ι_app_right,eq_self_iff_true,BinaryCofan.mk_inr]
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
    -- Porting note: simp timed out here too
      simpa only [IsColimit.fac,BinaryCofan.ι_app_left,eq_self_iff_true,
      Category.assoc,BinaryCofan.mk_inl,IsIso.hom_inv_id_assoc] using e₁
    -- Porting note: simp timed out here too
    · simpa only [IsColimit.fac,BinaryCofan.ι_app_right,eq_self_iff_true,BinaryCofan.mk_inr]
#align category_theory.limits.binary_cofan.is_colimit_comp_left_iso CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso

/-- If `Y' ≅ Y`, then `X ⨿ Y` also is the coproduct of `X` and `Y'`. -/
noncomputable def BinaryCofan.isColimitCompRightIso {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk c.inl (f ≫ c.inr)) :=
  BinaryCofan.isColimitFlip <| BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)
#align category_theory.limits.binary_cofan.is_colimit_comp_right_iso CategoryTheory.Limits.BinaryCofan.isColimitCompRightIso

/-- An abbreviation for `HasLimit (pair X Y)`. -/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)
#align category_theory.limits.has_binary_product CategoryTheory.Limits.HasBinaryProduct

/-- An abbreviation for `HasColimit (pair X Y)`. -/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)
#align category_theory.limits.has_binary_coproduct CategoryTheory.Limits.HasBinaryCoproduct

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or
    `X ⨯ Y`. -/
abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)
#align category_theory.limits.prod CategoryTheory.Limits.prod

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y` or
    `X ⨿ Y`. -/
abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)
#align category_theory.limits.coprod CategoryTheory.Limits.coprod

/-- Notation for the product -/
notation:20 X " ⨯ " Y:20 => prod X Y

/-- Notation for the coproduct -/
notation:20 X " ⨿ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.prod.fst CategoryTheory.Limits.prod.fst

/-- The projection map to the second component of the product. -/
abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.prod.snd CategoryTheory.Limits.prod.snd

/-- The inclusion map from the first component of the coproduct. -/
abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.coprod.inl CategoryTheory.Limits.coprod.inl

/-- The inclusion map from the second component of the coproduct. -/
abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.coprod.inr CategoryTheory.Limits.coprod.inr

/-- The binary fan constructed from the projection maps is a limit. -/
def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.id_comp]; rfl
    · dsimp; simp only [Category.id_comp]; rfl
  ))
#align category_theory.limits.prod_is_prod CategoryTheory.Limits.prodIsProd

/-- The binary cofan constructed from the coprojection maps is a colimit. -/
def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit (Cocones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))
#align category_theory.limits.coprod_is_coprod CategoryTheory.Limits.coprodIsCoprod

@[ext 1100]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂
#align category_theory.limits.prod.hom_ext CategoryTheory.Limits.prod.hom_ext

@[ext 1100]
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
    (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂
#align category_theory.limits.coprod.hom_ext CategoryTheory.Limits.coprod.hom_ext

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)
#align category_theory.limits.prod.lift CategoryTheory.Limits.prod.lift

/-- diagonal arrow of the binary product in the category `fam I` -/
abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)
#align category_theory.limits.diag CategoryTheory.Limits.diag

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)
#align category_theory.limits.coprod.desc CategoryTheory.Limits.coprod.desc

/-- codiagonal arrow of the binary coproduct -/
abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)
#align category_theory.limits.codiag CategoryTheory.Limits.codiag

-- Porting note (#10618): simp removes as simp can prove this
@[reassoc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _
#align category_theory.limits.prod.lift_fst CategoryTheory.Limits.prod.lift_fst
#align category_theory.limits.prod.lift_fst_assoc CategoryTheory.Limits.prod.lift_fst_assoc

-- Porting note (#10618): simp removes as simp can prove this
@[reassoc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _
#align category_theory.limits.prod.lift_snd CategoryTheory.Limits.prod.lift_snd
#align category_theory.limits.prod.lift_snd_assoc CategoryTheory.Limits.prod.lift_snd_assoc

-- The simp linter says simp can prove the reassoc version of this lemma.
-- Porting note: it can also prove the og version
@[reassoc]
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _
#align category_theory.limits.coprod.inl_desc CategoryTheory.Limits.coprod.inl_desc
#align category_theory.limits.coprod.inl_desc_assoc CategoryTheory.Limits.coprod.inl_desc_assoc

-- The simp linter says simp can prove the reassoc version of this lemma.
-- Porting note: it can also prove the og version
@[reassoc]
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _
#align category_theory.limits.coprod.inr_desc CategoryTheory.Limits.coprod.inr_desc
#align category_theory.limits.coprod.inr_desc_assoc CategoryTheory.Limits.coprod.inr_desc_assoc

instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _
#align category_theory.limits.prod.mono_lift_of_mono_left CategoryTheory.Limits.prod.mono_lift_of_mono_left

instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _
#align category_theory.limits.prod.mono_lift_of_mono_right CategoryTheory.Limits.prod.mono_lift_of_mono_right

instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _
#align category_theory.limits.coprod.epi_desc_of_epi_left CategoryTheory.Limits.coprod.epi_desc_of_epi_left

instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _
#align category_theory.limits.coprod.epi_desc_of_epi_right CategoryTheory.Limits.coprod.epi_desc_of_epi_right

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ Prod.fst = f` and `l ≫ Prod.snd = g`. -/
def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩
#align category_theory.limits.prod.lift' CategoryTheory.Limits.prod.lift'

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
    `coprod.inr ≫ l = g`. -/
def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩
#align category_theory.limits.coprod.desc' CategoryTheory.Limits.coprod.desc'

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)
#align category_theory.limits.prod.map CategoryTheory.Limits.prod.map

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)
#align category_theory.limits.coprod.map CategoryTheory.Limits.coprod.map

section ProdLemmas

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp
#align category_theory.limits.prod.comp_lift CategoryTheory.Limits.prod.comp_lift
#align category_theory.limits.prod.comp_lift_assoc CategoryTheory.Limits.prod.comp_lift_assoc

theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) :
    f ≫ diag Y = prod.lift f f := by simp
#align category_theory.limits.prod.comp_diag CategoryTheory.Limits.prod.comp_diag

@[reassoc (attr := simp)]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _
#align category_theory.limits.prod.map_fst CategoryTheory.Limits.prod.map_fst
#align category_theory.limits.prod.map_fst_assoc CategoryTheory.Limits.prod.map_fst_assoc

@[reassoc (attr := simp)]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _
#align category_theory.limits.prod.map_snd CategoryTheory.Limits.prod.map_snd
#align category_theory.limits.prod.map_snd_assoc CategoryTheory.Limits.prod.map_snd_assoc

@[simp]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp
#align category_theory.limits.prod.map_id_id CategoryTheory.Limits.prod.map_id_id

@[simp]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp
#align category_theory.limits.prod.lift_fst_snd CategoryTheory.Limits.prod.lift_fst_snd

@[reassoc (attr := simp)]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp
#align category_theory.limits.prod.lift_map CategoryTheory.Limits.prod.lift_map
#align category_theory.limits.prod.lift_map_assoc CategoryTheory.Limits.prod.lift_map_assoc

@[simp]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp
#align category_theory.limits.prod.lift_fst_comp_snd_comp CategoryTheory.Limits.prod.lift_fst_comp_snd_comp

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `map_fst` and `map_snd` can still work just
-- as well.
@[reassoc (attr := simp)]
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp
#align category_theory.limits.prod.map_map CategoryTheory.Limits.prod.map_map
#align category_theory.limits.prod.map_map_assoc CategoryTheory.Limits.prod.map_map_assoc

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by simp
#align category_theory.limits.prod.map_swap CategoryTheory.Limits.prod.map_swap
#align category_theory.limits.prod.map_swap_assoc CategoryTheory.Limits.prod.map_swap_assoc

@[reassoc]
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
    [HasBinaryProduct Z W] [HasBinaryProduct Y W] :
    prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by simp
#align category_theory.limits.prod.map_comp_id CategoryTheory.Limits.prod.map_comp_id
#align category_theory.limits.prod.map_comp_id_assoc CategoryTheory.Limits.prod.map_comp_id_assoc

@[reassoc]
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
    [HasBinaryProduct W Y] [HasBinaryProduct W Z] :
    prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by simp
#align category_theory.limits.prod.map_id_comp CategoryTheory.Limits.prod.map_id_comp
#align category_theory.limits.prod.map_id_comp_assoc CategoryTheory.Limits.prod.map_id_comp_assoc

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simps]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv
#align category_theory.limits.prod.map_iso CategoryTheory.Limits.prod.mapIso

instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom
#align category_theory.limits.is_iso_prod CategoryTheory.Limits.isIso_prod

instance prod.map_mono {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩
#align category_theory.limits.prod.map_mono CategoryTheory.Limits.prod.map_mono

@[reassoc] -- Porting note (#10618): simp can prove these
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by simp
#align category_theory.limits.prod.diag_map CategoryTheory.Limits.prod.diag_map
#align category_theory.limits.prod.diag_map_assoc CategoryTheory.Limits.prod.diag_map_assoc

@[reassoc] -- Porting note (#10618): simp can prove these
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by simp
#align category_theory.limits.prod.diag_map_fst_snd CategoryTheory.Limits.prod.diag_map_fst_snd
#align category_theory.limits.prod.diag_map_fst_snd_assoc CategoryTheory.Limits.prod.diag_map_fst_snd_assoc

@[reassoc] -- Porting note (#10618): simp can prove these
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by simp
#align category_theory.limits.prod.diag_map_fst_snd_comp CategoryTheory.Limits.prod.diag_map_fst_snd_comp
#align category_theory.limits.prod.diag_map_fst_snd_comp_assoc CategoryTheory.Limits.prod.diag_map_fst_snd_comp_assoc

instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

section CoprodLemmas

-- @[reassoc (attr := simp)]
@[simp] -- Porting note: removing reassoc tag since result is not hygienic (two h's)
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
    (h : Y ⟶ V) : coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp
#align category_theory.limits.coprod.desc_comp CategoryTheory.Limits.coprod.desc_comp

-- Porting note: hand generated reassoc here. Simp can prove it
theorem coprod.desc_comp_assoc {C : Type u} [Category C] {V W X Y : C}
    [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V) (h : Y ⟶ V) {Z : C} (l : W ⟶ Z) :
    coprod.desc g h ≫ f ≫ l = coprod.desc (g ≫ f) (h ≫ f) ≫ l := by simp
#align category_theory.limits.coprod.desc_comp_assoc CategoryTheory.Limits.coprod.desc_comp

theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y) :
    codiag X ≫ f = coprod.desc f f := by simp
#align category_theory.limits.coprod.diag_comp CategoryTheory.Limits.coprod.diag_comp

@[reassoc (attr := simp)]
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colimMap _ _
#align category_theory.limits.coprod.inl_map CategoryTheory.Limits.coprod.inl_map
#align category_theory.limits.coprod.inl_map_assoc CategoryTheory.Limits.coprod.inl_map_assoc

@[reassoc (attr := simp)]
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colimMap _ _
#align category_theory.limits.coprod.inr_map CategoryTheory.Limits.coprod.inr_map
#align category_theory.limits.coprod.inr_map_assoc CategoryTheory.Limits.coprod.inr_map_assoc

@[simp]
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp
#align category_theory.limits.coprod.map_id_id CategoryTheory.Limits.coprod.map_id_id

@[simp]
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] :
    coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by ext <;> simp
#align category_theory.limits.coprod.desc_inl_inr CategoryTheory.Limits.coprod.desc_inl_inr

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
    (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp
#align category_theory.limits.coprod.map_desc CategoryTheory.Limits.coprod.map_desc
#align category_theory.limits.coprod.map_desc_assoc CategoryTheory.Limits.coprod.map_desc_assoc

@[simp]
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]; simp
#align category_theory.limits.coprod.desc_comp_inl_comp_inr CategoryTheory.Limits.coprod.desc_comp_inl_comp_inr

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `inl_map` and `inr_map` can still work just
-- as well.
@[reassoc (attr := simp)]
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp
#align category_theory.limits.coprod.map_map CategoryTheory.Limits.coprod.map_map
#align category_theory.limits.coprod.map_map_assoc CategoryTheory.Limits.coprod.map_map_assoc

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
theorem coprod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f := by simp
#align category_theory.limits.coprod.map_swap CategoryTheory.Limits.coprod.map_swap
#align category_theory.limits.coprod.map_swap_assoc CategoryTheory.Limits.coprod.map_swap_assoc

@[reassoc]
theorem coprod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
    [HasBinaryCoproduct Y W] [HasBinaryCoproduct X W] :
    coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) := by simp
#align category_theory.limits.coprod.map_comp_id CategoryTheory.Limits.coprod.map_comp_id
#align category_theory.limits.coprod.map_comp_id_assoc CategoryTheory.Limits.coprod.map_comp_id_assoc

@[reassoc]
theorem coprod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
    [HasBinaryCoproduct W Y] [HasBinaryCoproduct W Z] :
    coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g := by simp
#align category_theory.limits.coprod.map_id_comp CategoryTheory.Limits.coprod.map_id_comp
#align category_theory.limits.coprod.map_id_comp_assoc CategoryTheory.Limits.coprod.map_id_comp_assoc

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
   `g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simps]
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z where
  hom := coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv
#align category_theory.limits.coprod.map_iso CategoryTheory.Limits.coprod.mapIso

instance isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g) :=
  (coprod.mapIso (asIso f) (asIso g)).isIso_hom
#align category_theory.limits.is_iso_coprod CategoryTheory.Limits.isIso_coprod

instance coprod.map_epi {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩
#align category_theory.limits.coprod.map_epi CategoryTheory.Limits.coprod.map_epi

-- The simp linter says simp can prove the reassoc version of this lemma.
-- Porting note: and the og version too
@[reassoc]
theorem coprod.map_codiag {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f := by simp
#align category_theory.limits.coprod.map_codiag CategoryTheory.Limits.coprod.map_codiag
#align category_theory.limits.coprod.map_codiag_assoc CategoryTheory.Limits.coprod.map_codiag_assoc

-- The simp linter says simp can prove the reassoc version of this lemma.
-- Porting note: and the og version too
@[reassoc]
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y]
    [HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)] :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) = 𝟙 (X ⨿ Y) := by simp
#align category_theory.limits.coprod.map_inl_inr_codiag CategoryTheory.Limits.coprod.map_inl_inr_codiag
#align category_theory.limits.coprod.map_inl_inr_codiag_assoc CategoryTheory.Limits.coprod.map_inl_inr_codiag_assoc

-- The simp linter says simp can prove the reassoc version of this lemma.
-- Porting note: and the og version too
@[reassoc]
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' := by simp
#align category_theory.limits.coprod.map_comp_inl_inr_codiag CategoryTheory.Limits.coprod.map_comp_inl_inr_codiag
#align category_theory.limits.coprod.map_comp_inl_inr_codiag_assoc CategoryTheory.Limits.coprod.map_comp_inl_inr_codiag_assoc

end CoprodLemmas

variable (C)

/-- `HasBinaryProducts` represents a choice of product for every pair of objects.

See <https://stacks.math.columbia.edu/tag/001T>.
-/
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C
#align category_theory.limits.has_binary_products CategoryTheory.Limits.HasBinaryProducts

/-- `HasBinaryCoproducts` represents a choice of coproduct for every pair of objects.

See <https://stacks.math.columbia.edu/tag/04AP>.
-/
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C
#align category_theory.limits.has_binary_coproducts CategoryTheory.Limits.HasBinaryCoproducts

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
theorem hasBinaryProducts_of_hasLimit_pair [∀ {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoPair F).symm }
#align category_theory.limits.has_binary_products_of_has_limit_pair CategoryTheory.Limits.hasBinaryProducts_of_hasLimit_pair

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem hasBinaryCoproducts_of_hasColimit_pair [∀ {X Y : C}, HasColimit (pair X Y)] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoPair F) }
#align category_theory.limits.has_binary_coproducts_of_has_colimit_pair CategoryTheory.Limits.hasBinaryCoproducts_of_hasColimit_pair

section

variable {C}

/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst
#align category_theory.limits.prod.braiding CategoryTheory.Limits.prod.braiding

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f := by simp
#align category_theory.limits.braid_natural CategoryTheory.Limits.braid_natural
#align category_theory.limits.braid_natural_assoc CategoryTheory.Limits.braid_natural_assoc

@[reassoc]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id
#align category_theory.limits.prod.symmetry' CategoryTheory.Limits.prod.symmetry'
#align category_theory.limits.prod.symmetry'_assoc CategoryTheory.Limits.prod.symmetry'_assoc

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id
#align category_theory.limits.prod.symmetry CategoryTheory.Limits.prod.symmetry
#align category_theory.limits.prod.symmetry_assoc CategoryTheory.Limits.prod.symmetry_assoc

/-- The associator isomorphism for binary products. -/
@[simps]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)
#align category_theory.limits.prod.associator CategoryTheory.Limits.prod.associator

@[reassoc]
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).hom =
      (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom := by
  simp
#align category_theory.limits.prod.pentagon CategoryTheory.Limits.prod.pentagon
#align category_theory.limits.prod.pentagon_assoc CategoryTheory.Limits.prod.pentagon_assoc

@[reassoc]
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
      (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) := by
  simp
#align category_theory.limits.prod.associator_naturality CategoryTheory.Limits.prod.associator_naturality
#align category_theory.limits.prod.associator_naturality_assoc CategoryTheory.Limits.prod.associator_naturality_assoc

variable [HasTerminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
#align category_theory.limits.prod.left_unitor CategoryTheory.Limits.prod.leftUnitor

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
#align category_theory.limits.prod.right_unitor CategoryTheory.Limits.prod.rightUnitor

@[reassoc]
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _
#align category_theory.limits.prod.left_unitor_hom_naturality CategoryTheory.Limits.prod.leftUnitor_hom_naturality
#align category_theory.limits.prod.left_unitor_hom_naturality_assoc CategoryTheory.Limits.prod.leftUnitor_hom_naturality_assoc

@[reassoc]
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.leftUnitor_hom_naturality]
#align category_theory.limits.prod.left_unitor_inv_naturality CategoryTheory.Limits.prod.leftUnitor_inv_naturality
#align category_theory.limits.prod.left_unitor_inv_naturality_assoc CategoryTheory.Limits.prod.leftUnitor_inv_naturality_assoc

@[reassoc]
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _
#align category_theory.limits.prod.right_unitor_hom_naturality CategoryTheory.Limits.prod.rightUnitor_hom_naturality
#align category_theory.limits.prod.right_unitor_hom_naturality_assoc CategoryTheory.Limits.prod.rightUnitor_hom_naturality_assoc

@[reassoc]
theorem prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.rightUnitor_hom_naturality]
#align category_theory.limits.prod_right_unitor_inv_naturality CategoryTheory.Limits.prod_rightUnitor_inv_naturality
#align category_theory.limits.prod_right_unitor_inv_naturality_assoc CategoryTheory.Limits.prod_rightUnitor_inv_naturality_assoc

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp
#align category_theory.limits.prod.triangle CategoryTheory.Limits.prod.triangle

end

section

-- Porting note (#10754): added category instance as it did not propagate
variable {C} [Category.{v} C] [HasBinaryCoproducts C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl
#align category_theory.limits.coprod.braiding CategoryTheory.Limits.coprod.braiding

@[reassoc]
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id
#align category_theory.limits.coprod.symmetry' CategoryTheory.Limits.coprod.symmetry'
#align category_theory.limits.coprod.symmetry'_assoc CategoryTheory.Limits.coprod.symmetry'_assoc

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
  coprod.symmetry' _ _
#align category_theory.limits.coprod.symmetry CategoryTheory.Limits.coprod.symmetry

/-- The associator isomorphism for binary coproducts. -/
@[simps]
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)
#align category_theory.limits.coprod.associator CategoryTheory.Limits.coprod.associator

theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).hom =
      (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom := by
  simp
#align category_theory.limits.coprod.pentagon CategoryTheory.Limits.coprod.pentagon

theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
      (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) := by
  simp
#align category_theory.limits.coprod.associator_naturality CategoryTheory.Limits.coprod.associator_naturality

variable [HasInitial C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
#align category_theory.limits.coprod.left_unitor CategoryTheory.Limits.coprod.leftUnitor

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
#align category_theory.limits.coprod.right_unitor CategoryTheory.Limits.coprod.rightUnitor

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp
#align category_theory.limits.coprod.triangle CategoryTheory.Limits.coprod.triangle

end

section ProdFunctor

-- Porting note (#10754): added category instance as it did not propagate
variable {C} [Category.{v} C] [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {Y Z} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }
#align category_theory.limits.prod.functor CategoryTheory.Limits.prod.functor

/-- The product functor can be decomposed. -/
def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)
#align category_theory.limits.prod.functor_left_comp CategoryTheory.Limits.prod.functorLeftComp

end ProdFunctor

section CoprodFunctor

-- Porting note (#10754): added category instance as it did not propagate
variable {C} [Category.{v} C] [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
def coprod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿ Y
      map := fun {Y Z} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }
#align category_theory.limits.coprod.functor CategoryTheory.Limits.coprod.functor

/-- The coproduct functor can be decomposed. -/
def coprod.functorLeftComp (X Y : C) :
    coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)
#align category_theory.limits.coprod.functor_left_comp CategoryTheory.Limits.coprod.functorLeftComp

end CoprodFunctor

section ProdComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)] [HasBinaryProduct (F.obj A') (F.obj B')]

/-- The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff F preserves binary products.
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)
#align category_theory.limits.prod_comparison CategoryTheory.Limits.prodComparison

variable (A B)

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _
#align category_theory.limits.prod_comparison_fst CategoryTheory.Limits.prodComparison_fst
#align category_theory.limits.prod_comparison_fst_assoc CategoryTheory.Limits.prodComparison_fst_assoc

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _
#align category_theory.limits.prod_comparison_snd CategoryTheory.Limits.prodComparison_snd
#align category_theory.limits.prod_comparison_snd_assoc CategoryTheory.Limits.prodComparison_snd_assoc

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]
#align category_theory.limits.prod_comparison_natural CategoryTheory.Limits.prodComparison_natural
#align category_theory.limits.prod_comparison_natural_assoc CategoryTheory.Limits.prodComparison_natural_assoc

/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]
#align category_theory.limits.prod_comparison_nat_trans CategoryTheory.Limits.prodComparisonNatTrans

@[reassoc]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]
#align category_theory.limits.inv_prod_comparison_map_fst CategoryTheory.Limits.inv_prodComparison_map_fst
#align category_theory.limits.inv_prod_comparison_map_fst_assoc CategoryTheory.Limits.inv_prodComparison_map_fst_assoc

@[reassoc]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]
#align category_theory.limits.inv_prod_comparison_map_snd CategoryTheory.Limits.inv_prodComparison_map_snd
#align category_theory.limits.inv_prod_comparison_map_snd_assoc CategoryTheory.Limits.inv_prodComparison_map_snd_assoc

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]
#align category_theory.limits.prod_comparison_inv_natural CategoryTheory.Limits.prodComparison_inv_natural
#align category_theory.limits.prod_comparison_inv_natural_assoc CategoryTheory.Limits.prodComparison_inv_natural_assoc

/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
-- @[simps (config := { rhsMd := semireducible })] -- Porting note: no config for semireducible
@[simps]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app
#align category_theory.limits.prod_comparison_nat_iso CategoryTheory.Limits.prodComparisonNatIso

end ProdComparison

section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']
variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `CategoryTheory/Limits/Preserves` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)
#align category_theory.limits.coprod_comparison CategoryTheory.Limits.coprodComparison

@[reassoc (attr := simp)]
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _
#align category_theory.limits.coprod_comparison_inl CategoryTheory.Limits.coprodComparison_inl
#align category_theory.limits.coprod_comparison_inl_assoc CategoryTheory.Limits.coprodComparison_inl_assoc

@[reassoc (attr := simp)]
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _
#align category_theory.limits.coprod_comparison_inr CategoryTheory.Limits.coprodComparison_inr
#align category_theory.limits.coprod_comparison_inr_assoc CategoryTheory.Limits.coprodComparison_inr_assoc

/-- Naturality of the coprod_comparison morphism in both arguments. -/
@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison, coprodComparison, coprod.map_desc, ← F.map_comp, ← F.map_comp,
    coprod.desc_comp, ← F.map_comp, coprod.inl_map, ← F.map_comp, coprod.inr_map]
#align category_theory.limits.coprod_comparison_natural CategoryTheory.Limits.coprodComparison_natural
#align category_theory.limits.coprod_comparison_natural_assoc CategoryTheory.Limits.coprodComparison_natural_assoc

/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/
@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]
#align category_theory.limits.coprod_comparison_nat_trans CategoryTheory.Limits.coprodComparisonNatTrans

@[reassoc]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp [IsIso.inv_comp_eq]
#align category_theory.limits.map_inl_inv_coprod_comparison CategoryTheory.Limits.map_inl_inv_coprodComparison
#align category_theory.limits.map_inl_inv_coprod_comparison_assoc CategoryTheory.Limits.map_inl_inv_coprodComparison_assoc

@[reassoc]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp [IsIso.inv_comp_eq]
#align category_theory.limits.map_inr_inv_coprod_comparison CategoryTheory.Limits.map_inr_inv_coprodComparison
#align category_theory.limits.map_inr_inv_coprod_comparison_assoc CategoryTheory.Limits.map_inr_inv_coprodComparison_assoc

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]
#align category_theory.limits.coprod_comparison_inv_natural CategoryTheory.Limits.coprodComparison_inv_natural
#align category_theory.limits.coprod_comparison_inv_natural_assoc CategoryTheory.Limits.coprodComparison_inv_natural_assoc

/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/
-- @[simps (config := { rhsMd := semireducible })] -- Porting note: no config for semireducible
@[simps]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F := by
  refine { @asIso _ _ _ _ _ (?_) with hom := coprodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app -- Porting note: this did not work inside { }
#align category_theory.limits.coprod_comparison_nat_iso CategoryTheory.Limits.coprodComparisonNatIso

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Auxiliary definition for `Over.coprod`. -/
@[simps]
def Over.coprodObj [HasBinaryCoproducts C] {A : C} : Over A → Over A ⥤ Over A := fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }
#align category_theory.over.coprod_obj CategoryTheory.Over.coprodObj

/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        dsimp; simp }
  map_id X := by
    ext
    dsimp; simp
  map_comp f g := by
    ext
    dsimp; simp
#align category_theory.over.coprod CategoryTheory.Over.coprod

end CategoryTheory
