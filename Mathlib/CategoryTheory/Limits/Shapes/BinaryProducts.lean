/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

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

universe v v₁ u u₁ u₂

open CategoryTheory Category

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

/-- The equivalence swapping left and right.
-/
def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun
    | left => right
    | right => left
  invFun
    | left => right
    | right => left
  left_inv j := by cases j <;> rfl
  right_inv j := by cases j <;> rfl

@[simp]
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl

/-- An equivalence from `WalkingPair` to `Bool`, sometimes useful when reindexing limits.
-/
def WalkingPair.equivBool : WalkingPair ≃ Bool where
  toFun
    | left => true
    | right => false
  -- to match equiv.sum_equiv_sigma_bool
  invFun b := Bool.recOn b right left
  left_inv j := by cases j <;> rfl
  right_inv b := by cases b <;> rfl

@[simp]
theorem WalkingPair.equivBool_apply_left : WalkingPair.equivBool left = true :=
  rfl

@[simp]
theorem WalkingPair.equivBool_apply_right : WalkingPair.equivBool right = false :=
  rfl

@[simp]
theorem WalkingPair.equivBool_symm_apply_true : WalkingPair.equivBool.symm true = left :=
  rfl

@[simp]
theorem WalkingPair.equivBool_symm_apply_false : WalkingPair.equivBool.symm false = right :=
  rfl

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pairFunction_left (X Y : C) : pairFunction X Y left = X :=
  rfl

@[simp]
theorem pairFunction_right (X Y : C) : pairFunction X Y right = Y :=
  rfl

variable [Category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X :=
  rfl

@[simp]
theorem pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y :=
  rfl

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩)
  (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- The natural transformation between two functors out of the
walking pair, specified by its components. -/
def mapPair : F ⟶ G where
  app
    | ⟨left⟩ => f
    | ⟨right⟩ => g
  naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by cat_disch

@[simp]
theorem mapPair_left : (mapPair f g).app ⟨left⟩ = f :=
  rfl

@[simp]
theorem mapPair_right : (mapPair f g).app ⟨right⟩ = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps!]
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by cat_disch)

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps!]
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) :
    F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u₁} [Category.{v₁} D]

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

/-- A binary fan is just a cone on a diagram indexing a product. -/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

/-- The first projection of a binary fan. -/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩

/-- The second projection of a binary fan. -/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩

-- Marking this `@[simp]` causes loops since `s.fst` is reducibly defeq to the LHS.
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl

-- Marking this `@[simp]` causes loops since `s.snd` is reducibly defeq to the LHS.
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl

/-- Constructs an isomorphism of `BinaryFan`s out of an isomorphism of the tips that commutes with
the projections. -/
def BinaryFan.ext {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) : c ≅ c' :=
  Cones.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
lemma BinaryFan.ext_hom_hom {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

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
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
abbrev BinaryCofan (X Y : C) := Cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.left⟩

/-- The second inclusion of a binary cofan. -/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩

/-- Constructs an isomorphism of `BinaryCofan`s out of an isomorphism of the tips that commutes with
the injections. -/
def BinaryCofan.ext {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) : c ≅ c' :=
  Cocones.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
lemma BinaryCofan.ext_hom_hom {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

-- This cannot be `@[simp]` because `s.inl` is reducibly defeq to the LHS.
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.left⟩ = s.inl := rfl

-- This cannot be `@[simp]` because `s.inr` is reducibly defeq to the LHS.
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.right⟩ = s.inr := rfl

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
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
    {f g : s.pt ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

variable {X Y : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- TODO: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps pt]
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  pt := P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }

/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
@[simps pt]
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  pt := P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }

end

@[simp]
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl

@[simp]
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl

/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
    Cones.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocones.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

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

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
-/
@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

/-- Binary products are symmetric. -/
def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => hc.lift (BinaryFan.mk s.snd s.fst)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.right⟩).symm)

theorem BinaryFan.isLimit_iff_isIso_fst {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.fst := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -comp_id] using comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.IsLimit.mk _ (fun f _ => f ≫ inv c.fst) (fun _ _ => by simp)
          (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ => by simp [← e]⟩

theorem BinaryFan.isLimit_iff_isIso_snd {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.snd := by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

/-- If `X' ≅ X`, then `X × Y` also is the product of `X'` and `Y`. -/
noncomputable def BinaryFan.isLimitCompLeftIso {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk (c.fst ≫ f) c.snd) := by
  fapply BinaryFan.isLimitMk
  · exact fun s => h.lift (BinaryFan.mk (s.fst ≫ inv f) s.snd)
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryFan.IsLimit.hom_ext h
    · simpa
    · simpa

/-- If `Y' ≅ Y`, then `X x Y` also is the product of `X` and `Y'`. -/
noncomputable def BinaryFan.isLimitCompRightIso {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk c.fst (c.snd ≫ f)) :=
  BinaryFan.isLimitFlip <| BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

/-- Binary coproducts are symmetric. -/
def BinaryCofan.isColimitFlip {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inr c.inl) :=
  BinaryCofan.isColimitMk (fun s => hc.desc (BinaryCofan.mk s.inr s.inl)) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm)

theorem BinaryCofan.isColimit_iff_isIso_inl {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inl := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (· ≫ inl c) hl
    rwa [Category.assoc, Category.id_comp] at e
  · intro
    exact
      ⟨BinaryCofan.IsColimit.mk _ (fun f _ => inv c.inl ≫ f)
          (fun _ _ => IsIso.hom_inv_id_assoc _ _) (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ =>
          (IsIso.eq_inv_comp _).mpr e⟩

theorem BinaryCofan.isColimit_iff_isIso_inr {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inr := by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

/-- If `X' ≅ X`, then `X ⨿ Y` also is the coproduct of `X'` and `Y`. -/
noncomputable def BinaryCofan.isColimitCompLeftIso {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk (f ≫ c.inl) c.inr) := by
  fapply BinaryCofan.isColimitMk
  · exact fun s => h.desc (BinaryCofan.mk (inv f ≫ s.inl) s.inr)
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
      simpa using e₁
    · simpa

/-- If `Y' ≅ Y`, then `X ⨿ Y` also is the coproduct of `X` and `Y'`. -/
noncomputable def BinaryCofan.isColimitCompRightIso {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk c.inl (f ≫ c.inr)) :=
  BinaryCofan.isColimitFlip <| BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

/-- An abbreviation for `HasLimit (pair X Y)`. -/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/-- An abbreviation for `HasColimit (pair X Y)`. -/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or `X ⨯ Y`. -/
noncomputable abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y` or `X ⨿ Y`. -/
noncomputable abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

/-- Notation for the product -/
notation:20 X " ⨯ " Y:20 => prod X Y

/-- Notation for the coproduct -/
notation:20 X " ⨿ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
noncomputable abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

/-- The projection map to the second component of the product. -/
noncomputable abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

/-- The inclusion map from the first component of the coproduct. -/
noncomputable abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩

/-- The inclusion map from the second component of the coproduct. -/
noncomputable abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩

/-- The binary fan constructed from the projection maps is a limit. -/
noncomputable def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

/-- The binary cofan constructed from the coprojection maps is a colimit. -/
noncomputable def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit (Cocones.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [comp_id]
    · dsimp; simp only [comp_id]
  ))

@[ext 1100]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
    (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
noncomputable abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
noncomputable abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
noncomputable abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
noncomputable abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _

@[reassoc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _

@[reassoc]
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _

@[reassoc]
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _

instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _

instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ Prod.fst = f` and `l ≫ Prod.snd = g`. -/
noncomputable def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
`coprod.inr ≫ l = g`. -/
noncomputable def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
noncomputable def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
noncomputable def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)

noncomputable section ProdLemmas

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp

theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) :
    f ≫ diag Y = lift f f := by simp

@[reassoc (attr := simp)]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _

@[reassoc (attr := simp)]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _

@[simp]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp

@[simp]
lemma prod.lift_comp_fst_snd {X Y Z : C} [HasBinaryProduct Y Z] (f : X ⟶ Y ⨯ Z) :
    prod.lift (f ≫ prod.fst) (f ≫ prod.snd) = f := by ext <;> simp

@[reassoc (attr := simp)]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `map_fst` and `map_snd` can still work just
-- as well.
@[reassoc (attr := simp)]
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by simp

@[reassoc]
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
    [HasBinaryProduct Z W] [HasBinaryProduct Y W] :
    prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by simp

@[reassoc]
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
    [HasBinaryProduct W Y] [HasBinaryProduct W Z] :
    prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by simp

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simps]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom

instance prod.map_mono {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

@[reassoc]
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by simp

@[reassoc]
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by simp

@[reassoc]
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by simp

instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

noncomputable section CoprodLemmas

@[reassoc, simp]
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
    (h : Y ⟶ V) : coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp

theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y) :
    codiag X ≫ f = coprod.desc f f := by simp

@[reassoc (attr := simp)]
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colimMap _ _

@[simp]
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] :
    coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by ext <;> simp

@[simp]
lemma coprod.desc_comp_inl_inr {X Y Z : C} [HasBinaryCoproduct X Y] (f : X ⨿ Y ⟶ Z) :
    coprod.desc (coprod.inl ≫ f) (coprod.inr ≫ f) = f := by ext <;> simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
    (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

@[simp]
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]; simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `inl_map` and `inr_map` can still work just
-- as well.
@[reassoc (attr := simp)]
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
theorem coprod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f := by simp

@[reassoc]
theorem coprod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
    [HasBinaryCoproduct Y W] [HasBinaryCoproduct X W] :
    coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) := by simp

@[reassoc]
theorem coprod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
    [HasBinaryCoproduct W Y] [HasBinaryCoproduct W Z] :
    coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g := by simp

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simps]
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z where
  hom := coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv

instance isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g) :=
  (coprod.mapIso (asIso f) (asIso g)).isIso_hom

instance coprod.map_epi {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

@[reassoc]
theorem coprod.map_codiag {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f := by simp

@[reassoc]
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y]
    [HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)] :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) = 𝟙 (X ⨿ Y) := by simp

@[reassoc]
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' := by simp

end CoprodLemmas

variable (C)

/-- A category `HasBinaryProducts` if it has all limits of shape `Discrete WalkingPair`,
i.e. if it has a product for every pair of objects. -/
@[stacks 001T]
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- A category `HasBinaryCoproducts` if it has all colimit of shape `Discrete WalkingPair`,
i.e. if it has a coproduct for every pair of objects. -/
@[stacks 04AP]
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
theorem hasBinaryProducts_of_hasLimit_pair [∀ {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem hasBinaryCoproducts_of_hasColimit_pair [∀ {X Y : C}, HasColimit (pair X Y)] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoPair F) }

noncomputable section

variable {C}

/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f := by simp

@[reassoc]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

/-- The associator isomorphism for binary products. -/
@[simps]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

@[reassoc]
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).hom =
      (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom := by
  simp

@[reassoc]
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
      (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) := by
  simp

variable [HasTerminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _

@[reassoc]
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv, prod.leftUnitor_hom_naturality]

@[reassoc]
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _

@[reassoc]
theorem prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv, prod.rightUnitor_hom_naturality]

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section

variable {C}
variable [HasBinaryCoproducts C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
  coprod.symmetry' _ _

/-- The associator isomorphism for binary coproducts. -/
@[simps]
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).hom =
      (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom := by
  simp

theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
      (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) := by
  simp

variable [HasInitial C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section ProdFunctor

variable {C} [Category.{v} C] [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

/-- The product functor can be decomposed. -/
def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)

end ProdFunctor

noncomputable section CoprodFunctor

variable {C} [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
def coprod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

/-- The coproduct functor can be decomposed. -/
def coprod.functorLeftComp (X Y : C) :
    coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)

end CoprodFunctor

noncomputable section ProdComparison

universe w w' u₃

variable {C} {D : Type u₂} [Category.{w} D] {E : Type u₃} [Category.{w'} E]
variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)]
variable [HasBinaryProduct (F.obj A') (F.obj B')]
variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]
variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

/-- The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff F preserves binary products.
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[reassoc (attr := simp)]
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]

/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[reassoc]
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

theorem prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

end ProdComparison

noncomputable section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']
variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `Mathlib/CategoryTheory/Limits/Preserves/` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the coprod_comparison morphism in both arguments. -/
@[reassoc]
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison, coprodComparison, coprod.map_desc, ← F.map_comp, ← F.map_comp,
    coprod.desc_comp, ← F.map_comp, coprod.inl_map, ← F.map_comp, coprod.inr_map]

/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/
@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp

@[reassoc]
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, assoc, IsIso.inv_comp_eq, coprodComparison_natural]

/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F :=
  { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Auxiliary definition for `Over.coprod`. -/
@[simps]
noncomputable def Over.coprodObj [HasBinaryCoproducts C] {A : C} :
    Over A → Over A ⥤ Over A :=
  fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
noncomputable def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

end CategoryTheory

namespace CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C] {X Y Z P : C}

section opposite

/-- A binary fan gives a binary cofan in the opposite category. -/
protected abbrev BinaryFan.op (c : BinaryFan X Y) : BinaryCofan (op X) (op Y) :=
  .mk c.fst.op c.snd.op

/-- A binary cofan gives a binary fan in the opposite category. -/
protected abbrev BinaryCofan.op (c : BinaryCofan X Y) : BinaryFan (op X) (op Y) :=
  .mk c.inl.op c.inr.op

/-- A binary fan in the opposite category gives a binary cofan. -/
protected abbrev BinaryFan.unop (c : BinaryFan (op X) (op Y)) : BinaryCofan X Y :=
  .mk c.fst.unop c.snd.unop

/-- A binary cofan in the opposite category gives a binary fan. -/
protected abbrev BinaryCofan.unop (c : BinaryCofan (op X) (op Y)) : BinaryFan X Y :=
  .mk c.inl.unop c.inr.unop

@[simp] lemma BinaryFan.op_mk (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    BinaryFan.op (mk π₁ π₂) = .mk π₁.op π₂.op := rfl

@[simp] lemma BinaryFan.unop_mk (π₁ : op P ⟶ op X) (π₂ : op P ⟶ op Y) :
    BinaryFan.unop (mk π₁ π₂) = .mk π₁.unop π₂.unop := rfl

@[simp] lemma BinaryCofan.op_mk (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    BinaryCofan.op (mk ι₁ ι₂) = .mk ι₁.op ι₂.op := rfl

@[simp] lemma BinaryCofan.unop_mk (ι₁ : op X ⟶ op P) (ι₂ : op Y ⟶ op P) :
    BinaryCofan.unop (mk ι₁ ι₂) = .mk ι₁.unop ι₂.unop := rfl

/-- If a `BinaryFan` is a limit, then its opposite is a colimit. -/
protected def BinaryFan.IsLimit.op {c : BinaryFan X Y} (hc : IsLimit c) : IsColimit c.op :=
  BinaryCofan.isColimitMk (fun s ↦ (hc.lift s.unop).op)
    (fun _ ↦ Quiver.Hom.unop_inj (by simp)) (fun _ ↦ Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.unop_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

/-- If a `BinaryCofan` is a colimit, then its opposite is a limit. -/
protected def BinaryCofan.IsColimit.op {c : BinaryCofan X Y} (hc : IsColimit c) : IsLimit c.op :=
  BinaryFan.isLimitMk (fun s ↦ (hc.desc s.unop).op)
    (fun _ ↦ Quiver.Hom.unop_inj (by simp)) (fun _ ↦ Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.unop_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

/-- If a `BinaryFan` in the opposite category is a limit, then its `unop` is a colimit. -/
protected def BinaryFan.IsLimit.unop {c : BinaryFan (op X) (op Y)} (hc : IsLimit c) :
    IsColimit c.unop :=
  BinaryCofan.isColimitMk (fun s ↦ (hc.lift s.op).unop)
    (fun _ ↦ Quiver.Hom.op_inj (by simp)) (fun _ ↦ Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.op_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

/-- If a `BinaryCofan` in the opposite category is a colimit, then its `unop` is a limit. -/
protected def BinaryCofan.IsColimit.unop {c : BinaryCofan (op X) (op Y)} (hc : IsColimit c) :
    IsLimit c.unop :=
  BinaryFan.isLimitMk (fun s ↦ (hc.desc s.op).unop)
    (fun _ ↦ Quiver.Hom.op_inj (by simp)) (fun _ ↦ Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.op_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

end opposite

section swap
variable {s : BinaryFan X Y} {t : BinaryFan Y X}

/-- Swap the two sides of a `BinaryFan`. -/
def BinaryFan.swap (s : BinaryFan X Y) : BinaryFan Y X := .mk s.snd s.fst

@[simp] lemma BinaryFan.swap_fst (s : BinaryFan X Y) : s.swap.fst = s.snd := rfl
@[simp] lemma BinaryFan.swap_snd (s : BinaryFan X Y) : s.swap.snd = s.fst := rfl

/-- If a binary fan `s` over `X Y` is a limit cone, then `s.swap` is a limit cone over `Y X`. -/
@[simps]
def IsLimit.binaryFanSwap (I : IsLimit s) : IsLimit s.swap where
  lift t := I.lift (BinaryFan.swap t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := I.uniq (BinaryFan.swap t) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w

@[deprecated (since := "2025-05-04")] alias IsLimit.swapBinaryFan := IsLimit.binaryFanSwap

/-- Construct `HasBinaryProduct Y X` from `HasBinaryProduct X Y`.
This can't be an instance, as it would cause a loop in typeclass search. -/
lemma HasBinaryProduct.swap (X Y : C) [HasBinaryProduct X Y] : HasBinaryProduct Y X :=
  .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

end swap

section braiding
variable {X Y : C} {s : BinaryFan X Y} (P : IsLimit s) {t : BinaryFan Y X} (Q : IsLimit t)

/-- Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every
pair, these isomorphisms constitute a braiding. -/
def BinaryFan.braiding (P : IsLimit s) (Q : IsLimit t) : s.pt ≅ t.pt :=
  P.conePointUniqueUpToIso Q.binaryFanSwap

@[reassoc (attr := simp)]
lemma BinaryFan.braiding_hom_fst : (braiding P Q).hom ≫ t.fst = s.snd :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

@[reassoc (attr := simp)]
lemma BinaryFan.braiding_hom_snd : (braiding P Q).hom ≫ t.snd = s.fst :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
lemma BinaryFan.braiding_inv_fst : (braiding P Q).inv ≫ s.fst = t.snd :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
lemma BinaryFan.braiding_inv_snd : (braiding P Q).inv ≫ s.snd = t.fst :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.right⟩

end braiding

section assoc
variable {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a Cartesian category. -/
def BinaryFan.assoc (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) : BinaryFan X sYZ.pt :=
  mk (s.fst ≫ sXY.fst) (Q.lift (mk (s.fst ≫ sXY.snd) s.snd))

@[simp]
lemma BinaryFan.assoc_fst (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).fst = s.fst ≫ sXY.fst := rfl

@[simp]
lemma BinaryFan.assoc_snd (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).snd = Q.lift (mk (s.fst ≫ sXY.snd) s.snd) := rfl

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a Cartesian category. -/
def BinaryFan.assocInv (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) : BinaryFan sXY.pt Z :=
  BinaryFan.mk (P.lift (BinaryFan.mk s.fst (s.snd ≫ sYZ.fst))) (s.snd ≫ sYZ.snd)

@[simp]
lemma BinaryFan.assocInv_fst (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).fst = P.lift (mk s.fst (s.snd ≫ sYZ.fst)) := rfl

@[simp]
lemma BinaryFan.assocInv_snd (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).snd = s.snd ≫ sYZ.snd := rfl

/-- If all the binary fans involved a limit cones, `BinaryFan.assoc` produces another limit cone. -/
@[simps]
protected def IsLimit.assoc (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) : IsLimit (BinaryFan.assoc Q s) where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp; apply Q.hom_ext; rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩ <;> simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩ <;> simp
      · exact w ⟨.left⟩
      · replace w : m ≫ Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd) = t.π.app ⟨.right⟩ := by
          simpa using w ⟨.right⟩
        simp [← w]
    · replace w : m ≫ Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd) = t.π.app ⟨.right⟩ := by
        simpa using w ⟨.right⟩
      simp [← w]

/-- Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points. -/
abbrev BinaryFan.associator (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) {t : BinaryFan X sYZ.pt} (S : IsLimit t) : s.pt ≅ t.pt :=
  (P.assoc Q R).conePointUniqueUpToIso S

/-- Given a fixed family of limit data for every pair `X Y`, we obtain an associator. -/
abbrev BinaryFan.associatorOfLimitCone (L : ∀ X Y : C, LimitCone (pair X Y)) (X Y Z : C) :
    (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt :=
  associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit

end assoc

section unitor

/-- Construct a left unitor from specified limit cones. -/
@[simps]
def BinaryFan.leftUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan s.pt X} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.snd
  inv := Q.lift <| BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp

/-- Construct a right unitor from specified limit cones. -/
@[simps]
def BinaryFan.rightUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan X s.pt} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.fst
  inv := Q.lift <| BinaryFan.mk (𝟙 _) <| P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩

end unitor
end CategoryTheory.Limits
