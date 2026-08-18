/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair

/-!
# Binary fans and cofans

A binary (co)fan is a (co)cone over a walking-pair diagram. These will be used (in a subsequent
file) to define binary products and coproducts.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

@[expose] public section

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

open WalkingPair

variable {C : Type u} [Category.{v} C]

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
  Cone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

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
  Cocone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

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

variable {X Y Z P : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- TODO: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps pt, implicit_reducible]
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
    Cone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

set_option backward.defeqAttrib.useBackward true in
/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

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
def BinaryFan.IsLimit.lift {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ s.pt :=
  h.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]
lemma BinaryFan.IsLimit.lift_fst {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.fst = f :=
  h.fac (BinaryFan.mk f g) _

@[reassoc (attr := simp)]
lemma BinaryFan.IsLimit.lift_snd {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.snd = g :=
  h.fac (BinaryFan.mk f g) _

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
-/
@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

/-- If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
def BinaryCofan.IsColimit.desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.pt ⟶ W :=
  h.desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
lemma BinaryCofan.IsColimit.inl_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inl ≫ desc h f g = f :=
  h.fac (BinaryCofan.mk f g) _

@[reassoc (attr := simp)]
lemma BinaryCofan.IsColimit.inr_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inr ≫ desc h f g = g :=
  h.fac (BinaryCofan.mk f g) _

/-- If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

/-- Binary products are symmetric. -/
def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => IsLimit.lift hc s.snd s.fst) (fun _ => hc.fac _ _)
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
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
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
  · exact fun s => IsLimit.lift h (s.fst ≫ inv f) s.snd
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
  BinaryCofan.isColimitMk (fun s => IsColimit.desc hc s.inr s.inl) (fun _ => hc.fac _ _)
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
  · exact fun s => BinaryCofan.IsColimit.desc h (inv f ≫ s.inl) s.inr
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


section

variable {D : Type*} [Category* D] {F : C ⥤ D}

variable (F) in
/-- The image of a binary fan by a functor. -/
abbrev BinaryFan.map {X Y : C} (s : BinaryFan X Y) : BinaryFan (F.obj X) (F.obj Y) :=
  mk (F.map s.fst) (F.map s.snd)

@[simp]
lemma BinaryFan.map_fst {X Y : C} (s : BinaryFan X Y) : (s.map F).fst = F.map s.fst := rfl

@[simp]
lemma BinaryFan.map_snd {X Y : C} (s : BinaryFan X Y) : (s.map F).snd = F.map s.snd := rfl

variable (F) in
/-- The image of a binary cofan by a functor. -/
abbrev BinaryCofan.map {X Y : C} (s : BinaryCofan X Y) : BinaryCofan (F.obj X) (F.obj Y) :=
  mk (F.map s.inl) (F.map s.inr)

@[simp]
lemma BinaryCofan.map_inl {X Y : C} (s : BinaryCofan X Y) : (s.map F).inl = F.map s.inl := rfl

@[simp]
lemma BinaryCofan.map_inr {X Y : C} (s : BinaryCofan X Y) : (s.map F).inr = F.map s.inr := rfl

/-- `F.mapCone s` being limiting is the same as the induced binary fan being limiting. -/
def BinaryFan.isLimitMapConeEquiv {X Y : C} {s : BinaryFan X Y} :
    IsLimit (F.mapCone s) ≃ IsLimit (s.map F) :=
  IsLimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ <| ext (Iso.refl _)
    (by simp [fst]) (by simp [snd])

set_option backward.defeqAttrib.useBackward true in
/-- `F.mapCocone s` being colimiting is the same as the induced binary cofan being colimiting. -/
def BinaryCofan.isColimitMapConeEquiv {X Y : C} {s : BinaryCofan X Y} :
    IsColimit (F.mapCocone s) ≃ IsColimit (s.map F) :=
  IsColimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ <| ext (Iso.refl _)
    (by simp [inl]) (by simp [inr])

end

section opposite

open Opposite

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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
  BinaryFan.mk (IsLimit.lift P s.fst (s.snd ≫ sYZ.fst)) (s.snd ≫ sYZ.snd)

@[simp]
lemma BinaryFan.assocInv_fst (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).fst = IsLimit.lift P s.fst (s.snd ≫ sYZ.fst) := rfl

@[simp]
lemma BinaryFan.assocInv_snd (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).snd = s.snd ≫ sYZ.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If all the binary fans involved a limit cones, `BinaryFan.assoc` produces another limit cone. -/
@[simps]
protected def IsLimit.assoc (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) : IsLimit (BinaryFan.assoc Q s) where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩
    · simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
      · simpa using w ⟨.left⟩
      · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
          simpa using! w ⟨.right⟩
        simp [← w]
    · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
        simpa using! w ⟨.right⟩
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

end
