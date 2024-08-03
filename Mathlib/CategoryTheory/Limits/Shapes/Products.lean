/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.DiscreteCategory

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`Discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `Fan` is a cone over a discrete category
* `Fan.mk` constructs a fan from an indexed collection of maps
* a `Pi` is a `limit (Discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

noncomputable section

universe w w' w₂ w₃ v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w} {α : Type w₂} {γ : Type w₃}
variable {C : Type u} [Category.{v} C]

-- We don't need an analogue of `Pair` (for binary products), `ParallelPair` (for equalizers),
-- or `(Co)span`, since we already have `Discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps! pt π_app]
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  pt := P
  π := Discrete.natTrans (fun X => p X.as)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps! pt ι_app]
def Cofan.mk {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : Cofan f where
  pt := P
  ι := Discrete.natTrans (fun X => p X.as)

/-- Get the `j`th "projection" in the fan.
(Note that the initial letter of `proj` matches the greek letter in `Cone.π`.) -/
def Fan.proj {f : β → C} (p : Fan f) (j : β) : p.pt ⟶ f j :=
  p.π.app (Discrete.mk j)

/-- Get the `j`th "injection" in the cofan.
(Note that the initial letter of `inj` matches the greek letter in `Cocone.ι`.) -/
def Cofan.inj {f : β → C} (p : Cofan f) (j : β) : f j ⟶ p.pt :=
  p.ι.app (Discrete.mk j)

@[simp]
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) (j : β) : (Fan.mk P p).proj j = p j :=
  rfl

@[simp]
theorem cofan_mk_inj {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) (j : β) :
    (Cofan.mk P p).inj j = p j :=
  rfl

/-- An abbreviation for `HasLimit (Discrete.functor f)`. -/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

/-- An abbreviation for `HasColimit (Discrete.functor f)`. -/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)

lemma hasCoproduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasCoproduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasCoproduct g := by
  have : HasColimit ((Discrete.equivalence e).functor ⋙ Discrete.functor f) :=
    hasColimit_equivalence_comp _
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimitOfIso α

lemma hasProduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasProduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasProduct g := by
  have : HasLimit ((Discrete.equivalence e).functor ⋙ Discrete.functor f) :=
    hasLimitEquivalenceComp _
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimitOfIso α.symm

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkFanLimit {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.pt ⟶ t.pt)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by aesop_cat)
    (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by aesop_cat) :
    IsLimit t :=
  { lift }

/-- Constructor for morphisms to the point of a limit fan. -/
def Fan.IsLimit.desc {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) : A ⟶ c.pt :=
  hc.lift (Fan.mk A f)

@[reassoc (attr := simp)]
lemma Fan.IsLimit.fac {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) (i : β) :
    Fan.IsLimit.desc hc f ≫ c.proj i = f i :=
  hc.fac (Fan.mk A f) ⟨i⟩

lemma Fan.IsLimit.hom_ext {I : Type*} {F : I → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f g : A ⟶ c.pt) (h : ∀ i, f ≫ c.proj i = g ≫ c.proj i) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkCofanColimit {f : β → C} (s : Cofan f) (desc : ∀ t : Cofan f, s.pt ⟶ t.pt)
    (fac : ∀ (t : Cofan f) (j : β), s.inj j ≫ desc t = t.inj j := by aesop_cat)
    (uniq : ∀ (t : Cofan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, s.inj j ≫ m = t.inj j),
      m = desc t := by aesop_cat) :
    IsColimit s :=
  { desc }

/-- Constructor for morphisms from the point of a colimit cofan. -/
def Cofan.IsColimit.desc {F : β → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) : c.pt ⟶ A :=
  hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]
lemma Cofan.IsColimit.fac {F : β → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) (i : β) :
    c.inj i ≫ Cofan.IsColimit.desc hc f = f i :=
  hc.fac (Cofan.mk A f) ⟨i⟩

lemma Cofan.IsColimit.hom_ext {I : Type*} {F : I → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f g : c.pt ⟶ A) (h : ∀ i, c.inj i ≫ f = c.inj i ≫ g) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

section

variable (C)

/-- An abbreviation for `HasLimitsOfShape (Discrete f)`. -/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/-- An abbreviation for `HasColimitsOfShape (Discrete f)`. -/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)

end

/-- `piObj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (Discrete.functor f)`,
so for most facts about `piObj f`, you will just use general facts about limits.) -/
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)

/-- `sigmaObj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (Discrete.functor f)`,
so for most facts about `sigmaObj f`, you will just use general facts about colimits.) -/
abbrev sigmaObj (f : β → C) [HasCoproduct f] :=
  colimit (Discrete.functor f)

/-- notation for categorical products. We need `ᶜ` to avoid conflict with `Finset.prod`. -/
notation "∏ᶜ " f:60 => piObj f

/-- notation for categorical coproducts -/
notation "∐ " f:60 => sigmaObj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ᶜ f ⟶ f b`. -/
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ᶜ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbrev Sigma.ι (f : β → C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) (Discrete.mk b)

-- porting note (#10688): added the next two lemmas to ease automation; without these lemmas,
-- `limit.hom_ext` would be applied, but the goal would involve terms
-- in `Discrete β` rather than `β` itself
@[ext 1050]
lemma Pi.hom_ext {f : β → C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
    (h : ∀ (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

@[ext 1050]
lemma Sigma.hom_ext {f : β → C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
    (h : ∀ (b : β), Sigma.ι f b ≫ g₁ = Sigma.ι f b ≫ g₂) : g₁ = g₂ :=
  colimit.hom_ext (fun ⟨j⟩ => h j)

/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cones.ext (Iso.refl _))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocones.ext (Iso.refl _))

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `Pi.whiskerEquiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem Pi.π_comp_eqToHom {J : Type*} (f : J → C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  cases w
  simp

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `Sigma.whiskerEquiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem Sigma.eqToHom_comp_ι {J : Type*} (f : J → C) [HasCoproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j := by
  cases w
  simp

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ᶜ f`. -/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ᶜ f :=
  limit.lift _ (Fan.mk P p)

theorem Pi.lift_π {β : Type w} {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

theorem Sigma.ι_desc {β : Type w} {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) (b : β) :
    Sigma.ι f b ≫ Sigma.desc p = p b := by
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

instance {f : β → C} [HasCoproduct f] : IsIso (Sigma.desc (fun a ↦ Sigma.ι f a)) := by
  convert IsIso.id _
  ext
  simp

/-- A version of `Cocones.ext` for `Cofan`s. -/
@[simps!]
def Cofan.ext {f : β → C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.inj b ≫ e.hom = c₂.inj b := by aesop_cat) : c₁ ≅ c₂ :=
  Cocones.ext e (fun ⟨j⟩ => w j)

/-- A cofan `c` on `f` such that the induced map `∐ f ⟶ c.pt` is an iso, is a coproduct. -/
def Cofan.isColimitOfIsIsoSigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f)
    [hc : IsIso (Sigma.desc c.inj)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))

lemma Cofan.isColimit_iff_isIso_sigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f) :
    IsIso (Sigma.desc c.inj) ↔ Nonempty (IsColimit c) := by
  refine ⟨fun h ↦ ⟨isColimitOfIsIsoSigmaDesc c⟩, fun ⟨hc⟩ ↦ ?_⟩
  have : IsIso (((coproductIsCoproduct f).coconePointUniqueUpToIso hc).hom ≫ hc.desc c) := by
    simp; infer_instance
  convert this
  ext
  simp only [colimit.ι_desc, mk_pt, mk_ι_app, IsColimit.coconePointUniqueUpToIso,
    coproductIsCoproduct, colimit.cocone_x, Functor.mapIso_hom, IsColimit.uniqueUpToIso_hom,
    Cocones.forget_map, IsColimit.descCoconeMorphism_hom, IsColimit.ofIsoColimit_desc,
    Cocones.ext_inv_hom, Iso.refl_inv, colimit.isColimit_desc, Category.id_comp,
    IsColimit.desc_self, Category.comp_id]
  rfl

/-- A coproduct of coproducts is a coproduct -/
def Cofan.isColimitTrans {X : α → C} (c : Cofan X) (hc : IsColimit c)
    {β : α → Type*} {Y : (a : α) → β a → C} (π : (a : α) → (b : β a) → Y a b ⟶ X a)
      (hs : ∀ a, IsColimit (Cofan.mk (X a) (π a))) :
        IsColimit (Cofan.mk (f := fun ⟨a,b⟩ => Y a b) c.pt
          (fun (⟨a, b⟩ : Σ a, _) ↦ π a b ≫ c.inj a)) := by
  refine mkCofanColimit _ ?_ ?_ ?_
  · exact fun t ↦ hc.desc (Cofan.mk _ fun a ↦ (hs a).desc (Cofan.mk t.pt (fun b ↦ t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ ↦ (hs a).hom_ext fun ⟨b⟩ ↦ ?_
    erw [hc.fac, (hs a).fac]
    simpa using h ⟨a, b⟩

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  limMap (Discrete.natTrans fun X => p X.as)

@[simp]
lemma Pi.map_id {f : α → C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

lemma Pi.map_comp_map {f g h : α → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Pi.map q ≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a) := by
  ext; simp

instance Pi.map_mono {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Mono (p i)] : Mono <| Pi.map p :=
  @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/-- Construct a morphism between categorical products from a family of morphisms between the
    factors. -/
def Pi.map' {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[reassoc (attr := simp)]
lemma Pi.map'_comp_π {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) (b : β) : Pi.map' p q ≫ Pi.π g b = Pi.π f (p b) ≫ q b :=
  limit.lift_π _ _

lemma Pi.map'_id_id {f : α → C} [HasProduct f] : Pi.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[simp]
lemma Pi.map'_id {f g : α → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) :
    Pi.map' id p = Pi.map p :=
  rfl

lemma Pi.map'_comp_map' {f : α → C} {g : β → C} {h : γ → C} [HasProduct f] [HasProduct g]
    [HasProduct h] (p : β → α) (p' : γ → β) (q : ∀ (b : β), f (p b) ⟶ g b)
    (q' : ∀ (c : γ), g (p' c) ⟶ h c) :
    Pi.map' p q ≫ Pi.map' p' q' = Pi.map' (p ∘ p') (fun c => q (p' c) ≫ q' c) := by
  ext; simp

lemma Pi.map'_comp_map {f : α → C} {g h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (b : β), f (p b) ⟶ g b) (q' : ∀ (b : β), g b ⟶ h b) :
    Pi.map' p q ≫ Pi.map q' = Pi.map' p (fun b => q b ≫ q' b) := by
  ext; simp

lemma Pi.map_comp_map' {f g : α → C} {h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (b : β), g (p b) ⟶ h b) :
    Pi.map q ≫ Pi.map' p q' = Pi.map' p (fun b => q (p b) ≫ q' b) := by
  ext; simp

lemma Pi.map'_eq {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] {p p' : β → α}
    {q : ∀ (b : β), f (p b) ⟶ g b} {q' : ∀ (b : β), f (p' b) ⟶ g b} (hp : p = p')
    (hq : ∀ (b : β), eqToHom (hp ▸ rfl) ≫ q b = q' b) : Pi.map' p q = Pi.map' p' q' := by
  aesop_cat

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ᶜ f ≅ ∏ᶜ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

section

/- In this section, we provide some API for products when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasProduct (fun j => X.obj (Discrete.mk j))]

/-- A limit cone for `X : Discrete α ⥤ C` that is given
by `∏ᶜ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
def Pi.cone : Cone X where
  pt := ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

/-- The cone `Pi.cone X` is a limit cone. -/
def productIsProduct' :
    IsLimit (Pi.cone X) where
  lift s := Pi.lift (fun j => s.π.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply hm

variable [HasLimit X]

/-- The isomorphism `∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X`. -/
def Pi.isoLimit :
    ∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X :=
  IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[reassoc (attr := simp)]
lemma Pi.isoLimit_inv_π (j : α) :
    (Pi.isoLimit X).inv ≫ Pi.π _ j = limit.π _ (Discrete.mk j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]
lemma Pi.isoLimit_hom_π (j : α) :
    (Pi.isoLimit X).hom ≫ limit.π _ (Discrete.mk j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

end

/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) :
    ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)

@[simp]
lemma Sigma.map_id {f : α → C} [HasCoproduct f] : Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

lemma Sigma.map_comp_map {f g h : α → C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Sigma.map q ≫ Sigma.map q' = Sigma.map (fun a => q a ≫ q' a) := by
  ext; simp

instance Sigma.map_epi {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Epi (p i)] : Epi <| Sigma.map p :=
  @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/-- Construct a morphism between categorical coproducts from a family of morphisms between the
    factors. -/
def Sigma.map' {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g] (p : α → β)
    (q : ∀ (a : α), f a ⟶ g (p a)) : ∐ f ⟶ ∐ g :=
  Sigma.desc (fun a => q a ≫ Sigma.ι _ _)

@[reassoc (attr := simp)]
lemma Sigma.ι_comp_map' {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g]
    (p : α → β) (q : ∀ (a : α), f a ⟶ g (p a)) (a : α) :
    Sigma.ι f a ≫ Sigma.map' p q = q a ≫ Sigma.ι g (p a) :=
  colimit.ι_desc _ _

lemma Sigma.map'_id_id {f : α → C} [HasCoproduct f] :
    Sigma.map' id (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

@[simp]
lemma Sigma.map'_id {f g : α → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) :
    Sigma.map' id p = Sigma.map p :=
  rfl

lemma Sigma.map'_comp_map' {f : α → C} {g : β → C} {h : γ → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (p' : β → γ) (q : ∀ (a : α), f a ⟶ g (p a))
    (q' : ∀ (b : β), g b ⟶ h (p' b)) :
    Sigma.map' p q ≫ Sigma.map' p' q' = Sigma.map' (p' ∘ p) (fun a => q a ≫ q' (p a)) := by
  ext; simp

lemma Sigma.map'_comp_map {f : α → C} {g h : β → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (q : ∀ (a : α), f a ⟶ g (p a)) (q' : ∀ (b : β), g b ⟶ h b) :
    Sigma.map' p q ≫ Sigma.map q' = Sigma.map' p (fun a => q a ≫ q' (p a)) := by
  ext; simp

lemma Sigma.map_comp_map' {f g : α → C} {h : β → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h (p a)) :
    Sigma.map q ≫ Sigma.map' p q' = Sigma.map' p (fun a => q a ≫ q' a) := by
  ext; simp

lemma Sigma.map'_eq {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g]
    {p p' : α → β} {q : ∀ (a : α), f a ⟶ g (p a)} {q' : ∀ (a : α), f a ⟶ g (p' a)}
    (hp : p = p') (hq : ∀ (a : α), q a ≫ eqToHom (hp ▸ rfl) = q' a) :
    Sigma.map' p q = Sigma.map' p' q' := by
  aesop_cat

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)

/-- Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
def Pi.whiskerEquiv {J K : Type*} {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasProduct f] [HasProduct g] : ∏ᶜ f ≅ ∏ᶜ g where
  hom := Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

/-- Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
def Sigma.whiskerEquiv {J K : Type*} {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasCoproduct f] [HasCoproduct g] : ∐ f ≅ ∐ g where
  hom := Sigma.map' e fun j => (w j).inv
  inv := Sigma.map' e.symm fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom

#adaptation_note /-- nightly-2024-04-01
The last proof was previously by `aesop_cat`. -/
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ᶜ fun i => ∏ᶜ g i) (fun X => Pi.π (fun i => ∏ᶜ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := mkFanLimit _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩)
        (by aesop_cat) (by intro s m w; simp only [Fan.mk_pt]; symm; ext i x; simp_all) }

/-- An iterated product is a product over a sigma type. -/
@[simps]
def piPiIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

#adaptation_note /-- nightly-2024-04-01
The last proof was previously by `aesop_cat`. -/
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    HasCoproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk (∐ fun i => ∐ g i)
        (fun X => Sigma.ι (g X.1) X.2 ≫ Sigma.ι (fun i => ∐ g i) X.1)
      isColimit := mkCofanColimit _
        (fun s => Sigma.desc fun b => Sigma.desc fun c => s.inj ⟨b, c⟩)
        (by aesop_cat) (by intro s m w; simp only [Cofan.mk_pt]; symm; ext i x; simp_all) }

/-- An iterated coproduct is a coproduct over a sigma type. -/
@[simps]
def sigmaSigmaIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    (∐ fun i => ∐ g i) ≅ (∐ fun p : Σ i, f i => g p.1 p.2) where
  hom := Sigma.desc fun i => Sigma.desc fun x => Sigma.ι (fun p : Σ i, f i => g p.1 p.2) ⟨i, x⟩
  inv := Sigma.desc fun ⟨i, x⟩ => Sigma.ι (g i) x ≫ Sigma.ι (fun i => ∐ g i) i

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
variable (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `PreservesProduct.ofIsoComparison`. -/
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] :
    G.obj (∏ᶜ f) ⟶ ∏ᶜ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[reassoc (attr := simp)]
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

@[reassoc (attr := simp)]
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Discrete.functor_obj, Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_pt, Fan.mk_π_app]

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`. -/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] :
    ∐ (fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]
theorem ι_comp_sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)

@[reassoc (attr := simp)]
theorem sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext j
  simp only [Discrete.functor_obj, ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc,
    Cofan.mk_pt, Cofan.mk_ι_app]

end Comparison

variable (C)

/-- An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C` -/
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

/-- An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C` -/
abbrev HasCoproducts :=
  ∀ J : Type w, HasColimitsOfShape (Discrete J) C

variable {C}

theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} J) ≌ _)

theorem has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C :=
  fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} J) ≌ _)

theorem hasProducts_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_isLimit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cones.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

/-!
(Co)products over a type with a unique term.
-/


section Unique

variable [Unique β] (f : β → C)

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
def limitConeOfUnique : LimitCone (Discrete.functor f) where
  cone :=
    { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        have h := Subsingleton.elim j default
        subst h
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }

instance (priority := 100) hasProduct_unique : HasProduct f :=
  HasLimit.mk (limitConeOfUnique f)

/-- A product over an index type with exactly one term is just the object over that term. -/
@[simps!]
def productUniqueIso : ∏ᶜ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
def colimitCoconeOfUnique : ColimitCocone (Discrete.functor f) where
  cocone :=
    { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        have h := Subsingleton.elim j default
        subst h
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        erw [Category.id_comp] at w
        exact w }

instance (priority := 100) hasCoproduct_unique : HasCoproduct f :=
  HasColimit.mk (colimitCoconeOfUnique f)

/-- A coproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
def coproductUniqueIso : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

end Unique

section Reindex

variable {γ : Type w'} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

@[reassoc (attr := simp)]
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

@[reassoc (attr := simp)]
theorem Sigma.ι_reindex_hom (b : β) :
    Sigma.ι (f ∘ ε) b ≫ (Sigma.reindex ε f).hom = Sigma.ι f (ε b) := by
  dsimp [Sigma.reindex]
  simp only [HasColimit.isoOfEquivalence_hom_π, Functor.id_obj, Discrete.functor_obj,
    Function.comp_apply, Discrete.equivalence_functor, Discrete.equivalence_inverse,
    Functor.comp_obj, Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  have h := colimit.w (Discrete.functor f) (Discrete.eqToHom' (ε.apply_symm_apply (ε b)))
  simp only [Discrete.functor_obj] at h
  erw [← h, eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  all_goals { simp }

@[reassoc (attr := simp)]
theorem Sigma.ι_reindex_inv (b : β) :
    Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by simp [Iso.comp_inv_eq]

end

end Reindex

end CategoryTheory.Limits
