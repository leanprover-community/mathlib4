/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Discrete.Basic

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
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

@[expose] public section

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
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : (Fan.mk P p).proj = p :=
  rfl

@[simp]
theorem cofan_mk_inj {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : (Cofan.mk P p).inj = p :=
  rfl

/-- An abbreviation for `HasLimit (Discrete.functor f)`. -/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

/-- An abbreviation for `HasColimit (Discrete.functor f)`. -/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)

lemma hasCoproduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasCoproduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasCoproduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α

lemma hasProduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasProduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasProduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimit_of_iso α.symm

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkFanLimit {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.pt ⟶ t.pt)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by cat_disch)
    (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by cat_disch) :
    IsLimit t :=
  { lift }

/-- Constructor for morphisms to the point of a limit fan. -/
def Fan.IsLimit.lift {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) : A ⟶ c.pt :=
  hc.lift (Fan.mk A f)

@[deprecated (since := "2026-01-12")] alias Fan.IsLimit.desc := Fan.IsLimit.lift

@[reassoc (attr := simp)]
lemma Fan.IsLimit.fac {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) (i : β) :
    Fan.IsLimit.lift hc f ≫ c.proj i = f i :=
  hc.fac (Fan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]
lemma Fan.IsLimit.lift_proj {X : β → C} {c : Fan X} (d : Fan X) (hc : IsLimit c)
    (i : β) : hc.lift d ≫ c.proj i = d.proj i :=
  hc.fac _ _

lemma Fan.IsLimit.hom_ext {I : Type*} {F : I → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f g : A ⟶ c.pt) (h : ∀ i, f ≫ c.proj i = g ≫ c.proj i) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkCofanColimit {f : β → C} (s : Cofan f) (desc : ∀ t : Cofan f, s.pt ⟶ t.pt)
    (fac : ∀ (t : Cofan f) (j : β), s.inj j ≫ desc t = t.inj j := by cat_disch)
    (uniq : ∀ (t : Cofan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, s.inj j ≫ m = t.inj j),
      m = desc t := by cat_disch) :
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

@[reassoc (attr := simp)]
lemma Cofan.IsColimit.inj_desc {X : β → C} {c : Cofan X} (d : Cofan X) (hc : IsColimit c)
    (i : β) : c.inj i ≫ hc.desc d = d.inj i :=
  hc.fac _ _

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

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
lemma Pi.hom_ext {f : β → C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
    (h : ∀ (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
lemma Sigma.hom_ext {f : β → C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
    (h : ∀ (b : β), Sigma.ι f b ≫ g₁ = Sigma.ι f b ≫ g₂) : g₁ = g₂ :=
  colimit.hom_ext (fun ⟨j⟩ => h j)

set_option backward.defeqAttrib.useBackward true in
/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
theorem Pi.π_comp_eqToHom {J : Type*} (f : J → C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  simp [*]

@[reassoc (attr := simp)]
theorem Sigma.eqToHom_comp_ι {J : Type*} (f : J → C) [HasCoproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j := by
  cases w
  simp

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ᶜ f`. -/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ᶜ f :=
  limit.lift _ (Fan.mk P p)

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
theorem Pi.lift_π {β : Type w} {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_π_app]

/-- A version of `Cone.ext` for `Fan`s. -/
@[simps!]
def Fan.ext {f : β → C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.proj b = e.hom ≫ c₂.proj b := by cat_disch) : c₁ ≅ c₂ :=
  Cone.ext e (fun ⟨j⟩ => w j)

/-- A fan `c` on `f` such that the induced map `c.pt ⟶ ∏ f` is an iso, is a product. -/
def Fan.isLimitOfIsIsoPiLift {f : β → C} [HasProduct f] (c : Fan f)
    [hc : IsIso (Pi.lift c.proj)] : IsLimit c :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm

lemma Fan.nonempty_isLimit_iff_isIso_piLift {f : β → C} [HasProduct f] (c : Fan f) :
    Nonempty (IsLimit c) ↔ IsIso (Pi.lift c.proj) :=
  (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem Sigma.ι_desc {β : Type w} {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) (b : β) :
    Sigma.ι f b ≫ Sigma.desc p = p b := by
  simp only [colimit.ι_desc, Cofan.mk_ι_app]

set_option backward.isDefEq.respectTransparency false in
instance {f : β → C} [HasCoproduct f] : IsIso (Sigma.desc (fun a ↦ Sigma.ι f a)) := by
  convert IsIso.id _
  ext
  simp

/-- A version of `Cocone.ext` for `Cofan`s. -/
@[simps!]
def Cofan.ext {f : β → C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.inj b ≫ e.hom = c₂.inj b := by cat_disch) : c₁ ≅ c₂ :=
  Cocone.ext e (fun ⟨j⟩ => w j)

/-- A cofan `c` on `f` such that the induced map `∐ f ⟶ c.pt` is an iso, is a coproduct. -/
def Cofan.isColimitOfIsIsoSigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f)
    [hc : IsIso (Sigma.desc c.inj)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))

lemma Cofan.nonempty_isColimit_iff_isIso_sigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f) :
    Nonempty (IsColimit c) ↔ IsIso (Sigma.desc c.inj) :=
  (colimit.isColimit (Discrete.functor f)).nonempty_isColimit_iff_isIso_desc

@[deprecated (since := "2026-01-21")]
alias Cofan.isColimit_iff_isIso_sigmaDesc := Cofan.nonempty_isColimit_iff_isIso_sigmaDesc

set_option backward.defeqAttrib.useBackward true in
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
def Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  limMap (Discrete.natTrans fun X => p X.as)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise nosimp]
lemma Pi.map_π {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) (b : β) :
    Pi.map p ≫ Pi.π g b = Pi.π f b ≫ p b := by simp [Pi.map]

@[simp]
lemma Pi.map_id {f : α → C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

lemma Pi.map_comp_map {f g h : α → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Pi.map q ≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a) := by
  ext; simp

set_option backward.defeqAttrib.useBackward true in
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
  cat_disch

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
def Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ᶜ f ≅ ∏ᶜ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
lemma Pi.mapIso_hom_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).hom ≫ π _ _ = π _ _ ≫ (p b).hom :=
  limMap_π _ _

@[reassoc (attr := simp)]
lemma Pi.mapIso_inv_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).inv ≫ π _ _ = π _ _ ≫ (p b).inv :=
  limMap_π _ _

instance Pi.map_isIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ⟶ g b)
    [∀ b, IsIso <| p b] : IsIso <| Pi.map p :=
  inferInstanceAs (IsIso (Pi.mapIso (fun b ↦ asIso (p b))).hom)

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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
def Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) :
    ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Sigma.ι_map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) (b : β) :
    Sigma.ι f b ≫ Sigma.map p = p b ≫ Sigma.ι g b := by simp [Sigma.map]

@[simp]
lemma Sigma.map_id {f : α → C} [HasCoproduct f] : Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

lemma Sigma.map_comp_map {f g h : α → C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Sigma.map q ≫ Sigma.map q' = Sigma.map (fun a => q a ≫ q' a) := by
  ext; simp

set_option backward.defeqAttrib.useBackward true in
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
  cat_disch

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
def Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
lemma Sigma.ι_mapIso_hom {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).hom = (p b).hom ≫ ι _ _ :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
lemma Sigma.ι_mapIso_inv {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).inv = (p b).inv ≫ ι _ _ :=
  ι_colimMap _ _

instance Sigma.map_isIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ⟶ g b)
    [∀ b, IsIso <| p b] : IsIso (Sigma.map p) :=
  inferInstanceAs (IsIso (Sigma.mapIso (fun b ↦ asIso (p b))).hom)

section

/- In this section, we provide some API for coproducts when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasCoproduct (fun j => X.obj (Discrete.mk j))]

/-- A colimit cocone for `X : Discrete α ⥤ C` that is given
by `∐ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
def Sigma.cocone : Cocone X where
  pt := ∐ (fun j => X.obj (Discrete.mk j))
  ι := Discrete.natTrans (fun _ => Sigma.ι (fun j ↦ X.obj ⟨j⟩) _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone `Sigma.cocone X` is a colimit cocone. -/
def coproductIsCoproduct' :
    IsColimit (Sigma.cocone X) where
  desc s := Sigma.desc (fun j => s.ι.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply hm

variable [HasColimit X]

/-- The isomorphism `∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X`. -/
def Sigma.isoColimit :
    ∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct' X) (colimit.isColimit X)

@[reassoc (attr := simp)]
lemma Sigma.ι_isoColimit_hom (j : α) :
    Sigma.ι _ j ≫ (Sigma.isoColimit X).hom = colimit.ι _ (Discrete.mk j) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' X) _ _

@[reassoc (attr := simp)]
lemma Sigma.ι_isoColimit_inv (j : α) :
    colimit.ι _ ⟨j⟩ ≫ (Sigma.isoColimit X).inv = Sigma.ι (fun j ↦ X.obj ⟨j⟩) _ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

end

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ᶜ fun i => ∏ᶜ g i) (fun X => Pi.π (fun i => ∏ᶜ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := mkFanLimit _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩)
        (by simp)
        (by intro s (m : _ ⟶ (∏ᶜ fun i ↦ ∏ᶜ g i)) w; aesop (add norm simp Sigma.forall)) }

set_option backward.isDefEq.respectTransparency false in
/-- An iterated product is a product over a sigma type. -/
@[simps]
def piPiIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    HasCoproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk (∐ fun i => ∐ g i)
        (fun X => Sigma.ι (g X.1) X.2 ≫ Sigma.ι (fun i => ∐ g i) X.1)
      isColimit := mkCofanColimit _
        (fun s => Sigma.desc fun b => Sigma.desc fun c => s.inj ⟨b, c⟩)
        (by simp)
        (by intro s (m : (∐ fun i ↦ ∐ g i) ⟶ _) w; aesop_cat (add norm simp Sigma.forall)) }

set_option backward.isDefEq.respectTransparency false in
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

@[reassoc (attr := simp), elementwise nosimp]
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`. -/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] :
    ∐ (fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]
theorem ι_comp_sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext j
  simp only [ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc, Cofan.mk_ι_app]

set_option backward.defeqAttrib.useBackward true in
/-- `F.mapCone c` being limiting is the same as the induced fan being limiting. -/
def Fan.isLimitMapConeEquiv (F : C ⥤ D) {ι : Type*} (X : ι → C) (c : Fan X) :
    IsLimit (F.mapCone c) ≃ IsLimit (Fan.mk _ fun i ↦ F.map (c.proj i)) :=
  (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans <|
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- `F.mapCocone c` being colimiting is the same as the induced cofan being colimiting. -/
def Cofan.isColimitMapCoconeEquiv (F : C ⥤ D) {ι : Type*} (X : ι → C) (c : Cofan X) :
    IsColimit (F.mapCocone c) ≃ IsColimit (Cofan.mk _ fun i ↦ F.map (c.inj i)) :=
  (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans <|
    IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

end Comparison

variable (C)

/-- An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C` -/
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

/-- An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C` -/
abbrev HasCoproducts :=
  ∀ J : Type w, HasColimitsOfShape (Discrete J) C

variable {C}

lemma hasProducts_shrink [HasProducts.{max w w'} C] : HasProducts.{w} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

lemma hasCoproducts_shrink [HasCoproducts.{max w w'} C] : HasCoproducts.{w} C := fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C :=
  hasProducts_shrink

theorem has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C :=
  hasCoproducts_shrink

theorem hasProducts_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_isLimit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

theorem hasCoproducts_of_colimit_cofans (cf : ∀ {J : Type w} (f : J → C), Cofan f)
    (cf_isColimit : ∀ {J : Type w} (f : J → C), IsColimit (cf f)) : HasCoproducts.{w} C :=
  fun _ : Type w =>
  { has_colimit := fun F =>
      HasColimit.mk
        ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj (cf fun j => F.obj ⟨j⟩),
          (IsColimit.precomposeHomEquiv _ _).symm (cf_isColimit _)⟩ }

instance (priority := 100) hasProductsOfShape_of_hasProducts [HasProducts.{w} C] (J : Type w) :
    HasProductsOfShape J C := inferInstance

instance (priority := 100) hasCoproductsOfShape_of_hasCoproducts [HasCoproducts.{w} C]
    (J : Type w) : HasCoproductsOfShape J C := inferInstance

open Opposite in
/-- The functor sending `(X, n)` to the product of copies of `X` indexed by `n`. -/
@[simps]
def piConst [Limits.HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where
  obj X := { obj n := ∏ᶜ fun _ : (unop n :) ↦ X, map f := Limits.Pi.map' f.unop fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ ↦ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `n ↦ ∏ₙ X` is left adjoint to `Hom(-, X)`. -/
def piConstAdj [Limits.HasProducts.{v} C] (X : C) :
    (piConst.obj X).rightOp ⊣ yoneda.obj X where
  unit := { app n := TypeCat.ofHom (fun i ↦ Limits.Pi.π (fun _ : n ↦ X) i) }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

/-- The functor sending `(X, n)` to the coproduct of copies of `X` indexed by `n`. -/
@[simps]
def sigmaConst [Limits.HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where
  obj X := { obj n := ∐ fun _ : n ↦ X, map f := Limits.Sigma.map' f fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ ↦ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `n ↦ ∐ₙ X` is left adjoint to `Hom(X, -)`. -/
def sigmaConstAdj [Limits.HasCoproducts.{v} C] (X : C) :
    sigmaConst.obj X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app n := TypeCat.ofHom (fun i ↦ Limits.Sigma.ι (fun _ : n ↦ X) i) }
  counit := { app Y := Limits.Sigma.desc id }

/-!
(Co)products over a type with a unique term.
-/


section Unique

set_option backward.defeqAttrib.useBackward true in
/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
def limitConeOfUnique [Unique β] (f : β → C) : LimitCone (Discrete.functor f) where
  cone :=
    { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }

instance (priority := 100) hasProduct_unique [Nonempty β] [Subsingleton β] (f : β → C) :
    HasProduct f :=
  let ⟨_⟩ := nonempty_unique β; HasLimit.mk (limitConeOfUnique f)

/-- A product over an index type with exactly one term is just the object over that term. -/
@[simps!]
def productUniqueIso [Unique β] (f : β → C) : ∏ᶜ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

set_option backward.defeqAttrib.useBackward true in
/-- Any isomorphism is the projection from a single object product. -/
def Fan.isLimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsLimit (Fan.mk X fun _ : J ↦ e.hom) := by
  refine mkFanLimit _ (fun s ↦ s.proj default ≫ e.inv) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

set_option backward.defeqAttrib.useBackward true in
/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
def colimitCoconeOfUnique [Unique β] (f : β → C) : ColimitCocone (Discrete.functor f) where
  cocone :=
    { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        simp_all }

instance (priority := 100) hasCoproduct_unique [Nonempty β] [Subsingleton β] (f : β → C) :
    HasCoproduct f :=
  let ⟨_⟩ := nonempty_unique β; HasColimit.mk (colimitCoconeOfUnique f)

/-- A coproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
def coproductUniqueIso [Unique β] (f : β → C) : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

set_option backward.defeqAttrib.useBackward true in
/-- Any isomorphism is the projection from a single object product. -/
def Cofan.isColimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsColimit (Cofan.mk Y fun _ : J ↦ e.hom) := by
  refine mkCofanColimit _ (fun s ↦ e.inv ≫ s.inj default) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_epi e.hom] using hm default

end Unique

section Reindex

variable {γ : Type w'} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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

variable {f} in
/-- Being a limiting fan is stable under equivalences in the index type. -/
def Fan.isLimitEquivOfEquiv (c : Fan f) :
    IsLimit c ≃ IsLimit (Fan.mk _ fun i : β ↦ c.proj (ε i)) :=
  IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem Sigma.ι_reindex_inv (b : β) :
    Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by simp [Iso.comp_inv_eq]

variable {f} in
/-- Being a colimiting cofan is stable under equivalences in the index type. -/
def Cofan.isColimitEquivOfEquiv (c : Cofan f) :
    IsColimit c ≃ IsColimit (Cofan.mk _ fun i : β ↦ c.inj (ε i)) :=
  IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

end Reindex

section

variable {J : Type u₂} [Category.{v₂} J] (F : J ⥤ C)

set_option backward.isDefEq.respectTransparency false in
instance [HasLimit F] [HasProduct F.obj] : Mono (Pi.lift (limit.π F)) where
  right_cancellation _ _ h := by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j

set_option backward.isDefEq.respectTransparency false in
instance [HasColimit F] [HasCoproduct F.obj] : Epi (Sigma.desc (colimit.ι F)) where
  left_cancellation _ _ h := by
    refine colimit.hom_ext fun j => ?_
    simpa using Sigma.ι _ j ≫= h

end

section Fubini

variable {ι ι' : Type*} {X : ι → ι' → C}

set_option backward.defeqAttrib.useBackward true in
/-- A product over products is a product indexed by a product. -/
def Fan.IsLimit.prod (c : ∀ i : ι, Fan (fun j : ι' ↦ X i j)) (hc : ∀ i : ι, IsLimit (c i))
    (c' : Fan (fun i : ι ↦ (c i).pt)) (hc' : IsLimit c') :
    (IsLimit <| Fan.mk c'.pt fun p : ι × ι' ↦ c'.proj _ ≫ (c p.1).proj p.2) := by
  refine mkFanLimit _ (fun t ↦ ?_) ?_ fun t m hm ↦ ?_
  · exact Fan.IsLimit.lift hc' fun i ↦ Fan.IsLimit.lift (hc i) fun j ↦ t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i ↦ ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j ↦ (by simpa using hm (i, j))

set_option backward.defeqAttrib.useBackward true in
/-- A coproduct over coproducts is a coproduct indexed by a product. -/
def Cofan.IsColimit.prod (c : ∀ i : ι, Cofan (fun j : ι' ↦ X i j)) (hc : ∀ i : ι, IsColimit (c i))
    (c' : Cofan (fun i : ι ↦ (c i).pt)) (hc' : IsColimit c') :
    (IsColimit <| Cofan.mk c'.pt fun p : ι × ι' ↦ (c p.1).inj p.2 ≫ c'.inj _) := by
  refine mkCofanColimit _ (fun t ↦ ?_) ?_ fun t m hm ↦ ?_
  · exact Cofan.IsColimit.desc hc' fun i ↦ Cofan.IsColimit.desc (hc i) fun j ↦ t.inj (i, j)
  · simp
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i ↦ ?_
    exact Cofan.IsColimit.hom_ext (hc i) _ _ fun j ↦ (by simpa using hm (i, j))

end Fubini

/-- The functor `C ⥤ (Type w)ᵒᵖ ⥤ C` which sends `X : C` and `α : Type w` to
the product of copies of `X` indexed by `α`. -/
@[simps]
def piFunctor [HasProducts.{w} C] :
    C ⥤ Type wᵒᵖ ⥤ C where
  obj X :=
    { obj α := ∏ᶜ (fun (t : α.unop) ↦ X)
      map f := Pi.map' f.unop (fun _ ↦ 𝟙 _) }
  map f := { app T := Pi.map (fun _ ↦ f) }

/-- The functor `C ⥤ Type w ⥤ C` which sends `X : C` and `α : Type w` to
the coproduct of copies of `X` indexed by `α`. -/
@[simps]
def sigmaFunctor [HasCoproducts.{w} C] :
    C ⥤ Type w ⥤ C where
  obj X :=
    { obj α := ∐ (fun (t : α) ↦ X)
      map f := Sigma.map' f (fun _ ↦ 𝟙 _) }
  map f := { app T := Sigma.map (fun _ ↦ f) }

end CategoryTheory.Limits
