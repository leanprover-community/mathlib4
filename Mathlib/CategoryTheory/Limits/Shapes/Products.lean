/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

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
@[to_dual
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/]
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[to_dual (attr := implicit_reducible, simps!)
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/]
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  pt := P
  π := Discrete.natTrans (fun X => p X.as)

/-- Get the `j`th "projection" in the fan.
(Note that the initial letter of `proj` matches the greek letter in `Cone.π`.) -/
@[to_dual inj
/-- Get the `j`th "injection" in the cofan.
(Note that the initial letter of `inj` matches the greek letter in `Cocone.ι`.) -/]
def Fan.proj {f : β → C} (p : Fan f) (j : β) : p.pt ⟶ f j :=
  p.π.app (Discrete.mk j)

@[to_dual (attr := simp) cofan_mk_inj]
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : (Fan.mk P p).proj = p :=
  rfl

/-- An abbreviation for `HasLimit (Discrete.functor f)`. -/
@[to_dual /-- An abbreviation for `HasColimit (Discrete.functor f)`. -/]
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

@[to_dual]
lemma hasCoproduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasCoproduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasCoproduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α

insert_to_dual_translation CategoryTheory.Limits.Fan.IsLimit CategoryTheory.Limits.Cofan.IsColimit

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
just a convenience lemma to avoid having to go through `Discrete` -/
@[to_dual (attr := simps)
/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
just a convenience lemma to avoid having to go through `Discrete` -/]
def Fan.IsLimit.mk {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.pt ⟶ t.pt)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by cat_disch)
    (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by cat_disch) :
    IsLimit t :=
  { lift }

@[deprecated (since := "2026-05-19")]
alias mkFanLimit := Fan.IsLimit.mk

/-- Constructor for morphisms to the point of a limit fan. -/
@[to_dual desc
/-- Constructor for morphisms from the point of a colimit cofan. -/]
def Fan.IsLimit.lift {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) : A ⟶ c.pt :=
  hc.lift (Fan.mk A f)

@[to_dual (attr := reassoc (attr := simp))]
lemma Fan.IsLimit.fac {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) (i : β) :
    Fan.IsLimit.lift hc f ≫ c.proj i = f i :=
  hc.fac (Fan.mk A f) ⟨i⟩

@[to_dual (attr := reassoc (attr := simp)) inj_desc]
lemma Fan.IsLimit.lift_proj {X : β → C} {c : Fan X} (d : Fan X) (hc : IsLimit c)
    (i : β) : hc.lift d ≫ c.proj i = d.proj i :=
  hc.fac _ _

@[to_dual]
lemma Fan.IsLimit.hom_ext {I : Type*} {F : I → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f g : A ⟶ c.pt) (h : ∀ i, f ≫ c.proj i = g ≫ c.proj i) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

@[deprecated (since := "2026-05-19")]
alias mkCofanColimit := Cofan.IsColimit.mk

variable (C) in
/-- An abbreviation for `HasLimitsOfShape (Discrete f)`. -/
@[to_dual /-- An abbreviation for `HasColimitsOfShape (Discrete f)`. -/]
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/-- `piObj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (Discrete.functor f)`,
so for most facts about `piObj f`, you will just use general facts about limits.) -/
@[to_dual sigmaObj
/-- `sigmaObj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (Discrete.functor f)`,
so for most facts about `sigmaObj f`, you will just use general facts about colimits.) -/]
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)

/-- notation for categorical products. We need `ᶜ` to avoid conflict with `Finset.prod`. -/
notation "∏ᶜ " f:60 => piObj f

/-- notation for categorical coproducts -/
notation "∐ " f:60 => sigmaObj f

insert_to_dual_translation CategoryTheory.Limits.Pi CategoryTheory.Limits.Sigma

/-- The `b`-th projection from the pi object over `f` has the form `∏ᶜ f ⟶ f b`. -/
@[to_dual ι
/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/]
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ᶜ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[to_dual (attr := ext 1050)
/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/]
lemma Pi.hom_ext {f : β → C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
    (h : ∀ (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
-- We use `existing` because `to_dual` translates `Cone.ext` to `Cocone.ext_inv`, not `Cocone.ext`.
@[to_dual existing]
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[to_dual (attr := reassoc) eqToHom_comp_ι]
theorem Pi.π_comp_eqToHom {J : Type*} (f : J → C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  simp [*]

attribute [simp] Sigma.eqToHom_comp_ι Sigma.eqToHom_comp_ι_assoc

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ᶜ f`. -/
@[to_dual desc /-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/]
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ᶜ f :=
  limit.lift _ (Fan.mk P p)

@[to_dual (attr := simp) desc_ι]
theorem Pi.lift_π {f : β → C} [HasProduct f] : Pi.lift (Pi.π f) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[to_dual instIsIsoDescι]
instance {f : β → C} [HasProduct f] : IsIso (Pi.lift (Pi.π f)) := by
  simp [IsIso.id]

@[to_dual (attr := reassoc, elementwise) ι_comp_desc]
theorem Pi.lift_comp_π {β : Type w} {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_π_app]

@[deprecated (since := "2026-08-17")] alias Pi.lift_π_apply := Pi.lift_comp_π_apply
@[deprecated (since := "2026-08-17")] alias Pi.lift_π_assoc := Pi.lift_comp_π_assoc
@[deprecated (since := "2026-08-17")] alias Sigma.ι_desc := Sigma.ι_comp_desc
@[deprecated (since := "2026-08-17")] alias Sigma.ι_desc_apply := Sigma.ι_comp_desc_apply
@[deprecated (since := "2026-08-17")] alias Sigma.ι_desc_assoc := Sigma.ι_comp_desc_assoc

/-- A version of `Cone.ext` for `Fan`s. -/
@[to_dual (attr := simps!) extInv /-- A version of `Cocone.ext` for `Cofan`s. -/]
def Fan.ext {f : β → C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.proj b = e.hom ≫ c₂.proj b := by cat_disch) : c₁ ≅ c₂ :=
  Cone.ext e (fun ⟨j⟩ => w j)

/-- A version of `Cone.ext` for `Fan`s. -/
@[to_dual (attr := reducible, simps! -isSimp) ext /-- A version of `Cocone.ext` for `Cofan`s. -/]
def Fan.extInv {f : β → C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), e.inv ≫ c₁.proj b = c₂.proj b := by cat_disch) : c₁ ≅ c₂ :=
  Cone.extInv e (fun ⟨j⟩ => w j)

/-- A fan `c` on `f` such that the induced map `c.pt ⟶ ∏ f` is an iso, is a product. -/
@[to_dual isColimitOfIsIsoSigmaDesc
/-- A cofan `c` on `f` such that the induced map `∐ f ⟶ c.pt` is an iso, is a coproduct. -/]
def Fan.isLimitOfIsIsoPiLift {f : β → C} [HasProduct f] (c : Fan f)
    [hc : IsIso (Pi.lift c.proj)] : IsLimit c :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm

@[to_dual nonempty_isColimit_iff_isIso_sigmaDesc]
lemma Fan.nonempty_isLimit_iff_isIso_piLift {f : β → C} [HasProduct f] (c : Fan f) :
    Nonempty (IsLimit c) ↔ IsIso (Pi.lift c.proj) :=
  (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

/-- A coproduct of coproducts is a coproduct -/
def Cofan.isColimitTrans {X : α → C} (c : Cofan X) (hc : IsColimit c)
    {β : α → Type*} {Y : (a : α) → β a → C} (π : (a : α) → (b : β a) → Y a b ⟶ X a)
      (hs : ∀ a, IsColimit (Cofan.mk (X a) (π a))) :
        IsColimit (Cofan.mk (f := fun ⟨a,b⟩ => Y a b) c.pt
          (fun (⟨a, b⟩ : Σ a, _) ↦ π a b ≫ c.inj a)) := by
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · exact fun t ↦ hc.desc (Cofan.mk _ fun a ↦ (hs a).desc (Cofan.mk t.pt (fun b ↦ t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ ↦ (hs a).hom_ext fun ⟨b⟩ ↦ ?_
    erw [hc.fac, (hs a).fac]
    simpa using! h ⟨a, b⟩

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
@[to_dual
/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/]
def Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  limMap (Discrete.natTrans fun X => p X.as)

@[to_dual (attr := reassoc (attr := simp), elementwise nosimp) ι_map]
lemma Pi.map_π {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) (b : β) :
    Pi.map p ≫ Pi.π g b = Pi.π f b ≫ p b := by simp [Pi.map]

@[to_dual (attr := simp)]
lemma Pi.map_id {f : α → C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[to_dual]
lemma Pi.map_comp_map {f g h : α → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Pi.map q ≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a) := by
  ext; simp

@[to_dual map_epi]
instance Pi.map_mono {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Mono (p i)] : Mono <| Pi.map p :=
  @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/-- Construct a morphism between categorical products from a family of morphisms between the
factors. -/
@[to_dual
/-- Construct a morphism between categorical coproducts from a family of morphisms between the
factors. -/]
def Pi.map' {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[to_dual (attr := reassoc (attr := simp)) ι_comp_map']
lemma Pi.map'_comp_π {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) (b : β) : Pi.map' p q ≫ Pi.π g b = Pi.π f (p b) ≫ q b :=
  limit.lift_π _ _

@[to_dual]
lemma Pi.map'_id_id {f : α → C} [HasProduct f] : Pi.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[to_dual (attr := simp)]
lemma Pi.map'_id {f g : α → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) :
    Pi.map' id p = Pi.map p :=
  rfl

@[to_dual]
lemma Pi.map'_comp_map' {f : α → C} {g : β → C} {h : γ → C} [HasProduct f] [HasProduct g]
    [HasProduct h] (p : β → α) (p' : γ → β) (q : ∀ (b : β), f (p b) ⟶ g b)
    (q' : ∀ (c : γ), g (p' c) ⟶ h c) :
    Pi.map' p q ≫ Pi.map' p' q' = Pi.map' (p ∘ p') (fun c => q (p' c) ≫ q' c) := by
  ext; simp

@[to_dual map_comp_map']
lemma Pi.map'_comp_map {f : α → C} {g h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (b : β), f (p b) ⟶ g b) (q' : ∀ (b : β), g b ⟶ h b) :
    Pi.map' p q ≫ Pi.map q' = Pi.map' p (fun b => q b ≫ q' b) := by
  ext; simp

@[to_dual map'_comp_map]
lemma Pi.map_comp_map' {f g : α → C} {h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (b : β), g (p b) ⟶ h b) :
    Pi.map q ≫ Pi.map' p q' = Pi.map' p (fun b => q (p b) ≫ q' b) := by
  ext; simp

@[to_dual]
lemma Pi.map'_eq {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] {p p' : β → α}
    {q : ∀ (b : β), f (p b) ⟶ g b} {q' : ∀ (b : β), f (p' b) ⟶ g b} (hp : p = p')
    (hq : ∀ (b : β), eqToHom (hp ▸ rfl) ≫ q b = q' b) : Pi.map' p q = Pi.map' p' q' := by
  cat_disch

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
@[to_dual
/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/]
def Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ᶜ f ≅ ∏ᶜ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

@[to_dual (attr := reassoc (attr := simp)) ι_mapIso_inv]
lemma Pi.mapIso_hom_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).hom ≫ π _ _ = π _ _ ≫ (p b).hom :=
  limMap_π _ _

@[to_dual (attr := reassoc (attr := simp)) ι_mapIso_hom]
lemma Pi.mapIso_inv_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).inv ≫ π _ _ = π _ _ ≫ (p b).inv :=
  limMap_π _ _

@[to_dual]
instance Pi.map_isIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ⟶ g b)
    [∀ b, IsIso <| p b] : IsIso <| Pi.map p :=
  inferInstanceAs (IsIso (Pi.mapIso (fun b ↦ asIso (p b))).hom)

section

/- In this section, we provide some API for products when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasProduct (fun j => X.obj (Discrete.mk j))]

/-- A limit cone for `X : Discrete α ⥤ C` that is given
by `∏ᶜ (fun j => X.obj (Discrete.mk j))`. -/
@[to_dual (attr := simps)
/-- A colimit cocone for `X : Discrete α ⥤ C` that is given
by `∐ (fun j => X.obj (Discrete.mk j))`. -/]
def Pi.cone : Cone X where
  pt := ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

set_option backward.defeqAttrib.useBackward true in
/-- The cone `Pi.cone X` is a limit cone. -/
@[to_dual /-- The cocone `Sigma.cocone X` is a colimit cocone. -/]
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
@[to_dual /-- The isomorphism `∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X`. -/]
def Pi.isoLimit : ∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X :=
  IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[to_dual (attr := reassoc (attr := simp)) ι_isoColimit_hom]
lemma Pi.isoLimit_inv_π (j : α) :
    (Pi.isoLimit X).inv ≫ Pi.π _ j = limit.π _ (Discrete.mk j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) ι_isoColimit_inv]
lemma Pi.isoLimit_hom_π (j : α) :
    (Pi.isoLimit X).hom ≫ limit.π _ (Discrete.mk j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

end

/-- Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[to_dual (attr := simps)
/-- Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/]
def Pi.whiskerEquiv {J K : Type*} {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasProduct f] [HasProduct g] : ∏ᶜ f ≅ ∏ᶜ g where
  hom := Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

@[to_dual]
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ᶜ fun i => ∏ᶜ g i) (fun X => Pi.π (fun i => ∏ᶜ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := Fan.IsLimit.mk _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩)
        (by simp)
        (by intro s (m : _ ⟶ (∏ᶜ fun i ↦ ∏ᶜ g i)) w; aesop (add norm simp Sigma.forall)) }

/-- An iterated product is a product over a sigma type. -/
@[to_dual (attr := simps) sigmaSigmaIso
/-- An iterated coproduct is a coproduct over a sigma type. -/]
def piPiIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
variable (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `PreservesProduct.ofIsoComparison`. -/
@[to_dual sigmaComparison
/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`. -/]
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] :
    G.obj (∏ᶜ f) ⟶ ∏ᶜ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[to_dual (attr := reassoc (attr := simp), elementwise nosimp) ι_comp_sigmaComparison]
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

@[to_dual (attr := reassoc (attr := simp)) sigmaComparison_map_desc]
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

/-- `F.mapCone c` being limiting is the same as the induced fan being limiting. -/
@[to_dual
/-- `F.mapCocone c` being colimiting is the same as the induced cofan being colimiting. -/]
def Fan.isLimitMapConeEquiv (F : C ⥤ D) {ι : Type*} (X : ι → C) (c : Fan X) :
    IsLimit (F.mapCone c) ≃ IsLimit (Fan.mk _ fun i ↦ F.map (c.proj i)) :=
  (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans <|
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

end Comparison

variable (C) in
/-- An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C` -/
@[to_dual /-- An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C` -/]
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

@[to_dual]
lemma hasProducts_shrink [HasProducts.{max w w'} C] : HasProducts.{w} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

@[to_dual]
theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C :=
  hasProducts_shrink

@[to_dual hasCoproducts_of_colimit_cofans]
theorem hasProducts_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_isLimit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

@[to_dual]
instance (priority := 100) hasProductsOfShape_of_hasProducts [HasProducts.{w} C] (J : Type w) :
    HasProductsOfShape J C := inferInstance

open Opposite in
/-- The functor sending `(X, n)` to the product of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
def piConst [Limits.HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where
  obj X := { obj n := ∏ᶜ fun _ : (unop n :) ↦ X, map f := Limits.Pi.map' f.unop fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ ↦ f }

/-- `n ↦ ∏ₙ X` is left adjoint to `Hom(-, X)`. -/
def piConstAdj [Limits.HasProducts.{v} C] (X : C) :
    (piConst.obj X).rightOp ⊣ yoneda.obj X where
  unit := { app n := ↾fun i ↦ Limits.Pi.π (fun _ : n ↦ X) i }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

-- Note: We may consider making `sigmaConst` an abbrev in order to
-- improve automation downstream
/-- The functor sending `(X, n)` to the coproduct of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
def sigmaConst [Limits.HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where
  obj X := { obj n := ∐ fun _ : n ↦ X, map f := Limits.Sigma.map' f fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ ↦ f }

/-- `n ↦ ∐ₙ X` is left adjoint to `Hom(X, -)`. -/
def sigmaConstAdj [Limits.HasCoproducts.{v} C] (X : C) :
    sigmaConst.obj X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app n := ↾fun i ↦ Limits.Sigma.ι (fun _ : n ↦ X) i }
  counit := { app Y := Limits.Sigma.desc id }

/-!
(Co)products over a type with a unique term.
-/


section Unique

/-- The limit cone for the product over an index type with exactly one term. -/
@[to_dual (attr := simps)
/-- The colimit cocone for the coproduct over an index type with exactly one term. -/]
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

@[to_dual]
instance (priority := 100) hasProduct_unique [Nonempty β] [Subsingleton β] (f : β → C) :
    HasProduct f :=
  let ⟨_⟩ := nonempty_unique β; HasLimit.mk (limitConeOfUnique f)

/-- A product over an index type with exactly one term is just the object over that term. -/
@[to_dual
/-- A coproduct over an index type with exactly one term is just the object over that term. -/]
def productUniqueIso [Unique β] (f : β → C) : ∏ᶜ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

@[to_dual (attr := simp) coproductUniqueIso_inv]
lemma productUniqueIso_hom [Unique β] (f : β → C) : (productUniqueIso f).hom = Pi.π f default :=
  rfl

@[to_dual (attr := reassoc (attr := simp)) ι_coproductUniqueIso_hom]
lemma productUniqueIso_inv_π [Unique β] (f : β → C) (b : β) :
    (productUniqueIso f).inv ≫ Pi.π f b = eqToHom (congrArg _ <| Subsingleton.allEq _ _) := by
  obtain rfl := Subsingleton.allEq b default
  simp [Iso.inv_comp_eq]

@[deprecated (since := "2026-06-30")] alias productUniqueIso_inv := productUniqueIso_inv_π
@[deprecated (since := "2026-06-30")] alias coproductUniqueIso_hom := ι_coproductUniqueIso_hom

/-- Any isomorphism is the projection from a single object product. -/
@[to_dual /-- Any isomorphism is the projection from a single object product. -/]
def Fan.isLimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsLimit (Fan.mk X fun _ : J ↦ e.hom) := by
  refine Fan.IsLimit.mk _ (fun s ↦ s.proj default ≫ e.inv) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

end Unique

section Reindex

variable {γ : Type w'} (ε : β ≃ γ) (f : γ → C) [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
@[to_dual /-- Reindex a categorical coproduct via an equivalence of the index types. -/]
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

@[to_dual (attr := reassoc (attr := simp)) ι_reindex_hom]
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [reindex]

@[to_dual (attr := reassoc (attr := simp)) ι_reindex_inv]
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  simp [← Iso.eq_inv_comp]

variable {f} in
/-- Being a limiting fan is stable under equivalences in the index type. -/
@[to_dual /-- Being a colimiting cofan is stable under equivalences in the index type. -/]
def Fan.isLimitEquivOfEquiv (c : Fan f) :
    IsLimit c ≃ IsLimit (Fan.mk _ fun i : β ↦ c.proj (ε i)) :=
  IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end Reindex

section

variable {J : Type u₂} [Category.{v₂} J] (F : J ⥤ C)

@[to_dual instEpiDescι]
instance [HasLimit F] [HasProduct F.obj] : Mono (Pi.lift (limit.π F)) where
  right_cancellation _ _ h := by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j

end

section Thin

variable [Quiver.IsThin C] {J : Type*} [Category* J] {K : J ⥤ C}

/-- If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components. -/
@[to_dual
/-- If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components. -/]
def isLimitEquivFanOfIsThin (c : Cone K) : IsLimit c ≃ IsLimit (Fan.mk c.pt c.π.app) where
  toFun hc := Fan.IsLimit.mk _ (fun s ↦ hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

end Thin

section Fubini

variable {ι ι' : Type*} {X : ι → ι' → C}

/-- A product over products is a product indexed by a product. -/
@[to_dual /-- A coproduct over coproducts is a coproduct indexed by a product. -/]
def Fan.IsLimit.prod (c : ∀ i : ι, Fan (fun j : ι' ↦ X i j)) (hc : ∀ i : ι, IsLimit (c i))
    (c' : Fan (fun i : ι ↦ (c i).pt)) (hc' : IsLimit c') :
    (IsLimit <| Fan.mk c'.pt fun p : ι × ι' ↦ c'.proj _ ≫ (c p.1).proj p.2) := by
  refine Fan.IsLimit.mk _ (fun t ↦ ?_) ?_ fun t m hm ↦ ?_
  · exact Fan.IsLimit.lift hc' fun i ↦ Fan.IsLimit.lift (hc i) fun j ↦ t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i ↦ ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j ↦ (by simpa using hm (i, j))

end Fubini

variable (α) in
/-- The functor `(f : α → C) ↦ ∏ᶜ f`. -/
@[to_dual (attr := simps) /-- The functor `(f : α → C) ↦ ∐ f`. -/]
noncomputable def Pi.functor [HasProductsOfShape α C] : (α → C) ⥤ C where
  obj f := ∏ᶜ f
  map {f g} t := Pi.map t

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation induced by `Pi.π`. -/
@[to_dual (attr := simps) /-- The natural transformation induced by `Sigma.ι`. -/]
def Pi.functorπ [HasProductsOfShape α C] (a : α) :
    Pi.functor α ⟶ Pi.eval (fun _ ↦ C) a where
  app f := Pi.π f a

set_option backward.defeqAttrib.useBackward true in
variable (α) in
/-- Up to pre-composing with an equivalence of categories, `Pi.functor` is isomorphic to `lim`. -/
@[to_dual (attr := simps!)
/-- Up to pre-composing with an equivalence of categories, `Sigma.functor` is isomorphic
to `colim`. -/]
def piEquivalenceFunctorDiscreteCompLim [HasProductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ lim ≅ Pi.functor _ :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc)]
lemma piEquivalenceFunctorDiscreteCompLim_comp_functorπ [HasProductsOfShape α C] (a : α) :
    (piEquivalenceFunctorDiscreteCompLim (C := C) α).hom ≫ Pi.functorπ a =
      Functor.whiskerLeft _ (lim.π <| Discrete.mk a) ≫
        (piEquivalenceFunctorDiscreteCompEvaluationIso _ _).hom := by
  cat_disch

@[to_dual]
lemma piEquivalenceFunctorDiscrete_functor_comp_lim [HasProductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ lim = Pi.functor _ :=
  rfl

attribute [local simp] Functor.pi in
/-- The `∏ᶜ` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∏ᶜ X`. -/
@[to_dual (attr := simps!) constCompSigmaIsoConst
/-- The `∐` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∐ X`. -/]
noncomputable def Pi.constCompPiIsoConst [HasProductsOfShape α C] {I : α → Type*}
    [∀ i, Category* (I i)] (X : α → C) :
    Functor.pi (fun i ↦ (Functor.const (I i)).obj (X i)) ⋙ Pi.functor α ≅
      (Functor.const _).obj (∏ᶜ X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

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
