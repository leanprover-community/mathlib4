/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.DiscreteCategory

#align_import category_theory.limits.shapes.products from "leanprover-community/mathlib"@"e11bafa5284544728bd3b189942e930e0d4701de"

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

universe w v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

-- We don't need an analogue of `Pair` (for binary products), `ParallelPair` (for equalizers),
-- or `(Co)span`, since we already have `Discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)
#align category_theory.limits.fan CategoryTheory.Limits.Fan

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)
#align category_theory.limits.cofan CategoryTheory.Limits.Cofan

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps! pt π_app]
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  pt := P
  π := Discrete.natTrans (fun X => p X.as)
#align category_theory.limits.fan.mk CategoryTheory.Limits.Fan.mk

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps! pt ι_app]
def Cofan.mk {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : Cofan f where
  pt := P
  ι := Discrete.natTrans (fun X => p X.as)
#align category_theory.limits.cofan.mk CategoryTheory.Limits.Cofan.mk

/-- Get the `j`th map in the fan -/
def Fan.proj {f : β → C} (p : Fan f) (j : β) : p.pt ⟶ f j :=
  p.π.app (Discrete.mk j)
#align category_theory.limits.fan.proj CategoryTheory.Limits.Fan.proj

/-- Get the `j`th map in the cofan -/
def Cofan.proj {f : β → C} (p : Cofan f) (j : β) : f j ⟶ p.pt :=
  p.ι.app (Discrete.mk j)

@[simp]
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) (j : β) : (Fan.mk P p).proj j = p j :=
  rfl
#align category_theory.limits.fan_mk_proj CategoryTheory.Limits.fan_mk_proj

@[simp]
theorem cofan_mk_proj {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) (j : β) :
    (Cofan.mk P p).proj j = p j :=
  rfl

/-- An abbreviation for `HasLimit (Discrete.functor f)`. -/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)
#align category_theory.limits.has_product CategoryTheory.Limits.HasProduct

/-- An abbreviation for `HasColimit (Discrete.functor f)`. -/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)
#align category_theory.limits.has_coproduct CategoryTheory.Limits.HasCoproduct

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkFanLimit {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.pt ⟶ t.pt)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by aesop_cat)
    (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by aesop_cat) :
    IsLimit t :=
  { lift }
#align category_theory.limits.mk_fan_limit CategoryTheory.Limits.mkFanLimit

/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
def mkCofanColimit {f : β → C} (s : Cofan f) (desc : ∀ t : Cofan f, s.pt ⟶ t.pt)
    (fac : ∀ (t : Cofan f) (j : β), s.proj j ≫ desc t = t.proj j := by aesop_cat)
    (uniq : ∀ (t : Cofan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, s.proj j ≫ m = t.proj j),
      m = desc t := by aesop_cat) :
    IsColimit s :=
  { desc }

section

variable (C)

/-- An abbreviation for `HasLimitsOfShape (Discrete f)`. -/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)
#align category_theory.limits.has_products_of_shape CategoryTheory.Limits.HasProductsOfShape

/-- An abbreviation for `HasColimitsOfShape (Discrete f)`. -/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)
#align category_theory.limits.has_coproducts_of_shape CategoryTheory.Limits.HasCoproductsOfShape

end

/-- `piObj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (Discrete.functor f)`,
so for most facts about `piObj f`, you will just use general facts about limits.) -/
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)
#align category_theory.limits.pi_obj CategoryTheory.Limits.piObj

/-- `sigmaObj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (Discrete.functor f)`,
so for most facts about `sigmaObj f`, you will just use general facts about colimits.) -/
abbrev sigmaObj (f : β → C) [HasCoproduct f] :=
  colimit (Discrete.functor f)
#align category_theory.limits.sigma_obj CategoryTheory.Limits.sigmaObj

/-- notation for categorical products -/
notation "∏ " f:60 => piObj f

/-- notation for categorical coproducts -/
notation "∐ " f:60 => sigmaObj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)
#align category_theory.limits.pi.π CategoryTheory.Limits.Pi.π

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbrev Sigma.ι (f : β → C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) (Discrete.mk b)
#align category_theory.limits.sigma.ι CategoryTheory.Limits.Sigma.ι

-- porting note: added the next two lemmas to ease automation; without these lemmas,
-- `limit.hom_ext` would be applied, but the goal would involve terms
-- in `Discrete β` rather than `β` itself
@[ext 1050]
lemma Pi.hom_ext {f : β → C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ f)
    (h : ∀ (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

@[ext 1050]
lemma Sigma.hom_ext {f : β → C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
    (h : ∀ (b : β), Sigma.ι f b ≫ g₁ = Sigma.ι f b ≫ g₂) : g₁ = g₂ :=
  colimit.hom_ext (fun ⟨j⟩ => h j)

/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cones.ext (Iso.refl _))
#align category_theory.limits.product_is_product CategoryTheory.Limits.productIsProduct

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocones.ext (Iso.refl _))
#align category_theory.limits.coproduct_is_coproduct CategoryTheory.Limits.coproductIsCoproduct

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `Pi.whisker_equiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem Pi.π_comp_eqToHom (f : J → C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  cases w
  simp

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `Sigma.whisker_equiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem Sigma.eqToHom_comp_ι (f : J → C) [HasCoproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j := by
  cases w
  simp

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ f :=
  limit.lift _ (Fan.mk P p)
#align category_theory.limits.pi.lift CategoryTheory.Limits.Pi.lift

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)
#align category_theory.limits.sigma.desc CategoryTheory.Limits.Sigma.desc

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
  limMap (Discrete.natTrans fun X => p X.as)
#align category_theory.limits.pi.map CategoryTheory.Limits.Pi.map

instance Pi.map_mono {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Mono (p i)] : Mono <| Pi.map p :=
  @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)
#align category_theory.limits.pi.map_mono CategoryTheory.Limits.Pi.map_mono

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ f ≅ ∏ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)
#align category_theory.limits.pi.map_iso CategoryTheory.Limits.Pi.mapIso

/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)
#align category_theory.limits.sigma.map CategoryTheory.Limits.Sigma.map

instance Sigma.map_epi {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Epi (p i)] : Epi <| Sigma.map p :=
  @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)
#align category_theory.limits.sigma.map_epi CategoryTheory.Limits.Sigma.map_epi

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)
#align category_theory.limits.sigma.map_iso CategoryTheory.Limits.Sigma.mapIso

/-- Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
def Pi.whisker_equiv {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasProduct f] [HasProduct g] : ∏ f ≅ ∏ g where
  hom := Pi.lift fun k => Pi.π f (e.symm k) ≫ (w _).inv ≫ eqToHom (by simp)
  inv := Pi.lift fun j => Pi.π g (e j) ≫ (w j).hom

/-- Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
def Sigma.whisker_equiv {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasCoproduct f] [HasCoproduct g] : ∐ f ≅ ∐ g where
  hom := Sigma.desc fun j => (w j).inv ≫ Sigma.ι g (e j)
  inv := Sigma.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ Sigma.ι f _

instance (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ fun i => ∏ g i) (fun X => Pi.π (fun i => ∏ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := mkFanLimit _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩) }

/-- An iterated product is a product over a sigma type. -/
@[simps]
def piPiIso (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ g i] :
    (∏ fun i => ∏ g i) ≅ (∏ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

instance (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    HasCoproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk (∐ fun i => ∐ g i)
        (fun X => Sigma.ι (g X.1) X.2 ≫ Sigma.ι (fun i => ∐ g i) X.1)
      isColimit := mkCofanColimit _
        (fun s => Sigma.desc fun b => Sigma.desc fun c => s.proj ⟨b, c⟩) }

/-- An iterated coproduct is a coproduct over a sigma type. -/
@[simps]
def sigmaSigmaIso (f : ι → Type*) (g : (i : ι) → (f i) → C)
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
    G.obj (∏ f) ⟶ ∏ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)
#align category_theory.limits.pi_comparison CategoryTheory.Limits.piComparison

@[reassoc (attr := simp)]
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)
#align category_theory.limits.pi_comparison_comp_π CategoryTheory.Limits.piComparison_comp_π

@[reassoc (attr := simp)]
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Discrete.functor_obj, Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
#align category_theory.limits.map_lift_pi_comparison CategoryTheory.Limits.map_lift_piComparison

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`. -/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] :
    ∐ (fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)
#align category_theory.limits.sigma_comparison CategoryTheory.Limits.sigmaComparison

@[reassoc (attr := simp)]
theorem ι_comp_sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)
#align category_theory.limits.ι_comp_sigma_comparison CategoryTheory.Limits.ι_comp_sigmaComparison

@[reassoc (attr := simp)]
theorem sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext j
  simp only [Discrete.functor_obj, ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc,
    Cofan.mk_pt, Cofan.mk_ι_app]
#align category_theory.limits.sigma_comparison_map_desc CategoryTheory.Limits.sigmaComparison_map_desc

end Comparison

variable (C)

/-- An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C` -/
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C
#align category_theory.limits.has_products CategoryTheory.Limits.HasProducts

/-- An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C` -/
abbrev HasCoproducts :=
  ∀ J : Type w, HasColimitsOfShape (Discrete J) C
#align category_theory.limits.has_coproducts CategoryTheory.Limits.HasCoproducts

variable {C}

theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} J) ≌ _)
#align category_theory.limits.has_smallest_products_of_has_products CategoryTheory.Limits.has_smallest_products_of_hasProducts

theorem has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C :=
  fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} J) ≌ _)
#align category_theory.limits.has_smallest_coproducts_of_has_coproducts CategoryTheory.Limits.has_smallest_coproducts_of_hasCoproducts

theorem hasProducts_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_is_limit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cones.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_is_limit _)⟩ }
#align category_theory.limits.has_products_of_limit_fans CategoryTheory.Limits.hasProducts_of_limit_fans

/-!
(Co)products over a type with a unique term.
-/


section Unique

variable [Unique β] (f : β → C)

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
def limitConeOfUnique : LimitCone (Discrete.functor f)
    where
  cone :=
    { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        apply Subsingleton.elim)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        have h := Subsingleton.elim j default
        subst h
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }
#align category_theory.limits.limit_cone_of_unique CategoryTheory.Limits.limitConeOfUnique

instance (priority := 100) hasProduct_unique : HasProduct f :=
  HasLimit.mk (limitConeOfUnique f)
#align category_theory.limits.has_product_unique CategoryTheory.Limits.hasProduct_unique

/-- A product over an index type with exactly one term is just the object over that term. -/
@[simps!]
def productUniqueIso : ∏ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit
#align category_theory.limits.product_unique_iso CategoryTheory.Limits.productUniqueIso

/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
def colimitCoconeOfUnique : ColimitCocone (Discrete.functor f)
    where
  cocone :=
    { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        apply Subsingleton.elim)) }
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
#align category_theory.limits.colimit_cocone_of_unique CategoryTheory.Limits.colimitCoconeOfUnique

instance (priority := 100) hasCoproduct_unique : HasCoproduct f :=
  HasColimit.mk (colimitCoconeOfUnique f)
#align category_theory.limits.has_coproduct_unique CategoryTheory.Limits.hasCoproduct_unique

/-- A coproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
def coproductUniqueIso : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit
#align category_theory.limits.coproduct_unique_iso CategoryTheory.Limits.coproductUniqueIso

end Unique

section Reindex

variable {γ : Type v} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)
#align category_theory.limits.pi.reindex CategoryTheory.Limits.Pi.reindex

@[reassoc (attr := simp)]
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))
#align category_theory.limits.pi.reindex_hom_π CategoryTheory.Limits.Pi.reindex_hom_π

@[reassoc (attr := simp)]
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]
#align category_theory.limits.pi.reindex_inv_π CategoryTheory.Limits.Pi.reindex_inv_π

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)
#align category_theory.limits.sigma.reindex CategoryTheory.Limits.Sigma.reindex

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
#align category_theory.limits.sigma.ι_reindex_hom CategoryTheory.Limits.Sigma.ι_reindex_hom

@[reassoc (attr := simp)]
theorem Sigma.ι_reindex_inv (b : β) :
    Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by simp [Iso.comp_inv_eq]
#align category_theory.limits.sigma.ι_reindex_inv CategoryTheory.Limits.Sigma.ι_reindex_inv

end

end Reindex

end CategoryTheory.Limits
