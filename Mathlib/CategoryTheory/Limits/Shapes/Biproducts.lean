/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts.
Binary biproducts are defined in `CategoryTheory.Limits.Shapes.BinaryBiproducts`.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

For biproducts indexed by a `Fintype J`, a `bicone` consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation notes

Prior to https://github.com/leanprover-community/mathlib3/pull/14046,
`HasFiniteBiproducts` required a `DecidableEq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib),
and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

open scoped Classical in
/-- A `c : Bicone F` is:
* an object `c.pt` and
* morphisms `π j : pt ⟶ F j` and `ι j : F j ⟶ pt` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
structure Bicone (F : J → C) where
  pt : C
  π : ∀ j, pt ⟶ F j
  ι : ∀ j, F j ⟶ pt
  ι_π : ∀ j j', ι j ≫ π j' =
    if h : j = j' then eqToHom (congrArg F h) else 0 := by aesop

attribute [inherit_doc Bicone] Bicone.pt Bicone.π Bicone.ι Bicone.ι_π

@[reassoc (attr := simp)]
theorem bicone_ι_π_self {F : J → C} (B : Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j

@[reassoc (attr := simp)]
theorem bicone_ι_π_ne {F : J → C} (B : Bicone F) {j j' : J} (h : j ≠ j') : B.ι j ≫ B.π j' = 0 := by
  simpa [h] using B.ι_π j j'

variable {F : J → C}

/-- A bicone morphism between two bicones for the same diagram is a morphism of the bicone points
which commutes with the cone and cocone legs. -/
structure BiconeMorphism {F : J → C} (A B : Bicone F) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wπ : ∀ j : J, hom ≫ B.π j = A.π j := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wι : ∀ j : J, A.ι j ≫ hom = B.ι j := by cat_disch

attribute [reassoc (attr := simp)] BiconeMorphism.wι BiconeMorphism.wπ

/-- The category of bicones on a given diagram. -/
@[simps]
instance Bicone.category : Category (Bicone F) where
  Hom A B := BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/- We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
-- a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
theorem BiconeMorphism.ext {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Bicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
    (wι : ∀ j, c.ι j ≫ φ.hom = c'.ι j := by cat_disch)
    (wπ : ∀ j, φ.hom ≫ c'.π j = c.π j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm }

variable (F) in
/-- A functor `G : C ⥤ D` sends bicones over `F` to bicones over `G.obj ∘ F` functorially. -/
@[simps]
def functoriality (G : C ⥤ D) [Functor.PreservesZeroMorphisms G] :
    Bicone F ⥤ Bicone (G.obj ∘ F) where
  obj A :=
    { pt := G.obj A.pt
      π := fun j => G.map (A.π j)
      ι := fun j => G.map (A.ι j)
      ι_π := fun i j => (Functor.map_comp _ _ _).symm.trans <| by
        rw [A.ι_π]
        cat_disch }
  map f :=
    { hom := G.map f.hom
      wπ := fun j => by simp [-BiconeMorphism.wπ, ← f.wπ j]
      wι := fun j => by simp [-BiconeMorphism.wι, ← f.wι j] }

variable (G : C ⥤ D)

instance functoriality_full [G.PreservesZeroMorphisms] [G.Full] [G.Faithful] :
    (functoriality F G).Full where
  map_surjective t :=
   ⟨{ hom := G.preimage t.hom
      wι := fun j => G.map_injective (by simpa using t.wι j)
      wπ := fun j => G.map_injective (by simpa using t.wπ j) }, by cat_disch⟩

instance functoriality_faithful [G.PreservesZeroMorphisms] [G.Faithful] :
    (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    BiconeMorphism.ext f g <| G.map_injective <| congr_arg BiconeMorphism.hom h

end Bicones

namespace Bicone

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- Porting note: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

/-- Extract the cone from a bicone. -/
def toConeFunctor : Bicone F ⥤ Cone (Discrete.functor F) where
  obj B := { pt := B.pt, π := { app := fun j => B.π j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wπ _ }

/-- A shorthand for `toConeFunctor.obj` -/
abbrev toCone (B : Bicone F) : Cone (Discrete.functor F) := toConeFunctor.obj B

-- TODO Consider changing this API to `toFan (B : Bicone F) : Fan F`.

@[simp] theorem toCone_pt (B : Bicone F) : B.toCone.pt = B.pt := rfl

@[simp] theorem toCone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as := rfl

theorem toCone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j := rfl

@[simp] theorem toCone_proj (B : Bicone F) (j : J) : Fan.proj B.toCone j = B.π j := rfl

/-- Extract the cocone from a bicone. -/
def toCoconeFunctor : Bicone F ⥤ Cocone (Discrete.functor F) where
  obj B := { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wι _ }

/-- A shorthand for `toCoconeFunctor.obj` -/
abbrev toCocone (B : Bicone F) : Cocone (Discrete.functor F) := toCoconeFunctor.obj B

@[simp] theorem toCocone_pt (B : Bicone F) : B.toCocone.pt = B.pt := rfl

@[simp]
theorem toCocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as := rfl

@[simp] theorem toCocone_inj (B : Bicone F) (j : J) : Cofan.inj B.toCocone j = B.ι j := rfl

theorem toCocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j := rfl

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
def ofLimitCone {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f where
  pt := t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
theorem ι_of_isLimit {f : J → C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
def ofColimitCocone {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) :
    Bicone f where
  pt := t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
theorem π_of_isColimit {f : J → C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
structure IsBilimit {F : J → C} (B : Bicone F) where
  isLimit : IsLimit B.toCone
  isColimit : IsColimit B.toCocone

attribute [inherit_doc IsBilimit] IsBilimit.isLimit IsBilimit.isColimit

attribute [simp] IsBilimit.mk.injEq

attribute [local ext] Bicone.IsBilimit

instance subsingleton_isBilimit {f : J → C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

section Whisker

variable {K : Type w'}

set_option backward.isDefEq.respectTransparency false in
/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
def whisker {f : J → C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g) where
  pt := c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto

/-- Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism. -/
def whiskerToCone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCone ≅
      (Cones.postcompose (Discrete.functorComp f g).inv).obj
        (c.toCone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cones.ext (Iso.refl _) (by simp)

/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
def whiskerToCocone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocones.precompose (Discrete.functorComp f g).hom).obj
        (c.toCocone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cocones.ext (Iso.refl _) (by simp)

/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
noncomputable def whiskerIsBilimitIff {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).IsBilimit ≃ c.IsBilimit := by
  refine equivOfSubsingletonOfSubsingleton (fun hc => ⟨?_, ?_⟩) fun hc => ⟨?_, ?_⟩
  · let this := IsLimit.ofIsoLimit hc.isLimit (Bicone.whiskerToCone c g)
    let this := (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _) this
    exact IsLimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · let this := IsColimit.ofIsoColimit hc.isColimit (Bicone.whiskerToCocone c g)
    let this := (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _) this
    exact IsColimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · apply IsLimit.ofIsoLimit _ (Bicone.whiskerToCone c g).symm
    apply (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _).symm _
    exact IsLimit.whiskerEquivalence hc.isLimit (Discrete.equivalence g)
  · apply IsColimit.ofIsoColimit _ (Bicone.whiskerToCocone c g).symm
    apply (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _).symm _
    exact IsColimit.whiskerEquivalence hc.isColimit (Discrete.equivalence g)

end Whisker

end Bicone

/-- A bicone over `F : J → C`, which is both a limit cone and a colimit cocone. -/
structure LimitBicone (F : J → C) where
  bicone : Bicone F
  isBilimit : bicone.IsBilimit

attribute [inherit_doc LimitBicone] LimitBicone.bicone LimitBicone.isBilimit

/-- `HasBiproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`. -/
class HasBiproduct (F : J → C) : Prop where mk' ::
  exists_biproduct : Nonempty (LimitBicone F)

attribute [inherit_doc HasBiproduct] HasBiproduct.exists_biproduct

theorem HasBiproduct.mk {F : J → C} (d : LimitBicone F) : HasBiproduct F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `BiproductData F` from `HasBiproduct F`. -/
def getBiproductData (F : J → C) [HasBiproduct F] : LimitBicone F :=
  Classical.choice HasBiproduct.exists_biproduct

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone (F : J → C) [HasBiproduct F] : Bicone F :=
  (getBiproductData F).bicone

/-- `biproduct.bicone F` is a bilimit bicone. -/
def biproduct.isBilimit (F : J → C) [HasBiproduct F] : (biproduct.bicone F).IsBilimit :=
  (getBiproductData F).isBilimit

/-- `biproduct.bicone F` is a limit cone. -/
def biproduct.isLimit (F : J → C) [HasBiproduct F] : IsLimit (biproduct.bicone F).toCone :=
  (getBiproductData F).isBilimit.isLimit

/-- `biproduct.bicone F` is a colimit cocone. -/
def biproduct.isColimit (F : J → C) [HasBiproduct F] : IsColimit (biproduct.bicone F).toCocone :=
  (getBiproductData F).isBilimit.isColimit

instance (priority := 100) hasProduct_of_hasBiproduct [HasBiproduct F] : HasProduct F :=
  HasLimit.mk
    { cone := (biproduct.bicone F).toCone
      isLimit := biproduct.isLimit F }

instance (priority := 100) hasCoproduct_of_hasBiproduct [HasBiproduct F] : HasCoproduct F :=
  HasColimit.mk
    { cocone := (biproduct.bicone F).toCocone
      isColimit := biproduct.isColimit F }

variable (J C)

/-- `C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`. -/
class HasBiproductsOfShape : Prop where
  has_biproduct : ∀ F : J → C, HasBiproduct F

attribute [instance 100] HasBiproductsOfShape.has_biproduct

/-- A category `HasFiniteBiproducts` if it has a biproduct for every finite family of objects in `C`
indexed by a finite type. -/
class HasFiniteBiproducts : Prop where
  out : ∀ n, HasBiproductsOfShape (Fin n) C

attribute [inherit_doc HasFiniteBiproducts] HasFiniteBiproducts.out

variable {J}

theorem hasBiproductsOfShape_of_equiv {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K) :
    HasBiproductsOfShape J C :=
  ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.has_biproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
    HasBiproduct.mk <| by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩

instance (priority := 100) hasBiproductsOfShape_finite [HasFiniteBiproducts C] [Finite J] :
    HasBiproductsOfShape J C := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  haveI : HasBiproductsOfShape (Fin n) C := HasFiniteBiproducts.out n
  exact hasBiproductsOfShape_of_equiv C e

instance (priority := 100) hasFiniteProducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where
  out _ := ⟨fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

instance (priority := 100) hasFiniteCoproducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where
  out _ := ⟨fun _ => hasColimit_of_iso Discrete.natIsoFunctor⟩

instance (priority := 100) hasProductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasProductsOfShape J C where
  has_limit _ := hasLimit_of_iso Discrete.natIsoFunctor.symm

instance (priority := 100) hasCoproductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasCoproductsOfShape J C where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor

variable {C}

/-- The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit. -/
def biproductIso (F : J → C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans <|
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

variable {J : Type w} {K : Type*}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
abbreviation for `limit (Discrete.functor f)`, so for most facts about `biproduct f`, you will
just use general facts about limits and colimits.) -/
abbrev biproduct (f : J → C) [HasBiproduct f] : C :=
  (biproduct.bicone f).pt

@[inherit_doc biproduct]
notation "⨁ " f:20 => biproduct f

/-- The projection onto a summand of a biproduct. -/
abbrev biproduct.π (f : J → C) [HasBiproduct f] (b : J) : ⨁ f ⟶ f b :=
  (biproduct.bicone f).π b

@[simp]
theorem biproduct.bicone_π (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).π b = biproduct.π f b := rfl

/-- The inclusion into a summand of a biproduct. -/
abbrev biproduct.ι (f : J → C) [HasBiproduct f] (b : J) : f b ⟶ ⨁ f :=
  (biproduct.bicone f).ι b

@[simp]
theorem biproduct.bicone_ι (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).ι b = biproduct.ι f b := rfl

/-- Note that as this lemma has an `if` in the statement, we include a `DecidableEq` argument.
This means you may not be able to `simp` using this lemma unless you `open scoped Classical`. -/
@[reassoc]
theorem biproduct.ι_π [DecidableEq J] (f : J → C) [HasBiproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eqToHom (congr_arg f h) else 0 := by
  convert (biproduct.bicone f).ι_π j j'

@[reassoc] -- Not `simp` because `simp` can prove this
theorem biproduct.ι_π_self (f : J → C) [HasBiproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by simp

@[reassoc]
theorem biproduct.ι_π_ne (f : J → C) [HasBiproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by simp [h]

@[reassoc (attr := simp)]
theorem biproduct.eqToHom_comp_ι (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ biproduct.ι f j' = biproduct.ι f j := by
  cases w
  simp

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
theorem biproduct.π_comp_eqToHom (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    biproduct.π f j ≫ eqToHom (by simp [w]) = biproduct.π f j' := by
  simp [*]

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbrev biproduct.lift {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ⨁ f :=
  (biproduct.isLimit f).lift (Fan.mk P p)

/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbrev biproduct.desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ⨁ f ⟶ P :=
  (biproduct.isColimit f).desc (Cofan.mk P p)

@[reassoc (attr := simp)]
theorem biproduct.lift_π {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j := (biproduct.isLimit f).fac _ ⟨j⟩

@[reassoc (attr := simp)]
theorem biproduct.ι_desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j := (biproduct.isColimit f).fac _ ⟨j⟩

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbrev biproduct.map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbrev biproduct.map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)

-- We put this at slightly higher priority than `biproduct.hom_ext'`,
-- to get the matrix indices in the "right" order.
@[ext 1001]
theorem biproduct.hom_ext {f : J → C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]
theorem biproduct.hom_ext' {f : J → C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (biproduct.isColimit f).hom_ext fun j => w j.as

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biproduct.isoProduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∏ᶜ f :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biproduct.isoProduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by simp [biproduct.isoProduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biproduct.isoProduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biproduct.isoCoproduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biproduct.isoCoproduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).hom = biproduct.desc (Sigma.ι f) :=
  biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/-- If a category has biproducts of a shape `J`, its `colim` and `lim` functor on diagrams over `J`
are isomorphic. -/
@[simps!]
def HasBiproductsOfShape.colimIsoLim [HasBiproductsOfShape J C] :
    colim (J := Discrete J) (C := C) ≅ lim :=
  NatIso.ofComponents (fun F => (Sigma.isoColimit F).symm ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫ Pi.isoLimit F)
    fun η => colimit.hom_ext fun ⟨i⟩ => limit.hom_ext fun ⟨j⟩ => by
      classical
      by_cases h : i = j <;>
       simp_all [Sigma.isoColimit, Pi.isoLimit, biproduct.ι_π, biproduct.ι_π_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem biproduct.map_eq_map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  classical
  ext
  dsimp
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    ← Bicone.toCone_π_app_mk, ← Bicone.toCocone_ι_app_mk]
  dsimp
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs with h
  · subst h; simp
  · simp

@[reassoc (attr := simp)]
theorem biproduct.map_π {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[reassoc (attr := simp)]
theorem biproduct.ι_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j := by
  rw [biproduct.map_eq_map']
  apply
    Limits.IsColimit.ι_map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as) (Discrete.mk j)

@[reassoc (attr := simp)]
theorem biproduct.map_desc {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    {P : C} (k : ∀ j, g j ⟶ P) :
    biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j := by
  ext; simp

@[reassoc (attr := simp)]
theorem biproduct.lift_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] {P : C}
    (k : ∀ j, P ⟶ f j) (p : ∀ j, f j ⟶ g j) :
    biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j := by
  ext; simp

/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
def biproduct.mapIso {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ≅ g b) :
    ⨁ f ≅ ⨁ g where
  hom := biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv

set_option backward.isDefEq.respectTransparency false in
instance biproduct.map_epi {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Epi (p j)] : Epi (biproduct.map p) := by
  classical
  have : biproduct.map p =
      (biproduct.isoCoproduct _).hom ≫ Sigma.map p ≫ (biproduct.isoCoproduct _).inv := by
    ext
    simp only [map_π, isoCoproduct_hom, isoCoproduct_inv, Category.assoc, ι_desc_assoc,
      ι_colimMap_assoc, Discrete.functor_obj_eq_as, Discrete.natTrans_app, colimit.ι_desc_assoc,
      Cofan.mk_pt, Cofan.mk_ι_app, ι_π, ι_π_assoc]
    split
    all_goals simp_all
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance Pi.map_epi {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Epi (p j)] : Epi (Pi.map p) := by
  rw [show Pi.map p = (biproduct.isoProduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoProduct _).hom by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance biproduct.map_mono {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Mono (p j)] : Mono (biproduct.map p) := by
  rw [show biproduct.map p = (biproduct.isoProduct _).hom ≫ Pi.map p ≫
    (biproduct.isoProduct _).inv by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance Sigma.map_mono {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Mono (p j)] : Mono (Sigma.map p) := by
  rw [show Sigma.map p = (biproduct.isoCoproduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoCoproduct _).hom by aesop]
  infer_instance

/-- Two biproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.

Unfortunately there are two natural ways to define each direction of this isomorphism
(because it is true for both products and coproducts separately).
We give the alternative definitions as lemmas below. -/
@[simps]
def biproduct.whiskerEquiv {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasBiproduct f] [HasBiproduct g] : ⨁ f ≅ ⨁ g where
  hom := biproduct.desc fun j => (w j).inv ≫ biproduct.ι g (e j)
  inv := biproduct.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ biproduct.ι f _

lemma biproduct.whiskerEquiv_hom_eq_lift {f : J → C} {g : K → C} (e : J ≃ K)
    (w : ∀ j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).hom =
      biproduct.lift fun k => biproduct.π f (e.symm k) ≫ (w _).inv ≫ eqToHom (by simp) := by
  simp only [whiskerEquiv_hom]
  ext k j
  by_cases h : k = e j
  · subst h
    simp
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne, biproduct.ι_π_ne_assoc]
    · simp
    · rintro rfl
      simp at h
    · exact Ne.symm h

lemma biproduct.whiskerEquiv_inv_eq_lift {f : J → C} {g : K → C} (e : J ≃ K)
    (w : ∀ j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).inv =
      biproduct.lift fun j => biproduct.π g (e j) ≫ (w j).hom := by
  simp only [whiskerEquiv_inv]
  ext j k
  by_cases h : k = e j
  · subst h
    simp only [ι_desc_assoc, ← eqToHom_iso_hom_naturality_assoc w (e.symm_apply_apply j).symm,
      Equiv.symm_apply_apply, eqToHom_comp_ι, Category.assoc, bicone_ι_π_self, Category.comp_id,
      lift_π, bicone_ι_π_self_assoc]
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne, biproduct.ι_π_ne_assoc]
    · simp
    · exact h
    · rintro rfl
      simp at h

attribute [local simp] Sigma.forall in
instance {ι} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    HasBiproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_biproduct := Nonempty.intro
    { bicone :=
      { pt := ⨁ fun i => ⨁ g i
        ι := fun X => biproduct.ι (g X.1) X.2 ≫ biproduct.ι (fun i => ⨁ g i) X.1
        π := fun X => biproduct.π (fun i => ⨁ g i) X.1 ≫ biproduct.π (g X.1) X.2
        ι_π := fun ⟨j, x⟩ ⟨j', y⟩ => by
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            simp
          · simp only [Sigma.mk.inj_iff, not_and] at h
            by_cases w : j = j'
            · cases w
              simp only [heq_eq_eq, forall_true_left] at h
              simp [biproduct.ι_π_ne _ h]
            · simp [biproduct.ι_π_ne_assoc _ w] }
      isBilimit :=
      { isLimit := mkFanLimit _
          (fun s => biproduct.lift fun b => biproduct.lift fun c => s.proj ⟨b, c⟩)
        isColimit := mkCofanColimit _
          (fun s => biproduct.desc fun b => biproduct.desc fun c => s.inj ⟨b, c⟩) } }

/-- An iterated biproduct is a biproduct over a sigma type. -/
@[simps]
def biproductBiproductIso {ι} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    (⨁ fun i => ⨁ g i) ≅ (⨁ fun p : Σ i, f i => g p.1 p.2) where
  hom := biproduct.lift fun ⟨i, x⟩ => biproduct.π _ i ≫ biproduct.π _ x
  inv := biproduct.lift fun i => biproduct.lift fun x => biproduct.π _ (⟨i, x⟩ : Σ i, f i)

section πKernel

section

variable (f : J → C) [HasBiproduct f]
variable (p : J → Prop) [HasBiproduct (Subtype.restrict p f)]

/-- The canonical morphism from the biproduct over a restricted index type to the biproduct of
the full index type. -/
def biproduct.fromSubtype : ⨁ Subtype.restrict p f ⟶ ⨁ f :=
  biproduct.desc fun j => biproduct.ι _ j.val

/-- The canonical morphism from a biproduct to the biproduct over a restriction of its index
type. -/
def biproduct.toSubtype : ⨁ f ⟶ ⨁ Subtype.restrict p f :=
  biproduct.lift fun _ => biproduct.π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem biproduct.fromSubtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j =
      if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i; dsimp
  rw [biproduct.fromSubtype, biproduct.ι_desc_assoc, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show (i : J) ≠ j from fun h₂ => h (h₂ ▸ i.2)), comp_zero]

theorem biproduct.fromSubtype_eq_lift [DecidablePred p] :
    biproduct.fromSubtype f p =
      biproduct.lift fun j => if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] -- Not `@[simp]` because `simp` can prove this
theorem biproduct.fromSubtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.fromSubtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
theorem biproduct.toSubtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrict p f) j = biproduct.π f j :=
  biproduct.lift_π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem biproduct.ι_toSubtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p =
      if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i
  rw [biproduct.toSubtype, Category.assoc, biproduct.lift_π, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show j ≠ i from fun h₂ => h (h₂.symm ▸ i.2)), zero_comp]

theorem biproduct.toSubtype_eq_desc [DecidablePred p] :
    biproduct.toSubtype f p =
      biproduct.desc fun j => if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext' _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem biproduct.ι_toSubtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.toSubtype, Category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
theorem biproduct.ι_fromSubtype (j : Subtype p) :
    biproduct.ι (Subtype.restrict p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem biproduct.fromSubtype_toSubtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrict p f) := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, biproduct.toSubtype_π, biproduct.fromSubtype_π_subtype, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem biproduct.toSubtype_fromSubtype [DecidablePred p] :
    biproduct.toSubtype f p ≫ biproduct.fromSubtype f p =
      biproduct.map fun j => if p j then 𝟙 (f j) else 0 := by
  ext1 i
  by_cases h : p i
  · simp [h]
  · simp [h]

end

section

variable (f : J → C) (i : J) [HasBiproduct f] [HasBiproduct (Subtype.restrict (fun j => j ≠ i) f)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits `i`
from the index set `J` into the biproduct over `J`. -/
def biproduct.isLimitFromSubtype :
    IsLimit (KernelFork.ofι (biproduct.fromSubtype f fun j => j ≠ i) (by simp) :
    KernelFork (biproduct.π f i)) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      apply biproduct.hom_ext; intro j
      rw [KernelFork.ι_ofι, Category.assoc, Category.assoc,
        biproduct.toSubtype_fromSubtype_assoc, biproduct.map_π]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), comp_zero, comp_zero, KernelFork.condition]
      · rw [if_pos (Ne.symm h), Category.comp_id], by
      intro m hm
      rw [← hm, KernelFork.ι_ofι, Category.assoc, biproduct.fromSubtype_toSubtype]
      exact (Category.comp_id _).symm⟩

instance : HasKernel (biproduct.π f i) :=
  HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

/-- The kernel of `biproduct.π f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
def kernelBiproductπIso : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The cokernel of `biproduct.ι f i` is the projection from the biproduct over the index set `J`
onto the biproduct omitting `i`. -/
def biproduct.isColimitToSubtype :
    IsColimit (CokernelCofork.ofπ (biproduct.toSubtype f fun j => j ≠ i) (by simp) :
    CokernelCofork (biproduct.ι f i)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      apply biproduct.hom_ext'; intro j
      rw [CokernelCofork.π_ofπ, biproduct.toSubtype_fromSubtype_assoc, biproduct.ι_map_assoc]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), zero_comp, CokernelCofork.condition]
      · rw [if_pos (Ne.symm h), Category.id_comp], by
      intro m hm
      rw [← hm, CokernelCofork.π_ofπ, ← Category.assoc, biproduct.fromSubtype_toSubtype]
      exact (Category.id_comp _).symm⟩

instance : HasCokernel (biproduct.ι f i) :=
  HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

/-- The cokernel of `biproduct.ι f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
def cokernelBiproductιIso : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩

end

section

-- Per https://github.com/leanprover-community/mathlib3/pull/15067, we only allow indexing in `Type 0` here.
variable {K : Type} [Finite K] [HasFiniteBiproducts C] (f : K → C)

set_option backward.isDefEq.respectTransparency false in
/-- The limit cone exhibiting `⨁ Subtype.restrict pᶜ f` as the kernel of
`biproduct.toSubtype f p` -/
@[simps]
def kernelForkBiproductToSubtype (p : K → Prop) :
    LimitCone (parallelPair (biproduct.toSubtype f p) 0) where
  cone :=
    KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        rw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.IsLimit.ofι _ _ (fun {_} g _ => g ≫ biproduct.toSubtype f pᶜ)
      (by
        classical
        intro W' g' w
        ext j
        simp only [Category.assoc, biproduct.toSubtype_fromSubtype, Pi.compl_apply,
          biproduct.map_π]
        split_ifs with h
        · simp
        · replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩
          simpa using w.symm)
      (by cat_disch)

instance (p : K → Prop) : HasKernel (biproduct.toSubtype f p) :=
  HasLimit.mk (kernelForkBiproductToSubtype f p)

/-- The kernel of `biproduct.toSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
def kernelBiproductToSubtypeIso (p : K → Prop) :
    kernel (biproduct.toSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  limit.isoLimitCone (kernelForkBiproductToSubtype f p)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit cocone exhibiting `⨁ Subtype.restrict pᶜ f` as the cokernel of
`biproduct.fromSubtype f p` -/
@[simps]
def cokernelCoforkBiproductFromSubtype (p : K → Prop) :
    ColimitCocone (parallelPair (biproduct.fromSubtype f p) 0) where
  cocone :=
    CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exact not_not.mpr k.2)
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _ (fun {_} g _ => biproduct.fromSubtype f pᶜ ≫ g)
      (by
        classical
        intro W g' w
        ext j
        simp only [biproduct.toSubtype_fromSubtype_assoc, Pi.compl_apply, biproduct.ι_map_assoc]
        split_ifs with h
        · simp
        · replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : Subtype p) ≫= w
          simpa using w.symm)
      (by cat_disch)

instance (p : K → Prop) : HasCokernel (biproduct.fromSubtype f p) :=
  HasColimit.mk (cokernelCoforkBiproductFromSubtype f p)

/-- The cokernel of `biproduct.fromSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
def cokernelBiproductFromSubtypeIso (p : K → Prop) :
    cokernel (biproduct.fromSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

end

end πKernel

section FiniteBiproducts

variable {J : Type} [Finite J] {K : Type} [Finite K] {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C] {f : J → C} {g : K → C}

/-- Convert a (dependently typed) matrix to a morphism of biproducts. -/
def biproduct.matrix (m : ∀ j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k

@[reassoc (attr := simp)]
theorem biproduct.matrix_π (m : ∀ j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k := by
  ext
  simp [biproduct.matrix]

@[reassoc (attr := simp)]
theorem biproduct.ι_matrix (m : ∀ j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k := by
  simp [biproduct.matrix]

/-- Extract the matrix components from a morphism of biproducts. -/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]
theorem biproduct.matrix_components (m : ∀ j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by simp [biproduct.components]

@[simp]
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) :
    (biproduct.matrix fun j k => biproduct.components m j k) = m := by
  ext
  simp [biproduct.components]

/-- Morphisms between direct sums are matrices. -/
@[simps]
def biproduct.matrixEquiv : (⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k where
  toFun := biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components

end FiniteBiproducts

variable {J : Type w}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

instance biproduct.ι_mono (f : J → C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) := by
  classical exact IsSplitMono.mk' { retraction := biproduct.desc <| Pi.single b (𝟙 (f b)) }

instance biproduct.π_epi (f : J → C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) := by
  classical exact IsSplitEpi.mk' { section_ := biproduct.lift <| Pi.single b (𝟙 (f b)) }

/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
theorem biproduct.conePointUniqueUpToIso_hom (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).hom = biproduct.lift b.π :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
theorem biproduct.conePointUniqueUpToIso_inv (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).inv = biproduct.desc b.ι := by
  classical
  refine biproduct.hom_ext' _ _ fun j => hb.isLimit.hom_ext fun j' => ?_
  rw [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp, Bicone.toCone_π_app,
    biproduct.bicone_π, biproduct.ι_desc, biproduct.ι_π, b.toCone_π_app, b.ι_π]

/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
but in the case of biproducts we can give an isomorphism with particularly nice definitional
properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
other. -/
@[simps]
def biproduct.uniqueUpToIso (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    b.pt ≅ ⨁ f where
  hom := biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb, ←
      biproduct.conePointUniqueUpToIso_inv f hb, Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb, ←
      biproduct.conePointUniqueUpToIso_inv f hb, Iso.inv_hom_id]

variable (C)

-- see Note [lower instance priority]
/-- A category with finite biproducts has a zero object. -/
instance (priority := 100) hasZeroObject_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasZeroObject C := by
  refine ⟨⟨biproduct Empty.elim, fun X => ⟨⟨⟨0⟩, ?_⟩⟩, fun X => ⟨⟨⟨0⟩, ?_⟩⟩⟩⟩
  · intro a; apply biproduct.hom_ext'; simp
  · intro a; apply biproduct.hom_ext; simp

section

variable {C}

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
def limitBiconeOfUnique [Unique J] (f : J → C) : LimitBicone f where
  bicone :=
    { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq])
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq]) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }

instance (priority := 100) hasBiproduct_unique [Subsingleton J] [Nonempty J] (f : J → C) :
    HasBiproduct f :=
  let ⟨_⟩ := nonempty_unique J; .mk (limitBiconeOfUnique f)

/-- A biproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
def biproductUniqueIso [Unique J] (f : J → C) : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

end

end CategoryTheory.Limits
