/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `BinaryBicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `BinaryBicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

For biproducts indexed by a `Fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation notes

Prior to leanprover-community/mathlib#14046,
`HasFiniteBiproducts` required a `DecidableEq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib),
 and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

noncomputable section

universe w w' v u

open CategoryTheory

open CategoryTheory.Functor

open scoped Classical

namespace CategoryTheory

namespace Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/-- A `c : Bicone F` is:
* an object `c.pt` and
* morphisms `π j : pt ⟶ F j` and `ι j : F j ⟶ pt` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed
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
  wπ : ∀ j : J, hom ≫ B.π j = A.π j := by aesop_cat
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wι : ∀ j : J, A.ι j ≫ hom = B.ι j := by aesop_cat

attribute [reassoc (attr := simp)] BiconeMorphism.wι
attribute [reassoc (attr := simp)] BiconeMorphism.wπ

/-- The category of bicones on a given diagram. -/
@[simps]
instance Bicone.category : Category (Bicone F) where
  Hom A B := BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

-- Porting note: if we do not have `simps` automatically generate the lemma for simplifying
-- the `hom` field of a category, we need to write the `ext` lemma in terms of the categorical
-- morphism, rather than the underlying structure.
@[ext]
theorem BiconeMorphism.ext {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Bicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
-- Porting note: `@[ext]` used to accept lemmas like this. Now we add an aesop rule
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
    (wι : ∀ j, c.ι j ≫ φ.hom = c'.ι j := by aesop_cat)
    (wπ : ∀ j, φ.hom ≫ c'.π j = c.π j := by aesop_cat) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm  }

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
        aesop_cat }
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
      wπ := fun j => G.map_injective (by simpa using t.wπ j) }, by aesop_cat⟩

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
  map {X Y} F := { hom := F.hom, w := fun _ => F.wπ _ }

/-- A shorthand for `toConeFunctor.obj` -/
abbrev toCone (B : Bicone F) : Cone (Discrete.functor F) := toConeFunctor.obj B

-- TODO Consider changing this API to `toFan (B : Bicone F) : Fan F`.

@[simp]
theorem toCone_pt (B : Bicone F) : B.toCone.pt = B.pt := rfl

@[simp]
theorem toCone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as := rfl

theorem toCone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j := rfl

@[simp]
theorem toCone_proj (B : Bicone F) (j : J) : Fan.proj B.toCone j = B.π j := rfl

/-- Extract the cocone from a bicone. -/
def toCoconeFunctor : Bicone F ⥤ Cocone (Discrete.functor F) where
  obj B := { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {X Y} F := { hom := F.hom, w := fun _ => F.wι _ }

/-- A shorthand for `toCoconeFunctor.obj` -/
abbrev toCocone (B : Bicone F) : Cocone (Discrete.functor F) := toCoconeFunctor.obj B

@[simp]
theorem toCocone_pt (B : Bicone F) : B.toCocone.pt = B.pt := rfl

@[simp]
theorem toCocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as := rfl

@[simp]
theorem toCocone_inj (B : Bicone F) (j : J) : Cofan.inj B.toCocone j = B.ι j := rfl

theorem toCocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j := rfl

/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
def ofLimitCone {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f where
  pt := t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

theorem ι_of_isLimit {f : J → C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
def ofColimitCocone {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) :
    Bicone f where
  pt := t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

theorem π_of_isColimit {f : J → C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed
structure IsBilimit {F : J → C} (B : Bicone F) where
  isLimit : IsLimit B.toCone
  isColimit : IsColimit B.toCocone


attribute [inherit_doc IsBilimit] IsBilimit.isLimit IsBilimit.isColimit

-- Porting note (#10618): simp can prove this, linter doesn't notice it is removed
attribute [-simp, nolint simpNF] IsBilimit.mk.injEq

attribute [local ext] Bicone.IsBilimit

instance subsingleton_isBilimit {f : J → C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

section Whisker

variable {K : Type w'}

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
  Cones.ext (Iso.refl _) (by aesop_cat)

/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
def whiskerToCocone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocones.precompose (Discrete.functorComp f g).hom).obj
        (c.toCocone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cocones.ext (Iso.refl _) (by aesop_cat)

/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
def whiskerIsBilimitIff {f : J → C} (c : Bicone f) (g : K ≃ J) :
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

/-- A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
-- @[nolint has_nonempty_instance] -- Porting note(#5171): removed; linter not ported yet
structure LimitBicone (F : J → C) where
  bicone : Bicone F
  isBilimit : bicone.IsBilimit

attribute [inherit_doc LimitBicone] LimitBicone.bicone LimitBicone.isBilimit

/-- `HasBiproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
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
of every function `F : J → C`.
-/
class HasBiproductsOfShape : Prop where
  has_biproduct : ∀ F : J → C, HasBiproduct F

attribute [instance 100] HasBiproductsOfShape.has_biproduct

/-- `HasFiniteBiproducts C` represents a choice of biproduct for every family of objects in `C`
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
      simpa only [(· ∘ ·), e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩

instance (priority := 100) hasBiproductsOfShape_finite [HasFiniteBiproducts C] [Finite J] :
    HasBiproductsOfShape J C := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  haveI : HasBiproductsOfShape (Fin n) C := HasFiniteBiproducts.out n
  exact hasBiproductsOfShape_of_equiv C e

instance (priority := 100) hasFiniteProducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where
  out _ := ⟨fun _ => hasLimitOfIso Discrete.natIsoFunctor.symm⟩

instance (priority := 100) hasFiniteCoproducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where
  out _ := ⟨fun _ => hasColimitOfIso Discrete.natIsoFunctor⟩

variable {C}

/-- The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproductIso (F : J → C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans <|
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

end Limits

namespace Limits

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

@[reassoc] -- Porting note: both versions proven by simp
theorem biproduct.ι_π_self (f : J → C) [HasBiproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by simp [biproduct.ι_π]

@[reassoc (attr := simp)]
theorem biproduct.ι_π_ne (f : J → C) [HasBiproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by simp [biproduct.ι_π, h]

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `biproduct.whiskerEquiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem biproduct.eqToHom_comp_ι (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ biproduct.ι f j' = biproduct.ι f j := by
  cases w
  simp

-- The `simpNF` linter incorrectly identifies these as simp lemmas that could never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
-- They are used by `simp` in `biproduct.whiskerEquiv` below.
@[reassoc (attr := simp, nolint simpNF)]
theorem biproduct.π_comp_eqToHom (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    biproduct.π f j ≫ eqToHom (by simp [w]) = biproduct.π f j' := by
  cases w
  simp

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

@[simp]
theorem biproduct.isoProduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by simp [biproduct.isoProduct]

@[simp]
theorem biproduct.isoProduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

@[simp]
theorem biproduct.isoCoproduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

@[simp]
theorem biproduct.isoCoproduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).hom = biproduct.desc (Sigma.ι f) :=
  biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

theorem biproduct.map_eq_map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  ext
  dsimp
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    Category.assoc, ← Bicone.toCone_π_app_mk, ← biproduct.bicone_π, ← Bicone.toCocone_ι_app_mk,
    ← biproduct.bicone_ι]
  dsimp
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs with h
  · subst h; rw [eqToHom_refl, Category.id_comp]; erw [Category.comp_id]
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

/-- Two biproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.

Unfortunately there are two natural ways to define each direction of this isomorphism
(because it is true for both products and coproducts separately).
We give the alternative definitions as lemmas below.
-/
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
  · simp only [ι_desc_assoc, Category.assoc, ne_eq, lift_π]
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
  · simp only [ι_desc_assoc, Category.assoc, ne_eq, lift_π]
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

@[reassoc (attr := simp)]
theorem biproduct.fromSubtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j =
      if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
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

@[reassoc] -- Porting note: both version solved using simp
theorem biproduct.fromSubtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrict p f) j := by
  ext
  rw [biproduct.fromSubtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
theorem biproduct.toSubtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrict p f) j = biproduct.π f j :=
  biproduct.lift_π _ _

@[reassoc (attr := simp)]
theorem biproduct.ι_toSubtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p =
      if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
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

@[reassoc] -- Porting note (#10618): simp can prove both versions
theorem biproduct.ι_toSubtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrict p f) j := by
  ext
  rw [biproduct.toSubtype, Category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
theorem biproduct.ι_fromSubtype (j : Subtype p) :
    biproduct.ι (Subtype.restrict p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _

@[reassoc (attr := simp)]
theorem biproduct.fromSubtype_toSubtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrict p f) := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, biproduct.toSubtype_π, biproduct.fromSubtype_π_subtype, Category.id_comp]

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

open scoped Classical

-- Per leanprover-community/mathlib#15067, we only allow indexing in `Type 0` here.
variable {K : Type} [Finite K] [HasFiniteBiproducts C] (f : K → C)

/-- The limit cone exhibiting `⨁ Subtype.restrict pᶜ f` as the kernel of
`biproduct.toSubtype f p` -/
@[simps]
def kernelForkBiproductToSubtype (p : Set K) :
    LimitCone (parallelPair (biproduct.toSubtype f p) 0) where
  cone :=
    KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        erw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.IsLimit.ofι _ _ (fun {W} g _ => g ≫ biproduct.toSubtype f pᶜ)
      (by
        intro W' g' w
        ext j
        simp only [Category.assoc, biproduct.toSubtype_fromSubtype, Pi.compl_apply,
          biproduct.map_π]
        split_ifs with h
        · simp
        · replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩
          simpa using w.symm)
      (by aesop_cat)

instance (p : Set K) : HasKernel (biproduct.toSubtype f p) :=
  HasLimit.mk (kernelForkBiproductToSubtype f p)

/-- The kernel of `biproduct.toSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
def kernelBiproductToSubtypeIso (p : Set K) :
    kernel (biproduct.toSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  limit.isoLimitCone (kernelForkBiproductToSubtype f p)

/-- The colimit cocone exhibiting `⨁ Subtype.restrict pᶜ f` as the cokernel of
`biproduct.fromSubtype f p` -/
@[simps]
def cokernelCoforkBiproductFromSubtype (p : Set K) :
    ColimitCocone (parallelPair (biproduct.fromSubtype f p) 0) where
  cocone :=
    CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exact not_not.mpr k.2)
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _ (fun {W} g _ => biproduct.fromSubtype f pᶜ ≫ g)
      (by
        intro W g' w
        ext j
        simp only [biproduct.toSubtype_fromSubtype_assoc, Pi.compl_apply, biproduct.ι_map_assoc]
        split_ifs with h
        · simp
        · replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : p) ≫= w
          simpa using w.symm)
      (by aesop_cat)

instance (p : Set K) : HasCokernel (biproduct.fromSubtype f p) :=
  HasColimit.mk (cokernelCoforkBiproductFromSubtype f p)

/-- The cokernel of `biproduct.fromSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
def cokernelBiproductFromSubtypeIso (p : Set K) :
    cokernel (biproduct.fromSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

end

end πKernel

end Limits

namespace Limits

section FiniteBiproducts

variable {J : Type} [Finite J] {K : Type} [Finite K] {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C] {f : J → C} {g : K → C}

/-- Convert a (dependently typed) matrix to a morphism of biproducts.
-/
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
  ext
  simp [biproduct.matrix]

/-- Extract the matrix components from a morphism of biproducts.
-/
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

universe uD uD'
variable {J : Type w}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

instance biproduct.ι_mono (f : J → C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) :=
  IsSplitMono.mk' { retraction := biproduct.desc <| Pi.single b (𝟙 (f b)) }

instance biproduct.π_epi (f : J → C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) :=
  IsSplitEpi.mk' { section_ := biproduct.lift <| Pi.single b (𝟙 (f b)) }

/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
theorem biproduct.conePointUniqueUpToIso_hom (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).hom = biproduct.lift b.π :=
  rfl

/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
theorem biproduct.conePointUniqueUpToIso_inv (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).inv = biproduct.desc b.ι := by
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

variable {C} [Unique J] (f : J → C)

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
def limitBiconeOfUnique : LimitBicone f where
  bicone :=
    { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq] )
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq] ) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }

instance (priority := 100) hasBiproduct_unique : HasBiproduct f :=
  HasBiproduct.mk (limitBiconeOfUnique f)

/-- A biproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
def biproductUniqueIso : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

end

variable {C}

/-- A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed
structure BinaryBicone (P Q : C) where
  pt : C
  fst : pt ⟶ P
  snd : pt ⟶ Q
  inl : P ⟶ pt
  inr : Q ⟶ pt
  inl_fst : inl ≫ fst = 𝟙 P := by aesop
  inl_snd : inl ≫ snd = 0 := by aesop
  inr_fst : inr ≫ fst = 0 := by aesop
  inr_snd : inr ≫ snd = 𝟙 Q := by aesop

attribute [inherit_doc BinaryBicone] BinaryBicone.pt BinaryBicone.fst BinaryBicone.snd
  BinaryBicone.inl BinaryBicone.inr BinaryBicone.inl_fst BinaryBicone.inl_snd
  BinaryBicone.inr_fst BinaryBicone.inr_snd

attribute [reassoc (attr := simp)]
  BinaryBicone.inl_fst BinaryBicone.inl_snd BinaryBicone.inr_fst BinaryBicone.inr_snd


/-- A binary bicone morphism between two binary bicones for the same diagram is a morphism of the
binary bicone points which commutes with the cone and cocone legs. -/
structure BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wfst : hom ≫ B.fst = A.fst := by aesop_cat
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wsnd : hom ≫ B.snd = A.snd := by aesop_cat
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winl : A.inl ≫ hom = B.inl := by aesop_cat
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winr : A.inr ≫ hom = B.inr := by aesop_cat


attribute [reassoc (attr := simp)] BinaryBiconeMorphism.wfst BinaryBiconeMorphism.wsnd
attribute [reassoc (attr := simp)] BinaryBiconeMorphism.winl BinaryBiconeMorphism.winr

/-- The category of binary bicones on a given diagram. -/
@[simps]
instance BinaryBicone.category {P Q : C} : Category (BinaryBicone P Q) where
  Hom A B := BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

-- Porting note: if we do not have `simps` automatically generate the lemma for simplifying
-- the `hom` field of a category, we need to write the `ext` lemma in terms of the categorical
-- morphism, rather than the underlying structure.
@[ext]
theorem BinaryBiconeMorphism.ext {P Q : C} {c c' : BinaryBicone P Q}
    (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace BinaryBicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
-- Porting note: `@[ext]` used to accept lemmas like this. Now we add an aesop rule
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
    (winl : c.inl ≫ φ.hom = c'.inl := by aesop_cat)
    (winr : c.inr ≫ φ.hom = c'.inr := by aesop_cat)
    (wfst : φ.hom ≫ c'.fst = c.fst := by aesop_cat)
    (wsnd : φ.hom ≫ c'.snd = c.snd := by aesop_cat) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

variable (P Q : C) (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

/-- A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially. -/
@[simps]
def functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  obj A :=
    { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

instance functoriality_full [F.Full] [F.Faithful] : (functoriality P Q F).Full where
  map_surjective t :=
   ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using t.winl)
      winr := F.map_injective (by simpa using t.winr)
      wfst := F.map_injective (by simpa using t.wfst)
      wsnd := F.map_injective (by simpa using t.wsnd) }, by aesop_cat⟩

instance functoriality_faithful [F.Faithful] : (functoriality P Q F).Faithful where
  map_injective {_X} {_Y} f g h :=
    BinaryBiconeMorphism.ext f g <| F.map_injective <| congr_arg BinaryBiconeMorphism.hom h

end BinaryBicones

namespace BinaryBicone

variable {P Q : C}

/-- Extract the cone from a binary bicone. -/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd

@[simp]
theorem toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt := rfl

@[simp]
theorem toCone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl

@[simp]
theorem toCone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl

@[simp]
theorem binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst := rfl

@[simp]
theorem binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) := BinaryCofan.mk c.inl c.inr

@[simp]
theorem toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt := rfl

@[simp]
theorem toCocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl

@[simp]
theorem toCocone_ι_app_right (c : BinaryBicone P Q) :
    c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr := rfl

@[simp]
theorem binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl

@[simp]
theorem binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl

instance (c : BinaryBicone P Q) : IsSplitMono c.inl :=
  IsSplitMono.mk'
    { retraction := c.fst
      id := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitMono c.inr :=
  IsSplitMono.mk'
    { retraction := c.snd
      id := c.inr_snd }

instance (c : BinaryBicone P Q) : IsSplitEpi c.fst :=
  IsSplitEpi.mk'
    { section_ := c.inl
      id := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitEpi c.snd :=
  IsSplitEpi.mk'
    { section_ := c.inr
      id := c.inr_snd }

/-- Convert a `BinaryBicone` into a `Bicone` over a pair. -/
@[simps]
def toBiconeFunctor {X Y : C} : BinaryBicone X Y ⥤ Bicone (pairFunction X Y) where
  obj b :=
    { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

/-- A shorthand for `toBiconeFunctor.obj` -/
abbrev toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y) :=
  toBiconeFunctor.obj b

/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <|
    Cones.ext (Iso.refl _) fun j => by
      cases' j with as; cases as <;> simp

/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
    cocone. -/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) :
    IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <|
    Cocones.ext (Iso.refl _) fun j => by
      cases' j with as; cases as <;> simp

end BinaryBicone

namespace Bicone

/-- Convert a `Bicone` over a function on `WalkingPair` to a BinaryBicone. -/
@[simps]
def toBinaryBiconeFunctor {X Y : C} : Bicone (pairFunction X Y) ⥤ BinaryBicone X Y where
  obj b :=
    { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp [Bicone.ι_π]
      inr_fst := by simp [Bicone.ι_π]
      inl_snd := by simp [Bicone.ι_π]
      inr_snd := by simp [Bicone.ι_π] }
  map f :=
    { hom := f.hom }

/-- A shorthand for `toBinaryBiconeFunctor.obj` -/
abbrev toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y :=
  toBinaryBiconeFunctor.obj b

/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
    cone. -/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cones.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
    colimit cocone. -/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocones.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

end Bicone

/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  isLimit : IsLimit b.toCone
  isColimit : IsColimit b.toCocone

attribute [inherit_doc BinaryBicone.IsBilimit] BinaryBicone.IsBilimit.isLimit
  BinaryBicone.IsBilimit.isColimit

/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) :
    b.toBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
    bilimit. -/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
-- @[nolint has_nonempty_instance] Porting note (#5171): removed
structure BinaryBiproductData (P Q : C) where
  bicone : BinaryBicone P Q
  isBilimit : bicone.IsBilimit

attribute [inherit_doc BinaryBiproductData] BinaryBiproductData.bicone
  BinaryBiproductData.isBilimit

/-- `HasBinaryBiproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)

attribute [inherit_doc HasBinaryBiproduct] HasBinaryBiproduct.exists_binary_biproduct

theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/--
Use the axiom of choice to extract explicit `BinaryBiproductData F` from `HasBinaryBiproduct F`.
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct

/-- A bicone for `P Q` which is both a limit cone and a colimit cocone. -/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).bicone

/-- `BinaryBiproduct.bicone P Q` is a limit bicone. -/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] :
    (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).isBilimit

/-- `BinaryBiproduct.bicone P Q` is a limit cone. -/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).isBilimit.isLimit

/-- `BinaryBiproduct.bicone P Q` is a colimit cocone. -/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).isBilimit.isColimit

section

variable (C)

/-- `HasBinaryBiproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class HasBinaryBiproducts : Prop where
  has_binary_biproduct : ∀ P Q : C, HasBinaryBiproduct P Q

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

/-- A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }

end

variable {P Q : C}

instance HasBinaryBiproduct.hasLimit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

instance HasBinaryBiproduct.hasColimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

instance (priority := 100) hasBinaryProducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where
  has_limit F := hasLimitOfIso (diagramIsoPair F).symm

instance (priority := 100) hasBinaryCoproducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where
  has_colimit F := hasColimitOfIso (diagramIsoPair F)

/-- The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans <|
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst

/-- The projection onto the second summand of a binary biproduct. -/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd

/-- The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

/-- The inclusion into the second summand of a binary biproduct. -/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr

section

variable {X Y : C} [HasBinaryBiproduct X Y]

@[simp]
theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr :=
  rfl

end

@[reassoc] -- Porting note: simp can solve both versions
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc] -- Porting note: simp can solve both versions
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc] -- Porting note: simp can solve both versions
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc] -- Porting note: simp can solve both versions
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  (BinaryBiproduct.isLimit X Y).lift (BinaryFan.mk f g)

/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  (BinaryBiproduct.isColimit X Y).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

@[simp]
theorem biprod.isoProd_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).hom = prod.lift biprod.fst biprod.snd := by
      ext <;> simp [biprod.isoProd]

@[simp]
theorem biprod.isoProd_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  ext <;> simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

@[simp]
theorem biprod.isoCoprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [biprod.isoCoprod]

@[simp]
theorem biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).hom = biprod.desc coprod.inl coprod.inr := by
  ext <;> simp [← Iso.eq_comp_inv]

theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g := by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π, biprod.inl_fst_assoc,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ← BinaryBiproduct.bicone_fst, ←
      BinaryBicone.toCocone_ι_app_left, ← BinaryBiproduct.bicone_inl]
    dsimp; simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π, zero_comp, biprod.inl_snd_assoc,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ← BinaryBiproduct.bicone_snd, ←
      BinaryBicone.toCocone_ι_app_left, ← BinaryBiproduct.bicone_inl]
    simp
  · simp only [mapPair_right, biprod.inr_fst_assoc, IsColimit.ι_map, IsLimit.map_π, zero_comp,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ← BinaryBiproduct.bicone_fst, ←
      BinaryBicone.toCocone_ι_app_right, ← BinaryBiproduct.bicone_inr]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π, biprod.inr_snd_assoc,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ← BinaryBiproduct.bicone_snd, ←
      BinaryBicone.toCocone_ι_app_right, ← BinaryBiproduct.bicone_inr]
    simp

instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }

instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }

instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }

instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[reassoc (attr := simp)]
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z where
  hom := biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
theorem biprod.conePointUniqueUpToIso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).hom =
      biprod.lift b.fst b.snd := rfl

/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
theorem biprod.conePointUniqueUpToIso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv =
      biprod.desc b.inl b.inr := by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
    limits, but in the case of biproducts we can give an isomorphism with particularly nice
    definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
    are inverses of each other. -/
@[simps]
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) : b.pt ≅ X ⊞ Y where
  hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.inv_hom_id]

-- There are three further variations,
-- about `IsIso biprod.inr`, `IsIso biprod.fst` and `IsIso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl := by
  constructor
  · intro h
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 <| @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc, Category.comp_id] at this
    rw [this, IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

/-- A kernel fork for the kernel of `BinaryBicone.fst`. It consists of the morphism
`BinaryBicone.inr`. -/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst

@[simp]
theorem BinaryBicone.fstKernelFork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr := rfl

/-- A kernel fork for the kernel of `BinaryBicone.snd`. It consists of the morphism
`BinaryBicone.inl`. -/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd

@[simp]
theorem BinaryBicone.sndKernelFork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inl`. It consists of the morphism
`BinaryBicone.snd`. -/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd

@[simp]
theorem BinaryBicone.inlCokernelCofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inr`. It consists of the morphism
`BinaryBicone.fst`. -/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst

@[simp]
theorem BinaryBicone.inrCokernelCofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst := rfl

variable {c}

/-- The fork defined in `BinaryBicone.fstKernelFork` is indeed a kernel. -/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

/-- The fork defined in `BinaryBicone.sndKernelFork` is indeed a kernel. -/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

/-- The cofork defined in `BinaryBicone.inlCokernelCofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inlCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

/-- The cofork defined in `BinaryBicone.inrCokernelCofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inrCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _

@[simp]
theorem biprod.fstKernelFork_ι : Fork.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.fstKernelFork` is indeed a limit. -/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _

@[simp]
theorem biprod.sndKernelFork_ι : Fork.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.sndKernelFork` is indeed a limit. -/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _

@[simp]
theorem biprod.inlCokernelCofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl

/-- The cofork `biprod.inlCokernelFork` is indeed a colimit. -/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _

@[simp]
theorem biprod.inrCokernelCofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl

/-- The cofork `biprod.inrCokernelFork` is indeed a colimit. -/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

end HasBinaryBiproduct

variable {X Y : C} [HasBinaryBiproduct X Y]

instance : HasKernel (biprod.fst : X ⊞ Y ⟶ X) :=
  HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps!]
def kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
  limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩

instance : HasKernel (biprod.snd : X ⊞ Y ⟶ Y) :=
  HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps!]
def kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
  limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩

instance : HasCokernel (biprod.inl : X ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps!]
def cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

instance : HasCokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps!]
def cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

end BiprodKernel

section IsZero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps!]
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]
lemma biprod_isZero_iff (A B : C) [HasBinaryBiproduct A B] :
    IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

end IsZero

section

variable [HasBinaryBiproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  aesop_cat

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f := by
  aesop_cat

@[reassoc]
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f := by
  aesop_cat

@[reassoc (attr := simp)]
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  aesop_cat

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem biprod.symmetry (P Q : C) :
    (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ := by simp

/-- The associator isomorphism which associates a binary biproduct. -/
@[simps]
def biprod.associator (P Q R : C) : (P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R) where
  hom := biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.associator_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map (biprod.map f g) h ≫ (biprod.associator _ _ _).hom
      = (biprod.associator _ _ _).hom ≫ biprod.map f (biprod.map g h) := by
  aesop_cat

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.associator_inv_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map f (biprod.map g h) ≫ (biprod.associator _ _ _).inv
      = (biprod.associator _ _ _).inv ≫ biprod.map (biprod.map f g) h := by
  aesop_cat

end

end Limits

open CategoryTheory.Limits

-- TODO:
-- If someone is interested, they could provide the constructions:
--   HasBinaryBiproducts ↔ HasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z

/-- If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
theorem isIso_left_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

/-- If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
theorem isIso_right_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso g :=
  letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

end CategoryTheory

set_option linter.style.longFile 2100
