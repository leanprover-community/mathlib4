/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves of (commutative) rings.

Results specific to sheaves of commutative rings including sheaves of continuous functions
`TopCat.continuousFunctions` with natural operations of  `pullback` and `map` and
sub, quotient, and localization operations on sheaves of rings with
- `SubmonoidPresheaf` : A subpresheaf with a submonoid structure on each of the components.
- `LocalizationPresheaf` : The localization of a presheaf of commrings at a `SubmonoidPresheaf`.
- `TotalQuotientPresheaf` : The presheaf of total quotient rings.

As more results accumulate, please consider splitting this file.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

universe u v w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.

Note that the universes for `TopCat` and `CommRingCat` must be the same for this argument
to go through.
-/
example (X : TopCat.{u₁}) (F : Presheaf CommRingCat.{u₁} X)
    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :
    F.IsSheaf :=
(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h

open AlgebraicGeometry in
/-- Unfold `restrictOpen` in the category of commutative rings (with the correct carrier type).

Although unification hints help with applying `TopCat.Presheaf.restrictOpenCommRingCat`,
so it can be safely de-specialized, this lemma needs to be kept to ensure rewrites go right.
-/
lemma restrictOpenCommRingCat_apply {X : TopCat}
    {F : Presheaf CommRingCat X} {V : Opens ↑X} (f : CommRingCat.carrier (F.obj (op V)))
    (U : Opens ↑X) (e : U ≤ V := by restrict_tac) :
    f |_ U = F.map (homOfLE e).op f :=
  rfl

section SubmonoidPresheaf

open scoped nonZeroDivisors

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]

-- note: this was specialized to `CommRingCat` in https://github.com/leanprover-community/mathlib4/issues/19757
/-- A subpresheaf with a submonoid structure on each of the components. -/
structure SubmonoidPresheaf (F : X.Presheaf CommRingCat) where
  /-- The submonoid structure for each component -/
  obj : ∀ U, Submonoid (F.obj U)
  map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U ≤ (obj V).comap (F.map i).hom

variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)

/-- The localization of a presheaf of `CommRing`s with respect to a `SubmonoidPresheaf`. -/
protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
  obj U := CommRingCat.of <| Localization (G.obj U)
  map {_ _} i := CommRingCat.ofHom <| IsLocalization.map _ (F.map i).hom (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.map_comp]
    ext : 1
    dsimp
    rw [IsLocalization.map_comp_map]

instance (U) : Algebra (F.obj U) (G.localizationPresheaf.obj U) :=
  show Algebra _ (Localization (G.obj U)) from inferInstance

instance (U) : IsLocalization (G.obj U) (G.localizationPresheaf.obj U) :=
  show IsLocalization (G.obj U) (Localization (G.obj U)) from inferInstance

/-- The map into the localization presheaf. -/
@[simps app]
def SubmonoidPresheaf.toLocalizationPresheaf : F ⟶ G.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (F.obj U) (Localization <| G.obj U)
  naturality {_ _} i := CommRingCat.hom_ext <| (IsLocalization.map_comp (G.map i)).symm

instance epi_toLocalizationPresheaf : Epi G.toLocalizationPresheaf :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ G.toLocalizationPresheaf fun U => Localization.epi' (G.obj U)

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps]
noncomputable def submonoidPresheafOfStalk (S : ∀ x : X, Submonoid (F.stalk x)) :
    F.SubmonoidPresheaf where
  obj U := ⨅ x : U.unop, Submonoid.comap (F.germ U.unop x.1 x.2).hom (S x)
  map {U V} i := by
    intro s hs
    simp only [Submonoid.mem_comap, Submonoid.mem_iInf] at hs ⊢
    intro x
    change (F.map i.unop.op ≫ F.germ V.unop x.1 x.2) s ∈ _
    rw [F.germ_res]
    exact hs ⟨_, i.unop.le x.2⟩

noncomputable instance : Inhabited F.SubmonoidPresheaf :=
  ⟨F.submonoidPresheafOfStalk fun _ => ⊥⟩

/-- The localization of a presheaf of `CommRing`s at locally non-zero-divisor sections. -/
noncomputable def totalQuotientPresheaf : X.Presheaf CommRingCat.{w} :=
  (F.submonoidPresheafOfStalk fun x => (F.stalk x)⁰).localizationPresheaf

/-- The map into the presheaf of total quotient rings -/
noncomputable def toTotalQuotientPresheaf : F ⟶ F.totalQuotientPresheaf :=
  SubmonoidPresheaf.toLocalizationPresheaf _
deriving Epi

instance (F : X.Sheaf CommRingCat.{w}) : Mono F.presheaf.toTotalQuotientPresheaf := by
  apply (config := { allowSynthFailures := true }) NatTrans.mono_of_mono_app
  intro U
  apply ConcreteCategory.mono_of_injective
  dsimp [toTotalQuotientPresheaf]
  -- Porting note: `M` and `S` need to be specified manually, so used a hack to save some typing
  set m := _
  change Function.Injective (algebraMap _ (Localization m))
  refine IsLocalization.injective (M := m) (S := Localization m) ?_
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
  intro s hs t e
  apply section_ext F (unop U)
  intro x hx
  rw [RingHom.map_zero]
  apply (Submonoid.mem_iInf.mp hs ⟨x, hx⟩).2
  rw [← map_mul, e, map_zero]

end SubmonoidPresheaf

end TopCat.Presheaf

section ContinuousFunctions

namespace TopCat

variable (X : TopCat.{v}) (R : TopCommRingCat.{v})

instance : NatCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  natCast n := ofHom n

instance : IntCast (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  intCast n := ofHom n

instance : Zero (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  zero := ofHom 0

instance : One (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  one := ofHom 1

instance : Neg (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  neg f := ofHom (-f.hom)

instance : Sub (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  sub f g := ofHom (f.hom - g.hom)

instance : Add (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  add f g := ofHom (f.hom + g.hom)

instance : Mul (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  mul f g := ofHom (f.hom * g.hom)

instance : SMul ℕ (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)

instance : SMul ℤ (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) where
  smul n f := ofHom (n • f.hom)

instance : Pow (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) ℕ where
  pow f n := ofHom (f.hom ^ n)

instance : CommRing (X ⟶ (forget₂ TopCommRingCat TopCat).obj R) :=
  Function.Injective.commRing _ ConcreteCategory.hom_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- TODO upgrade the result to TopCommRing?
/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
def continuousFunctions (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v}) : CommRingCat.{v} :=
  CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R)

namespace continuousFunctions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat) :
    continuousFunctions X R ⟶ continuousFunctions Y R := CommRingCat.ofHom
  { toFun g := f.unop ≫ g
    map_one' := rfl
    map_zero' := rfl
    map_add' := by cat_disch
    map_mul' := by cat_disch }

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S := CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

end continuousFunctions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : TopCat` to `R : TopCommRingCat` form a commutative ring, functorial in both `X` and
`R`. -/
def commRingYoneda : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj R :=
    { obj := fun X => continuousFunctions X R
      map := fun {_ _} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {_ _ _} _ _ => rfl }
  map {_ _} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun _ _ _ => rfl }
  map_id X := by
    ext
    rfl
  map_comp {_ _ _} _ _ := rfl

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex-valued functions of `X` as
```
presheafToTopCommRing X (TopCommRingCat.of ℂ)
```
(this requires `import Topology.Instances.Complex`).
-/
def presheafToTopCommRing (T : TopCommRingCat.{v}) : X.Presheaf CommRingCat.{v} :=
  (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

end TopCat

end ContinuousFunctions

section Stalks

namespace TopCat.Presheaf

variable {X Y Z : TopCat.{v}}

instance algebra_section_stalk (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ U x.1 x.2).hom.toAlgebra

@[simp]
theorem stalk_open_algebraMap {X : TopCat} (F : X.Presheaf CommRingCat) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = (F.germ U x.1 x.2).hom :=
  rfl

end TopCat.Presheaf

end Stalks

noncomputable section Gluing

namespace TopCat.Sheaf

open TopologicalSpace Opposite CategoryTheory

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/-- `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ V)`. -/
def objSupIsoProdEqLocus {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) :
    F.1.obj (op <| U ⊔ V) ≅ CommRingCat.of <|
    -- Porting note: Lean 3 is able to figure out the ring homomorphism automatically
    RingHom.eqLocus
      (RingHom.comp (F.val.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom
        (RingHom.fst (F.val.obj <| op U) (F.val.obj <| op V)))
      (RingHom.comp (F.val.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom
        (RingHom.snd (F.val.obj <| op U) (F.val.obj <| op V))) :=
  (F.isLimitPullbackCone U V).conePointUniqueUpToIso (CommRingCat.pullbackConeIsLimit _ _)

theorem objSupIsoProdEqLocus_hom_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.fst = F.1.map (homOfLE le_sup_left).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

theorem objSupIsoProdEqLocus_hom_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    ((F.objSupIsoProdEqLocus U V).hom x).1.snd = F.1.map (homOfLE le_sup_right).op x :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_hom_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

theorem objSupIsoProdEqLocus_inv_fst {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_left).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.1 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.left)
    x

theorem objSupIsoProdEqLocus_inv_snd {X : TopCat} (F : X.Sheaf CommRingCat) (U V : Opens X) (x) :
    F.1.map (homOfLE le_sup_right).op ((F.objSupIsoProdEqLocus U V).inv x) = x.1.2 :=
  ConcreteCategory.congr_hom
    ((F.isLimitPullbackCone U V).conePointUniqueUpToIso_inv_comp
      (CommRingCat.pullbackConeIsLimit _ _) WalkingCospan.right)
    x

theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W ≤ U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW ≤ U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW ≤ V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (inf_le_right : V ⊓ W ≤ W)) ?_ _ _ ?_ ?_
    · rw [← inf_sup_right]
      exact le_inf e le_rfl
    · rw [← e₁, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    · rw [← e₂, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]

end TopCat.Sheaf

end Gluing
