/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.PUnit
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The category of `R`-modules

`ModuleCat.{v} R` is the category of bundled `R`-modules with carrier in the universe `v`. We show
that it is preadditive and show that being an isomorphism, monomorphism and epimorphism is
equivalent to being a linear equivalence, an injective linear map and a surjective linear map,
respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : ModuleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps, written `f.hom` (`ModuleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `ModuleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe v u

variable (R : Type u) [Ring R]

/-- The category of R-modules and their morphisms.

Note that in the case of `R = ℤ`, we cannot
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure ModuleCat where
  private mk ::
  /-- the underlying type of an object in `ModuleCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

attribute [instance] ModuleCat.isAddCommGroup ModuleCat.isModule

namespace ModuleCat

instance : CoeSort (ModuleCat.{v} R) (Type v) :=
  ⟨ModuleCat.carrier⟩

attribute [coe] ModuleCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `ModuleCat R`. -/
abbrev of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : ModuleCat.{v} R) : of R M = M := by with_reducible rfl

variable {R} in
/-- The type of morphisms in `ModuleCat R`. -/
@[ext]
structure Hom (M N : ModuleCat.{v} R) where
  private mk ::
  /-- The underlying linear map. -/
  hom' : M →ₗ[R] N

instance moduleCategory : Category.{v, max (v+1) u} (ModuleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (ModuleCat.{v} R) (· →ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

section

variable {R}

/-- Turn a morphism in `ModuleCat` back into a `LinearMap`. -/
abbrev Hom.hom {A B : ModuleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := ModuleCat R) f

/-- Typecheck a `LinearMap` as a morphism in `ModuleCat`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := ModuleCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : ModuleCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {M : ModuleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

/- Provided for rewriting. -/
lemma id_apply (M : ModuleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[simp]
lemma hom_comp {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_bijective {M N : ModuleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `ModuleCat.hom_bijective.injective`. -/
lemma hom_injective {M N : ModuleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.injective

/-- Convenience shortcut for `ModuleCat.hom_bijective.surjective`. -/
lemma hom_surjective {M N : ModuleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.surjective

@[simp]
lemma hom_ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {M : Type v} [AddCommGroup M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

@[simp]
lemma ofHom_comp {M N O : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/- Doesn't need to be `@[simp]` since `simp only` can solve this. -/
lemma ofHom_apply {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl

lemma inv_hom_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

/-- `ModuleCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {M N : ModuleCat.{v} R} : (M ⟶ N) ≃ (M →ₗ[R] N) where
  toFun := Hom.hom
  invFun := ofHom

end

/- Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues. -/
lemma forget_obj {M : ModuleCat.{v} R} : (forget (ModuleCat.{v} R)).obj M = M := rfl

@[simp]
lemma forget_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (forget (ModuleCat.{v} R)).map f = f :=
  rfl

instance hasForgetToAddCommGroup : HasForget₂ (ModuleCat R) AddCommGrpCat where
  forget₂ :=
    { obj := fun M => AddCommGrpCat.of M
      map := fun f => AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

@[simp]
theorem forget₂_obj (X : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj X = AddCommGrpCat.of X :=
  rfl

theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (of R X) = AddCommGrpCat.of X :=
  rfl

@[simp]
theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f = AddCommGrpCat.ofHom f.hom :=
  rfl

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

@[simp] theorem of_coe (X : ModuleCat R) : of R X = X := rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[deprecated Iso.refl (since := "2025-05-15")]
def ofSelfIso (M : ModuleCat R) : ModuleCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

theorem isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

instance : HasZeroObject (ModuleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

end ModuleCat

variable {R}
variable {X₁ X₂ : Type v}

open ModuleCat

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[ModuleCat] notation "↟" f:1024 => ModuleCat.ofHom f

section

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  hom := ofHom (e : X₁ →ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

namespace CategoryTheory.Iso

/-- Build a `LinearEquiv` from an isomorphism in the category `ModuleCat R`. -/
def toLinearEquiv {X Y : ModuleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
  LinearEquiv.ofLinear i.hom.hom i.inv.hom (by aesop) (by aesop)

end CategoryTheory.Iso

/-- linear equivalences between `Module`s are the same as (isomorphic to) isomorphisms
in `ModuleCat` -/
@[simps]
def linearEquivIsoModuleIso {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ ModuleCat.of R X ≅ ModuleCat.of R Y where
  hom e := e.toModuleIso
  inv i := i.toLinearEquiv

end

namespace ModuleCat

section AddCommGroup

variable {M N : ModuleCat.{v} R}

instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩

@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

instance : Zero (M ⟶ N) where
  zero := ⟨0⟩

@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom⟩

@[simp] lemma hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom⟩

@[simp] lemma hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] lemma hom_zsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.hom) hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] lemma hom_sum {ι : Type*} (f : ι → (M ⟶ N)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ({ toFun := ModuleCat.Hom.hom, map_zero' := ModuleCat.hom_zero, map_add' := hom_add } :
    (M ⟶ N) →+ (M →ₗ[R] N)) _ _

instance : Preadditive (ModuleCat.{v} R) where

instance forget₂_addCommGrp_additive :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat).Additive where

/-- `ModuleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (M →ₗ[R] N) :=
  { homEquiv with
    map_add' := fun _ _ => rfl }

theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  rw [← LinearMap.id_apply (R := R) x, ← ModuleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

lemma isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommGroup M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

end AddCommGroup

section SMul

variable {M N : ModuleCat.{v} R} {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance : SMul S (M ⟶ N) where
  smul c f := ⟨c • f.hom⟩

@[simp] lemma hom_smul (s : S) (f : M ⟶ N) : (s • f).hom = s • f.hom := rfl

end SMul

section Module

variable {M N : ModuleCat.{v} R} {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

instance Hom.instModule : Module S (M ⟶ N) :=
  Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

/-- `ModuleCat.Hom.hom` bundled as a linear equivalence. -/
@[simps]
def homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M →ₗ[R] N) :=
  { homAddEquiv with
    map_smul' := fun _ _ => rfl }

end Module

section

universe u₀

namespace Algebra

variable {S₀ : Type u₀} [CommSemiring S₀] {S : Type u} [Ring S] [Algebra S₀ S]

variable {M N : ModuleCat.{v} S}

/--
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
scoped instance : Module S₀ M := Module.compHom _ (algebraMap S₀ S)

scoped instance : IsScalarTower S₀ S M where
  smul_assoc _ _ _ := by rw [Algebra.smul_def, mul_smul]; rfl

scoped instance : SMulCommClass S S₀ M where
  smul_comm s s₀ n :=
    show s • algebraMap S₀ S s₀ • n = algebraMap S₀ S s₀ • s • n by
    rw [← smul_assoc, smul_eq_mul, ← Algebra.commutes, mul_smul]

/--
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
-/
scoped instance instLinear : Linear S₀ (ModuleCat.{v} S) where
  smul_comp _ M N s₀ f g := by ext; simp

end Algebra

section

variable {S : Type u} [CommRing S]

instance : Linear S (ModuleCat.{v} S) := ModuleCat.Algebra.instLinear

variable {X Y X' Y' : ModuleCat.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquiv j.toLinearEquiv f.hom⟩ :=
  rfl

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquiv f.hom⟩ :=
  rfl

end

end

variable (M N : ModuleCat.{v} R)

/-- `ModuleCat.Hom.hom` as an isomorphism of rings. -/
@[simps!] def endRingEquiv : End M ≃+* (M →ₗ[R] M) where
  toFun := ModuleCat.Hom.hom
  invFun := ModuleCat.ofHom
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The scalar multiplication on an object of `ModuleCat R` considered as
a morphism of rings from `R` to the endomorphisms of the underlying abelian group. -/
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGrpCat).obj M) where
  toFun r := AddCommGrpCat.ofHom
    { toFun := fun (m : M) => r • m
      map_zero' := by rw [smul_zero]
      map_add' := fun x y => by rw [smul_add] }
  map_one' := AddCommGrpCat.ext (fun x => by simp)
  map_zero' := AddCommGrpCat.ext (fun x => by simp)
  map_mul' r s := AddCommGrpCat.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddCommGrpCat.ext (fun (x : M) => add_smul r s x)

lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGrpCat).map f := by
  ext x
  exact (f.hom.map_smul r x).symm

variable (R) in
/-- The scalar multiplication on `ModuleCat R` considered as a morphism of rings
to the endomorphisms of the forgetful functor to `AddCommGrpCat)`. -/
@[simps]
def smulNatTrans : R →+* End (forget₂ (ModuleCat R) AddCommGrpCat) where
  toFun r :=
    { app := fun M => M.smul r
      naturality := fun _ _ _ => smul_naturality _ r }
  map_one' := NatTrans.ext (by cat_disch)
  map_zero' := NatTrans.ext (by cat_disch)
  map_mul' _ _ := NatTrans.ext (by cat_disch)
  map_add' _ _ := NatTrans.ext (by cat_disch)

/-- Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is a type synonym
for `A`, on which we shall define a structure of `R`-module. -/
@[nolint unusedArguments]
def mkOfSMul' {A : AddCommGrpCat} (_ : R →+* End A) := A

section

variable {A : AddCommGrpCat} (φ : R →+* End A)

instance : AddCommGroup (mkOfSMul' φ) := by
  dsimp only [mkOfSMul']
  infer_instance

instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩

@[simp]
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero (N := A) _
  smul_add _ _ _ := map_add (N := A) _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp

/-- Given `A : AddCommGrpCat` and a ring morphism `R →+* End A`, this is an object in
`ModuleCat R`, whose underlying abelian group is `A` and whose scalar multiplication is
given by `R`. -/
abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)

lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

end

section

variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

/-- Constructor for morphisms in `ModuleCat R` which takes as inputs
a morphism between the underlying objects in `AddCommGrpCat` and the compatibility
with the scalar multiplication. -/
@[simps]
def homMk : M ⟶ N where
  hom'.toFun := φ
  hom'.map_add' _ _ := φ.hom.map_add _ _
  hom'.map_smul' r x := (congr_hom (hφ r) x).symm

lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (homMk φ hφ) = φ := rfl

end

instance : (forget (ModuleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)

instance : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGrpCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

end ModuleCat

section Bilinear

variable {R : Type*} [CommRing R]

namespace ModuleCat

/-- Turn a bilinear map into a homomorphism. -/
@[simps!]
def ofHom₂ {M N P : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    M ⟶ of R (N ⟶ P) :=
  ofHom <| homLinearEquiv.symm.toLinearMap ∘ₗ f

/-- Turn a homomorphism into a bilinear map. -/
@[simps!]
def Hom.hom₂ {M N P : ModuleCat.{u} R}
    -- We write `Hom` instead of `M ⟶ (of R (N ⟶ P))`, otherwise dot notation breaks
    -- since it is expecting the type of `f` to be `ModuleCat.Hom`, not `Quiver.Hom`.
    (f : Hom M (of R (N ⟶ P))) :
    M →ₗ[R] N →ₗ[R] P :=
  Hom.hom (by convert (f ≫ ofHom homLinearEquiv.toLinearMap))

@[simp] lemma Hom.hom₂_ofHom₂ {M N P : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    (ofHom₂ f).hom₂ = f := rfl

@[simp] lemma ofHom₂_hom₂ {M N P : ModuleCat.{u} R} (f : M ⟶ of R (N ⟶ P)) :
    ofHom₂ f.hom₂ = f := rfl

end ModuleCat

end Bilinear

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp] theorem LinearMap.comp_id_moduleCat
    {R} [Ring R] {G : ModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H] (f : G →ₗ[R] H) :
    f.comp (𝟙 G : G ⟶ G).hom = f := by simp

@[simp] theorem LinearMap.id_moduleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : ModuleCat.{u} R} (f : G →ₗ[R] H) :
    LinearMap.comp (𝟙 H : H ⟶ H).hom f = f := by simp
