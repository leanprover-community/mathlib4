/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Junyan Xu
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.PUnit
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of `R`-modules

If `R` is a semiring, `SemimoduleCat.{v} R` is the category of bundled `R`-modules with carrier
in the universe `v`. We  show that it is preadditive and show that being an isomorphism and
monomorphism are equivalent to being a linear equivalence and an injective linear map respectively.

## Implementation details

To construct an object in the category of `R`-modules from a type `M` with an instance of the
`Module` typeclass, write `of R M`. There is a coercion in the other direction.
The roundtrip `↑(of R M)` is definitionally equal to `M` itself (when `M` is a type with `Module`
instance), and so is `of R ↑M` (when `M : SemimoduleCat R M`).

The morphisms are given their own type, not identified with `LinearMap`.
There is a cast from morphisms in `Module R` to linear maps,
written `f.hom` (`SemimoduleCat.Hom.hom`).
To go from linear maps to morphisms in `Module R`, use `SemimoduleCat.ofHom`.

Similarly, given an isomorphism `f : M ≅ N` use `f.toLinearEquiv` and given a linear equiv
`f : M ≃ₗ[R] N`, use `f.toModuleIso`.
-/


open CategoryTheory Limits WalkingParallelPair

universe v u

variable (R : Type u) [Semiring R]

/-- The category of R-modules and their morphisms.

Note that in the case of `R = ℕ`, we can not
impose here that the `ℕ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommMonoid` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure SemimoduleCat where
  private mk ::
  /-- the underlying type of an object in `SemimoduleCat R` -/
  carrier : Type v
  [isAddCommMonoid : AddCommMonoid carrier]
  [isModule : Module R carrier]

attribute [instance] SemimoduleCat.isAddCommMonoid SemimoduleCat.isModule

namespace SemimoduleCat

instance : CoeSort (SemimoduleCat.{v} R) (Type v) :=
  ⟨SemimoduleCat.carrier⟩

attribute [coe] SemimoduleCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `SemimoduleCat R`. -/
abbrev of (X : Type v) [AddCommMonoid X] [Module R X] : SemimoduleCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X :=
  rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type v) [Semiring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : SemimoduleCat.{v} R) : of R M = M := by with_reducible rfl

variable {R} in
/-- The type of morphisms in `SemimoduleCat R`. -/
@[ext]
structure Hom (M N : SemimoduleCat.{v} R) where
  mk ::
  /-- The underlying linear map. -/
  hom' : M →ₗ[R] N

instance moduleCategory : Category.{v, max (v+1) u} (SemimoduleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (SemimoduleCat.{v} R) (· →ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

section

variable {R}

/-- Turn a morphism in `SemimoduleCat` back into a `LinearMap`. -/
abbrev Hom.hom {A B : SemimoduleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := SemimoduleCat R) f

/-- Typecheck a `LinearMap` as a morphism in `SemimoduleCat`. -/
abbrev ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := SemimoduleCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : SemimoduleCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

/- Provided for rewriting. -/
lemma id_apply (M : SemimoduleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[simp]
lemma hom_comp {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_bijective {M N : SemimoduleCat.{v} R} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) where
  left f g h := by cases f; cases g; simpa using h
  right f := ⟨⟨f⟩, rfl⟩

/-- Convenience shortcut for `SemimoduleCat.hom_bijective.injective`. -/
lemma hom_injective {M N : SemimoduleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.injective

/-- Convenience shortcut for `SemimoduleCat.hom_bijective.surjective`. -/
lemma hom_surjective {M N : SemimoduleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) :=
  hom_bijective.surjective

@[simp]
lemma hom_ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {M : Type v} [AddCommMonoid M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

@[simp]
lemma ofHom_comp {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/- Doesn't need to be `@[simp]` since `simp only` can solve this. -/
lemma ofHom_apply {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl

lemma inv_hom_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

/-- `SemimoduleCat.Hom.hom` bundled as an `Equiv`. -/
def homEquiv {M N : SemimoduleCat.{v} R} : (M ⟶ N) ≃ (M →ₗ[R] N) where
  toFun := Hom.hom
  invFun := ofHom

end

/- Not a `@[simp]` lemma since it will rewrite the (co)domain of maps and cause
definitional equality issues. -/
lemma forget_obj {M : SemimoduleCat.{v} R} : (forget (SemimoduleCat.{v} R)).obj M = M := rfl

@[simp]
lemma forget_map {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    (forget (SemimoduleCat.{v} R)).map f = f :=
  rfl

instance hasForgetToAddCommMonoid : HasForget₂ (SemimoduleCat R) AddCommMonCat where
  forget₂ :=
    { obj := fun M => .of M
      map := fun f => AddCommMonCat.ofHom f.hom.toAddMonoidHom }

@[simp]
theorem forget₂_obj (X : SemimoduleCat R) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj X = .of X :=
  rfl

theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommMonoid X] [Module R X] :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj (of R X) = .of X :=
  rfl

@[simp]
theorem forget₂_map (X Y : SemimoduleCat R) (f : X ⟶ Y) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).map f = AddCommMonCat.ofHom f.hom :=
  rfl

instance : Inhabited (SemimoduleCat R) :=
  ⟨of R PUnit⟩

@[simp] theorem of_coe (X : SemimoduleCat R) : of R X = X := rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[deprecated Iso.refl (since := "2025-05-15")]
def ofSelfIso (M : SemimoduleCat R) : SemimoduleCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

theorem isZero_of_subsingleton (M : SemimoduleCat R) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom (0 : M →ₗ[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨ofHom (0 : X →ₗ[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

instance : HasZeroObject (SemimoduleCat.{v} R) :=
  ⟨⟨of R PUnit, isZero_of_subsingleton _⟩⟩

end SemimoduleCat

variable {R}
variable {X₁ X₂ : Type v}

open SemimoduleCat

/-- Reinterpreting a linear map in the category of `R`-modules -/
scoped[SemimoduleCat] notation "↟" f:1024 => SemimoduleCat.ofHom f

section

/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
def LinearEquiv.toModuleIsoₛ {g₁ : AddCommMonoid X₁} {g₂ : AddCommMonoid X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : SemimoduleCat.of R X₁ ≅ SemimoduleCat.of R X₂ where
  hom := ofHom (e : X₁ →ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

namespace CategoryTheory.Iso

/-- Build a `LinearEquiv` from an isomorphism in the category `SemimoduleCat R`. -/
def toLinearEquivₛ {X Y : SemimoduleCat R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
  LinearEquiv.ofLinear i.hom.hom i.inv.hom (by aesop) (by aesop)

end CategoryTheory.Iso

/-- linear equivalences between `Module`s are the same as (isomorphic to) isomorphisms
in `SemimoduleCat` -/
@[simps]
def linearEquivIsoModuleIsoₛ {X Y : Type u} [AddCommMonoid X] [AddCommMonoid Y] [Module R X]
    [Module R Y] : (X ≃ₗ[R] Y) ≅ SemimoduleCat.of R X ≅ SemimoduleCat.of R Y where
  hom e := e.toModuleIsoₛ
  inv i := i.toLinearEquivₛ

end

namespace SemimoduleCat

section AddCommMonoid

variable {M N : SemimoduleCat.{v} R}

instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩

@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

instance : Zero (M ⟶ N) where
  zero := ⟨0⟩

@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

@[simp] lemma hom_zsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : AddCommMonoid (M ⟶ N) :=
  Function.Injective.addCommMonoid Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] lemma hom_sum {ι : Type*} (f : ι → (M ⟶ N)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ({ toFun := SemimoduleCat.Hom.hom, map_zero' := SemimoduleCat.hom_zero,
             map_add' := hom_add } : (M ⟶ N) →+ (M →ₗ[R] N)) _ _

/- TODO: generalize Preadditive and Functor.Additive, see #28826.
instance : Presemiadditive (SemimoduleCat.{v} R) where
instance : (forget₂ (SemimoduleCat.{v} R) AddCommMonCat).Additive where -/

instance : HasZeroMorphisms (SemimoduleCat.{v} R) where

/-- `SemimoduleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (M →ₗ[R] N) :=
  { homEquiv with
    map_add' := fun _ _ => rfl }

theorem subsingleton_of_isZero (h : IsZero M) : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 (fun x ↦ ?_)
  rw [← LinearMap.id_apply (R := R) x, ← SemimoduleCat.hom_id]
  simp only [(CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp h, hom_zero, LinearMap.zero_apply]

lemma isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommMonoid M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

end AddCommMonoid

section SMul

variable {M N : SemimoduleCat.{v} R}
variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance : SMul S (M ⟶ N) where
  smul c f := ⟨c • f.hom⟩

@[simp] lemma hom_smul (s : S) (f : M ⟶ N) : (s • f).hom = s • f.hom := rfl

end SMul

section Module

variable {M N : SemimoduleCat.{v} R} {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

instance Hom.instModule : Module S (M ⟶ N) :=
  Function.Injective.module S
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add }
    hom_injective
    (fun _ _ => rfl)

/-- `SemimoduleCat.Hom.hom` bundled as a linear equivalence. -/
@[simps]
def homLinearEquiv : (M ⟶ N) ≃ₗ[S] (M →ₗ[R] N) :=
  { homAddEquiv with
    map_smul' := fun _ _ => rfl }

end Module

section

universe u₀

namespace Algebra

variable {S₀ : Type u₀} [CommSemiring S₀] {S : Type u} [Semiring S] [Algebra S₀ S]

variable {M N : SemimoduleCat.{v} S}

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

/- TODO: generalize `Functor.Linear`, see #28826.
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
scoped instance instLinear : Linear S₀ (SemimoduleCat.{v} S) where
  smul_comp _ M N s₀ f g := by ext; simp -/

end Algebra

section

variable {S : Type u} [CommSemiring S]

/- TODO: generalize `Functor.Linear`, see #28826.
instance : Linear S (SemimoduleCat.{v} S) := SemimoduleCat.Algebra.instLinear -/

variable {X Y X' Y' : SemimoduleCat.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = ⟨LinearEquiv.arrowCongr i.toLinearEquivₛ j.toLinearEquivₛ f.hom⟩ :=
  rfl

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = ⟨LinearEquiv.conj i.toLinearEquivₛ f.hom⟩ :=
  rfl

end

end

/- TODO: Declarations in #28826 from `endSemiringEquiv` to `forget₂_map_homMk` can be added back
after appropriate generalizations. -/

instance : (forget (SemimoduleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (SemimoduleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIsoₛ).hom)

instance : (forget₂ (SemimoduleCat.{v} R) AddCommMonCat.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommMonCat).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)

end SemimoduleCat

section Bilinear

variable {R : Type*} [CommSemiring R]

namespace SemimoduleCat

/-- Turn a bilinear map into a homomorphism. -/
@[simps!]
def ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    M ⟶ of R (N ⟶ P) :=
  ofHom <| homLinearEquiv.symm.toLinearMap ∘ₗ f

/-- Turn a homomorphism into a bilinear map. -/
@[simps!]
def Hom.hom₂ {M N P : SemimoduleCat.{u} R}
    -- We write `Hom` instead of `M ⟶ (of R (N ⟶ P))`, otherwise dot notation breaks
    -- since it is expecting the type of `f` to be `SemimoduleCat.Hom`, not `Quiver.Hom`.
    (f : Hom M (of R (N ⟶ P))) :
    M →ₗ[R] N →ₗ[R] P :=
  Hom.hom (by convert (f ≫ ofHom homLinearEquiv.toLinearMap))

@[simp] lemma Hom.hom₂_ofHom₂ {M N P : SemimoduleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    (ofHom₂ f).hom₂ = f := rfl

@[simp] lemma ofHom₂_hom₂ {M N P : SemimoduleCat.{u} R} (f : M ⟶ of R (N ⟶ P)) :
    ofHom₂ f.hom₂ = f := rfl

end SemimoduleCat

end Bilinear

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp] theorem LinearMap.comp_id_semiModuleCat {R} [Semiring R]
    {G : SemimoduleCat.{u} R} {H : Type u} [AddCommMonoid H] [Module R H] (f : G →ₗ[R] H) :
    f.comp (𝟙 G : G ⟶ G).hom = f := by simp

@[simp] theorem LinearMap.id_semiModuleCat_comp {R} [Semiring R]
    {G : Type u} [AddCommMonoid G] [Module R G] {H : SemimoduleCat.{u} R} (f : G →ₗ[R] H) :
    LinearMap.comp (𝟙 H : H ⟶ H).hom f = f := by simp
