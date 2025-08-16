/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Defs

/-!

# Extension of algebras

## Main definition

- `Algebra.Extension`: An extension of an `R`-algebra `S` is an `R` algebra `P` together with a
surjection `P →ₐ[R] R`.

- `Algebra.Extension.Hom`: Given a commuting square
  ```
  R --→ P -→ S
  |          |
  ↓          ↓
  R' -→ P' → S
  ```
  A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.

- `Algebra.Extension.Cotangent`:
  The cotangent space wrt an extension `P → S` by `I`, i.e. the space `I/I²`.

-/

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
An extension of an `R`-algebra `S` is an `R` algebra `P` together with a surjection `P →ₐ[R] S`.
Also see `Algebra.Extension.ofSurjective`.
-/
structure Algebra.Extension where
  /-- The underlying algebra of an extension. -/
  Ring : Type w
  [commRing : CommRing Ring]
  [algebra₁ : Algebra R Ring]
  [algebra₂ : Algebra Ring S]
  [isScalarTower : IsScalarTower R Ring S]
  /-- A chosen (set-theoretic) section of an extension. -/
  σ : S → Ring
  algebraMap_σ : ∀ x, algebraMap Ring S (σ x) = x

namespace Algebra.Extension

variable {R S}
variable (P : Extension.{w} R S)

attribute [instance] commRing algebra₁ algebra₂ isScalarTower

attribute [simp] algebraMap_σ

-- We want to make sure `R₀` acts compatibly on `R` and `S` to avoid unsensical instances
@[nolint unusedArguments]
noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    Algebra R₀ P.Ring := Algebra.compHom P.Ring (algebraMap R₀ R)

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ R P.Ring := IsScalarTower.of_algebraMap_eq' rfl

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    {R₁} [CommRing R₁] [Algebra R₁ R] [Algebra R₁ S] [IsScalarTower R₁ R S]
    [Algebra R₀ R₁] [IsScalarTower R₀ R₁ R] :
    IsScalarTower R₀ R₁ P.Ring := IsScalarTower.of_algebraMap_eq' <| by
  rw [IsScalarTower.algebraMap_eq R₀ R, IsScalarTower.algebraMap_eq R₁ R,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R₀ R₁ R]

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq' <| by
  rw [IsScalarTower.algebraMap_eq R₀ R P.Ring, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

@[simp]
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def, algebraMap_σ]

lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.algebraMap_σ x, ← P.algebraMap_σ y, e]

lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) := (⟨_, P.algebraMap_σ ·⟩)

section Construction

/-- Construct `Extension` from a surjective algebra homomorphism. -/
@[simps -isSimp Ring σ]
noncomputable
def ofSurjective {P : Type w} [CommRing P] [Algebra R P] (f : P →ₐ[R] S)
    (h : Function.Surjective f) : Extension.{w} R S where
  Ring := P
  algebra₂ := f.toAlgebra
  isScalarTower := letI := f.toAlgebra; IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  σ x := (h x).choose
  algebraMap_σ x := (h x).choose_spec

variable (R S) in
/-- The trivial extension of `S`. -/
@[simps -isSimp Ring σ]
noncomputable
def self : Extension R S where
  Ring := S
  σ := _root_.id
  algebraMap_σ _ := rfl

/-- The kernel of an extension. -/
abbrev ker : Ideal P.Ring := RingHom.ker (algebraMap P.Ring S)

section Localization

variable (M : Submonoid S) {S' : Type*} [CommRing S'] [Algebra S S'] [IsLocalization M S']
variable [Algebra R S'] [IsScalarTower R S S']

/--
An `R`-extension `P → S` gives an `R`-extension `Pₘ → Sₘ`.
Note that this is different from `baseChange` as the base does not change.
-/
noncomputable
def localization (P : Extension.{w} R S) : Extension R S' where
  Ring := Localization (M.comap (algebraMap P.Ring S))
  algebra₂ := (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
      (g := (algebraMap S S').comp (algebraMap P.Ring S))
      (by simpa using fun x hx ↦ IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
  isScalarTower := by
    letI : Algebra (Localization (M.comap (algebraMap P.Ring S))) S' :=
      (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
        (g := (algebraMap S S').comp (algebraMap P.Ring S))
        (by simpa using fun x hx ↦ IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R P.Ring (Localization _),
      ← RingHom.comp_assoc, IsLocalization.lift_comp, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  σ s := Localization.mk (P.σ (IsLocalization.sec M s).1) ⟨P.σ (IsLocalization.sec M s).2, by simp⟩
  algebraMap_σ s := by
    simp [RingHom.algebraMap_toAlgebra, Localization.mk_eq_mk', IsLocalization.lift_mk',
      Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight, IsLocalization.sec_spec]

end Localization

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The base change of an `R`-extension of `S` to `T` gives a `T`-extension of `T ⊗[R] S`. -/
noncomputable
def baseChange {T} [CommRing T] [Algebra R T] (P : Extension R S) : Extension T (T ⊗[R] S) where
  Ring := T ⊗[R] P.Ring
  __ := ofSurjective (P := T ⊗[R] P.Ring) (Algebra.TensorProduct.map (AlgHom.id T T)
    (IsScalarTower.toAlgHom _ _ _)) (LinearMap.lTensor_surjective T
    (g := (IsScalarTower.toAlgHom R P.Ring S).toLinearMap) P.algebraMap_surjective)


end Construction

variable {R' S'} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Extension R' S')
variable {R'' S''} [CommRing R''] [CommRing S''] [Algebra R'' S''] (P'' : Extension R'' S'')

section Hom

section

variable [Algebra R R'] [Algebra R' R''] [Algebra R R'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

/-- Given a commuting square
```
R --→ P -→ S
|          |
↓          ↓
R' -→ P' → S
```
A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.
-/
@[ext]
structure Hom where
  /-- The underlying ring homomorphism of a hom between extensions. -/
  toRingHom : P.Ring →+* P'.Ring
  toRingHom_algebraMap :
    ∀ x, toRingHom (algebraMap R P.Ring x) = algebraMap R' P'.Ring (algebraMap R R' x)
  algebraMap_toRingHom :
    ∀ x, (algebraMap P'.Ring S' (toRingHom x)) = algebraMap S S' (algebraMap P.Ring S x)

attribute [simp] Hom.toRingHom_algebraMap Hom.algebraMap_toRingHom

variable {P P'}

/-- A hom between extensions as an algebra homomorphism. -/
noncomputable
def Hom.toAlgHom [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') :
    P.Ring →ₐ[R] P'.Ring where
  __ := f.toRingHom
  commutes' := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
lemma Hom.toAlgHom_apply [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') (x) :
    f.toAlgHom x = f.toRingHom x := rfl

variable (P P')

/-- The identity hom. -/
@[simps]
protected noncomputable def Hom.id : Hom P P := ⟨RingHom.id _, by simp, by simp⟩

@[simp]
lemma Hom.toAlgHom_id : Hom.toAlgHom (.id P) = AlgHom.id _ _ := by ext1; simp

variable {P P' P''}

variable [IsScalarTower R R' R''] [IsScalarTower S S' S''] in
/-- The composition of two homs. -/
@[simps]
noncomputable def Hom.comp (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  toRingHom := f.toRingHom.comp g.toRingHom
  toRingHom_algebraMap := by simp [← IsScalarTower.algebraMap_apply]
  algebraMap_toRingHom := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
lemma Hom.comp_id (f : Hom P P') : f.comp (Hom.id P) = f := by ext; simp

@[simp]
lemma Hom.id_comp (f : Hom P P') : (Hom.id P').comp f = f := by
  ext; simp [Hom.id]

/-- A map between extensions induce a map between kernels. -/
@[simps]
def Hom.mapKer (f : P.Hom P')
    [alg : Algebra P.Ring P'.Ring] (halg : algebraMap P.Ring P'.Ring = f.toRingHom) :
    P.ker →ₗ[P.Ring] P'.ker where
  toFun x := ⟨f.toRingHom x, by simp [show algebraMap P.Ring S x = 0 from x.2]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' := by simp [Algebra.smul_def, ← halg]

end

end Hom

section Infinitesimal

/-- Given an `R`-algebra extension `0 → I → P → S → 0` of `S`,
the infinitesimal extension associated to it is `0 → I/I² → P/I² → S → 0`. -/
noncomputable
def infinitesimal (P : Extension R S) : Extension R S where
  Ring := P.Ring ⧸ P.ker ^ 2
  σ := Ideal.Quotient.mk _ ∘ P.σ
  algebraMap_σ x := by dsimp; exact P.algebraMap_σ x

/-- The canonical map `P → P/I²` as maps between extensions. -/
noncomputable
def toInfinitesimal (P : Extension R S) : P.Hom P.infinitesimal where
  toRingHom := Ideal.Quotient.mk _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

lemma ker_infinitesimal (P : Extension R S) :
    P.infinitesimal.ker = P.ker.cotangentIdeal :=
  AlgHom.ker_kerSquareLift _

end Infinitesimal

section Cotangent

/-- The cotangent space of an extension.
This is a type synonym so that `P.Ring` can act on it through the action of `S` without creating
a diamond. -/
def Cotangent : Type _ := P.ker.Cotangent

noncomputable
instance : AddCommGroup P.Cotangent := inferInstanceAs (AddCommGroup P.ker.Cotangent)

variable {P}

/-- The identity map `P.ker.Cotangent → P.Cotangent` into the type synonym. -/
def Cotangent.of (x : P.ker.Cotangent) : P.Cotangent := x

/-- The identity map `P.Cotangent → P.ker.Cotangent` from the type synonym. -/
def Cotangent.val (x : P.Cotangent) : P.ker.Cotangent := x

@[ext]
lemma Cotangent.ext {x y : P.Cotangent} (e : x.val = y.val) : x = y := e

namespace Cotangent

variable (x y : P.Cotangent) (w z : P.ker.Cotangent)

@[simp] lemma val_add : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_zero : (0 : P.Cotangent).val = 0 := rfl
@[simp] lemma of_add : of (w + z) = of w + of z := rfl
@[simp] lemma of_zero : (of 0 : P.Cotangent) = 0 := rfl
@[simp] lemma of_val : of x.val = x := rfl
@[simp] lemma val_of : (of w).val = w := rfl
@[simp] lemma val_sub : (x - y).val = x.val - y.val := rfl

end Cotangent

lemma Cotangent.smul_eq_zero_of_mem (p : P.Ring) (hp : p ∈ P.ker) (m : P.ker.Cotangent) :
    p • m = 0 :=
  Ideal.Cotangent.smul_eq_zero_of_mem hp m

attribute [local simp] RingHom.mem_ker

noncomputable
instance Cotangent.module : Module S P.Cotangent where
  smul := fun r s ↦ .of (P.σ r • s.val)
  smul_zero := fun r ↦ ext (smul_zero (P.σ r))
  smul_add := fun r x y ↦ ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp ) x
    simpa only [sub_smul, add_smul, sub_eq_zero]
  zero_smul := fun x ↦ smul_eq_zero_of_mem (P.σ 0 : P.Ring) (by simp) x
  one_smul := fun x ↦ by
    have := smul_eq_zero_of_mem (P.σ 1 - 1 : P.Ring) (by simp) x
    simpa [sub_eq_zero, sub_smul]
  mul_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r * s) - (P.σ r * P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, mul_smul, sub_eq_zero] using this

noncomputable
instance {R₀} [CommRing R₀] [Algebra R₀ S] : Module R₀ P.Cotangent :=
  Module.compHom P.Cotangent (algebraMap R₀ S)

instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ S] [Algebra R₂ S] [Algebra R₁ R₂]
    [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ P.Cotangent := by
  constructor
  intros r s m
  change algebraMap R₂ S (r • s) • m = (algebraMap _ S r) • (algebraMap _ S s) • m
  rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply]

/-- The action of `R₀` on `P.Cotangent` for an extension `P → S`, if `S` is an `R₀` algebra. -/
lemma Cotangent.val_smul''' {R₀} [CommRing R₀] [Algebra R₀ S] (r : R₀) (x : P.Cotangent) :
    (r • x).val = P.σ (algebraMap R₀ S r) • x.val := rfl

/-- The action of `S` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
lemma Cotangent.val_smul (r : S) (x : P.Cotangent) : (r • x).val = P.σ r • x.val := rfl

/-- The action of `P` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
lemma Cotangent.val_smul' (r : P.Ring) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [val_smul''', ← sub_eq_zero, ← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

/-- The action of `R` on `P.Cotangent` for an `R`-extension `P → S`. -/
@[simp]
lemma Cotangent.val_smul'' (r : R) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [← algebraMap_smul P.Ring, val_smul', algebraMap_smul]

/-- The quotient map from the kernel of `P → S` onto the cotangent space. -/
noncomputable def Cotangent.mk : P.ker →ₗ[P.Ring] P.Cotangent where
  toFun x := .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
  map_smul' x y := ext <| by simp

@[simp]
lemma Cotangent.val_mk (x : P.ker) : (mk x).val = Ideal.toCotangent _ x := rfl

lemma Cotangent.mk_surjective : Function.Surjective (mk (P := P)) :=
  fun x ↦ Ideal.toCotangent_surjective P.ker x.val

lemma Cotangent.mk_eq_zero_iff {P : Extension R S} (x : P.ker) :
    Cotangent.mk x = 0 ↔ x.val ∈ P.ker ^ 2 := by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]

variable {P'}
variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']
variable [Algebra R S'] [IsScalarTower R R' S']

/-- A hom between two extensions induces a map between cotangent spaces. -/
noncomputable
def Cotangent.map (f : Hom P P') : P.Cotangent →ₗ[S] P'.Cotangent where
  toFun x := .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx ↦ by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
  map_add' x y := ext (map_add _ x.val y.val)
  map_smul' r x := by
    ext
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective r
    simp only [algebraMap_smul, val_smul', val_mk, val_of, Ideal.mapCotangent_toCotangent,
      RingHomCompTriple.comp_apply, ← (Ideal.toCotangent _).map_smul]
    conv_rhs => rw [← algebraMap_smul S', ← f.algebraMap_toRingHom, algebraMap_smul, val_smul',
      val_of, ← (Ideal.toCotangent _).map_smul]
    congr 1
    ext1
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, Hom.toAlgHom_apply]

@[simp]
lemma Cotangent.map_mk (f : Hom P P') (x) :
    Cotangent.map f (.mk x) =
      .mk ⟨f.toAlgHom x, by simpa [-map_aeval] using RingHom.congr_arg (algebraMap S S') x.2⟩ :=
  rfl

@[simp]
lemma Cotangent.map_id :
    Cotangent.map (.id P) = LinearMap.id := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_id, AlgHom.coe_id, id_eq, Subtype.coe_eta, val_mk,
    LinearMap.id_coe]

variable [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower R' R'' S'']
  [Algebra R S''] [IsScalarTower R R'' S''] [IsScalarTower S S' S'']

lemma Cotangent.map_comp (f : Hom P P') (g : Hom P' P'') :
    Cotangent.map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
    val_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars]

lemma Cotangent.finite (hP : P.ker.FG) :
    Module.Finite S P.Cotangent := by
  refine ⟨.of_restrictScalars (R := P.Ring) _ ?_⟩
  rw [Submodule.restrictScalars_top, ← LinearMap.range_eq_top.mpr Extension.Cotangent.mk_surjective,
    ← Submodule.map_top]
  exact (P.ker.fg_top.mpr hP).map _

end Cotangent

end Algebra.Extension
