/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Change Of Rings

## Main definitions

* `ModuleCat.restrictScalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrictScalars : ModuleCat S ⥤ ModuleCat R` is defined by `M ↦ M` where an `S`-module `M`
  is seen as an `R`-module by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as
  well.

* `ModuleCat.extendScalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extendScalars : ModuleCat R ⥤ ModuleCat S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

* `ModuleCat.coextendScalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`
  then `coextendScalars : ModuleCat R ⥤ ModuleCat S` is defined by `M ↦ (S →ₗ[R] M)` where `S` is
  seen as an `R`-module by restriction of scalars and `l ↦ l ∘ _`.

## Main results

* `ModuleCat.extendRestrictScalarsAdj`: given commutative rings `R, S` and a ring
  homomorphism `f : R →+* S`, the extension and restriction of scalars by `f` are adjoint functors.
* `ModuleCat.restrictCoextendScalarsAdj`: given rings `R, S` and a ring homomorphism
  `f : R ⟶ S` then `coextendScalars f` is the right adjoint of `restrictScalars f`.

## Notation
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f] m` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`.
-/

@[expose] public section

suppress_compilation


open CategoryTheory Limits

namespace ModuleCat

universe v u₁ u₂ u₃ w

namespace RestrictScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
variable (M : ModuleCat.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
`r • m := f r • m` (`Module.compHom`). This is called restriction of scalars. -/
def obj' : ModuleCat R :=
  let _ := Module.compHom M f
  of R M

/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `RestrictScalars.obj'` needs to be redesigned.
  ofHom (X := obj' f M) (Y := obj' f M')
    { g.hom with map_smul' := fun r => g.hom.map_smul (f r) }

end RestrictScalars

/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj := RestrictScalars.obj' f
  map := RestrictScalars.map' f

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).Faithful where
  map_injective h := by
    ext x
    simpa only using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).PreservesMonomorphisms where
  preserves _ h := by rwa [mono_iff_injective] at h ⊢

instance {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars f).ReflectsIsomorphisms :=
  have : (restrictScalars f ⋙ CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms :=
    inferInstanceAs% (CategoryTheory.forget (ModuleCat S)).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (CategoryTheory.forget _)

-- Porting note: this should be automatic
-- TODO: this instance gives diamonds if `f : S →+* S`, see `PresheafOfModules.pushforward₀`.
-- The correct solution is probably to define explicit maps between `M` and
-- `(restrictScalars f).obj M`.
instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} : Module S <| (restrictScalars f).obj M :=
  inferInstanceAs <| Module S M

@[simp]
theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) : (restrictScalars f).map g x = g x :=
  rfl

@[simp]
theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (restrictScalars f).obj M) : r • m = f r • show M from m :=
  rfl

theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) :
    r • (show (restrictScalars f).obj M from m) = f r • m :=
  rfl


instance (priority := 100) sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R] [CommRing S]
    (f : R →+* S) (M : Type v) [I : AddCommGroup M] [Module S M] :
    haveI : SMul R M := (RestrictScalars.obj' f (ModuleCat.of S M)).isModule.toSMul
    SMulCommClass R S M :=
  @SMulCommClass.mk R S M (_) _
    fun r s m => (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear maps `M →ₛₗ[f] N` identify to
morphisms `M ⟶ (ModuleCat.restrictScalars f).obj N`. -/
@[simps]
def semilinearMapAddEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    (M →ₛₗ[f] N) ≃+ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  toFun g := ofHom (Y := (ModuleCat.restrictScalars f).obj N) <|
    { toFun := g
      map_add' := by simp
      map_smul' := by simp }
  invFun g :=
    { toFun := g
      map_add' := by simp
      map_smul' := g.hom.map_smul }
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restrictions scalars along equal ring homomorphisms are naturally isomorphic. -/
def restrictScalarsCongr
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g) :
    ModuleCat.restrictScalars f ≅ ModuleCat.restrictScalars g :=
  NatIso.ofComponents (fun X ↦ LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars f).obj X) (X₂ := (ModuleCat.restrictScalars g).obj X)
    { __ := AddEquiv.refl _, map_smul' _ _ := by subst e; rfl }) fun _ ↦ by subst e; rfl

@[simp]
lemma restrictScalarsCongr_symm
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g) :
  (restrictScalarsCongr e).symm = restrictScalarsCongr e.symm := rfl

@[simp]
lemma restrictScalarsCongr_hom_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).hom.app M x = x := rfl

@[simp]
lemma restrictScalarsCongr_inv_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (restrictScalarsCongr e).inv.app M x = x := rfl

section

variable {R : Type u₁} [Ring R] (f : R →+* R)

/-- For an `R`-module `M`, the restriction of scalars of `M` by the identity morphism identifies
to `M`. -/
def restrictScalarsId'App (hf : f = RingHom.id R) (M : ModuleCat R) :
    (restrictScalars f).obj M ≅ M :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _ (((restrictScalars f).obj M).isModule) _
      (by rfl) (fun r x ↦ by subst hf; rfl)

variable (hf : f = RingHom.id R)

@[simp] lemma restrictScalarsId'App_hom_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).hom x = x :=
  rfl

@[simp] lemma restrictScalarsId'App_inv_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).inv x = x :=
  rfl

/-- The restriction of scalars by a ring morphism that is the identity identifies to the
identity functor. -/
@[simps! hom_app inv_app]
def restrictScalarsId' : ModuleCat.restrictScalars.{v} f ≅ 𝟭 _ :=
    NatIso.ofComponents <| fun M ↦ restrictScalarsId'App f hf M

@[reassoc]
lemma restrictScalarsId'App_hom_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    (restrictScalars f).map φ ≫ (restrictScalarsId'App f hf N).hom =
      (restrictScalarsId'App f hf M).hom ≫ φ :=
  (restrictScalarsId' f hf).hom.naturality φ

@[reassoc]
lemma restrictScalarsId'App_inv_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    φ ≫ (restrictScalarsId'App f hf N).inv =
      (restrictScalarsId'App f hf M).inv ≫ (restrictScalars f).map φ :=
  (restrictScalarsId' f hf).inv.naturality φ

variable (R)

/-- The restriction of scalars by the identity morphism identifies to the
identity functor. -/
abbrev restrictScalarsId := restrictScalarsId'.{v} (RingHom.id R) rfl

end

section

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Ring R₁] [Ring R₂] [Ring R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃)

/-- For each `R₃`-module `M`, restriction of scalars of `M` by a composition of ring morphisms
identifies to successively restricting scalars. -/
def restrictScalarsComp'App (hgf : gf = g.comp f) (M : ModuleCat R₃) :
    (restrictScalars gf).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    (by rfl)
    (fun r x ↦ by subst hgf; rfl)).toModuleIso

variable (hgf : gf = g.comp f)

@[simp] lemma restrictScalarsComp'App_hom_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).hom x = x :=
  rfl

@[simp] lemma restrictScalarsComp'App_inv_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).inv x = x :=
  rfl

/-- The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors. -/
@[simps! hom_app inv_app]
def restrictScalarsComp' :
    ModuleCat.restrictScalars.{v} gf ≅
      ModuleCat.restrictScalars g ⋙ ModuleCat.restrictScalars f :=
  NatIso.ofComponents <| fun M ↦ restrictScalarsComp'App f g gf hgf M

@[reassoc]
lemma restrictScalarsComp'App_hom_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ (restrictScalarsComp'App f g gf hgf N).hom =
      (restrictScalarsComp'App f g gf hgf M).hom ≫
        (restrictScalars f).map ((restrictScalars g).map φ) :=
  (restrictScalarsComp' f g gf hgf).hom.naturality φ

@[reassoc]
lemma restrictScalarsComp'App_inv_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (restrictScalars f).map ((restrictScalars g).map φ) ≫
        (restrictScalarsComp'App f g gf hgf N).inv =
      (restrictScalarsComp'App f g gf hgf M).inv ≫ (restrictScalars gf).map φ :=
  (restrictScalarsComp' f g gf hgf).inv.naturality φ

/-- The restriction of scalars by a composition of ring morphisms identifies to the
composition of the restriction of scalars functors. -/
abbrev restrictScalarsComp := restrictScalarsComp'.{v} f g _ rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence of categories `ModuleCat S ≌ ModuleCat R` induced by `e : R ≃+* S`. -/
def restrictScalarsEquivalenceOfRingEquiv {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    ModuleCat S ≌ ModuleCat R where
  functor := ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := M)
    (X₂ := (restrictScalars e.symm.toRingHom).obj ((restrictScalars e.toRingHom).obj M))
    { __ := AddEquiv.refl M
      map_smul' := fun s m ↦ congr_arg (· • m) (e.right_inv s).symm }) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := (restrictScalars e.toRingHom).obj ((restrictScalars e.symm.toRingHom).obj M))
    (X₂ := M)
    { __ := AddEquiv.refl M
      map_smul' := fun r _ ↦ congr_arg (· • (_ : M)) (e.left_inv r) }) (by intros; rfl)
  functor_unitIso_comp := by intros; rfl

instance restrictScalars_isEquivalence_of_ringEquiv {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
  (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

instance {R S} [Ring R] [Ring S] (f : R →+* S) : (restrictScalars f).Additive where

instance restrictScalarsEquivalenceOfRingEquiv_additive {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.Additive where

namespace Algebra

instance {R₀ R S} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
    (f : R →ₐ[R₀] S) : (restrictScalars f.toRingHom).Linear R₀ where
  map_smul {M N} g r₀ := by ext m; exact congr_arg (· • g.hom m) (f.commutes r₀).symm

instance restrictScalarsEquivalenceOfRingEquiv_linear
    {R₀ R S} [CommSemiring R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S] (e : R ≃ₐ[R₀] S) :
    (restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.Linear R₀ :=
  inferInstanceAs% ((restrictScalars e.toAlgHom.toRingHom).Linear R₀)

end Algebra

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

section ModuleCat.Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- Tensor product of elements along a base change.

This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
without this notation, one needs to work with `s : (restrictScalars f).obj ⟨S⟩`. -/
scoped[ChangeOfRings] notation:100 s:100 " ⊗ₜ[" R "," f "] " m:101 =>
  @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

open ChangeOfRings

namespace ExtendScalars

variable (M : ModuleCat.{v} R)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars turns an `R`-module into an `S`-module by M ↦ S ⨂ M
-/
def obj' : ModuleCat S :=
  of _ (TensorProduct R ((restrictScalars f).obj (of _ S)) M)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2 :=
  ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

set_option backward.isDefEq.respectTransparency false in
theorem map'_id {M : ModuleCat.{v} R} : map' f (𝟙 M) = 𝟙 _ := by
  simp [map', obj']

theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => grind

end ExtendScalars

/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def extendScalars {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj M := ExtendScalars.obj' f M
  map l := ExtendScalars.map' f l
  map_id _ := ExtendScalars.map'_id f
  map_comp := ExtendScalars.map'_comp f

namespace ExtendScalars

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
@[simp]
protected theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s' ⊗ₜ[R,f] m : (extendScalars f).obj M) = (s * s') ⊗ₜ[R,f] m :=
  rfl

@[simp]
theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (extendScalars f).map g (s ⊗ₜ[R,f] m) = s ⊗ₜ[R,f] g m :=
  rfl

variable {f}

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_ext {M : ModuleCat R} {N : ModuleCat S}
    {α β : (extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M), α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β := by
  apply (restrictScalars f).map_injective
  letI := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s ⊗ₜ m) = β (s ⊗ₜ m)
  have : s ⊗ₜ[R] (m : M) = s • (1 : S) ⊗ₜ[R] m := by
    rw [ExtendScalars.smul_tmul, mul_one]
  simp only [this, map_smul, h]

end ExtendScalars

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
-- Porting note: this seems to cause problems related to lack of reducibility
-- local notation "S'" => (restrictScalars f).obj ⟨S⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given an `R`-module M, consider Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
-/
instance hasSMul : SMul S <| (restrictScalars f).obj (of _ S) →ₗ[R] M where
  smul s g :=
    { toFun := fun s' : S => g (s' * s : S)
      map_add' := fun x y : S => by rw [add_mul, map_add]
      map_smul' := fun r (t : S) => by
        simp [← map_smul, ModuleCat.restrictScalars.smul_def (M := ModuleCat.of _ S), mul_assoc] }

@[simp]
theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
    (s • g) s' = g (s' * s : S) :=
  rfl

instance mulAction : MulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.hasSMul f _ with
    one_smul := fun g => LinearMap.ext fun s : S => by simp
    mul_smul := fun (s t : S) g => LinearMap.ext fun x : S => by simp [mul_assoc] }

instance distribMulAction : DistribMulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.mulAction f _ with
    smul_add := fun s g h => LinearMap.ext fun _ : S => by simp
    smul_zero := fun _ => LinearMap.ext fun _ : S => by simp }

set_option backward.isDefEq.respectTransparency false in
/-- `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
-/
instance isModule : Module S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.distribMulAction f _ with
    add_smul := fun s1 s2 g => LinearMap.ext fun x : S => by simp [mul_add, map_add]
    zero_smul := fun g => LinearMap.ext fun x : S => by simp [map_zero] }

end Unbundled

variable (M : ModuleCat.{v} R)

/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with
scalar multiplication defined by `s • l := x ↦ l (x • s)` -/
def obj' : ModuleCat S :=
  of _ ((restrictScalars f).obj (of _ S) →ₗ[R] M)

instance : CoeFun (obj' f M) fun _ => S → M :=
  inferInstanceAs <| CoeFun ((restrictScalars f).obj (of _ S) →ₗ[R] M) _

/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h` -/
@[simps!]
def map' {M M' : ModuleCat R} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  ofHom
  { toFun := fun h => g.hom.comp h
    map_add' := fun _ _ => LinearMap.comp_add _ _ _
    map_smul' := fun s h => by ext; simp }

end CoextendScalars

/--
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor from `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module via restriction of
scalars and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.
-/
def coextendScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S where
  obj := CoextendScalars.obj' f
  map := CoextendScalars.map' f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

instance (M : ModuleCat R) : CoeFun ((coextendScalars f).obj M) fun _ => S → M :=
  inferInstanceAs <| CoeFun (CoextendScalars.obj' f M) _

theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
    (s • g) s' = g (s' * s) :=
  rfl

@[simp]
theorem map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (coextendScalars f).map g x s = g (x s) :=
  rfl

end CoextendScalars

namespace RestrictionCoextensionAdj

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, any `g : (restrictScalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextendScalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
-/
def HomEquiv.fromRestriction {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) : Y ⟶ (coextendScalars f).obj X :=
  ofHom
  { toFun := fun y : Y =>
      { toFun := fun s : S => g <| (s • y : Y)
        map_add' := fun s1 s2 : S => by simp only [add_smul]; rw [map_add]
        map_smul' := fun r (s : S) => by
          -- Porting note: dsimp clears out some rw's but less eager to apply others with Lean 4
          dsimp
          rw [← g.hom.map_smul]
          erw [smul_eq_mul, mul_smul]
          rfl }
    map_add' := fun y1 y2 : Y =>
      LinearMap.ext fun s : S => by
        simp [smul_add, map_add]
    map_smul' := fun (s : S) (y : Y) => LinearMap.ext fun t : S => by
        simp [mul_smul] }

/-- This should be autogenerated by `@[simps]` but we need to give `s` the correct type here. -/
@[simp] lemma HomEquiv.fromRestriction_hom_apply_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) (y) (s : S) :
    (HomEquiv.fromRestriction f g).hom y s = g (s • y) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextendScalars f).obj X`
corresponds to `(restrictScalars f).obj Y ⟶ X` by `y ↦ g y 1`
-/
def HomEquiv.toRestriction {X Y} (g : Y ⟶ (coextendScalars f).obj X) :
    (restrictScalars f).obj Y ⟶ X :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (X := (restrictScalars f).obj Y)
  { toFun := fun y : Y => (g y) (1 : S)
    map_add' := fun x y => by dsimp; rw [g.hom.map_add, LinearMap.add_apply]
    map_smul' := fun r (y : Y) => by
      dsimp
      rw [← map_smul]
      erw [smul_eq_mul, mul_one, map_smul]
      rw [CoextendScalars.smul_apply (s := f r) (g := g y) (s' := 1), one_mul]
      simp }

/-- This should be autogenerated by `@[simps]` but we need to give `1` the correct type here. -/
@[simp] lemma HomEquiv.toRestriction_hom_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : Y ⟶ (coextendScalars f).obj X) (y) :
    (HomEquiv.toRestriction f g).hom y = g.hom y (1 : S) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unit'`, to address timeouts. -/
def app' (Y : ModuleCat S) : Y →ₗ[S] (restrictScalars f ⋙ coextendScalars f).obj Y :=
  { toFun := fun y : Y =>
      { toFun := fun s : S => (s • y : Y)
        map_add' := fun _ _ => add_smul _ _ _
        map_smul' := fun r (s : S) => by
          dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
          erw [smul_eq_mul, mul_smul]
          simp }
    map_add' := fun y1 y2 =>
      LinearMap.ext fun s : S => by
        -- Porting note: double dsimp seems odd
        dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
          RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, ZeroHom.coe_mk, smul_eq_mul, id_eq, eq_mpr_eq_cast, cast_eq,
          Functor.comp_obj]
        rw [LinearMap.add_apply, LinearMap.coe_mk, LinearMap.coe_mk, LinearMap.coe_mk]
        dsimp
        rw [smul_add]
    map_smul' := fun s (y : Y) => LinearMap.ext fun t : S => by
      -- Porting note: used to be simp [mul_smul]
      rw [RingHom.id_apply, LinearMap.coe_mk, CoextendScalars.smul_apply', LinearMap.coe_mk]
      dsimp
      rw [mul_smul] }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps]
protected noncomputable def unit' : 𝟭 (ModuleCat S) ⟶ restrictScalars f ⋙ coextendScalars f where
  app Y := ofHom (app' f Y)
  naturality Y Y' g :=
    hom_ext <| LinearMap.ext fun y : Y => LinearMap.ext fun s : S => by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): previously simp [CoextendScalars.map_apply]
      simp only [ModuleCat.hom_comp, Functor.id_map, Functor.id_obj, Functor.comp_obj,
        Functor.comp_map]
      change s • (g y) = g (s • y)
      rw [map_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps]
protected noncomputable def counit' : coextendScalars f ⋙ restrictScalars f ⟶ 𝟭 (ModuleCat R) where
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  app X := ofHom (X := (restrictScalars f).obj ((coextendScalars f).obj X))
    { toFun := fun g => g.toFun (1 : S)
      map_add' := fun x1 x2 => by
        dsimp
        rw [LinearMap.add_apply]
      map_smul' := fun r (g : (restrictScalars f).obj ((coextendScalars f).obj X)) => by
        dsimp
        rw [CoextendScalars.smul_apply, one_mul, ← map_smul]
        congr
        change f r = f r • (1 : S)
        rw [smul_eq_mul (f r) 1, mul_one] }

end RestrictionCoextensionAdj

set_option backward.isDefEq.respectTransparency false in
-- Porting note: very fiddly universes
/-- Restriction of scalars is left adjoint to coextension of scalars. -/
-- @[simps] Porting note: not in normal form and not used
def restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    restrictScalars.{max v u₂, u₁, u₂} f ⊣ coextendScalars f :=
  Adjunction.mk' {
    homEquiv := fun X Y ↦
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁, u₂, v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁, u₂, v} f
        left_inv := fun g => by ext; simp
        right_inv := fun g => hom_ext <| LinearMap.ext fun x => LinearMap.ext fun s : S => by
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): once just simp
          rw [RestrictionCoextensionAdj.HomEquiv.fromRestriction_hom_apply_apply,
              RestrictionCoextensionAdj.HomEquiv.toRestriction_hom_apply, map_smulₛₗ,
              RingHom.id_apply, CoextendScalars.smul_apply', one_mul] }
    unit := RestrictionCoextensionAdj.unit'.{u₁, u₂, v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁, u₂, v} f
    homEquiv_unit := hom_ext <| LinearMap.ext fun _ => rfl
    homEquiv_counit := fun {X Y g} => by
      ext
      simp [RestrictionCoextensionAdj.counit'] }

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{max u₂ w} f).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (coextendScalars.{u₁, u₂, max u₂ w} f).IsRightAdjoint :=
  (restrictCoextendScalarsAdj f).isRightAdjoint

namespace ExtendRestrictScalarsAdj

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `g : (extendScalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrictScalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps! hom_apply]
def HomEquiv.toRestrictScalars {X Y} (g : (extendScalars f).obj X ⟶ Y) :
    X ⟶ (restrictScalars f).obj Y :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (restrictScalars f).obj Y)
  { toFun := fun x => g <| (1 : S) ⊗ₜ[R,f] x
    map_add' := fun _ _ => by dsimp; rw [tmul_add, map_add]
    map_smul' := fun r s => by
      letI : Module R S := Module.compHom S f
      letI : Module R Y := Module.compHom Y f
      dsimp
      rw [RestrictScalars.smul_def, ← LinearMap.map_smul]
      erw [tmul_smul]
      congr }

set_option backward.isDefEq.respectTransparency false in
-- Porting note: forced to break apart fromExtendScalars due to timeouts
/--
The map `S → X →ₗ[R] Y` given by `fun s x => s • (g x)`
-/
@[simps]
def HomEquiv.evalAt {X : ModuleCat R} {Y : ModuleCat S} (s : S)
    (g : X ⟶ (restrictScalars f).obj Y) : have : Module R Y := Module.compHom Y f
    X →ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun := fun x => s • (g x : Y)
      map_add' := by
        intros
        dsimp only
        rw [map_add, smul_add] }
    (by
      intro r x
      rw [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, map_smul, smul_comm r s (g x : Y)])

set_option backward.isDefEq.respectTransparency false in
/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrictScalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps! hom_apply]
def HomEquiv.fromExtendScalars {X Y} (g : X ⟶ (restrictScalars f).obj Y) :
    (extendScalars f).obj X ⟶ Y := by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom
    { toFun z := TensorProduct.lift (σ₁₂ := .id _) ?_ z, map_add' := ?_, map_smul' := ?_ }
  · refine
    { toFun s := HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) ↦ ?_,
      map_smul' := fun (r : R) (s : S) ↦ ?_ }
    · ext
      dsimp only [m2, evalAt_apply, LinearMap.add_apply]
      rw [← add_smul]
    · ext x
      apply mul_smul (f r) s (g x)
  · simp
  · intro s z
    change lift _ (s • z) = s • lift _ z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x =>
      rw [LinearMap.coe_mk, ExtendScalars.smul_tmul]
      erw [lift.tmul, lift.tmul]
      set s' : S := s'
      change (s * s') • (g x) = s • s' • (g x)
      rw [mul_smul]
    | add _ _ ih1 ih2 => rw [smul_add, map_add, ih1, ih2, map_add, smul_add]

set_option backward.isDefEq.respectTransparency false in
/-- Given `R`-module X and `S`-module Y, `S`-linear maps `(extendScalars f).obj X ⟶ Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrictScalars f).obj Y`.
-/
@[simps symm_apply]
def homEquiv {X Y} :
    ((extendScalars f).obj X ⟶ Y) ≃ (X ⟶ (restrictScalars.{max v u₂, u₁, u₂} f).obj Y) where
  toFun := HomEquiv.toRestrictScalars.{u₁, u₂, v} f
  invFun := HomEquiv.fromExtendScalars.{u₁, u₂, v} f
  left_inv g := by
    letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
    apply hom_ext
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x s =>
      erw [TensorProduct.lift.tmul]
      simp only [LinearMap.coe_mk]
      change S at x
      dsimp
      erw [← map_smul, ExtendScalars.smul_tmul, mul_one x]
      rfl
    | add _ _ ih1 ih2 => rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
    ext x
    rw [HomEquiv.toRestrictScalars_hom_apply]
    -- This needs to be `erw` because of some unfolding in `fromExtendScalars`
    erw [HomEquiv.fromExtendScalars_hom_apply]
    rw [lift.tmul, LinearMap.coe_mk, LinearMap.coe_mk]
    dsimp
    rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
-- @[simps] Porting note: not in normal form and not used
def Unit.map {X} : X ⟶ (extendScalars f ⋙ restrictScalars f).obj X :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ofHom (Y := (extendScalars f ⋙ restrictScalars f).obj X)
  { toFun := fun x => (1 : S) ⊗ₜ[R,f] x
    map_add' := fun x x' => by dsimp; rw [TensorProduct.tmul_add]
    map_smul' := fun r x => by
      letI m1 : Module R S := Module.compHom S f
      dsimp; rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul'] }

/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
def unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂, u₁, u₂} f where
  app _ := Unit.map.{u₁, u₂, v} f

set_option backward.isDefEq.respectTransparency false in
set_option backward.proofsInPublic true in
/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y` -/
@[simps! hom_apply]
def Counit.map {Y} : (restrictScalars f ⋙ extendScalars f).obj Y ⟶ Y :=
  ofHom
  { toFun :=
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      TensorProduct.lift
      { toFun := fun s : S =>
        { toFun := fun y : Y => s • y,
          map_add' := smul_add _
          map_smul' := fun r y => by
            change s • f r • y = f r • s • y
            rw [← mul_smul, mul_comm, mul_smul] },
        map_add' := fun s₁ s₂ => by
          ext y
          change (s₁ + s₂) • y = s₁ • y + s₂ • y
          rw [add_smul]
        map_smul' := fun r s => by
          ext y
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul, mul_smul] }
    map_add' := fun _ _ => by rw [map_add]
    map_smul' := fun s z => by
      let m1 : Module R S := Module.compHom S f
      let m2 : Module R Y := Module.compHom Y f
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y =>
        rw [ExtendScalars.smul_tmul, LinearMap.coe_mk]
        erw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        set s' : S := s'
        change (s * s') • y = s • s' • y
        rw [mul_smul]
      | add _ _ ih1 ih2 => rw [smul_add, map_add, map_add, ih1, ih2, smul_add] }

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps app]
def counit : restrictScalars.{max v u₂, u₁, u₂} f ⋙ extendScalars f ⟶ 𝟭 (ModuleCat S) where
  app _ := Counit.map.{u₁, u₂, v} f
  naturality Y Y' g := by
    -- Porting note: this is very annoying; fix instances in concrete categories
    letI m1 : Module R S := Module.compHom S f
    letI m2 : Module R Y := Module.compHom Y f
    letI m2 : Module R Y' := Module.compHom Y' f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s' y =>
      dsimp
      -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
      erw [Counit.map_hom_apply]
      rw [lift.tmul, LinearMap.coe_mk, LinearMap.coe_mk]
      set s' : S := s'
      change s' • g y = g (s' • y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1
end ExtendRestrictScalarsAdj

set_option backward.isDefEq.respectTransparency false in
/-- Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and restriction of
scalars by `f` are adjoint to each other.
-/
def extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    extendScalars.{u₁, u₂, max v u₂} f ⊣ restrictScalars.{max v u₂, u₁, u₂} f :=
  Adjunction.mk' {
    homEquiv := fun _ _ ↦ ExtendRestrictScalarsAdj.homEquiv.{v, u₁, u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v, u₁, u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v, u₁, u₂} f
    homEquiv_unit := fun {X Y g} ↦ hom_ext <| LinearMap.ext fun x => by
      dsimp
      rfl
    homEquiv_counit := fun {X Y g} ↦ hom_ext <| LinearMap.ext fun x => by
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul =>
          rw [ExtendRestrictScalarsAdj.homEquiv_symm_apply]
          dsimp
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [ExtendRestrictScalarsAdj.Counit.map_hom_apply,
              ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
        | add => rw [map_add, map_add]; congr 1 }

lemma extendRestrictScalarsAdj_homEquiv_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {f : R →+* S} {M : ModuleCat.{max v u₂} R} {N : ModuleCat S}
    (φ : (extendScalars f).obj M ⟶ N) (m : M) :
    (extendRestrictScalarsAdj f).homEquiv _ _ φ m = φ ((1 : S) ⊗ₜ m) :=
  rfl

lemma extendRestrictScalarsAdj_unit_app_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{max v u₂} R) (m : M) :
    (extendRestrictScalarsAdj f).unit.app M m = (1 : S) ⊗ₜ[R,f] m :=
  rfl

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (extendScalars.{u₁, u₂, max u₂ w} f).IsLeftAdjoint :=
  (extendRestrictScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (restrictScalars.{max u₂ w, u₁, u₂} f).IsRightAdjoint :=
  (extendRestrictScalarsAdj f).isRightAdjoint

noncomputable instance preservesLimit_restrictScalars
    {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R →+* S) {J : Type*} [Category* J]
    (F : J ⥤ ModuleCat.{v} S) [Small.{v} (F ⋙ forget _).sections] :
    PreservesLimit F (restrictScalars f) :=
  ⟨fun {c} hc => ⟨by
    have hc' := isLimitOfPreserves (forget₂ _ AddCommGrpCat) hc
    exact isLimitOfReflects (forget₂ _ AddCommGrpCat) hc'⟩⟩

instance preservesColimit_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {J : Type*} [Category* J] (F : J ⥤ ModuleCat.{v} S)
    [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)] :
    PreservesColimit F (ModuleCat.restrictScalars.{v} f) := by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
    inferInstanceAs% (HasColimit (F ⋙ forget₂ _ AddCommGrpCat))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ (ModuleCat.{v} R) AddCommGrpCat)
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
  exact HasColimit.isColimitColimitCocone F

variable (R) in
/-- The extension of scalars by the identity of a ring is isomorphic to the
identity functor. -/
noncomputable def extendScalarsId : extendScalars (RingHom.id R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm

lemma extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M) :
    (extendScalarsId R).inv.app M m = (1 : R) ⊗ₜ m := rfl

set_option backward.isDefEq.respectTransparency false in
lemma homEquiv_extendScalarsId (M : ModuleCat R) :
    (extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((extendScalarsId R).hom.app M) =
      (restrictScalarsId R).inv.app M := by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply, ← extendScalarsId_inv_app_apply, ← comp_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    (extendScalarsId R).hom.app M ((1 : R) ⊗ₜ m) = m := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply,
    homEquiv_extendScalarsId]
  dsimp

section

variable {R₁ R₂ R₃ R₄ : Type u₁} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄)

/-- The extension of scalars by a composition of commutative ring morphisms
identifies to the composition of the extension of scalars functors. -/
noncomputable def extendScalarsComp :
    extendScalars (f₂₃.comp f₁₂) ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃ :=
  (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂))).symm (restrictScalarsComp f₁₂ f₂₃).symm

set_option backward.isDefEq.respectTransparency false in
lemma homEquiv_extendScalarsComp (M : ModuleCat R₁) :
    (extendRestrictScalarsAdj (f₂₃.comp f₁₂)).homEquiv _ _
      ((extendScalarsComp f₁₂ f₂₃).hom.app M) =
      (extendRestrictScalarsAdj f₁₂).unit.app M ≫
        (restrictScalars f₁₂).map ((extendRestrictScalarsAdj f₂₃).unit.app _) ≫
        (restrictScalarsComp f₁₂ f₂₃).inv.app _ := by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Category.assoc, Category.id_comp, Category.comp_id,
    Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) :
    (extendScalarsComp f₁₂ f₂₃).hom.app M ((1 : R₃) ⊗ₜ m) =
      (1 : R₃) ⊗ₜ[R₂,f₂₃] ((1 : R₂) ⊗ₜ[R₁,f₁₂] m) := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply, homEquiv_extendScalarsComp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma extendScalars_assoc :
    (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ =
        (extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).hom ≫
          Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).hom ≫
            (Functor.associator _ _ _).inv := by
  ext M m
  have h₁ := extendScalarsComp_hom_app_one_tmul (f₂₃.comp f₁₂) f₃₄ M m
  have h₂ := extendScalarsComp_hom_app_one_tmul f₁₂ (f₃₄.comp f₂₃) M m
  have h₃ := extendScalarsComp_hom_app_one_tmul f₂₃ f₃₄
  have h₄ := extendScalarsComp_hom_app_one_tmul f₁₂ f₂₃ M m
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [h₁]
  erw [h₂]
  rw [h₃, ExtendScalars.map_tmul, h₄]

set_option backward.isDefEq.respectTransparency false in
/-- The associativity compatibility for the extension of scalars, in the exact form
that is needed in the definition `CommRingCat.moduleCatExtendScalarsPseudofunctor`
in the file `Mathlib/Algebra/Category/ModuleCat/Pseudofunctor.lean` -/
lemma extendScalars_assoc' :
    (extendScalarsComp (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (extendScalarsComp f₁₂ f₂₃).hom _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (extendScalarsComp f₂₃ f₃₄).inv ≫
            (extendScalarsComp f₁₂ (f₃₄.comp f₂₃)).inv = 𝟙 _ := by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma extendScalars_id_comp :
    (extendScalarsComp (RingHom.id R₁) f₁₂).hom ≫ Functor.whiskerRight (extendScalarsId R₁).hom _ ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul (RingHom.id R₁) f₁₂ M m]
  rw [ExtendScalars.map_tmul]
  erw [extendScalarsId_hom_app_one_tmul]
  rfl

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid a strange error. -/
@[reassoc]
lemma extendScalars_comp_id :
    (extendScalarsComp f₁₂ (RingHom.id R₂)).hom ≫ Functor.whiskerLeft _ (extendScalarsId R₂).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul f₁₂ (RingHom.id R₂) M m,
    extendScalarsId_hom_app_one_tmul]
  rfl

end

end ModuleCat

end ModuleCat
