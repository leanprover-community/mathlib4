/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.RingTheory.TensorProduct.Basic

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

## List of notations
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f] m` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`.
-/

namespace Module

/-- `Module.RestrictScalars f M` is the module with scalar multiplication given by `f c • x`
for `c : R`, `x : M`.

It is intended as a more type-safe alternative to `Module.compHom`.

This is a type synonym to ensure we don't accidentally put the wrong module structure on `M`,
especially if we have `f : R →+* R` which is not the identity.
-/
@[ext]
structure RestrictScalars {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (M : Type*) where into ::
  out : M

namespace RestrictScalars

variable {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S} {M : Type*}

variable (f) in
lemma into_injective : Function.Injective (into : M → RestrictScalars f M) :=
  fun _ _ h => congr_arg out h

variable (f) in
lemma out_injective : Function.Injective (out : RestrictScalars f M → M) :=
  fun _ _ h => RestrictScalars.ext h

/-! Copy over the instances from the underlying type to `RestrictScalars`. -/

instance [Add M] : Add (RestrictScalars f M) where
  add x y := into (out x + out y)

instance [Zero M] : Zero (RestrictScalars f M) where
  zero := into 0

instance [Neg M] : Neg (RestrictScalars f M) where
  neg x := into (- out x)

instance [Sub M] : Sub (RestrictScalars f M) where
  sub x y := into (out x - out y)

instance {X : Type*} [SMul X M] : SMul X (RestrictScalars f M) where
  smul x y := into (x • out y)

instance [AddCommMonoid M] : AddCommMonoid (RestrictScalars f M) :=
  (out_injective f).addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddCommGroup M] : AddCommGroup (RestrictScalars f M) :=
  (out_injective f).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ _ => rfl)

variable (f M) in
/-- Bundle `out` into an additive isomorphism. -/
def outAddEquiv [Add M] : RestrictScalars f M ≃+ M where
  toFun := out
  invFun := into
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! The `Module` instance itself. -/

instance [AddCommMonoid M] [Module S M] : Module R (RestrictScalars f M) :=
  let _ := Module.compHom M f
  (out_injective f).module R (outAddEquiv f M : _ →+ M) (fun _ _ => rfl)

/-! Moving maps back and forth from `RestrictScalars`. -/

variable {N : Type*} [AddCommMonoid M] [AddCommMonoid N]

/-- `out` as a semilinear map. -/
@[simps]
def outₛₗ [Module S M] : RestrictScalars f M →ₛₗ[f] M where
  toFun := out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composing with `into` turns a semilinear map into a linear map. -/
@[simps]
def mapInto [Module R M] [Module S N] (g : M →ₛₗ[f] N) : M →ₗ[R] RestrictScalars f N where
  toFun x := into (g x)
  map_add' x y := congr_arg into (map_add g x y)
  map_smul' c x := congr_arg into (map_smulₛₗ g c x)

/-- Restrict the domain and codomain of a linear map. -/
@[simps!]
def map [Module S M] [Module S N] (g : M →ₗ[S] N) :
    RestrictScalars f M →ₗ[R] RestrictScalars f N :=
  mapInto (g.comp outₛₗ)

/-- Restricting by the identity map gives back an isomorphic module. -/
@[simps! apply symm_apply]
def idEquiv [Module R M] : RestrictScalars (RingHom.id R) M ≃ₗ[R] M where
  __ := outₛₗ
  invFun := into
  left_inv _ := rfl
  right_inv _ := rfl

end RestrictScalars

end Module

open CategoryTheory Limits

namespace ModuleCat

universe v u₁ u₂ u₃ w

namespace RestrictScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
variable (M : ModuleCat.{v} S)

open Module.RestrictScalars

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`Module.compHom`). This is called restriction of scalars. -/
abbrev obj' : ModuleCat R :=
  of R (Module.RestrictScalars f M)

/-- Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : ModuleCat.{v} S} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
  ofHom <| map g.hom

end RestrictScalars

/-- The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrictScalars {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj := RestrictScalars.obj' f
  map := RestrictScalars.map' f

namespace restrictScalars

abbrev into {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{v} S}
    (x : M) : (restrictScalars f).obj M := Module.RestrictScalars.into x

lemma into_injective {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} : Function.Injective (into f : M → _) :=
  Module.RestrictScalars.into_injective _

@[simp] lemma into_add {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} (x y : M) : into f (x + y) = into f x + into f y := rfl

/-- Variant of `into_add` with `ModuleCat.of`. -/
@[simp] lemma into_add' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : Type v} [AddCommGroup M] [Module S M] (x y : M) :
    into (M := ModuleCat.of S M) f (x + y) = into f x + into f y := rfl

@[simp] lemma into_zero {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} : into f (0 : M) = 0 := rfl

/-- Variant of `into_zero` with `ModuleCat.of`. -/
@[simp] lemma into_zero' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : Type v} [AddCommGroup M] [Module S M] :
    into (M := ModuleCat.of S M) f 0 = 0 := rfl

/-- Forget that `M` is equipped with the restriction of scalar multiplication. -/
def out {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{v} S} :
    (restrictScalars f).obj M →ₛₗ[f] M :=
  Module.RestrictScalars.outₛₗ

lemma out_injective {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} : Function.Injective (out f : _ → M) :=
  Module.RestrictScalars.out_injective _

@[simp] lemma out_add {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} (x y : (restrictScalars f).obj M) :
    out f (x + y) = out f x + out f y := rfl

@[simp] lemma out_into {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (x : M) : out f (into f x) = x := rfl

@[ext] lemma obj_ext {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (x y : (restrictScalars f).obj M) (h : out _ x = out _ y) : x = y :=
  Module.RestrictScalars.out_injective _ h

@[ext high] lemma hom_ext {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} {N : ModuleCat.{v} R} (g g' : (restrictScalars f).obj M ⟶ N)
    (h : g ∘ into _ = g' ∘ into _) : g = g' := by
  ext ⟨x⟩
  exact congr_fun h x

@[ext high] lemma map_ext {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} {N : Type*} [AddCommMonoid N] [Module R N]
    (g g' : (restrictScalars f).obj M →ₗ[R] N) (h : g ∘ into _ = g' ∘ into _) : g = g' := by
  ext ⟨x⟩
  exact congr_fun h x

@[simp]
theorem coe_map {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') :
    ((restrictScalars f).map g : _ → _) = into f ∘ g ∘ out f :=
  rfl

@[simp]
theorem map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) :
    (restrictScalars f).map g (into f x) = into f (g x) :=
  rfl

@[simp] lemma into_eq_into_iff {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f : R →+* S}
    {M : ModuleCat.{v} S} {x y : M} : into f x = into f y ↔ x = y :=
  (Module.RestrictScalars.into_injective _).eq_iff

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).Faithful where
  map_injective h := by
    ext x
    simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) (into f x)

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{v} f).PreservesMonomorphisms where
  preserves _ h := by
    rw [mono_iff_injective] at h ⊢
    exact into_injective.comp (h.comp out_injective)

@[simp]
theorem smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (restrictScalars f).obj M) :
    r • m = into f (f r • out f m) :=
  rfl

theorem smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) :
    r • (into f m) = into f (f r • m) :=
  rfl

end restrictScalars

suppress_compilation

open restrictScalars

/-- Semilinear maps `M →ₛₗ[f] N` identify to
morphisms `M ⟶ (ModuleCat.restrictScalars f).obj N`. -/
@[simps]
def semilinearMapAddEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    (M →ₛₗ[f] N) ≃+ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  toFun g := ofHom <| Module.RestrictScalars.mapInto g
  invFun g :=
    { toFun x := out f (g x)
      map_add' _ _ := by simp
      map_smul' _ _ := by simp }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section

variable {R : Type u₁} [Ring R] (f : R →+* R)

/-- For a `R`-module `M`, the restriction of scalars of `M` by the identity morphisms identifies
to `M`. -/
@[simps!]
def restrictScalarsId'App (hf : f = RingHom.id R) (M : ModuleCat R) :
    (restrictScalars f).obj M ≅ M :=
  LinearEquiv.toModuleIso <|
    AddEquiv.toLinearEquiv
      { toFun := out f
        invFun := into f
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl }
      (fun r x ↦ by simp [hf])

variable (hf : f = RingHom.id R)

@[simp] lemma restrictScalarsId'App_hom_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).hom (into f x) = x :=
  rfl

@[simp] lemma restrictScalarsId'App_inv_apply (M : ModuleCat R) (x : M) :
    (restrictScalarsId'App f hf M).inv x = (into f x) :=
  rfl

/-- The restriction of scalars by a ring morphism that is the identity identify to the
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

/-- The restriction of scalars by the identity morphisms identify to the
identity functor. -/
abbrev restrictScalarsId := restrictScalarsId'.{v} (RingHom.id R) rfl

end

section

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Ring R₁] [Ring R₂] [Ring R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃)

/-- For each `R₃`-module `M`, restriction of scalars of `M` by a composition of ring morphisms
identifies to successively restricting scalars. -/
@[simps!]
def restrictScalarsComp'App (hgf : gf = g.comp f) (M : ModuleCat R₃) :
    (restrictScalars gf).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((restrictScalars gf).obj M))
    (M₂ := ↑((restrictScalars f).obj ((restrictScalars g).obj M)))
    { toFun x := into _ (into _ (out _ x))
      invFun x := into _ (out _ (out _ x))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
    (fun r x ↦ by simp [hgf])).toModuleIso

variable (hgf : gf = g.comp f)

@[simp] lemma restrictScalarsComp'App_hom_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).hom (into _ x) = into _ (into _ x) :=
  rfl

@[simp] lemma restrictScalarsComp'App_inv_apply (M : ModuleCat R₃) (x : M) :
    (restrictScalarsComp'App f g gf hgf M).inv (into _ (into _ x)) = into _ x :=
  rfl

/-- The restriction of scalars by a composition of ring morphisms identify to the
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

/-- The restriction of scalars by a composition of ring morphisms identify to the
composition of the restriction of scalars functors. -/
abbrev restrictScalarsComp := restrictScalarsComp'.{v} f g _ rfl

end

/-- The equivalence of categories `ModuleCat S ≌ ModuleCat R` induced by `e : R ≃+* S`. -/
def restrictScalarsEquivalenceOfRingEquiv {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    ModuleCat S ≌ ModuleCat R where
  functor := ModuleCat.restrictScalars e.toRingHom
  inverse := ModuleCat.restrictScalars e.symm
  unitIso := NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := M)
    (X₂ := (restrictScalars e.symm.toRingHom).obj ((restrictScalars e.toRingHom).obj M))
    { toFun x := into _ (into _ x)
      invFun x := out _ (out _ x)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := by simp }) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := (restrictScalars e.toRingHom).obj ((restrictScalars e.symm.toRingHom).obj M))
    (X₂ := M)
    { toFun x := out _ (out _ x)
      invFun x := into _ (into _ x)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r _ := by simp }) (by intros; rfl)
  functor_unitIso_comp := by intros; rfl

instance restrictScalars_isEquivalence_of_ringEquiv {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
  (restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

section ModuleCat.Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
-- without this notation, one need to work with `s : (restrictScalars f).obj ⟨S⟩`.
scoped[ChangeOfRings]
  notation s "⊗ₜ[" R "," f "]" m => @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ f) _ s m

end Unbundled

namespace ExtendScalars

open ChangeOfRings

variable (M : ModuleCat.{v} R)

instance (priority := 100) sMulCommClass_mk {R : Type u₁} {S : Type u₂} [Ring R] [CommRing S]
    (f : R →+* S) (M : Type v) [I : AddCommGroup M] [Module S M] :
    haveI : SMul R M := (Module.compHom M f).toSMul
    SMulCommClass R S M :=
  @SMulCommClass.mk R S M (_) _
   fun r s m => (by simp [← mul_smul, mul_comm] : f r • s • m = s • f r • m)

/-- Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def obj' : ModuleCat S :=
  let _ := Module.compHom S f
  of _ (TensorProduct R S M)

/-- Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : ModuleCat.{v} R} (l : M1 ⟶ M2) : obj' f M1 ⟶ obj' f M2 :=
  ofHom (@LinearMap.baseChange R S M1 M2 _ _ ((algebraMap S _).comp f).toAlgebra _ _ _ _ l.hom)

theorem map'_id {M : ModuleCat.{v} R} : map' f (𝟙 M) = 𝟙 _ := by
  ext x
  simp [map']

theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ := by
  ext x
  dsimp only [map']
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]

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

open ChangeOfRings

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

@[simp]
protected theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s' ⊗ₜ[R,f] m : (extendScalars f).obj M) = (s * s')⊗ₜ[R,f]m :=
  rfl

@[simp]
theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (extendScalars f).map g (s⊗ₜ[R,f]m) = s⊗ₜ[R,f]g m :=
  rfl

end ExtendScalars

namespace CoextendScalars

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

section Unbundled

variable (M : Type v) [AddCommMonoid M] [Module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
-- Porting note: this seems to cause problems related to lack of reducibility
-- local notation "S'" => (restrictScalars f).obj ⟨S⟩

/-- Given an `R`-module M, consider Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
 means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
 -/
instance hasSMul : SMul S <| (restrictScalars f).obj (of _ S) →ₗ[R] M where
  smul s g :=
    { toFun s' := g (into _ ((out _ s') * s : S))
      map_add' x y := by dsimp; simp [add_mul, map_add]
      map_smul' r t := by
        dsimp
        rw [out_into, ← smul_eq_mul (a := f r), smul_mul_assoc, ← restrictScalars.smul_def',
            map_smul] }

@[simp]
theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
    (s • g) (into _ s') = g (into _ (s' * s)) :=
  rfl

instance mulAction : MulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.hasSMul f _ with
    one_smul _ := by ext; simp
    mul_smul _ _ _ := by ext; simp [mul_assoc] }

instance distribMulAction : DistribMulAction S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.mulAction f _ with
    smul_add s g h := by ext; simp
    smul_zero _ := by ext; simp }

/-- `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
 -/
instance isModule : Module S <| (restrictScalars f).obj (of _ S) →ₗ[R] M :=
  { CoextendScalars.distribMulAction f _ with
    add_smul _ _ _ := by ext; simp [mul_add]
    zero_smul g := by ext; simp }

end Unbundled

variable (M : ModuleCat.{v} R)

/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with
scalar multiplication defined by `s • l := x ↦ l (x • s)`-/
def obj' : ModuleCat S :=
  of _ ((restrictScalars f).obj (of _ S) →ₗ[R] M)

instance : CoeFun (obj' f M) fun _ => ((restrictScalars f).obj (of _ S)) → M where
  coe (f : ((restrictScalars f).obj (of _ S) →ₗ[R] M)) := f

/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h`-/
@[simps]
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

instance (M : ModuleCat R) : CoeFun ((coextendScalars f).obj M) fun _ =>
    ((restrictScalars f).obj (of _ S)) → M :=
  inferInstanceAs <| CoeFun (CoextendScalars.obj' f M) _

@[ext] lemma ext (M : ModuleCat R) (g g' : (coextendScalars f).obj M)
    (h : g ∘ into _ = g' ∘ into _) : g = g' := restrictScalars.map_ext _ _ _ h

theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
    (s • g) (into _ s') = g (into _ (s' * s)) :=
  rfl

@[simp]
theorem map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (coextendScalars f).map g x (into _ s) = g (x (into _ s)) :=
  rfl

end CoextendScalars

namespace RestrictionCoextensionAdj

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- Given `R`-module X and `S`-module Y, any `g : (restrictScalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextendScalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
-/
def HomEquiv.fromRestriction {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) : Y ⟶ (coextendScalars f).obj X :=
  ofHom
  { toFun y :=
      { toFun s := g (into _ (out _ s • y))
        map_add' := fun ⟨s1⟩ ⟨s2⟩ => by simp [add_smul]
        map_smul' := fun r ⟨s⟩ => by
          dsimp
          rw [← g.hom.map_smul, restrictScalars.smul_def', restrictScalars.smul_def',
            ← smul_assoc, smul_eq_mul, out_into, out_into, smul_eq_mul] }
    map_add' _ _ := by
        ext
        simp [smul_add, map_add]
    map_smul' s y := by
        ext
        dsimp
        rw [← smul_assoc, smul_eq_mul]
        rfl }

/-- This should be autogenerated by `@[simps]` but we need to give `s` the correct type here. -/
@[simp] lemma HomEquiv.fromRestriction_hom_apply_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : (restrictScalars f).obj Y ⟶ X) (y) (s) :
    (HomEquiv.fromRestriction f g).hom y s = g (into _ (out _ s • y)) := rfl

/-- Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextendScalars f).obj X`
corresponds to `(restrictScalars f).obj Y ⟶ X` by `y ↦ g y 1`
-/
def HomEquiv.toRestriction {X Y} (g : Y ⟶ (coextendScalars f).obj X) :
    (restrictScalars f).obj Y ⟶ X :=
  ofHom
  { toFun y := g (out _ y) (into _ 1)
    map_add' x y := by
      dsimp
      rw [map_add, map_add, LinearMap.add_apply]
    map_smul' := by
      rintro r ⟨y⟩
      dsimp
      rw [restrictScalars.smul_def, out_into, map_smul, CoextendScalars.smul_apply, one_mul,
        ← map_smul, restrictScalars.smul_def', smul_eq_mul, mul_one, out_into] }

/-- This should be autogenerated by `@[simps]` but we need to give `s` the correct type here. -/
@[simp] lemma HomEquiv.toRestriction_hom_apply {X : ModuleCat R} {Y : ModuleCat S}
    (g : Y ⟶ (coextendScalars f).obj X) (y) :
    (HomEquiv.toRestriction f g).hom y = g (out _ y) (into _ 1) := rfl

-- Porting note: add to address timeout in unit'
/-- Auxiliary definition for `unit'` -/
def app' (Y : ModuleCat S) : Y →ₗ[S] (restrictScalars f ⋙ coextendScalars f).obj Y :=
  { toFun := fun y : Y =>
      { toFun s := into _ (out _ s • y)
        map_add' _ _ := by simp [add_smul]
        map_smul' := by
          rintro r ⟨_⟩
          dsimp only [restrictScalars.smul_def, RingHom.id_apply, out_into, into_eq_into_iff]
          rw [out_into, smul_def', out_into, smul_assoc] }
    map_add' y1 y2 :=
      LinearMap.ext <| by
        rintro ⟨s⟩
        rw [LinearMap.add_apply]
        simp [smul_add]
    map_smul' s y := LinearMap.ext <| by
      rintro ⟨t⟩
      dsimp
      rw [CoextendScalars.smul_apply, ← smul_eq_mul, ← smul_assoc, out_into, LinearMap.coe_mk,
        AddHom.coe_mk, out_into] }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps]
protected def unit' : 𝟭 (ModuleCat S) ⟶ restrictScalars f ⋙ coextendScalars f where
  app Y := ofHom (app' f Y)
  naturality Y Y' g := by dsimp; ext; simp [CoextendScalars.map_apply, app']

/-- The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps]
protected def counit' : coextendScalars f ⋙ restrictScalars f ⟶ 𝟭 (ModuleCat R) where
  app X := ofHom
    { toFun g := out _ g (into _ 1)
      map_add' x1 x2 := by
        dsimp
        rw [out_add, LinearMap.add_apply]
      map_smul' := fun r g => by
        dsimp
        rw [restrictScalars.smul_def, out_into, CoextendScalars.smul_apply, one_mul,
            ← LinearMap.map_smul, restrictScalars.smul_def', smul_eq_mul, mul_one] }

end RestrictionCoextensionAdj

-- Porting note: very fiddly universes
/-- Restriction of scalars is left adjoint to coextension of scalars. -/
-- @[simps] Porting note: not in normal form and not used
def restrictCoextendScalarsAdj {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    restrictScalars.{max v u₂,u₁,u₂} f ⊣ coextendScalars f :=
  Adjunction.mk' {
    homEquiv := fun X Y ↦
      { toFun := RestrictionCoextensionAdj.HomEquiv.fromRestriction.{u₁,u₂,v} f
        invFun := RestrictionCoextensionAdj.HomEquiv.toRestriction.{u₁,u₂,v} f
        left_inv := fun g => by ext; dsimp; rw [out_into, one_smul]
        right_inv := fun g => by
          ext
          -- Porting note (https://github.com/leanprover-community/mathlib4/pull/10745): once just simp
          dsimp
          rw [map_smul, CoextendScalars.smul_apply', one_mul, out_into] }
    unit := RestrictionCoextensionAdj.unit'.{u₁,u₂,v} f
    counit := RestrictionCoextensionAdj.counit'.{u₁,u₂,v} f
    homEquiv_unit := hom_ext <| LinearMap.ext fun _ => rfl
    homEquiv_counit := fun {X Y g} => by
      ext
      simp [RestrictionCoextensionAdj.counit'] }

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (restrictScalars.{max u₂ w} f).IsLeftAdjoint  :=
  (restrictCoextendScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (coextendScalars.{u₁, u₂, max u₂ w} f).IsRightAdjoint  :=
  (restrictCoextendScalarsAdj f).isRightAdjoint

namespace ExtendRestrictScalarsAdj

open ChangeOfRings

open TensorProduct

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y and a map `g : (extendScalars f).obj X ⟶ Y`, i.e. `S`-linear
map `S ⨂ X → Y`, there is a `X ⟶ (restrictScalars f).obj Y`, i.e. `R`-linear map `X ⟶ Y` by
`x ↦ g (1 ⊗ x)`.
-/
@[simps hom_apply]
def HomEquiv.toRestrictScalars {X Y} (g : (extendScalars f).obj X ⟶ Y) :
    X ⟶ (restrictScalars f).obj Y :=
  ofHom
  { toFun := fun x => into _ <| g <| (1 : S)⊗ₜ[R,f]x
    map_add' := fun _ _ => by
      let _ : Module R S := Module.compHom S f
      dsimp
      rw [tmul_add, map_add, into_add]
    map_smul' := fun r s => by
      letI : Module R S := Module.compHom S f
      letI : Module R Y := Module.compHom Y f
      dsimp
      rw [tmul_smul, restrictScalars.smul_def', ← map_smul]
      congr }

-- Porting note: forced to break apart fromExtendScalars due to timeouts
/--
The map `S → X →ₗ[R] Y` given by `fun s x => s • (g x)`
-/
@[simps]
def HomEquiv.evalAt {X : ModuleCat R} {Y : ModuleCat S} (s : S)
    (g : X ⟶ (restrictScalars f).obj Y) : have : Module R Y := Module.compHom Y f
    X →ₗ[R] Y :=
  @LinearMap.mk _ _ _ _ (RingHom.id R) X Y _ _ _ (_)
    { toFun x := s • out _ (g x)
      map_add' := by
        intros
        dsimp only
        rw [map_add, out_add, smul_add] }
    (by
      intros r x
      rw [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply,
        LinearMap.map_smul, smul_comm r s, restrictScalars.smul_def, out_into]
      -- This does not look defeq because we have the competing instance `Module.compHom Y f`,
      -- but it is indeed equal.
      rfl )

/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restrictScalars f).obj Y`, i.e `R`-linear map
`X ⟶ Y`, there is a map `(extend_scalars f).obj X ⟶ Y`, i.e `S`-linear map `S ⨂ X → Y` by
`s ⊗ x ↦ s • g x`.
-/
@[simps hom_apply]
def HomEquiv.fromExtendScalars {X Y} (g : X ⟶ (restrictScalars f).obj Y) :
    (extendScalars f).obj X ⟶ Y := by
  letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
  refine ofHom {toFun := fun z => TensorProduct.lift ?_ z, map_add' := ?_, map_smul' := ?_}
  · refine
    {toFun := fun s => HomEquiv.evalAt f s g, map_add' := fun (s₁ s₂ : S) => ?_,
      map_smul' := fun (r : R) (s : S) => ?_}
    · ext
      dsimp only [m2, evalAt_apply, LinearMap.add_apply]
      rw [← add_smul]
    · ext x
      apply mul_smul (f r) s (out _ (g x))
  · intros z₁ z₂
    change lift _ (z₁ + z₂) = lift _ z₁ + lift _ z₂
    rw [map_add]
  · intro s z
    change lift _ (s • z) = s • lift _ z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x => simp [mul_smul]
    | add _ _ ih1 ih2 => rw [smul_add, map_add, ih1, ih2, map_add, smul_add]

/-- Given `R`-module X and `S`-module Y, `S`-linear linear maps `(extendScalars f).obj X ⟶ Y`
bijectively correspond to `R`-linear maps `X ⟶ (restrictScalars f).obj Y`.
-/
@[simps symm_apply]
def homEquiv {X Y} :
    ((extendScalars f).obj X ⟶ Y) ≃ (X ⟶ (restrictScalars.{max v u₂,u₁,u₂} f).obj Y) where
  toFun := HomEquiv.toRestrictScalars.{u₁,u₂,v} f
  invFun := HomEquiv.fromExtendScalars.{u₁,u₂,v} f
  left_inv g := by
    letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
    apply hom_ext
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x s =>
      erw [TensorProduct.lift.tmul]
      dsimp
      erw [← LinearMap.map_smul, ExtendScalars.smul_tmul, mul_one x]
    | add _ _ ih1 ih2 => rw [map_add, map_add, ih1, ih2]
  right_inv g := by
    letI m1 : Module R S := Module.compHom S f; letI m2 : Module R Y := Module.compHom Y f
    ext x
    -- This needs to be `erw` because of some unfolding in `fromExtendScalars`
    erw [HomEquiv.toRestrictScalars_hom_apply, HomEquiv.fromExtendScalars_hom_apply]
    simp

/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
-- @[simps] Porting note: not in normal form and not used
def Unit.map {X} : X ⟶ (extendScalars f ⋙ restrictScalars f).obj X :=
  ofHom
  { toFun := fun x => into _ <| (1 : S)⊗ₜ[R,f]x
    map_add' x x' := by
      let m1 : Module R S := Module.compHom S f
      dsimp
      rw [TensorProduct.tmul_add, into_add]
    map_smul' := fun r x => by
      letI m1 : Module R S := Module.compHom S f
      -- Porting note: used to be rfl
      simp only [tmul_smul]
      rfl }

/--
The natural transformation from identity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
@[simps]
def unit : 𝟭 (ModuleCat R) ⟶ extendScalars f ⋙ restrictScalars.{max v u₂,u₁,u₂} f where
  app _ := Unit.map.{u₁,u₂,v} f

/-- For any `S`-module Y, there is a natural `R`-linear map from `S ⨂ Y` to `Y` by
`s ⊗ y ↦ s • y` -/
@[simps hom_apply]
def Counit.map {Y} : (restrictScalars f ⋙ extendScalars f).obj Y ⟶ Y :=
  ofHom
  { toFun :=
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      TensorProduct.lift
      { toFun s :=
        { toFun y := s • out _ y,
          map_add' y₁ y₂ := by
            simp only [out_add, smul_add]
          map_smul' r y := by
            dsimp only [restrictScalars.smul_def, AddHom.toFun_eq_coe, AddHom.coe_mk, out_into,
              RingHom.id_apply]
            rw [← mul_smul, mul_comm, mul_smul]
            rfl },
        map_add' s₁ s₂ := by
          ext y
          dsimp only [smul_def, AddHom.toFun_eq_coe, AddHom.coe_mk, out_into, RingHom.id_apply,
            id_eq, eq_mpr_eq_cast, LinearMap.coe_mk, Function.comp_apply, LinearMap.add_apply]
          rw [add_smul]
        map_smul' r s := by
          ext y
          dsimp only [restrictScalars.smul_def, AddHom.toFun_eq_coe, AddHom.coe_mk, out_into,
            RingHom.id_apply, id_eq, eq_mpr_eq_cast, LinearMap.coe_mk, LinearMap.add_apply,
            LinearMap.smul_apply]
          change (f r • s) • y = (f r) • s • y
          rw [smul_eq_mul, mul_smul] }
    map_add' := fun _ _ => map_add _ _ _
    map_smul' := fun s z => by
      letI m1 : Module R S := Module.compHom S f
      letI m2 : Module R Y := Module.compHom Y f
      dsimp only [RingHom.id_apply, restrictScalars.smul_def, out_into, id_eq, eq_mpr_eq_cast,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        cast_eq]
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s' y =>
        dsimp only [ExtendScalars.smul_tmul, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
        rw [mul_smul]
      | add _ _ ih1 ih2 => 
        rw [smul_add, map_add, map_add, smul_add, ih1, ih2] }

/-- The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps app]
def counit : restrictScalars.{max v u₂,u₁,u₂} f ⋙ extendScalars f ⟶ 𝟭 (ModuleCat S) where
  app _ := Counit.map.{u₁,u₂,v} f
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
      change s' • g (out _ y) = g (s' • out _ y)
      rw [map_smul]
    | add _ _ ih₁ ih₂ => rw [map_add, map_add]; congr 1
end ExtendRestrictScalarsAdj

/-- Given commutative rings `R, S` and a ring hom `f : R →+* S`, the extension and restriction of
scalars by `f` are adjoint to each other.
-/
-- @[simps] -- Porting note: removed not in normal form and not used
def extendRestrictScalarsAdj {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    extendScalars.{u₁,u₂,max v u₂} f ⊣ restrictScalars.{max v u₂,u₁,u₂} f :=
  Adjunction.mk' {
    homEquiv := fun _ _ ↦ ExtendRestrictScalarsAdj.homEquiv.{v,u₁,u₂} f
    unit := ExtendRestrictScalarsAdj.unit.{v,u₁,u₂} f
    counit := ExtendRestrictScalarsAdj.counit.{v,u₁,u₂} f
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

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (extendScalars.{u₁, u₂, max u₂ w} f).IsLeftAdjoint :=
  (extendRestrictScalarsAdj f).isLeftAdjoint

instance {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S) :
    (restrictScalars.{max u₂ w, u₁, u₂} f).IsRightAdjoint :=
  (extendRestrictScalarsAdj f).isRightAdjoint

/-- Forgetting the scalar multiplication after changing it is the same as forgetting it directly. -/
def restrictScalars_comp_forget₂
    {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    restrictScalars f ⋙ forget₂ (ModuleCat R) AddCommGrp ≅ forget₂ (ModuleCat S) AddCommGrp where
  hom.app M := AddCommGrp.ofHom <| (Module.RestrictScalars.outAddEquiv f M).toAddMonoidHom
  inv.app M := AddCommGrp.ofHom <| (Module.RestrictScalars.outAddEquiv f M).symm.toAddMonoidHom

noncomputable instance preservesLimit_restrictScalars
    {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R →+* S) {J : Type*} [Category J]
    (F : J ⥤ ModuleCat.{v} S) [Small.{v} (F ⋙ forget _).sections] :
    PreservesLimit F (restrictScalars f) :=
  ⟨fun hc => ⟨isLimitOfReflects (forget₂ _ AddCommGrp)
    (IsLimit.mapConeEquiv (restrictScalars_comp_forget₂ f).symm
      (isLimitOfPreserves (forget₂ _ AddCommGrp) hc))⟩⟩

instance preservesColimit_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {J : Type*} [Category J] (F : J ⥤ ModuleCat.{v} S)
    [HasColimit (F ⋙ forget₂ _ AddCommGrp)] :
    PreservesColimit F (ModuleCat.restrictScalars.{v} f) := by
  have : HasColimit ((F ⋙ restrictScalars f) ⋙ forget₂ (ModuleCat R) AddCommGrp) := by
    exact hasColimitOfIso ((Functor.associator F _ _).trans
      (isoWhiskerLeft F (restrictScalars_comp_forget₂ f)))
  apply preservesColimit_of_preserves_colimit_cocone (HasColimit.isColimitColimitCocone F)
  apply isColimitOfReflects (forget₂ _ AddCommGrp)
  apply IsColimit.mapCoconeEquiv (restrictScalars_comp_forget₂ f).symm
  apply isColimitOfPreserves (forget₂ (ModuleCat.{v} S) AddCommGrp.{v})
  exact HasColimit.isColimitColimitCocone F

end ModuleCat

end ModuleCat
