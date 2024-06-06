/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.RingTheory.OreLocalization.Module

#align_import algebra.module.localized_module from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.
The construction is via `OreLocalization` and provided in `RingTheory/OreLocalization/Module`.

## Main definitions

* `IsLocalizedModule` : The characteristic predicate of localized modules.
* `IsLocalizedModule.lift`: The universal property of localized modules.

Also see `RingTheory/Localization/BaseChange` for the characterization of localized modules
as the base change of the module to the localization.

-/

section IsLocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/-- The characteristic predicate for localized module.
`IsLocalizedModule S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`LocalizedModule S M`.
-/
@[mk_iff] class IsLocalizedModule : Prop where
  map_units : ∀ x : S, IsUnit (algebraMap R (Module.End R M') x)
  surj' : ∀ y : M', ∃ x : M × S, x.2 • y = f x.1
  exists_of_eq : ∀ {x₁ x₂}, f x₁ = f x₂ → ∃ c : S, c • x₁ = c • x₂
#align is_localized_module IsLocalizedModule

attribute [nolint docBlame] IsLocalizedModule.map_units IsLocalizedModule.surj'
  IsLocalizedModule.exists_of_eq

-- Porting note: Manually added to make `S` and `f` explicit.
lemma IsLocalizedModule.surj [IsLocalizedModule S f] (y : M') : ∃ x : M × S, x.2 • y = f x.1 :=
  surj' y

-- Porting note: Manually added to make `S` and `f` explicit.
lemma IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} :
    f x₁ = f x₂ ↔ ∃ c : S, c • x₁ = c • x₂ :=
  Iff.intro exists_of_eq fun ⟨c, h⟩ ↦ by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End_isUnit_iff _).mp <| map_units f c).1 h

theorem IsLocalizedModule.of_linearEquiv (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (e ∘ₗ f : M →ₗ[R] M'') where
  map_units s := by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp, Module.End_isUnit_iff, LinearMap.coe_comp, LinearMap.coe_comp,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, EquivLike.comp_bijective, EquivLike.bijective_comp]
    exact (Module.End_isUnit_iff _).mp <| hf.map_units s
  surj' x := by
    obtain ⟨p, h⟩ := hf.surj' (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

variable (M) in
lemma isLocalizedModule_id (R') [CommSemiring R'] [Algebra R R'] [IsLocalization S R'] [Module R' M]
    [IsScalarTower R R' M] : IsLocalizedModule S (.id : M →ₗ[R] M) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj' m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

variable {S} in
theorem isLocalizedModule_iff_isLocalization {A Aₛ} [CommSemiring A] [Algebra R A] [CommSemiring Aₛ]
    [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔
      IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ := by
  rw [isLocalizedModule_iff, isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ ↦ ?_) (forall₂_congr fun _ _ ↦ ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]

instance {A Aₛ} [CommSemiring A] [Algebra R A][CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ]
    [IsScalarTower R A Aₛ] [h : IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr h

lemma isLocalizedModule_iff_isLocalization' (R') [CommSemiring R'] [Algebra R R'] :
    IsLocalizedModule S (Algebra.ofId R R').toLinearMap ↔ IsLocalization S R' := by
  convert isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := R')
  exact (Submonoid.map_id S).symm

instance localizedModuleIsLocalizedModule :
    IsLocalizedModule S (LocalizedModule.mkLinearMap S M) where
  map_units s :=
    ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
        DFunLike.ext _ _ <| LocalizedModule.mul_by_divBy s,
        DFunLike.ext _ _ <| LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
        p.induction_on <| by
          intros
          rfl⟩
  surj' p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      erw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply, Submonoid.coe_subtype,
        LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1
#align localized_module_is_localized_module localizedModuleIsLocalizedModule

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M → M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      -- Porting note: We remove `generalize_proofs h1 h2`.
      rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, ← map_smul,
        Module.End_algebraMap_isUnit_inv_apply_eq_iff', ← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)
#align is_localized_module.from_localized_module' IsLocalizedModule.fromLocalizedModule'

@[simp]
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.from_localized_module'_mk IsLocalizedModule.fromLocalizedModule'_mk

theorem fromLocalizedModule'_add (x y : LocalizedModule S M) :
    fromLocalizedModule' S f (x + y) = fromLocalizedModule' S f x + fromLocalizedModule' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      -- Porting note: We remove `generalize_proofs h1 h2 h3`.
      rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul, ← map_smul,
        ← map_smul, map_add]
      congr 1
      all_goals rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y
#align is_localized_module.from_localized_module'_add IsLocalizedModule.fromLocalizedModule'_add

theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk, LocalizedModule.smul'_mk, fromLocalizedModule'_mk]
      -- Porting note: We remove `generalize_proofs h1`.
      rw [f.map_smul, map_smul])
    x
#align is_localized_module.from_localized_module'_smul IsLocalizedModule.fromLocalizedModule'_smul

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]
#align is_localized_module.from_localized_module IsLocalizedModule.fromLocalizedModule

theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.from_localized_module_mk IsLocalizedModule.fromLocalizedModule_mk

theorem fromLocalizedModule.inj : Function.Injective <| fromLocalizedModule S f := fun x y eq1 => by
  induction' x using LocalizedModule.induction_on with a b
  induction' y using LocalizedModule.induction_on with a' b'
  simp only [fromLocalizedModule_mk] at eq1
  -- Porting note: We remove `generalize_proofs h1 h2`.
  rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← LinearMap.map_smul,
    Module.End_algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def,
    Submonoid.smul_def, f.map_smul, f.map_smul, eq1]
#align is_localized_module.from_localized_module.inj IsLocalizedModule.fromLocalizedModule.inj

theorem fromLocalizedModule.surj : Function.Surjective <| fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← eq1,
      Submonoid.smul_def]⟩
#align is_localized_module.from_localized_module.surj IsLocalizedModule.fromLocalizedModule.surj

theorem fromLocalizedModule.bij : Function.Bijective <| fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩
#align is_localized_module.from_localized_module.bij IsLocalizedModule.fromLocalizedModule.bij

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
@[simps!]
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
    Equiv.ofBijective (fromLocalizedModule S f) <| fromLocalizedModule.bij _ _ with }
#align is_localized_module.iso IsLocalizedModule.iso

theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.iso_apply_mk IsLocalizedModule.iso_apply_mk

theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  -- Porting note: We remove `generalize_proofs _ h2`.
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp only [iso_apply, LinearMap.toFun_eq_coe, fromLocalizedModule_mk]
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff', (surj' _).choose_spec]

#align is_localized_module.iso_symm_apply_aux IsLocalizedModule.iso_symm_apply_aux

theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      -- Porting note: We remove `generalize_proofs h1`.
      rw [← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def, Submonoid.smul_def, f.map_smul,
        f.map_smul, ← (surj' _).choose_spec, ← Submonoid.smul_def, ← Submonoid.smul_def, ← mul_smul,
        mul_comm, mul_smul, eq1]
#align is_localized_module.iso_symm_apply' IsLocalizedModule.iso_symm_apply'

theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe, iso_symm_apply']
  exact one_smul _ _
#align is_localized_module.iso_symm_comp IsLocalizedModule.iso_symm_comp

/--
If `M'` is a localized module and `g` is a linear map `M' → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap
#align is_localized_module.lift IsLocalizedModule.lift

theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc, iso_symm_comp, LocalizedModule.lift_comp S g h]
#align is_localized_module.lift_comp IsLocalizedModule.lift_comp

@[simp]
theorem lift_apply (g : M →ₗ[R] M'') (h) (x) :
    lift S f g h (f x) = g x := LinearMap.congr_fun (lift_comp S f g h) x

theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : M' →ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap), LinearMap.comp_assoc,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]
  rw [LinearMap.comp_assoc, ← hl]
  congr 1
  ext x
  rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe, iso_apply,
    fromLocalizedModule'_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, OneMemClass.coe_one,
    one_smul]
#align is_localized_module.lift_unique IsLocalizedModule.lift_unique

/-- Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following universal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertible and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` such that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
theorem is_universal :
    ∀ (g : M →ₗ[R] M'') (_ : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)),
      ∃! l : M' →ₗ[R] M'', l.comp f = g :=
  fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩
#align is_localized_module.is_universal IsLocalizedModule.is_universal

theorem ringHom_ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  rfl
#align is_localized_module.ring_hom_ext IsLocalizedModule.ringHom_ext

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)
#align is_localized_module.linear_equiv IsLocalizedModule.linearEquiv

variable {S}

theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective
#align is_localized_module.smul_injective IsLocalizedModule.smul_injective

theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff
#align is_localized_module.smul_inj IsLocalizedModule.smul_inj

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)
#align is_localized_module.mk' IsLocalizedModule.mk'

theorem mk'_smul (r : R) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  rw [← LocalizedModule.smul'_mk, LinearMap.map_smul]
#align is_localized_module.mk'_smul IsLocalizedModule.mk'_smul

theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  rw [← map_add, LocalizedModule.mk_add_mk]
#align is_localized_module.mk'_add_mk' IsLocalizedModule.mk'_add_mk'

@[simp]
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]
#align is_localized_module.mk'_zero IsLocalizedModule.mk'_zero

variable (S)

@[simp]
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, Submonoid.coe_one,
    one_smul]
#align is_localized_module.mk'_one IsLocalizedModule.mk'_one

variable {S}

@[simp]
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  rw [LocalizedModule.mk_cancel, ← mk'_one S f, fromLocalizedModule_mk,
    Module.End_algebraMap_isUnit_inv_apply_eq_iff, OneMemClass.coe_one, mk'_one, one_smul]
#align is_localized_module.mk'_cancel IsLocalizedModule.mk'_cancel

@[simp]
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]
#align is_localized_module.mk'_cancel' IsLocalizedModule.mk'_cancel'

@[simp]
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]
#align is_localized_module.mk'_cancel_left IsLocalizedModule.mk'_cancel_left

@[simp]
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]
#align is_localized_module.mk'_cancel_right IsLocalizedModule.mk'_cancel_right

theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk', ← smul_add, mk'_cancel_left]
#align is_localized_module.mk'_add IsLocalizedModule.mk'_add

theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff, LocalizedModule.mk_eq]
  simp_rw [eq_comm]
#align is_localized_module.mk'_eq_mk'_iff IsLocalizedModule.mk'_eq_mk'_iff

theorem mk'_neg {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) : mk' f (-m) s = -mk' f m s := by
  delta mk'
  rw [LocalizedModule.mk_neg, map_neg]
#align is_localized_module.mk'_neg IsLocalizedModule.mk'_neg

theorem mk'_sub {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]
#align is_localized_module.mk'_sub IsLocalizedModule.mk'_sub

theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]
#align is_localized_module.mk'_sub_mk' IsLocalizedModule.mk'_sub_mk'

theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [Semiring M] [Semiring M'] [Module R M]
    [Algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  apply (Module.End_algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]
#align is_localized_module.mk'_mul_mk'_of_map_mul IsLocalizedModule.mk'_mul_mk'_of_map_mul

theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M →ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap f.map_mul m₁ m₂ s₁ s₂
#align is_localized_module.mk'_mul_mk' IsLocalizedModule.mk'_mul_mk'

variable {f}

/-- Porting note (#10618): simp can prove this
@[simp] -/
theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]
#align is_localized_module.mk'_eq_iff IsLocalizedModule.mk'_eq_iff

@[simp]
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]
#align is_localized_module.mk'_eq_zero IsLocalizedModule.mk'_eq_zero

variable (f)

theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]
#align is_localized_module.mk'_eq_zero' IsLocalizedModule.mk'_eq_zero'

theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm, mk'_eq_iff, Submonoid.smul_def, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, LocalizedModule.mkLinearMap_apply]
#align is_localized_module.mk_eq_mk' IsLocalizedModule.mk_eq_mk'

variable (A) in
lemma mk'_smul_mk' (x : R) (m : M) (s t : S) :
    IsLocalization.mk' A x s • mk' f m t = mk' f (x • m) (s * t) := by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

variable (S)

theorem eq_zero_iff {m : M} : f m = 0 ↔ ∃ s' : S, s' • m = 0 :=
  (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)
#align is_localized_module.eq_zero_iff IsLocalizedModule.eq_zero_iff

theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S → M') := by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩
#align is_localized_module.mk'_surjective IsLocalizedModule.mk'_surjective

variable {N N'} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
variable (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[R] Nₛ`. -/
noncomputable
def map : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[R] N') where
  toFun h := lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ringHom_ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ringHom_ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp,
      LinearMap.comp_smul, RingHom.id_apply]

lemma map_comp (h : M →ₗ[R] N) : (map S f g h) ∘ₗ f = g ∘ₗ h :=
  lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]
lemma map_apply (h : M →ₗ[R] N) (x) : map S f g h (f x) = g (h x) :=
  lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

section Algebra

theorem mkOfAlgebra {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra R S'] (M : Submonoid R) (f : S →ₐ[R] S') (h₁ : ∀ x ∈ M, IsUnit (algebraMap R S' x))
    (h₂ : ∀ y, ∃ x : S × M, x.2 • y = f x.1) (h₃ : ∀ x, f x = 0 → ∃ m : M, m • x = 0) :
    IsLocalizedModule M f.toLinearMap := by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
      (h₁ m hm).mul_left_cancel <| by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End_isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ : _) * a, ?_⟩
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  · exact h₂
  · intros x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero, ← map_sub, h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id
#align is_localized_module.mk_of_algebra IsLocalizedModule.mkOfAlgebra

end Algebra

end IsLocalizedModule

end IsLocalizedModule
