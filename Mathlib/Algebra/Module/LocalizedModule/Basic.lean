/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.OreLocalization.Module

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r`: the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S`: the localized module by `S`.
* `LocalizedModule.mk`: the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn`: any well defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂`: any well defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk`: in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.

## Future work

 * Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/


namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [Module R M]
variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

section

variable {M S}

/--
If `T` is the localization of `R` at `S`, then `M[S⁻¹]` has a natural `T`-module structure.
This is not an instance as this causes a diamond with the usual action of `R[S⁻¹]` on `M[S⁻¹]`.
-/
@[reducible] noncomputable
def smulOfIsLocalization : SMul T (LocalizedModule S M) where
  smul x p :=
    let a := IsLocalization.sec S x
    liftOn p (fun p ↦ mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf )

attribute [local instance] smulOfIsLocalization

theorem smul_def (x : T) (m : M) (s : S) :
    x • mk m s = mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s) := rfl

theorem mk'_smul_mk (r : R) (m : M) (s s' : S) :
    IsLocalization.mk' T r s • mk m s' = mk (r • m) (s * s') := by
  rw [smul_def, mk_eq]
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp <| IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

variable {T}

private theorem one_smul_aux (p : LocalizedModule S M) : (1 : T) • p = p := by
  induction' p using LocalizedModule.induction_on with m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one, map_one]]
  rw [mk'_smul_mk, one_smul, one_mul]

private theorem mul_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x * y) • p = x • y • p := by
  induction' p using LocalizedModule.induction_on with m s
  rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]

private theorem smul_add_aux (x : T) (p q : LocalizedModule S M) :
    x • (p + q) = x • p + x • q := by
  induction' p using LocalizedModule.induction_on with m s
  induction' q using LocalizedModule.induction_on with n t
  rw [smul_def, smul_def, mk_add_mk, mk_add_mk]
  rw [show x • _ =  IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2, mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here

private theorem smul_zero_aux (x : T) : x • (0 : LocalizedModule S M) = 0 := by
  erw [OreLocalization.zero_def, smul_def, smul_zero, zero_mk, OreLocalization.zero_def]

private theorem add_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x + y) • p = x • p + y • p := by
  induction' p using LocalizedModule.induction_on with m s
  rw [smul_def T x, smul_def T y, mk_add_mk, show (x + y) • _ =  IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y,
      ← IsLocalization.mk'_add, IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here

private theorem zero_smul_aux (p : LocalizedModule S M) : (0 : T) • p = 0 := by
  induction' p using LocalizedModule.induction_on with m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]

/--
If `T` is the localization of `R` at `S`, then `M[S⁻¹]` has a natural `T`-module structure.
This is not an instance as this causes a diamond with the usual action of `R[S⁻¹]` on `M[S⁻¹]`.
-/
@[reducible] noncomputable
def moduleOfIsLocalization : Module T (LocalizedModule S M) where
  smul := (· • ·)
  one_smul := one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

lemma smul_eq_iff_of_mem
    (r : R) (hr : r ∈ S) (x y : LocalizedModule S M) :
    r • x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y := by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk, mk_smul_mk, one_smul, mk_eq, mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul, ← eq1, Submonoid.mk_smul, smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1, mul_comm, mul_smul, Submonoid.mk_smul]
        rfl

lemma eq_zero_of_smul_eq_zero
    (r : R) (hr : r ∈ S) (x : LocalizedModule S M) (hx : r • x = 0) : x = 0 := by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx, smul_zero]

theorem smul'_mul_of_isLocalization {A : Type*} [Semiring A] [Algebra R A]
    (x : T) (p₁ p₂ : LocalizedModule S A) :
    x • p₁ * p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk, smul_def, smul_def, mk_mul_mk, mul_assoc, smul_mul_assoc]

theorem mul_smul'_of_isLocalization {A : Type*} [Semiring A] [Algebra R A]
    (x : T) (p₁ p₂ : LocalizedModule S A) :
    p₁ * x • p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def, mk_mul_mk, mk_mul_mk, smul_def, mul_left_comm, mul_smul_comm]

variable (T)

/--
If `T` is the localization of `R` at `S`, then `M[S⁻¹]` has a natural `T`-algebra structure.
This is not an instance as this causes a diamond with the usual action of `R[S⁻¹]` on `M[S⁻¹]`.
-/
attribute [local instance] moduleOfIsLocalization in
@[reducible] noncomputable
def algebraOfIsLocalization {A : Type*} [Semiring A] [Algebra R A] :
    Algebra T (LocalizedModule S A) :=
  Algebra.ofModule smul'_mul_of_isLocalization mul_smul'_of_isLocalization

attribute [local instance] algebraOfIsLocalization in
/--
If `T` is the localization of `R` at `S`, then `A[S⁻¹]` has a natural `T`-algebra structure.
This is not an instance as this causes a diamond with the usual action of `R[S⁻¹]` on `M[S⁻¹]`.
-/
theorem algebraMap_mk' {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (IsLocalization.mk' T a s) = mk (algebraMap R A a) s := by
  rw [Algebra.algebraMap_eq_smul_one, OreLocalization.one_def]
  change _ • mk _ _ = _
  rw [mk'_smul_mk, Algebra.algebraMap_eq_smul_one, mul_one]

instance : IsScalarTower R T (LocalizedModule S M) where
  smul_assoc r x p := by
    induction' p using LocalizedModule.induction_on with m s
    rw [← IsLocalization.mk'_sec (M := S) T x, IsLocalization.smul_mk', mk'_smul_mk, mk'_smul_mk,
      smul'_mk, mul_smul]

end

end LocalizedModule

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

@[simp]
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

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

theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk, LocalizedModule.smul'_mk, fromLocalizedModule'_mk]
      -- Porting note: We remove `generalize_proofs h1`.
      rw [f.map_smul, map_smul])
    x

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]

theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

theorem fromLocalizedModule.inj : Function.Injective <| fromLocalizedModule S f := fun x y eq1 => by
  induction' x using LocalizedModule.induction_on with a b
  induction' y using LocalizedModule.induction_on with a' b'
  simp only [fromLocalizedModule_mk] at eq1
  -- Porting note: We remove `generalize_proofs h1 h2`.
  rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← LinearMap.map_smul,
    Module.End_algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def,
    Submonoid.smul_def, f.map_smul, f.map_smul, eq1]

theorem fromLocalizedModule.surj : Function.Surjective <| fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← eq1,
      Submonoid.smul_def]⟩

theorem fromLocalizedModule.bij : Function.Bijective <| fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
@[simps!]
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
    Equiv.ofBijective (fromLocalizedModule S f) <| fromLocalizedModule.bij _ _ with }

theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  -- Porting note: We remove `generalize_proofs _ h2`.
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp only [iso_apply, LinearMap.toFun_eq_coe, fromLocalizedModule_mk]
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff', (surj' _).choose_spec]

theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      -- Porting note: We remove `generalize_proofs h1`.
      rw [← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def, Submonoid.smul_def, f.map_smul,
        f.map_smul, ← (surj' _).choose_spec, ← Submonoid.smul_def, ← Submonoid.smul_def, ← mul_smul,
        mul_comm, mul_smul, eq1]

theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe, iso_symm_apply']
  exact one_smul _ _

/--
If `M'` is a localized module and `g` is a linear map `M → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc, iso_symm_comp, LocalizedModule.lift_comp S g h]

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

theorem ringHom_ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  rfl

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)

variable {S}

include f in
theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in
theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)

theorem mk'_smul (r : R) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  rw [← LocalizedModule.smul'_mk, LinearMap.map_smul]

theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  rw [← map_add, LocalizedModule.mk_add_mk]

@[simp]
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

variable (S)

@[simp]
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, Submonoid.coe_one,
    one_smul]

variable {S}

@[simp]
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  rw [LocalizedModule.mk_cancel, ← mk'_one S f, fromLocalizedModule_mk,
    Module.End_algebraMap_isUnit_inv_apply_eq_iff, OneMemClass.coe_one, mk'_one, one_smul]

@[simp]
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]

theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk', ← smul_add, mk'_cancel_left]

theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff, LocalizedModule.mk_eq]
  simp_rw [eq_comm]

theorem mk'_neg {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) : mk' f (-m) s = -mk' f m s := by
  delta mk'
  rw [LocalizedModule.mk_neg, map_neg]

theorem mk'_sub {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]

theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]

theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [Semiring M] [Semiring M'] [Module R M]
    [Algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  apply (Module.End_algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]

theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M →ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂

variable {f}

theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]

variable (f)

theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]

theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm, mk'_eq_iff, Submonoid.smul_def, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, LocalizedModule.mkLinearMap_apply]

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

theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S → M') := by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩

section liftOfLE

variable {M₁ M₂} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (f₁ : M →ₗ[R] M₁) (f₂ : M →ₗ[R] M₂)
variable [IsLocalizedModule S₁ f₁] [IsLocalizedModule S₂ f₂]

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
def liftOfLE : M₁ →ₗ[R] M₂ :=
  lift S₁ f₁ f₂ fun x ↦ map_units f₂ ⟨x.1, h x.2⟩

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
abbrev _root_.LocalizedModule.liftOfLE : LocalizedModule S₁ M →ₗ[R] LocalizedModule S₂ M :=
  IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)

lemma liftOfLE_comp : (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂ := lift_comp ..

@[simp] lemma liftOfLE_apply (x) : liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x := lift_apply ..

/-- The image of `m/s` under `liftOfLE` is `m/s`. -/
@[simp]
lemma liftOfLE_mk' (m : M) (s : S₁) :
    liftOfLE S₁ S₂ h f₁ f₂ (mk' f₁ m s) = mk' f₂ m ⟨s.1, h s.2⟩ := by
  apply ((Module.End_isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE, lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm

instance : IsLocalizedModule S₂ (liftOfLE S₁ S₂ h f₁ f₂) where
  map_units := map_units f₂
  surj' y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intros x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff, Submonoid.mk_smul,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

end liftOfLE

variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
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

@[simp]
lemma map_mk' (h : M →ₗ[R] N) (x) (s : S) :
    map S f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s) := by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s), LocalizedModule.lift_mk]
  rfl

@[simp]
lemma map_id : map S f f (.id ) = .id := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]
theorem map_injective (h : M →ₗ[R] N) (h_inj : Function.Injective h) :
    Function.Injective (map S f g h) := by
  intros x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intros c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]
theorem map_surjective (h : M →ₗ[R] N) (h_surj : Function.Surjective h) :
    Function.Surjective (map S f g h) := by
  intros x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

open LocalizedModule LinearEquiv LinearMap Submonoid

variable (M)

/-- The linear map `(LocalizedModule S M) → (LocalizedModule S M)` from `iso` is the identity. -/
lemma iso_localizedModule_eq_refl : iso S (mkLinearMap S M) = refl R (LocalizedModule S M) := by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj, univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
  exact Eq.symm <| univ (refl R (LocalizedModule S M)) (by simp)

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]

/-- Formula for `IsLocalizedModule.map` when each localized module is a `LocalizedModule`.-/
lemma map_LocalizedModules (g : M₀ →ₗ[R] M₁) (m : M₀) (s : S) :
    ((map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g)
    (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s := by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl, refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]

lemma map_iso_commute (g : M₀ →ₗ[R] M₁) : (map S f₀ f₁) g ∘ₗ (iso S f₀) =
    (iso S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g := by
  ext x
  refine induction_on (fun m s ↦ ((Module.End_isUnit_iff _).1 (map_units f₁ s)).1 ?_) x
  repeat rw [Module.algebraMap_end_apply, ← CompatibleSMul.map_smul, smul'_mk, ← mk_smul, mk_cancel]
  simp -- Can't be combined with next simp. This uses map_apply, which would be preempted by map.
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

end IsLocalizedModule

namespace IsLocalizedModule

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

/-- Localization of composition is the composition of localization -/
theorem map_comp' (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) :
    map S f₀ f₂ (h ∘ₗ g) = map S f₁ f₂ h ∘ₗ map S f₀ f₁ g := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

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

end Algebra

end IsLocalizedModule

end IsLocalizedModule

section Subsingleton

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

lemma LocalizedModule.mem_ker_mkLinearMap_iff {S : Submonoid R} {m} :
    m ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M) ↔ ∃ r ∈ S, r • m = 0 := by
  constructor
  · intro H
    obtain ⟨r, hr⟩ := (@LocalizedModule.mk_eq _ _ S M _ _ m 0 1 1).mp (by simpa using H)
    exact ⟨r, r.2, by simpa using hr⟩
  · rintro ⟨r, hr, e⟩
    apply ((Module.End_isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) ⟨r, hr⟩)).injective
    simp [← IsLocalizedModule.mk_eq_mk', LocalizedModule.smul'_mk, e]

lemma LocalizedModule.subsingleton_iff_ker_eq_top {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔
      LinearMap.ker (LocalizedModule.mkLinearMap S M) = ⊤ := by
  rw [← top_le_iff]
  refine ⟨fun H m _ ↦ Subsingleton.elim _ _, fun H ↦ (subsingleton_iff_forall_eq 0).mpr fun x ↦ ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
  simpa using @H x trivial

lemma LocalizedModule.subsingleton_iff {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔ ∀ m : M, ∃ r ∈ S, r • m = 0 := by
  simp_rw [subsingleton_iff_ker_eq_top, ← top_le_iff, SetLike.le_def,
    mem_ker_mkLinearMap_iff, Submodule.mem_top, true_implies]

end Subsingleton
