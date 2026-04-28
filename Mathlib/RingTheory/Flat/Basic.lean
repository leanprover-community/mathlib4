/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang, Yongle Hu
-/
module

public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Flat modules

A module `M` over a commutative semiring `R` is *mono-flat* if for all monomorphisms of modules
(i.e., injective linear maps) `N →ₗ[R] P`, the canonical map `N ⊗ M → P ⊗ M` is injective
(cf. [Katsov2004], [KatsovNam2011]).
To show a module is mono-flat, it suffices to check inclusions of finitely generated
submodules `N` into finitely generated modules `P`, and `P` can be further assumed to lie in
the same universe as `R`.

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

Currently, `Module.Flat` is defined to be equivalent to mono-flatness over a semiring.
It is left as a TODO item to introduce the genuine flatness over semirings and rename
the current `Module.Flat` to `Module.MonoFlat`.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat module are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring modules
  in the higher universe preserves injectivity.
* `Module.Flat.lTensor_exact`: If `M` is a flat module then tensoring with `M` is an exact
  functor. This lemma is fully universally polymorphic in all arguments, i.e.
  `R`, `M` and linear maps `N → N' → N''` can all have different universe levels.
* `Module.Flat.iff_lTensor_exact`: a module is flat iff tensoring modules
  in the higher universe is an exact functor.

## TODO

* Generalize flatness to noncommutative semirings.

-/

@[expose] public section

assert_not_exists AddCircle

universe v' u v w

open TensorProduct

namespace Module

open Function (Injective Surjective)

open LinearMap Submodule DirectSum

section Semiring

/-! ### Flatness over a semiring -/

variable {R : Type u} {M : Type v} {N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

theorem _root_.LinearMap.rTensor_injective_of_fg {f : N →ₗ[R] P}
    (h : ∀ (N' : Submodule R N) (P' : Submodule R P),
      N'.FG → P'.FG → ∀ h : N' ≤ P'.comap f, Function.Injective ((f.restrict h).rTensor M)) :
    Function.Injective (f.rTensor M) := fun x y eq ↦ by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor_comp_apply] at eq
  have ⟨P', Pfg, le, eq⟩ := (Nfg.map _).exists_rTensor_fg_inclusion_eq eq
  simp_rw [← rTensor_comp_apply] at eq
  rw [h _ _ Nfg Pfg (map_le_iff_le_comap.mp le) eq]

lemma _root_.LinearMap.rTensor_injective_iff_subtype {f : N →ₗ[R] P} (hf : Function.Injective f)
    (e : P ≃ₗ[R] Q) : Function.Injective (f.rTensor M) ↔
      Function.Injective ((range <| e.toLinearMap ∘ₗ f).subtype.rTensor M) := by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

variable (R M) in
/-- An `R`-module `M` is flat if for every finitely generated submodule `N` of every
finitely generated `R`-module `P` in the same universe as `R`,
the canonical map `N ⊗ M → P ⊗ M` is injective. This implies the same is true for
arbitrary `R`-modules `N` and `P` and injective linear maps `N →ₗ[R] P`, see
`Flat.rTensor_preserves_injective_linearMap`. To show a module over a ring `R` is flat, it
suffices to consider the case `P = R`, see `Flat.iff_rTensor_injective`. -/
@[mk_iff] class Flat : Prop where
  out ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] [Module.Finite R P] (N : Submodule R P) : N.FG →
    Function.Injective (N.subtype.rTensor M)

namespace Flat

/-- If `M` is a flat module, then `f ⊗ 𝟙 M` is injective for all injective linear maps `f`. -/
theorem rTensor_preserves_injective_linearMap [Flat R M] (f : N →ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.rTensor M) := by
  refine rTensor_injective_of_fg fun N P Nfg Pfg le ↦ ?_
  rw [← Finite.iff_fg] at Nfg Pfg
  have := Finite.small R P
  let se := (Shrink.linearEquiv R P).symm
  have := Module.Finite.equiv se
  rw [rTensor_injective_iff_subtype (fun _ _ ↦ (Subtype.ext <| hf <| Subtype.ext_iff.mp ·)) se]
  exact (flat_iff R M).mp ‹_› _ (Finite.iff_fg.mp inferInstance)

/-- If `M` is a flat module, then `𝟙 M ⊗ f` is injective for all injective linear maps `f`. -/
theorem lTensor_preserves_injective_linearMap [Flat R M] (f : N →ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.lTensor M) :=
  (f.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap f hf)

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map
in a universe that `R` fits in. -/
lemma iff_rTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h ↦ ⟨fun P _ _ _ _ _ ↦ by
    have := Finite.small.{v'} R P
    rw [rTensor_injective_iff_subtype Subtype.val_injective (Shrink.linearEquiv R P).symm]
    exact h _ Subtype.val_injective⟩⟩

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map
in a universe that `R` fits in. -/
lemma iff_lTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMapₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

/-- An easier-to-use version of `Module.flat_iff`, with finiteness conditions removed. -/
lemma iff_rTensor_injectiveₛ : Flat R M ↔ ∀ ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.rTensor M) :=
  ⟨fun _ _ _ _ _ ↦ rTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun h ↦ ⟨fun _ _ _ _ _ _ ↦ h _⟩⟩

lemma iff_lTensor_injectiveₛ : Flat R M ↔ ∀ ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.lTensor M) := by
  simp_rw [iff_rTensor_injectiveₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

instance instSubalgebraToSubmodule {S : Type v} [Semiring S] [Algebra R S]
    (A : Subalgebra R S) [Flat R A] : Flat R A.toSubmodule := ‹Flat R A›

instance self : Flat R R where
  out _ _ _ _ I _ := by
    rw [← (TensorProduct.rid R I).symm.injective_comp, ← (TensorProduct.rid R _).comp_injective]
    convert Subtype.coe_injective using 1
    ext; simp

/-- A retract of a flat `R`-module is flat. -/
lemma of_retract [f : Flat R M] (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id) :
    Flat R N := by
  rw [iff_rTensor_injectiveₛ] at *
  refine fun P _ _ Q ↦ .of_comp (f := lTensor P i) ?_
  rw [← coe_comp, lTensor_comp_rTensor, ← rTensor_comp_lTensor, coe_comp]
  refine (f Q).comp (Function.RightInverse.injective (g := lTensor Q r) fun x ↦ ?_)
  simp [← comp_apply, ← lTensor_comp, h]

/-- An `R`-module linearly equivalent to a flat `R`-module is flat. -/
lemma of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : Flat R N :=
  of_retract e.toLinearMap e.symm (by simp)

/-- If an `R`-module `M` is linearly equivalent to another `R`-module `N`, then `M` is flat
  if and only if `N` is flat. -/
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ ↦ of_linearEquiv e.symm, fun _ ↦ of_linearEquiv e⟩

instance ulift [Flat R M] : Flat R (ULift.{v'} M) :=
  of_linearEquiv ULift.moduleEquiv

-- Making this an instance causes an infinite sequence `M → ULift M → ULift (ULift M) → ...`.
lemma of_ulift [Flat R (ULift.{v'} M)] : Flat R M :=
  of_linearEquiv ULift.moduleEquiv.symm

instance shrink [Small.{v'} M] [Flat R M] : Flat R (Shrink.{v'} M) :=
  of_linearEquiv (Shrink.linearEquiv R M)

-- Making this an instance causes an infinite sequence `M → Shrink M → Shrink (Shrink M) → ...`.
lemma of_shrink [Small.{v'} M] [Flat R (Shrink.{v'} M)] : Flat R M :=
  of_linearEquiv (Shrink.linearEquiv R M).symm

section DirectSum

variable {ι : Type v} {M : ι → Type w} [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]

theorem directSum_iff : Flat R (⨁ i, M i) ↔ ∀ i, Flat R (M i) := by
  classical
  simp_rw [iff_rTensor_injectiveₛ, ← EquivLike.comp_injective _ (directSumRight R R _ _),
    ← LinearEquiv.coe_coe, ← coe_comp, directSumRight_comp_rTensor, coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp, lmap_injective]
  constructor <;> (intro h; intros; apply h)

theorem dfinsupp_iff : Flat R (Π₀ i, M i) ↔ ∀ i, Flat R (M i) := directSum_iff ..

/-- A direct sum of flat `R`-modules is flat. -/
instance directSum [∀ i, Flat R (M i)] : Flat R (⨁ i, M i) := directSum_iff.mpr ‹_›

instance dfinsupp [∀ i, Flat R (M i)] : Flat R (Π₀ i, M i) := dfinsupp_iff.mpr ‹_›

end DirectSum

/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (ι : Type v) : Flat R (ι →₀ R) := by
  classical exact of_linearEquiv (finsuppLEquivDirectSum R R ι)

instance of_projective [Projective R M] : Flat R M :=
  have ⟨e, he⟩:= Module.projective_def'.mp ‹_›
  of_retract _ _ he

instance of_free [Free R M] : Flat R M := inferInstance

instance {S} [CommSemiring S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [Flat S M] [Flat R N] : Flat S (M ⊗[R] N) :=
  iff_rTensor_injectiveₛ.mpr fun P _ _ I ↦ by
    letI := RestrictScalars.moduleOrig R S P
    change Submodule S (RestrictScalars R S P) at I
    change Function.Injective (rTensor _ I.subtype)
    simpa [AlgebraTensorModule.rTensor_tensor] using
      rTensor_preserves_injective_linearMap (.restrictScalars R <| I.subtype.rTensor M)
      (rTensor_preserves_injective_linearMap _ I.injective_subtype)

example [Flat R M] [Flat R N] : Flat R (M ⊗[R] N) := inferInstance

theorem linearIndependent_one_tmul {S} [Semiring S] [Algebra R S] [Flat R S] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent S ((1 : S) ⊗ₜ[R] v ·) := by
  classical rw [LinearIndependent, ← LinearMap.coe_restrictScalars R,
    Finsupp.linearCombination_one_tmul]
  simpa using lTensor_preserves_injective_linearMap _ hv

variable (R M) in
/-- See also `Module.FaithfullyFlat.tensorProduct_mk_injective`. -/
lemma tensorProduct_mk_injective
    (A : Type*) [CommSemiring A] [Algebra R A] [FaithfulSMul R A] [Flat R M] :
    Injective (TensorProduct.mk R A M 1) := by
  have : TensorProduct.mk R A M 1 =
      (Algebra.linearMap R A).rTensor M ∘ (TensorProduct.lid R M).symm := by ext; simp
  rw [this]
  refine Injective.comp ?_ (LinearEquiv.injective _)
  exact Flat.rTensor_preserves_injective_linearMap _ <| FaithfulSMul.algebraMap_injective R A

end Flat

end Semiring

namespace Flat

/-! ### Flatness over a ring -/

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
lemma iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h ↦
    iff_rTensor_preserves_injective_linearMapₛ.mpr fun P N _ _ _ _ ↦ by
      letI := Module.addCommMonoidToAddCommGroup R (M := P)
      letI := Module.addCommMonoidToAddCommGroup R (M := N)
      apply h⟩

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
lemma iff_rTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  iff_rTensor_preserves_injective_linearMap'

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
lemma iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
lemma iff_lTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) :=
  iff_lTensor_preserves_injective_linearMap'

variable (M) in
/-- If `M` is flat then `M ⊗ -` is an exact functor. -/
lemma lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [show g = ι.comp π from rfl, lTensor_comp]
    exact exact1.comp_injective _ (lTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.lTensor_exact _ (fun x ↦ by simp [π]) Quotient.mk''_surjective

variable (M) in
/-- If `M` is flat then `- ⊗ M` is an exact functor. -/
lemma rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [show g = ι.comp π from rfl, rTensor_comp]
    exact exact1.comp_injective _ (rTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.rTensor_exact M (fun x ↦ by simp [π]) Quotient.mk''_surjective

/-- `M` is flat if and only if `M ⊗ -` is an exact functor. See
  `Module.Flat.iff_lTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
theorem iff_lTensor_exact' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ ↦ lTensor_exact _, fun H ↦ iff_lTensor_preserves_injective_linearMap'.mpr
    fun N' N'' _ _ _ _ L hL ↦ LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) ↦ ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x ↦ by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp hx

/-- `M` is flat if and only if `M ⊗ -` is an exact functor.
  See `Module.Flat.iff_lTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
theorem iff_lTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) :=
  iff_lTensor_exact'

/-- `M` is flat if and only if `- ⊗ M` is an exact functor. See
  `Module.Flat.iff_rTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
theorem iff_rTensor_exact' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ ↦ rTensor_exact _, fun H ↦ iff_rTensor_preserves_injective_linearMap'.mpr
    fun N' N'' _ _ _ _ f hf ↦ LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) ↦ ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 f (fun x ↦ by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (f.map_eq_zero_iff hf).trans eq_comm) x |>.mp hx

/-- `M` is flat if and only if `- ⊗ M` is an exact functor.
  See `Module.Flat.iff_rTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
theorem iff_rTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) :=
  iff_rTensor_exact'

end Flat

end Module

section Injective

variable {R S A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CommSemiring S] [Algebra S A] [SMulCommClass R S A]

namespace Algebra.TensorProduct

theorem includeLeft_injective [Module.Flat R A] (hb : Function.Injective (algebraMap R B)) :
    Function.Injective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  convert Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb
    |>.comp (_root_.TensorProduct.rid R A).symm.injective
  ext; simp

theorem includeRight_injective [Module.Flat R B] (ha : Function.Injective (algebraMap R A)) :
    Function.Injective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  convert Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha
    |>.comp (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

end Algebra.TensorProduct

variable (A) [Module.Flat R A] {M : Type*} [AddCommMonoid M] [Module R M] (p : Submodule R M)

namespace Submodule

theorem toBaseChange_injective : Function.Injective (p.toBaseChange A) :=
  (p.subtype.baseChange A).injective_rangeRestrict_iff.mpr
    (Module.Flat.lTensor_preserves_injective_linearMap p.subtype (injective_subtype p))

/-- `Submodule.toBaseChange` as a `LinearEquiv`. -/
@[simps! apply]
noncomputable def toBaseChange.toLinearEquiv : A ⊗[R] ↥p ≃ₗ[A] baseChange A p :=
  .ofBijective (p.toBaseChange A) ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

@[simp]
theorem toBaseChange.toLinearEquiv_symm_apply (a : A) (m : p) :
    (toBaseChange.toLinearEquiv A p).symm
      ⟨a ⊗ₜ[R] m, tmul_mem_baseChange_of_mem a m.2⟩ = a ⊗ₜ[R] m :=
  (toBaseChange.toLinearEquiv A p).symm_apply_apply (a ⊗ₜ[R] m)

end Submodule

end Injective

section Nontrivial

variable (R : Type*) [CommSemiring R]

namespace TensorProduct

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `N`,
and `M` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
theorem nontrivial_of_linearMap_injective_of_flat_left (f : R →ₗ[R] N) (h : Function.Injective f)
    [Module.Flat R M] [Nontrivial M] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h |>.comp
    (TensorProduct.rid R M).symm.injective |>.nontrivial

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `M`,
and `N` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
theorem nontrivial_of_linearMap_injective_of_flat_right (f : R →ₗ[R] M) (h : Function.Injective f)
    [Module.Flat R N] [Nontrivial N] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h |>.comp
    (TensorProduct.lid R N).symm.injective |>.nontrivial

variable {R M N}
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat'` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness conditions. -/
lemma map_injective_of_flat_flat
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [Module.Flat R M] [Module.Flat R Q]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

/-- Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness conditions. -/
lemma map_injective_of_flat_flat'
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [Module.Flat R P] [Module.Flat R N]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

variable {ι κ : Type*} {v : ι → M} {w : κ → N} {s : Set ι} {t : Set κ}

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`. -/
lemma _root_.LinearIndependent.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert (TensorProduct.map_injective_of_flat_flat _ _ hv hw).comp
    (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_left hw).comp _ (Equiv.Set.prod _ _).injective :)

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`. -/
lemma _root_.LinearIndependent.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 :=
  (((TensorProduct.comm R N M).toLinearMap.linearIndependent_iff_of_injOn
    (TensorProduct.comm R N M).injective.injOn).mpr
      (hw.tmul_of_flat_left hv)).comp Prod.swap Prod.swap_bijective.injective

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_right hw).comp _ (Equiv.Set.prod _ _).injective :)

variable (p : Submodule R M) (q : Submodule R N)

/-- If p and q are submodules of M and N respectively, and M and q are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_right
    [Module.Flat R M] [Module.Flat R q] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

/-- If p and q are submodules of M and N respectively, and N and p are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_left
    [Module.Flat R p] [Module.Flat R N] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat' _ _ p.subtype_injective q.subtype_injective

end TensorProduct

namespace Algebra.TensorProduct

variable (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- If `A`, `B` are `R`-algebras, `R` injects into `B`,
and `A` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
theorem nontrivial_of_algebraMap_injective_of_flat_left (h : Function.Injective (algebraMap R B))
    [Module.Flat R A] [Nontrivial A] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

/-- If `A`, `B` are `R`-algebras, `R` injects into `A`,
and `B` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
theorem nontrivial_of_algebraMap_injective_of_flat_right (h : Function.Injective (algebraMap R A))
    [Module.Flat R B] [Nontrivial B] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

end Algebra.TensorProduct

end Nontrivial

namespace IsTensorProduct

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P] {M₁ M₂ N₁ N₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]
  {f : M₁ →ₗ[R] M₂ →ₗ[R] M} {g : N₁ →ₗ[R] N₂ →ₗ[R] N}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂)

theorem map_id_injective_of_flat_left {g : M₁ →ₗ[R] N₂ →ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₂ →ₗ[R] N₂) (hi : Function.Injective i) [Module.Flat R M₁] :
    Function.Injective (hf.map hg LinearMap.id i) := by
  have h : hf.map hg LinearMap.id i = hg.equiv ∘ i.lTensor M₁ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using Module.Flat.lTensor_preserves_injective_linearMap i hi

theorem map_id_injective_of_flat_right {g : N₁ →ₗ[R] M₂ →ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₁ →ₗ[R] N₁) (hi : Function.Injective i) [Module.Flat R M₂] :
    Function.Injective (hf.map hg i LinearMap.id) := by
  have h : hf.map hg i LinearMap.id = hg.equiv ∘ i.rTensor M₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using Module.Flat.rTensor_preserves_injective_linearMap i hi

/-- If `M₂` and `N₁` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂` are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` induced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat'` for different flatness conditions. -/
theorem map_injective_of_flat_right_left (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₂] [Module.Flat R N₁] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat i₁ i₂ h₁ h₂

/-- If `M₁` and `N₂` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂` are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` induced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat` for different flatness conditions. -/
theorem map_injective_of_flat_left_right (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₁] [Module.Flat R N₂] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat' i₁ i₂ h₁ h₂

end IsTensorProduct

section IsSMulRegular

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Module.Flat R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

theorem IsSMulRegular.of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {x : R}
    (reg : IsSMulRegular M x) : IsSMulRegular N (algebraMap R S x) := by
  have h := hf.map_id_injective_of_flat_left hf (LinearMap.lsmul R M x) reg
  rwa [hf.map_id_lsmul_eq_lsmul_algebraMap] at h

theorem IsSMulRegular.of_flat {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

end IsSMulRegular

/-- Let `R` be a commutative semiring, let `C` be a commutative `R`-algebra, and let `A` be an
  `R`-algebra. If `C ⊗[R] B` is reduced for all finitely generated subalgebras `B` of `A`, then
  `C ⊗[R] A` is also reduced. -/
theorem IsReduced.tensorProduct_of_flat_of_forall_fg {R C A : Type*}
    [CommSemiring R] [CommSemiring C] [Semiring A] [Algebra R A] [Algebra R C] [Module.Flat R C]
    (h : ∀ B : Subalgebra R A, B.FG → IsReduced (C ⊗[R] B)) :
    IsReduced (C ⊗[R] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C) D.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨z, rfl⟩ := hD.2
  have h_notReduced : ¬IsReduced (C ⊗[R] D) := by
    simp_rw [isReduced_iff, not_forall]
    exact ⟨z, (IsNilpotent.map_iff h_inj).mp hx.right, (by simpa [·] using hx.1)⟩
  tauto
