/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

#align_import algebra.lie.of_associative from "leanprover-community/mathlib"@"f0f3d964763ecd0090c9eb3ae0d15871d08781c4"

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

 * `LieAlgebra.ofAssociativeAlgebra`
 * `LieAlgebra.ofAssociativeAlgebraHom`
 * `LieModule.toEndomorphism`
 * `LieAlgebra.ad`
 * `LinearEquiv.lieConj`
 * `AlgEquiv.toLieEquiv`

## Tags

lie algebra, ring commutator, adjoint action
-/


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ring A]

namespace Ring

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
instance (priority := 100) : Bracket A A :=
  ⟨fun x y => x * y - y * x⟩

theorem lie_def (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  rfl
#align ring.lie_def Ring.lie_def

end Ring

theorem commute_iff_lie_eq {x y : A} : Commute x y ↔ ⁅x, y⁆ = 0 :=
  sub_eq_zero.symm
#align commute_iff_lie_eq commute_iff_lie_eq

theorem Commute.lie_eq {x y : A} (h : Commute x y) : ⁅x, y⁆ = 0 :=
  sub_eq_zero_of_eq h
#align commute.lie_eq Commute.lie_eq

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
instance (priority := 100) ofAssociativeRing : LieRing A where
  add_lie _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
                      -- ⊢ x✝² * x✝ + x✝¹ * x✝ - (x✝ * x✝² + x✝ * x✝¹) = x✝² * x✝ - x✝ * x✝² + (x✝¹ * x …
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
                      -- ⊢ x✝² * x✝¹ + x✝² * x✝ - (x✝¹ * x✝² + x✝ * x✝²) = x✝² * x✝¹ - x✝¹ * x✝² + (x✝² …
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
                 -- 🎉 no goals
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]; abel
    -- ⊢ x✝² * (x✝¹ * x✝) - x✝² * (x✝ * x✝¹) - (x✝¹ * (x✝ * x✝²) - x✝ * (x✝¹ * x✝²))  …
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
#align lie_ring.of_associative_ring LieRing.ofAssociativeRing

theorem of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  rfl
#align lie_ring.of_associative_ring_bracket LieRing.of_associative_ring_bracket

@[simp]
theorem lie_apply {α : Type*} (f g : α → A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ :=
  rfl
#align lie_ring.lie_apply LieRing.lie_apply

end LieRing

section AssociativeModule

variable {M : Type w} [AddCommGroup M] [Module A M]

/-- We can regard a module over an associative ring `A` as a Lie ring module over `A` with Lie
bracket equal to its ring commutator.

Note that this cannot be a global instance because it would create a diamond when `M = A`,
specifically we can build two mathematically-different `bracket A A`s:
 1. `@Ring.bracket A _` which says `⁅a, b⁆ = a * b - b * a`
 2. `(@LieRingModule.ofAssociativeModule A _ A _ _).toBracket` which says `⁅a, b⁆ = a • b`
    (and thus `⁅a, b⁆ = a * b`)

See note [reducible non-instances] -/
@[reducible]
def LieRingModule.ofAssociativeModule : LieRingModule A M where
  bracket := (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]
                    -- 🎉 no goals
#align lie_ring_module.of_associative_module LieRingModule.ofAssociativeModule

attribute [local instance] LieRingModule.ofAssociativeModule

theorem lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m :=
  rfl
#align lie_eq_smul lie_eq_smul

end AssociativeModule

section LieAlgebra

variable {R : Type u} [CommRing R] [Algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
instance (priority := 100) LieAlgebra.ofAssociativeAlgebra : LieAlgebra R A where
  lie_smul t x y := by
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
#align lie_algebra.of_associative_algebra LieAlgebra.ofAssociativeAlgebra

attribute [local instance] LieRingModule.ofAssociativeModule

section AssociativeRepresentation

variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A representation of an associative algebra `A` is also a representation of `A`, regarded as a
Lie algebra via the ring commutator.

See the comment at `LieRingModule.ofAssociativeModule` for why the possibility `M = A` means
this cannot be a global instance. -/
theorem LieModule.ofAssociativeModule : LieModule R A M where
  smul_lie := smul_assoc
  lie_smul := smul_algebra_smul_comm
#align lie_module.of_associative_module LieModule.ofAssociativeModule

instance Module.End.lieRingModule : LieRingModule (Module.End R M) M :=
  LieRingModule.ofAssociativeModule
#align module.End.lie_ring_module Module.End.lieRingModule

instance Module.End.lieModule : LieModule R (Module.End R M) M :=
  LieModule.ofAssociativeModule
#align module.End.lie_module Module.End.lieModule

end AssociativeRepresentation

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

/-- The map `ofAssociativeAlgebra` associating a Lie algebra to an associative algebra is
functorial. -/
def toLieHom : A →ₗ⁅R⁆ B :=
  { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }
                                -- 🎉 no goals
#align alg_hom.to_lie_hom AlgHom.toLieHom

instance : Coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) :=
  ⟨toLieHom⟩

/- Porting note: is a syntactic tautology
@[simp]
theorem toLieHom_coe : f.toLieHom = ↑f :=
  rfl
-/
#noalign alg_hom.to_lie_hom_coe

@[simp]
theorem coe_toLieHom : ((f : A →ₗ⁅R⁆ B) : A → B) = f :=
  rfl
#align alg_hom.coe_to_lie_hom AlgHom.coe_toLieHom

theorem toLieHom_apply (x : A) : f.toLieHom x = f x :=
  rfl
#align alg_hom.to_lie_hom_apply AlgHom.toLieHom_apply

@[simp]
theorem toLieHom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id :=
  rfl
#align alg_hom.to_lie_hom_id AlgHom.toLieHom_id

@[simp]
theorem toLieHom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) :=
  rfl
#align alg_hom.to_lie_hom_comp AlgHom.toLieHom_comp

theorem toLieHom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a; exact LieHom.congr_fun h a
  -- ⊢ ↑f a = ↑g a
         -- 🎉 no goals
#align alg_hom.to_lie_hom_injective AlgHom.toLieHom_injective

end AlgHom

end LieAlgebra

end OfAssociative

section AdjointAction

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `LieModule.toModuleHom`. -/
@[simps]
def LieModule.toEndomorphism : L →ₗ⁅R⁆ Module.End R M where
  toFun x :=
    { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
                     -- ⊢ ↑((fun x => { toAddHom := { toFun := fun m => ⁅x, m⁆, map_add' := (_ : ∀ (m  …
                            -- 🎉 no goals
  map_smul' t x := by ext m; apply smul_lie
                      -- ⊢ ↑(AddHom.toFun { toFun := fun x => { toAddHom := { toFun := fun m => ⁅x, m⁆, …
                             -- 🎉 no goals
  map_lie' {x y} := by ext m; apply lie_lie
                       -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := fun x => { toAddHom := { toFun := fu …
                              -- 🎉 no goals
#align lie_module.to_endomorphism LieModule.toEndomorphism

/-- The adjoint action of a Lie algebra on itself. -/
def LieAlgebra.ad : L →ₗ⁅R⁆ Module.End R L :=
  LieModule.toEndomorphism R L L
#align lie_algebra.ad LieAlgebra.ad

@[simp]
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆ :=
  rfl
#align lie_algebra.ad_apply LieAlgebra.ad_apply

@[simp]
theorem LieModule.toEndomorphism_module_end :
    LieModule.toEndomorphism R (Module.End R M) M = LieHom.id := by ext g m; simp [lie_eq_smul]
                                                                    -- ⊢ ↑(↑(toEndomorphism R (Module.End R M) M) g) m = ↑(↑LieHom.id g) m
                                                                             -- 🎉 no goals
#align lie_module.to_endomorphism_module_End LieModule.toEndomorphism_module_end

theorem LieSubalgebra.toEndomorphism_eq (K : LieSubalgebra R L) {x : K} :
    LieModule.toEndomorphism R K M x = LieModule.toEndomorphism R L M x :=
  rfl
#align lie_subalgebra.to_endomorphism_eq LieSubalgebra.toEndomorphism_eq

@[simp]
theorem LieSubalgebra.toEndomorphism_mk (K : LieSubalgebra R L) {x : L} (hx : x ∈ K) :
    LieModule.toEndomorphism R K M ⟨x, hx⟩ = LieModule.toEndomorphism R L M x :=
  rfl
#align lie_subalgebra.to_endomorphism_mk LieSubalgebra.toEndomorphism_mk

variable {R L M}

namespace LieSubmodule

open LieModule

variable {N : LieSubmodule R L M} {x : L}

theorem coe_map_toEndomorphism_le :
    (N : Submodule R M).map (LieModule.toEndomorphism R L M x) ≤ N := by
  rintro n ⟨m, hm, rfl⟩
  -- ⊢ ↑(↑(toEndomorphism R L M) x) m ∈ ↑N
  exact N.lie_mem hm
  -- 🎉 no goals
#align lie_submodule.coe_map_to_endomorphism_le LieSubmodule.coe_map_toEndomorphism_le

variable (N x)

theorem toEndomorphism_comp_subtype_mem (m : M) (hm : m ∈ (N : Submodule R M)) :
    (toEndomorphism R L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ ∈ (N : Submodule R M) := by
  simpa using N.lie_mem hm
  -- 🎉 no goals
#align lie_submodule.to_endomorphism_comp_subtype_mem LieSubmodule.toEndomorphism_comp_subtype_mem

@[simp]
theorem toEndomorphism_restrict_eq_toEndomorphism (h := N.toEndomorphism_comp_subtype_mem x) :
    (toEndomorphism R L M x).restrict h = toEndomorphism R L N x := by
  ext; simp [LinearMap.restrict_apply]
  -- ⊢ ↑(↑(LinearMap.restrict (↑(toEndomorphism R L M) x) h) x✝) = ↑(↑(↑(toEndomorp …
       -- 🎉 no goals
#align lie_submodule.to_endomorphism_restrict_eq_to_endomorphism LieSubmodule.toEndomorphism_restrict_eq_toEndomorphism

end LieSubmodule

open LieAlgebra

theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R A] :
    (ad R A : A → Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight R := by
  ext a b; simp [LieRing.of_associative_ring_bracket]
  -- ⊢ ↑(↑(ad R A) a) b = ↑((LinearMap.mulLeft R - LinearMap.mulRight R) a) b
           -- 🎉 no goals
#align lie_algebra.ad_eq_lmul_left_sub_lmul_right LieAlgebra.ad_eq_lmul_left_sub_lmul_right

theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L ↑x).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) := by
  ext y
  -- ⊢ ↑(LinearMap.comp (↑(ad R L) ↑x) ↑(incl K)) y = ↑(LinearMap.comp (↑(incl K))  …
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]
#align lie_subalgebra.ad_comp_incl_eq LieSubalgebra.ad_comp_incl_eq

end AdjointAction

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
    (A' : Subalgebra R A) : LieSubalgebra R A :=
  { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ ∈ A'; change x ∈ A' at hx; change y ∈ A' at hy
      -- ⊢ ⁅x, y⁆ ∈ A'
                          -- ⊢ ⁅x, y⁆ ∈ A'
                                               -- ⊢ ⁅x, y⁆ ∈ A'
      rw [LieRing.of_associative_ring_bracket]
      -- ⊢ x * y - y * x ∈ A'
      have hxy := A'.mul_mem hx hy
      -- ⊢ x * y - y * x ∈ A'
      have hyx := A'.mul_mem hy hx
      -- ⊢ x * y - y * x ∈ A'
      exact Submodule.sub_mem (Subalgebra.toSubmodule A') hxy hyx }
      -- 🎉 no goals
#align lie_subalgebra_of_subalgebra lieSubalgebraOfSubalgebra

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}

variable [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

variable (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, LinearMap.mul_eq_comp, e.conj_comp,
          LinearEquiv.map_sub] }
#align linear_equiv.lie_conj LinearEquiv.lieConj

@[simp]
theorem lieConj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f :=
  rfl
#align linear_equiv.lie_conj_apply LinearEquiv.lieConj_apply

@[simp]
theorem lieConj_symm : e.lieConj.symm = e.symm.lieConj :=
  rfl
#align linear_equiv.lie_conj_symm LinearEquiv.lieConj_symm

end LinearEquiv

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}

variable [CommRing R] [Ring A₁] [Ring A₂] [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def toLieEquiv : A₁ ≃ₗ⁅R⁆ A₂ :=
  { e.toLinearEquiv with
    toFun := e.toFun
    map_lie' := fun {x y} => by
      have : e.toEquiv.toFun = e := rfl
      -- ⊢ AddHom.toFun { toAddHom := { toFun := e.toFun, map_add' := (_ : ∀ (x y : A₁) …
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }
      -- 🎉 no goals
#align alg_equiv.to_lie_equiv AlgEquiv.toLieEquiv

@[simp]
theorem toLieEquiv_apply (x : A₁) : e.toLieEquiv x = e x :=
  rfl
#align alg_equiv.to_lie_equiv_apply AlgEquiv.toLieEquiv_apply

@[simp]
theorem toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x :=
  rfl
#align alg_equiv.to_lie_equiv_symm_apply AlgEquiv.toLieEquiv_symm_apply

end AlgEquiv
