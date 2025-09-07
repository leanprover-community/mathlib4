/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

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
* `LieModule.toEnd`
* `LieAlgebra.ad`
* `LinearEquiv.lieConj`
* `AlgEquiv.toLieEquiv`

## Tags

lie algebra, ring commutator, adjoint action
-/


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ring A]

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
instance (priority := 100) ofAssociativeRing : LieRing A where
  add_lie _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]; abel

theorem of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  rfl

@[simp]
theorem lie_apply {α : Type*} (f g : α → A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ :=
  rfl

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
abbrev LieRingModule.ofAssociativeModule : LieRingModule A M where
  bracket := (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]

attribute [local instance] LieRingModule.ofAssociativeModule

theorem lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m :=
  rfl

end AssociativeModule

section LieAlgebra

variable {R : Type u} [CommRing R] [Algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
instance (priority := 100) LieAlgebra.ofAssociativeAlgebra : LieAlgebra R A where
  lie_smul t x y := by
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

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

instance Module.End.instLieRingModule : LieRingModule (Module.End R M) M :=
  LieRingModule.ofAssociativeModule

instance Module.End.instLieModule : LieModule R (Module.End R M) M :=
  LieModule.ofAssociativeModule

@[simp] lemma Module.End.lie_apply (f : Module.End R M) (m : M) : ⁅f, m⁆ = f m := rfl

end AssociativeRepresentation

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]
variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

/-- The map `ofAssociativeAlgebra` associating a Lie algebra to an associative algebra is
functorial. -/
def toLieHom : A →ₗ⁅R⁆ B :=
  { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }

instance : Coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) :=
  ⟨toLieHom⟩

@[simp]
theorem coe_toLieHom : ((f : A →ₗ⁅R⁆ B) : A → B) = f :=
  rfl

theorem toLieHom_apply (x : A) : f.toLieHom x = f x :=
  rfl

@[simp]
theorem toLieHom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id :=
  rfl

@[simp]
theorem toLieHom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) :=
  rfl

theorem toLieHom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a; exact LieHom.congr_fun h a

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
def LieModule.toEnd : L →ₗ⁅R⁆ Module.End R M where
  toFun x :=
    { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
  map_smul' t x := by ext m; apply smul_lie
  map_lie' {x y} := by ext m; apply lie_lie

/-- The adjoint action of a Lie algebra on itself. -/
def LieAlgebra.ad : L →ₗ⁅R⁆ Module.End R L :=
  LieModule.toEnd R L L

@[simp]
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆ :=
  rfl

@[simp]
theorem LieModule.toEnd_module_end :
    LieModule.toEnd R (Module.End R M) M = LieHom.id := by ext g m; simp [lie_eq_smul]

theorem LieSubalgebra.toEnd_eq (K : LieSubalgebra R L) {x : K} :
    LieModule.toEnd R K M x = LieModule.toEnd R L M x :=
  rfl

@[simp]
theorem LieSubalgebra.toEnd_mk (K : LieSubalgebra R L) {x : L} (hx : x ∈ K) :
    LieModule.toEnd R K M ⟨x, hx⟩ = LieModule.toEnd R L M x :=
  rfl

section IsFaithful

open Function

namespace LieModule

/-- A Lie module is *faithful* if the associated map `L → End M` is injective. -/
@[mk_iff]
class IsFaithful : Prop where
  injective_toEnd : Injective <| toEnd R L M

@[simp]
lemma toEnd_eq_iff [IsFaithful R L M] {x y : L} :
    toEnd R L M x = toEnd R L M y ↔ x = y :=
  IsFaithful.injective_toEnd.eq_iff

variable {R L} in
lemma ext_of_isFaithful [IsFaithful R L M] {x y : L} (h : ∀ m : M, ⁅x, m⁆ = ⁅y, m⁆) :
    x = y :=
  (toEnd_eq_iff R L M).mp <| LinearMap.ext h

@[simp]
lemma toEnd_eq_zero_iff [IsFaithful R L M] {x : L} :
    toEnd R L M x = 0 ↔ x = 0 := by
  simp [- LieHom.map_zero, ← (toEnd R L M).map_zero]

lemma isFaithful_iff' : IsFaithful R L M ↔ ∀ x : L, (∀ m : M, ⁅x, m⁆ = 0) → x = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m ↦ ?_
    rw [sub_lie, sub_eq_zero, ← toEnd_apply_apply R, ← toEnd_apply_apply R, hxy]

instance [IsFaithful R L M] {L' : LieSubalgebra R L} :
    IsFaithful R L' M := by
  refine ⟨(?_ : Injective (toEnd R L M ∘ ((↑) : L' → L)))⟩
  exact IsFaithful.injective_toEnd.comp Subtype.val_injective

instance : IsFaithful R (Module.End R M) M where
  injective_toEnd := by simpa using injective_id

end LieModule

end IsFaithful


section

open LieAlgebra LieModule

lemma LieSubmodule.coe_toEnd (N : LieSubmodule R L M) (x : L) (y : N) :
    (toEnd R L N x y : M) = toEnd R L M x y := rfl

lemma LieSubmodule.coe_toEnd_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : ℕ) :
    ((toEnd R L N x ^ n) y : M) = (toEnd R L M x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]

lemma LieSubalgebra.coe_ad (H : LieSubalgebra R L) (x y : H) :
    (ad R H x y : L) = ad R L x y := rfl

lemma LieSubalgebra.coe_ad_pow (H : LieSubalgebra R L) (x y : H) (n : ℕ) :
    ((ad R H x ^ n) y : L) = (ad R L x ^ n) y :=
  LieSubmodule.coe_toEnd_pow R H L H.toLieSubmodule x y n

variable {L M}

local notation "φ" => LieModule.toEnd R L M

lemma LieModule.toEnd_lie (x y : L) (z : M) :
    (φ x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆ := by
  simp

lemma LieAlgebra.ad_lie (x y z : L) :
    (ad R L x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, ad R L x z⁆ :=
  toEnd_lie _ x y z

open Finset in
lemma LieModule.toEnd_pow_lie (x y : L) (z : M) (n : ℕ) :
    ((φ x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((φ x) ^ ij.2) z⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j ↦ ⁅((ad R L x) ^ i) y, ((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_comm, add_left_cancel_iff, sum_congr rfl]
    rintro ⟨i, j⟩ hij
    rw [mem_antidiagonal] at hij
    rw [Nat.choose_symm_of_eq_add hij.symm]

open Finset in
lemma LieAlgebra.ad_pow_lie (x y z : L) (n : ℕ) :
    ((ad R L x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2) z⁆ :=
  toEnd_pow_lie _ x y z n

end

variable {R L M}

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  (f : M →ₗ⁅R,L⁆ M₂) (k : ℕ) (x : L)

lemma toEnd_pow_comp_lieHom :
    (toEnd R L M₂ x ^ k) ∘ₗ f = f ∘ₗ toEnd R L M x ^ k := by
  apply Module.End.commute_pow_left_of_commute
  ext
  simp

lemma toEnd_pow_apply_map (m : M) :
    (toEnd R L M₂ x ^ k) (f m) = f ((toEnd R L M x ^ k) m) :=
  LinearMap.congr_fun (toEnd_pow_comp_lieHom f k x) m

end LieModule

namespace LieSubmodule

open LieModule Set

variable {N : LieSubmodule R L M} {x : L}

theorem coe_map_toEnd_le :
    (N : Submodule R M).map (LieModule.toEnd R L M x) ≤ N := by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

variable (N x)

theorem toEnd_comp_subtype_mem (m : M) (hm : m ∈ (N : Submodule R M)) :
    (toEnd R L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ ∈ (N : Submodule R M) := by
  simpa using N.lie_mem hm

@[simp]
theorem toEnd_restrict_eq_toEnd (h := N.toEnd_comp_subtype_mem x) :
    (toEnd R L M x).restrict h = toEnd R L N x := by
  ext
  simp only [LinearMap.restrict_coe_apply, toEnd_apply_apply, ← coe_bracket,
    SetLike.coe_eq_coe]
  rfl

lemma mapsTo_pow_toEnd_sub_algebraMap {φ : R} {k : ℕ} {x : L} :
    MapsTo ((toEnd R L M x - algebraMap R (Module.End R M) φ) ^ k) N N := by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm ↦ N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

end LieSubmodule

open LieAlgebra

theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R A] :
    (ad R A : A → Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight R := by
  ext a b; simp [LieRing.of_associative_ring_bracket]

theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L ↑x).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) := by
  ext y
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]

end AdjointAction

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
    (A' : Subalgebra R A) : LieSubalgebra R A :=
  { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ ∈ A'; change x ∈ A' at hx; change y ∈ A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem (Subalgebra.toSubmodule A') hxy hyx }

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}
variable [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, e.conj_comp,
          map_sub] }

@[simp]
theorem lieConj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f :=
  rfl

@[simp]
theorem lieConj_symm : e.lieConj.symm = e.symm.lieConj :=
  rfl

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
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }

@[simp]
theorem toLieEquiv_apply (x : A₁) : e.toLieEquiv x = e x :=
  rfl

@[simp]
theorem toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x :=
  rfl

end AlgEquiv

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

open LieEquiv

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and an element `x : L`, the conjugate
of the endomorphism `ad(x)` of `L` by `e` is the endomorphism `ad(e x)` of `L'`. -/
@[simp]
lemma conj_ad_apply (e : L ≃ₗ⁅R⁆ L') (x : L) : e.toLinearEquiv.conj (ad R L x) = ad R L' (e x) := by
  ext y'
  rw [LinearEquiv.conj_apply_apply, ad_apply, ad_apply, coe_toLinearEquiv, map_lie,
    ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]

end LieAlgebra
