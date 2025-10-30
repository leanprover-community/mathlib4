/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Pi

/-!
# Properties of the module `α →₀ M`

* `Finsupp.linearEquivFunOnFinite`: `α →₀ β` and `a → β` are equivalent if `α` is finite
* `FunOnFinite.map`: the map `(X → M) → (Y → M)` induced by a map `f : X ⟶ Y` when
`X` and `Y` are finite.
* `FunOnFinite.linearMmap`: the linear map `(X → M) →ₗ[R] (Y → M)` induced
by a map `f : X ⟶ Y` when `X` and `Y` are finite.

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section LinearEquiv.finsuppUnique

variable (R : Type*) {S : Type*} (M : Type*)
variable [AddCommMonoid M] [Semiring R] [Module R M]
variable (α : Type*) [Unique α]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
noncomputable def LinearEquiv.finsuppUnique : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {R M}

@[simp]
theorem LinearEquiv.finsuppUnique_apply (f : α →₀ M) :
    LinearEquiv.finsuppUnique R M α f = f default :=
  rfl

variable {α}

@[simp]
theorem LinearEquiv.finsuppUnique_symm_apply (m : M) :
    (LinearEquiv.finsuppUnique R M α).symm m = Finsupp.single default m := by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]

end LinearEquiv.finsuppUnique

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Forget that a function is finitely supported.

This is the linear version of `Finsupp.toFun`. -/
@[simps]
def lcoeFun : (α →₀ M) →ₗ[R] α → M where
  toFun := (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

namespace LinearMap

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFinsuppSurjective`
/-- A surjective linear map to functions on a finite type has a splitting. -/
def splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R) (s : Surjective f) :
    (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap

theorem splittingOfFunOnFintypeSurjective_splits [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.id := by
  classical
  ext x y
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single, Finsupp.sum_single_index, one_smul,
    (s (Finsupp.single x 1)).choose_spec, Finsupp.single_eq_pi_single]
  rw [zero_smul]

theorem leftInverse_splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g

theorem splittingOfFunOnFintypeSurjective_injective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s) :=
  (leftInverse_splittingOfFunOnFintypeSurjective f s).injective

end LinearMap

namespace Finsupp

variable {α : Type*}

/-- Given a family `Sᵢ` of `R`-submodules of `M` indexed by a type `α`, this is the `R`-submodule
of `α →₀ M` of functions `f` such that `f i ∈ Sᵢ` for all `i : α`. -/
def submodule (S : α → Submodule R M) : Submodule R (α →₀ M) where
  carrier := { x | ∀ i, x i ∈ S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
lemma mem_submodule_iff (S : α → Submodule R M) (x : α →₀ M) :
    x ∈ submodule S ↔ ∀ i, x i ∈ S i := by
  rfl

theorem ker_mapRange (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.ker (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]

theorem range_mapRange_linearMap (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : Type*) :
    LinearMap.range (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose!
    <;> simp_all (config := {contextual := true}) [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace FunOnFinite

section

variable {M : Type*} [AddCommMonoid M] {X Y Z : Type*}

/-- The map `(X → M) → (Y → M)` induced by a map `X → Y` between finite types. -/
noncomputable def map [Finite X] [Finite Y] (f : X → Y) (s : X → M) : Y → M :=
  Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))

lemma map_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    map f s y = ∑ x with f x = y, s x := by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finset_sum]
  simp [Finset.sum_filter]
  congr
  aesop

@[simp]
lemma map_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    map f (Pi.single x m) = Pi.single (f x) m := by
  simp [map]

variable (M) in
lemma map_id [Finite X] : map (_root_.id : X → X) (M := M) = _root_.id := by
  ext s
  simp [map]

lemma map_comp [Finite X] [Finite Y] [Finite Z] (g : Y → Z) (f : X → Y) :
    map (g.comp f) (M := M) = (map g).comp (map f) := by
  ext s
  simp [map, Finsupp.mapDomain_comp]

end

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {X Y Z : Type*}

/-- The linear map `(X → M) →ₗ[R] (Y → M)` induced by a map `X → Y` between finite types. -/
noncomputable def linearMap [Finite X] [Finite Y] (f : X → Y) :
    (X → M) →ₗ[R] (Y → M) :=
  (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap

lemma linearMap_apply_apply
    [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    linearMap R M f s y = (Finset.univ.filter (fun (x : X) ↦ f x = y)).sum s := by
  apply map_apply_apply

@[simp]
lemma linearMap_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    linearMap R M f (Pi.single x m) = Pi.single (f x) m := by
  apply map_piSingle

variable (X) in
@[simp]
lemma linearMap_id [Finite X] : linearMap R M (_root_.id : X → X) = .id := by
  classical
  aesop

lemma linearMap_comp [Finite X] [Finite Y] [Finite Z] (f : X → Y) (g : Y → Z) :
    linearMap R M (g.comp f) = (linearMap R M g).comp (linearMap R M f) := by
  classical
  aesop

end

end FunOnFinite
