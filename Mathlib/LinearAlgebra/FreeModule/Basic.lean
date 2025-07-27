/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Logic.Small.Basic

/-!
# Free modules

We introduce a class `Module.Free R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.linearCombination_id_surjective` to prove that any module is the quotient of a free
module.

## Main definition

* `Module.Free R M` : the class of free `R`-modules.
-/

assert_not_exists DirectSum Matrix TensorProduct

universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

namespace Module
section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Module.Free R M` is the statement that the `R`-module `M` is free. -/
class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M

lemma Free.exists_set [Free R M] : ∃ S : Set M, Nonempty (Basis S R M) :=
  let ⟨_I, b⟩ := exists_basis R M; ⟨Set.range b, ⟨b.reindexRange⟩⟩

theorem free_iff_set : Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun _ ↦ Free.exists_set .., fun ⟨S, hS⟩ ↦ ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩

/-- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`Module.Free.of_basis`. -/
theorem free_def [Small.{w, v} M] : Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) where
  mp h :=
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩
  mpr h := ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩

variable {R M}

theorem Free.of_basis {ι : Type w} (b : Basis ι R M) : Free R M :=
  (free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩

end Basic

namespace Free

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid N] [Module R N]

/-- If `Module.Free R M` then `ChooseBasisIndex R M` is the `ι` which indexes the basis
  `ι → M`. Note that this is defined such that this type is finite if `R` is trivial. -/
def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose

/-- There is no hope of computing this, but we add the instance anyway to avoid fumbling with
`open scoped Classical`. -/
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _

/-- If `Module.Free R M` then `chooseBasis : ι → M` is the basis.
Here `ι = ChooseBasisIndex R M`. -/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some

/-- The isomorphism `M ≃ₗ[R] (ChooseBasisIndex R M →₀ R)`. -/
noncomputable def repr : M ≃ₗ[R] ChooseBasisIndex R M →₀ R :=
  (chooseBasis R M).repr

/-- The universal property of free modules: giving a function `(ChooseBasisIndex R M) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings]. -/
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S

instance (priority := 100) noZeroSMulDivisors [NoZeroDivisors R] : NoZeroSMulDivisors R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.noZeroSMulDivisors

instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty

theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

instance [Module.Free R M] [Nontrivial M] : FaithfulSMul R M :=
  .of_injective _ (Module.Free.repr R M).symm.injective

variable {R M N}

theorem of_equiv (e : M ≃ₗ[R] N) : Module.Free R N :=
  of_basis <| (chooseBasis R M).map e

/-- A variation of `of_equiv`: the assumption `Module.Free R P` here is explicit rather than an
instance. -/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') [Module.Free R M] :
    Module.Free R' M' := by
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I →₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I →₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I →₀ R') :=
    { __ := e, map_smul' := fun m x ↦ Finsupp.ext fun i ↦ by simp [he, map_smulₛₗ] }
  exact of_basis (.ofRepr e')

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma iff_of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ ↦ of_ringEquiv e₁ e₂, fun _ ↦ of_ringEquiv e₁.symm e₂.symm⟩

variable (R M N)

/-- The module structure provided by `Semiring.toModule` is free. -/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)

instance ulift [Free R M] : Free R (ULift M) := of_equiv ULift.moduleEquiv.symm

instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis.{u,z,z} (Basis.empty N : Basis PEmpty R N)

instance (priority := 100) of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N

end Semiring

end Free

namespace Basis

open Finset

variable {S : Type*} [CommRing R] [Ring S] [Algebra R S]

/-- If `B` is a basis of the `R`-algebra `S` such that `B i = 1` for some index `i`, then
each `r : R` gets represented as `s • B i` as an element of `S`. -/
theorem repr_algebraMap {ι : Type*} [DecidableEq ι] {B : Basis ι R S} {i : ι} (hBi : B i = 1)
    (r : R) : B.repr ((algebraMap R S) r) = fun j : ι ↦ if i = j then r else 0 := by
  ext j
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ← hBi, Finsupp.smul_apply, B.repr_self_apply]
  simp

end Module.Basis
