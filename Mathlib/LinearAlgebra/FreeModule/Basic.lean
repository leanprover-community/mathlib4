/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Data.Finsupp.Fintype
import Mathlib.LinearAlgebra.TensorProduct.Basis

#align_import linear_algebra.free_module.basic from "leanprover-community/mathlib"@"4e7e7009099d4a88a750de710909b95487bf0124"

/-!
# Free modules

We introduce a class `Module.Free R M`, for `R` a `Semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `Finsupp.total_id_surjective` to prove that any module is the quotient of a free module.

## Main definition

* `Module.Free R M` : the class of free `R`-modules.
-/


universe u v w z

variable {ι : Type*} (R : Type u) (M : Type v) (N : Type z)

open TensorProduct DirectSum

section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Module.Free R M` is the statement that the `R`-module `M` is free. -/
class Module.Free : Prop where
  exists_basis : Nonempty <| (I : Type v) × Basis I R M
#align module.free Module.Free

/-- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`Module.Free.of_basis`. -/
theorem Module.free_def [Small.{w,v} M] :
    Module.Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) :=
  ⟨fun h =>
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩,
    fun h => ⟨(nonempty_sigma.2 h).map fun ⟨_, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩⟩
#align module.free_def Module.free_def

theorem Module.free_iff_set : Module.Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun h => ⟨Set.range h.exists_basis.some.2, ⟨Basis.reindexRange h.exists_basis.some.2⟩⟩,
    fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩
#align module.free_iff_set Module.free_iff_set

variable {R M}

theorem Module.Free.of_basis {ι : Type w} (b : Basis ι R M) : Module.Free R M :=
  (Module.free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩
#align module.free.of_basis Module.Free.of_basis

end Basic

namespace Module.Free

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid N] [Module R N]

/-- If `Module.Free R M` then `ChooseBasisIndex R M` is the `ι` which indexes the basis
  `ι → M`. Note that this is defined such that this type is finite if `R` is trivial. -/
def ChooseBasisIndex : Type _ :=
  ((Module.free_iff_set R M).mp ‹_›).choose
#align module.free.choose_basis_index Module.Free.ChooseBasisIndex

/-- There is no hope of computing this, but we add the instance anyway to avoid fumbling with
`open scoped Classical`. -/
noncomputable instance : DecidableEq (ChooseBasisIndex R M) := Classical.decEq _

/-- If `Module.Free R M` then `chooseBasis : ι → M` is the basis.
Here `ι = ChooseBasisIndex R M`. -/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  ((Module.free_iff_set R M).mp ‹_›).choose_spec.some
#align module.free.choose_basis Module.Free.chooseBasis

/-- The isomorphism `M ≃ₗ[R] (ChooseBasisIndex R M →₀ R)`. -/
noncomputable def repr : M ≃ₗ[R] ChooseBasisIndex R M →₀ R :=
  (chooseBasis R M).repr
#align module.free.repr Module.Free.repr

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
#align module.free.constr Module.Free.constr

instance (priority := 100) noZeroSMulDivisors [NoZeroDivisors R] : NoZeroSMulDivisors R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis (R := R) (M := M)
  b.noZeroSMulDivisors
#align module.free.no_zero_smul_divisors Module.Free.noZeroSMulDivisors

instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty

theorem infinite [Infinite R] [Nontrivial M] : Infinite M :=
  (Equiv.infinite_iff (chooseBasis R M).repr.toEquiv).mpr Finsupp.infinite_of_right

variable {R M N}

theorem of_equiv (e : M ≃ₗ[R] N) : Module.Free R N :=
  of_basis <| (chooseBasis R M).map e
#align module.free.of_equiv Module.Free.of_equiv

/-- A variation of `of_equiv`: the assumption `Module.Free R P` here is explicit rather than an
instance. -/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (_ : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e
#align module.free.of_equiv' Module.Free.of_equiv'

variable (R M N)

/-- The module structure provided by `Semiring.toModule` is free. -/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)
#align module.free.self Module.Free.self

instance prod [Module.Free R N] : Module.Free R (M × N) :=
  of_basis <| (chooseBasis R M).prod (chooseBasis R N)
#align module.free.prod Module.Free.prod

/-- The product of finitely many free modules is free. -/
instance pi (M : ι → Type*) [Finite ι] [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]
    [∀ i : ι, Module.Free R (M i)] : Module.Free R (∀ i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
  of_basis <| Pi.basis fun i => chooseBasis R (M i)
#align module.free.pi Module.Free.pi

/-- The module of finite matrices is free. -/
instance matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _
#align module.free.matrix Module.Free.matrix

instance ulift [Free R M] : Free R (ULift M) := of_equiv ULift.moduleEquiv.symm

variable (ι)

/-- The product of finitely many free modules is free (non-dependent version to help with typeclass
search). -/
instance function [Finite ι] : Module.Free R (ι → M) :=
  Free.pi _ _
#align module.free.function Module.Free.function

instance finsupp : Module.Free R (ι →₀ M) :=
  of_basis (Finsupp.basis fun _ => chooseBasis R M)
#align module.free.finsupp Module.Free.finsupp

variable {ι}

instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis.{u,z,z} (Basis.empty N : Basis PEmpty R N)
#align module.free.of_subsingleton Module.Free.of_subsingleton

instance (priority := 100) of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N
#align module.free.of_subsingleton' Module.Free.of_subsingleton'

instance dfinsupp {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
  of_basis <| DFinsupp.basis fun i => chooseBasis R (M i)
#align module.free.dfinsupp Module.Free.dfinsupp

instance directSum {ι : Type*} (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M
#align module.free.direct_sum Module.Free.directSum

end Semiring

section CommSemiring

variable {S} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module S M] [IsScalarTower R S M] [Module.Free S M]
  [AddCommMonoid N] [Module R N] [Module.Free R N]

instance tensor : Module.Free S (M ⊗[R] N) :=
  let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)
#align module.free.tensor Module.Free.tensor

end CommSemiring

end Module.Free
