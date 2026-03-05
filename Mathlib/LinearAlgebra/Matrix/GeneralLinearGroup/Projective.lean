/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Data.Sign.Basic

/-!
# Projective general linear group

In this file we define `Matrix.ProjGenLinGroup n R` as the quotient of `GL n R` by its center.
We introduce notation `PGL(n, R)` for this group,
which works if `n` is either a finite type or a natural number.
If `n` is a number, then `PGL(n, R)` is interpreted as `PGL(Fin n, R)`.
-/

open scoped MatrixGroups

public section

namespace Matrix

/-- Projective general linear group $PGL(n, R)$
defined as the quotient of the general linear group by its center. -/
def ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : Type _ :=
  GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

namespace ProjGenLinGroup
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The natural projection from `GL n R` to `PGL n R`. -/
def mk : GL n R →* PGL(n, R) := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk : GL n R → PGL(n, R)) :=
  Quotient.mk_surjective

@[simp]
theorem ker_mk : mk.ker = Subgroup.center (GL n R) := QuotientGroup.ker_mk' _

@[simp]
theorem mk_scalar (u : Rˣ) : mk (.scalar n u) = 1 := by
  rw [← MonoidHom.mem_ker, ker_mk, GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]
theorem induction_on {motive : PGL(n, R) → Prop} (g : PGL(n, R))
    (mk : ∀ g : GL n R, motive (ProjGenLinGroup.mk g)) : motive g :=
  Quotient.inductionOn g mk

variable {M : Type*} [Monoid M]

/-- Lift a monoid homomorphism `f : GL n R →* M` that vanishes on all scalar matrices
to a homomorphism from `PGL(n, R)`. -/
def lift (f : GL n R →* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1) :
    PGL(n, R) →* M :=
  QuotientGroup.lift _ f <| by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]
theorem lift_mk {f : GL n R →* M} (hf) (g : GL n R) : lift f hf (mk g) = f g := by
  rfl

@[simp]
theorem lift_comp_mk {f : GL n R →* M} (hf) : (lift f hf).comp mk = f := by
  rfl

/-- Given an action of `GL n R` such that the scalar matrices act trivially,
define an action of `PGL n R`. -/
def mulActionOfGL {α : Type*} [MulAction (GL n R) α]
    (h : ∀ (u : Rˣ) (a : α), GeneralLinearGroup.scalar n u • a = a) :
    MulAction (PGL(n, R)) α :=
  .ofEndHom <| lift MulAction.toEndHom <| by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a

theorem mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) :
    letI : MulAction (PGL(n, R)) α := mulActionOfGL h
    mk g • a = g • a := by
  rfl

variable [Fact (Even (Fintype.card n))] [LinearOrder R] [IsStrictOrderedRing R]

/-- In case of an even dimension, the sign of the determinant of `g : PGL(n, R)` is well-defined. -/
def signDet : PGL(n, R) →* SignTypeˣ :=
  lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) <| by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]

theorem signDet_mk (g : GL n R) : signDet (mk g) = Units.map signHom.toMonoidHom g.det := by
  rfl

@[simp]
theorem val_signDet_mk (g : GL n R) : (signDet (mk g) : SignType) = .sign g.det.val := by
  rfl

end ProjGenLinGroup

end Matrix
