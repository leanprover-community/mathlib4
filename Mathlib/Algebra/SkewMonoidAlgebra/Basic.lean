/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.Data.Finsupp.SMul

/-!
# Skew monoid algebras

This file presents a skewed version of `Mathlib.Algebra.MonoidAlgebra.Basic` with an
irreducible definition.

The definition is separated from `Finsupp` by wrapping it with a structure.
For https://github.com/leanprover-community/mathlib4/pull/15878, the goal is only to get this separation right. This means that
most of what makes these objects skewed is currently missing from this PR.

The goal will then be to define a skewed convolution product on `SkewMonoidAlgebra k G`.
Here, the product of two elements `f g : SkewMonoidAlgebra k G` is the finitely supported
function whose value at `a` is the sum of `f x * (x • g y)` over all pairs `x, y`
such that `x * y = a`. (See https://github.com/leanprover-community/mathlib4/pull/10541 at line 558 for an implementation.)

The associativity of the skewed multiplication depends on the `[MulSemiringAction G k]` instance.
In particular, this means that unlike in `Mathlib.Algebra.MonoidAlgebra.Basic`, `G` will
need to be a monoid for most of our uses.
-/

noncomputable section

/-- The skew monoid algebra over a semiring `k` generated by the monoid `G`.
It is the type of finite formal `k`-linear combinations of terms of `G`,
endowed with a skewed convolution product. -/
structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofFinsupp ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  toFinsupp : G →₀ k

open Function
namespace SkewMonoidAlgebra

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k]

@[simp]
theorem eta (f : SkewMonoidAlgebra k G) : ofFinsupp f.toFinsupp = f := rfl

@[irreducible]
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

instance instZero : Zero (SkewMonoidAlgebra k G) := ⟨⟨0⟩⟩

instance instAdd : Add (SkewMonoidAlgebra k G) := ⟨add⟩

instance instSMulZeroClass {S : Type*} [SMulZeroClass S k] :
    SMulZeroClass S (SkewMonoidAlgebra k G) where
  smul s f := smul s f
  smul_zero a := by simp only [smul]; exact congr_arg ofFinsupp (smul_zero a)

@[simp]
theorem ofFinsupp_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

@[simp]
theorem ofFinsupp_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]

@[simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G →₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) :=
  show _ = smul _ _ by rw [smul]

@[simp]
theorem toFinsupp_zero : (0 : SkewMonoidAlgebra k G).toFinsupp = 0 := rfl

@[simp]
theorem toFinsupp_add (a b : SkewMonoidAlgebra k G) :
    (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := by
  cases a
  cases b
  rw [← ofFinsupp_add]

@[simp]
theorem toFinsupp_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G) :
    (a • b).toFinsupp = a • b.toFinsupp := by
  cases b
  rw [← ofFinsupp_smul]

theorem _root_.IsSMulRegular.skewMonoidAlgebra {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}
    (ha : IsSMulRegular k a) : IsSMulRegular (SkewMonoidAlgebra k G) a
  | ⟨_⟩, ⟨_⟩, h => by
    simp only [← ofFinsupp_smul] at h
    exact congr_arg _ <| ha.finsupp (ofFinsupp.inj h)

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : SkewMonoidAlgebra k G → Finsupp _ _) :=
  fun ⟨_⟩ _ => congr_arg _

@[simp]
theorem toFinsupp_inj {a b : SkewMonoidAlgebra k G} : a.toFinsupp = b.toFinsupp ↔ a = b :=
  toFinsupp_injective.eq_iff

theorem ofFinsupp_injective :
    Function.Injective (ofFinsupp : Finsupp _ _ → SkewMonoidAlgebra k G) :=
  fun _ _ => congr_arg toFinsupp

/-- A more convenient spelling of `SkewMonoidAlgebra.ofFinsupp.injEq` in terms of `Iff`. -/
theorem ofFinsupp_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b :=
  ofFinsupp_injective.eq_iff

@[simp]
theorem toFinsupp_eq_zero {a : SkewMonoidAlgebra k G} : a.toFinsupp = 0 ↔ a = 0 := by
  rw [← toFinsupp_zero, toFinsupp_inj]

@[simp]
theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0 := by
  rw [← ofFinsupp_zero, ofFinsupp_inj]

instance instInhabited : Inhabited (SkewMonoidAlgebra k G) := ⟨0⟩

instance instNontrivial [Nontrivial k] [Nonempty G] :
    Nontrivial (SkewMonoidAlgebra k G) := Function.Injective.nontrivial ofFinsupp_injective

instance instAddCommMonoid : AddCommMonoid (SkewMonoidAlgebra k G) where
  __ := toFinsupp_injective.addCommMonoid _ toFinsupp_zero toFinsupp_add
    (fun _ _ => toFinsupp_smul _ _)
  toAdd  := SkewMonoidAlgebra.instAdd
  toZero := SkewMonoidAlgebra.instZero
  nsmul  := (· • ·)

section Support

/-- For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that
`f a ≠ 0`. -/
def support : SkewMonoidAlgebra k G → Finset G
  | ⟨p⟩ => p.support

@[simp]
theorem support_ofFinsupp (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support := by
  rw [support]

theorem support_toFinsupp (p : SkewMonoidAlgebra k G) : p.toFinsupp.support = p.support := by
  rw [support]

@[simp]
theorem support_zero : (0 : SkewMonoidAlgebra k G).support = ∅ := rfl

@[simp]
theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by
  rcases p with ⟨⟩
  simp only [support, Finsupp.support_eq_empty, ofFinsupp_eq_zero]

end Support

end AddCommMonoid

end SkewMonoidAlgebra
