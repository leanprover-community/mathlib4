/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Group.Defs

/-!
# Graded heterogeneous multiplication

In this file, we define `GradedType M` as `M → Type*`. When the index set `M` is
equipped with an addition, and `X`, `Y` and `Z` are graded types indexed by `M`, we
introduce the notion of graded heterogeneous multiplication. Informally, this
means that if `x : X a` and `y : Y b`, we can define the product in `Z (a + b)`.
In order to avoid type theory issues, the datum involved in the typeclass
`[HasGradedHMul X Y Z]` consists of the datum of a map `X a → Y b → Z c` whenever
`a + b = c`.

Then, we introduce the notation `x •[h] y : Z c` for this graded heterogeneous
multiplication, with `x : X a`, `y : Y b` and `h : a + b = c`. The associativity of
such multiplications can be phrased using the typeclass `IsAssocGradedHMul`.

Part of the reason for this design choice is that if `M` is an additive monoid,
`x : X a`, `y : Y 0`, we would usually want the product of `x` and `y` to be in
`Z a` rather than `Z (a + 0)`, which can be achieved here by using the notation
`x •[add_zero a] y`.

Graded heterogeneous multiplications shall be useful in the development of
cohomology theory:
* If `K` and `L` are cochain complexes (indexed by `ℤ`) in a preadditive category,
we may define `Cochain K L n` as families of morphisms `K.X p ⟶ L.X q` for all integers
`p` and `q` such that `p + n = q`. If `M` is another cochain complex, we have a
composition of cochains `HasGradedHMul (Cochain K L) (Cochain L M) (Cochain K M)`
which is associative. This will play an important role in the construction
of the triangulated structure on the homotopy category of cochain complexes of
an additive category (TODO).
* If `K` and `L` are objects of a triangulated category, "shifted homs" `K ⟶ L⟦n⟧`
form a graded type indexed by `ℤ`, and the composition of these is also associative (TODO).
* The composition of `Ext` groups in an abelian category can also be interpreted
using an associative graded heterogeneous multiplication (TODO).

-/

universe u₁ u₂

/-- A graded type indexed by `M` is a map `M → Type*` -/
abbrev GradedType (M : Type u₁) := M → Type u₂

variable {M G : Type u₁}

/-- A graded heterogeneous multiplication from `X` and `Y` to `Z` (all are graded types
indexed by `M`) consists of maps `X a → Y b → Z c` whenever `a + b = c` in `M`. -/
class HasGradedHMul [Add M] (X Y : GradedType M) (Z : outParam (GradedType M)) where
  /-- the heterogeneous multiplication -/
  γhmul' (a b c : M) (h : a + b = c) (α : X a) (β : Y b) : Z c

/-- When `[HasGradedHMul X Y Z]`, `x : X a`, `y : Y b` and `a + b = c`, this is the
result in `Z c` of the graded heterogeneous multiplication of `x` and `y`. -/
def HasGradedHMul.γhmul [Add M] {X Y : GradedType M} {Z : outParam (GradedType M)}
    [HasGradedHMul X Y Z] {a b : M} (α : X a) (β : Y b) {c : M} (h : a + b = c) : Z c :=
  γhmul' a b c h α β

/-- When `[HasGradedHMul X Y Z]`, `x : X a`, `y : Y b` and `a + b = c`, this is the
result in `Z c` of the graded heterogeneous multiplication of `x` and `y`. -/
notation a " •[" h "] " b:80 => HasGradedHMul.γhmul a b h

section

variable [AddMonoid M] (X Y Z : GradedType M) (XY YZ XYZ : outParam (GradedType M))
  [HasGradedHMul X Y XY] [HasGradedHMul Y Z YZ]
  [HasGradedHMul X YZ XYZ] [HasGradedHMul XY Z XYZ]

/-- The condition that graded heterogeneous multiplications are associative. -/
class IsAssocGradedHMul : Prop where
  /-- The associativity condition on graded heterogeneous multiplications. -/
  γhmul_assoc : ∀ ⦃a b c : M⦄ (α : X a) (β : Y b) (γ : Z c) (ab bc abc : M)
    (hab : a + b = ab) (hbc : b + c = bc) (habc : ab + c = abc),
      (α •[hab] β) •[habc] γ =
        α •[show a + bc = abc by rw [← hbc, ← add_assoc, hab, habc]] (β •[hbc] γ)

/- Similarly as for the composition of morphisms in categories, we would favour
the rewriting of `(α •[_] β) •[_] γ` as `α •[_] (β •[_] γ)`, but in general,
there is no way to determine the most convenient expression for the sum of the
degrees of `β` and `γ`. However, we provide a few convenient lemmas which correspond
to special cases when there is a reasonable choice, e.g. when `α`, `β` or `γ` is
in degree zero. -/

@[simp]
lemma γhmul_assoc_of_first_degree_eq_zero [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {b c : M} (α : X 0) (β : Y b) (γ : Z c) (bc : M) (hbc : b + c = bc) :
    (α •[zero_add _] β) •[hbc] γ = α •[zero_add _] β •[hbc] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

@[simp]
lemma γhmul_assoc_of_second_degree_eq_zero [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {a c : M} (α : X a) (β : Y 0) (γ : Z c) (ac : M) (hac : a + c = ac) :
  (α •[add_zero _] β) •[hac] γ = α •[hac] β •[zero_add _] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

@[simp]
lemma γhmul_assoc_of_third_degree_eq_zero [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {a b : M} (α : X a) (β : Y b) (γ : Z 0) (ab : M) (hab : a + b = ab) :
  (α •[hab] β) •[add_zero _] γ = α •[hab] β •[add_zero _] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

end

section

variable [AddGroup G] (X' Y' Z' : GradedType G) (XY' YZ' XYZ' : outParam (GradedType G))
  [HasGradedHMul X' Y' XY'] [HasGradedHMul Y' Z' YZ']
  [HasGradedHMul X' YZ' XYZ'] [HasGradedHMul XY' Z' XYZ']

@[simp]
lemma γhmul_assoc_of_second_degree_eq_neg_third_degree [IsAssocGradedHMul X' Y' Z' XY' YZ' XYZ']
    {a b ab : G} (α : X' a) (β : Y' (-b)) (γ : Z' b) (hab : a + (-b) = ab) :
    (α •[hab] β) •[show ab + b = a by rw [← hab, add_assoc, neg_add_self, add_zero]] γ =
      α •[add_zero a] (β •[neg_add_self b] γ) := by
  apply IsAssocGradedHMul.γhmul_assoc

end
