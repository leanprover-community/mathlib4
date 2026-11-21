/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Justin Mu, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.Homology.AInfinity.AInfinityCategoryStruct
public import Mathlib.Algebra.Homology.AInfinity.StasheffIndex

/-!
# The Stasheff identities

Given a graded `R`-linear quiver with higher compositions
mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ) of degree 2 - n
(i.e. an `AInfinityCategoryStruct`), the arity-n Stasheff identity states
$$\sum_{r + s + t = n,\ s \ge 1} (-1)^{\|a_{r+s}\| + \dots + \|a_{n-1}\|}
  m_{r+1+t}(a_0, \dots, a_{r-1}, m_s(a_r, \dots, a_{r+s-1}), a_{r+s}, \dots, a_{n-1}) = 0,$$
where ‖a‖ = |a| - 1 is the reduced degree.

The index triples (r, s, t) and their API
are in `Mathlib/Algebra/Homology/AInfinity/StasheffIndex.lean`.

## Main definitions

* `AInfinity.stasheffTerm`: the term for a specific index (r, s, t) of the Stasheff sum without
  its Koszul sign.
* `AInfinity.stasheffSum`: the full signed Stasheff sum in arity n.

## Implementation notes

Morphisms are written in diagrammatic order: the input aᵢ of mₙ is a morphism from Xᵢ to Xᵢ₊₁,
and mₙ(a₀, …, aₙ₋₁) is a morphism from X₀ to Xₙ. This is the reverse of the order in which
[seidel2008] writes the arguments, so the Koszul sign of the (r, s, t) summand is (−1) raised to the
sum of the reduced degrees of the last t inputs. Degrees lie in an arbitrary `AInfinity.Grading`,
which generalizes the `ℤ`-grading of [seidel2008].

The value of an operation on inputs of degrees `deg` lies in the hom space of degree
`operationTargetDeg deg`. This is often only propositionally equal to the target degree,
so the definitions of this file, following `CochainComplex.HomComplex.Cochain`,
take a target degree `d` together with a proof `hd` that it equals the computed degree.

## References

* [P. Seidel, *Fukaya categories and Picard-Lefschetz theory*][seidel2008]
-/

@[expose] public section

namespace AInfinity

universe u v w

open GradedLinearQuiver
open AInfinityCategoryStruct (m)

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {R : Type u} [Semiring R] {Obj : Type w} [AInfinityCategoryStruct β R Obj]
variable {n : ℕ} {X : Fin (n + 1) → Obj} {deg : Fin n → β}
variable (a : ∀ i : Fin n, ComposableHom β R X i (deg i)) (p : StasheffIndex n)

/-- The inputs of the inner operation mₛ are the s middle input morphisms. -/
def stasheffInputsIn :
    ∀ j : Fin p.s, ComposableHom β R (stasheffObjIn X p) j (stasheffDegIn deg p j) :=
  fun j ↦ a (p.innerIndex j)

@[simp]
lemma stasheffInputsIn_apply (j : Fin p.s) : stasheffInputsIn a p j = a (p.innerIndex j) :=
  rfl

/-- The value $m_s(a_r, \dots, a_{r+s-1})$ of the inner operation, a morphism from `X r`
to `X (r + s)` of degree `stasheffInnerDeg deg p`. -/
def stasheffInner (d : β) (hd : stasheffInnerDeg deg p = d) :
    (stasheffObjIn X p 0 →ᵍ[R] stasheffObjIn X p (Fin.last p.s)) d :=
  (m (stasheffObjIn X p)).v (stasheffDegIn deg p) d hd (stasheffInputsIn a p)

/-- The inputs of the outer operation are the first r inputs, then the inner output, then the
last t inputs, each transported to the correct hom space for the outer operation. -/
def stasheffInputsOut :
    ∀ i : Fin (p.r + 1 + p.t), ComposableHom β R (stasheffObjOut X p) i (stasheffDegOut deg p i) :=
  Fin.addCases
    (Fin.snoc
      (fun j ↦ homCongr R (stasheffObjOut_left_castSucc X p j).symm
        (stasheffObjOut_left_succ X p j).symm (stasheffDegOut_left deg p j).symm
        (a (p.leftIndex j)))
      (homCongr R (stasheffObjOut_middle_castSucc X p).symm (stasheffObjOut_middle_succ X p).symm
        rfl (stasheffInner a p _ (stasheffDegOut_middle deg p).symm)))
    fun j ↦ homCongr R (stasheffObjOut_right_castSucc X p j).symm
      (stasheffObjOut_right_succ X p j).symm (stasheffDegOut_right deg p j).symm
      (a (p.rightIndex j))

@[simp]
lemma stasheffInputsOut_left (j : Fin p.r) :
    stasheffInputsOut a p (j.castSucc.castAdd p.t) =
      homCongr R (stasheffObjOut_left_castSucc X p j).symm (stasheffObjOut_left_succ X p j).symm
        (stasheffDegOut_left deg p j).symm (a (p.leftIndex j)) := by
  simp [stasheffInputsOut]

@[simp]
lemma stasheffInputsOut_right (j : Fin p.t) :
    stasheffInputsOut a p (j.natAdd (p.r + 1)) =
      homCongr R (stasheffObjOut_right_castSucc X p j).symm (stasheffObjOut_right_succ X p j).symm
        (stasheffDegOut_right deg p j).symm (a (p.rightIndex j)) := by
  simp [stasheffInputsOut]

@[simp]
lemma stasheffInputsOut_middle :
    stasheffInputsOut a p p.middleIndex =
      homCongr R (stasheffObjOut_middle_castSucc X p).symm (stasheffObjOut_middle_succ X p).symm
        rfl (stasheffInner a p _ (stasheffDegOut_middle deg p).symm) := by
  simp [stasheffInputsOut]

/-- The value of the outer operation when applied to its inputs `stasheffInputsOut a p`, i.e.
$m_{r+1+t}(a_0, \dots, a_{r-1}, m_s(a_r, \dots, a_{r+s-1}), a_{r+s}, \dots, a_{n-1})$, of degree
`operationTargetDeg (stasheffDegOut deg p)`. -/
def stasheffOuter (d : β) (hd : operationTargetDeg (stasheffDegOut deg p) = d) :
    (stasheffObjOut X p 0 →ᵍ[R] stasheffObjOut X p (Fin.last (p.r + 1 + p.t))) d :=
  (m (stasheffObjOut X p)).v (stasheffDegOut deg p) d hd (stasheffInputsOut a p)

/-- The (r, s, t) summand of the Stasheff sum without its Koszul sign is `stasheffOuter a p`,
transported to the hom space from `X 0` to `X (Fin.last n)`. -/
def stasheffTerm (d : β) (hd : stasheffTargetDeg deg = d) : (X 0 →ᵍ[R] X (Fin.last n)) d :=
  homCongr R (stasheffObjOut_zero X p) (stasheffObjOut_last X p) rfl
    (stasheffOuter a p d ((stasheffDegOut_sum deg p).trans hd))

/-- The arity-n Stasheff sum of the terms `stasheffTerm a p` over all index triples `p`,
each with its Koszul sign `stasheffSign deg p`. -/
def stasheffSum (d : β) (hd : stasheffTargetDeg deg = d) : (X 0 →ᵍ[R] X (Fin.last n)) d :=
  signedStasheffSum deg fun q ↦ stasheffTerm a q d hd

end AInfinity
