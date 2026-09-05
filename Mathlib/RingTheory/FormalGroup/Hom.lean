/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.FormalGroup.AddInv
public import Mathlib.RingTheory.FormalGroup.Basic

/-!
# Homomorphisms and isomorphisms of formal group laws

Let `R` be a commutative ring and let `F` and `G` be one dimensional formal group laws over `R`.
A homomorphism `F → G` is a power series `α(X) = b₁ X + b₂ X ^ 2 + ⋯` in `R⟦X⟧` without constant
term such that
`α(F(X, Y)) = G(α(X), α(Y))`.
It is an isomorphism when it admits a two-sided inverse homomorphism `G → F`, that is, when the
underlying power series is invertible for substitution, and a strict isomorphism when moreover
`b₁ = 1`.

This file introduces these notions and records the basic consequences of invertibility.

## Main definitions

* `FormalGroupHom F G`: a homomorphism of formal group laws from `F` to `G`, bundled as its
  underlying power series together with the vanishing of its constant coefficient and the
  compatibility condition `α(F(X, Y)) = G(α(X), α(Y))`.
* `FormalGroupIso F G`: an isomorphism of formal group laws from `F` to `G`, bundled as a
  homomorphism `F → G` together with a homomorphism `G → F` inverse to it on both sides.
* `FormalGroupIso.IsStrict`: the property that the coefficient of `X` in an isomorphism is `1`.
* `FormalGroupHom.applyPoint`: the action of a homomorphism `F → G` on points with values in a
  complete linearly topologized `R`-algebra `S`, given by evaluating the underlying power series.
* `FormalGroupHom.toAddMonoidHom`: that action bundled as an additive monoid homomorphism
  `F.Point S →+ G.Point S`.
* `FormalGroupIso.toAddEquiv`: the additive isomorphism `F.Point S ≃+ G.Point S` induced by an
  isomorphism of formal group laws.

## Main results

* `FormalGroupIso.toHom_subst_invHom` and `FormalGroupIso.invHom_subst_toHom`: the power series
  underlying the two halves of an isomorphism are inverse to each other for substitution.
* `FormalGroupIso.ext_iff'`: an isomorphism is determined by the homomorphism `F → G` it
  contains, since the inverse homomorphism is then unique.
* `FormalGroupHom.applyPoint_add`: a homomorphism preserves the formal group addition on points.
* `FormalGroupHom.hasSum_applyPoint`: the value of `φ.applyPoint x` is the sum of the series `φ`
  evaluated at `x`.
* `FormalGroupHom.applyPoint_map`: evaluation at a point commutes with any continuous
  `R`-algebra endomorphism of `S`.

## References

* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section

open PowerSeries HasSubst

variable {R : Type*} [CommRing R] {F G : FormalGroup R}

variable (F G) in
/-- Let $F G$ be two formal group laws over commutative ring $R$. A homomorphism (over $R$)
$F (X, Y) → G (X, Y)$ is a power series $α(X) = b_1 X + b_2 X ^ 2 + ⋯$ with coefficients
in $R$ without constant term such that $α(F (X, Y)) = G (α (X), α (Y))$. -/
@[ext]
structure FormalGroupHom where
  /-- The underlying power series of a formal group homomorphism. -/
  toPowerSeries : PowerSeries R
  /-- Constant coefficient of underlying power series is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The homomorphism condition: $f(F(X,Y))=G(f(X),f(Y))$. -/
  hom : toPowerSeries.subst F = G.toPowerSeries.subst (toPowerSeries.toMvPowerSeries ·)

section FormalGroupIso

variable (F G) in
/-- The homomorphism $α(X) : F (X, Y) → G (X, Y)$ is an isomorphism if there exists a
homomorphism $β(X) : G (X, Y) → F (X, Y)$ such that $α ∘ β = id$ and $β ∘ α = id$. -/
@[ext]
structure FormalGroupIso where
  /-- The underlying formal group homomorphism of a formal group isomorphism. -/
  toHom : FormalGroupHom F G
  /-- The inverse homomorphism of underlying formal group homomorphism. -/
  invHom : FormalGroupHom G F
  /-- `toHom ∘ invHom = id`, i.e. `toHom(invHom(X)) = X`. -/
  left_inv : PowerSeries.subst invHom.toPowerSeries ∘ PowerSeries.subst toHom.toPowerSeries = id
  /-- `invHom ∘ toHom = id`, i.e. `invHom(toHom(X)) = X`. -/
  right_inv : PowerSeries.subst toHom.toPowerSeries ∘ PowerSeries.subst invHom.toPowerSeries = id

@[simp]
lemma FormalGroupIso.toHom_subst_invHom {α : FormalGroupIso F G} :
    α.toHom.toPowerSeries.subst α.invHom.toPowerSeries = X :=
  (subst_comp_eq_id_iff (.of_constantCoeff_zero' α.invHom.zero_constantCoeff)
    (.of_constantCoeff_zero' α.toHom.zero_constantCoeff)).mp α.left_inv

@[simp]
lemma FormalGroupIso.invHom_subst_toHom {α : FormalGroupIso F G} :
    α.invHom.toPowerSeries.subst α.toHom.toPowerSeries = PowerSeries.X :=
  (subst_comp_eq_id_iff (.of_constantCoeff_zero' α.toHom.zero_constantCoeff)
    (.of_constantCoeff_zero' α.invHom.zero_constantCoeff)).mp α.right_inv

/-- An isomorphism $α(X) : F (X, Y) → G (X, Y)$, $α(X) = a_1 X + a_2 X ^ 2 + ⋯$
is called strict isomorphism if $a_1 = 1$. -/
class FormalGroupIso.IsStrict (α : FormalGroupIso F G) : Prop where
  coeff_one : α.toHom.toPowerSeries.coeff 1 = 1

theorem FormalGroupIso.ext_iff' {α β : FormalGroupIso F G} :
    α = β ↔ α.toHom = β.toHom := by
  rw [FormalGroupIso.ext_iff, and_iff_left_iff_imp]
  intro h
  rw [FormalGroupHom.ext_iff, ← (X_subst α.invHom.toPowerSeries), ← β.toHom_subst_invHom,
    ← subst_comp_subst_apply (.of_constantCoeff_zero' β.toHom.zero_constantCoeff)
      (.of_constantCoeff_zero' β.invHom.zero_constantCoeff), ← h, α.invHom_subst_toHom,
      subst_X (.of_constantCoeff_zero' (β.invHom.zero_constantCoeff))]

end FormalGroupIso

section Point

open PowerSeries WithPiTopology

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
  [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S] [Algebra R S]

/-- Evaluating a composite `f(g(X))` of power series evaluates `f` at the value of `g`.

This is the `PowerSeries` counterpart of `MvPowerSeries.eval₂_subst`. -/
lemma _root_.PowerSeries.eval₂_subst [UniformSpace R] [DiscreteUniformity R] {a : S}
    (ha : HasEval a) {g : PowerSeries R} (hg : HasSubst g) (f : PowerSeries R) :
    eval₂ (algebraMap R S) a (f.subst g) =
      eval₂ (algebraMap R S) (eval₂ (algebraMap R S) a g) f := by
  simp [subst_def, eval₂, MvPowerSeries.eval₂_subst hg.const (hasEval ha)]

namespace FormalGroupHom

/-- A homomorphism `φ : F → G` of formal group laws acts on points by evaluation: `φ.applyPoint x`
is the value at `x` of the power series underlying `φ`. Since that power series has zero constant
coefficient, its value at a topologically nilpotent element is again topologically nilpotent, so
this lands in `G.Point S`. -/
noncomputable def applyPoint (φ : FormalGroupHom F G) (x : F.Point S) : G.Point S :=
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  ⟨aeval x.prop φ.toPowerSeries, .map (continuous_aeval x.prop)
    (isTopologicallyNilpotent_of_constantCoeff_zero φ.zero_constantCoeff)⟩

variable (φ : FormalGroupHom F G)

/-- Evaluating a homomorphism at a point commutes with a continuous `R`-algebra endomorphism `ε`
of `S`: the coefficients of `φ` lie in `R` and are therefore fixed by `ε`, and continuity lets `ε`
pass through the sum defining the value. -/
lemma applyPoint_map {ε : S →ₐ[R] S} (hε : Continuous ε) (x : F.Point S) :
    (φ.applyPoint ⟨ε x.val, .map hε x.prop⟩).val = ε (φ.applyPoint x).val := by
  let : UniformSpace R := ⊥
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  exact (DFunLike.congr_fun (comp_aeval x.prop hε) φ.toPowerSeries).symm

variable [UniformSpace R] [DiscreteUniformity R]

@[simp]
lemma applyPoint_eq_eval₂ (x : F.Point S) :
    (φ.applyPoint x).val = eval₂ (algebraMap R S) x.val φ.toPowerSeries := by
  obtain rfl := DiscreteUniformity.eq_bot (X := R)
  let : UniformSpace R := ⊥
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  exact congrFun (coe_aeval x.prop) φ.toPowerSeries

/-- The value of `φ.applyPoint x` is the sum of the series `φ` evaluated at `x`. -/
lemma hasSum_applyPoint (x : F.Point S) :
    HasSum (fun d ↦ coeff d φ.toPowerSeries • x.val ^ d) (φ.applyPoint x).val := by
  obtain rfl := DiscreteUniformity.eq_bot (X := R)
  let : UniformSpace R := ⊥
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  exact hasSum_aeval x.prop φ.toPowerSeries

/-- A homomorphism of formal group laws preserves the formal group addition on points. -/
lemma applyPoint_add (x y : F.Point S) :
    φ.applyPoint (x + y) = φ.applyPoint x + φ.applyPoint y := Subtype.ext <| by
  have he : MvPowerSeries.HasEval ![x.val, y.val] := F.hasEval_point x y
  have hG : MvPowerSeries.HasSubst (fun i : Fin 2 ↦ φ.toPowerSeries.toMvPowerSeries i) :=
    MvPowerSeries.HasSubst.toMvPowerSeries φ.zero_constantCoeff
  calc
    _ = (φ.toPowerSeries.subst F.toPowerSeries).eval₂ _ ![x.val, y.val] := by
      rw [applyPoint_eq_eval₂, eval₂, subst_def, MvPowerSeries.eval₂_subst
        (of_constantCoeff_zero F.zero_constantCoeff).const he, FormalGroup.add_eq_eval₂]
    _ = (φ.applyPoint x + φ.applyPoint y).val := by
      rw [φ.hom, MvPowerSeries.eval₂_subst hG he, FormalGroup.add_eq_eval₂]
      congr 1 with i
      fin_cases i <;>
      simp [toMvPowerSeries_eq_subst, subst_def, MvPowerSeries.eval₂_subst
        (of_constantCoeff_zero _).const he, eval₂]

/-- A homomorphism of formal group laws, as an additive monoid homomorphism on points. -/
@[simps! apply]
noncomputable def toAddMonoidHom : F.Point S →+ G.Point S :=
  AddMonoidHom.mk' φ.applyPoint φ.applyPoint_add

@[simp]
lemma applyPoint_zero : φ.applyPoint (0 : F.Point S) = 0 :=
  map_zero φ.toAddMonoidHom

@[simp]
lemma applyPoint_neg (x : F.Point S) : φ.applyPoint (-x) = -φ.applyPoint x :=
  map_neg φ.toAddMonoidHom x

end FormalGroupHom

namespace FormalGroupIso

variable (α : FormalGroupIso F G) [UniformSpace R] [DiscreteUniformity R]

/-- An isomorphism of formal group laws induces an additive isomorphism on points, with inverse
induced by the inverse homomorphism. -/
@[simps! apply]
noncomputable def toAddEquiv : F.Point S ≃+ G.Point S where
  toFun := α.toHom.applyPoint
  invFun := α.invHom.applyPoint
  left_inv x := Subtype.ext <| by
    rw [FormalGroupHom.applyPoint_eq_eval₂, FormalGroupHom.applyPoint_eq_eval₂,
      ← eval₂_subst x.prop (HasSubst.of_constantCoeff_zero' α.toHom.zero_constantCoeff),
      α.invHom_subst_toHom, eval₂_X]
  right_inv y := Subtype.ext <| by
    rw [FormalGroupHom.applyPoint_eq_eval₂, FormalGroupHom.applyPoint_eq_eval₂,
      ← eval₂_subst y.prop (HasSubst.of_constantCoeff_zero' α.invHom.zero_constantCoeff),
      α.toHom_subst_invHom, eval₂_X]
  map_add' := α.toHom.applyPoint_add

@[simp]
lemma toAddEquiv_symm_apply (y : G.Point S) : α.toAddEquiv.symm y = α.invHom.applyPoint y := rfl

end FormalGroupIso

end Point

open MvPowerSeries
