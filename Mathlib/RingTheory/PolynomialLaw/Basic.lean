/-
Copyright (c) 2025 Antoine Chambert-Loir & María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir & María-Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial law `f : PolynomialLaw R M N`, with notation `f : M →ₚₗₗ[R] N`,
is a “law” that assigns a natural map `PolynomialLaw.toFun' f S : S ⊗[R] M → S ⊗[R] N`
for every `R`-algebra `S`.

For type-theoretic reasons, if `R : Type u`, then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit of its finitely generated submodules, that a
finitely generated subalgebra is a quotient of a polynomial ring in the universe `u`, plus
the commutation of tensor products with direct limits, we extend the functor
to all `R`-algebras.

The two fields involving the definition of `PolynomialLaw`,
`PolynomialLaw.toFun'` and `PolynomialLaw.isCompat'` are primed.
They are superseded by their universe-polymorphic counterparts,
the definition `PolynomialLaw.toFun` and the lemma `PolynomialLaw.isCompat`
which should be used once the theory is properly stated.

For constructions of general definitions of `PolynomialLaw`
at a universe-polymorphic level, one needs to lift
elements in a tensor product to smaller universes.
For this, one can make use of
`PolynomialLaw.exists_lift` or `PolynomialLaw.exists_lift'`,
or establish appropriate generalizations.

## Main definitions/lemmas

* Instance : `Module R (M →ₚₗ[R] N)` shows that polynomial laws form an `R`-module.

* `PolynomialLaw.ground f` is the map `M → N` corresponding to `PolynomialLaw.toFun' f R` under
  the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further works, we construct the coefficients of a polynomial law and show the relation with
polynomials (when the module `M` is free and finite).

## Implementation notes

In the literature, the theory is written for commutative rings, but this implementation
only assumes `R` is a commutative semiring.

## References

* [Roby, Norbert. 1963. «Lois polynomes et lois formelles en théorie des modules».
Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348](Roby-1963)

-/

@[expose] public section

universe u v w

noncomputable section PolynomialLaw

open scoped TensorProduct

open LinearMap TensorProduct AlgHom RingCon

/-- A polynomial law `M →ₚₗ[R] N` between `R`-modules is a functorial family of maps
`S ⊗[R] M → S ⊗[R] N`, for all `R`-algebras `S`.

For universe reasons, `S` has to be restricted to the same universe as `R`. -/
@[ext]
structure PolynomialLaw (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] (N : Type*) [AddCommMonoid N] [Module R N] where
  /-- The functions `S ⊗[R] M → S ⊗[R] N` underlying a polynomial law -/
  toFun' (S : Type u) [CommSemiring S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  /-- The compatibility relations between the functions underlying a polynomial law -/
  isCompat' {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M := by aesop

/-- `M →ₚₗ[R] N` is the type of `R`-polynomial laws from `M` to `N`. -/
notation:25 M " →ₚₗ[" R:25 "] " N:0 => PolynomialLaw R M N

@[local simp]
theorem PolynomialLaw.isCompat_apply'
    {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N] {f : M →ₚₗ[R] N}
    {S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun' S) x) = (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using congr_fun (f.isCompat' φ) x

attribute [local simp] PolynomialLaw.isCompat_apply'

namespace PolynomialLaw

section Module

section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (r a b : R) (f g : M →ₚₗ[R] N)

instance : Zero (M →ₚₗ[R] N) := ⟨{ toFun' _ := 0 }⟩

@[simp]
theorem zero_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (0 : PolynomialLaw R M N).toFun' S = 0 := rfl

instance : Inhabited (PolynomialLaw R M N) := ⟨Zero.zero⟩

/-- The identity as a polynomial law -/
def id : M →ₚₗ[R] M where
  toFun' S _ _ := _root_.id

theorem id_apply' {S : Type u} [CommSemiring S] [Algebra R S] :
    (id : M →ₚₗ[R] M).toFun' S = _root_.id := rfl

/-- The sum of two polynomial laws -/
noncomputable def add : M →ₚₗ[R] N where
  toFun' S _ _ := f.toFun' S + g.toFun' S

instance : Add (PolynomialLaw R M N) := ⟨add⟩

@[simp]
theorem add_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl

theorem add_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl

/-- External multiplication of a `f : M →ₚₗ[R] N` by `r : R` -/
def smul : M →ₚₗ[R] N where
  toFun' S _ _ := r • f.toFun' S

instance : SMul R (M →ₚₗ[R] N) := ⟨smul⟩

@[simp]
theorem smul_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S := rfl

theorem smul_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (r • f).toFun' S m = r • f.toFun' S m := rfl

theorem add_smul : (a + b) • f = a • f + b • f := by
  ext; simp only [add_def, smul_def, _root_.add_smul]

theorem zero_smul : (0 : R) • f = 0 := by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

theorem one_smul : (1 : R) • f = f := by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]

instance : MulAction R (M →ₚₗ[R] N) where
  one_smul := one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

instance : AddCommMonoid (M →ₚₗ[R] N) where
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ n f := by simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

instance : Module R (M →ₚₗ[R] N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M →ₚₗ[R] N)

/-- The opposite of a polynomial law -/
noncomputable def neg : M →ₚₗ[R] N where
  toFun' S _ _ := (-1 : R) • f.toFun' S

instance : Neg (M →ₚₗ[R] N) := ⟨neg⟩

@[simp]
theorem neg_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (-f).toFun' S = (-1 : R) • f.toFun' S := rfl

instance : AddCommGroup (M →ₚₗ[R] N) where
  zsmul n f := (n : R) • f
  zsmul_zero' f := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast,
    Int.cast_one, add_smul, _root_.one_smul]
  zsmul_neg' n f := by
    ext S _ _ m
    rw [neg_def]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, _root_.add_smul,
      add_def_apply, smul_def_apply, Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast,
      Int.cast_one, _root_.one_smul, add_def, smul_def, Pi.smul_apply, Pi.add_apply, smul_add,
      smul_smul, neg_mul, one_mul]
    rw [add_comm]
  neg_add_cancel f := by
    ext S _ _ m
    simp only [add_def_apply, neg_def, Pi.smul_apply, zero_def, Pi.zero_apply]
    nth_rewrite 2 [← _root_.one_smul (M := R) (b := f.toFun' S m)]
    rw [← _root_.add_smul]
    simp only [neg_add_cancel, _root_.zero_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

end CommRing

end Module

section ground

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
variable (f : M →ₚₗ[R] N)

/-- The map `M → N` associated with a `f : M →ₚₗ[R] N` (essentially, `f.toFun' R`) -/
def ground : M → N := (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

theorem ground_apply (m : M) : f.ground m = TensorProduct.lid R N (f.toFun' R (1 ⊗ₜ[R] m)) := rfl

instance : CoeFun (M →ₚₗ[R] N) (fun _ ↦ M → N) where
  coe := ground

theorem one_tmul_ground_apply' {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  rw [ground_apply]
  convert f.isCompat_apply' (Algebra.algHom R R S) (1 ⊗ₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

/-- The map ground assigning a function `M → N` to a polynomial map `f : M →ₚₗ[R] N` as a
  linear map. -/
def lground : (M →ₚₗ[R] N) →ₗ[R] (M → N) where
  toFun := ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]

theorem ground_id : (id : M →ₚₗ[R] M).ground = _root_.id := by
  ext; simp [ground_apply, id_apply']

theorem ground_id_apply (m : M) : (id : M →ₚₗ[R] M).ground m = m := by
  rw [ground_id, id_eq]

end ground

section Composition

variable {R : Type u} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
variable (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Composition of polynomial maps. -/
def comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : M →ₚₗ[R] P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']

theorem comp_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl

theorem comp_assoc : h.comp (g.comp f) = (h.comp g).comp f := rfl

theorem comp_id : g.comp id = g := by ext; rfl

theorem id_comp : id.comp f = f := by ext; rfl

end Composition

section Universe

open scoped TensorProduct

open MvPolynomial

variable (R : Type u) [CommSemiring R]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N]
  (S : Type v) [CommSemiring S] [Algebra R S]
  (f : M →ₚₗ[R] N)

section Lift

open LinearMap

-- The universe of `PolynomialLaw.lifts` is computed by the compiler
/-- The type of lifts of  `S ⊗[R] M` to a polynomial ring. -/
def lifts : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M


variable {S}

/-- The lift of `f.toFun to the type `lifts` -/
def φ (s : Finset S) : MvPolynomial (Fin s.card) R →ₐ[R] S :=
  aeval (R := R) (fun n ↦ (s.equivFin.symm n : S))

theorem range_φ (s : Finset S) : (φ R s).range = Algebra.adjoin R s := by
  simp only [φ]
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr
  rw [← Function.comp_def, Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOf_mem]

variable (S)

/-- The projection from `φ` to `S ⊗[R] M`. -/
def π : lifts R M S → S ⊗[R] M := fun ⟨s, p⟩ ↦ rTensor M (φ R s).toLinearMap p

variable {R M N}

/-- The auxiliary lift of `PolynomialLaw.toFun'` on `PolynomialLaw.lifts` -/
def toFunLifted : lifts R M S → S ⊗[R] N :=
  fun ⟨s, p⟩ ↦ rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

/-- The extension of `PolynomialLaw.toFun'` to all universes. -/
def toFun : S ⊗[R] M → S ⊗[R] N := Function.extend (π R M S) (f.toFunLifted S) (fun _ ↦ 0)

variable {S}

theorem exists_range_φ_eq_of_fg {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    ∃ s : Finset S, (φ R s).range = B :=
  ⟨hB.choose, by simp only [range_φ, hB.choose_spec]⟩

section diagrams

variable
    {A : Type u} [CommSemiring A] [Algebra R A] {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {T : Type w} [CommSemiring T] [Algebra R T]
    {B : Type u} [CommSemiring B] [Algebra R B] {ψ : B →ₐ[R] T} (q : B ⊗[R] M)
    (g : A →ₐ[R] B) (h : S →ₐ[R] T)

/-- Compare the values of `PolynomialLaw.toFun' in a square diagram -/
theorem toFun'_eq_of_diagram
    (h : S →ₐ[R] T) (h' : φ.range →ₐ[R] ψ.range)
    (hh' : ψ.range.val.comp h' = h.comp φ.range.val)
    (hpq : (h'.comp φ.rangeRestrict).toLinearMap.rTensor M p =
      ψ.rangeRestrict.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) =
      ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  let θ := (quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((quotientKerEquivRangeₐ ψ).toAlgHom.comp θ) := by
    simp only [θ, ← AlgHom.comp_assoc, ← hh']
    simp [AlgHom.comp_assoc]
  rw [← φ.val_comp_rangeRestrict, ← quotientKerEquivRangeₐ_comp_mkₐ φ,
    ← ψ.val_comp_rangeRestrict, ← quotientKerEquivRangeₐ_comp_mkₐ ψ,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc _, ht]
  simp only [AlgHom.comp_toLinearMap, rTensor_comp_apply]
  apply congr_arg
  rw [← rTensor_comp_apply, ← AlgHom.comp_toLinearMap, isCompat_apply',
    isCompat_apply', AlgHom.comp_toLinearMap, rTensor_comp_apply,
    isCompat_apply']
  apply congr_arg
  simp only [θ, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, AlgHom.comp_assoc]
  rw [quotientKerEquivRangeₐ_comp_mkₐ, comp_toLinearMap,
    rTensor_comp_apply, hpq, ← rTensor_comp_apply, ← comp_toLinearMap,
    ← quotientKerEquivRangeₐ_comp_mkₐ, ← AlgHom.comp_assoc]
  simp

/-- Compare the values of `PolynomialLaw.toFun' in a square diagram,
  when one of the maps is a subalgebra inclusion. -/
theorem toFun'_eq_of_inclusion {ψ : B →ₐ[R] S} (h : φ.range ≤ ψ.range)
    (hpq : ((Subalgebra.inclusion h).comp
      φ.rangeRestrict).toLinearMap.rTensor M p = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    φ.toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) :=
  toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

end diagrams

theorem factorsThrough_toFunLifted_π :
    Function.FactorsThrough (f.toFunLifted S) (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
    -- (Algebra.FiniteType.mvPolynomial R (Fin s.card)).out
  set u' := rTensor M (φ R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φ R s').range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
    -- (Algebra.FiniteType.mvPolynomial R (Fin s'.card)).out
  have huu' : rTensor M (Subalgebra.val _).toLinearMap u =
    rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [π] at h
    simp only [hu, hu', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap,
      val_comp_rangeRestrict, h]
  obtain ⟨B, hAB, hA'B, ⟨t, hB⟩, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u'FG huu'
  rw [← range_φ R t, eq_comm] at hB
  have hAB' : (φ R s).range ≤ (φ R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φ R s').range ≤ (φ R t).range := le_trans hA'B (le_of_eq hB)
  have : ∃ q : MvPolynomial (Fin t.card) R ⊗[R] M, rTensor M (toLinearMap (φ R t).rangeRestrict) q =
      rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp
        (Subalgebra.inclusion hAB)).toLinearMap u :=
    rTensor_surjective _ (rangeRestrict_surjective _) _
  obtain ⟨q, hq⟩ := this
  rw [toFun'_eq_of_inclusion f p q hAB', toFun'_eq_of_inclusion f p' q hA'B']
  · simp only [hq, comp_toLinearMap, rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  · simp only [hq, hu, ← LinearMap.comp_apply, comp_toLinearMap, rTensor_comp]
    congr; ext; rfl

theorem toFun_eq_rTensor_φ_toFun' {t : S ⊗[R] M} {s : Finset S}
    {p : MvPolynomial (Fin s.card) R ⊗[R] M} (ha : π R M S (⟨s, p⟩ : lifts R M S) = t) :
    f.toFun S t = (φ R s).toLinearMap.rTensor N (f.toFun' _ p) := by
  rw [PolynomialLaw.toFun, ← ha, (factorsThrough_toFunLifted_π f).extend_apply, toFunLifted]

theorem exists_lift_of_mem_range_rTensor
    {T : Type*} [CommSemiring T] [Algebra R T]
    (A : Subalgebra R T) {φ : S →ₐ[R] T} (hφ : A ≤ φ.range) {t : T ⊗[R] M}
    (ht : t ∈ range ((Subalgebra.val A).toLinearMap.rTensor M)) :
    ∃ s : S ⊗[R] M, φ.toLinearMap.rTensor M s = t := by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj : Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu, ← Subalgebra.val_comp_inclusion hφ, comp_toLinearMap, rTensor_comp,
      LinearMap.comp_apply, ← hp, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  exact rTensor_surjective M (rangeRestrict_surjective φ)

/-- Tensor products in `S ⊗[R] M` can be lifted to some
`MvPolynomial R n ⊗[R] M`, for a finite `n`. -/
theorem π_surjective : Function.Surjective (π R M S) := by
  classical
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t ∈ range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := exists_range_φ_eq_of_fg hB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, hp⟩

/-- Lift an element of a tensor product -/
theorem exists_lift (t : S ⊗[R] M) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M), ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

/-- Lift an element of a tensor product and a scalar -/
theorem exists_lift' (t : S ⊗[R] M) (s : S) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M) (q : MvPolynomial (Fin n) R),
      ψ.toLinearMap.rTensor M p = t ∧ ψ q = s := by
  classical
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.FG.sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := exists_range_φ_eq_of_fg hB
  have hAB : A ≤ A ⊔ Algebra.adjoin R ({s} : Finset S) := le_sup_left
  rw [← hgen] at hAB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor _ hAB ht
  have hs : s ∈ (φ R gen).range := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    exact Or.inr (Algebra.subset_adjoin rfl)
  use gen.card, φ R gen, p, hs.choose, hp, hs.choose_spec

/-- For semirings in the universe `u`, `PolynomialLaw.toFun` coincides
with `PolynomialLaw.toFun'`. -/
@[simp]
theorem toFun'_eq_toFun (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun' S = f.toFun S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_rTensor_φ_toFun' ha, f.isCompat_apply']
  exact congr_arg _ ha.symm

/-- Extends `PolynomialLaw.isCompat_apply'` to all universes. -/
theorem isCompat_apply {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) (t : S ⊗[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range →ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [range_φ] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, Finset.coe_image,
      Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)
  let j : Fin s.card → Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ ↦ ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φ R s').comp (rename j) = h.comp (φ R s) := by
    ext p
    simp only [φ, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp only [Function.comp_apply, Equiv.symm_apply_apply, j]
  let p' := rTensor M (rename j).toLinearMap p
  have ha' : π R M T (⟨s', p'⟩ : lifts R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, eq_h_comp]
  rw [toFun_eq_rTensor_φ_toFun' f ha, toFun_eq_rTensor_φ_toFun' f ha', ← LinearMap.comp_apply,
    ← rTensor_comp, ← comp_toLinearMap]
  apply toFun'_eq_of_diagram f p p' h h'
  · simp only [val_comp_codRestrict, h']
  · simp only [p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    congr
    ext n
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_codRestrict,
      Subalgebra.coe_val, rename_X, h', j]
    simp only [φ, aeval_X, Equiv.symm_apply_apply]

/-- Extends `PolynomialLaw.isCompat` to all universes -/
theorem isCompat {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

end Lift

section Module

variable
  {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (r a b : R) (f g : M →ₚₗ[R] N)
  {S : Type*} [CommSemiring S] [Algebra R S]

/-- Extension of `PolynomialLaw.zero_def` -/
@[simp]
theorem toFun_zero : (0 : M →ₚₗ[R] N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

/-- Extension of `PolynomialLaw.add_def_apply` -/
@[simp]
theorem toFun_add_apply (t : S ⊗[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_rTensor_φ_toFun' _ ha, add_def, map_add]

/-- Extension of `PolynomialLaw.add_def` -/
@[simp]
theorem toFun_add :
    (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, toFun_add_apply]

@[simp]
theorem toFun_neg {R : Type u} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    (-f).toFun S = (-1 : R) • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, neg_def, Pi.smul_apply, map_smul]

variable (S) in
/-- Extension of `PolynomialLaw.smul_def` -/
@[simp]
theorem toFun_smul : (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, smul_def, Pi.smul_apply, map_smul]

end Module

section ground

variable {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S]

theorem one_tmul_ground (x : M) :
    1 ⊗ₜ f.ground x = f.toFun S (1 ⊗ₜ x) := by
  simp only [ground, toFun'_eq_toFun]
  convert f.isCompat_apply (Algebra.ofId R S) (1 ⊗ₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

end ground

section Comp

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Extension of `MvPolynomial.comp_toFun'` -/
@[simp]
theorem toFun_comp (S : Type*) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_rTensor_φ_toFun' _ ha, π]
  rw [Function.comp_apply, toFun_eq_rTensor_φ_toFun' _ hb, toFun_eq_rTensor_φ_toFun' _ ha,
    comp_toFun', Function.comp_apply]

theorem toFun_comp_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := by
  simp only [toFun_comp, Function.comp_apply]

end Comp

end Universe

end PolynomialLaw
