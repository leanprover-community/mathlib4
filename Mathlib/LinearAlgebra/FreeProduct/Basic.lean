/-
Copyright (c) 2024 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# The free product of $R$-algebras

We define the free product of an indexed collection of (noncommutative) $R$-algebras
`(i : ι) → A i`, with `Algebra R (A i)` for all `i` and `R` a commutative
semiring, as the quotient of the tensor algebra on the direct sum
`⨁ (i : ι), A i` by the relation generated by extending the relation

* `aᵢ ⊗ₜ aᵢ' ~ aᵢ aᵢ'` for all `i : ι` and `aᵢ aᵢ' : A i`
* `1ᵢ ~ 1ⱼ` for `1ᵢ := One.one (A i)` and for all `i, j : ι`.

to the whole tensor algebra in an `R`-linear way.

The main result of this file is the universal property of the free product,
which establishes the free product as the coproduct in the category of
general $R$-algebras. (In the category of commutative $R$-algebras, the coproduct
is just `PiTensorProduct`.)

## Main definitions

* `FreeProduct R A` is the free product of the `R`-algebras `A i`, defined as a quotient
  of the tensor algebra on the direct sum of the `A i`.
* `FreeProduct_ofPowers R A` is the free product of the `R`-algebras `A i`, defined as a quotient
  of the (infinite) direct sum of tensor powers of the `A i`.
* `lift` is the universal property of the free product.

## Main results

* `equivPowerAlgebra` establishes an equivalence between `FreeProduct R A` and
  `FreeProduct_ofPowers R A`.
* `FreeProduct` is the coproduct in the category of `R`-algebras.

## TODO
- Induction principle for `FreeProduct`

-/
universe u v w w'

namespace DirectSum
open scoped DirectSum

/--A variant of `DirectSum.induction_on` that uses `DirectSum.lof` instead of `.of`-/
theorem induction_lon {R : Type*} [Semiring R] {ι: Type*} [DecidableEq ι]
    {M : ι → Type*} [(i: ι) → AddCommMonoid <| M i] [(i : ι) → Module R (M i)]
    {C: (⨁ i, M i) → Prop} (x : ⨁ i, M i)
    (H_zero : C 0)
    (H_basic : ∀ i (x : M i), C (lof R ι M i x))
    (H_plus : ∀ (x y : ⨁ i, M i), C x → C y → C (x + y)) : C x := by
  induction x using DirectSum.induction_on with
  | H_zero => exact H_zero
  | H_basic => exact H_basic _ _
  | H_plus x y hx hy => exact H_plus x y hx hy

end DirectSum

namespace RingQuot
universe uS uA uB

open scoped Function -- required for scoped `on` notation

/--If two `R`-algebras are `R`-equivalent and their quotients by a relation `rel` are defined,
then their quotients are also `R`-equivalent.

(Special case of the third isomorphism theorem.)-/
def algEquiv_quot_algEquiv
    {R : Type u} [CommSemiring R] {A B : Type v} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) (rel : A → A → Prop) :
    RingQuot rel ≃ₐ[R] RingQuot (rel on f.symm) :=
  AlgEquiv.ofAlgHom
    (RingQuot.liftAlgHom R (s := rel)
      ⟨AlgHom.comp (RingQuot.mkAlgHom R (rel on f.symm)) f,
      fun x y h_rel ↦ by
        apply RingQuot.mkAlgHom_rel
        simpa [Function.onFun]⟩)
    ((RingQuot.liftAlgHom R (s := rel on f.symm)
      ⟨AlgHom.comp (RingQuot.mkAlgHom R rel) f.symm,
      fun x y h ↦ by apply RingQuot.mkAlgHom_rel; simpa⟩))
    (by ext b; simp) (by ext a; simp)

/--If two (semi)rings are equivalent and their quotients by a relation `rel` are defined,
then their quotients are also equivalent.

(Special case of `algEquiv_quot_algEquiv` when `R = ℕ`, which in turn is a special
case of the third isomorphism theorem.)-/
def equiv_quot_equiv {A B : Type v} [Semiring A] [Semiring B] (f : A ≃+* B) (rel : A → A → Prop)  :
    RingQuot rel ≃+* RingQuot (rel on f.symm) :=
  let f_alg : A ≃ₐ[ℕ] B :=
    AlgEquiv.ofRingEquiv (f := f) (fun n ↦ by simp)
  algEquiv_quot_algEquiv f_alg rel |>.toRingEquiv

end RingQuot

open TensorAlgebra DirectSum TensorPower

variable {I : Type u} [DecidableEq I] {i : I} -- The type of the indexing set
  (R : Type v) [CommSemiring R] -- The commutative semiring `R`
  (A : I → Type w) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] -- The collection of `R`-algebras
  {B : Type w'} [Semiring B] [Algebra R B] -- Another `R`-algebra
  (maps : {i : I} → A i →ₐ[R] B) -- A family of `R`algebra homomorphisms

namespace LinearAlgebra.FreeProduct

instance : Module R (⨁ i, A i) := by infer_instance

/--The free tensor algebra over a direct sum of `R`-algebras, before
taking the quotient by the free product relation.-/
abbrev FreeTensorAlgebra := TensorAlgebra R (⨁ i, A i)

/--The direct sum of tensor powers of a direct sum of `R`-algebras,
before taking the quotient by the free product relation.-/
abbrev PowerAlgebra := ⨁ (n : ℕ), TensorPower R n (⨁ i, A i)

/--The free tensor algebra and its representation as an infinite direct sum
of tensor powers are (noncomputably) equivalent as `R`-algebras.-/
@[reducible] noncomputable def powerAlgebra_equiv_freeAlgebra :
    PowerAlgebra R A ≃ₐ[R] FreeTensorAlgebra R A :=
  TensorAlgebra.equivDirectSum.symm

/--The generating equivalence relation for elements of the free tensor algebra
that are identified in the free product.-/
inductive rel : FreeTensorAlgebra R A → FreeTensorAlgebra R A → Prop
  | id  : ∀ {i : I}, rel (ι R <| lof R I A i 1) 1
  | prod : ∀ {i : I} {a₁ a₂ : A i},
      rel
        (tprod R (⨁ i, A i) 2 (fun | 0 => lof R I A i a₁ | 1 => lof R I A i a₂))
        (ι R <| lof R I A i (a₁ * a₂))

open scoped Function -- required for scoped `on` notation

/--The generating equivalence relation for elements of the power algebra
that are identified in the free product. -/
@[reducible, simp] def rel' := rel R A on ofDirectSum

theorem rel_id (i : I) : rel R A (ι R <| lof R I A i 1) 1 := rel.id


/--The free product of the collection of `R`-algebras `A i`, as a quotient of
`FreeTensorAlgebra R A`.-/
@[reducible] def _root_.LinearAlgebra.FreeProduct := RingQuot <| FreeProduct.rel R A

/--The free product of the collection of `R`-algebras `A i`, as a quotient of `PowerAlgebra R A`-/
@[reducible] def _root_.LinearAlgebra.FreeProduct_ofPowers := RingQuot <| FreeProduct.rel' R A

/--The `R`-algebra equivalence relating `FreeProduct` and `FreeProduct_ofPowers`-/
noncomputable def equivPowerAlgebra : FreeProduct_ofPowers R A ≃ₐ[R] FreeProduct R A :=
  RingQuot.algEquiv_quot_algEquiv
    (FreeProduct.powerAlgebra_equiv_freeAlgebra R A |>.symm) (FreeProduct.rel R A)
  |>.symm

open RingQuot Function

local infixr:60 " ∘ₐ " => AlgHom.comp

instance instSemiring : Semiring (FreeProduct R A) := by infer_instance
instance instAlgebra : Algebra R (FreeProduct R A) := by infer_instance

/--The canonical quotient map `FreeTensorAlgebra R A →ₐ[R] FreeProduct R A`,
as an `R`-algebra homomorphism.-/
abbrev mkAlgHom : FreeTensorAlgebra R A →ₐ[R] FreeProduct R A :=
  RingQuot.mkAlgHom R (rel R A)

/--The canonical linear map from the direct sum of the `A i` to the free product.-/
abbrev ι' : (⨁ i, A i) →ₗ[R] FreeProduct R A :=
  (mkAlgHom R A).toLinearMap ∘ₗ TensorAlgebra.ι R (M := ⨁ i, A i)

@[simp] theorem ι_apply (x : ⨁ i, A i) :
  ⟨Quot.mk (Rel <| rel R A) (TensorAlgebra.ι R x)⟩ = ι' R A x := by
    aesop (add simp [ι', mkAlgHom, RingQuot.mkAlgHom, mkRingHom])

/--The injection into the free product of any `1 : A i` is the 1 of the free product.-/
theorem identify_one (i : I) : ι' R A (DirectSum.lof R I A i 1) = 1 := by
  suffices ι' R A (DirectSum.lof R I A i 1) = mkAlgHom R A 1 by simpa
  exact RingQuot.mkAlgHom_rel R <| rel_id R A (i := i)

/--Multiplication in the free product of the injections of any two `aᵢ aᵢ': A i` for
the same `i` is just the injection of multiplication `aᵢ * aᵢ'` in `A i`.-/
theorem mul_injections (a₁ a₂ : A i) :
    ι' R A (DirectSum.lof R I A i a₁) * ι' R A (DirectSum.lof R I A i a₂)
      = ι' R A (DirectSum.lof R I A i (a₁ * a₂)) := by
  convert RingQuot.mkAlgHom_rel R <| rel.prod
  aesop

/--The `i`th canonical injection, from `A i` to the free product, as
a linear map.-/
abbrev lof (i : I) : A i →ₗ[R] FreeProduct R A :=
  ι' R A ∘ₗ DirectSum.lof R I A i

/--`lof R A i 1 = 1` for all `i`.-/
theorem lof_map_one (i : I) : lof R A i 1 = 1 := by
  rw [lof]; dsimp [mkAlgHom]; exact identify_one R A i

/--The `i`th canonical injection, from `A i` to the free product.-/
irreducible_def ι (i : I) : A i →ₐ[R] FreeProduct R A :=
  AlgHom.ofLinearMap (ι' R A ∘ₗ DirectSum.lof R I A i)
    (lof_map_one R A i) (mul_injections R A · · |>.symm)

/--The family of canonical injection maps, with `i` left implicit.-/
irreducible_def of {i : I} : A i →ₐ[R] FreeProduct R A := ι R A i


/--Universal property of the free product of algebras:
for every `R`-algebra `B`, every family of maps `maps : (i : I) → (A i →ₐ[R] B)` lifts
to a unique arrow `π` from `FreeProduct R A` such that  `π ∘ ι i = maps i`.-/
@[simps] def lift : ({i : I} → A i →ₐ[R] B) ≃ (FreeProduct R A →ₐ[R] B) where
  toFun maps :=
    RingQuot.liftAlgHom R ⟨
        TensorAlgebra.lift R <|
          DirectSum.toModule R I B <|
            (@maps · |>.toLinearMap),
        fun x y r ↦ by
          cases r with
          | id => simp
          | prod => simp⟩
  invFun π i := π ∘ₐ ι R A i
  left_inv π := by
    ext i aᵢ
    aesop (add simp [ι, ι'])
  right_inv maps := by
    ext i a
    aesop (add simp [ι, ι'])

/--Universal property of the free product of algebras, property:
for every `R`-algebra `B`, every family of maps `maps : (i : I) → (A i →ₐ[R] B)` lifts
to a unique arrow `π` from `FreeProduct R A` such that  `π ∘ ι i = maps i`.-/
theorem lift_comp_ι : (lift R A maps) ∘ₐ (ι R A i) = maps := by
  ext a
  simp [lift_apply, ι]

@[aesop safe destruct] theorem lift_unique
    (f : FreeProduct R A →ₐ[R] B) (h : ∀ i, f ∘ₐ ι R A i = maps) :
    f = lift R A maps := by
  ext i a; simp_rw [AlgHom.ext_iff] at h; specialize h i a
  simp [h.symm, ι]

end LinearAlgebra.FreeProduct
