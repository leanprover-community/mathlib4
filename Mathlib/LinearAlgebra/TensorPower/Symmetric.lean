/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.SymmetricMap
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Tactic.SuppressCompilation

public import Mathlib.Algebra.Module.Congruence.Defs

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `ι`-indexed symmetric tensor power of `M` as the `PiTensorProduct` quotiented by
the relation that the `tprod` of `ι` elements is equal to the `tprod` of the same elements permuted
by a permutation of `ι`. We denote this space by `Sym[R] ι M`, and the canonical multilinear map
from `ι → M` to `Sym[R] ι M` by `⨂ₛ[R] i, f i`. We also reserve the notation `Sym[R]^n M` for the
`n`th symmetric tensor power of `M`, which is the symmetric tensor power indexed by `Fin n`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogeneous (multivariate) polynomials of degree `n`.

-/

@[expose] public section

suppress_compilation
universe u v


--------------------------------------------------------------------------------
namespace ModuleConGen

variable {R : Type u} {M : Type v} [Semiring R] [AddZeroClass M] [SMul R M]

/-- The inductively defined smallest congruence relation compatible with a module structure
containing a given binary relation. -/
inductive Rel (r : M → M → Prop) : M → M → Prop
  | of {x y} : r x y → Rel r x y
  | refl {x} :  Rel r x x
  | symm {x y} : Rel r x y → Rel r y x
  | trans {x y z} : Rel r x y → Rel r y z → Rel r x z
  | add {w x y z} : Rel r w x → Rel r y z → Rel r (w + y) (x + z)
  | smul  (s : R) {x y : M} :  Rel r x y → Rel r (s • x) (s • y)

end ModuleConGen

variable {R : Type u} {M : Type v} [Semiring R]
def moduleConGen [AddZeroClass M] [SMul R M] (r : M → M → Prop) : ModuleCon R M :=
 { r := ModuleConGen.Rel r
   iseqv := {
     refl := fun _ => .refl
     symm := .symm
     trans := .trans
     }
   add' := .add
   smul := .smul
   }

--------------------------------------------------------------------------------
namespace ModuleCon

/-- The homomorphism on the quotient of an R-module by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
def lift {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : ModuleCon R M) {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (H : ∀ a b, c.r a b → f a = f b) :
    ModuleCon.Quotient M c →ₗ[R] N where
  toFun x := Quotient.liftOn x f H
  map_add' x y := Quotient.inductionOn₂ x y fun m n => map_add f m n
  map_smul' r x := Quotient.inductionOn x fun m => map_smul f r m

def mk' {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : ModuleCon R M) : M →ₗ[R] c.Quotient where
  toFun := AddCon.mk' c.toAddCon
  map_add' := (AddCon.mk' c.toAddCon).map_add
  map_smul' _ _ := rfl

theorem eq {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    {c : ModuleCon R M} {x y : M} :
    c.mk' x = c.mk' y ↔ c.r x y :=
  AddCon.eq c.toAddCon

theorem lift_mk' {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : ModuleCon R M) {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (H : ∀ a b, c.r a b → f a = f b) (x : M) :
    ModuleCon.lift c f H (c.mk' x) = f x :=
  rfl

theorem mk'_surjective
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (c : ModuleCon R M) : Function.Surjective c.mk' :=
  letI : Setoid M := c.toAddCon.toSetoid
  Quotient.mk'_surjective

end ModuleCon

--------------------------------------------------------------------------------

open TensorProduct Equiv

variable (R ι : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (s : ι → M)

/-- The relation on the `ι`-indexed tensor power of `M` where two tensors are equal
if they are related by a permutation of `ι`. -/
inductive SymmetricPower.Rel : (⨂[R] _, M) → (⨂[R] _, M) → Prop
  | perm : (e : Perm ι) → (f : ι → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

def SymmetricCon : ModuleCon R (⨂[R] (_ : ι), M) :=
    moduleConGen (R := R) (SymmetricPower.Rel R ι M)

/-- The `ι`-indexed symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `ι`-indexed tensor power of `M` by the relation that two tensors are equal
if they are related by a permutation of `ι`. -/
def SymmetricPower : Type max u v :=
 (SymmetricCon R ι M).Quotient

instance : AddCommMonoid (SymmetricPower R ι M) :=
  show AddCommMonoid (SymmetricCon R ι M).Quotient from inferInstance

instance : Module R (SymmetricPower R ι M) :=
  show Module R (SymmetricCon R ι M).Quotient from inferInstance

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

/-- The `n`th symmetric tensor power of a semimodule `M` over a commutative semiring `R` -/
scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => Sym[R] (Fin n) M

namespace SymmetricPower

/-- The canonical map from the `ι`-indexed tensor power to the symmetric tensor power. -/
def mk : (⨂[R] (_ : ι), M) →ₗ[R] Sym[R] ι M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M ι} in
/-- The multilinear map that takes `ι`-indexed elements of `M` and
returns their symmetric tensor power. Denoted `⨂ₛ[R] i, f i`. -/
def tprod : MultilinearMap R (fun _ : ι ↦ M) Sym[R] ι M :=
  (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R ι M} in
@[simp] lemma tprod_equiv (e : Perm ι) (f : ι → M) :
    (⨂ₛ[R] i, f (e i)) = ⨂ₛ[R] i, f i :=
  Eq.symm <| Quot.sound <| ModuleConGen.Rel.of <| Rel.perm e f

variable {R M n} in
@[simp] lemma domDomCongr_tprod (e : Perm ι) :
    (tprod R (ι := ι) (M := M)).domDomCongr e = tprod R :=
  MultilinearMap.ext <| tprod_equiv e

theorem range_mk : LinearMap.range (mk R ι M) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor power. -/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤ := by
  rw [tprod, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

-- UMP


def lift {N : Type*} [AddCommMonoid N] [Module R N] :
    (M [Σ^ι]→ₗ[R] N) ≃ₗ[R] ((Sym[R] ι M) →ₗ[R] N) :=

  let liftFun : (M [Σ^ι]→ₗ[R] N) → (Sym[R] ι M →ₗ[R] N) := fun f =>
    ModuleCon.lift (SymmetricCon R ι M) (PiTensorProduct.lift f.toMultilinearMap) (by
      intro a b rel
      induction rel with
      | of h =>
        match h with
        | .perm e s => simp [PiTensorProduct.lift.tprod]
      | refl => rfl
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      | add _ _ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
      | smul s _ ih => simp [map_smul, ih])

  let inv : (Sym[R] ι M →ₗ[R] N) → (M [Σ^ι]→ₗ[R] N) := fun g => by
    let φ : (⨂[R] (_ : ι), M) →ₗ[R] N := g ∘ₗ (SymmetricCon R ι M).mk'
    let Gm := φ.compMultilinearMap (PiTensorProduct.tprod R)
    apply SymmetricMap.mk Gm
    intro v e
    change (g ∘ₗ (SymmetricCon R ι M).mk') (PiTensorProduct.tprod R (v ∘ e))
       = (g ∘ₗ (SymmetricCon R ι M).mk') (PiTensorProduct.tprod R v)
    simp only [LinearMap.comp_apply]
    congr 1
    exact ModuleCon.eq.mpr (ModuleConGen.Rel.of (SymmetricPower.Rel.perm e v)).symm

  { toFun := liftFun

    map_add' := fun f g => by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (SymmetricCon R ι M).mk'_surjective x
      simp only [liftFun, LinearMap.add_apply]
      have key : PiTensorProduct.lift (f + g).toMultilinearMap
           = PiTensorProduct.lift f.toMultilinearMap + PiTensorProduct.lift g.toMultilinearMap := by
        rw [SymmetricMap.toMultilinearMap_add]
        exact LinearEquiv.map_add PiTensorProduct.lift f.toMultilinearMap g.toMultilinearMap

      have h1 : PiTensorProduct.lift (f + g).toMultilinearMap y
           = PiTensorProduct.lift f.toMultilinearMap y
             + PiTensorProduct.lift g.toMultilinearMap y :=
        LinearMap.congr_fun key y

      exact h1

    map_smul' := fun r f => by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (SymmetricCon R ι M).mk'_surjective x
      simp only [liftFun, LinearMap.smul_apply]
      have key : PiTensorProduct.lift (r • f).toMultilinearMap
          = r • PiTensorProduct.lift f.toMultilinearMap := by
        rw [SymmetricMap.toMultilinearMap_smul]
        exact LinearEquiv.map_smul PiTensorProduct.lift r f.toMultilinearMap
      have h1 : PiTensorProduct.lift (r • f).toMultilinearMap y
          = r • PiTensorProduct.lift f.toMultilinearMap y :=
        LinearMap.congr_fun key y
      exact h1

    invFun := inv

    left_inv := fun f => by
      apply SymmetricMap.ext
      intro v
      change ((liftFun f) ∘ₗ (SymmetricCon R ι M).mk').compMultilinearMap
        (PiTensorProduct.tprod R) v = f.toMultilinearMap v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, liftFun]
      exact (ModuleCon.lift_mk' (SymmetricCon R ι M) (PiTensorProduct.lift f.toMultilinearMap) _
        (PiTensorProduct.tprod R v)).trans (PiTensorProduct.lift.tprod v)

    right_inv := fun g => by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (SymmetricCon R ι M).mk'_surjective x
      change liftFun (inv g) ((SymmetricCon R ι M).mk' y) = g ((SymmetricCon R ι M).mk' y)
      simp only [liftFun, inv]
      have key : PiTensorProduct.lift
          ((g ∘ₗ (SymmetricCon R ι M).mk').compMultilinearMap (PiTensorProduct.tprod R))
          = g ∘ₗ (SymmetricCon R ι M).mk' := by
        apply PiTensorProduct.ext
        ext v
        simp [PiTensorProduct.lift.tprod]
      have h1 : (PiTensorProduct.lift
          ((g ∘ₗ (SymmetricCon R ι M).mk').compMultilinearMap (PiTensorProduct.tprod R))) y
          = (g ∘ₗ (SymmetricCon R ι M).mk') y :=
        LinearMap.congr_fun key y
      exact h1

      }

example (N : Type*) [AddCommMonoid N] [Module R N] (f : (M [Σ^ι]→ₗ[R] N))
  : (⨂[R] (_:ι), M) →ₗ[R] N  := by
  exact PiTensorProduct.lift f

example (N : Type*) [AddCommMonoid N] [Module R N] (f : (M [Σ^ι]→ₗ[R] N))
  : (⨂[R] (_:ι), M) →ₗ[R] N  := by
  exact PiTensorProduct.lift f


example (N : Type) [AddCommGroup N] [Module R N] (φ : Sym[R] ι M →ₗ[R] N)
    : (⨂[R] (_ : ι), M) →ₗ[R] N := by
  let π : (⨂[R] (_ : ι), M) →ₗ[R] (Sym[R] ι M) := mk R ι M
  exact φ ∘ₗ π


end SymmetricPower
