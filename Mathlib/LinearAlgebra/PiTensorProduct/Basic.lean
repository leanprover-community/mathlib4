/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Multilinear.TensorProduct
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `FreeAddMonoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap σ M N` is the corresponding linear map
  `(⨂[R] i, M i) →ₛₗ[σ] N`. This is bundled as a linear equivalence.
* `PiTensorProduct.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `PiTensorProduct.tmulEquiv` equivalence between a `TensorProduct` of `PiTensorProduct`s and
  a single `PiTensorProduct`.

## Notation

* `⨂[R] i, s i` is defined as localized notation in scope `TensorProduct`.
* `⨂ₜ[R] i, f i` with `f : ∀ i, s i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `FreeAddMonoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `FreeAddMonoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `Fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.
* Instead of requiring `DecidableEq ι` as an argument to `PiTensorProduct` itself, we include it
  as an argument in the constructors of the relation. A decidability instance still has to come
  from somewhere due to the use of `Function.update`, but this hides it from the downstream user.
  See the implementation notes for `MultilinearMap` for an extended discussion of this choice.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

@[expose] public section

open Function

section Semiring

variable {ι ι₂ ι₃ : Type*}
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S}
variable {R₁ R₂ R₃ R₄ : Type*}
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {M M₁ M₂ M₃ : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {N N₃ : Type*} [AddCommMonoid N] [Module S N]
variable {F : Type*} [AddCommMonoid F]

namespace PiTensorProduct

variable (R) (s)

/-- The relation on `FreeAddMonoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive Eqv : FreeAddMonoid (R × Π i, s i) → FreeAddMonoid (R × Π i, s i) → Prop
  | of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
  | of_zero_scalar : ∀ f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
  | of_add : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂))
        (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
  | of_add_scalar : ∀ (r r' : R) (f : Π i, s i),
      Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
  | of_smul : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R),
      Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end PiTensorProduct

variable (R) (s)

/-- `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
def PiTensorProduct : Type _ :=
  (addConGen (PiTensorProduct.Eqv R s)).Quotient

variable {R}

/-- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product `PiTensorProduct`,
given an indexed family of types `s : ι → Type*`. -/
scoped[TensorProduct] notation3:100"⨂["R"] "(...)", "r:(scoped f => PiTensorProduct R f) => r

open TensorProduct

namespace PiTensorProduct

section Module

instance : AddCommMonoid (⨂[R] i, s i) :=
  { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y ↦
      AddCon.induction_on₂ x y fun _ _ ↦
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }

instance : Inhabited (⨂[R] i, s i) := ⟨0⟩

variable (R) {s}

/-- `tprodCoeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
def tprodCoeff (r : R) (f : Π i, s i) : ⨂[R] i, s i :=
  AddCon.mk' _ <| FreeAddMonoid.of (r, f)

variable {R}

theorem zero_tprodCoeff (f : Π i, s i) : tprodCoeff R 0 f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_scalar _

theorem zero_tprodCoeff' (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0) : tprodCoeff R z f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero _ _ i hf

theorem add_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
    tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) =
      tprodCoeff R z (update f i (m₁ + m₂)) :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)

theorem add_tprodCoeff' (z₁ z₂ : R) (f : Π i, s i) :
    tprodCoeff R z₁ f + tprodCoeff R z₂ f = tprodCoeff R (z₁ + z₂) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)

theorem smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R) :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _ _ _

theorem smul_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
    [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f := by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁, h₂]
  exact smul_tprodCoeff_aux z f i _

/-- Construct an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × Π i, s i) → F` with the appropriate properties. -/
def liftAddHom (φ : (R × Π i, s i) → F)
    (C0 : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), φ (r, f) = 0)
    (C0' : ∀ f : Π i, s i, φ (0, f) = 0)
    (C_add : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
    (C_add_scalar : ∀ (r r' : R) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (r' : R),
      φ (r, update f i (r' • f i)) = φ (r' * r, f)) :
    (⨂[R] i, s i) →+ F :=
  (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ) <|
    AddCon.addConGen_le.2 fun x y hxy ↦
      match hxy with
      | Eqv.of_zero r' f i hf =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0']
      | Eqv.of_add inst z f i m₁ m₂ =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_add inst]
      | Eqv.of_add_scalar z₁ z₂ f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C_add_scalar]
      | Eqv.of_smul inst z f i r' =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_smul inst]
      | Eqv.add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

/-- Induct using `tprodCoeff` -/
@[elab_as_elim]
protected theorem induction_on' {motive : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (tprodCoeff : ∀ (r : R) (f : Π i, s i), motive (tprodCoeff R r f))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  have C0 : motive 0 := by
    have h₁ := tprodCoeff 0 0
    rwa [zero_tprodCoeff] at h₁
  refine AddCon.induction_on z fun x ↦ FreeAddMonoid.recOn x C0 ?_
  simp_rw [AddCon.coe_add]
  refine fun f y ih ↦ add _ _ ?_ ih
  convert! tprodCoeff f.1 f.2

section DistribMulAction

variable [Monoid R₁] [DistribMulAction R₁ R] [SMulCommClass R₁ R R]
variable [Monoid R₂] [DistribMulAction R₂ R] [SMulCommClass R₂ R R]

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance hasSMul' : SMul R₁ (⨂[R] i, s i) :=
  ⟨fun r ↦
    liftAddHom (fun f : R × Π i, s i ↦ tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf ↦ by simp_rw [zero_tprodCoeff' _ f i hf])
      (fun f ↦ by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ ↦ by simp [add_tprodCoeff])
      (fun r' r'' f ↦ by simp [add_tprodCoeff']) fun z f i r' ↦ by
      simp [smul_tprodCoeff, mul_smul_comm]⟩

instance : SMul R (⨂[R] i, s i) :=
  PiTensorProduct.hasSMul'

theorem smul_tprodCoeff' (r : R₁) (z : R) (f : Π i, s i) :
    r • tprodCoeff R z f = tprodCoeff R (r • z) f := rfl

protected theorem smul_add (r : R₁) (x y : ⨂[R] i, s i) : r • (x + y) = r • x + r • y :=
  map_add _ _ _

instance distribMulAction' : DistribMulAction R₁ (⨂[R] i, s i) where
  smul_add _ _ _ := map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} ↦ by simp [smul_tprodCoeff', smul_smul])
      fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
  one_smul x :=
    PiTensorProduct.induction_on' x (fun {r f} ↦ by rw [smul_tprodCoeff', one_smul])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]
  smul_zero _ := map_zero _

instance smulCommClass' [SMulCommClass R₁ R₂ R] : SMulCommClass R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_comm])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

instance isScalarTower' [SMul R₁ R₂] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_assoc])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩

end DistribMulAction

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance module' [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] : Module R₁ (⨂[R] i, s i) :=
  { PiTensorProduct.distribMulAction' with
    add_smul := fun r r' x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
    zero_smul := fun x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', zero_smul, zero_tprodCoeff])
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_zero] }

-- shortcut instances
instance : Module R (⨂[R] i, s i) :=
  PiTensorProduct.module'

instance : SMulCommClass R R (⨂[R] i, s i) :=
  PiTensorProduct.smulCommClass'

instance : IsScalarTower R R (⨂[R] i, s i) :=
  PiTensorProduct.isScalarTower'

variable (R) in
/-- The canonical `MultilinearMap (.id R) s (⨂[R] i, s i)`.

`tprod R fun i => f i` has notation `⨂ₜ[R] i, f i`. -/
def tprod : MultilinearMap (.id R) s (⨂[R] i, s i) where
  toFun := tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff', ← smul_tprodCoeff (1 : R) _ i, update_idem, update_self, RingHom.id_apply]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f) => r

theorem tprod_eq_tprodCoeff_one :
    ⇑(tprod R : MultilinearMap (.id R) s (⨂[R] i, s i)) = tprodCoeff R 1 := rfl

@[simp]
theorem tprodCoeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprodCoeff R z f = z • tprod R f := by
  have : z = z • (1 : R) := by simp only [mul_one, smul_eq_mul]
  conv_lhs => rw [this]
  rfl

/-- The image of an element `p` of `FreeAddMonoid (R × Π i, s i)` in the `PiTensorProduct` is
equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries `(a, m)` of `p`.
-/
lemma _root_.FreeAddMonoid.toPiTensorProduct (p : FreeAddMonoid (R × Π i, s i)) :
    AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p =
    List.sum (List.map (fun x ↦ x.1 • ⨂ₜ[R] i, x.2 i) p.toList) := by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => rfl
  | of_add b a ih =>
    rw [FreeAddMonoid.toList_of_add, List.map_cons, List.sum_cons, ← ih, ← tprodCoeff_eq_smul_tprod]
    rfl

/-- The set of lifts of an element `x` of `⨂[R] i, s i` in `FreeAddMonoid (R × Π i, s i)`. -/
def lifts (x : ⨂[R] i, s i) : Set (FreeAddMonoid (R × Π i, s i)) :=
  {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

set_option backward.isDefEq.respectTransparency false in
/-- An element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i, s i`
if and only if `x` is equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries
`(a, m)` of `p`.
-/
lemma mem_lifts_iff (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i)) :
    p ∈ lifts x ↔ List.sum (List.map (fun x ↦ x.1 • ⨂ₜ[R] i, x.2 i) p.toList) = x := by
  simp only [lifts, Set.mem_ofPred_eq, FreeAddMonoid.toPiTensorProduct]

set_option backward.isDefEq.respectTransparency false in
/-- Every element of `⨂[R] i, s i` has a lift in `FreeAddMonoid (R × Π i, s i)`.
-/
lemma nonempty_lifts (x : ⨂[R] i, s i) : Set.Nonempty (lifts x) := by
  existsi Quot.out x
  simp [lifts, ← AddCon.quot_mk_eq_coe]

instance (x : ⨂[R] i, s i) : Nonempty ↑x.lifts := nonempty_subtype.mpr (nonempty_lifts x)

/-- The empty list lifts the element `0` of `⨂[R] i, s i`.
-/
lemma lifts_zero : 0 ∈ lifts (0 : ⨂[R] i, s i) := by
  rw [mem_lifts_iff, FreeAddMonoid.toList_zero, List.map_nil, List.sum_nil]

set_option backward.isDefEq.respectTransparency false in
/-- If elements `p,q` of `FreeAddMonoid (R × Π i, s i)` lift elements `x,y` of `⨂[R] i, s i`
respectively, then `p + q` lifts `x + y`.
-/
lemma lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
    (hp : p ∈ lifts x) (hq : q ∈ lifts y) : p + q ∈ lifts (x + y) := by
  simp only [lifts, Set.mem_ofPred_eq, AddCon.coe_add]
  rw [hp, hq]

/-- If an element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i, s i`,
and if `a` is an element of `R`, then the list obtained by multiplying the first entry of each
element of `p` by `a` lifts `a • x`.
-/
lemma lifts_smul {x : ⨂[R] i, s i} {p : FreeAddMonoid (R × Π i, s i)} (h : p ∈ lifts x) (a : R) :
    p.map (fun (y : R × Π i, s i) ↦ (a * y.1, y.2)) ∈ lifts (a • x) := by
  rw [mem_lifts_iff] at h ⊢
  rw [← h]
  simp [Function.comp_def, mul_smul, List.smul_sum]

/-- Induct using scaled versions of `PiTensorProduct.tprod`. -/
@[elab_as_elim]
protected theorem induction_on {motive : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (smul_tprod : ∀ (r : R) (f : Π i, s i), motive (r • tprod R f))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  simp_rw [← tprodCoeff_eq_smul_tprod] at smul_tprod
  exact PiTensorProduct.induction_on' z smul_tprod add

@[ext]
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₛₗ[σ] N}
    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by
  refine LinearMap.ext ?_
  refine fun z ↦
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy ↦ by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod, φ₁.map_smulₛₗ, φ₂.map_smulₛₗ]
    apply congr_arg
    exact MultilinearMap.congr_fun H f

/-- The pure tensors (i.e. the elements of the image of `PiTensorProduct.tprod`) span
the tensor product. -/
theorem span_tprod_eq_top :
    Submodule.span R (Set.range (tprod R)) = (⊤ : Submodule R (⨂[R] i, s i)) :=
  Submodule.eq_top_iff'.mpr fun t ↦ t.induction_on
    (fun _ _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (by simp only [Set.mem_range, exists_apply_eq_apply])))
    (fun _ _ hx hy ↦ Submodule.add_mem _ hx hy)

end Module

section Multilinear

open MultilinearMap

section lift

/-- Auxiliary function to constructing a linear map `(⨂[R] i, M i) → N` given a
`MultilinearMap σ M N` with the property that its composition with the canonical
`MultilinearMap σ M (⨂[R] i, M i)` is the given multilinear map. -/
def liftAux (φ : MultilinearMap σ M N) : (⨂[R] i, M i) →+ N :=
  liftAddHom (fun p : R × Π i, M i ↦ σ p.1 • φ p.2)
    (fun z f i hf ↦ by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f ↦ by simp_rw [_root_.map_zero, zero_smul])
    (fun z f i m₁ m₂ ↦ by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f ↦ by rw [map_add, ← add_smul])
    fun z f i r ↦ by simp [φ.map_update_smul, smul_smul, mul_comm]

theorem liftAux_tprod (φ : MultilinearMap σ M N) (f : Π i, M i) :
    liftAux φ (tprod R f) = φ f := by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.lift, FreeAddMonoid.sumAux]
  -- show _ • _ = _
  -- rw [one_smul]
  conv_lhs => apply AddCon.lift_coe
  simp

theorem liftAux_tprodCoeff (φ : MultilinearMap σ M N) (z : R) (f : Π i, M i) :
    liftAux φ (tprodCoeff R z f) = σ z • φ f := rfl

theorem liftAux.smul {φ : MultilinearMap σ M N} (r : R) (x : ⨂[R] i, M i) :
    liftAux φ (r • x) = σ r • liftAux φ x := by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f, liftAux_tprodCoeff, liftAux_tprodCoeff, smul_eq_mul, map_mul,
      ← smul_eq_mul, smul_assoc]
  · intro z y ihz ihy
    rw [smul_add, (liftAux φ).map_add, ihz, ihy, (liftAux φ).map_add, smul_add]

/-- Constructing a linear map `(⨂[R] i, M i) → N` given a `MultilinearMap σ M N` with the
property that its composition with `PiTensorProduct.tprod` is the given multilinear map `φ`. -/
def lift : MultilinearMap σ M N ≃ₗ[S] (⨂[R] i, M i) →ₛₗ[σ] N where
  toFun φ := { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
  right_inv φ := by
    ext
    simp [liftAux_tprod]
  map_add' φ₁ φ₂ := by
    ext
    simp [liftAux_tprod]
  map_smul' r φ₂ := by
    ext
    simp [liftAux_tprod]

variable {φ : MultilinearMap σ M N}

@[simp]
theorem lift.tprod (x : Π i, M i) : lift φ (tprod R x) = φ x :=
  liftAux_tprod φ x

theorem lift.unique' {φ' : (⨂[R] i, M i) →ₛₗ[σ] N}
    (H : φ'.compMultilinearMap (PiTensorProduct.tprod R) = φ) : φ' = lift φ :=
  ext <| H.symm ▸ (lift.symm_apply_apply φ).symm

theorem lift.unique {φ' : (⨂[R] i, M i) →ₛₗ[σ] N} (H : ∀ f, φ' (PiTensorProduct.tprod R f) = φ f) :
    φ' = lift φ :=
  lift.unique' (MultilinearMap.ext H)

@[simp]
theorem lift_symm (φ' : (⨂[R] i, M i) →ₛₗ[σ] N) : lift.symm φ' = φ'.compMultilinearMap (tprod R) :=
  rfl

@[simp]
theorem lift_tprod : lift (tprod R : MultilinearMap _ s _) = LinearMap.id :=
  Eq.symm <| lift.unique' rfl

end lift

section map

variable [CommSemiring R₁] [CommSemiring R₂] [CommSemiring R₃]
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R₁ (M₁ i)]
variable [∀ i, AddCommMonoid (M₂ i)] [∀ i, Module R₂ (M₂ i)]
variable [∀ i, AddCommMonoid (M₃ i)] [∀ i, Module R₃ (M₃ i)]
variable [AddCommMonoid N₃] [Module R₃ N₃]
variable (g : Π i, M₂ i →ₛₗ[σ₂₃] M₃ i) (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i)

/--
Let `M₁ᵢ` and `M₂ᵢ` be families of `R₁`- and `R₂`-modules.
Let `f` be a family of `σ₁₂`-semilinear maps between `M₁ᵢ` and `M₂ᵢ`, i.e. `f : Πᵢ M₁ᵢ → M₂ᵢ`,
then there is an induced map `⨂ᵢ M₁ᵢ → ⨂ᵢ M₂ᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.

This is `TensorProduct.map` for an arbitrary family of modules.
-/
def map : (⨂[R₁] i, M₁ i) →ₛₗ[σ₁₂] ⨂[R₂] i, M₂ i :=
  lift <| (tprod R₂).compLinearMap f

@[simp] lemma map_tprod (x : Π i, M₁ i) :
    map f (tprod R₁ x) = tprod R₂ fun i ↦ f i (x i) :=
  lift.tprod _

-- No lemmas about associativity, because we don't have associativity of `PiTensorProduct` yet.

theorem map_range_eq_span_tprod [RingHomSurjective σ₁₂] :
    LinearMap.range (map f) =
      Submodule.span R₂ {t | ∃ (m : Π i, M₁ i), tprod R₂ (fun i ↦ f i (m i)) = t} := by
  rw [← Submodule.map_top, ← span_tprod_eq_top, Submodule.map_span, ← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_ofPred_eq]

/-- Given submodules `p i ⊆ M i`, this is the natural map: `⨂[R] i, p i → ⨂[R] i, M i`.
This is `TensorProduct.mapIncl` for an arbitrary family of modules.
-/
@[simp]
def mapIncl (p : Π i, Submodule R (M i)) : (⨂[R] i, p i) →ₗ[R] ⨂[R] i, M i :=
  map fun (i : ι) ↦ (p i).subtype

theorem map_comp : map (fun (i : ι) ↦ g i ∘ₛₗ f i) = map g ∘ₛₗ map f := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]

theorem lift_comp_map (φ : MultilinearMap σ₂₃ M₂ N₃) :
    lift φ ∘ₛₗ map f = lift (φ.compLinearMap f) := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

attribute [local ext high] ext

@[simp]
theorem map_id : map (fun i ↦ (LinearMap.id : M i →ₗ[R] M i)) = .id := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]
protected theorem map_one : map (fun (i : ι) ↦ (1 : M i →ₗ[R] M i)) = 1 :=
  map_id

protected theorem map_mul (f₁ f₂ : Π i, M i →ₗ[R] M i) :
    map (fun i ↦ f₁ i * f₂ i) = map f₁ * map f₂ :=
  map_comp f₁ f₂

/-- Upgrading `PiTensorProduct.map` to a `MonoidHom` when `M₁ = M₂`. -/
@[simps]
def mapMonoidHom : (Π i, M i →ₗ[R] M i) →* ((⨂[R] i, M i) →ₗ[R] ⨂[R] i, M i) where
  toFun := map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]
protected theorem map_pow (f : Π i, M i →ₗ[R] M i) (n : ℕ) :
    map (f ^ n) = map f ^ n := map_pow mapMonoidHom _ _

open Function in
private theorem map_add_smul_aux [DecidableEq ι] (i : ι) (x : Π i, M₁ i) (u : M₁ i →ₛₗ[σ₁₂] M₂ i) :
    (fun j ↦ update f i u j (x j)) = update (fun j ↦ (f j) (x j)) i (u (x i)) := by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j

open Function in
protected theorem map_update_add [DecidableEq ι] (i : ι) (u v : M₁ i →ₛₗ[σ₁₂] M₂ i) :
    map (update f i (u + v)) = map (update f i u) + map (update f i v) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]

open Function in
protected theorem map_update_smul [DecidableEq ι] (i : ι) (c : R₂) (u : M₁ i →ₛₗ[σ₁₂] M₂ i) :
    map (update f i (c • u)) = c • map (update f i u) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul, RingHom.id_apply]

variable (σ₁₂ M₁ M₂) in
/-- The tensor product of a family of linear maps from `M₁ᵢ` to `M₂ᵢ`,
as a multilinear map of the family. -/
@[simps]
noncomputable def mapMultilinear :
    MultilinearMap (.id R₂) (fun (i : ι) ↦ M₁ i →ₛₗ[σ₁₂] M₂ i)
      ((⨂[R₁] i, M₁ i) →ₛₗ[σ₁₂] ⨂[R₂] i, M₂ i) where
  toFun := map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _

/--
Let `M₁ᵢ` and `M₂ᵢ` be families of `R₁`- and `R₂`-modules.
Then there is an `R₂`-linear map between `⨂ᵢ Hom(M₁ᵢ, M₂ᵢ)` and `Hom(⨂ᵢ M₁ᵢ, ⨂ M₂ᵢ)` defined by
`⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ fᵢ aᵢ`.

This is `TensorProduct.homTensorHomMap` for an arbitrary family of modules.

Note that `PiTensorProduct.piTensorHomMap (tprod R₂ f)` is equal to `PiTensorProduct.map f`.
-/
def piTensorHomMap : (⨂[R₂] i, M₁ i →ₛₗ[σ₁₂] M₂ i) →ₗ[R₂] (⨂[R₁] i, M₁ i) →ₛₗ[σ₁₂] ⨂[R₂] i, M₂ i :=
  lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R₂)

@[simp] lemma piTensorHomMap_tprod_tprod (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (x : Π i, M₁ i) :
    piTensorHomMap (tprod R₂ f) (tprod R₁ x) = tprod R₂ fun i ↦ f i (x i) := by
  simp [piTensorHomMap]

lemma piTensorHomMap_tprod_eq_map (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) :
    piTensorHomMap (tprod R₂ f) = map f := by
  ext; simp

section congr

variable {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- If `M₁ᵢ` and `M₂ᵢ` are linearly equivalent for every `i` in `ι`, then `⨂[R₁] i, M₁ i` and
`⨂[R₂] i, M₂ i` are linearly equivalent.

This is the n-ary version of `TensorProduct.congr`
-/
noncomputable def congr (f : Π i, M₁ i ≃ₛₗ[σ₁₂] M₂ i) : (⨂[R₁] i, M₁ i) ≃ₛₗ[σ₁₂] ⨂[R₂] i, M₂ i :=
  .ofLinearMap
    (map (fun i ↦ f i))
    (map (fun i ↦ (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem congr_tprod (f : Π i, M₁ i ≃ₛₗ[σ₁₂] M₂ i) (m : Π i, M₁ i) :
    congr f (tprod R₁ m) = tprod R₂ (fun (i : ι) ↦ (f i) (m i)) := by
  simp only [congr, LinearEquiv.coe_ofLinearMap, map_tprod, LinearEquiv.coe_coe]

@[simp]
theorem congr_symm_tprod (f : Π i, M₁ i ≃ₛₗ[σ₁₂] M₂ i) (p : Π i, M₂ i) :
    (congr f).symm (tprod R₂ p) = tprod R₁ (fun (i : ι) ↦ (f i).symm (p i)) := by
  simp only [congr, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap, map_tprod,
    LinearEquiv.coe_coe]

end congr

/--
Let `M₁ᵢ`, `M₂ᵢ` and `M₃ᵢ` be families of `R₁`-, `R₂`- and `R₃`-modules;
then `f : Πᵢ M₁ᵢ → M₂ᵢ → M₃ᵢ` induces an element of `Hom(⨂ᵢ M₁ᵢ, Hom(⨂ M₂ᵢ, ⨂ᵢ M₃ᵢ))`
defined by `⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `PiTensorProduct.map` for two arbitrary families of modules.
This is `TensorProduct.map₂` for families of modules.
-/
def map₂ (f : Π i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) :
    (⨂[R₁] i, M₁ i) →ₛₗ[σ₁₃] (⨂[R₂] i, M₂ i) →ₛₗ[σ₂₃] ⨂[R₃] i, M₃ i :=
  lift <| LinearMap.compMultilinearMap piTensorHomMap <| (tprod R₃).compLinearMap f

lemma map₂_tprod_tprod (f : Π i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) (x : Π i, M₁ i) (y : Π i, M₂ i) :
    map₂ f (tprod R₁ x) (tprod R₂ y) = tprod R₃ fun i ↦ f i (x i) (y i) := by
  simp [map₂]

/--
Let `M₁ᵢ`, `M₂ᵢ` and `M₃ᵢ` be families of `R₁`-, `R₂`- and `R₃`-modules.
Then there is a function from `⨂ᵢ Hom(M₁ᵢ, Hom(M₂ᵢ, M₃ᵢ))` to `Hom(⨂ᵢ M₁ᵢ, Hom(⨂ M₂ᵢ, ⨂ᵢ M₃ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`. -/
def piTensorHomMapFun₂ : (⨂[R₃] i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) →
    (⨂[R₁] i, M₁ i) →ₛₗ[σ₁₃] (⨂[R₂] i, M₂ i) →ₛₗ[σ₂₃] (⨂[R₃] i, M₃ i) :=
  fun φ => lift <| LinearMap.compMultilinearMap piTensorHomMap <|
    (lift <| MultilinearMap.piLinearMap <| tprod R₃) φ

theorem piTensorHomMapFun₂_add (φ ψ : ⨂[R₃] i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) :
    piTensorHomMapFun₂ (φ + ψ) = piTensorHomMapFun₂ φ + piTensorHomMapFun₂ ψ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

theorem piTensorHomMapFun₂_smul (r : R₃) (φ : ⨂[R₃] i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) :
    piTensorHomMapFun₂ (r • φ) = r • piTensorHomMapFun₂ φ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

/--
Let `M₁ᵢ`, `M₂ᵢ` and `M₃ᵢ` be families of `R₁`-, `R₂`- and `R₃`-modules;
Then there is a linear map from `⨂ᵢ Hom(M₁ᵢ, Hom(M₂ᵢ, M₃ᵢ))` to `Hom(⨂ᵢ M₁ᵢ, Hom(⨂ M₂ᵢ, ⨂ᵢ M₃ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `TensorProduct.homTensorHomMap` for two arbitrary families of modules.
-/
def piTensorHomMap₂ : (⨂[R₃] i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) →ₗ[R₃]
    (⨂[R₁] i, M₁ i) →ₛₗ[σ₁₃] (⨂[R₂] i, M₂ i) →ₛₗ[σ₂₃] (⨂[R₃] i, M₃ i) where
  toFun := piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y := piTensorHomMapFun₂_smul x y

@[simp] lemma piTensorHomMap₂_tprod_tprod_tprod
    (f : Π i, M₁ i →ₛₗ[σ₁₃] M₂ i →ₛₗ[σ₂₃] M₃ i) (x : ∀ i, M₁ i) (y : ∀ i, M₂ i) :
    piTensorHomMap₂ (tprod R₃ f) (tprod R₁ x) (tprod R₂ y) =
      tprod R₃ (fun i ↦ f i (x i) (y i)) := by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]

end map

section reindex

variable (R M) in
/-- Re-index the components of the tensor power by `e`. -/
def reindex (e : ι ≃ ι₂) : (⨂[R] i : ι, M i) ≃ₗ[R] ⨂[R] i : ι₂, M (e.symm i) :=
  let f := domDomCongrLinearEquiv' R M (⨂[R] (i : ι₂), M (e.symm i)) _ e
  let g := domDomCongrLinearEquiv' R M (⨂[R] (i : ι), M i) _ e
  LinearEquiv.ofLinearMap (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

@[simp]
theorem reindex_tprod (e : ι ≃ ι₂) (f : Π i, M i) :
    reindex R M e (tprod R f) = tprod R fun i ↦ f (e.symm i) := by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]
theorem reindex_comp_tprod (e : ι ≃ ι₂) :
    (reindex R s e).compMultilinearMap (tprod R) =
    (domDomCongrLinearEquiv' R s _ _ e).symm (tprod R) :=
  MultilinearMap.ext <| reindex_tprod e

theorem lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap σ (fun i ↦ M (e.symm i)) N) :
    lift φ ∘ₛₗ (reindex R M e).1 = lift ((domDomCongrLinearEquiv' S M N σ e).symm.1 φ) := by
  ext; simp [reindex]

@[simp]
theorem lift_comp_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap σ M N) :
    lift φ ∘ₛₗ (reindex R M e).symm.1 = lift (domDomCongrLinearEquiv' S M N σ e φ) := by
  ext; simp [reindex]

theorem lift_reindex
    (e : ι ≃ ι₂) (φ : MultilinearMap σ (fun i ↦ M (e.symm i)) N) (x : ⨂[R] i, M i) :
    lift φ (reindex R M e x) = lift ((domDomCongrLinearEquiv' S M N σ e).symm φ) x :=
  LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]
theorem lift_reindex_symm
    (e : ι ≃ ι₂) (φ : MultilinearMap σ M N) (x : ⨂[R] i, M (e.symm i)) :
    lift φ (reindex R M e |>.symm x) = lift (domDomCongrLinearEquiv' S M N σ e φ) x :=
  LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

@[simp]
theorem reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
    (reindex R M e).trans (reindex R _ e') = reindex R M (e.trans e') := by
  apply LinearEquiv.toLinearMap_injective
  ext
  rw [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    reindex_tprod, reindex_tprod]
  exact (reindex_tprod (e.trans e') _).symm

theorem reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, M i) :
    reindex R _ e' (reindex R M e x) = reindex R M (e.trans e') x :=
  LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R M (e.trans e')) x

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
theorem reindex_symm (e : ι ≃ ι₂) :
    (reindex S (fun _ ↦ N) e).symm = reindex S (fun _ ↦ N) e.symm := by
  ext x
  simp [reindex]

@[simp]
theorem reindex_refl : reindex R M (Equiv.refl ι) = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  ext
  rw [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, reindex_tprod]
  exact DFunLike.congr_arg (tprod R) rfl

variable [CommSemiring R₁] [CommSemiring R₂] {σ₁₂ : R₁ →+* R₂}
variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R₁ (M₁ i)]
variable [∀ i, AddCommMonoid (M₂ i)] [∀ i, Module R₂ (M₂ i)]

/-- Re-indexing the components of the tensor product by an equivalence `e` is compatible
with `PiTensorProduct.map`. -/
theorem map_comp_reindex_eq (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (e : ι ≃ ι₂) :
    map (fun i ↦ f (e.symm i)) ∘ₛₗ (reindex R₁ M₁ e).1 = (reindex R₂ M₂ e).1 ∘ₛₗ map f := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]

theorem map_reindex (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (e : ι ≃ ι₂) (x : ⨂[R₁] i, M₁ i) :
    map (fun i ↦ f (e.symm i)) (reindex R₁ M₁ e x) = reindex R₂ M₂ e (map f x) :=
  DFunLike.congr_fun (map_comp_reindex_eq _ _) _

theorem map_comp_reindex_symm (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (e : ι ≃ ι₂) :
    map f ∘ₛₗ (reindex R₁ M₁ e).symm.1 =
      (reindex R₂ M₂ e).symm.1 ∘ₛₗ map (fun i => f (e.symm i)) := by
  ext m
  apply LinearEquiv.injective (reindex R₂ M₂ e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]

theorem map_reindex_symm (f : Π i, M₁ i →ₛₗ[σ₁₂] M₂ i) (e : ι ≃ ι₂) (x : ⨂[R₁] i, M₁ (e.symm i)) :
    map f ((reindex R₁ M₁ e).symm x) = (reindex R₂ M₂ e).symm (map (fun i ↦ f (e.symm i)) x) :=
  DFunLike.congr_fun (map_comp_reindex_symm _ _) _

end reindex

variable (ι) {s}

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
def isEmptyEquiv [IsEmpty ι] : (⨂[R] i : ι, s i) ≃ₗ[R] R where
  toFun := lift (constOfIsEmpty (.id R) s 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    · intro x y
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      aesop
    · simp only
      intro x y hx hy
      rw [map_add, add_smul, hx, hy]
  right_inv t := by simp
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
theorem isEmptyEquiv_apply_tprod [IsEmpty ι] (f : Π i, s i) :
    isEmptyEquiv ι (tprod R f) = 1 :=
  lift.tprod _

variable {ι}

section subsingleton

variable [Subsingleton ι] (i₀ : ι)

/-- Tensor product over a singleton type with element `i₀` is equivalent to `s i₀`. -/
def subsingletonEquiv : (⨂[R] i : ι, s i) ≃ₗ[R] s i₀ :=
  LinearEquiv.ofLinearMap
    (lift
      { toFun f := f i₀
        map_update_add' m i := by rw [Subsingleton.elim i i₀]; simp
        map_update_smul' m i := by rw [Subsingleton.elim i i₀]; simp })
    ({ toFun x := tprod R (update (0 : (i : ι) → s i) i₀ x)
       map_add' := by simp
       map_smul' := by simp })
    (by ext _; simp)
    (by
      ext f
      have h : update (0 : (i : ι) → s i) i₀ (f i₀) = f := update_eq_self i₀ f
      simp [h])

@[simp]
theorem subsingletonEquiv_apply_tprod (f : (i : ι) → s i) :
    subsingletonEquiv i₀ (⨂ₜ[R] i, f i) = f i₀ := lift.tprod _

theorem subsingletonEquiv_symm_apply (x : s i₀) :
    (subsingletonEquiv i₀).symm x = tprod R (fun i ↦ update (0 : (j : ι) → s j) i₀ x i) := rfl

@[simp]
lemma subsingletonEquiv_symm_apply' (x : N) :
  (subsingletonEquiv (s := fun _ ↦ N) i₀).symm x = (tprod S fun _ ↦ x) := by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

end subsingleton

variable (R)

section tmulEquivDep

variable (N : ι ⊕ ι₂ → Type*) [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type. If `N` is a constant family of
modules, use the non-dependent version `PiTensorProduct.tmulEquiv` instead. -/
def tmulEquivDep :
    (⨂[R] i₁, N (.inl i₁)) ⊗[R] (⨂[R] i₂, N (.inr i₂)) ≃ₗ[R] ⨂[R] i, N i :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift
      { toFun a := PiTensorProduct.lift (PiTensorProduct.lift
          (MultilinearMap.currySumEquiv (tprod R)) a)
        map_add' := by simp
        map_smul' := by simp })
    (PiTensorProduct.lift (MultilinearMap.domCoprodDep (tprod R) (tprod R))) (by
      ext
      dsimp
      simp only [lift.tprod, domCoprodDep_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
        currySum_apply]
      congr
      ext (_ | _) <;> simp)
    (TensorProduct.ext (by aesop))

@[simp]
lemma tmulEquivDep_apply (a : (i₁ : ι) → N (.inl i₁))
    (b : (i₂ : ι₂) → N (.inr i₂)) :
      tmulEquivDep R N ((⨂ₜ[R] i₁, a i₁) ⊗ₜ (⨂ₜ[R] i₂, b i₂)) =
        (⨂ₜ[R] i, Sum.rec a b i) := by
  simp [tmulEquivDep]

@[simp]
lemma tmulEquivDep_symm_apply (f : (i : ι ⊕ ι₂) → N i) :
    (tmulEquivDep R N).symm (⨂ₜ[R] i, f i) =
      ((⨂ₜ[R] i₁, f (.inl i₁)) ⊗ₜ (⨂ₜ[R] i₂, f (.inr i₂))) := by
  simp [tmulEquivDep]

end tmulEquivDep

section tmulEquiv

variable [Module R N]

variable (N) in
/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type.

See `PiTensorProduct.tmulEquivDep` for the dependent version. -/
def tmulEquiv :
    (⨂[R] (_ : ι), N) ⊗[R] (⨂[R] (_ : ι₂), N) ≃ₗ[R] ⨂[R] (_ : ι ⊕ ι₂), N :=
  tmulEquivDep R (fun _ ↦ N)

@[simp]
theorem tmulEquiv_apply (a : ι → N) (b : ι₂ → N) :
    tmulEquiv R N ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.elim a b i := by
  simp [tmulEquiv, Sum.elim]

@[simp]
theorem tmulEquiv_symm_apply (a : ι ⊕ ι₂ → N) :
    (tmulEquiv R N).symm (⨂ₜ[R] i, a i) =
      (⨂ₜ[R] i, a (Sum.inl i)) ⊗ₜ[R] (⨂ₜ[R] i, a (Sum.inr i)) := by
  simp [tmulEquiv]

end tmulEquiv

end Multilinear

end PiTensorProduct

end Semiring

section Ring

namespace PiTensorProduct

open PiTensorProduct

open TensorProduct

variable {ι : Type*} {R : Type*} [CommRing R]
variable {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

/-- Unlike for the binary tensor product, we require `R` to be a `CommRing` here, otherwise
this is false in the case where `ι` is empty. -/
instance : AddCommGroup (⨂[R] i, s i) :=
  Module.addCommMonoidToAddCommGroup R

end PiTensorProduct

end Ring
