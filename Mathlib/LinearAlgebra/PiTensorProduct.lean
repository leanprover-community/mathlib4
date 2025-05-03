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
binary tensor product in `LinearAlgebra/TensorProduct.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
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
variable {R : Type*} [CommSemiring R]
variable {R₁ R₂ : Type*}
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {E : Type*} [AddCommMonoid E] [Module R E]
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
    AddCon.addConGen_le fun x y hxy ↦
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
  convert tprodCoeff f.1 f.2

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
/-- The canonical `MultilinearMap R s (⨂[R] i, s i)`.

`tprod R fun i => f i` has notation `⨂ₜ[R] i, f i`. -/
def tprod : MultilinearMap R s (⨂[R] i, s i) where
  toFun := tprodCoeff R 1
  map_update_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_update_smul' {_ f} i r x := by
    rw [smul_tprodCoeff', ← smul_tprodCoeff (1 : R) _ i, update_idem, update_self]

@[inherit_doc tprod]
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => tprod R f) => r

theorem tprod_eq_tprodCoeff_one :
    ⇑(tprod R : MultilinearMap R s (⨂[R] i, s i)) = tprodCoeff R 1 := rfl

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
  induction h : FreeAddMonoid.toList p generalizing p with
  | nil =>
    rw [@Equiv.apply_eq_iff_eq_symm_apply] at h
    simp only [FreeAddMonoid.toList_symm, FreeAddMonoid.ofList_nil] at h
    simp [h]
  | cons x ps ih =>
    rw [@Equiv.apply_eq_iff_eq_symm_apply] at h
    simp only [FreeAddMonoid.toList_symm] at h
    rw [List.map_cons, List.sum_cons, ← ih _ rfl, h]
    simp only [FreeAddMonoid.ofList_cons, AddCon.coe_add]
    congr -- TODO still defeq abuse here
    ext <;>
    simp

/-- The set of lifts of an element `x` of `⨂[R] i, s i` in `FreeAddMonoid (R × Π i, s i)`. -/
def lifts (x : ⨂[R] i, s i) : Set (FreeAddMonoid (R × Π i, s i)) :=
  {p | AddCon.toQuotient (c := addConGen (PiTensorProduct.Eqv R s)) p = x}

/-- An element `p` of `FreeAddMonoid (R × Π i, s i)` lifts an element `x` of `⨂[R] i, s i`
if and only if `x` is equal to the sum of `a • ⨂ₜ[R] i, m i` over all the entries
`(a, m)` of `p`.
-/
lemma mem_lifts_iff (x : ⨂[R] i, s i) (p : FreeAddMonoid (R × Π i, s i)) :
    p ∈ lifts x ↔ List.sum (List.map (fun x ↦ x.1 • ⨂ₜ[R] i, x.2 i) p.toList) = x := by
  simp only [lifts, Set.mem_setOf_eq, FreeAddMonoid.toPiTensorProduct]

/-- Every element of `⨂[R] i, s i` has a lift in `FreeAddMonoid (R × Π i, s i)`.
-/
lemma nonempty_lifts (x : ⨂[R] i, s i) : Set.Nonempty (lifts x) := by
  existsi @Quotient.out _ (addConGen (PiTensorProduct.Eqv R s)).toSetoid x
  simp only [lifts, Set.mem_setOf_eq]
  rw [← AddCon.quot_mk_eq_coe]
  apply Quot.out_eq

/-- The empty list lifts the element `0` of `⨂[R] i, s i`.
-/
lemma lifts_zero : 0 ∈ lifts (0 : ⨂[R] i, s i) := by
  rw [mem_lifts_iff, FreeAddMonoid.toList_zero, List.map_nil, List.sum_nil]

/-- If elements `p,q` of `FreeAddMonoid (R × Π i, s i)` lift elements `x,y` of `⨂[R] i, s i`
respectively, then `p + q` lifts `x + y`.
-/
lemma lifts_add {x y : ⨂[R] i, s i} {p q : FreeAddMonoid (R × Π i, s i)}
    (hp : p ∈ lifts x) (hq : q ∈ lifts y) : p + q ∈ lifts (x + y) := by
  simp only [lifts, Set.mem_setOf_eq, AddCon.coe_add]
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
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by
  refine LinearMap.ext ?_
  refine fun z ↦
    PiTensorProduct.induction_on' z ?_ fun {x y} hx hy ↦ by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    rw [tprodCoeff_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul]
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

variable {s}

section lift

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`MultilinearMap R s E` with the property that its composition with the canonical
`MultilinearMap R s (⨂[R] i, s i)` is the given multilinear map. -/
def liftAux (φ : MultilinearMap R s E) : (⨂[R] i, s i) →+ E :=
  liftAddHom (fun p : R × Π i, s i ↦ p.1 • φ p.2)
    (fun z f i hf ↦ by simp_rw [map_coord_zero φ i hf, smul_zero])
    (fun f ↦ by simp_rw [zero_smul])
    (fun z f i m₁ m₂ ↦ by simp_rw [← smul_add, φ.map_update_add])
    (fun z₁ z₂ f ↦ by rw [← add_smul])
    fun z f i r ↦ by simp [φ.map_update_smul, smul_smul, mul_comm]

theorem liftAux_tprod (φ : MultilinearMap R s E) (f : Π i, s i) : liftAux φ (tprod R f) = φ f := by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- The end of this proof was very different before https://github.com/leanprover/lean4/pull/2644:
  -- rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- dsimp [FreeAddMonoid.lift, FreeAddMonoid.sumAux]
  -- show _ • _ = _
  -- rw [one_smul]
  conv_lhs => apply AddCon.lift_coe
  simp

theorem liftAux_tprodCoeff (φ : MultilinearMap R s E) (z : R) (f : Π i, s i) :
    liftAux φ (tprodCoeff R z f) = z • φ f := rfl

theorem liftAux.smul {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i) :
    liftAux φ (r • x) = r • liftAux φ x := by
  refine PiTensorProduct.induction_on' x ?_ ?_
  · intro z f
    rw [smul_tprodCoeff' r z f, liftAux_tprodCoeff, liftAux_tprodCoeff, smul_assoc]
  · intro z y ihz ihy
    rw [smul_add, (liftAux φ).map_add, ihz, ihy, (liftAux φ).map_add, smul_add]

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `MultilinearMap R s E` with the
property that its composition with the canonical `MultilinearMap R s E` is
the given multilinear map `φ`. -/
def lift : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) →ₗ[R] E where
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

variable {φ : MultilinearMap R s E}

@[simp]
theorem lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f :=
  liftAux_tprod φ f

theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ'.compMultilinearMap (PiTensorProduct.tprod R) = φ) : φ' = lift φ :=
  ext <| H.symm ▸ (lift.symm_apply_apply φ).symm

theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (PiTensorProduct.tprod R f) = φ f) :
    φ' = lift φ :=
  lift.unique' (MultilinearMap.ext H)

@[simp]
theorem lift_symm (φ' : (⨂[R] i, s i) →ₗ[R] E) : lift.symm φ' = φ'.compMultilinearMap (tprod R) :=
  rfl

@[simp]
theorem lift_tprod : lift (tprod R : MultilinearMap R s _) = LinearMap.id :=
  Eq.symm <| lift.unique' rfl

end lift

section map

variable {t t' : ι → Type*}
variable [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]
variable [∀ i, AddCommMonoid (t' i)] [∀ i, Module R (t' i)]
variable (g : Π i, t i →ₗ[R] t' i) (f : Π i, s i →ₗ[R] t i)

/--
Let `sᵢ` and `tᵢ` be two families of `R`-modules.
Let `f` be a family of `R`-linear maps between `sᵢ` and `tᵢ`, i.e. `f : Πᵢ sᵢ → tᵢ`,
then there is an induced map `⨂ᵢ sᵢ → ⨂ᵢ tᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.

This is `TensorProduct.map` for an arbitrary family of modules.
-/
def map : (⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i :=
  lift <| (tprod R).compLinearMap f

@[simp] lemma map_tprod (x : Π i, s i) :
    map f (tprod R x) = tprod R fun i ↦ f i (x i) :=
  lift.tprod _

-- No lemmas about associativity, because we don't have associativity of `PiTensorProduct` yet.

theorem map_range_eq_span_tprod :
    LinearMap.range (map f) =
      Submodule.span R {t | ∃ (m : Π i, s i), tprod R (fun i ↦ f i (m i)) = t} := by
  rw [← Submodule.map_top, ← span_tprod_eq_top, Submodule.map_span, ← Set.range_comp]
  apply congrArg; ext x
  simp only [Set.mem_range, comp_apply, map_tprod, Set.mem_setOf_eq]

/-- Given submodules `p i ⊆ s i`, this is the natural map: `⨂[R] i, p i → ⨂[R] i, s i`.
This is `TensorProduct.mapIncl` for an arbitrary family of modules.
-/
@[simp]
def mapIncl (p : Π i, Submodule R (s i)) : (⨂[R] i, p i) →ₗ[R] ⨂[R] i, s i :=
  map fun (i : ι) ↦ (p i).subtype

theorem map_comp : map (fun (i : ι) ↦ g i ∘ₗ f i) = map g ∘ₗ map f := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.coe_comp, Function.comp_apply]

theorem lift_comp_map (h : MultilinearMap R t E) :
    lift h ∘ₗ map f = lift (h.compLinearMap f) := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    map_tprod, lift.tprod, MultilinearMap.compLinearMap_apply]

attribute [local ext high] ext

@[simp]
theorem map_id : map (fun i ↦ (LinearMap.id : s i →ₗ[R] s i)) = .id := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, LinearMap.id_coe, id_eq]

@[simp]
protected theorem map_one : map (fun (i : ι) ↦ (1 : s i →ₗ[R] s i)) = 1 :=
  map_id

protected theorem map_mul (f₁ f₂ : Π i, s i →ₗ[R] s i) :
    map (fun i ↦ f₁ i * f₂ i) = map f₁ * map f₂ :=
  map_comp f₁ f₂

/-- Upgrading `PiTensorProduct.map` to a `MonoidHom` when `s = t`. -/
@[simps]
def mapMonoidHom : (Π i, s i →ₗ[R] s i) →* ((⨂[R] i, s i) →ₗ[R] ⨂[R] i, s i) where
  toFun := map
  map_one' := PiTensorProduct.map_one
  map_mul' := PiTensorProduct.map_mul

@[simp]
protected theorem map_pow (f : Π i, s i →ₗ[R] s i) (n : ℕ) :
    map (f ^ n) = map f ^ n := map_pow mapMonoidHom _ _

open Function in
private theorem map_add_smul_aux [DecidableEq ι] (i : ι) (x : Π i, s i) (u : s i →ₗ[R] t i) :
    (fun j ↦ update f i u j (x j)) = update (fun j ↦ (f j) (x j)) i (u (x i)) := by
  ext j
  exact apply_update (fun i F => F (x i)) f i u j

open Function in
protected theorem map_update_add [DecidableEq ι] (i : ι) (u v : s i →ₗ[R] t i) :
    map (update f i (u + v)) = map (update f i u) + map (update f i v) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.add_apply,
    MultilinearMap.map_update_add]

open Function in
protected theorem map_update_smul [DecidableEq ι] (i : ι) (c : R) (u : s i →ₗ[R] t i) :
    map (update f i (c • u)) = c • map (update f i u) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, map_tprod, map_add_smul_aux, LinearMap.smul_apply,
    MultilinearMap.map_update_smul]

variable (R s t)

/-- The tensor of a family of linear maps from `sᵢ` to `tᵢ`, as a multilinear map of
the family.
-/
@[simps]
noncomputable def mapMultilinear :
    MultilinearMap R (fun (i : ι) ↦ s i →ₗ[R] t i) ((⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i) where
  toFun := map
  map_update_smul' _ _ _ _ := PiTensorProduct.map_update_smul _ _ _ _
  map_update_add' _ _ _ _ := PiTensorProduct.map_update_add _ _ _ _

variable {R s t}

/--
Let `sᵢ` and `tᵢ` be families of `R`-modules.
Then there is an `R`-linear map between `⨂ᵢ Hom(sᵢ, tᵢ)` and `Hom(⨂ᵢ sᵢ, ⨂ tᵢ)` defined by
`⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ fᵢ aᵢ`.

This is `TensorProduct.homTensorHomMap` for an arbitrary family of modules.

Note that `PiTensorProduct.piTensorHomMap (tprod R f)` is equal to `PiTensorProduct.map f`.
-/
def piTensorHomMap : (⨂[R] i, s i →ₗ[R] t i) →ₗ[R] (⨂[R] i, s i) →ₗ[R] ⨂[R] i, t i :=
  lift.toLinearMap ∘ₗ lift (MultilinearMap.piLinearMap <| tprod R)

@[simp] lemma piTensorHomMap_tprod_tprod (f : Π i, s i →ₗ[R] t i) (x : Π i, s i) :
    piTensorHomMap (tprod R f) (tprod R x) = tprod R fun i ↦ f i (x i) := by
  simp [piTensorHomMap]

lemma piTensorHomMap_tprod_eq_map (f : Π i, s i →ₗ[R] t i) :
    piTensorHomMap (tprod R f) = map f := by
  ext; simp

/-- If `s i` and `t i` are linearly equivalent for every `i` in `ι`, then `⨂[R] i, s i` and
`⨂[R] i, t i` are linearly equivalent.

This is the n-ary version of `TensorProduct.congr`
-/
noncomputable def congr (f : Π i, s i ≃ₗ[R] t i) :
    (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i, t i :=
  .ofLinear
    (map (fun i ↦ f i))
    (map (fun i ↦ (f i).symm))
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π i, s i) :
    congr f (tprod R m) = tprod R (fun (i : ι) ↦ (f i) (m i)) := by
  simp only [congr, LinearEquiv.ofLinear_apply, map_tprod, LinearEquiv.coe_coe]

@[simp]
theorem congr_symm_tprod (f : Π i, s i ≃ₗ[R] t i) (p : Π i, t i) :
    (congr f).symm (tprod R p) = tprod R (fun (i : ι) ↦ (f i).symm (p i)) := by
  simp only [congr, LinearEquiv.ofLinear_symm_apply, map_tprod, LinearEquiv.coe_coe]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules, then `f : Πᵢ sᵢ → tᵢ → t'ᵢ` induces an
element of `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))` defined by `⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `PiTensorProduct.map` for two arbitrary families of modules.
This is `TensorProduct.map₂` for families of modules.
-/
def map₂ (f : Π i, s i →ₗ[R] t i →ₗ[R] t' i) :
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] ⨂[R] i, t' i :=
  lift <| LinearMap.compMultilinearMap piTensorHomMap <| (tprod R).compLinearMap f

lemma map₂_tprod_tprod (f : Π i, s i →ₗ[R] t i →ₗ[R] t' i) (x : Π i, s i) (y : Π i, t i) :
    map₂ f (tprod R x) (tprod R y) = tprod R fun i ↦ f i (x i) (y i) := by
  simp [map₂]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a function from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`. -/
def piTensorHomMapFun₂ : (⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) →
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] (⨂[R] i, t' i) :=
  fun φ => lift <| LinearMap.compMultilinearMap piTensorHomMap <|
    (lift <| MultilinearMap.piLinearMap <| tprod R) φ

theorem piTensorHomMapFun₂_add (φ ψ : ⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) :
    piTensorHomMapFun₂ (φ + ψ) = piTensorHomMapFun₂ φ + piTensorHomMapFun₂ ψ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_add, LinearMap.compMultilinearMap_apply,
    lift.tprod, add_apply, LinearMap.add_apply]

theorem piTensorHomMapFun₂_smul (r : R) (φ : ⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) :
    piTensorHomMapFun₂ (r • φ) = r • piTensorHomMapFun₂ φ := by
  dsimp [piTensorHomMapFun₂]; ext; simp only [map_smul, LinearMap.compMultilinearMap_apply,
    lift.tprod, smul_apply, LinearMap.smul_apply]

/--
Let `sᵢ`, `tᵢ` and `t'ᵢ` be families of `R`-modules.
Then there is a linear map from `⨂ᵢ Hom(sᵢ, Hom(tᵢ, t'ᵢ))` to `Hom(⨂ᵢ sᵢ, Hom(⨂ tᵢ, ⨂ᵢ t'ᵢ))`
defined by `⨂ᵢ fᵢ ↦ ⨂ᵢ aᵢ ↦ ⨂ᵢ bᵢ ↦ ⨂ᵢ fᵢ aᵢ bᵢ`.

This is `TensorProduct.homTensorHomMap` for two arbitrary families of modules.
-/
def piTensorHomMap₂ : (⨂[R] i, s i →ₗ[R] t i →ₗ[R] t' i) →ₗ[R]
    (⨂[R] i, s i) →ₗ[R] (⨂[R] i, t i) →ₗ[R] (⨂[R] i, t' i) where
  toFun := piTensorHomMapFun₂
  map_add' x y := piTensorHomMapFun₂_add x y
  map_smul' x y :=  piTensorHomMapFun₂_smul x y

@[simp] lemma piTensorHomMap₂_tprod_tprod_tprod
    (f : ∀ i, s i →ₗ[R] t i →ₗ[R] t' i) (a : ∀ i, s i) (b : ∀ i, t i) :
    piTensorHomMap₂ (tprod R f) (tprod R a) (tprod R b) = tprod R (fun i ↦ f i (a i) (b i)) := by
  simp [piTensorHomMapFun₂, piTensorHomMap₂]

end map

section

variable (R M)

variable (s) in
/-- Re-index the components of the tensor power by `e`. -/
def reindex (e : ι ≃ ι₂) : (⨂[R] i : ι, s i) ≃ₗ[R] ⨂[R] i : ι₂, s (e.symm i) :=
  let f := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι₂), s (e.symm i)) e
  let g := domDomCongrLinearEquiv' R R s (⨂[R] (i : ι), s i) e
  LinearEquiv.ofLinear (lift <| f.symm <| tprod R) (lift <| g <| tprod R) (by aesop) (by aesop)

end

@[simp]
theorem reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i) :
    reindex R s e (tprod R f) = tprod R fun i ↦ f (e.symm i) := by
  dsimp [reindex]
  exact liftAux_tprod _ f

@[simp]
theorem reindex_comp_tprod (e : ι ≃ ι₂) :
    (reindex R s e).compMultilinearMap (tprod R) =
    (domDomCongrLinearEquiv' R R s _ e).symm (tprod R) :=
  MultilinearMap.ext <| reindex_tprod e

theorem lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i ↦ s (e.symm i)) E) :
    lift φ ∘ₗ (reindex R s e) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) := by
  ext; simp [reindex]

@[simp]
theorem lift_comp_reindex_symm (e : ι ≃ ι₂) (φ : MultilinearMap R s E) :
    lift φ ∘ₗ (reindex R s e).symm = lift (domDomCongrLinearEquiv' R R s _ e φ) := by
  ext; simp [reindex]

theorem lift_reindex
    (e : ι ≃ ι₂) (φ : MultilinearMap R (fun i ↦ s (e.symm i)) E) (x : ⨂[R] i, s i) :
    lift φ (reindex R s e x) = lift ((domDomCongrLinearEquiv' R R s _ e).symm φ) x :=
  LinearMap.congr_fun (lift_comp_reindex e φ) x

@[simp]
theorem lift_reindex_symm
    (e : ι ≃ ι₂) (φ : MultilinearMap R s E) (x : ⨂[R] i, s (e.symm i)) :
    lift φ (reindex R s e |>.symm x) = lift (domDomCongrLinearEquiv' R R s _ e φ) x :=
  LinearMap.congr_fun (lift_comp_reindex_symm e φ) x

@[simp]
theorem reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
    (reindex R s e).trans (reindex R _ e') = reindex R s (e.trans e') := by
  apply LinearEquiv.toLinearMap_injective
  ext f
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply,
    reindex_comp_tprod]
  congr

theorem reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, s i) :
    reindex R _ e' (reindex R s e x) = reindex R s (e.trans e') x :=
  LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R s (e.trans e')) x

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
theorem reindex_symm (e : ι ≃ ι₂) :
    (reindex R (fun _ ↦ M) e).symm = reindex R (fun _ ↦ M) e.symm := by
  ext x
  simp [reindex]

@[simp]
theorem reindex_refl : reindex R s (Equiv.refl ι) = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  ext
  simp only [Equiv.refl_symm, Equiv.refl_apply, reindex, domDomCongrLinearEquiv',
    LinearEquiv.coe_symm_mk, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.refl_toLinearMap, LinearMap.id_coe, id_eq]
  simp

variable {t : ι → Type*}
variable [∀ i, AddCommMonoid (t i)] [∀ i, Module R (t i)]

/-- Re-indexing the components of the tensor product by an equivalence `e` is compatible
with `PiTensorProduct.map`. -/
theorem map_comp_reindex_eq (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) :
    map (fun i ↦ f (e.symm i)) ∘ₗ reindex R s e = reindex R t e ∘ₗ map f := by
  ext m
  simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearMap.comp_apply, reindex_tprod, map_tprod]

theorem map_reindex (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s i) :
    map (fun i ↦ f (e.symm i)) (reindex R s e x) = reindex R t e (map f x) :=
  DFunLike.congr_fun (map_comp_reindex_eq _ _) _

theorem map_comp_reindex_symm (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) :
    map f ∘ₗ (reindex R s e).symm = (reindex R t e).symm ∘ₗ map (fun i => f (e.symm i)) := by
  ext m
  apply LinearEquiv.injective (reindex R t e)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, ← map_reindex, LinearEquiv.apply_symm_apply, map_tprod]

theorem map_reindex_symm (f : Π i, s i →ₗ[R] t i) (e : ι ≃ ι₂) (x : ⨂[R] i, s (e.symm i)) :
    map f ((reindex R s e).symm x) = (reindex R t e).symm (map (fun i ↦ f (e.symm i)) x) :=
  DFunLike.congr_fun (map_comp_reindex_symm _ _) _

variable (ι)

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
def isEmptyEquiv [IsEmpty ι] : (⨂[R] i : ι, s i) ≃ₗ[R] R where
  toFun := lift (constOfIsEmpty R _ 1)
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
  LinearEquiv.ofLinear
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
lemma subsingletonEquiv_symm_apply' (x : M) :
  (subsingletonEquiv (s := fun _ ↦ M) i₀).symm x = (tprod R fun _ ↦ x) := by
  simp [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod]

end subsingleton

variable (R M)

section tmulEquivDep

variable (N : ι ⊕ ι₂ → Type*) [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type. If `N` is a constant family of
modules, use the non-dependent version `PiTensorProduct.tmulEquiv` instead. -/
def tmulEquivDep :
    (⨂[R] i₁, N (.inl i₁)) ⊗[R] (⨂[R] i₂, N (.inr i₂)) ≃ₗ[R] ⨂[R] i, N i :=
  LinearEquiv.ofLinear
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

/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type.

See `PiTensorProduct.tmulEquivDep` for the dependent version. -/
def tmulEquiv :
    (⨂[R] (_ : ι), M)  ⊗[R] (⨂[R] (_ : ι₂), M) ≃ₗ[R] ⨂[R] (_ : ι ⊕ ι₂), M :=
  tmulEquivDep R (fun _ ↦ M)

@[simp]
theorem tmulEquiv_apply (a : ι → M) (b : ι₂ → M) :
    tmulEquiv R M ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, Sum.elim a b i := by
  simp [tmulEquiv, Sum.elim]

@[simp]
theorem tmulEquiv_symm_apply (a : ι ⊕ ι₂ → M) :
    (tmulEquiv R M).symm (⨂ₜ[R] i, a i) =
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

/- Unlike for the binary tensor product, we require `R` to be a `CommRing` here, otherwise
this is false in the case where `ι` is empty. -/
instance : AddCommGroup (⨂[R] i, s i) :=
  Module.addCommMonoidToAddCommGroup R

end PiTensorProduct

end Ring
