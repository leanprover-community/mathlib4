/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Type synonym for types with a `CStarModule` structure

It is often the case that we want to construct a `CStarModule` instance on a type that is already
endowed with a norm, but this norm is not the one associated to its `CStarModule` structure. For
this reason, we create a type synonym `WithCStarModule` which is endowed with the requisite
`CStarModule` instance. We also introduce the scoped notation `C⋆ᵐᵒᵈ` for this type synonym.

The common use cases are, when `A` is a C⋆-algebra:

+ `E × F` where `E` and `F` are `CStarModule`s over `A`
+ `Π i, E i` where `E i` is a `CStarModule` over `A` and `i : ι` with `ι` a `Fintype`

In this way, the set up is very similar to the `WithLp` type synonym, although there is no way to
reuse `WithLp` because the norms *do not* coincide in general.

The `WithCStarModule` synonym is of vital importance, especially because the `CStarModule` class
marks `A` as an `outParam`. Indeed, we want to infer `A` from the type of `E`, but, as with modules,
a type `E` can be a `CStarModule` over different C⋆-algebras. For example, note that if `A` is a
C⋆-algebra, then so is `A × A`, and therefore we may consider both `A` and `A × A` as `CStarModule`s
over themselves, respectively. However, we may *also* consider `A × A` as a `CStarModule` over `A`.
However, by utilizing the type synonym, these actually correspond to *different types*, namely:

+ `A` as a `CStarModule` over `A` corresponds to `A`
+ `A × A` as a `CStarModule` over `A × A` corresponds to `A × A`
+ `A × A` as a `CStarModule` over `A` corresponds to `C⋆ᵐᵒᵈ (A × A)`

## Main definitions

* `WithCStarModule A E`: a copy of `E` to be equipped with a `CStarModule A` structure.
* `WithCStarModule.equiv A E`: the canonical equivalence between `WithCStarModule A E` and `E`.
* `WithCStarModule.linearEquiv ℂ A E`: the canonical `ℂ`-module isomorphism between
  `WithCStarModule A E` and `E`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type, and allows all the structure-copying code to be shared.
-/

set_option linter.unusedVariables false in
/-- A type synonym for endowing a given type with a `CStarModule` structure. This has the scoped
notation `C⋆ᵐᵒᵈ`. -/
@[nolint unusedArguments]
def WithCStarModule (A E : Type*) := E

namespace WithCStarModule

@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ(" A ", " E ")" => WithCStarModule A E

section Basic

variable (R R' A E : Type*)

/-- The canonical equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. This should always be used to
convert back and forth between the representations. -/
def equiv : WithCStarModule A E ≃ E := Equiv.refl _

instance instNontrivial [Nontrivial E] : Nontrivial C⋆ᵐᵒᵈ(A, E) := ‹Nontrivial E›
instance instInhabited [Inhabited E] : Inhabited C⋆ᵐᵒᵈ(A, E) := ‹Inhabited E›
instance instNonempty [Nonempty E] : Nonempty C⋆ᵐᵒᵈ(A, E) := ‹Nonempty E›
instance instUnique [Unique E] : Unique C⋆ᵐᵒᵈ(A, E) := ‹Unique E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits various module-adjacent structures from `E`. -/

instance instZero [Zero E] : Zero C⋆ᵐᵒᵈ(A, E) := ‹Zero E›
instance instAdd [Add E] : Add C⋆ᵐᵒᵈ(A, E) := ‹Add E›
instance instSub [Sub E] : Sub C⋆ᵐᵒᵈ(A, E) := ‹Sub E›
instance instNeg [Neg E] : Neg C⋆ᵐᵒᵈ(A, E) := ‹Neg E›
instance instAddMonoid [AddMonoid E] : AddMonoid C⋆ᵐᵒᵈ(A, E) := ‹AddMonoid E›
instance instSubNegMonoid [SubNegMonoid E] : SubNegMonoid C⋆ᵐᵒᵈ(A, E) := ‹SubNegMonoid E›
instance instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid C⋆ᵐᵒᵈ(A, E) :=
  ‹SubNegZeroMonoid E›

instance instAddCommGroup [AddCommGroup E] : AddCommGroup C⋆ᵐᵒᵈ(A, E) := ‹AddCommGroup E›

instance instSMul {R : Type*} [SMul R E] : SMul R C⋆ᵐᵒᵈ(A, E) := ‹SMul R E›

instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R C⋆ᵐᵒᵈ(A, E) :=
  ‹Module R E›

instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹IsScalarTower R R' E›

instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹SMulCommClass R R' E›

section Equiv

variable {R A E}
variable [SMul R E] (c : R) (x y : C⋆ᵐᵒᵈ(A, E)) (x' y' : E)

/-! `WithCStarModule.equiv` preserves the module structure. -/

section AddCommGroup

variable [AddCommGroup E]

@[simp]
theorem equiv_zero : equiv A E 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero : (equiv A E).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : equiv A E (x + y) = equiv A E x + equiv A E y :=
  rfl

@[simp]
theorem equiv_symm_add :
    (equiv A E).symm (x' + y') = (equiv A E).symm x' + (equiv A E).symm y' :=
  rfl

@[simp]
theorem equiv_sub : equiv A E (x - y) = equiv A E x - equiv A E y :=
  rfl

@[simp]
theorem equiv_symm_sub :
    (equiv A E).symm (x' - y') = (equiv A E).symm x' - (equiv A E).symm y' :=
  rfl

@[simp]
theorem equiv_neg : equiv A E (-x) = -equiv A E x :=
  rfl

@[simp]
theorem equiv_symm_neg : (equiv A E).symm (-x') = -(equiv A E).symm x' :=
  rfl

end AddCommGroup

@[simp]
theorem equiv_smul : equiv A E (c • x) = c • equiv A E x :=
  rfl

@[simp]
theorem equiv_symm_smul : (equiv A E).symm (c • x') = c • (equiv A E).symm x' :=
  rfl

end Equiv

/-- `WithCStarModule.equiv` as an additive equivalence. -/
def addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ(A, E) ≃+ E :=
  { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/-- `WithCStarModule.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

lemma map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    (⊤ : Submodule R E).map (linearEquiv R A E).symm = ⊤ := by
  ext x
  refine ⟨fun _  => trivial, fun _ => ?_⟩
  rw [Submodule.mem_map]
  exact ⟨linearEquiv R A E x, by simp⟩

instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R C⋆ᵐᵒᵈ(A, E) := ‹Module.Finite R E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits the uniformity and bornology from `E`. -/

variable {A E}

instance [u : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E) := u.comap <| equiv A E

instance [Bornology E] : Bornology C⋆ᵐᵒᵈ(A, E) := Bornology.induced <| equiv A E


/-- `WithCStarModule.equiv` as a uniform equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. -/
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ(A, E) ≃ᵤ E :=
  equiv A E |>.toUniformEquivOfIsUniformInducing ⟨rfl⟩

/-- `WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
@[simps! apply symm_apply]
def equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃L[R] E :=
  { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

instance [UniformSpace E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance

instance [AddCommGroup E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E) :=
  ContinuousAdd.induced (addEquiv A E)

instance [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E) :=
  IsUniformAddGroup.comap (addEquiv A E)

instance [Semiring R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
    [ContinuousSMul R E] : ContinuousSMul R C⋆ᵐᵒᵈ(A, E) :=
  ContinuousSMul.induced (linearEquiv R A E)

end Basic

/-! ## Prod

Register simplification lemmas for the applications of `WithCStarModule (E × F)` elements, as
the usual lemmas for `Prod` will not trigger. -/

section Prod

variable {R A E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ(A, E × F)) (c : R)

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F]

@[simp]
theorem zero_fst : (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0 :=
  rfl

@[simp]
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

end AddCommGroup

@[simp]
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
theorem equiv_fst (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_snd (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).snd = x.snd :=
  rfl

@[simp]
theorem equiv_symm_fst (x : E × F) : ((equiv A (E × F)).symm x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_symm_snd (x : E × F) : ((equiv A (E × F)).symm x).snd = x.snd :=
  rfl

end Prod

/-! ## Pi

Register simplification lemmas for the applications of `WithCStarModule (Π i, E i)` elements, as
the usual lemmas for `Pi` will not trigger.

We also provide a `CoeFun` instance for `WithCStarModule (Π i, E i)`. -/

section Pi

/- The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`. -/
instance {A ι : Type*} (E : ι → Type*) : CoeFun (C⋆ᵐᵒᵈ(A, Π i, E i)) (fun _ ↦ Π i, E i) where
  coe := equiv _ _

@[ext]
protected theorem ext {A ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
    (h : ∀ i, x i = y i) : x = y :=
  funext h

variable {R A ι : Type*} {E : ι → Type*}
variable [∀ i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)

section AddCommGroup

variable [∀ i, AddCommGroup (E i)]

@[simp]
theorem zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0 :=
  rfl

@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

end AddCommGroup

@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
theorem equiv_pi_apply (i : ι) : equiv _ _ x i = x i :=
  rfl

@[simp]
theorem equiv_symm_pi_apply (x : ∀ i, E i) (i : ι) :
    (equiv A _).symm x i = x i :=
  rfl

end Pi

end WithCStarModule
