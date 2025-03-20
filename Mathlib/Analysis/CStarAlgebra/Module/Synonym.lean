/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.UniformGroup.Basic

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

* `WithCStarModule E`: a copy of `E` to be equipped with a `CStarModule A` structure. Note that
  `A` is an `outParam` in the class `CStarModule`, so it can be inferred from the type of `E`.
* `WithCStarModule.equiv E`: the canonical equivalence between `WithCStarModule E` and `E`.
* `WithCStarModule.linearEquiv ℂ A E`: the canonical `ℂ`-module isomorphism between
  `WithCStarModule E` and `E`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type, and allows all the structure-copying code to be shared.
-/

/-- A type synonym for endowing a given type with a `CStarModule` structure.
This has the scoped notation `C⋆ᵐᵒᵈ` in the WithCStarModule namespace.

Note: because the C⋆-algebra `A` over which `E` is a `CStarModule` is listed as an `outParam` in
that class, we don't pass it as an unused argument to `WithCStarModule`, unlike the `p` parameter
in `WithLp`, which can vary. -/
def WithCStarModule (E : Type*) := E

namespace WithCStarModule

@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ" => WithCStarModule

section Basic

variable (R R' E : Type*)

/-- The canonical equivalence between `WithCStarModule E` and `E`. This should always be used to
convert back and forth between the representations. -/
def equiv : WithCStarModule E ≃ E := Equiv.refl _

instance instNontrivial [Nontrivial E] : Nontrivial (WithCStarModule E) := ‹Nontrivial E›
instance instInhabited [Inhabited E] : Inhabited (WithCStarModule E) := ‹Inhabited E›
instance instNonempty [Nonempty E] : Nonempty (WithCStarModule E) := ‹Nonempty E›
instance instUnique [Unique E] : Unique (WithCStarModule E) := ‹Unique E›

/-! ## `WithCStarModule E` inherits various module-adjacent structures from `E`. -/

instance instZero [Zero E] : Zero (WithCStarModule E) := ‹Zero E›
instance instAdd [Add E] : Add (WithCStarModule E) := ‹Add E›
instance instSub [Sub E] : Sub (WithCStarModule E) := ‹Sub E›
instance instNeg [Neg E] : Neg (WithCStarModule E) := ‹Neg E›
instance instAddMonoid [AddMonoid E] : AddMonoid (WithCStarModule E) := ‹AddMonoid E›
instance instSubNegMonoid [SubNegMonoid E] : SubNegMonoid (WithCStarModule E) := ‹SubNegMonoid E›
instance instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid (WithCStarModule E) :=
  ‹SubNegZeroMonoid E›

instance instAddCommGroup [AddCommGroup E] : AddCommGroup (WithCStarModule E) := ‹AddCommGroup E›

instance instSMul {R : Type*} [SMul R E] : SMul R (WithCStarModule E) := ‹SMul R E›

instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R (WithCStarModule E) := ‹Module R E›

instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' (WithCStarModule E) :=
  ‹IsScalarTower R R' E›

instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' (WithCStarModule E) :=
  ‹SMulCommClass R R' E›

section Equiv

variable {R E}
variable [SMul R E] (c : R) (x y : WithCStarModule E) (x' y' : E)

/-! `WithCStarModule.equiv` preserves the module structure. -/

section AddCommGroup

variable [AddCommGroup E]

@[simp]
theorem equiv_zero : equiv E 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero : (equiv E).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : equiv E (x + y) = equiv E x + equiv E y :=
  rfl

@[simp]
theorem equiv_symm_add :
    (equiv E).symm (x' + y') = (equiv E).symm x' + (equiv E).symm y' :=
  rfl

@[simp]
theorem equiv_sub : equiv E (x - y) = equiv E x - equiv E y :=
  rfl

@[simp]
theorem equiv_symm_sub :
    (equiv E).symm (x' - y') = (equiv E).symm x' - (equiv E).symm y' :=
  rfl

@[simp]
theorem equiv_neg : equiv E (-x) = -equiv E x :=
  rfl

@[simp]
theorem equiv_symm_neg : (equiv E).symm (-x') = -(equiv E).symm x' :=
  rfl

end AddCommGroup

@[simp]
theorem equiv_smul : equiv E (c • x) = c • equiv E x :=
  rfl

@[simp]
theorem equiv_symm_smul : (equiv E).symm (c • x') = c • (equiv E).symm x' :=
  rfl

end Equiv

/-- `WithCStarModule.equiv` as an additive equivalence. -/
def addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ E ≃+ E :=
  { AddEquiv.refl _ with
    toFun := equiv _
    invFun := (equiv _).symm }

/-- `WithCStarModule.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ E ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _
    invFun := (equiv _).symm }

lemma map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    (⊤ : Submodule R E).map (linearEquiv R E).symm = ⊤ := by
  ext x
  refine ⟨fun _  => trivial, fun _ => ?_⟩
  rw [Submodule.mem_map]
  exact ⟨linearEquiv R E x, by simp⟩

instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R (WithCStarModule E) := inferInstanceAs (Module.Finite R E)

/-! ## `WithCStarModule E` inherits the uniformity and bornology from `E`. -/

variable {E}

instance [u : UniformSpace E] : UniformSpace (C⋆ᵐᵒᵈ E) := u.comap <| equiv E

instance [Bornology E] : Bornology (C⋆ᵐᵒᵈ E) := Bornology.induced <| equiv E

/-- `WithCStarModule.equiv` as a uniform equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ E ≃ᵤ E :=
  equiv E |>.toUniformEquivOfIsUniformInducing ⟨rfl⟩

/-- `WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
@[simps! apply symm_apply]
def equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ E ≃L[R] E :=
  { linearEquiv R E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

instance [UniformSpace E] [CompleteSpace E] : CompleteSpace (C⋆ᵐᵒᵈ E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance

instance [AddCommGroup E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd (C⋆ᵐᵒᵈ E) :=
  ContinuousAdd.induced (addEquiv E)

instance [AddCommGroup E] [UniformSpace E] [UniformAddGroup E] : UniformAddGroup (C⋆ᵐᵒᵈ E) :=
  UniformAddGroup.comap (addEquiv E)

instance [Semiring R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
    [ContinuousSMul R E] : ContinuousSMul R (C⋆ᵐᵒᵈ E) :=
  ContinuousSMul.induced (linearEquiv R E)

end Basic

/-! ## Prod

Register simplification lemmas for the applications of `WithCStarModule (E × F)` elements, as
the usual lemmas for `Prod` will not trigger. -/

section Prod

variable {R E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ (E × F)) (c : R)

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F]

@[simp]
theorem zero_fst : (0 : C⋆ᵐᵒᵈ (E × F)).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : C⋆ᵐᵒᵈ (E × F)).snd = 0 :=
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
theorem equiv_fst (x : C⋆ᵐᵒᵈ (E × F)) : (equiv (E × F) x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_snd (x : C⋆ᵐᵒᵈ (E × F)) : (equiv (E × F) x).snd = x.snd :=
  rfl

@[simp]
theorem equiv_symm_fst (x : E × F) : ((equiv (E × F)).symm x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_symm_snd (x : E × F) : ((equiv (E × F)).symm x).snd = x.snd :=
  rfl

end Prod

/-! ## Pi

Register simplification lemmas for the applications of `WithCStarModule (Π i, E i)` elements, as
the usual lemmas for `Pi` will not trigger.

We also provide a `CoeFun` instance for `WithCStarModule (Π i, E i)`. -/

section Pi

/- The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`. -/
instance {ι : Type*} (E : ι → Type*) : CoeFun (C⋆ᵐᵒᵈ (Π i, E i)) (fun _ ↦ Π i, E i) where
  coe := WithCStarModule.equiv _

@[ext]
protected theorem ext {ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ (Π i, E i)}
    (h : ∀ i, x i = y i) : x = y :=
  funext h

variable {R ι : Type*} {E : ι → Type*}
variable [∀ i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ (Π i, E i)) (i : ι)

section AddCommGroup

variable [∀ i, AddCommGroup (E i)]

@[simp]
theorem zero_apply : (0 : C⋆ᵐᵒᵈ (Π i, E i)) i = 0 :=
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
theorem equiv_pi_apply (i : ι) : equiv _ x i = x i :=
  rfl

@[simp]
theorem equiv_symm_pi_apply (x : ∀ i, E i) (i : ι) :
    (WithCStarModule.equiv _).symm x i = x i :=
  rfl

end Pi

end WithCStarModule
