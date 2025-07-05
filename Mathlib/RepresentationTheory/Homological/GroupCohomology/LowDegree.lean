/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cocycles and group cohomology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.

In `RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we define the `n`th group
cohomology of `A` to be the cohomology of a complex `inhomogeneousCochains A`, whose objects are
`(Fin n → G) → A`; this is unnecessarily unwieldy in low degree. Here, meanwhile, we define the one
and two cocycles and coboundaries as submodules of `Fun(G, A)` and `Fun(G × G, A)`, and provide
maps to `H1` and `H2`.

We also show that when the representation on `A` is trivial, `H¹(G, A) ≃ Hom(G, A)`.

Given an additive or multiplicative abelian group `A` with an appropriate scalar action of `G`,
we provide support for turning a function `f : G → A` satisfying the 1-cocycle identity into an
element of the `oneCocycles` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries. The
multiplicative case, starting with the section `IsMulCocycle`, just mirrors the additive case;
unfortunately `@[to_additive]` can't deal with scalar actions.

The file also contains an identification between the definitions in
`RepresentationTheory/Homological/GroupCohomology/Basic.lean`, `groupCohomology.cocycles A n`, and
the `nCocycles` in this file, for `n = 0, 1, 2`.

## Main definitions

* `groupCohomology.H0Iso A`: isomorphism between `H⁰(G, A)` and the invariants `Aᴳ` of the
  `G`-representation on `A`.
* `groupCohomology.H1π A`: epimorphism from the 1-cocycles
  (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) to `H¹(G, A)`.
* `groupCohomology.H2π A`: epimorphism from the 2-cocycles
  (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) to `H²(G, A)`.
* `groupCohomology.H1IsoOfIsTrivial`: the isomorphism `H¹(G, A) ≅ Hom(G, A)` when the
  representation on `A` is trivial.

## TODO

* The relationship between `H2` and group extensions
* Nonabelian group cohomology

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupCohomology

section Cochains

variable [DecidableEq G]

/-- The 0th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def zeroCochainsIso : (inhomogeneousCochains A).X 0 ≅ A.V :=
  (LinearEquiv.funUnique (Fin 0 → G) k A).toModuleIso

@[deprecated (since := "2025-05-09")] noncomputable alias zeroCochainsLequiv := zeroCochainsIso

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def oneCochainsIso : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G → A) :=
  (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

@[deprecated (since := "2025-05-09")] noncomputable alias oneCochainsLequiv := oneCochainsIso

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G², A)` as a `k`-module. -/
def twoCochainsIso : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

@[deprecated (since := "2025-05-09")] noncomputable alias twoCochainsLequiv := twoCochainsIso

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G³, A)` as a `k`-module. -/
def threeCochainsIso : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

@[deprecated (since := "2025-05-09")] noncomputable alias threeCochainsLequiv := threeCochainsIso

end Cochains

section Differentials

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
@[simps!]
def dZero : A.V ⟶ ModuleCat.of k (G → A) :=
  ModuleCat.ofHom
  { toFun m g := A.ρ g m - m
    map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub] }

theorem dZero_ker_eq_invariants : LinearMap.ker (dZero A).hom = invariants A.ρ := by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl

@[simp] theorem dZero_eq_zero [A.IsTrivial] : dZero A = 0 := by
  ext
  rw [dZero_hom_apply, isTrivial_apply, sub_self]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma subtype_comp_dZero : ModuleCat.ofHom (A.ρ.invariants.subtype) ≫ dZero A = 0 := by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
@[simps!]
def dOne : ModuleCat.of k (G → A) ⟶ ModuleCat.of k (G × G → A) :=
  ModuleCat.ofHom
  { toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
    map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub] }

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
@[simps!]
def dTwo : ModuleCat.of k (G × G → A) ⟶ ModuleCat.of k (G × G × G → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
    map_add' x y :=
      funext fun g => by
        dsimp
        rw [map_add, add_sub_add_comm (A.ρ _ _), add_sub_assoc, add_sub_add_comm, add_add_add_comm,
          add_sub_assoc, add_sub_assoc]
    map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub] }

variable [DecidableEq G]

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dZero` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C⁰(G, A) ---d⁰---> C¹(G, A)
  |                    |
  |                    |
  |                    |
  v                    v
  A ---- dZero ---> Fun(G, A)
```
where the vertical arrows are `zeroCochainsIso` and `oneCochainsIso` respectively.
-/
theorem comp_dZero_eq :
    (zeroCochainsIso A).hom ≫ dZero A =
      (inhomogeneousCochains A).d 0 1 ≫ (oneCochainsIso A).hom := by
  ext x y
  show A.ρ y (x default) - x default = _ + ({0} : Finset _).sum _
  simp_rw [Fin.val_eq_zero, zero_add, pow_one, neg_smul, one_smul,
    Finset.sum_singleton, sub_eq_add_neg]
  rcongr i <;> exact Fin.elim0 i

@[deprecated (since := "2025-05-09")] alias dZero_comp_eq := comp_dZero_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dZero_comp_inv :
    (zeroCochainsIso A).inv ≫ (inhomogeneousCochains A).d 0 1 =
      dZero A ≫ (oneCochainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dZero_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dOne` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C¹(G, A) ---d¹-----> C²(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  Fun(G, A) -dOne-> Fun(G × G, A)
```
where the vertical arrows are `oneCochainsIso` and `twoCochainsIso` respectively.
-/
theorem comp_dOne_eq :
    (oneCochainsIso A).hom ≫ dOne A =
      (inhomogeneousCochains A).d 1 2 ≫ (twoCochainsIso A).hom := by
  ext x y
  show A.ρ y.1 (x _) - x _ + x _ =  _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

@[deprecated (since := "2025-05-09")] alias dOne_comp_eq := comp_dOne_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dOne_comp_inv :
    (oneCochainsIso A).inv ≫ (inhomogeneousCochains A).d 1 2 =
      dOne A ≫ (twoCochainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dOne_eq A⟩).w

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `dTwo` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
      C²(G, A) -------d²-----> C³(G, A)
        |                         |
        |                         |
        |                         |
        v                         v
  Fun(G × G, A) --dTwo--> Fun(G × G × G, A)
```
where the vertical arrows are `twoCochainsIso` and `threeCochainsIso` respectively.
-/
theorem comp_dTwo_eq :
    (twoCochainsIso A).hom ≫ dTwo A =
      (inhomogeneousCochains A).d 2 3 ≫ (threeCochainsIso A).hom := by
  ext x y
  show A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

@[deprecated (since := "2025-05-09")] alias dTwo_comp_eq := comp_dTwo_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_dTwo_comp_inv :
    (twoCochainsIso A).inv ≫ (inhomogeneousCochains A).d 2 3 =
      dTwo A ≫ (threeCochainsIso A).inv :=
  (CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w

omit [DecidableEq G] in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem dZero_comp_dOne : dZero A ≫ dOne A = 0 := by
  ext
  simp [Pi.zero_apply (M := fun _ => A)]

@[deprecated (since := "2025-05-14")] alias dOne_comp_dZero := dZero_comp_dOne

omit [DecidableEq G] in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem dOne_comp_dTwo : dOne A ≫ dTwo A = 0 := by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

@[deprecated (since := "2025-05-14")] alias dTwo_comp_dOne := dOne_comp_dTwo

open ShortComplex

/-- The (exact) short complex `A.ρ.invariants ⟶ A ⟶ (G → A)`. -/
@[simps! -isSimp f g]
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (subtype_comp_dZero A)

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)`. -/
@[simps! -isSimp f g]
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk (dZero A) (dOne A) (dZero_comp_dOne A)

/-- The short complex `Fun(G, A) --dOne--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)`. -/
@[simps! -isSimp f g]
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk (dOne A) (dTwo A) (dOne_comp_dTwo A)

end Differentials

section Cocycles

/-- The 1-cocycles `Z¹(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def oneCocycles : Submodule k (G → A) := LinearMap.ker (dOne A).hom

/-- The 2-cocycles `Z²(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G × G, A) → Fun(G × G × G, A)` sending
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
def twoCocycles : Submodule k (G × G → A) := LinearMap.ker (dTwo A).hom

variable {A}

instance : FunLike (oneCocycles A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem oneCocycles.coe_mk (f : G → A) (hf) : ((⟨f, hf⟩ : oneCocycles A) : G → A) = f := rfl

@[simp]
theorem oneCocycles.val_eq_coe (f : oneCocycles A) : f.1 = f := rfl

@[ext]
theorem oneCocycles_ext {f₁ f₂ : oneCocycles A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

theorem mem_oneCocycles_def (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, dOne_hom_apply, Prod.forall]
    rfl

theorem mem_oneCocycles_iff (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [mem_oneCocycles_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

@[simp] theorem oneCocycles_map_one (f : oneCocycles A) : f 1 = 0 := by
  have := (mem_oneCocycles_def f).1 f.2 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this

@[simp] theorem oneCocycles_map_inv (f : oneCocycles A) (g : G) :
    A.ρ g (f g⁻¹) = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← oneCocycles_map_one f, ← mul_inv_cancel g,
    (mem_oneCocycles_iff f).1 f.2 g g⁻¹]

theorem dZero_apply_mem_oneCocycles (x : A) :
    dZero A x ∈ oneCocycles A :=
  dZero_comp_dOne_apply _ _

@[simp]
theorem oneCocycles.dOne_apply (x : oneCocycles A) :
    dOne A x = 0 := x.2

theorem oneCocycles_map_mul_of_isTrivial [A.IsTrivial] (f : oneCocycles A) (g h : G) :
    f (g * h) = f g + f h := by
  rw [(mem_oneCocycles_iff f).1 f.2, isTrivial_apply A.ρ g (f h), add_comm]

theorem mem_oneCocycles_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    f ∘ Additive.ofMul ∈ oneCocycles A :=
  (mem_oneCocycles_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      oneCocycles_map_mul_of_isTrivial, isTrivial_apply A.ρ g (f (Additive.ofMul h)),
      add_comm (f (Additive.ofMul g))]

variable (A) in
/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps!]
def oneCocyclesIsoOfIsTrivial [hA : A.IsTrivial] :
    ModuleCat.of k (oneCocycles A) ≅ ModuleCat.of k (Additive G →+ A) :=
  LinearEquiv.toModuleIso
  { toFun f :=
      { toFun := f ∘ Additive.toMul
        map_zero' := oneCocycles_map_one f
        map_add' := oneCocycles_map_mul_of_isTrivial f }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun f :=
      { val := f
        property := mem_oneCocycles_of_addMonoidHom f } }

@[deprecated (since := "2025-05-09")]
noncomputable alias oneCocyclesLequivOfIsTrivial := oneCocyclesIsoOfIsTrivial

instance : FunLike (twoCocycles A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem twoCocycles.coe_mk (f : G × G → A) (hf) : ((⟨f, hf⟩ : twoCocycles A) : G × G → A) = f := rfl

@[simp]
theorem twoCocycles.val_eq_coe (f : twoCocycles A) : f.1 = f := rfl

@[ext]
theorem twoCocycles_ext {f₁ f₂ : twoCocycles A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

theorem mem_twoCocycles_def (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, dTwo_hom_apply, Prod.forall]
    rfl

theorem mem_twoCocycles_iff (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_twoCocycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

theorem twoCocycles_map_one_fst (f : twoCocycles A) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((mem_twoCocycles_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

theorem twoCocycles_map_one_snd (f : twoCocycles A) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (mem_twoCocycles_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

lemma twoCocycles_ρ_map_inv_sub_map_inv (f : twoCocycles A) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (mem_twoCocycles_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, twoCocycles_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

theorem dOne_apply_mem_twoCocycles (x : G → A) :
    dOne A x ∈ twoCocycles A :=
  dOne_comp_dTwo_apply _ _

@[simp]
theorem twoCocycles.dTwo_apply (x : twoCocycles A) :
    dTwo A x = 0 := x.2

end Cocycles

section Coboundaries

/-- The 1-coboundaries `B¹(G, A)` of `A : Rep k G`, defined as the image of the map
`A → Fun(G, A)` sending `(a, g) ↦ ρ_A(g)(a) - a.` -/
def oneCoboundaries : Submodule k (G → A) :=
  LinearMap.range (dZero A).hom

/-- The 2-coboundaries `B²(G, A)` of `A : Rep k G`, defined as the image of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def twoCoboundaries : Submodule k (G × G → A) :=
  LinearMap.range (dOne A).hom

variable {A}

instance : FunLike (oneCoboundaries A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem oneCoboundaries.coe_mk (f : G → A) (hf) :
    ((⟨f, hf⟩ : oneCoboundaries A) : G → A) = f := rfl

@[simp]
theorem oneCoboundaries.val_eq_coe (f : oneCoboundaries A) : f.1 = f := rfl

@[ext]
theorem oneCoboundaries_ext {f₁ f₂ : oneCoboundaries A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

variable (A) in
lemma oneCoboundaries_le_oneCocycles : oneCoboundaries A ≤ oneCocycles A := by
  rintro _ ⟨x, rfl⟩
  exact dZero_apply_mem_oneCocycles x

variable (A) in
/-- Natural inclusion `B¹(G, A) →ₗ[k] Z¹(G, A)`. -/
abbrev oneCoboundariesToOneCocycles : oneCoboundaries A →ₗ[k] oneCocycles A :=
  Submodule.inclusion (oneCoboundaries_le_oneCocycles A)

@[simp]
lemma oneCoboundariesToOneCocycles_apply (x : oneCoboundaries A) :
    oneCoboundariesToOneCocycles A x = x.1 := rfl

theorem oneCoboundaries_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    oneCoboundaries A = ⊥ := by
  simp_rw [oneCoboundaries, dZero_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

instance : FunLike (twoCoboundaries A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem twoCoboundaries.coe_mk (f : G × G → A) (hf) :
    ((⟨f, hf⟩ : twoCoboundaries A) : G × G → A) = f := rfl

@[simp]
theorem twoCoboundaries.val_eq_coe (f : twoCoboundaries A) : f.1 = f := rfl

@[ext]
theorem twoCoboundaries_ext {f₁ f₂ : twoCoboundaries A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) :
    f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

variable (A) in
lemma twoCoboundaries_le_twoCocycles : twoCoboundaries A ≤ twoCocycles A := by
  rintro _ ⟨x, rfl⟩
  exact dOne_apply_mem_twoCocycles x

variable (A) in
/-- Natural inclusion `B²(G, A) →ₗ[k] Z²(G, A)`. -/
abbrev twoCoboundariesToTwoCocycles : twoCoboundaries A →ₗ[k] twoCocycles A :=
  Submodule.inclusion (twoCoboundaries_le_twoCocycles A)

@[simp]
lemma twoCoboundariesToTwoCocycles_apply (x : twoCoboundaries A) :
    twoCoboundariesToTwoCocycles A x = x.1 := rfl

end Coboundaries

section IsCocycle

section

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-cocycle condition if
`f(gh) = g • f(h) + f(g)` for all `g, h : G`. -/
def IsOneCocycle (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g

/-- A function `f : G × G → A` satisfies the 2-cocycle condition if
`f(gh, j) + f(g, h) = g • f(h, j) + f(g, hj)` for all `g, h : G`. -/
def IsTwoCocycle (f : G × G → A) : Prop :=
  ∀ g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

end

section

variable {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]

theorem map_one_of_isOneCocycle {f : G → A} (hf : IsOneCocycle f) :
    f 1 = 0 := by
  simpa only [mul_one, one_smul, left_eq_add] using hf 1 1

theorem map_one_fst_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

theorem map_one_snd_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, add_left_inj] using hf g 1 1

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [MulAction G A]

@[scoped simp] theorem map_inv_of_isOneCocycle {f : G → A} (hf : IsOneCocycle f) (g : G) :
    g • f g⁻¹ = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← map_one_of_isOneCocycle hf, ← mul_inv_cancel g, hf g g⁻¹]

theorem smul_map_inv_sub_map_inv_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    g • f (g⁻¹, g) - f (g, g⁻¹) = f (1, 1) - f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isTwoCocycle hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

end

end IsCocycle

section IsCoboundary

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-coboundary condition if there's `x : A` such that
`g • x - x = f(g)` for all `g : G`. -/
def IsOneCoboundary (f : G → A) : Prop := ∃ x : A, ∀ g : G, g • x - x = f g

/-- A function `f : G × G → A` satisfies the 2-coboundary condition if there's `x : G → A` such
that `g • x(h) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def IsTwoCoboundary (f : G × G → A) : Prop :=
  ∃ x : G → A, ∀ g h : G, g • x h - x (g * h) + x g = f (g, h)

end IsCoboundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-cocycle condition, produces a 1-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def oneCocyclesOfIsOneCocycle {f : G → A} (hf : IsOneCocycle f) :
    oneCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_oneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isOneCocycle_of_mem_oneCocycles
    (f : G → A) (hf : f ∈ oneCocycles (Rep.ofDistribMulAction k G A)) :
    IsOneCocycle f :=
  fun _ _ => (mem_oneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-coboundary condition, produces a 1-coboundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
def oneCoboundariesOfIsOneCoboundary {f : G → A} (hf : IsOneCoboundary f) :
    oneCoboundaries (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose, funext hf.choose_spec⟩

theorem isOneCoboundary_of_mem_oneCoboundaries
    (f : G → A) (hf : f ∈ oneCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsOneCoboundary f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ => rfl⟩

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-cocycle condition, produces a 2-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def twoCocyclesOfIsTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) :
    twoCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_twoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

theorem isTwoCocycle_of_mem_twoCocycles
    (f : G × G → A) (hf : f ∈ twoCocycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCocycle f := (mem_twoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-coboundary condition, produces a 2-coboundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def twoCoboundariesOfIsTwoCoboundary {f : G × G → A} (hf : IsTwoCoboundary f) :
    twoCoboundaries (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose,funext fun g ↦ hf.choose_spec g.1 g.2⟩

theorem isTwoCoboundary_of_mem_twoCoboundaries
    (f : G × G → A) (hf : f ∈ twoCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoCoboundary f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ _ => rfl⟩

end ofDistribMulAction

/-! The next few sections, until the section `CocyclesIso`, are a multiplicative copy of the
previous few sections beginning with `IsCocycle`. Unfortunately `@[to_additive]` doesn't work with
scalar actions. -/

section IsMulCocycle

section

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-cocycle condition if
`f(gh) = g • f(h) * f(g)` for all `g, h : G`. -/
def IsMulOneCocycle (f : G → M) : Prop := ∀ g h : G, f (g * h) = g • f h * f g

/-- A function `f : G × G → M` satisfies the multiplicative 2-cocycle condition if
`f(gh, j) * f(g, h) = g • f(h, j) * f(g, hj)` for all `g, h : G`. -/
def IsMulTwoCocycle (f : G × G → M) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

end

section

variable {G M : Type*} [Monoid G] [CommGroup M] [MulAction G M]

theorem map_one_of_isMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) :
    f 1 = 1 := by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

theorem map_one_fst_of_isMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

theorem map_one_snd_of_isMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

end

section

variable {G M : Type*} [Group G] [CommGroup M] [MulAction G M]

@[scoped simp] theorem map_inv_of_isMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← map_one_of_isMulOneCocycle hf, ← mul_inv_cancel g, hf g g⁻¹]

theorem smul_map_inv_div_map_inv_of_isMulTwoCocycle
    {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    g • f (g⁻¹, g) / f (g, g⁻¹) = f (1, 1) / f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulTwoCocycle hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

end

end IsMulCocycle

section IsMulCoboundary

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-coboundary condition if there's `x : M`
such that `g • x / x = f(g)` for all `g : G`. -/
def IsMulOneCoboundary (f : G → M) : Prop := ∃ x : M, ∀ g : G, g • x / x = f g

/-- A function `f : G × G → M` satisfies the 2-coboundary condition if there's `x : G → M` such
that `g • x(h) / x(gh) * x(g) = f(g, h)` for all `g, h : G`. -/
def IsMulTwoCoboundary (f : G × G → M) : Prop :=
  ∃ x : G → M, ∀ g h : G, g • x h / x (g * h) * x g = f (g, h)

end IsMulCoboundary

section ofMulDistribMulAction

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-cocycle condition, produces a 1-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def oneCocyclesOfIsMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) :
    oneCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_oneCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulOneCocycle_of_mem_oneCocycles
    (f : G → M) (hf : f ∈ oneCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCocycle (Additive.toMul ∘ f) :=
  (mem_oneCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-coboundary condition, produces a
1-coboundary for the representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def oneCoboundariesOfIsMulOneCoboundary {f : G → M} (hf : IsMulOneCoboundary f) :
    oneCoboundaries (Rep.ofMulDistribMulAction G M) :=
  ⟨f, hf.choose, funext hf.choose_spec⟩

theorem isMulOneCoboundary_of_mem_oneCoboundaries
    (f : G → M) (hf : f ∈ oneCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCoboundary (M := M) (Additive.ofMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ =>  rfl⟩

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-cocycle condition, produces a 2-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def twoCocyclesOfIsMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) :
    twoCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_twoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

theorem isMulTwoCocycle_of_mem_twoCocycles
    (f : G × G → M) (hf : f ∈ twoCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCocycle (Additive.toMul ∘ f) :=
  (mem_twoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-coboundary condition, produces a
2-coboundary for the representation on `M` induced by the `MulDistribMulAction`. -/
def twoCoboundariesOfIsMulTwoCoboundary {f : G × G → M} (hf : IsMulTwoCoboundary f) :
    twoCoboundaries (Rep.ofMulDistribMulAction G M) :=
  ⟨f, hf.choose, funext fun g ↦ hf.choose_spec g.1 g.2⟩

theorem isMulTwoCoboundary_of_mem_twoCoboundaries
    (f : G × G → M) (hf : f ∈ twoCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCoboundary (M := M) (Additive.toMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ _ => rfl⟩

end ofMulDistribMulAction

open ShortComplex

section CocyclesIso

section zeroCocyclesIso

instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : dZero _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

variable [DecidableEq G]

/-- The arrow `A --dZero--> Fun(G, A)` is isomorphic to the differential
`(inhomogeneousCochains A).d 0 1` of the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso :
    Arrow.mk ((inhomogeneousCochains A).d 0 1) ≅ Arrow.mk (dZero A) :=
  Arrow.isoMk (zeroCochainsIso A) (oneCochainsIso A) (comp_dZero_eq A)

/-- The 0-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`A.ρ.invariants`, which is a simpler type. -/
def zeroCocyclesIso : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dZeroArrowIso A)

@[deprecated (since := "2025-06-12")]
noncomputable alias isoZeroCocycles := zeroCocyclesIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma zeroCocyclesIso_hom_comp_f :
    (zeroCocyclesIso A).hom ≫ (shortComplexH0 A).f =
      iCocycles A 0 ≫ (zeroCochainsIso A).hom := by
  dsimp [zeroCocyclesIso]
  apply KernelFork.mapOfIsLimit_ι

@[deprecated (since := "2025-06-12")]
alias isoZeroCocycles_hom_comp_subtype := zeroCocyclesIso_hom_comp_f

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma zeroCocyclesIso_inv_comp_iCocycles :
    (zeroCocyclesIso A).inv ≫ iCocycles A 0 =
      (shortComplexH0 A).f ≫ (zeroCochainsIso A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, zeroCocyclesIso_hom_comp_f]

@[deprecated (since := "2025-06-12")]
alias isoZeroCocycles_inv_comp_iCocycles := zeroCocyclesIso_inv_comp_iCocycles

end zeroCocyclesIso

section isoOneCocycles

variable [DecidableEq G]

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def shortComplexH1Iso : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A :=
  (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (zeroCochainsIso A) (oneCochainsIso A) (twoCochainsIso A)
      (comp_dZero_eq A) (comp_dOne_eq A)

/-- The 1-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`oneCocycles A`, which is a simpler type. -/
def isoOneCocycles : cocycles A 1 ≅ ModuleCat.of k (oneCocycles A) :=
  cyclesMapIso' (shortComplexH1Iso A) _ (shortComplexH1 A).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoOneCocycles_hom_comp_i :
    (isoOneCocycles A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.i =
      iCocycles A 1 ≫ (oneCochainsIso A).hom := by
  simp [isoOneCocycles, iCocycles, HomologicalComplex.iCycles, iCycles]

@[deprecated (since := "2025-05-09")]
alias isoOneCocycles_hom_comp_subtype := isoOneCocycles_hom_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoOneCocycles_inv_comp_iCocycles :
    (isoOneCocycles A).inv ≫ iCocycles A 1 =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ (oneCochainsIso A).inv :=
  (CommSq.horiz_inv ⟨isoOneCocycles_hom_comp_i A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCocycles_comp_isoOneCocycles_hom :
    toCocycles A 0 1 ≫ (isoOneCocycles A).hom =
      (zeroCochainsIso A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_dZero_eq,
    shortComplexH1_f]

end isoOneCocycles

section isoTwoCocycles

variable [DecidableEq G]

/-- The short complex `Fun(G, A) --dOne--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def shortComplexH2Iso :
    (inhomogeneousCochains A).sc 2 ≅ shortComplexH2 A :=
  (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (oneCochainsIso A) (twoCochainsIso A) (threeCochainsIso A)
      (comp_dOne_eq A) (comp_dTwo_eq A)

/-- The 2-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`twoCocycles A`, which is a simpler type. -/
def isoTwoCocycles : cocycles A 2 ≅ ModuleCat.of k (twoCocycles A) :=
  cyclesMapIso' (shortComplexH2Iso A) _ (shortComplexH2 A).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoTwoCocycles_hom_comp_i :
    (isoTwoCocycles A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.i =
      iCocycles A 2 ≫ (twoCochainsIso A).hom := by
  simp [isoTwoCocycles, iCocycles, HomologicalComplex.iCycles, iCycles]

@[deprecated (since := "2025-05-09")]
alias isoTwoCocycles_hom_comp_subtype := isoTwoCocycles_hom_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoTwoCocycles_inv_comp_iCocycles :
    (isoTwoCocycles A).inv ≫ iCocycles A 2 =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ (twoCochainsIso A).inv :=
  (CommSq.horiz_inv ⟨isoTwoCocycles_hom_comp_i A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCocycles_comp_isoTwoCocycles_hom :
    toCocycles A 1 2 ≫ (isoTwoCocycles A).hom =
      (oneCochainsIso A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_dOne_eq,
    shortComplexH2_f]

end isoTwoCocycles
end CocyclesIso

section Cohomology

variable [DecidableEq G]

section H0

/-- Shorthand for the 0th group cohomology of a `k`-linear `G`-representation `A`, `H⁰(G, A)`,
defined as the 0th cohomology of the complex of inhomogeneous cochains of `A`. -/
abbrev H0 := groupCohomology A 0

/-- The 0th group cohomology of `A`, defined as the 0th cohomology of the complex of inhomogeneous
cochains, is isomorphic to the invariants of the representation on `A`. -/
def H0Iso : H0 A ≅ ModuleCat.of k A.ρ.invariants :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ zeroCocyclesIso A

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH0 := H0Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H0Iso_hom  :
    π A 0 ≫ (H0Iso A).hom = (zeroCocyclesIso A).hom := by
  simp [← cancel_mono (shortComplexH0 A).f, H0Iso]

@[deprecated (since := "2025-06-12")]
alias groupCohomologyπ_comp_isoH0_hom := π_comp_H0Iso_hom

@[elab_as_elim]
theorem H0_induction_on {C : H0 A → Prop} (x : H0 A)
    (h : ∀ x : A.ρ.invariants, C ((H0Iso A).inv x)) : C x := by
  simpa using h ((H0Iso A).hom x)

section IsTrivial

variable [A.IsTrivial]

/-- When the representation on `A` is trivial, then `H⁰(G, A)` is all of `A.` -/
def H0IsoOfIsTrivial :
    H0 A ≅ A.V := H0Iso A ≪≫ (LinearEquiv.ofTop _ (invariants_eq_top A.ρ)).toModuleIso

@[deprecated (since := "2025-05-09")]
noncomputable alias H0LequivOfIsTrivial := H0IsoOfIsTrivial

@[simp, elementwise]
theorem H0IsoOfIsTrivial_hom :
    (H0IsoOfIsTrivial A).hom = (H0Iso A).hom ≫ (shortComplexH0 A).f := rfl

@[deprecated (since := "2025-06-11")]
alias H0LequivOfIsTrivial_eq_subtype := H0IsoOfIsTrivial_hom

@[deprecated (since := "2025-05-09")]
alias H0LequivOfIsTrivial_apply := H0IsoOfIsTrivial_hom_apply

@[reassoc, elementwise]
theorem π_comp_H0IsoOfIsTrivial_hom :
    π A 0 ≫ (H0IsoOfIsTrivial A).hom = iCocycles A 0 ≫ (zeroCochainsIso A).hom := by
  simp

variable {A} in
@[simp]
theorem H0IsoOfIsTrivial_inv_apply (x : A) :
    (H0IsoOfIsTrivial A).inv x = (H0Iso A).inv ⟨x, by simp⟩ := rfl

@[deprecated (since := "2025-05-09")]
alias H0LequivOfIsTrivial_symm_apply := H0IsoOfIsTrivial_inv_apply

end IsTrivial
end H0
section H1

/-- Shorthand for the 1st group cohomology of a `k`-linear `G`-representation `A`, `H¹(G, A)`,
defined as the 1st cohomology of the complex of inhomogeneous cochains of `A`. -/
abbrev H1 := groupCohomology A 1

/-- The quotient map from the 1-cocycles of `A`, as a submodule of `G → A`, to `H¹(G, A)`. -/
def H1π : ModuleCat.of k (oneCocycles A) ⟶ H1 A :=
  (isoOneCocycles A).inv ≫ π A 1

instance : Epi (H1π A) := by unfold H1π; infer_instance

variable {A}

lemma H1π_eq_zero_iff (x : oneCocycles A) : H1π A x = 0 ↔ ⇑x ∈ oneCoboundaries A := by
  have h := leftHomologyπ_naturality'_assoc (shortComplexH1Iso A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoOneCocycles, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <|  _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, oneCoboundaries, shortComplexH1, oneCocycles]

lemma H1π_eq_iff (x y : oneCocycles A) :
    H1π A x = H1π A y ↔ ⇑x - ⇑y ∈ oneCoboundaries A := by
  rw [← sub_eq_zero, ← map_sub, H1π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H1_induction_on {C : H1 A → Prop} (x : H1 A) (h : ∀ x : oneCocycles A, C (H1π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H1π] using h ((isoOneCocycles A).hom y)

variable (A)

/-- The 1st group cohomology of `A`, defined as the 1st cohomology of the complex of inhomogeneous
cochains, is isomorphic to `oneCocycles A ⧸ oneCoboundaries A`, which is a simpler type. -/
def H1Iso : H1 A ≅ (shortComplexH1 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (shortComplexH1Iso A) _ _)

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH1 := H1Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H1Iso_hom  :
    π A 1 ≫ (H1Iso A).hom = (isoOneCocycles A).hom ≫
      (shortComplexH1 A).moduleCatLeftHomologyData.π := by
  simp [H1Iso, isoOneCocycles, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[deprecated (since := "2025-06-12")]
alias groupCohomologyπ_comp_isoH1_hom := π_comp_H1Iso_hom

section IsTrivial

variable [A.IsTrivial]

/-- When `A : Rep k G` is a trivial representation of `G`, `H¹(G, A)` is isomorphic to the
group homs `G → A`. -/
def H1IsoOfIsTrivial :
    H1 A ≅ ModuleCat.of k (Additive G →+ A) :=
  (HomologicalComplex.isoHomologyπ _ 0 1 (CochainComplex.prev_nat_succ 0) <| by
    ext; simp [inhomogeneousCochains.d_def, inhomogeneousCochains.d,
      Unique.eq_default (α := Fin 0 → G), Pi.zero_apply (M := fun _ => A)]).symm ≪≫
  isoOneCocycles A ≪≫ oneCocyclesIsoOfIsTrivial A

@[deprecated (since := "2025-05-09")]
noncomputable alias H1LequivOfIsTrivial := H1IsoOfIsTrivial

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H1π_comp_H1IsoOfIsTrivial_hom:
    H1π A ≫ (H1IsoOfIsTrivial A).hom = (oneCocyclesIsoOfIsTrivial A).hom := by
  simp [H1IsoOfIsTrivial, H1π]

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_comp_H1π := H1π_comp_H1IsoOfIsTrivial_hom

variable {A}

theorem H1IsoOfIsTrivial_H1π_apply_apply
    (f : oneCocycles A) (x : Additive G) :
    (H1IsoOfIsTrivial A).hom (H1π A f) x = f x.toMul := by simp

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_comp_H1_π_apply_apply := H1IsoOfIsTrivial_H1π_apply_apply

theorem H1IsoOfIsTrivial_inv_apply (f : Additive G →+ A) :
    (H1IsoOfIsTrivial A).inv f = H1π A ((oneCocyclesIsoOfIsTrivial A).inv f) := rfl

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_symm_apply := H1IsoOfIsTrivial_inv_apply

end IsTrivial
end H1
section H2

/-- Shorthand for the 2nd group cohomology of a `k`-linear `G`-representation `A`, `H²(G, A)`,
defined as the 2nd cohomology of the complex of inhomogeneous cochains of `A`. -/
abbrev H2 := groupCohomology A 2

/-- The quotient map from the 2-cocycles of `A`, as a submodule of `G × G → A`, to `H²(G, A)`. -/
def H2π : ModuleCat.of k (twoCocycles A) ⟶ H2 A :=
  (isoTwoCocycles A).inv ≫ π A 2

instance : Epi (H2π A) := by unfold H2π; infer_instance

variable {A}

lemma H2π_eq_zero_iff (x : twoCocycles A) : H2π A x = 0 ↔ ⇑x ∈ twoCoboundaries A := by
  have h := leftHomologyπ_naturality'_assoc (shortComplexH2Iso A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoTwoCocycles, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <|  _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, twoCoboundaries, shortComplexH2, twoCocycles]

lemma H2π_eq_iff (x y : twoCocycles A) :
    H2π A x = H2π A y ↔ ⇑x - ⇑y ∈ twoCoboundaries A := by
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H2_induction_on {C : H2 A → Prop} (x : H2 A) (h : ∀ x : twoCocycles A, C (H2π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H2π] using h ((isoTwoCocycles A).hom y)

variable (A)

/-- The 2nd group cohomology of `A`, defined as the 2nd cohomology of the complex of inhomogeneous
cochains, is isomorphic to `twoCocycles A ⧸ twoCoboundaries A`, which is a simpler type. -/
def H2Iso : H2 A ≅ (shortComplexH2 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (shortComplexH2Iso A) _ _)

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH2 := H2Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H2Iso_hom  :
    π A 2 ≫ (H2Iso A).hom = (isoTwoCocycles A).hom ≫
      (shortComplexH2 A).moduleCatLeftHomologyData.π := by
  simp [H2Iso, isoTwoCocycles, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[deprecated (since := "2025-06-12")]
alias groupCohomologyπ_comp_isoH2_hom := π_comp_H2Iso_hom

end H2
end Cohomology
end groupCohomology
