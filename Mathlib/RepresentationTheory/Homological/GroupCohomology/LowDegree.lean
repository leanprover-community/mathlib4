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
element of the `cocycles₁` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries. The
multiplicative case, starting with the section `IsMulCocycle`, just mirrors the additive case;
unfortunately `@[to_additive]` can't deal with scalar actions.

The file also contains an identification between the definitions in
`RepresentationTheory/Homological/GroupCohomology/Basic.lean`, `groupCohomology.cocycles A n`, and
the `cocyclesₙ` in this file, for `n = 0, 1, 2`.

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

/-- The 0th object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `A` as a `k`-module. -/
def cochainsIso₀ : (inhomogeneousCochains A).X 0 ≅ A.V :=
  (LinearEquiv.funUnique (Fin 0 → G) k A).toModuleIso

@[deprecated (since := "2025-06-25")] noncomputable alias zeroCochainsIso := cochainsIso₀
@[deprecated (since := "2025-05-09")] noncomputable alias zeroCochainsLequiv := zeroCochainsIso

/-- The 1st object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G, A)` as a `k`-module. -/
def cochainsIso₁ : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G → A) :=
  (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

@[deprecated (since := "2025-06-25")] noncomputable alias oneCochainsIso := cochainsIso₁
@[deprecated (since := "2025-05-09")] noncomputable alias oneCochainsLequiv := oneCochainsIso

/-- The 2nd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G², A)` as a `k`-module. -/
def cochainsIso₂ : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

@[deprecated (since := "2025-06-25")] noncomputable alias twoCochainsIso := cochainsIso₂
@[deprecated (since := "2025-05-09")] noncomputable alias twoCochainsLequiv := twoCochainsIso

/-- The 3rd object in the complex of inhomogeneous cochains of `A : Rep k G` is isomorphic
to `Fun(G³, A)` as a `k`-module. -/
def cochainsIso₃ : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

@[deprecated (since := "2025-06-25")] noncomputable alias threeCochainsIso := cochainsIso₃
@[deprecated (since := "2025-05-09")] noncomputable alias threeCochainsLequiv := threeCochainsIso

end Cochains

section Differentials

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
@[simps!]
def d₀₁ : A.V ⟶ ModuleCat.of k (G → A) :=
  ModuleCat.ofHom
  { toFun m g := A.ρ g m - m
    map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub] }

@[deprecated (since := "2025-06-25")] noncomputable alias dZero := d₀₁

theorem d₀₁_ker_eq_invariants : LinearMap.ker (d₀₁ A).hom = invariants A.ρ := by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl

@[deprecated (since := "2025-06-25")]
noncomputable alias dZero_ker_eq_invariants := d₀₁_ker_eq_invariants

@[simp] theorem d₀₁_eq_zero [A.IsTrivial] : d₀₁ A = 0 := by
  ext
  rw [d₀₁_hom_apply, isTrivial_apply, sub_self]
  rfl

@[deprecated (since := "2025-06-25")] alias dZero_eq_zero := d₀₁_eq_zero

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma subtype_comp_d₀₁ : ModuleCat.ofHom (A.ρ.invariants.subtype) ≫ d₀₁ A = 0 := by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx

@[deprecated (since := "2025-06-25")] alias subtype_comp_dZero := subtype_comp_d₀₁

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
@[simps!]
def d₁₂ : ModuleCat.of k (G → A) ⟶ ModuleCat.of k (G × G → A) :=
  ModuleCat.ofHom
  { toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
    map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub] }

@[deprecated (since := "2025-06-25")] noncomputable alias dOne := d₁₂

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
@[simps!]
def d₂₃ : ModuleCat.of k (G × G → A) ⟶ ModuleCat.of k (G × G × G → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
    map_add' x y :=
      funext fun g => by
        dsimp
        rw [map_add, add_sub_add_comm (A.ρ _ _), add_sub_assoc, add_sub_add_comm, add_add_add_comm,
          add_sub_assoc, add_sub_assoc]
    map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub] }

@[deprecated (since := "2025-06-25")] noncomputable alias dTwo := d₂₃

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d₀₁` gives a simpler expression for the 0th differential: that is, the following
square commutes:
```
  C⁰(G, A) --d 0 1--> C¹(G, A)
  |                     |
  |                     |
  |                     |
  v                     v
  A ------d₀₁-----> Fun(G, A)
```
where the vertical arrows are `cochainsIso₀` and `cochainsIso₁` respectively.
-/
theorem comp_d₀₁_eq :
    (cochainsIso₀ A).hom ≫ d₀₁ A =
      (inhomogeneousCochains A).d 0 1 ≫ (cochainsIso₁ A).hom := by
  ext x y
  change A.ρ y (x default) - x default = _ + ({0} : Finset _).sum _
  simp_rw [Fin.val_eq_zero, zero_add, pow_one, neg_smul, one_smul,
    Finset.sum_singleton, sub_eq_add_neg]
  rcongr i <;> exact Fin.elim0 i

@[deprecated (since := "2025-06-25")] noncomputable alias comp_dZero_eq := comp_d₀₁_eq

@[deprecated (since := "2025-05-09")] noncomputable alias dZero_comp_eq := comp_dZero_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₀₁_comp_inv :
    (cochainsIso₀ A).inv ≫ (inhomogeneousCochains A).d 0 1 =
      d₀₁ A ≫ (cochainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₀₁_eq A⟩).w

@[deprecated (since := "2025-06-25")] alias eq_dZero_comp_inv := eq_d₀₁_comp_inv

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d₁₂` gives a simpler expression for the 1st differential: that is, the following
square commutes:
```
  C¹(G, A) ---d 1 2---> C²(G, A)
    |                      |
    |                      |
    |                      |
    v                      v
  Fun(G, A) --d₁₂--> Fun(G × G, A)
```
where the vertical arrows are `cochainsIso₁` and `cochainsIso₂` respectively.
-/
theorem comp_d₁₂_eq :
    (cochainsIso₁ A).hom ≫ d₁₂ A =
      (inhomogeneousCochains A).d 1 2 ≫ (cochainsIso₂ A).hom := by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ =  _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

@[deprecated (since := "2025-06-25")] alias comp_dOne_eq := comp_d₁₂_eq

@[deprecated (since := "2025-05-09")] alias dOne_comp_eq := comp_dOne_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₁₂_comp_inv :
    (cochainsIso₁ A).inv ≫ (inhomogeneousCochains A).d 1 2 =
      d₁₂ A ≫ (cochainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₁₂_eq A⟩).w

@[deprecated (since := "2025-06-25")] alias eq_dOne_comp_inv := eq_d₁₂_comp_inv

/-- Let `C(G, A)` denote the complex of inhomogeneous cochains of `A : Rep k G`. This lemma
says `d₂₃` gives a simpler expression for the 2nd differential: that is, the following
square commutes:
```
      C²(G, A) ----d 2 3----> C³(G, A)
        |                         |
        |                         |
        |                         |
        v                         v
  Fun(G × G, A) --d₂₃--> Fun(G × G × G, A)
```
where the vertical arrows are `cochainsIso₂` and `cochainsIso₃` respectively.
-/
theorem comp_d₂₃_eq :
    (cochainsIso₂ A).hom ≫ d₂₃ A =
      (inhomogeneousCochains A).d 2 3 ≫ (cochainsIso₃ A).hom := by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

@[deprecated (since := "2025-06-25")] alias comp_dTwo_eq := comp_d₂₃_eq

@[deprecated (since := "2025-05-09")] alias dTwo_comp_eq := comp_dTwo_eq

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem eq_d₂₃_comp_inv :
    (cochainsIso₂ A).inv ≫ (inhomogeneousCochains A).d 2 3 =
      d₂₃ A ≫ (cochainsIso₃ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₂₃_eq A⟩).w

@[deprecated (since := "2025-06-25")] alias eq_dTwo_comp_inv := eq_d₂₃_comp_inv

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₀₁_comp_d₁₂ : d₀₁ A ≫ d₁₂ A = 0 := by
  ext
  simp [Pi.zero_apply (M := fun _ => A)]

@[deprecated (since := "2025-06-25")] alias dZero_comp_dOne := d₀₁_comp_d₁₂

@[deprecated (since := "2025-05-14")] alias dOne_comp_dZero := dZero_comp_dOne

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₁₂_comp_d₂₃ : d₁₂ A ≫ d₂₃ A = 0 := by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

@[deprecated (since := "2025-06-25")] alias dOne_comp_dTwo := d₁₂_comp_d₂₃

@[deprecated (since := "2025-05-14")] alias dTwo_comp_dOne := dOne_comp_dTwo

open ShortComplex

/-- The (exact) short complex `A.ρ.invariants ⟶ A ⟶ (G → A)`. -/
@[simps! -isSimp f g]
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (subtype_comp_d₀₁ A)

/-- The short complex `A --d₀₁--> Fun(G, A) --d₁₂--> Fun(G × G, A)`. -/
@[simps! -isSimp f g]
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk (d₀₁ A) (d₁₂ A) (d₀₁_comp_d₁₂ A)

/-- The short complex `Fun(G, A) --d₁₂--> Fun(G × G, A) --d₂₃--> Fun(G × G × G, A)`. -/
@[simps! -isSimp f g]
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk (d₁₂ A) (d₂₃ A) (d₁₂_comp_d₂₃ A)

end Differentials

section Cocycles

/-- The 1-cocycles `Z¹(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def cocycles₁ : Submodule k (G → A) := LinearMap.ker (d₁₂ A).hom

@[deprecated (since := "2025-06-25")] noncomputable alias oneCocycles := cocycles₁

/-- The 2-cocycles `Z²(G, A)` of `A : Rep k G`, defined as the kernel of the map
`Fun(G × G, A) → Fun(G × G × G, A)` sending
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
def cocycles₂ : Submodule k (G × G → A) := LinearMap.ker (d₂₃ A).hom

@[deprecated (since := "2025-06-25")] noncomputable alias twoCocycles := cocycles₂

variable {A}

instance : FunLike (cocycles₁ A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cocycles₁.coe_mk (f : G → A) (hf) : ((⟨f, hf⟩ : cocycles₁ A) : G → A) = f := rfl

@[deprecated (since := "2025-06-25")] alias oneCocycles.coe_mk := cocycles₁.coe_mk

@[simp]
theorem cocycles₁.val_eq_coe (f : cocycles₁ A) : f.1 = f := rfl

@[deprecated (since := "2025-06-25")] alias oneCocycles.val_eq_coe := cocycles₁.val_eq_coe

@[ext]
theorem cocycles₁_ext {f₁ f₂ : cocycles₁ A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

@[deprecated (since := "2025-06-25")] alias oneCocycles_ext := cocycles₁_ext

theorem mem_cocycles₁_def (f : G → A) :
    f ∈ cocycles₁ A ↔ ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₁₂_hom_apply, Prod.forall]
    rfl

@[deprecated (since := "2025-06-25")] alias mem_oneCocycles_def := mem_cocycles₁_def

theorem mem_cocycles₁_iff (f : G → A) :
    f ∈ cocycles₁ A ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [mem_cocycles₁_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

@[deprecated (since := "2025-06-25")] alias mem_oneCocycles_iff := mem_cocycles₁_iff

@[simp] theorem cocycles₁_map_one (f : cocycles₁ A) : f 1 = 0 := by
  have := (mem_cocycles₁_def f).1 f.2 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this

@[deprecated (since := "2025-06-25")] alias oneCocycles_map_one := cocycles₁_map_one

@[simp] theorem cocycles₁_map_inv (f : cocycles₁ A) (g : G) :
    A.ρ g (f g⁻¹) = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← cocycles₁_map_one f, ← mul_inv_cancel g,
    (mem_cocycles₁_iff f).1 f.2 g g⁻¹]

@[deprecated (since := "2025-06-25")] alias oneCocycles_map_inv := cocycles₁_map_inv

theorem d₀₁_apply_mem_cocycles₁ (x : A) :
    d₀₁ A x ∈ cocycles₁ A :=
  d₀₁_comp_d₁₂_apply _ _

@[deprecated (since := "2025-06-25")] alias dZero_apply_mem_oneCocycles := d₀₁_apply_mem_cocycles₁

@[simp]
theorem cocycles₁.d₁₂_apply (x : cocycles₁ A) :
    d₁₂ A x = 0 := x.2

@[deprecated (since := "2025-06-25")] alias oneCocycles.dOne_apply := cocycles₁.d₁₂_apply

theorem cocycles₁_map_mul_of_isTrivial [A.IsTrivial] (f : cocycles₁ A) (g h : G) :
    f (g * h) = f g + f h := by
  rw [(mem_cocycles₁_iff f).1 f.2, isTrivial_apply A.ρ g (f h), add_comm]

@[deprecated (since := "2025-06-25")]
alias oneCocycles_map_mul_of_isTrivial := cocycles₁_map_mul_of_isTrivial

theorem mem_cocycles₁_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    f ∘ Additive.ofMul ∈ cocycles₁ A :=
  (mem_cocycles₁_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      isTrivial_apply A.ρ g (f (Additive.ofMul h)), add_comm (f (Additive.ofMul g))]

@[deprecated (since := "2025-06-25")]
alias mem_oneCocycles_of_addMonoidHom := mem_cocycles₁_of_addMonoidHom

variable (A) in
/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps!]
def cocycles₁IsoOfIsTrivial [hA : A.IsTrivial] :
    ModuleCat.of k (cocycles₁ A) ≅ ModuleCat.of k (Additive G →+ A) :=
  LinearEquiv.toModuleIso
  { toFun f :=
      { toFun := f ∘ Additive.toMul
        map_zero' := cocycles₁_map_one f
        map_add' := cocycles₁_map_mul_of_isTrivial f }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun f :=
      { val := f
        property := mem_cocycles₁_of_addMonoidHom f } }

@[deprecated (since := "2025-06-25")]
noncomputable alias oneCocyclesIsoOfIsTrivial := cocycles₁IsoOfIsTrivial

@[deprecated (since := "2025-05-09")]
noncomputable alias oneCocyclesLequivOfIsTrivial := oneCocyclesIsoOfIsTrivial

instance : FunLike (cocycles₂ A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cocycles₂.coe_mk (f : G × G → A) (hf) : ((⟨f, hf⟩ : cocycles₂ A) : G × G → A) = f := rfl

@[deprecated (since := "2025-06-25")] alias twoCocycles.coe_mk := cocycles₂.coe_mk

@[simp]
theorem cocycles₂.val_eq_coe (f : cocycles₂ A) : f.1 = f := rfl

@[deprecated (since := "2025-06-25")] alias twoCocycles.val_eq_coe := cocycles₂.val_eq_coe

@[ext]
theorem cocycles₂_ext {f₁ f₂ : cocycles₂ A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

@[deprecated (since := "2025-06-25")] alias twoCocycles_ext := cocycles₂_ext

theorem mem_cocycles₂_def (f : G × G → A) :
    f ∈ cocycles₂ A ↔ ∀ g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₂₃_hom_apply, Prod.forall]
    rfl

@[deprecated (since := "2025-06-25")] alias mem_twoCocycles_def := mem_cocycles₂_def

theorem mem_cocycles₂_iff (f : G × G → A) :
    f ∈ cocycles₂ A ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_cocycles₂_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

@[deprecated (since := "2025-06-25")] alias mem_twoCocycles_iff := mem_cocycles₂_iff

theorem cocycles₂_map_one_fst (f : cocycles₂ A) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((mem_cocycles₂_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

@[deprecated (since := "2025-06-25")] alias twoCocycles_map_one_fst := cocycles₂_map_one_fst

theorem cocycles₂_map_one_snd (f : cocycles₂ A) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (mem_cocycles₂_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

@[deprecated (since := "2025-06-25")] alias twoCocycles_map_one_snd := cocycles₂_map_one_snd

lemma cocycles₂_ρ_map_inv_sub_map_inv (f : cocycles₂ A) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (mem_cocycles₂_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, cocycles₂_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

@[deprecated (since := "2025-06-25")]
alias twoCocycles_ρ_map_inv_sub_map_inv := cocycles₂_ρ_map_inv_sub_map_inv

theorem d₁₂_apply_mem_cocycles₂ (x : G → A) :
    d₁₂ A x ∈ cocycles₂ A :=
  d₁₂_comp_d₂₃_apply _ _

@[deprecated (since := "2025-06-25")] alias dOne_apply_mem_twoCocycles := d₁₂_apply_mem_cocycles₂

@[simp]
theorem cocycles₂.d₂₃_apply (x : cocycles₂ A) :
    d₂₃ A x = 0 := x.2

@[deprecated (since := "2025-06-25")] alias twoCocycles.dTwo_apply := cocycles₂.d₂₃_apply

end Cocycles

section Coboundaries

/-- The 1-coboundaries `B¹(G, A)` of `A : Rep k G`, defined as the image of the map
`A → Fun(G, A)` sending `(a, g) ↦ ρ_A(g)(a) - a.` -/
def coboundaries₁ : Submodule k (G → A) :=
  LinearMap.range (d₀₁ A).hom

@[deprecated (since := "2025-06-25")] noncomputable alias oneCoboundaries := coboundaries₁

/-- The 2-coboundaries `B²(G, A)` of `A : Rep k G`, defined as the image of the map
`Fun(G, A) → Fun(G × G, A)` sending `(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
def coboundaries₂ : Submodule k (G × G → A) :=
  LinearMap.range (d₁₂ A).hom

@[deprecated (since := "2025-06-25")] noncomputable alias twoCoboundaries := coboundaries₂

variable {A}

instance : FunLike (coboundaries₁ A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem coboundaries₁.coe_mk (f : G → A) (hf) :
    ((⟨f, hf⟩ : coboundaries₁ A) : G → A) = f := rfl

@[deprecated (since := "2025-06-25")] alias oneCoboundaries.coe_mk := coboundaries₁.coe_mk

@[simp]
theorem coboundaries₁.val_eq_coe (f : coboundaries₁ A) : f.1 = f := rfl

@[deprecated (since := "2025-06-25")] alias oneCoboundaries.val_eq_coe := coboundaries₁.val_eq_coe

@[ext]
theorem coboundaries₁_ext {f₁ f₂ : coboundaries₁ A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

@[deprecated (since := "2025-06-25")] alias oneCoboundaries_ext := coboundaries₁_ext

variable (A) in
lemma coboundaries₁_le_cocycles₁ : coboundaries₁ A ≤ cocycles₁ A := by
  rintro _ ⟨x, rfl⟩
  exact d₀₁_apply_mem_cocycles₁ x

@[deprecated (since := "2025-06-25")]
alias oneCoboundaries_le_oneCocycles := coboundaries₁_le_cocycles₁

variable (A) in
/-- Natural inclusion `B¹(G, A) →ₗ[k] Z¹(G, A)`. -/
abbrev coboundariesToCocycles₁ : coboundaries₁ A →ₗ[k] cocycles₁ A :=
  Submodule.inclusion (coboundaries₁_le_cocycles₁ A)

@[deprecated (since := "2025-06-25")]
noncomputable alias oneCoboundariesToOneCocycles := coboundariesToCocycles₁

@[simp]
lemma coboundariesToCocycles₁_apply (x : coboundaries₁ A) :
    coboundariesToCocycles₁ A x = x.1 := rfl

@[deprecated (since := "2025-06-25")]
alias oneCoboundariesToOneCocycles_apply := coboundariesToCocycles₁_apply

theorem coboundaries₁_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    coboundaries₁ A = ⊥ := by
  simp_rw [coboundaries₁, d₀₁_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

@[deprecated (since := "2025-06-25")]
alias oneCoboundaries_eq_bot_of_isTrivial := coboundaries₁_eq_bot_of_isTrivial

instance : FunLike (coboundaries₂ A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem coboundaries₂.coe_mk (f : G × G → A) (hf) :
    ((⟨f, hf⟩ : coboundaries₂ A) : G × G → A) = f := rfl

@[deprecated (since := "2025-06-25")] alias twoCoboundaries.coe_mk := coboundaries₂.coe_mk

@[simp]
theorem coboundaries₂.val_eq_coe (f : coboundaries₂ A) : f.1 = f := rfl

@[deprecated (since := "2025-06-25")] alias twoCoboundaries.val_eq_coe := coboundaries₂.val_eq_coe

@[ext]
theorem coboundaries₂_ext {f₁ f₂ : coboundaries₂ A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) :
    f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

@[deprecated (since := "2025-06-25")] alias twoCoboundaries_ext := coboundaries₂_ext

variable (A) in
lemma coboundaries₂_le_cocycles₂ : coboundaries₂ A ≤ cocycles₂ A := by
  rintro _ ⟨x, rfl⟩
  exact d₁₂_apply_mem_cocycles₂ x

@[deprecated (since := "2025-06-25")]
alias twoCoboundaries_le_twoCocycles := coboundaries₂_le_cocycles₂

variable (A) in
/-- Natural inclusion `B²(G, A) →ₗ[k] Z²(G, A)`. -/
abbrev coboundariesToCocycles₂ : coboundaries₂ A →ₗ[k] cocycles₂ A :=
  Submodule.inclusion (coboundaries₂_le_cocycles₂ A)

@[deprecated (since := "2025-06-25")]
noncomputable alias twoCoboundariesToTwoCocycles := coboundariesToCocycles₂

@[simp]
lemma coboundariesToCocycles₂_apply (x : coboundaries₂ A) :
    coboundariesToCocycles₂ A x = x.1 := rfl

@[deprecated (since := "2025-06-25")]
alias twoCoboundariesToTwoCocycles_apply := coboundariesToCocycles₂_apply

end Coboundaries

section IsCocycle

section

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-cocycle condition if
`f(gh) = g • f(h) + f(g)` for all `g, h : G`. -/
def IsCocycle₁ (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g

@[deprecated (since := "2025-06-25")] alias IsOneCocycle := IsCocycle₁

/-- A function `f : G × G → A` satisfies the 2-cocycle condition if
`f(gh, j) + f(g, h) = g • f(h, j) + f(g, hj)` for all `g, h : G`. -/
def IsCocycle₂ (f : G × G → A) : Prop :=
  ∀ g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

@[deprecated (since := "2025-06-25")] alias IsTwoCocycle := IsCocycle₂

end

section

variable {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]

theorem map_one_of_isCocycle₁ {f : G → A} (hf : IsCocycle₁ f) :
    f 1 = 0 := by
  simpa only [mul_one, one_smul, left_eq_add] using hf 1 1

@[deprecated (since := "2025-06-25")] alias map_one_of_isOneCocycle := map_one_of_isCocycle₁

theorem map_one_fst_of_isCocycle₂ {f : G × G → A} (hf : IsCocycle₂ f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

@[deprecated (since := "2025-06-25")] alias map_one_fst_of_isTwoCocycle := map_one_fst_of_isCocycle₂

theorem map_one_snd_of_isCocycle₂ {f : G × G → A} (hf : IsCocycle₂ f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, add_left_inj] using hf g 1 1

@[deprecated (since := "2025-06-25")] alias map_one_snd_of_isTwoCocycle := map_one_snd_of_isCocycle₂

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [MulAction G A]

@[scoped simp] theorem map_inv_of_isCocycle₁ {f : G → A} (hf : IsCocycle₁ f) (g : G) :
    g • f g⁻¹ = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← map_one_of_isCocycle₁ hf, ← mul_inv_cancel g, hf g g⁻¹]

@[deprecated (since := "2025-06-25")] alias map_inv_of_isOneCocycle := map_inv_of_isCocycle₁

theorem smul_map_inv_sub_map_inv_of_isCocycle₂ {f : G × G → A} (hf : IsCocycle₂ f) (g : G) :
    g • f (g⁻¹, g) - f (g, g⁻¹) = f (1, 1) - f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isCocycle₂ hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

@[deprecated (since := "2025-06-25")]
alias smul_map_inv_sub_map_inv_of_isTwoCocycle := smul_map_inv_sub_map_inv_of_isCocycle₂

end

end IsCocycle

section IsCoboundary

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/-- A function `f : G → A` satisfies the 1-coboundary condition if there's `x : A` such that
`g • x - x = f(g)` for all `g : G`. -/
def IsCoboundary₁ (f : G → A) : Prop := ∃ x : A, ∀ g : G, g • x - x = f g

@[deprecated (since := "2025-06-25")] alias IsOneCoboundary := IsCoboundary₁

/-- A function `f : G × G → A` satisfies the 2-coboundary condition if there's `x : G → A` such
that `g • x(h) - x(gh) + x(g) = f(g, h)` for all `g, h : G`. -/
def IsCoboundary₂ (f : G × G → A) : Prop :=
  ∃ x : G → A, ∀ g h : G, g • x h - x (g * h) + x g = f (g, h)

@[deprecated (since := "2025-06-25")] alias IsTwoCoboundary := IsCoboundary₂

end IsCoboundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-cocycle condition, produces a 1-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def cocyclesOfIsCocycle₁ {f : G → A} (hf : IsCocycle₁ f) :
    cocycles₁ (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

@[deprecated (since := "2025-06-25")] alias oneCocyclesOfIsOneCocycle := cocyclesOfIsCocycle₁

theorem isCocycle₁_of_mem_cocycles₁
    (f : G → A) (hf : f ∈ cocycles₁ (Rep.ofDistribMulAction k G A)) :
    IsCocycle₁ f :=
  fun _ _ => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

@[deprecated (since := "2025-07-02")]
alias isOneCocycle_of_mem_oneCocycles := isCocycle₁_of_mem_cocycles₁

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-coboundary condition, produces a 1-coboundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
def coboundariesOfIsCoboundary₁ {f : G → A} (hf : IsCoboundary₁ f) :
    coboundaries₁ (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose, funext hf.choose_spec⟩

@[deprecated (since := "2025-06-25")]
alias oneCoboundariesOfIsOneCoboundary := coboundariesOfIsCoboundary₁

theorem isCoboundary₁_of_mem_coboundaries₁
    (f : G → A) (hf : f ∈ coboundaries₁ (Rep.ofDistribMulAction k G A)) :
    IsCoboundary₁ f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ => rfl⟩

@[deprecated (since := "2025-07-02")]
alias isOneCoboundary_of_mem_oneCoboundaries := isCoboundary₁_of_mem_coboundaries₁

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-cocycle condition, produces a 2-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
def cocyclesOfIsCocycle₂ {f : G × G → A} (hf : IsCocycle₂ f) :
    cocycles₂ (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

@[deprecated (since := "2025-06-25")] alias twoCocyclesOfIsTwoCocycle := cocyclesOfIsCocycle₂

theorem isCocycle₂_of_mem_cocycles₂
    (f : G × G → A) (hf : f ∈ cocycles₂ (Rep.ofDistribMulAction k G A)) :
    IsCocycle₂ f := (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

@[deprecated (since := "2025-07-02")]
alias isTwoCocycle_of_mem_twoCocycles := isCocycle₂_of_mem_cocycles₂

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-coboundary condition, produces a 2-coboundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
def coboundariesOfIsCoboundary₂ {f : G × G → A} (hf : IsCoboundary₂ f) :
    coboundaries₂ (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose,funext fun g ↦ hf.choose_spec g.1 g.2⟩

@[deprecated (since := "2025-06-25")]
alias twoCoboundariesOfIsTwoCoboundary := coboundariesOfIsCoboundary₂

theorem isCoboundary₂_of_mem_coboundaries₂
    (f : G × G → A) (hf : f ∈ coboundaries₂ (Rep.ofDistribMulAction k G A)) :
    IsCoboundary₂ f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ _ => rfl⟩

@[deprecated (since := "2025-07-02")]
alias isTwoCoboundary_of_mem_twoCoboundaries := isCoboundary₂_of_mem_coboundaries₂

end ofDistribMulAction

/-! The next few sections, until the section `CocyclesIso`, are a multiplicative copy of the
previous few sections beginning with `IsCocycle`. Unfortunately `@[to_additive]` doesn't work with
scalar actions. -/

section IsMulCocycle

section

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-cocycle condition if
`f(gh) = g • f(h) * f(g)` for all `g, h : G`. -/
def IsMulCocycle₁ (f : G → M) : Prop := ∀ g h : G, f (g * h) = g • f h * f g

@[deprecated (since := "2025-06-25")] alias IsMulOneCocycle := IsMulCocycle₁

/-- A function `f : G × G → M` satisfies the multiplicative 2-cocycle condition if
`f(gh, j) * f(g, h) = g • f(h, j) * f(g, hj)` for all `g, h : G`. -/
def IsMulCocycle₂ (f : G × G → M) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

@[deprecated (since := "2025-06-25")] alias IsMulTwoCocycle := IsMulCocycle₂

end

section

variable {G M : Type*} [Monoid G] [CommGroup M] [MulAction G M]

theorem map_one_of_isMulCocycle₁ {f : G → M} (hf : IsMulCocycle₁ f) :
    f 1 = 1 := by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

@[deprecated (since := "2025-06-25")] alias map_one_of_isMulOneCocycle := map_one_of_isMulCocycle₁

theorem map_one_fst_of_isMulCocycle₂ {f : G × G → M} (hf : IsMulCocycle₂ f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

@[deprecated (since := "2025-06-25")]
alias map_one_fst_of_isMulTwoCocycle := map_one_fst_of_isMulCocycle₂

theorem map_one_snd_of_isMulCocycle₂ {f : G × G → M} (hf : IsMulCocycle₂ f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

@[deprecated (since := "2025-06-25")]
alias map_one_snd_of_isMulTwoCocycle := map_one_snd_of_isMulCocycle₂

end

section

variable {G M : Type*} [Group G] [CommGroup M] [MulAction G M]

@[scoped simp] theorem map_inv_of_isMulCocycle₁ {f : G → M} (hf : IsMulCocycle₁ f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← map_one_of_isMulCocycle₁ hf, ← mul_inv_cancel g, hf g g⁻¹]

@[deprecated (since := "2025-06-25")] alias map_inv_of_isMulOneCocycle := map_inv_of_isMulCocycle₁

theorem smul_map_inv_div_map_inv_of_isMulCocycle₂
    {f : G × G → M} (hf : IsMulCocycle₂ f) (g : G) :
    g • f (g⁻¹, g) / f (g, g⁻¹) = f (1, 1) / f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulCocycle₂ hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

@[deprecated (since := "2025-07-02")]
alias smul_map_inv_div_map_inv_of_isMulTwoCocycle := smul_map_inv_div_map_inv_of_isMulCocycle₂

end

end IsMulCocycle

section IsMulCoboundary

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/-- A function `f : G → M` satisfies the multiplicative 1-coboundary condition if there's `x : M`
such that `g • x / x = f(g)` for all `g : G`. -/
def IsMulCoboundary₁ (f : G → M) : Prop := ∃ x : M, ∀ g : G, g • x / x = f g

@[deprecated (since := "2025-06-25")] alias IsMulOneCoboundary := IsMulCoboundary₁

/-- A function `f : G × G → M` satisfies the 2-coboundary condition if there's `x : G → M` such
that `g • x(h) / x(gh) * x(g) = f(g, h)` for all `g, h : G`. -/
def IsMulCoboundary₂ (f : G × G → M) : Prop :=
  ∃ x : G → M, ∀ g h : G, g • x h / x (g * h) * x g = f (g, h)

@[deprecated (since := "2025-06-25")] alias IsMulTwoCoboundary := IsMulCoboundary₂

end IsMulCoboundary

section ofMulDistribMulAction

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-cocycle condition, produces a 1-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def cocyclesOfIsMulCocycle₁ {f : G → M} (hf : IsMulCocycle₁ f) :
    cocycles₁ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

@[deprecated (since := "2025-06-25")] alias oneCocyclesOfIsMulOneCocycle := cocyclesOfIsMulCocycle₁

theorem isMulCocycle₁_of_mem_cocycles₁
    (f : G → M) (hf : f ∈ cocycles₁ (Rep.ofMulDistribMulAction G M)) :
    IsMulCocycle₁ (Additive.toMul ∘ f) :=
  (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

@[deprecated (since := "2025-07-02")]
alias isMulOneCocycle_of_mem_oneCocycles := isMulCocycle₁_of_mem_cocycles₁

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-coboundary condition, produces a
1-coboundary for the representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def coboundariesOfIsMulCoboundary₁ {f : G → M} (hf : IsMulCoboundary₁ f) :
    coboundaries₁ (Rep.ofMulDistribMulAction G M) :=
  ⟨f, hf.choose, funext hf.choose_spec⟩

@[deprecated (since := "2025-06-25")]
alias oneCoboundariesOfIsMulOneCoboundary := coboundariesOfIsMulCoboundary₁

theorem isMulCoboundary₁_of_mem_coboundaries₁
    (f : G → M) (hf : f ∈ coboundaries₁ (Rep.ofMulDistribMulAction G M)) :
    IsMulCoboundary₁ (M := M) (Additive.ofMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ =>  rfl⟩

@[deprecated (since := "2025-07-02")]
alias isMulOneCoboundary_of_mem_oneCoboundaries := isMulCoboundary₁_of_mem_coboundaries₁

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-cocycle condition, produces a 2-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
def cocyclesOfIsMulCocycle₂ {f : G × G → M} (hf : IsMulCocycle₂ f) :
    cocycles₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

@[deprecated (since := "2025-06-25")] alias twoCocyclesOfIsMulTwoCocycle := cocyclesOfIsMulCocycle₂

theorem isMulCocycle₂_of_mem_cocycles₂
    (f : G × G → M) (hf : f ∈ cocycles₂ (Rep.ofMulDistribMulAction G M)) :
    IsMulCocycle₂ (Additive.toMul ∘ f) :=
  (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

@[deprecated (since := "2025-07-02")]
alias isMulTwoCocycle_of_mem_twoCocycles := isMulCocycle₂_of_mem_cocycles₂

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-coboundary condition, produces a
2-coboundary for the representation on `M` induced by the `MulDistribMulAction`. -/
def coboundariesOfIsMulCoboundary₂ {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    coboundaries₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨f, hf.choose, funext fun g ↦ hf.choose_spec g.1 g.2⟩

@[deprecated (since := "2025-06-25")]
alias twoCoboundariesOfIsMulTwoCoboundary := coboundariesOfIsMulCoboundary₂

theorem isMulCoboundary₂_of_mem_coboundaries₂
    (f : G × G → M) (hf : f ∈ coboundaries₂ (Rep.ofMulDistribMulAction G M)) :
    IsMulCoboundary₂ (M := M) (Additive.toMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ _ => rfl⟩

@[deprecated (since := "2025-07-02")]
alias isMulTwoCoboundary_of_mem_twoCoboundaries := isMulCoboundary₂_of_mem_coboundaries₂

end ofMulDistribMulAction

open ShortComplex

section CocyclesIso

section cocyclesIso₀

instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : d₀₁ _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

/-- The arrow `A --d₀₁--> Fun(G, A)` is isomorphic to the differential
`(inhomogeneousCochains A).d 0 1` of the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dArrowIso₀₁ :
    Arrow.mk ((inhomogeneousCochains A).d 0 1) ≅ Arrow.mk (d₀₁ A) :=
  Arrow.isoMk (cochainsIso₀ A) (cochainsIso₁ A) (comp_d₀₁_eq A)

@[deprecated (since := "2025-06-25")] noncomputable alias dZeroArrowIso := dArrowIso₀₁

/-- The 0-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`A.ρ.invariants`, which is a simpler type. -/
def cocyclesIso₀ : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dArrowIso₀₁ A)

@[deprecated (since := "2025-07-02")] noncomputable alias zeroCocyclesIso := cocyclesIso₀
@[deprecated (since := "2025-06-12")]
noncomputable alias isoZeroCocycles := zeroCocyclesIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesIso₀_hom_comp_f :
    (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f = iCocycles A 0 ≫ (cochainsIso₀ A).hom := by
  dsimp [cocyclesIso₀]
  apply KernelFork.mapOfIsLimit_ι

@[deprecated (since := "2025-07-02")]
noncomputable alias zeroCocyclesIso_hom_comp_f := cocyclesIso₀_hom_comp_f
@[deprecated (since := "2025-06-12")]
alias isoZeroCocycles_hom_comp_subtype := zeroCocyclesIso_hom_comp_f

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesIso₀_inv_comp_iCocycles :
    (cocyclesIso₀ A).inv ≫ iCocycles A 0 =
      (shortComplexH0 A).f ≫ (cochainsIso₀ A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, cocyclesIso₀_hom_comp_f]

@[deprecated (since := "2025-07-02")]
noncomputable alias zeroCocyclesIso_inv_comp_iCocycles := cocyclesIso₀_inv_comp_iCocycles
@[deprecated (since := "2025-06-12")]
alias isoZeroCocycles_inv_comp_iCocycles := zeroCocyclesIso_inv_comp_iCocycles

variable {A} in
lemma cocyclesMk₀_eq (x : A.ρ.invariants) :
    cocyclesMk ((cochainsIso₀ A).inv x.1) (by ext g; simp [cochainsIso₀, x.2 (g 0),
      inhomogeneousCochains.d, Pi.zero_apply (M := fun _ => A)]) = (cocyclesIso₀ A).inv x :=
  (ModuleCat.mono_iff_injective <| iCocycles A 0).1 inferInstance <| by
    rw [iCocycles_mk]
    exact (cocyclesIso₀_inv_comp_iCocycles_apply A x).symm

@[deprecated (since := "2025-07-02")] alias cocyclesMk_0_eq := cocyclesMk₀_eq

end cocyclesIso₀

section isoCocycles₁

/-- The short complex `A --d₀₁--> Fun(G, A) --d₁₂--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def isoShortComplexH1 : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A :=
  (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₀ A) (cochainsIso₁ A) (cochainsIso₂ A)
      (comp_d₀₁_eq A) (comp_d₁₂_eq A)

@[deprecated (since := "2025-07-11")] noncomputable alias shortComplexH1Iso := isoShortComplexH1

/-- The 1-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`cocycles₁ A`, which is a simpler type. -/
def isoCocycles₁ : cocycles A 1 ≅ ModuleCat.of k (cocycles₁ A) :=
  cyclesMapIso' (isoShortComplexH1 A) _ (shortComplexH1 A).moduleCatLeftHomologyData

@[deprecated (since := "2025-06-25")] noncomputable alias isoOneCocycles := isoCocycles₁

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCocycles₁_hom_comp_i :
    (isoCocycles₁ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.i =
      iCocycles A 1 ≫ (cochainsIso₁ A).hom := by
  simp [isoCocycles₁, iCocycles, HomologicalComplex.iCycles, iCycles]

@[deprecated (since := "2025-06-25")] alias isoOneCocycles_hom_comp_i := isoCocycles₁_hom_comp_i

@[deprecated (since := "2025-05-09")]
alias isoOneCocycles_hom_comp_subtype := isoOneCocycles_hom_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCocycles₁_inv_comp_iCocycles :
    (isoCocycles₁ A).inv ≫ iCocycles A 1 =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₁_hom_comp_i A⟩).w

@[deprecated (since := "2025-06-25")]
alias isoOneCocycles_inv_comp_iCocycles := isoCocycles₁_inv_comp_iCocycles

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCocycles_comp_isoCocycles₁_hom :
    toCocycles A 0 1 ≫ (isoCocycles₁ A).hom =
      (cochainsIso₀ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₀₁_eq,
    shortComplexH1_f]

@[deprecated (since := "2025-06-25")]
alias toCocycles_comp_isoOneCocycles_hom := toCocycles_comp_isoCocycles₁_hom

lemma cocyclesMk₁_eq (x : cocycles₁ A) :
    cocyclesMk ((cochainsIso₁ A).inv x) (by
      simp [← inhomogeneousCochains.d_def, cocycles₁.d₁₂_apply x]) =
      (isoCocycles₁ A).inv x := by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 1) using
    (AddCommGrpCat.mono_iff_injective _).1 <| (forget₂ _ _).map_mono _
  simpa only [HomologicalComplex.i_cyclesMk] using
    (isoCocycles₁_inv_comp_iCocycles_apply _ x).symm

@[deprecated (since := "2025-07-02")] alias cocyclesMk_1_eq := cocyclesMk₁_eq

end isoCocycles₁

section isoCocycles₂

/-- The short complex `Fun(G, A) --d₁₂--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
def isoShortComplexH2 :
    (inhomogeneousCochains A).sc 2 ≅ shortComplexH2 A :=
  (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₁ A) (cochainsIso₂ A) (cochainsIso₃ A)
      (comp_d₁₂_eq A) (comp_d₂₃_eq A)

@[deprecated (since := "2025-07-11")] noncomputable alias shortComplexH2Iso := isoShortComplexH2

/-- The 2-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`cocycles₂ A`, which is a simpler type. -/
def isoCocycles₂ : cocycles A 2 ≅ ModuleCat.of k (cocycles₂ A) :=
  cyclesMapIso' (isoShortComplexH2 A) _ (shortComplexH2 A).moduleCatLeftHomologyData

@[deprecated (since := "2025-06-25")] noncomputable alias isoTwoCocycles := isoCocycles₂

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCocycles₂_hom_comp_i :
    (isoCocycles₂ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.i =
      iCocycles A 2 ≫ (cochainsIso₂ A).hom := by
  simp [isoCocycles₂, iCocycles, HomologicalComplex.iCycles, iCycles]

@[deprecated (since := "2025-06-25")] alias isoTwoCocycles_hom_comp_i := isoCocycles₂_hom_comp_i

@[deprecated (since := "2025-05-09")]
alias isoTwoCocycles_hom_comp_subtype := isoTwoCocycles_hom_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma isoCocycles₂_inv_comp_iCocycles :
    (isoCocycles₂ A).inv ≫ iCocycles A 2 =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₂_hom_comp_i A⟩).w

@[deprecated (since := "2025-06-25")]
alias isoTwoCocycles_inv_comp_iCocycles := isoCocycles₂_inv_comp_iCocycles

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toCocycles_comp_isoCocycles₂_hom :
    toCocycles A 1 2 ≫ (isoCocycles₂ A).hom =
      (cochainsIso₁ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₁₂_eq,
    shortComplexH2_f]

@[deprecated (since := "2025-06-25")]
alias toCocycles_comp_isoTwoCocycles_hom := toCocycles_comp_isoCocycles₂_hom

lemma cocyclesMk₂_eq (x : cocycles₂ A) :
    cocyclesMk ((cochainsIso₂ A).inv x) (by
      simp [← inhomogeneousCochains.d_def, cocycles₂.d₂₃_apply x]) =
      (isoCocycles₂ A).inv x := by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 2) using
    (AddCommGrpCat.mono_iff_injective _).1 <| (forget₂ _ _).map_mono _
  simpa only [HomologicalComplex.i_cyclesMk] using
    (isoCocycles₂_inv_comp_iCocycles_apply _ x).symm

@[deprecated (since := "2025-07-02")] alias cocyclesMk_2_eq := cocyclesMk₂_eq

end isoCocycles₂
end CocyclesIso

section Cohomology

section H0

/-- Shorthand for the 0th group cohomology of a `k`-linear `G`-representation `A`, `H⁰(G, A)`,
defined as the 0th cohomology of the complex of inhomogeneous cochains of `A`. -/
abbrev H0 := groupCohomology A 0

/-- The 0th group cohomology of `A`, defined as the 0th cohomology of the complex of inhomogeneous
cochains, is isomorphic to the invariants of the representation on `A`. -/
def H0Iso : H0 A ≅ ModuleCat.of k A.ρ.invariants :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH0 := H0Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H0Iso_hom :
    π A 0 ≫ (H0Iso A).hom = (cocyclesIso₀ A).hom := by
  simp [H0Iso]

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
    π A 0 ≫ (H0IsoOfIsTrivial A).hom = iCocycles A 0 ≫ (cochainsIso₀ A).hom := by
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
def H1π : ModuleCat.of k (cocycles₁ A) ⟶ H1 A :=
  (isoCocycles₁ A).inv ≫ π A 1

instance : Epi (H1π A) := by unfold H1π; infer_instance

variable {A}

lemma H1π_eq_zero_iff (x : cocycles₁ A) : H1π A x = 0 ↔ ⇑x ∈ coboundaries₁ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCocycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <|  _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₁, shortComplexH1, cocycles₁]

lemma H1π_eq_iff (x y : cocycles₁ A) :
    H1π A x = H1π A y ↔ ⇑x - ⇑y ∈ coboundaries₁ A := by
  rw [← sub_eq_zero, ← map_sub, H1π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H1_induction_on {C : H1 A → Prop} (x : H1 A) (h : ∀ x : cocycles₁ A, C (H1π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H1π] using h ((isoCocycles₁ A).hom y)

variable (A)

/-- The 1st group cohomology of `A`, defined as the 1st cohomology of the complex of inhomogeneous
cochains, is isomorphic to `cocycles₁ A ⧸ coboundaries₁ A`, which is a simpler type. -/
def H1Iso : H1 A ≅ (shortComplexH1 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH1 A) _ _)

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH1 := H1Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H1Iso_hom :
    π A 1 ≫ (H1Iso A).hom = (isoCocycles₁ A).hom ≫
      (shortComplexH1 A).moduleCatLeftHomologyData.π := by
  simp [H1Iso, isoCocycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

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
  isoCocycles₁ A ≪≫ cocycles₁IsoOfIsTrivial A

@[deprecated (since := "2025-05-09")]
noncomputable alias H1LequivOfIsTrivial := H1IsoOfIsTrivial

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H1π_comp_H1IsoOfIsTrivial_hom :
    H1π A ≫ (H1IsoOfIsTrivial A).hom = (cocycles₁IsoOfIsTrivial A).hom := by
  simp [H1IsoOfIsTrivial, H1π]

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_comp_H1π := H1π_comp_H1IsoOfIsTrivial_hom

variable {A}

theorem H1IsoOfIsTrivial_H1π_apply_apply
    (f : cocycles₁ A) (x : Additive G) :
    (H1IsoOfIsTrivial A).hom (H1π A f) x = f x.toMul := by simp

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_comp_H1_π_apply_apply := H1IsoOfIsTrivial_H1π_apply_apply

theorem H1IsoOfIsTrivial_inv_apply (f : Additive G →+ A) :
    (H1IsoOfIsTrivial A).inv f = H1π A ((cocycles₁IsoOfIsTrivial A).inv f) := rfl

@[deprecated (since := "2025-05-09")]
alias H1LequivOfIsTrivial_symm_apply := H1IsoOfIsTrivial_inv_apply

end IsTrivial
end H1
section H2

/-- Shorthand for the 2nd group cohomology of a `k`-linear `G`-representation `A`, `H²(G, A)`,
defined as the 2nd cohomology of the complex of inhomogeneous cochains of `A`. -/
abbrev H2 := groupCohomology A 2

/-- The quotient map from the 2-cocycles of `A`, as a submodule of `G × G → A`, to `H²(G, A)`. -/
def H2π : ModuleCat.of k (cocycles₂ A) ⟶ H2 A :=
  (isoCocycles₂ A).inv ≫ π A 2

instance : Epi (H2π A) := by unfold H2π; infer_instance

variable {A}

lemma H2π_eq_zero_iff (x : cocycles₂ A) : H2π A x = 0 ↔ ⇑x ∈ coboundaries₂ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCocycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <|  _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₂, shortComplexH2, cocycles₂]

lemma H2π_eq_iff (x y : cocycles₂ A) :
    H2π A x = H2π A y ↔ ⇑x - ⇑y ∈ coboundaries₂ A := by
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H2_induction_on {C : H2 A → Prop} (x : H2 A) (h : ∀ x : cocycles₂ A, C (H2π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H2π] using h ((isoCocycles₂ A).hom y)

variable (A)

/-- The 2nd group cohomology of `A`, defined as the 2nd cohomology of the complex of inhomogeneous
cochains, is isomorphic to `cocycles₂ A ⧸ coboundaries₂ A`, which is a simpler type. -/
def H2Iso : H2 A ≅ (shortComplexH2 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH2 A) _ _)

@[deprecated (since := "2025-06-11")]
noncomputable alias isoH2 := H2Iso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma π_comp_H2Iso_hom :
    π A 2 ≫ (H2Iso A).hom = (isoCocycles₂ A).hom ≫
      (shortComplexH2 A).moduleCatLeftHomologyData.π := by
  simp [H2Iso, isoCocycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[deprecated (since := "2025-06-12")]
alias groupCohomologyπ_comp_isoH2_hom := π_comp_H2Iso_hom

end H2
end Cohomology
end groupCohomology
