/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cocycles and group cohomology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.

In `RepresentationTheory.GroupCohomology.Basic`, we define the `n`th group cohomology of `A` to be
the cohomology of a complex `inhomogeneousCochains A`, whose objects are `(Fin n → G) → A`; this is
unnecessarily unwieldy in low degree.

Moreover, cohomology of a complex is defined as an abstract cokernel, whereas the definitions here
are currently explicit quotients of cocycles by coboundaries. However, we are currently moving away
from this approach, and instead defining more convenient constructors for the existing definitions
of cocycles and cohomology, in order to streamline API. So far the new API is in the sections
`oneCocycles', twoCocycles', oneCoboundaries'` and `twoCoboundaries'`.

We also show that when the representation on `A` is trivial, `H¹(G, A) ≃ Hom(G, A)`.

Given an additive or multiplicative abelian group `A` with an appropriate scalar action of `G`,
we provide support for turning a function `f : G → A` satisfying the 1-cocycle identity into an
element of the `oneCocycles` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries. The
multiplicative case, starting with the section `IsMulCocycle`, just mirrors the additive case;
unfortunately `@[to_additive]` can't deal with scalar actions.

## Main definitions

* `groupCohomology.H0 A`: the invariants `Aᴳ` of the `G`-representation on `A`.
* `groupCohomology.H1 A`: 1-cocycles (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) modulo
  1-coboundaries (i.e. `B¹(G, A) := Im(d⁰: A → Fun(G, A))`).
* `groupCohomology.H2 A`: 2-cocycles (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) modulo
  2-coboundaries (i.e. `B²(G, A) := Im(d¹: Fun(G, A) → Fun(G², A))`).
* `groupCohomology.H1IsoOfIsTrivial`: the isomorphism `H¹(G, A) ≅ Hom(G, A)` when the
  representation on `A` is trivial.
* `groupCohomology.isoHn` for `n = 0, 1, 2`: an isomorphism
  `groupCohomology A n ≅ groupCohomology.Hn A`.

## TODO

* The relationship between `H2` and group extensions
* The inflation-restriction exact sequence
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
theorem dZero_comp_dOne : dZero A ≫ dOne A = 0 := by
  simp [(Iso.eq_inv_comp _).2 (comp_dOne_eq A), (Iso.eq_inv_comp _).2 (comp_dZero_eq A)]

@[deprecated (since := "2025-05-14")] alias dOne_comp_dZero := dZero_comp_dOne

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem dOne_comp_dTwo : dOne A ≫ dTwo A = 0 := by
  simp [(Iso.eq_inv_comp _).2 (comp_dOne_eq A), (Iso.eq_inv_comp _).2 (comp_dTwo_eq A)]

@[deprecated (since := "2025-05-14")] alias dTwo_comp_dOne := dOne_comp_dTwo

open ShortComplex

/-- The (exact) short complex `A.ρ.invariants ⟶ A ⟶ (G → A)`. -/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (subtype_comp_dZero A)

/-- The arrow `A --dZero--> Fun(G, A)` is isomorphic to the differential
`(inhomogeneousCochains A).d 0 1` of the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso : Arrow.mk ((inhomogeneousCochains A).d 0 1) ≅ Arrow.mk (dZero A) :=
  Arrow.isoMk (zeroCochainsIso A) (oneCochainsIso A) (comp_dZero_eq A)

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)`. -/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk (dZero A) (dOne A) (dZero_comp_dOne A)

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_τ₁ hom_τ₂ hom_τ₃ inv_τ₁ inv_τ₂ inv_τ₃]
def shortComplexH1Iso : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A :=
    (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (zeroCochainsIso A) (oneCochainsIso A) (twoCochainsIso A)
      (comp_dZero_eq A) (comp_dOne_eq A)

/-- The short complex `Fun(G, A) --dOne--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)`. -/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk (dOne A) (dTwo A) (dOne_comp_dTwo A)

/-- The short complex `A --dZero--> Fun(G, A) --dOne--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_τ₁ hom_τ₂ hom_τ₃ inv_τ₁ inv_τ₂ inv_τ₃]
def shortComplexH2Iso : (inhomogeneousCochains A).sc 2 ≅ shortComplexH2 A :=
    (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (oneCochainsIso A) (twoCochainsIso A) (threeCochainsIso A)
      (comp_dOne_eq A) (comp_dTwo_eq A)

end Differentials

section Cocycles

instance : FunLike (cocycles A 1) G A :=
  ⟨iCocycles A 1 ≫ (oneCochainsIso A).hom, (ModuleCat.mono_iff_injective _).1 inferInstance⟩

/-- The natural inclusion `cocycles A 1 ⟶ (inhomogeneousCochains A).X 1`, defined to be
`(Fin 1 → G) → A`, composed with an isomorphism to `G → A`. -/
def iOneCocycles : cocycles A 1 ⟶ ModuleCat.of k (G → A) :=
  iCocycles A 1 ≫ (oneCochainsIso A).hom

instance : Mono (iOneCocycles A) := by unfold iOneCocycles; infer_instance

variable {A}

@[simp]
lemma iOneCocycles_apply (f : cocycles A 1) : iOneCocycles A f = f := rfl

/-- Given a `G`-representation `A`, we say a function `f : G → A` is a member of the 1-cocycles
if the function `(g, h) ↦ A.ρ(g)(f(h)) - f(gh) + f(g)` is 0. -/
abbrev MemOneCocycles (f : G → A) := dOne A f = 0

/-- Given a `G`-representation `A`, this produces an element of the 1-cocycles of `A` given a
function `f : G → A` satisfying `MemOneCocycles`. -/
def mkOneCocycles (f : G → A) (hf : MemOneCocycles f) : cocycles A 1 :=
  ((inhomogeneousCochains A).sc 1).cyclesMk ((oneCochainsIso A).inv f) <| by
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 1)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 1) 1) ((oneCochainsIso A).inv f))
    have := congr($((CommSq.horiz_inv ⟨comp_dOne_eq A⟩).w) f)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom]

theorem memOneCocycles (f : cocycles A 1) :
    MemOneCocycles f := by
  simpa using congr($(congr(iCocycles A 1 ≫ $(comp_dOne_eq A))) f)

theorem iOneCocycles_mkOneCocycles (f : G → A) (hf) :
    iOneCocycles A (mkOneCocycles f hf) = f := by
  apply (ModuleCat.mono_iff_injective (oneCochainsIso A).inv).1 inferInstance
  simpa [iOneCocycles] using ((inhomogeneousCochains A).sc 1).i_cyclesMk _ _

@[simp]
theorem coe_mkOneCocycles (f : G → A) (hf) :
    (mkOneCocycles f hf : G → A) = f := iOneCocycles_mkOneCocycles _ _

@[ext]
theorem oneCocycles_ext {f₁ f₂ : cocycles A 1} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

@[simp]
theorem mkOneCocycles_coe (f : cocycles A 1) :
    mkOneCocycles (f : G → A) (memOneCocycles f) = f := by ext; simp

theorem memOneCocycles_def (f : G → A) :
    MemOneCocycles f ↔ ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, dOne_hom_apply, Prod.forall]
    rfl

theorem memOneCocycles_iff (f : G → A) :
    MemOneCocycles f ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [memOneCocycles_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

theorem memOneCocycles_map_one (f : G → A) (hf : MemOneCocycles f) : f 1 = 0 := by
  have := (memOneCocycles_def f).1 hf 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this

@[simp]
theorem oneCocycles_map_one (f : cocycles A 1) : f 1 = 0 :=
  memOneCocycles_map_one f (memOneCocycles f)

theorem memOneCocycles_map_inv (f : G → A) (hf : MemOneCocycles f) (g : G) :
    A.ρ g (f g⁻¹) = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← memOneCocycles_map_one f hf, ← mul_inv_cancel g,
    (memOneCocycles_iff f).1 hf g g⁻¹]

@[simp]
theorem oneCocycles_map_inv (f : cocycles A 1) (g : G) :
    A.ρ g (f g⁻¹) = - f g :=
  memOneCocycles_map_inv f (memOneCocycles f) g

theorem memOneCocycles_dZero_apply (x : A) :
    MemOneCocycles (dZero A x) :=
  congr($(dZero_comp_dOne A) x)

theorem memOneCocycles_map_mul_of_isTrivial [A.IsTrivial]
    (f : G → A) (hf : MemOneCocycles f) (g h : G) :
    f (g * h) = f g + f h := by
  rw [(memOneCocycles_iff f).1 hf, isTrivial_apply A.ρ g (f h), add_comm]

theorem memOneCocycles_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    MemOneCocycles (f ∘ Additive.ofMul) :=
  (memOneCocycles_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      memOneCocycles_map_mul_of_isTrivial, isTrivial_apply A.ρ g (f (Additive.ofMul h)),
      add_comm (f (Additive.ofMul g))]

variable (A)

/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps! hom_hom_apply_apply inv_hom_apply]
def oneCocyclesIsoOfIsTrivial [hA : A.IsTrivial] :
    cocycles A 1 ≅ ModuleCat.of k (Additive G →+ A) :=
  LinearEquiv.toModuleIso
  { toFun (f : cocycles A 1) :=
      { toFun := f ∘ Additive.toMul
        map_zero' := memOneCocycles_map_one f (memOneCocycles f)
        map_add' := memOneCocycles_map_mul_of_isTrivial f (memOneCocycles f) }
    map_add' _ _ := by ext; simp [← iOneCocycles_apply]
    map_smul' _ _ := by ext; simp [← iOneCocycles_apply]
    invFun f := mkOneCocycles (f ∘ Additive.ofMul) (memOneCocycles_of_addMonoidHom f)
    left_inv _ := oneCocycles_ext <| fun _ => by simp
    right_inv _ := by ext; simp }

instance : FunLike (cocycles A 2) (G × G) A :=
  ⟨iCocycles A 2 ≫ (twoCochainsIso A).hom, (ModuleCat.mono_iff_injective _).1 inferInstance⟩

/-- The natural inclusion `cocycles A 2 ⟶ (inhomogeneousCochains A).X 2`, defined to be
`(Fin 2 → G) → A`, composed with an isomorphism to `G × G → A`. -/
def iTwoCocycles : cocycles A 2 ⟶ ModuleCat.of k (G × G → A) :=
  iCocycles A 2 ≫ (twoCochainsIso A).hom

variable {A}

@[simp]
lemma iTwoCocycles_apply (f : cocycles A 2) :
    iTwoCocycles A f = f := rfl

/-- Given a `G`-representation `A`, we say a function `f : G × G → A` is a member of the 2-cocycles
if the function `(g, h, j) ↦ A.ρ(g)(f(h, j)) - f(gh, j) + f(g, hj) - f(g, h)` is 0. -/
abbrev MemTwoCocycles (f : G × G → A) := dTwo A f = 0

/-- Given a `G`-representation `A`, this produces an element of the 2-cocycles of `A` given a
function `f : G × G → A` satisfying `MemTwoCocycles`. -/
def mkTwoCocycles (f : G × G → A) (hf : MemTwoCocycles f) : cocycles A 2 :=
  ((inhomogeneousCochains A).sc 2).cyclesMk ((twoCochainsIso A).inv f) <| by
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 2)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 2) 2) ((twoCochainsIso A).inv f))
    have := congr($((CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w) f)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom]

theorem memTwoCocycles (f : cocycles A 2) :
    MemTwoCocycles f := by
  simpa using congr($(congr(iCocycles A 2 ≫ $(comp_dTwo_eq A))) f)

theorem iTwoCocycles_mkTwoCocycles (f : G × G → A) (hf) :
    iTwoCocycles A (mkTwoCocycles f hf) = f := by
  apply (ModuleCat.mono_iff_injective (twoCochainsIso A).inv).1 inferInstance
  simpa [iTwoCocycles] using ((inhomogeneousCochains A).sc 2).i_cyclesMk _ _

@[simp]
theorem coe_mkTwoCocycles (f : G × G → A) (hf) :
    (mkTwoCocycles f hf : G × G → A) = f := iTwoCocycles_mkTwoCocycles _ _

@[ext]
theorem twoCocycles_ext {f₁ f₂ : cocycles A 2} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.2 h)

@[simp]
theorem mkTwoCocycles_coe (f : cocycles A 2) :
    mkTwoCocycles (f : G × G → A) (memTwoCocycles f) = f := by ext; simp

theorem memTwoCocycles_def (f : G × G → A) :
    MemTwoCocycles f ↔
      ∀ g h j : G, A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, dTwo_hom_apply, Prod.forall]
    rfl

theorem memTwoCocycles_iff (f : G × G → A) :
    MemTwoCocycles f ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [memTwoCocycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

theorem memTwoCocycles_map_one_fst (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((memTwoCocycles_iff f).1 hf 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

theorem memTwoCocycles_map_one_snd (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (memTwoCocycles_iff f).1 hf g 1 1
  simpa only [mul_one, add_left_inj, this]

lemma memTwoCocycles_ρ_map_inv_sub_map_inv (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (memTwoCocycles_iff f).1 hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, memTwoCocycles_map_one_fst f hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

theorem memTwoCocycles_dOne_apply (x : G → A) :
    MemTwoCocycles (dOne A x) :=
  congr($(dOne_comp_dTwo A) x)

end twoCocycles
section twoCocycles'

instance : FunLike (cocycles A 2) (G × G) A :=
  ⟨iCocycles A 2 ≫ (twoCochainsIso A).hom, (ModuleCat.mono_iff_injective _).1 inferInstance⟩

variable (A) in
/-- The natural inclusion `cocycles A 2 ⟶ (inhomogeneousCochains A).X 2`, defined to be
`(Fin 2 → G) → A`, composed with an isomorphism to `G × G → A`. -/
def iTwoCocycles : cocycles A 2 ⟶ ModuleCat.of k (G × G → A) :=
  iCocycles A 2 ≫ (twoCochainsIso A).hom

@[simp]
lemma iTwoCocycles_apply (f : cocycles A 2) :
    iTwoCocycles A f = f := rfl

/-- Given a `G`-representation `A`, we say a function `f : G × G → A` is a member of the 2-cocycles
if the function `(g, h, j) ↦ A.ρ(g)(f(h, j)) - f(gh, j) + f(g, hj) - f(g, h)` is 0. -/
abbrev MemTwoCocycles (f : G × G → A) := dTwo A f = 0

/-- Given a `G`-representation `A`, this produces an element of the 2-cocycles of `A` given a
function `f : G × G → A` satisfying `MemTwoCocycles`. -/
def mkTwoCocycles (f : G × G → A) (hf : MemTwoCocycles f) : cocycles A 2 :=
  ((inhomogeneousCochains A).sc 2).cyclesMk ((twoCochainsIso A).inv f) <| by
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 2)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 2) 2) ((twoCochainsIso A).inv f))
    have := congr($((CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w) f)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom]

theorem memTwoCocycles (f : cocycles A 2) :
    MemTwoCocycles f := by
  simpa using congr($(congr(iCocycles A 2 ≫ $(comp_dTwo_eq A))) f)

theorem iTwoCocycles_mkTwoCocycles (f : G × G → A) (hf) :
    iTwoCocycles A (mkTwoCocycles f hf) = f := by
  apply (ModuleCat.mono_iff_injective (twoCochainsIso A).inv).1 inferInstance
  simpa [iTwoCocycles] using ((inhomogeneousCochains A).sc 2).i_cyclesMk _ _

@[simp]
theorem coe_mkTwoCocycles (f : G × G → A) (hf) :
    (mkTwoCocycles f hf : G × G → A) = f := iTwoCocycles_mkTwoCocycles _ _

@[ext]
theorem twoCocycles_ext' {f₁ f₂ : cocycles A 2} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.2 h)

@[simp]
theorem mkTwoCocycles_coe (f : cocycles A 2) :
    mkTwoCocycles (f : G × G → A) (memTwoCocycles f) = f := by ext; simp

theorem memTwoCocycles_def (f : G × G → A) :
    MemTwoCocycles f ↔
      ∀ g h j : G, A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, dTwo_hom_apply, Prod.forall]
    rfl

theorem memTwoCocycles_iff (f : G × G → A) :
    MemTwoCocycles f ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [memTwoCocycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

theorem memTwoCocycles_map_one_fst (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((memTwoCocycles_iff f).1 hf 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

theorem memTwoCocycles_map_one_snd (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (memTwoCocycles_iff f).1 hf g 1 1
  simpa only [mul_one, add_left_inj, this]

lemma memTwoCocycles_ρ_map_inv_sub_map_inv (f : G × G → A) (hf : MemTwoCocycles f) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (memTwoCocycles_iff f).1 hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, memTwoCocycles_map_one_fst f hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

theorem memTwoCocycles_dOne_apply (x : G → A) :
    MemTwoCocycles (dOne A x) :=
  congr($(dOne_comp_dTwo A) x)

end twoCocycles'

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

section oneCoboundaries

instance : FunLike (oneCoboundaries A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem oneCoboundaries.coe_mk (f : G → A) (hf) :
    ((⟨f, hf⟩ : oneCoboundaries A) : G → A) = f := rfl

@[simp]
theorem oneCoboundaries.val_eq_coe (f : oneCoboundaries A) : f.1 = f := rfl

@[ext]
theorem oneCoboundaries_ext {f₁ f₂ : oneCoboundaries A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

lemma oneCoboundaries_memOneCocycles (x : oneCoboundaries A) : MemOneCocycles x := by
  rcases x with ⟨_, ⟨x, rfl⟩⟩
  exact memOneCocycles_dZero_apply x

variable (A) in
/-- Natural inclusion `B¹(G, A) →ₗ[k] Z¹(G, A)`. -/
abbrev oneCoboundariesToOneCocycles :
    ModuleCat.of k (oneCoboundaries A) ⟶ cocycles A 1 :=
  ((inhomogeneousCochains A).sc 1).liftCycles
    (ModuleCat.ofHom (Submodule.subtype _) ≫ (oneCochainsIso A).inv) <| by
    ext x
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 1)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 1) 1) ((oneCochainsIso A).inv x))
    have := congr($((CommSq.horiz_inv ⟨comp_dOne_eq A⟩).w) x)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom, oneCoboundaries_memOneCocycles x]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem oneCoboundariesToOneCocycles_iOneCocycles :
    oneCoboundariesToOneCocycles A ≫ iOneCocycles A =
      ModuleCat.ofHom (Submodule.subtype _) := by
  ext x : 2
  apply (ModuleCat.mono_iff_injective (oneCochainsIso A).inv).1 inferInstance
  simpa [oneCoboundariesToOneCocycles, iOneCocycles, -ShortComplex.liftCycles_i] using
    (congr($(((inhomogeneousCochains A).sc 1).liftCycles_i _ _) x))

@[simp]
lemma oneCoboundariesToOneCocycles_apply (x : oneCoboundaries A) :
    oneCoboundariesToOneCocycles A x = x.1 := by
  simp [← iOneCocycles_apply]

theorem oneCoboundaries_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    oneCoboundaries A = ⊥ := by
  simp_rw [oneCoboundaries, dZero_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

lemma oneCoboundaries_memOneCocycles (x : oneCoboundaries A) : MemOneCocycles x := by
  rcases x with ⟨_, ⟨x, rfl⟩⟩
  exact memOneCocycles_dZero_apply x

end oneCoboundaries
section oneCoboundaries'

variable (A) in
/-- Natural inclusion `B¹(G, A) →ₗ[k] Z¹(G, A)`. -/
abbrev oneCoboundariesToOneCocycles' :
    ModuleCat.of k (oneCoboundaries A) ⟶ cocycles A 1 :=
  ((inhomogeneousCochains A).sc 1).liftCycles
    (ModuleCat.ofHom (Submodule.subtype _) ≫ (oneCochainsIso A).inv) <| by
    ext x
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 1)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 1) 1) ((oneCochainsIso A).inv x))
    have := congr($((CommSq.horiz_inv ⟨comp_dOne_eq A⟩).w) x)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom, oneCoboundaries_memOneCocycles x]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem oneCoboundariesToOneCocycles_iOneCocycles :
    oneCoboundariesToOneCocycles' A ≫ iOneCocycles A =
      ModuleCat.ofHom (Submodule.subtype _) := by
  ext x : 2
  apply (ModuleCat.mono_iff_injective (oneCochainsIso A).inv).1 inferInstance
  simpa [oneCoboundariesToOneCocycles', iOneCocycles, -ShortComplex.liftCycles_i] using
    (congr($(((inhomogeneousCochains A).sc 1).liftCycles_i _ _) x))

@[simp]
lemma oneCoboundariesToOneCocycles_apply' (x : oneCoboundaries A) :
    oneCoboundariesToOneCocycles A x = x.1 := by
  simp [← iOneCocycles_apply]

end oneCoboundaries'
section twoCoboundaries

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

lemma twoCoboundaries_memTwoCocycles (x : twoCoboundaries A) : MemTwoCocycles x := by
  rcases x with ⟨_, ⟨x, rfl⟩⟩
  exact memTwoCocycles_dOne_apply x

variable (A) in
/-- Natural inclusion `B²(G, A) →ₗ[k] Z²(G, A)`. -/
abbrev twoCoboundariesToTwoCocycles :
    ModuleCat.of k (twoCoboundaries A) ⟶ cocycles A 2 :=
  ((inhomogeneousCochains A).sc 2).liftCycles
    (ModuleCat.ofHom (Submodule.subtype _) ≫ (twoCochainsIso A).inv) <| by
    ext x
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 2)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 2) 2) ((twoCochainsIso A).inv x))
    have := congr($((CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w) x)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom, twoCoboundaries_memTwoCocycles x]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem twoCoboundariesToTwoCocycles_iTwoCocycles :
    twoCoboundariesToTwoCocycles A ≫ iTwoCocycles A =
      ModuleCat.ofHom (Submodule.subtype _) := by
  ext x : 2
  apply (ModuleCat.mono_iff_injective (twoCochainsIso A).inv).1 inferInstance
  simpa [twoCoboundariesToTwoCocycles, iTwoCocycles, -ShortComplex.liftCycles_i] using
    (congr($(((inhomogeneousCochains A).sc 2).liftCycles_i _ _) x))

@[simp]
lemma twoCoboundariesToTwoCocycles_apply (x : twoCoboundaries A) :
    twoCoboundariesToTwoCocycles A x = x.1 := by
  simp [← iTwoCocycles_apply]

lemma twoCoboundaries_memTwoCocycles (x : twoCoboundaries A) : MemTwoCocycles x := by
  rcases x with ⟨_, ⟨x, rfl⟩⟩
  exact memTwoCocycles_dOne_apply x

end twoCoboundaries
section twoCoboundaries'

variable (A) in
/-- Natural inclusion `B²(G, A) →ₗ[k] Z²(G, A)`. -/
abbrev twoCoboundariesToTwoCocycles' :
    ModuleCat.of k (twoCoboundaries A) ⟶ cocycles A 2 :=
  ((inhomogeneousCochains A).sc 2).liftCycles
    (ModuleCat.ofHom (Submodule.subtype _) ≫ (twoCochainsIso A).inv) <| by
    ext x
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).XIsoOfEq (CochainComplex.next ℕ 2)).hom).1 inferInstance
    have := congr($((inhomogeneousCochains A).d_comp_XIsoOfEq_hom
      (CochainComplex.next _ 2) 2) ((twoCochainsIso A).inv x))
    have := congr($((CommSq.horiz_inv ⟨comp_dTwo_eq A⟩).w) x)
    simp_all [-HomologicalComplex.d_comp_XIsoOfEq_hom, twoCoboundaries_memTwoCocycles x]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem twoCoboundariesToTwoCocycles_iTwoCocycles :
    twoCoboundariesToTwoCocycles' A ≫ iTwoCocycles A =
      ModuleCat.ofHom (Submodule.subtype _) := by
  ext x : 2
  apply (ModuleCat.mono_iff_injective (twoCochainsIso A).inv).1 inferInstance
  simpa [twoCoboundariesToTwoCocycles, iTwoCocycles, -ShortComplex.liftCycles_i] using
    (congr($(((inhomogeneousCochains A).sc 2).liftCycles_i _ _) x))

@[simp]
lemma twoCoboundariesToTwoCocycles_apply' (x : twoCoboundaries A) :
    twoCoboundariesToTwoCocycles' A x = x.1 := by
  simp [← iTwoCocycles_apply]

end twoCoboundaries'
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
abbrev oneCocyclesOfIsOneCocycle {f : G → A} (hf : IsOneCocycle f) :
    cocycles (Rep.ofDistribMulAction k G A) 1 :=
  mkOneCocycles f <| (memOneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf

theorem isOneCocycle_of_memOneCocycles
    (f : G → A) (hf : MemOneCocycles (A := Rep.ofDistribMulAction k G A) f) :
    IsOneCocycle f :=
  fun _ _ => (memOneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

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
abbrev twoCocyclesOfIsTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) :
    cocycles (Rep.ofDistribMulAction k G A) 2 :=
  mkTwoCocycles f <| (memTwoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf

theorem isTwoCocycle_of_memTwoCocycles
    (f : G × G → A) (hf : MemTwoCocycles (A := Rep.ofDistribMulAction k G A) f) :
    IsTwoCocycle f := (memTwoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

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

/-! The next few sections, until the section `Cohomology`, are a multiplicative copy of the
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
abbrev oneCocyclesOfIsMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) :
    cocycles (Rep.ofMulDistribMulAction G M) 1 :=
  mkOneCocycles (Additive.ofMul ∘ f) <| (memOneCocycles_iff
    (A := Rep.ofMulDistribMulAction G M) f).2 hf

theorem isMulOneCocycle_of_memOneCocycles
    (f : G → M) (hf : MemOneCocycles (A := Rep.ofMulDistribMulAction G M) f) :
    IsMulOneCocycle (Additive.toMul ∘ f) :=
  (memOneCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

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
abbrev twoCocyclesOfIsMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) :
    cocycles (Rep.ofMulDistribMulAction G M) 2 :=
  mkTwoCocycles (Additive.ofMul ∘ f) <|
    (memTwoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf

theorem isMulTwoCocycle_of_memTwoCocycles
    (f : G × G → M) (hf : MemTwoCocycles (A := Rep.ofMulDistribMulAction G M) f) :
    IsMulTwoCocycle (Additive.toMul ∘ f) :=
  (memTwoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

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

section H0

instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : dZero _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

/-- The 0-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`A.ρ.invariants`, which is a simpler type. -/
def zeroCocyclesIso : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dZeroArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma zeroCocyclesIso_hom_comp_f :
    (zeroCocyclesIso A).hom ≫ (shortComplexH0 A).f =
      iCocycles A 0 ≫ (zeroCochainsIso A).hom := by
  dsimp [zeroCocyclesIso]
  apply KernelFork.mapOfIsLimit_ι

@[deprecated (since := "2025-05-09")]
alias isoZeroCocycles_hom_comp_subtype := zeroCocyclesIso_hom_comp_f

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma zeroCocyclesIso_inv_comp_iCocycles :
    (zeroCocyclesIso A).inv ≫ iCocycles A 0 =
      (shortComplexH0 A).f ≫ (zeroCochainsIso A).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, zeroCocyclesIso_hom_comp_f]

variable {A} in
lemma mk_eq_zeroCocyclesIso_inv_apply (x : A.ρ.invariants) :
    cocyclesMk ((zeroCochainsIso A).inv x.1) (by
      ext g; simp [zeroCochainsIso, x.2 (g 0)]) = (zeroCocyclesIso A).inv x :=
  (ModuleCat.mono_iff_injective <| iCocycles A 0).1 inferInstance <| by
    rw [iCocycles_mk]
    exact (zeroCocyclesIso_inv_comp_iCocycles_apply A x).symm

/-- The 0-opcocycles of the complex of inhomogeneous chains of `A` are isomorphic to `A`. -/
def zeroOpcocyclesIso : (inhomogeneousCochains A).opcycles 0 ≅ A.V :=
  ((inhomogeneousCochains A).pOpcyclesIso 0 _ (by simp) (by simp)).symm ≪≫ zeroCochainsIso A

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma pOpcocycles_hom_comp_zeroOpcocyclesIso :
    (inhomogeneousCochains A).pOpcycles 0 ≫ (zeroOpcocyclesIso A).hom =
      (zeroCochainsIso A).hom := by
  simp [zeroOpcocyclesIso]

/-- The 0-cocycles of the complex of inhomogeneous cochains of `A` are isomorphic to
`A.ρ.invariants`, which is a simpler type. -/
def isoZeroCocycles : groupCohomology A 0 ≅ cocycles A 0 :=
  (CochainComplex.isoHomologyπ₀ _).symm

/-- The inclusion `H⁰(G, A) ≅ Z⁰(G, A) ⟶ ((Fin 0 → G) → A) ≅ A`. -/
abbrev iZero : groupCohomology A 0 ⟶ A.V :=
  (isoZeroCocycles A).hom ≫ iCocycles A 0 ≫ (zeroCochainsIso A).hom

instance : Mono (iZero A) := by unfold iZero; infer_instance

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem π_isoZeroCocycles_hom :
    groupCohomologyπ A 0 ≫ (isoZeroCocycles A).hom = 𝟙 _ := by
  simp [isoZeroCocycles, groupCohomologyπ]

/-- The 0th group cohomology of `A`, defined as the 0th cohomology of the complex of inhomogeneous
cochains, is isomorphic to the invariants of the representation on `A`. -/
def H0Iso : groupCohomology A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  isoZeroCocycles A ≪≫ zeroCocyclesIso A

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem π_H0Iso_hom :
    groupCohomologyπ A 0 ≫ (H0Iso A).hom = (zeroCocyclesIso A).hom := by
  simp [H0Iso]

@[ext]
theorem H0_ext {x y : groupCohomology A 0}
    (h : iZero A x = iZero A y) : x = y := (ModuleCat.mono_iff_injective _).1 inferInstance h

/-- When the representation on `A` is trivial, then `H⁰(G, A)` is all of `A.` -/
def H0IsoOfIsTrivial [A.IsTrivial] :
    groupCohomology A 0 ≅ A.V :=
  H0Iso A ≪≫ LinearEquiv.toModuleIso (LinearEquiv.ofTop _ (invariants_eq_top A.ρ))

@[simp] theorem H0IsoOfIsTrivial_hom_eq_iZero [A.IsTrivial] :
    (H0IsoOfIsTrivial A).hom = iZero A := by
  simp [H0IsoOfIsTrivial, H0Iso, ← zeroCocyclesIso_hom_comp_f, shortComplexH0,
    LinearEquiv.ofTop]

@[reassoc]
lemma groupCohomologyπ_comp_H0Iso_hom  :
    groupCohomologyπ A 0 ≫ (H0Iso A).hom = (zeroCocyclesIso A).hom := by
  simp

end H0

section H1
open ShortComplex

/-- The quotient map `Z¹(G, A) → H¹(G, A).` -/
abbrev H1π : cocycles A 1 ⟶ groupCohomology A 1 := groupCohomologyπ A 1

variable {A} in
lemma H1π_eq_zero_iff (x : cocycles A 1) : H1π A x = 0 ↔ ⇑x ∈ oneCoboundaries A := by
  have h₁ := leftHomologyπ_naturality' (shortComplexH1Iso A).hom (leftHomologyData _)
    (shortComplexH1 A).moduleCatLeftHomologyData
  have h₂ : _ = iCocycles A 1 ≫ (oneCochainsIso A).hom := cyclesMap'_i (shortComplexH1Iso A).hom
    ((inhomogeneousCochains A).sc 1).leftHomologyData (shortComplexH1 A).moduleCatLeftHomologyData
  simp_all only [HomologicalComplex.homologyπ, homologyπ, leftHomologyπ, ← leftHomologyMapIso'_hom,
    ← Iso.eq_comp_inv, ModuleCat.hom_comp]
  simp [LinearMap.range_codRestrict, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective <|  _).1
    inferInstance), moduleCatToCycles, ← iOneCocycles_apply, iOneCocycles, ← h₂, oneCoboundaries,
    -cyclesMap'_i, shortComplexH1]

variable {A} in
lemma H1π_eq_iff (x y : cocycles A 1) : H1π A x = H1π A y ↔ ⇑(x - y) ∈ oneCoboundaries A := by
  rw [← sub_eq_zero, ← map_sub, H1π_eq_zero_iff]

@[elab_as_elim]
theorem H1_induction {C : groupCohomology A 1 → Prop}
    (h : ∀ (f : G → A) (hf : MemOneCocycles f), C (H1π A <| mkOneCocycles f hf))
    (x : groupCohomology A 1) : C x := by
  induction x using groupCohomology_induction with | @h x =>
  simpa using h x (memOneCocycles x)

/-- When `A : Rep k G` is a trivial representation of `G`, `H¹(G, A)` is isomorphic to the
group homs `G → A`. -/
def H1IsoOfIsTrivial [A.IsTrivial] :
    groupCohomology A 1 ≅ ModuleCat.of k (Additive G →+ A) :=
  ((inhomogeneousCochains A).isoHomologyπ 0 1 (by simp) <| by
    ext; simp [inhomogeneousCochains.d_def, inhomogeneousCochains.d,
      Unique.eq_default (α := Fin 0 → G), Pi.zero_apply (M := fun _ => A)]).symm ≪≫
    oneCocyclesIsoOfIsTrivial A

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H1π_comp_H1IsoOfIsTrivial [A.IsTrivial] :
    H1π A ≫ (H1IsoOfIsTrivial A).hom = (oneCocyclesIsoOfIsTrivial A).hom := by
  simp [H1IsoOfIsTrivial]

theorem H1IsoOfIsTrivial_H1π_apply_apply [A.IsTrivial] (f : cocycles A 1) (x : Additive G) :
    (H1IsoOfIsTrivial A).hom (H1π A f) x = f x.toMul := by
  simp [oneCocyclesIsoOfIsTrivial]

@[simp]
theorem H1IsoOfIsTrivial_inv_apply [A.IsTrivial] (f : Additive G →+ A) :
    (H1IsoOfIsTrivial A).inv f = H1π A ((oneCocyclesIsoOfIsTrivial A).inv f) := by
  rfl

end H1

section H2
open ShortComplex

/-- The quotient map `Z²(G, A) → H²(G, A).` -/
abbrev H2π : cocycles A 2 ⟶ groupCohomology A 2 := groupCohomologyπ A 2

variable {A} in
lemma H2π_eq_zero_iff (x : cocycles A 2) : H2π A x = 0 ↔ ⇑x ∈ twoCoboundaries A := by
  have h₁ := leftHomologyπ_naturality' (shortComplexH2Iso A).hom (leftHomologyData _)
    (shortComplexH2 A).moduleCatLeftHomologyData
  have h₂ : _ = iCocycles A 2 ≫ (twoCochainsIso A).hom := cyclesMap'_i (shortComplexH2Iso A).hom
    ((inhomogeneousCochains A).sc 2).leftHomologyData (shortComplexH2 A).moduleCatLeftHomologyData
  simp_all only [HomologicalComplex.homologyπ, homologyπ, leftHomologyπ, ← leftHomologyMapIso'_hom,
    ← Iso.eq_comp_inv, ModuleCat.hom_comp]
  simp [LinearMap.range_codRestrict, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective <|  _).1
    inferInstance), moduleCatToCycles, ← iTwoCocycles_apply, iTwoCocycles, ← h₂, twoCoboundaries,
    -cyclesMap'_i, shortComplexH2]

variable {A} in
lemma H2π_eq_iff (x y : cocycles A 2) : H2π A x = H2π A y ↔ ⇑(x - y) ∈ twoCoboundaries A := by
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]

@[elab_as_elim]
theorem H2_induction {C : groupCohomology A 2 → Prop}
    (h : ∀ (f : G × G → A) (hf : MemTwoCocycles f), C (H2π A <| mkTwoCocycles f hf))
    (x : groupCohomology A 2) : C x := by
  induction x using groupCohomology_induction with | @h x =>
  simpa using h x (memTwoCocycles x)

end H2
end groupCohomology
