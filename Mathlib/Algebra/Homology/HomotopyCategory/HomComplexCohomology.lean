/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Cohomology of the hom complex

Given `ℤ`-indexed cochain complexes `K` and `L`, and `n : ℤ`, we introduce
a type `HomComplex.CohomologyClass K L n` which is the quotient
of `HomComplex.Cocycle K L n` which identifies cohomologous cocycles.
We construct this type of cohomology classes instead of using
the homology API because `Cochain K L` can be considered both
as a complex of abelian groups or as a complex of `R`-modules
when the category is `R`-linear. This also complements the API
around `HomComplex` which is centered on terms in types
`Cochain` or `Cocycle` which are suitable for computations.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

namespace HomComplex

/-- The subgroup of `Cocycle K L n` consisting of coboundaries. -/
def coboundaries : AddSubgroup (Cocycle K L n) where
  carrier := setOf (fun α ↦ ∃ (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintro α ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, -β, by aesop⟩

/-- The type of cohomology classes of degree `n` in the complex of morphisms
from `K` to `L`. -/
def CohomologyClass : Type v := Cocycle K L n ⧸ coboundaries K L n

instance : AddCommGroup (CohomologyClass K L n) :=
  inferInstanceAs (AddCommGroup (Cocycle K L n ⧸ coboundaries K L n))

namespace CohomologyClass

variable {K L n}

/-- The cohomology class of a cocycle. -/
def mk (x : Cocycle K L n) : CohomologyClass K L n :=
  Quotient.mk _ x

lemma mk_surjective : Function.Surjective (mk : Cocycle K L n → _) :=
  Quotient.mk_surjective

variable (K L n) in
@[simp]
lemma mk_zero :
    mk (0 : Cocycle K L n) = 0 := rfl

@[simp]
lemma mk_add (x y : Cocycle K L n) :
    mk (x + y) = mk x + mk y := rfl

@[simp]
lemma mk_sub (x y : Cocycle K L n) :
    mk (x - y) = mk x - mk y := rfl

@[simp]
lemma mk_neg (x : Cocycle K L n) :
    mk (-x) = - mk x := rfl

lemma mk_eq_zero_iff (x : Cocycle K L n) :
    mk x = 0 ↔ x ∈ coboundaries K L n :=
  QuotientAddGroup.eq_zero_iff x

variable (K L n) in
/-- The projection map `Cocycle K L n →+ CohomologyClass K L n`. -/
@[simps]
def mkAddMonoidHom : Cocycle K L n →+ CohomologyClass K L n where
  toFun := mk
  map_zero' := by simp
  map_add' := by simp

section

variable {G : Type*} [AddCommGroup G]
  (f : Cocycle K L n →+ G) (hf : coboundaries K L n ≤ f.ker)

/-- Constructor for additive morphisms from `CohomologyClass K L n`. -/
def descAddMonoidHom :
    CohomologyClass K L n →+ G :=
  QuotientAddGroup.lift _ f hf

@[simp]
lemma descAddMonoidHom_cohomologyClass (x : Cocycle K L n) :
    descAddMonoidHom f hf (mk x) = f x := rfl

end

end CohomologyClass

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps]
def leftHomologyData' (hm : n + 1 = m) (hp : m + 1 = p) :
    ((HomComplex K L).sc' n m p).LeftHomologyData where
  K := .of (Cocycle K L m)
  H := .of (CohomologyClass K L m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom K L m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom K L m)
  wi := by cat_disch
  hi := Cocycle.isKernel K L _ _ hp
  wπ := by
    ext x
    dsimp
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n, hm, x, rfl⟩
  hπ :=
    Cofork.IsColimit.mk _
      (fun s ↦ AddCommGrpCat.ofHom (CohomologyClass.descAddMonoidHom s.π.hom
        (by
          rintro ⟨_, _⟩ ⟨q, hq, y, rfl⟩
          obtain rfl : n = q := by lia
          simpa only [zero_comp] using ConcreteCategory.congr_hom s.condition y)))
      (fun s ↦ rfl)
      (fun s l hl ↦ by
        ext x
        obtain ⟨y, rfl⟩ := x.mk_surjective
        simpa using ConcreteCategory.congr_hom hl y)

/-- `CohomologyClass K L m` identifies to the cohomology of the complex `HomComplex K L`
in degree `m`. -/
@[simps!]
noncomputable def leftHomologyData :
    ((HomComplex K L).sc n).LeftHomologyData :=
  leftHomologyData' K L _ n _ (by simp) (by simp)

/-- The homology of `HomComplex K L` in degree `n` identifies to `CohomologyClass K L n`. -/
noncomputable def homologyAddEquiv :
    (HomComplex K L).homology n ≃+ CohomologyClass K L n :=
  (leftHomologyData K L n).homologyIso.addCommGroupIsoToAddEquiv

end HomComplex

end CochainComplex
