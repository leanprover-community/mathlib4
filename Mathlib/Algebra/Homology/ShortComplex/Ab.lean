import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.EpiMono

open CategoryTheory Category

universe u

@[ext]
lemma AddCommGroupCat.hom_ext_from_uliftℤ
    {X : Ab.{u}} (f g : AddCommGroupCat.of (ULift.{u} ℤ) ⟶ X)
    (h : f (ULift.up 1) = g (ULift.up 1)) :
    f = g := by
  let f' : ℤ →+ X :=
    { toFun := fun n => f (ULift.up n)
      map_zero' := f.map_zero
      map_add' := fun x y => f.map_add _ _ }
  let g' : ℤ →+ X :=
    { toFun := fun n => g (ULift.up n)
      map_zero' := g.map_zero
      map_add' := fun x y => g.map_add _ _ }
  have : f' = g' := by ext ; exact h
  ext n
  change f' (ULift.down n) = g' (ULift.down n)
  rw [this]

@[simps]
def AddCommGroupCat.homEquivFromUliftℤ (X : Ab.{u}) :
    (AddCommGroupCat.of (ULift.{u} ℤ) ⟶ X) ≃ (X : Type u) where
  toFun f := f (ULift.up 1)
  invFun x :=
    { toFun := fun n => ULift.down n • x
      map_zero' := zero_smul _ _
      map_add' := fun n₁ n₂ => add_smul _ _ _ }
  left_inv f := by
    apply hom_ext_from_uliftℤ
    dsimp
    rw [one_smul]
  right_inv x := by
    dsimp
    rw [one_smul]

@[simp 1100]
lemma AddCommGroupCat.homEquivFromUliftℤ_symm_one {X : Ab.{u}} (x : X) :
    (homEquivFromUliftℤ X).symm x (ULift.up 1) = x := by
  dsimp
  rw [one_smul]

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex Ab.{u})

noncomputable def liftCyclesAb (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  (AddCommGroupCat.homEquivFromUliftℤ S.cycles)
    (S.liftCycles ((AddCommGroupCat.homEquivFromUliftℤ S.X₂).symm x) (by
      ext
      simp [hx]))

@[simp]
lemma liftCyclesAb_ι (x : S.X₂) (hx : S.g x = 0) :
    S.iCycles (S.liftCyclesAb x hx) = x := by
  dsimp [liftCyclesAb]
  rw [← comp_apply, liftCycles_i, AddCommGroupCat.homEquivFromUliftℤ_symm_one]

lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0),
      ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_epi_toCycles, AddCommGroupCat.epi_iff_surjective]
  constructor
  . intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h (S.liftCyclesAb x₂ hx₂)
    exact ⟨x₁, by rw [← S.toCycles_i, comp_apply, hx₁, liftCyclesAb_ι]⟩
  . intro hS z
    obtain ⟨x₁, hx₁⟩ := hS (S.iCycles z) (by
      rw [← comp_apply, iCycles_g]
      rfl)
    refine' ⟨x₁, _⟩
    apply_fun S.iCycles
    . rw [← hx₁, ← comp_apply, toCycles_i]
    . rw [← AddCommGroupCat.mono_iff_injective]
      infer_instance

end ShortComplex

end CategoryTheory
