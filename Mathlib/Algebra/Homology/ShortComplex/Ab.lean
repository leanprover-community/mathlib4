import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.EpiMono

open CategoryTheory Category

universe u

@[ext]
lemma AddCommGroupCat.hom_ext_from_uliftℤ
    {X : Ab.{u}} (f g : AddCommGroupCat.of (ULift.{u} ℤ) ⟶ X)
    (h : f (ULift.up 1) = g (ULift.up 1)) :
    f = g := by
  let f' : ℤ →+ X := AddMonoidHom.mk' (fun n => f (ULift.up n)) (fun _ _ => f.map_add _ _)
  let g' : ℤ →+ X := AddMonoidHom.mk' (fun n => g (ULift.up n)) (fun _ _ => g.map_add _ _)
  have : f' = g' := by ext; exact h
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

noncomputable def abLiftCycles (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  (AddCommGroupCat.homEquivFromUliftℤ S.cycles)
    (S.liftCycles ((AddCommGroupCat.homEquivFromUliftℤ S.X₂).symm x) (by
      ext
      simp [hx]))

@[simp]
lemma abLiftCycles_ι (x : S.X₂) (hx : S.g x = 0) :
    S.iCycles (S.abLiftCycles x hx) = x := by
  dsimp [abLiftCycles]
  erw [← comp_apply, liftCycles_i, AddCommGroupCat.homEquivFromUliftℤ_symm_one]

lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0),
      ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_epi_toCycles, AddCommGroupCat.epi_iff_surjective]
  constructor
  . intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h (S.abLiftCycles x₂ hx₂)
    exact ⟨x₁, by erw [← S.toCycles_i, comp_apply, hx₁, abLiftCycles_ι]⟩
  . intro hS z
    obtain ⟨x₁, hx₁⟩ := hS (S.iCycles z) (by
      erw [← comp_apply, iCycles_g]
      rfl)
    refine' ⟨x₁, _⟩
    apply_fun S.iCycles
    · erw [← hx₁, ← comp_apply, toCycles_i]
      rfl
    · rw [← AddCommGroupCat.mono_iff_injective]
      infer_instance

lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGroupCat.mono_iff_injective _).1 hS.mono_f

lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGroupCat.epi_iff_surjective _).1 hS.epi_g

lemma ab_exact_iff_ker_le_range :
    S.Exact ↔ S.g.ker ≤ S.f.range :=
  S.ab_exact_iff

lemma ab_exact_iff_range_eq_ker :
    S.Exact ↔ S.f.range = S.g.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine' le_antisymm _ h
    rintro _ ⟨x₁, rfl⟩
    erw [AddMonoidHom.mem_ker, ← comp_apply, S.zero]
    rfl
  · intro h
    rw [h]

end ShortComplex

end CategoryTheory
