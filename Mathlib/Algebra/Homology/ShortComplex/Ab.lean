import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.EpiMono

universe u

open CategoryTheory Category Limits

/-@[ext]
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
  rw [one_smul]-/

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex Ab.{u})

@[simp]
lemma ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  erw [← comp_apply, S.zero]
  rfl

@[simps!]
def abToCycles : S.X₁ →+ AddMonoidHom.ker S.g :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

@[simps]
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGroupCat.of (AddMonoidHom.ker S.g)
  H := AddCommGroupCat.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles)
  i := (AddMonoidHom.ker S.g).subtype
  π := QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGroupCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    erw [QuotientAddGroup.eq_zero_iff]
    rw [AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGroupCat.cokernelIsColimit (AddCommGroupCat.ofHom S.abToCycles)

@[simp]
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = S.abToCycles := rfl

noncomputable def abCyclesIso : S.cycles ≅ AddCommGroupCat.of (AddMonoidHom.ker S.g) :=
  S.abLeftHomologyData.cyclesIso

noncomputable def abHomologyIso : S.homology ≅
    AddCommGroupCat.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso

lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', abLeftHomologyData_f',
    AddCommGroupCat.epi_iff_surjective]
  rfl

lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0),
      ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, hx₁⟩ := h x₂ hx₂
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩

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

lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGroupCat.mono_iff_injective _).1 hS.mono_f

lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGroupCat.epi_iff_surjective _).1 hS.epi_g

end ShortComplex

end CategoryTheory
