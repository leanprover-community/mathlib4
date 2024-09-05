import Mathlib.RepresentationTheory.GroupCohomology.Basic

universe v u
open CategoryTheory Limits

variable {C D : Type*} [Category C] [HasZeroMorphisms C] [Category D] (F : C ⥤ D)

structure CompleteResolution (Z : C) where
  complex : ChainComplex C ℤ
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  [hasHomology : ∀ i, complex.HasHomology i]
  π : complex.X 0 ⟶ Z
  [π_mono : Mono π]
  ε : Z ⟶ complex.X (-1)
  [ε_epi : Epi ε]
  π_comp_ε : π ≫ ε = complex.d 0 (-1)

open CompleteResolution in
attribute [instance] projective hasHomology π_mono ε_epi

class HasCompleteResolution (Z : C) : Prop where
  out : Nonempty (CompleteResolution Z)

variable (C) in
class HasCompleteResolutions : Prop where
  out : ∀ Z : C, HasCompleteResolution Z

instance [HasCompleteResolutions C] (Z : C) :
    HasCompleteResolution Z where
  out := (HasCompleteResolutions.out Z).out

noncomputable abbrev completeResolution (Z : C) [HasZeroObject C]
    [HasZeroMorphisms C] [HasCompleteResolution Z] :
    CompleteResolution Z :=
  (HasCompleteResolution.out (Z := Z)).some

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

section norm

lemma ρ_mul_apply (g h : G) (x : A) :
    A.ρ (g * h) x = A.ρ g (A.ρ h x) := by
  simp

variable [Fintype G]
/-- The norm map associated to a `k`-linear `G`-representation on `A`, when `G` is a finite group.
Sends `x : A` to `∑ ρ(g)(x)` for `g : G`. -/
@[simps]
def norm (A : Rep k G) : A ⟶ A where
  hom := ∑ g, Action.ρ A g
  comm g := by
    ext x
    simp only [ModuleCat.coe_comp, Function.comp_apply]
    erw [LinearMap.coeFn_sum]
    simp only [Finset.sum_apply, map_sum]
    rw [Fintype.sum_bijective (fun x => g⁻¹ * x * g)
      ((Group.mulRight_bijective g).comp (Group.mulLeft_bijective g⁻¹))]
    intro h
    erw [ρ_mul_apply, ρ_mul_apply, ρ_self_inv_apply]
    rfl

-- I always have to `erw` this; not sure how to fix it
@[simp] theorem norm_apply {A : Rep k G} (x : A) :
    (norm A).hom x = ∑ g : G, A.ρ g x := LinearMap.sum_apply _ _ _

theorem norm_of_unique [hU : Unique G] {A : Rep k G} (x : A) :
    (Rep.norm A).hom x = x := by
  erw [Rep.norm_apply x]
  rw [Finset.univ_unique, Finset.sum_singleton,
    ← Unique.eq_default 1, map_one, LinearMap.one_apply]

theorem norm_ofDistribMulAction_eq {A : Type u} [AddCommGroup A] [Module k A]
    [DistribMulAction G A] [SMulCommClass G k A] (x : A) :
    (norm (ofDistribMulAction k G A)).hom x = ∑ g : G, g • x := norm_apply _

theorem norm_ofMulDistribMulAction_eq {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] (x : M) :
    Additive.toMul ((Rep.norm (Rep.ofMulDistribMulAction G M)).hom (Additive.ofMul x))
      = ∏ g : G, g • x := norm_apply _

end norm

instance : HasCompleteResolutions (Rep k G) := sorry

noncomputable def tateCohomologyOne (A : Rep k G) (i : ℤ) : ModuleCat k :=
  ((completeResolution (Rep.trivial k G k)).complex.linearYonedaObj
    k A).homology i

def tateCohomologyTwo (A : Rep k G) (i : ℤ) : ModuleCat k

/-
complex morphism for proj resn means that
   d
P₁ → P₀
|    |π
0 -> Z
d ≫ π = 0
and the quasiiso bit means that P₀/Im d ≅ Z

I want

X₁ ⟶ X₀ ⟶ X₋₁ ⟶ X₋₂
     π|    |ε
        Z

what I need is just π epi, ε mono, π ≫ ε = d₀



I mean we want π ≫ ε = d₀
π is an epi, ε is a mono
so indeed d₁ ≫ π = 0

and ε satisfies ε ≫ d₋₁

well π ≫ ε ≫ d₋₁ = 0

if π is a morphism of complexes that just means
-/
