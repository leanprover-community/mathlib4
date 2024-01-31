import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable (𝒞 : Type u) [Category.{v} 𝒞]
variable [Abelian 𝒞]

open ZeroObject

/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
@[ext] structure AdditiveFunction :=
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
toFun : 𝒞 → ℤ
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
additive (s : ShortComplex 𝒞) (e : s.ShortExact) : toFun s.X₁ + toFun s.X₃ = toFun s.X₂

@[inherit_doc]
notation C "⟹+ ℤ" => AdditiveFunction C


@[inherit_doc]
notation C "==>+ ℤ" => AdditiveFunction C

namespace AdditiveFunction

variable {𝒞}
variable (μ : 𝒞 ⟹+ ℤ)

instance : DFunLike (AdditiveFunction 𝒞) 𝒞 (fun _ ↦ ℤ) where
  coe μ := μ.toFun
  coe_injective' _ _ h := AdditiveFunction.ext _ _ h

lemma map_zero : μ 0 = 0 := by
  let s : ShortComplex 𝒞 :=
  { X₁ := 0
    X₂ := 0
    X₃ := 0
    f := 0
    g := 0
    zero := by aesop_cat }
  have hs : s.Exact
  · rw [← exact_iff_shortComplex_exact (S := s)]
    change Exact 0 0
    exact exact_zero_mono 0
  replace hs : s.ShortExact
  · fconstructor; exact hs
  have : μ 0 + μ 0 = μ 0 := μ.additive s hs
  aesop

lemma eq_of_iso {x y : 𝒞} (e : x ≅ y) : μ x = μ y := by
  let s : ShortComplex 𝒞 :=
  { X₁ := x
    X₂ := y
    X₃ := 0
    f := e.hom
    g := 0
    zero := by aesop_cat }
  have hs : s.Exact
  · rw [← exact_iff_shortComplex_exact (S := s)]
    change Exact e.hom 0
    exact exact_epi_zero e.hom
  replace hs : s.ShortExact
  · fconstructor; exact hs
  have : μ x + μ 0 = μ y := μ.additive s hs
  rwa [map_zero, add_zero] at this

section ShortComplex

variable (s : ShortComplex 𝒞) (hs : s.Exact)

private noncomputable abbrev sc1 : ShortComplex 𝒞 where
  X₁ := kernel s.f
  X₂ := s.X₁
  X₃ := image s.f
  f := kernel.ι _
  g := factorThruImage s.f
  zero := zero_of_comp_mono (image.ι s.f) <| by
    rw [Category.assoc, image.fac, kernel.condition]

private lemma sc1_exact : sc1 s |>.Exact := by
  rw [← exact_iff_shortComplex_exact] at hs ⊢
  dsimp
  have e1 : Exact (kernel.ι s.f) s.f := by exact exact_kernel_ι
  have e2 : Exact (kernel.ι s.f) (factorThruImage s.f ≫ image.ι s.f)
  · aesop_cat
  rwa [exact_comp_mono_iff] at e2

private lemma sc1_shortExact : sc1 s |>.ShortExact := by
  fconstructor; apply sc1_exact

private lemma apply_X₁ : μ (kernel s.f) + μ (image s.f) = μ s.X₁ :=
  μ.additive _ <| sc1_shortExact s

private noncomputable abbrev sc2 : ShortComplex 𝒞 where
  X₁ := kernel s.g
  X₂ := s.X₂
  X₃ := image s.g
  f := kernel.ι _
  g := factorThruImage s.g
  zero := zero_of_comp_mono (image.ι s.g) <| by
    rw [Category.assoc, image.fac, kernel.condition]

private lemma sc2_exact : sc2 s |>.Exact := by
  rw [← exact_iff_shortComplex_exact] at hs ⊢
  dsimp
  have e1 : Exact (kernel.ι s.g) s.g := by exact exact_kernel_ι
  have e2 : Exact (kernel.ι s.g) (factorThruImage s.g ≫ image.ι s.g)
  · aesop_cat
  rwa [exact_comp_mono_iff] at e2

private lemma sc2_shortExact : sc2 s |>.ShortExact := by
  fconstructor; apply sc2_exact

private lemma apply_X₂ : μ (kernel s.g) + μ (image s.g) = μ s.X₂ :=
  μ.additive _ <| sc2_shortExact s

private noncomputable def imageIsoKernel : image s.f ≅ kernel s.g :=
  calc image s.f
    _ ≅ imageSubobject s.f := imageSubobjectIso _ |>.symm
    _ ≅ kernelSubobject s.g :=
      letI := imageToKernel_isIso_of_image_eq_kernel s.f s.g <|
        (Abelian.exact_iff_image_eq_kernel s.f s.g).mp <| exact_iff_shortComplex_exact _ |>.mpr hs
      asIso (imageToKernel s.f s.g _)
    _ ≅ kernel s.g := kernelSubobjectIso _

lemma apply_shortComplex_of_exact : μ (kernel s.f) - μ (image s.g) = μ s.X₁ - μ s.X₂ := by
  have eq1 : μ (kernel s.f) + μ (image s.f) - (μ (kernel s.g) + μ (image s.g)) = μ s.X₁ - μ s.X₂ :=
    congr_arg₂ (· - ·) (μ.apply_X₁ s) (μ.apply_X₂ s)
  rw [μ.eq_of_iso (imageIsoKernel s hs)] at eq1
  rwa [add_comm (μ (kernel s.g)), add_sub_add_right_eq_sub] at eq1

end ShortComplex

end AdditiveFunction
