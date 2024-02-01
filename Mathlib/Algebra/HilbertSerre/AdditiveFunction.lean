import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Tactic.Linarith

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

section

variable {A B : 𝒞} (f : A ⟶ B)

private noncomputable abbrev sc1 : ShortComplex 𝒞 where
  X₁ := kernel f
  X₂ := A
  X₃ := image f
  f := kernel.ι _
  g := factorThruImage f
  zero := zero_of_comp_mono (image.ι f) <| by
    rw [Category.assoc, image.fac, kernel.condition]

private lemma sc1_exact : sc1 f |>.Exact := by
  rw [← exact_iff_shortComplex_exact]
  dsimp
  have e1 : Exact (kernel.ι f) f := by exact exact_kernel_ι
  have e2 : Exact (kernel.ι f) (factorThruImage f ≫ image.ι f)
  · aesop_cat
  rwa [exact_comp_mono_iff] at e2

private lemma sc1_shortExact : sc1 f |>.ShortExact := by
  fconstructor; apply sc1_exact

private noncomputable abbrev sc2 : ShortComplex 𝒞 where
  X₁ := image f
  X₂ := B
  X₃ := cokernel f
  f := image.ι _
  g := cokernel.π _
  zero := by aesop_cat

private lemma sc2_exact : sc2 f |>.Exact := by
  rw [← exact_iff_shortComplex_exact]
  dsimp
  have e1 : Exact f (cokernel.π f):= Abelian.exact_cokernel f
  have e2 : Exact (factorThruImage f ≫ image.ι f) (cokernel.π f)
  · aesop_cat
  exact Abelian.exact_epi_comp_iff _ _ _ |>.mp e2

private lemma sc2_shortExact : sc2 f |>.ShortExact := by
  fconstructor
  apply sc2_exact

lemma eq_apply_kernel_add_apply_image : μ (kernel f) + μ (image f) = μ A :=
  μ.additive _ <| sc1_shortExact f

lemma eq_apply_image_add_apply_cokernel : μ (image f) + μ (cokernel f) = μ B :=
  μ.additive _ <| sc2_shortExact f

lemma apply_kernel_sub_apply_cokernel_eq_apply_src_sub_apply_tgt :
    μ (kernel f) - μ (cokernel f) = μ A - μ B := by
  have eq1 := congr_arg₂ (· - ·) (μ.eq_apply_kernel_add_apply_image f)
    (μ.eq_apply_image_add_apply_cokernel f)
  simp only at eq1
  linarith

end

section ShortComplex

variable (s : ShortComplex 𝒞) (hs : s.Exact)

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
    congr_arg₂ (· - ·)
      (μ.eq_apply_kernel_add_apply_image s.f)
      (μ.eq_apply_kernel_add_apply_image s.g)
  rw [μ.eq_of_iso (imageIsoKernel s hs)] at eq1
  rwa [add_comm (μ (kernel s.g)), add_sub_add_right_eq_sub] at eq1

lemma apply_shortComplex_of_exact' : μ (kernel s.g) - μ (cokernel s.g) = μ s.X₂ - μ s.X₃ :=
  μ.apply_kernel_sub_apply_cokernel_eq_apply_src_sub_apply_tgt s.g

end ShortComplex

section ComposableArrows

section arbitrary_length

variable {N : ℕ} (S : ComposableArrows 𝒞 N) (hS : S.Exact)

local notation "ker_" m => kernel (S.map' m (m + 1))
local notation "im_" m => image (S.map' m (m + 1))

private lemma im_eq_ker_succ (n : ℕ) (hn : n + 2 ≤ N) : (im_ n) ≅ ker_ (n + 1) :=
  calc (im_ n)
    _ ≅ imageSubobject (S.map' n (n + 1)) := imageSubobjectIso _ |>.symm
    _ ≅ kernelSubobject (S.map' (n + 1) (n + 2)) := by
      letI := imageToKernel_isIso_of_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
        (Abelian.exact_iff_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).mp <|
        (exact_iff_shortComplex_exact (S.sc hS.toIsComplex n)).mpr <| hS.exact _
      exact asIso (imageToKernel _ _ _)
    _ ≅ ker_ (n + 1) := kernelSubobjectIso _

lemma apply_image_eq_apply_ker_succ (n : ℕ) (hn : n + 2 ≤ N) : μ (im_ n) = μ (ker_ (n + 1)) :=
  μ.eq_of_iso (im_eq_ker_succ S hS n hn)

lemma apply_sub_apply_succ (n : ℕ) (hn : n + 3 ≤ N) :
    μ (S.obj' n) - μ (S.obj' (n + 1)) =
    μ (ker_ n) - μ (ker_ (n + 2)) := by
  have eq0 : μ (S.obj' n) - μ (S.obj' (n + 1)) = μ (ker_ n) - μ (im_ (n + 1)) :=
    μ.apply_shortComplex_of_exact (S.sc hS.toIsComplex n) (hS.exact _) |>.symm
  rw [apply_image_eq_apply_ker_succ (hS := hS)] at eq0
  exact eq0

end arbitrary_length

section length6

variable (S : ComposableArrows 𝒞 5) (hS : S.Exact)

local notation "μ_" n => μ (S.obj' n)

lemma alternating_apply_aux_of_length6 :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    (μ (kernel (S.map' 0 1)) - μ (kernel (S.map' 4 5))) + (μ_ 4) - (μ_ 5) := by
  rw [show (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    ((μ_ 0) - (μ_ 1)) + ((μ_ 2) - (μ_ 3)) + ((μ_ 4) - (μ_ 5)) by abel]
  rw [apply_sub_apply_succ (hS := hS) (n := 0), apply_sub_apply_succ (hS := hS) (n := 2)]
  all_goals try omega

lemma alternating_sum_apply_of_length6 :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    μ (kernel (S.map' 0 1)) - μ (cokernel (S.map' 4 5)) := by
  rw [μ.alternating_apply_aux_of_length6 (hS := hS)]
  have := S.sc hS.toIsComplex 3
  have eq0 : _ = μ (S.obj' 4) - μ (S.obj' 5) :=
    μ.apply_shortComplex_of_exact' (S.sc hS.toIsComplex 3)
  rw [add_sub_assoc, ← eq0]
  simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Nat.cast_ofNat, Fin.zero_eta,
    Fin.mk_one, ComposableArrows.map', sub_add_sub_cancel]

lemma alternating_sum_apply_eq_zero_of_zero_zero_of_length6
    (left_zero : IsZero S.left) (right_zero : IsZero S.right) :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) = 0 := by
  rw [alternating_sum_apply_of_length6 (hS := hS)]
  rw [show μ (kernel (S.map' 0 1)) = 0 from ?_, show μ (cokernel (S.map' 4 5)) = 0 from ?_,
    sub_zero]
  · rw [μ.eq_of_iso, μ.map_zero]
    rw [show ComposableArrows.map' S 4 5 = 0 from IsZero.eq_zero_of_tgt right_zero _]
    exact cokernelZeroIsoTarget ≪≫ right_zero.isoZero
  · rw [μ.eq_of_iso, μ.map_zero]
    rw [show ComposableArrows.map' S 0 1 = 0 from IsZero.eq_zero_of_src left_zero _]
    exact kernelZeroIsoSource ≪≫ left_zero.isoZero

end length6

end ComposableArrows

end AdditiveFunction
