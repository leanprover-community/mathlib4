import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Tactic.Linarith

open CategoryTheory CategoryTheory.Limits

universe u v w

variable (𝒞 : Type u) [Category.{v} 𝒞]
variable (T : Type w) [AddCommGroup T]
variable [Abelian 𝒞]

open ZeroObject

/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
structure AdditiveFunction :=
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
toFun : 𝒞 → T
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
additive (s : ShortComplex 𝒞) (e : s.ShortExact) : toFun s.X₁ + toFun s.X₃ = toFun s.X₂

@[inherit_doc]
notation C "⟹+" T => AdditiveFunction C T


-- @[inherit_doc]
-- notation C "==>+ ℤ" => AdditiveFunction C

namespace AdditiveFunction

variable {𝒞 T}
variable (μ : 𝒞 ⟹+ T)

private lemma ext' {α β : 𝒞 ⟹+ T} (h : α.toFun = β.toFun) : α = β := by
  cases α; cases β; rwa [mk.injEq]

instance : DFunLike (AdditiveFunction 𝒞 T) 𝒞 (fun _ ↦ T) where
  coe μ := μ.toFun
  coe_injective' _ _ h := AdditiveFunction.ext' h

@[ext] lemma ext {α β : 𝒞 ⟹+ T} (h : ∀ x, α x = β x) : α = β := by
  apply ext'; ext; apply h

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
  rw [← eq1]
  abel

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

@[simps!]
private noncomputable def im_eq_ker_succ (n : ℕ) (hn : n + 2 ≤ N := by omega) :
    (image (S.map' n (n + 1))) ≅ kernel (S.map' (n + 1) (n + 2)) :=
  (imageSubobjectIso (S.map' n (n + 1))).symm ≪≫
    @asIso (f := imageToKernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
        hS.toIsComplex.zero n) _
      (imageToKernel_isIso_of_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
        (Abelian.exact_iff_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).mp <|
        (exact_iff_shortComplex_exact (S.sc hS.toIsComplex n)).mpr <| hS.exact _)
  -- (let h1 : IsIso (imageToKernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <| hS.toIsComplex.zero n) :=
      -- imageToKernel_isIso_of_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
      --   (Abelian.exact_iff_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).mp <|
      --   (exact_iff_shortComplex_exact (S.sc hS.toIsComplex n)).mpr <| hS.exact _
  --   asIso (imageToKernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <| hS.toIsComplex.zero n))
    ≪≫
  kernelSubobjectIso (S.map' (n + 1) (n + 2))

  -- calc (im_ n)
  --   _ ≅ imageSubobject (S.map' n (n + 1)) := imageSubobjectIso _ |>.symm
  --   _ ≅ kernelSubobject (S.map' (n + 1) (n + 2)) := by
      -- letI := imageToKernel_isIso_of_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
      --   (Abelian.exact_iff_image_eq_kernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).mp <|
      --   (exact_iff_shortComplex_exact (S.sc hS.toIsComplex n)).mpr <| hS.exact _
  --     exact asIso (imageToKernel (S.map' (n + 1) (n + 2)) (S.map' n (n + 1)) _)
  --   _ ≅ ker_ (n + 1) := kernelSubobjectIso _

lemma apply_image_eq_apply_ker_succ (n : ℕ) (hn : n + 2 ≤ N) : μ (im_ n) = μ (ker_ (n + 1)) :=
  μ.eq_of_iso (im_eq_ker_succ S hS n hn)

lemma apply_sub_apply_succ (n : ℕ) (hn : n + 3 ≤ N) :
    μ (S.obj' n) - μ (S.obj' (n + 1)) =
    μ (ker_ n) - μ (ker_ (n + 2)) := by
  have eq0 : μ (S.obj' n) - μ (S.obj' (n + 1)) = μ (ker_ n) - μ (im_ (n + 1)) :=
    μ.apply_shortComplex_of_exact (S.sc hS.toIsComplex n) (hS.exact _) |>.symm
  rw [apply_image_eq_apply_ker_succ (hS := hS)] at eq0
  exact eq0

lemma apply_eq_apply_image_add_apply_image
    (n : ℕ) (hn1 : 1 ≤ n := by omega) (hn2 : n + 1 ≤ N := by omega) :
    μ (S.obj' n) = μ (image (S.map' (n - 1) n)) + μ (image (S.map' n (n + 1))) := by
  let sc : ShortComplex 𝒞 :=
  { X₁ := image (S.map' (n - 1) n)
    X₂ := S.obj' n
    X₃ := image (S.map' n (n + 1))
    f := image.ι _
    g := factorThruImage (S.map' _ _)
    zero := by
      refine zero_of_comp_mono (image.ι _) ?_
      rw [Category.assoc, image.fac]
      refine image.ext _ ?_
      rw [image.fac_assoc, comp_zero]

      have eq1 :
        S.map' (n - 1) (n - 1 + 1) ≫ S.map' (n - 1 + 1) (n - 1 + 2) ≫
        S.map' (n - 1 + 2) (n + 1) = 0
      · rw [← Category.assoc, hS.toIsComplex.zero (n - 1), zero_comp]
      simp only [← S.map_comp, homOfLE_comp, ← eq1] }

  have sc_exact : sc.Exact
  · have e1 := hS.exact (n - 1)
    have e2 : Exact (kernel.ι (S.map' n (n + 1))) (S.map' n (n + 1)) := by exact exact_kernel_ι
    have e3 : Exact (kernel.ι (S.map' n (n + 1)))
      (factorThruImage (S.map' n (n + 1)) ≫ image.ι (S.map' n (n + 1)))
    · aesop_cat
    rw [← exact_iff_shortComplex_exact] at e1 ⊢
    change Exact (image.ι _) (factorThruImage (S.map' n (n + 1)))
    have e4 : Exact (image.ι (ComposableArrows.map' S (n - 1) n))
      (factorThruImage (ComposableArrows.map' S n (n + 1)) ≫
        image.ι (ComposableArrows.map' S n (n + 1)))
    · rw [image.fac]
      suffices : Exact (Abelian.image.ι (S.map' (n - 1) n)) (S.map' n (n + 1))
      · have eq0 := Abelian.imageIsoImage_hom_comp_image_ι (S.map' (n - 1) n)
        rw [← Iso.eq_inv_comp] at eq0
        rwa [eq0, exact_iso_comp]
      rw [← Abelian.exact_iff_exact_image_ι]
      change Exact (S.map' _ _) (S.map' _ _) at e1

      let α1 : S.obj' (n - 1 + 1) ≅ S.obj' n := eqToIso (by congr; omega)
      replace e1 := exact_comp_hom_inv_comp_iff
        (f := S.map' (n - 1) (n - 1 + 1)) (g := S.map' (n - 1 + 1) (n - 1 + 2)) (i := α1) |>.mpr e1
      rwa [show S.map' (n - 1) (n - 1 + 1) ≫ α1.hom = S.map' (n - 1) n from ?_,
        show α1.inv ≫ S.map' (n - 1 + 1) (n - 1 + 2) =
          S.map' n (n + 1) ≫ (eqToIso (by congr 2; omega)).hom from _,
        exact_comp_iso] at e1
      · rw [show α1.inv = S.map (eqToHom <| by congr 1; omega) from _, ← S.map_comp,
          show (eqToIso _).hom = S.map (eqToHom <| by congr 1; omega) from _, ← S.map_comp]
        · rfl
        · rw [eqToIso.hom, eqToHom_map]
        · rw [eqToIso.inv, eqToHom_map]
      · rw [show α1.hom = S.map (eqToHom <| by congr 1; omega) from _, ← S.map_comp]
        congr 1
        rw [eqToIso.hom, eqToHom_map]
    rwa [exact_comp_mono_iff] at e4

  have sc_shortExact : sc.ShortExact
  · fconstructor; exact sc_exact

  exact μ.additive _ sc_shortExact |>.symm

lemma apply_eq_apply_kernel_add_apply_kernel
    (n : ℕ) (hn : n + 2 ≤ N) :
    μ (S.obj' n) = μ (kernel (S.map' n (n + 1))) + μ (kernel (S.map' (n + 1) (n + 2))) := by
  let sc : ShortComplex 𝒞 :=
  { X₁ := kernel (S.map' n (n + 1))
    X₂ := S.obj' n
    X₃ := kernel (S.map' (n + 1) (n + 2))
    f := kernel.ι _
    g := kernel.lift _ (S.map' _ _) <| hS.toIsComplex.zero n
    zero := zero_of_comp_mono (kernel.ι _) <| by simp }

  have sc_exact : sc.Exact
  · rw [← exact_iff_shortComplex_exact]
    change Exact (kernel.ι _) (kernel.lift _ _ _)
    rw [← exact_comp_mono_iff (h := kernel.ι _), kernel.lift_ι]
    exact exact_kernel_ι

  have sc_shortExact : sc.ShortExact
  · refine .mk' sc_exact equalizer.ι_mono ?_
    change Epi (kernel.lift _ _ _)

    suffices eq0 :
      (kernel.lift _ (S.map' n (n + 1)) <| hS.toIsComplex.zero n) =
      factorThruImage _ ≫ (im_eq_ker_succ S hS n).hom
    · rw [eq0]; exact epi_comp _ _

    ext
    rw [im_eq_ker_succ_hom (n := n), kernel.lift_ι, Category.assoc, Category.assoc, Category.assoc,
      kernelSubobject_arrow, imageToKernel_arrow, imageSubobject_arrow', image.fac]

  exact μ.additive _ sc_shortExact |>.symm

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
  abel

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

section AddCommGroup

instance add : Add (𝒞 ⟹+ T) where
  add α β :=
  { toFun := α + β
    additive := fun s hs ↦ by
      have eq0 : α _ + α _ + (β _ + β _) = α _ + β _ :=
        congr_arg₂ (· + ·) (α.additive _ hs) (β.additive _ hs)
      simp only [Pi.add_apply] at eq0 ⊢
      rw [← eq0]
      abel }

@[simp] lemma add_apply (α β : 𝒞 ⟹+ T) (x) : (α + β) x = α x + β x := rfl

instance neg : Neg (𝒞 ⟹+ T) where
  neg μ :=
  { toFun := - μ
    additive := fun s hs ↦ by
      have eq0 : - (μ _ + μ _) = - μ _ := congr_arg (- ·) (μ.additive _ hs)
      simp only [Pi.neg_apply] at eq0 ⊢
      rw [← eq0]
      abel }

@[simp] lemma neg_apply (μ : 𝒞 ⟹+ T) (x) : (-μ) x = - (μ x) := rfl

instance zero : Zero (𝒞 ⟹+ T) where
  zero :=
  { toFun := 0
    additive := fun _ _ ↦ show 0 + 0 = 0 by simp }

@[simp] lemma zero_apply (x) : (0 : 𝒞 ⟹+ T) x = 0 := rfl

instance addSemigroup : AddSemigroup (𝒞 ⟹+ T) where
  add_assoc α β γ := ext fun x ↦ by simp [add_assoc]

instance addZeroClass : AddZeroClass (𝒞 ⟹+ T) where
  zero_add _ := ext fun _ ↦ by simp
  add_zero _ := ext fun _ ↦ by simp

instance addMonoid : AddMonoid (𝒞 ⟹+ T) where
  __ := addSemigroup
  __ := addZeroClass

instance addCommMonoid : AddCommMonoid (𝒞 ⟹+ T) where
  __ := addMonoid
  add_comm _ _ := ext fun _ ↦ by simp [add_comm]

instance : AddCommGroup (𝒞 ⟹+ T) where
  __ := addCommMonoid
  add_left_neg _ := ext fun _ ↦ by simp

end AddCommGroup

end AdditiveFunction
