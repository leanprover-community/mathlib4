/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution

/-!
# Horseshoe Lemma

The Horseshoe Lemma is a result in homological algebra that provides a way to construct a short
exact sequence of projective resolutions. Let `𝒞` be an abelian category with enough projectives
and
```
0 -> A --> B --> C -> 0
```
be a short exact sequence.
In this file, we construct simultaneously three projective resolutions `P` of `A`, `S` of `B`,
and `Q` of `C` such that `S` is the binary biproduct of `P` and `Q`. That is we have the following
commutative diagram:
```
0 -> ... --> ... ----> ... -> 0
      |       |         |
      v       v         v
0 -> P₁ --> P₁ ⊕ Q₁ --> Q₁ -> 0
      |       |         |
      v       v         v
0 -> P₀ -> P₀ ⊕ Q₀ ---> Q₀ -> 0
      |       |         |
      v       v         v
0 -> A ----> B ------> C -> 0
```
-/

open CategoryTheory Limits
open scoped ZeroObject

noncomputable section

universe u v

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] [EnoughProjectives 𝒞]

lemma exact_lemma1 {X Y Z W : 𝒞}
    (g : Y ⟶ Z) (h : Z ⟶ W) (f : X ⟶ kernel g) (i : kernel g ⟶ Y) (hf : Epi f) (hh : Mono h)
  (hi : i = kernel.ι g) : CategoryTheory.Exact (f ≫ i) (g ≫ h) := by
  suffices Exact i g by
    exact exact_comp_mono (exact_epi_comp this)
  rw [hi]
  exact exact_kernel_ι


namespace CategoryTheory.ShortComplex

variable (A B : ShortComplex 𝒞) (fAB : A ⟶ B)

open Projective

/--
The first row of the horseshoe lemma.
```
      P₁ --> P₁ ⊕ Q₁ --> Q₁
      |       |         |
      v       v         v
0 --> A ----> B ------> C --> 0
```
-/
@[simps]
def horseshoeBase : ShortComplex 𝒞 where
  X₁ := over A.X₁
  X₂ := over A.X₁ ⊞ over A.X₃
  X₃ := over A.X₃
  f := biprod.inl
  g := biprod.snd
  zero := by simp

/--
The first row `P₁ --> P₁ ⊕ Q₁ --> Q₁` of the horseshoe lemma is split.
-/
def horseshoeBase_splitting : A.horseshoeBase.Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := by simp
  s_g := by simp
  id := by simp

lemma horseshoeBase_shortExact : A.horseshoeBase.ShortExact :=
  A.horseshoeBase_splitting.shortExact

instance : Fact (ShortExact (horseshoeBase A)) := ⟨horseshoeBase_shortExact _⟩

/--
The morphism from the first row `P₁ --> P₁ ⊕ Q₁ --> Q₁` to the zeroth row. We will call it `π`.
-/
@[simps]
def horseshoeBaseπ [epi : Epi A.g] : A.horseshoeBase ⟶ A where
  τ₁ := π _
  τ₂ := biprod.desc (π _ ≫ A.f) (factorThru (π _) A.g)
  τ₃ := π _
  comm₁₂ := by simp
  comm₂₃ := by aesop_cat

instance horseshoeBaseπ_epi_τ₁ [epi : Epi A.g] : Epi A.horseshoeBaseπ.τ₁ := by
  simp only [horseshoeBase_X₁, horseshoeBaseπ_τ₁]; infer_instance

instance horseshoeBaseπ_epi_τ₃ [epi : Epi A.g] : Epi A.horseshoeBaseπ.τ₃ := by
  simp only [horseshoeBase_X₃, horseshoeBaseπ_τ₃]; infer_instance

lemma horseshoeBase_exact1 :
    (ComposableArrows.mk₃
      (horseshoeBase A).f
      (horseshoeBase A).g
      (0 : (horseshoeBase A).X₃ ⟶ 0)).Exact := by
  fconstructor
  · refine ⟨fun n hn => ?_⟩
    simp only [ge_iff_le] at hn
    replace hn : n = 0 ∨ n = 1 := by omega
    rcases hn with (rfl | rfl)
    · simp
    · simp
  · intro n hn
    simp only [ge_iff_le] at hn
    replace hn : n = 0 ∨ n = 1 := by omega
    rcases hn with (rfl | rfl)
    · exact horseshoeBase_shortExact A |>.exact
    · rw [← exact_iff_shortComplex_exact]
      simp only [horseshoeBase_X₁, horseshoeBase_X₂, horseshoeBase_X₃, horseshoeBase_f,
        horseshoeBase_g, ComposableArrows.mk₃, ComposableArrows.mk₂, id_eq, Nat.cast_ofNat,
        Int.Nat.cast_ofNat_Int, ComposableArrows.precomp_obj, ComposableArrows.Precomp.obj_succ,
        ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, ComposableArrows.precomp_map,
        ComposableArrows.Precomp.map_succ_succ, BinaryBiproduct.bicone_inl,
        BinaryBiproduct.bicone_snd, Fin.zero_eta, ComposableArrows.Precomp.obj_zero, Fin.mk_one,
        ComposableArrows.Precomp.obj_one, ComposableArrows.map',
        ComposableArrows.Precomp.map_one_succ, ComposableArrows.Precomp.map_zero_one,
        ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map]
      rw [← epi_iff_exact_zero_right]
      infer_instance

instance [short_exact : Fact <| A.ShortExact] : Epi A.g := short_exact.out.epi_g

instance [short_exact : Fact <| A.ShortExact] : Mono A.f := short_exact.out.mono_f

instance horseshoeBaseπ_epi_τ₂ [short_exact : Fact <| A.ShortExact] : Epi A.horseshoeBaseπ.τ₂ := by
  classical
  simp only [horseshoeBase_X₂, horseshoeBaseπ_τ₂]
  refine @Abelian.epi_of_epi_of_epi_of_mono 𝒞 _ _
    (.mk₃  (horseshoeBase A).f (horseshoeBase A).g (0 : over A.X₃ ⟶ 0))
    (.mk₃ A.f A.g (0 : A.X₃ ⟶ 0))
    (ComposableArrows.homMk₃ (π _) (biprod.desc (π _ ≫ A.f) (factorThru (π _) A.g)) (π _) 0
    (by simp) (by aesop_cat) (by simp)) ?_ ?_ ?_ ?_ ?_
  · apply horseshoeBase_exact1
  · fconstructor
    · refine ⟨fun n hn => ?_⟩
      simp only [ge_iff_le] at hn
      replace hn : n = 0 ∨ n = 1 := by omega
      rcases hn with (rfl | rfl)
      · simp
      · simp
    · intro n hn
      simp only [ge_iff_le] at hn
      replace hn : n = 0 ∨ n = 1 := by omega
      rcases hn with (rfl | rfl)
      · exact short_exact.out.exact
      · rw [← exact_iff_shortComplex_exact]
        simp only [ComposableArrows.mk₃, ComposableArrows.mk₂, id_eq, Nat.cast_ofNat,
          Int.Nat.cast_ofNat_Int, ComposableArrows.precomp_obj, ComposableArrows.Precomp.obj_succ,
          ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, ComposableArrows.precomp_map,
          ComposableArrows.Precomp.map_succ_succ, Fin.zero_eta, ComposableArrows.Precomp.obj_zero,
          Fin.mk_one, ComposableArrows.Precomp.obj_one, ComposableArrows.map',
          ComposableArrows.Precomp.map_one_succ, ComposableArrows.Precomp.map_zero_one,
          ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map]
        rw [← epi_iff_exact_zero_right]
        infer_instance
  · dsimp; infer_instance
  · dsimp; infer_instance
  · dsimp; infer_instance

-- TODO : move this; this belongs to another file
variable {A B} in
/--
kernel of a short complex
-/
@[simps!]
def horseshoeKer : ShortComplex 𝒞 where
  X₁ := kernel fAB.τ₁
  X₂ := kernel fAB.τ₂
  X₃ := kernel fAB.τ₃
  f := kernel.map _ _ A.f B.f fAB.comm₁₂
  g := kernel.map _ _ A.g B.g fAB.comm₂₃
  zero := by
    ext
    simp only [horseshoeBase_X₁, horseshoeBaseπ_τ₁, horseshoeBase_X₃, horseshoeBaseπ_τ₃,
      horseshoeBase_X₂, horseshoeBaseπ_τ₂, horseshoeBase_f, horseshoeBase_g, equalizer_as_kernel,
      Category.assoc, zero_comp]
    erw [kernel.lift_ι, kernel.lift_ι_assoc]
    simp

-- TODO : move this; this belongs to another file
variable {A B} in
/--
the morphism from kernel of a short compelx to itself
-/
@[simps]
def horseshoeKerι : horseshoeKer fAB ⟶ A where
  τ₁ := kernel.ι _
  τ₂ := kernel.ι _
  τ₃ := kernel.ι _
  comm₁₂ := by simp
  comm₂₃ := by simp


-- TODO : move this; this belongs to another file
variable {A B} in
/--
cokernel of a short complex
-/
@[simps!]
def horseshoeCoker : ShortComplex 𝒞 where
  X₁ := cokernel fAB.τ₁
  X₂ := cokernel fAB.τ₂
  X₃ := cokernel fAB.τ₃
  f := cokernel.map _ _ A.f B.f fAB.comm₁₂
  g := cokernel.map _ _ A.g B.g fAB.comm₂₃
  zero := by ext; simp

-- TODO : move this; this belongs to another file
variable {A B} in
/--
the morphism a short complex to its cokernel
-/
@[simps]
def horseshoeCokerπ : B ⟶ horseshoeCoker fAB where
  τ₁ := cokernel.π _
  τ₂ := cokernel.π _
  τ₃ := cokernel.π _
  comm₁₂ := by simp
  comm₂₃ := by simp

@[reassoc]
lemma horseshoeKerι_comp [Fact <| A.ShortExact] :
    horseshoeKerι A.horseshoeBaseπ ≫ A.horseshoeBaseπ = 0 := by
  ext <;> simp


variable [a_se : Fact <| A.ShortExact] [b_se : Fact <| B.ShortExact]

variable {A B} in
/-- ker f -> A - f -> B -> coker f -/
@[simps!]
def horseshoeSnakeInput :
    SnakeInput 𝒞 where
  L₀ := horseshoeKer fAB
  L₁ := A
  L₂ := B
  L₃ := horseshoeCoker fAB
  v₀₁ := horseshoeKerι fAB
  v₁₂ := fAB
  v₂₃ := horseshoeCokerπ fAB
  h₀ := by
    apply (config := {allowSynthFailures := true}) KernelFork.IsLimit.ofι'
    · intro C g h
      refine ⟨⟨kernel.lift _ g.τ₁ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.1,
        kernel.lift _ g.τ₂ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.1,
        kernel.lift _ g.τ₃ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.2, ?_, ?_⟩, ?_⟩
      · exact equalizer.hom_ext <| by simpa using g.comm₁₂
      · exact equalizer.hom_ext <| by simpa using g.comm₂₃
      · ext <;> simp
    · constructor
      intro C g₁ g₂ h
      ext
      · exact equalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.1
      · exact equalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.1
      · exact equalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.2
  h₃ := by
    apply (config := {allowSynthFailures := true}) CokernelCofork.IsColimit.ofπ'
    · intro C g h
      refine ⟨⟨cokernel.desc _ g.τ₁ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.1,
        cokernel.desc _ g.τ₂ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.1,
        cokernel.desc _ g.τ₃ <| ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.2, ?_, ?_⟩, ?_⟩
      · exact coequalizer.hom_ext <| by simpa using g.comm₁₂
      · exact coequalizer.hom_ext <| by simpa using g.comm₂₃
      · ext <;> simp
    · constructor
      intro C g₁ g₂ h
      ext
      · exact coequalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.1
      · exact coequalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.1
      · exact coequalizer.hom_ext <| by simpa using ShortComplex.Hom.ext_iff _ _ |>.mp h |>.2.2
  L₁_exact := a_se.out.exact
  epi_L₁_g := inferInstance
  L₂_exact := b_se.out.exact
  mono_L₂_f := inferInstance

lemma horseshoeSnakeInput_L₀_shortExact [Epi fAB.τ₁] :
    (horseshoeSnakeInput fAB).L₀.ShortExact where
  exact := (horseshoeSnakeInput fAB).L₀_exact
  mono_f := by dsimp; infer_instance
  epi_g := by
    dsimp only [horseshoeSnakeInput_L₀_X₂, horseshoeSnakeInput_L₀_X₃, horseshoeSnakeInput_L₀_g]
    have h := Abelian.tfae_epi (cokernel fAB.τ₁) (kernel.map fAB.τ₂ fAB.τ₃ A.g B.g fAB.comm₂₃)
      |>.out 0 2
    refine h.mpr ?_
    have := (horseshoeSnakeInput fAB).snake_lemma.2 1
    rw [← exact_iff_shortComplex_exact] at this
    simp only [SnakeInput.composableArrows, ComposableArrows.mk₅, horseshoeSnakeInput_L₀_X₂,
      horseshoeSnakeInput_L₀_X₃, horseshoeSnakeInput_L₃_X₁, horseshoeSnakeInput_L₃_X₂,
      horseshoeSnakeInput_L₃_X₃, horseshoeSnakeInput_L₀_g, horseshoeSnakeInput_L₃_f,
      horseshoeSnakeInput_L₃_g, ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂,
      horseshoeSnakeInput_L₀_X₁, horseshoeSnakeInput_L₀_f, id_eq, Nat.cast_ofNat,
      Int.Nat.cast_ofNat_Int, Fin.mk_one, ComposableArrows.precomp_obj,
      ComposableArrows.Precomp.obj_one, Fin.zero_eta, ComposableArrows.Precomp.obj_zero,
      ComposableArrows.Precomp.obj_succ, ComposableArrows.map', ComposableArrows.precomp_map,
      ComposableArrows.Precomp.map_one_succ, ComposableArrows.Precomp.map_zero_one,
      ComposableArrows.Precomp.map_succ_succ] at this
    dsimp at this
    convert this using 1
    symm
    convert IsZero.eq_of_tgt _ _ _ using 1
    simp only [horseshoeSnakeInput_L₃_X₁]
    exact (isZero_zero _).of_iso <| Limits.cokernel.ofEpi _

instance [Epi fAB.τ₁] : Fact (horseshoeSnakeInput fAB).L₀.ShortExact :=
  ⟨horseshoeSnakeInput_L₀_shortExact _ _ _⟩

variable (𝒞) in
/--
structure used in the inductive step of the horseshoe lemma
-/
structure STEP where
/--we need three short exact sequences X, Y, Z-/
(X Y Z : ShortComplex 𝒞)
/--short exact-/
(X_se : X.ShortExact)
/--short exact-/
(Y_se : Y.ShortExact)
/--short exact-/
(Z_se : Z.ShortExact)
/-- the morphism between X and Y-/
(ι : X ⟶ Y)
/-- the morphism between Y and Z-/
(π : Y ⟶ Z)

instance (x : STEP 𝒞) : Fact (x.X.ShortExact) := ⟨x.X_se⟩
instance (x : STEP 𝒞) : Fact (x.Y.ShortExact) := ⟨x.Y_se⟩
instance (x : STEP 𝒞) : Fact (x.Z.ShortExact) := ⟨x.Z_se⟩

/--
induction:

for case zero, we consider the following:
```
0 --> ker a ---> ker b --> ker c -> 0
      |          |         |
      v          v         v
0 --> P₁ --> P₁ ⊕ Q₁ ---> Q₁ -> 0
      |a       |b        |c
      v        v         v
0 --> A ----> B ------> C --> 0
```

Assume we have case n:
```
0 -> G --> H --> I -> 0
    |     |     |
    v     v     v
0 -> D --> E --> F -> 0
    |     |     |
    v     v     v
0 -> A --> B --> C -> 0
```
we consider the following:
```
0 -> ker a --> ker b --> ker c -> 0
      |         |          |
      v         v          v
0 -> P_G --> P_G ⊕ P_I --> P_I -> 0
      |a        |b        |c
      v        v          v
0 -> G ------> H -------> I -> 0
```
-/
def horseshoeStep : ℕ → STEP 𝒞
  | 0 =>
    { X := horseshoeKer (horseshoeBaseπ A)
      Y := horseshoeBase A
      Z := A
      X_se := horseshoeSnakeInput_L₀_shortExact _ _ _
      Y_se := horseshoeBase_shortExact A
      Z_se := a_se.out
      ι := horseshoeKerι _
      π := horseshoeBaseπ _ }
  | n + 1 =>
    { X := horseshoeKer (horseshoeBaseπ (horseshoeStep n).X)
      Y := horseshoeBase (horseshoeStep n).X
      Z := (horseshoeStep n).X
      X_se := horseshoeSnakeInput_L₀_shortExact _ _ _
      Y_se := horseshoeBase_shortExact _
      Z_se := (horseshoeStep n).X_se
      ι := horseshoeKerι _
      π := horseshoeBaseπ _ }

@[reassoc]
lemma horseshoeStep_ι_comp_π (n : ℕ) : (horseshoeStep A n).ι ≫ (horseshoeStep A n).π = 0 :=
match n with
| 0 => by apply horseshoeKerι_comp
| n + 1 => by apply horseshoeKerι_comp

instance horseshoeStep_mono₁ (n : ℕ) : Mono (horseshoeStep A n).ι.τ₁ :=
match n with
| 0 => by
  simp [horseshoeStep]
  infer_instance
| n + 1 => by
  simp [horseshoeStep]
  infer_instance


instance horseshoeStep_mono₂ (n : ℕ) : Mono (horseshoeStep A n).ι.τ₂ :=
match n with
| 0 => by
  simp [horseshoeStep]
  infer_instance
| n + 1 => by
  simp [horseshoeStep]
  infer_instance


instance horseshoeStep_mono₃ (n : ℕ) : Mono (horseshoeStep A n).ι.τ₃ :=
match n with
| 0 => by
  simp [horseshoeStep]
  infer_instance
| n + 1 => by
  simp [horseshoeStep]
  infer_instance

/--
the `n`-th row of the horseshoe lemma
-/
def horseshoeObj (n : ℕ) : ShortComplex 𝒞 := horseshoeStep A n |>.Y

/--
the morphism from the `n+1`-th row to the `n`-th row of the horseshoe lemma
-/
def horseshoeD (n : ℕ) : horseshoeObj A (n + 1) ⟶ horseshoeObj A n :=
  (horseshoeStep A (n + 1)).π ≫ (horseshoeStep A n).ι

lemma horseshoeD_square (n : ℕ) : horseshoeD A (n + 1) ≫ horseshoeD A n = 0 := by
  simp [horseshoeD, horseshoeStep, horseshoeKerι_comp_assoc]

/--
the chain complex of short complex in the horse lemma, every row is short exact,
every column is exact.
```
0 -> ... -----> ... ----> ....
      |         |          |
      v         v          v
0 -> P₂ --> P₂ ⊕ Q₂ --> Q₂ -> 0
      |       |         |
      v       v         v
0 -> P₁ --> P₁ ⊕ Q₁ --> Q₁ -> 0
      |       |         |
      v       v         v
0 -> P₀ --> P₀ ⊕ Q₀ --> Q₀ -> 0
```
-/
@[simps!]
def horseshoe : ChainComplex (ShortComplex 𝒞) ℕ :=
.of (horseshoeObj A) (horseshoeD A) (horseshoeD_square A)

/--
the zeroth row `P₀ --> P₀ ⊕ Q₀ --> Q₀` to the base `A --> B --> C`.
-/
abbrev horseshoeπ : (horseshoe A).X 0 ⟶ A := horseshoeBaseπ A

lemma horseshoe_d_π : (horseshoe A).d 1 0 ≫ horseshoeπ A = 0 := by
  simp only [horseshoe_X, horseshoe_d, zero_add, ↓reduceDite, eqToHom_refl, Category.id_comp]
  have eq := horseshoeStep_ι_comp_π A 0
  simp only [horseshoeStep, horseshoeD, Category.assoc] at eq ⊢
  rw [eq, comp_zero]

/--
a chain complex of the left term
-/
abbrev horseshoeChainComplex₁ : ChainComplex 𝒞 ℕ :=
ShortComplex.π₁.mapHomologicalComplex _ |>.obj (horseshoe A)

/--
a chain complex of the middle term
-/
abbrev horseshoeChainComplex₂ : ChainComplex 𝒞 ℕ :=
ShortComplex.π₂.mapHomologicalComplex _ |>.obj (horseshoe A)

/--
a chain complex of the right term
-/
abbrev horseshoeChainComplex₃ : ChainComplex 𝒞 ℕ :=
ShortComplex.π₃.mapHomologicalComplex _ |>.obj (horseshoe A)

instance (n : ℕ) : Projective <| (horseshoeChainComplex₁ A).X n := by
  rcases n with (_|n) <;>
  simp only [Nat.zero_eq, Functor.mapHomologicalComplex_obj_X, horseshoe_X,
    horseshoeObj, horseshoeStep, π₁_obj, horseshoeBase_X₁, horseshoeChainComplex₁] <;>
  infer_instance

instance (n : ℕ) : Projective <| (horseshoeChainComplex₂ A).X n := by
  rcases n with (_|n) <;>
  simp only [Nat.zero_eq, Functor.mapHomologicalComplex_obj_X, horseshoe_X, horseshoeObj,
    horseshoeStep, π₂_obj, horseshoeBase_X₂] <;>
  infer_instance

instance (n : ℕ) : Projective <| (horseshoeChainComplex₃ A).X n := by
  rcases n with (_|n) <;>
  simp only [Nat.zero_eq, Functor.mapHomologicalComplex_obj_X, horseshoe_X, horseshoeObj,
    horseshoeStep, π₃_obj, horseshoeBase_X₃] <;>
  infer_instance

/--
the augmentation map on the left term.
-/
abbrev horseshoeToSingle₁ :
    horseshoeChainComplex₁ A ⟶ (ChainComplex.single₀ 𝒞).obj A.X₁ :=
  ChainComplex.toSingle₀Equiv _ _ |>.symm
    ⟨ShortComplex.π₁.map (horseshoeπ A), by simp [horseshoeD, horseshoeStep]⟩

/--
the augmentation map on the middle term.
-/
abbrev horseshoeToSingle₂ :
    horseshoeChainComplex₂ A ⟶ (ChainComplex.single₀ 𝒞).obj A.X₂ :=
  ChainComplex.toSingle₀Equiv _ _ |>.symm
    ⟨ShortComplex.π₂.map (horseshoeπ A), by simp [horseshoeD, horseshoeStep]⟩

/--
the augmentation map on the right term.
-/
abbrev horseshoeToSingle₃ :
    horseshoeChainComplex₃ A ⟶ (ChainComplex.single₀ 𝒞).obj A.X₃ :=
  ChainComplex.toSingle₀Equiv _ _ |>.symm
  ⟨ShortComplex.π₃.map (horseshoeπ A), by simp [horseshoeD, horseshoeStep]⟩

lemma horseshoeExact₁ (n : ℕ) :
    CategoryTheory.Exact
      ((horseshoeChainComplex₁ A).d (n + 2) (n + 1))
      ((horseshoeChainComplex₁ A).d (n + 1) n) := by
  simp only [horseshoeChainComplex₁, Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₁_obj,
    Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, horseshoeD, Category.id_comp,
    dite_eq_ite, π₁_map, ↓reduceDite, comp_τ₁]
  rw [if_pos (by abel)]
  apply exact_lemma1
  · change Epi (horseshoeBaseπ _).τ₁
    simp only [horseshoeBase_X₁, horseshoeBaseπ_τ₁]
    infer_instance
  · cases n <;>
    change Mono (horseshoeKerι _).τ₁ <;>
    simp only [Nat.zero_eq, horseshoeKer_X₁, horseshoeBaseπ_τ₁, horseshoeKerι_τ₁] <;>
    infer_instance
  · simp [horseshoeStep]

lemma horseshoeExact₂ (n : ℕ) :
    CategoryTheory.Exact
      ((horseshoeChainComplex₂ A).d (n + 2) (n + 1))
      ((horseshoeChainComplex₂ A).d (n + 1) n) := by
  simp only [Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₂_obj,
    Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, horseshoeD, Category.id_comp,
    dite_eq_ite, π₂_map, ↓reduceDite, comp_τ₂]
  rw [if_pos (by abel)]
  apply exact_lemma1
  · change Epi (horseshoeBaseπ _).τ₂
    infer_instance
  · cases n <;>
    change Mono (horseshoeKerι _).τ₂ <;>
    simp only [Nat.zero_eq, horseshoeKer_X₂, horseshoeBaseπ_τ₂, horseshoeKerι_τ₂] <;>
    infer_instance
  · simp [horseshoeStep]

lemma horseshoeExact₃ (n : ℕ) :
    CategoryTheory.Exact
      ((horseshoeChainComplex₃ A).d (n + 2) (n + 1))
      ((horseshoeChainComplex₃ A).d (n + 1) n) := by
  simp only [Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₂_obj,
    Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, horseshoeD, Category.id_comp,
    dite_eq_ite, π₂_map, ↓reduceDite, comp_τ₂]
  rw [if_pos (by abel)]
  apply exact_lemma1
  · change Epi (horseshoeBaseπ _).τ₃
    infer_instance
  · cases n <;>
    change Mono (horseshoeKerι _).τ₃ <;>
    simp only [Nat.zero_eq, horseshoeKer_X₃, horseshoeBaseπ_τ₃, horseshoeKerι_τ₃] <;>
    infer_instance
  · simp [horseshoeStep]

instance : QuasiIsoAt (horseshoeToSingle₁ A) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros'] <;> try rfl
  dsimp
  simp only [zero_add, ↓reduceIte, Category.id_comp, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    horseshoe_X, π₁_map, horseshoeBaseπ_τ₁]
  refine ⟨?_, inferInstance⟩
  rw [← exact_iff_shortComplex_exact]
  apply (config := {allowSynthFailures := true}) CategoryTheory.exact_epi_comp
  · exact exact_kernel_ι
  · dsimp [horseshoeStep]; infer_instance

instance : QuasiIsoAt (horseshoeToSingle₂ A) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros'] <;> try rfl
  dsimp
  simp only [zero_add, ↓reduceIte, Category.id_comp, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    horseshoe_X, π₂_map, horseshoeBaseπ_τ₂]
  refine ⟨?_, (horseshoeBaseπ_epi_τ₂ A)⟩
  rw [← exact_iff_shortComplex_exact]
  apply (config := {allowSynthFailures := true}) CategoryTheory.exact_epi_comp
  · exact exact_kernel_ι
  · exact horseshoeBaseπ_epi_τ₂ (horseshoeStep A 0).X

instance : QuasiIsoAt (horseshoeToSingle₃ A) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros'] <;> try rfl
  dsimp
  simp only [zero_add, ↓reduceIte, Category.id_comp, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    horseshoe_X, π₃_map, horseshoeBaseπ_τ₃]
  refine ⟨?_, (horseshoeBaseπ_epi_τ₃ A)⟩
  rw [← exact_iff_shortComplex_exact]
  apply (config := {allowSynthFailures := true}) CategoryTheory.exact_epi_comp
  · exact exact_kernel_ι
  · exact horseshoeBaseπ_epi_τ₃ (horseshoeStep A 0).X

lemma stupid_aux (A B : ShortComplex 𝒞) (h : A = B)  :
    (eqToHom h).τ₁ = eqToHom (by simp [h]) := by induction h; simp

lemma stupid_aux' (A B : ShortComplex 𝒞) (h : A = B)  :
    (eqToHom h).τ₂ = eqToHom (by simp [h]) := by induction h; simp

lemma stupid_aux'' (A B : ShortComplex 𝒞) (h : A = B)  :
    (eqToHom h).τ₃ = eqToHom (by simp [h]) := by induction h; simp

lemma stupid_aux2 (m n : ℕ) (h : m = n) :
    eqToHom (by simp [h]) ≫ horseshoeD A m = horseshoeD A n ≫ eqToHom (by simp [h]) := by
  induction h; simp

lemma stupid_aux2' (m n : ℕ) (h : m = n) :
    eqToHom (by simp [h]) ≫ (horseshoeD A m).τ₁ = (horseshoeD A n).τ₁ ≫ eqToHom (by simp [h]) := by
  induction h; simp

lemma stupid_aux2'' (m n : ℕ) (h : m = n) :
    eqToHom (by simp [h]) ≫ (horseshoeD A m).τ₂ = (horseshoeD A n).τ₂ ≫ eqToHom (by simp [h]) := by
  induction h; simp

lemma stupid_aux2''' (m n : ℕ) (h : m = n) :
    eqToHom (by simp [h]) ≫ (horseshoeD A m).τ₃ = (horseshoeD A n).τ₃ ≫ eqToHom (by simp [h]) := by
  induction h; simp

instance (n : ℕ) : QuasiIsoAt (horseshoeToSingle₁ A) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have z1 : IsZero <| ((ChainComplex.single₀ _).obj A.X₁).homology (n + 1) := by
    apply HomologicalComplex.isZero_single_obj_homology
    simp

  have z2 : IsZero <| HomologicalComplex.homology (horseshoeChainComplex₁ A) (n + 1) := by
    suffices e : HomologicalComplex.homology (horseshoeChainComplex₁ A) (n + 1) ≅ 0 from
      e.isZero_iff.mpr (isZero_zero _)

    refine exact_iff_homology_iso_zero _ |>.mp ?_ |>.some
    rw [← exact_iff_shortComplex_exact]
    have := horseshoeExact₁ A n
    simp only [Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₁_obj,
      Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, Category.id_comp,
      dite_eq_ite, π₁_map, ↓reduceDite] at this
    rw [if_pos (by abel)] at this

    simp only [horseshoeChainComplex₁, HomologicalComplex.shortComplexFunctor_obj_X₁,
      Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₁_obj,
      HomologicalComplex.shortComplexFunctor_obj_X₂, HomologicalComplex.shortComplexFunctor_obj_X₃,
      HomologicalComplex.shortComplexFunctor_obj_f, Functor.mapHomologicalComplex_obj_d,
      horseshoe_d, ChainComplex.prev, ↓reduceDite, π₁_map, comp_τ₁,
      HomologicalComplex.shortComplexFunctor_obj_g, ChainComplex.next_nat_succ, exact_iso_comp]

    set g := _; change CategoryTheory.Exact _ g
    dsimp at g
    suffices g_eq : g = (horseshoeD A n).τ₁ ≫ eqToHom (by simp) by
      rw [g_eq, exact_comp_iso]
      exact this
    simp only [g]
    generalize_proofs h1 h2
    rw [show (eqToHom h1).τ₁ = eqToHom (by simp) from stupid_aux _ _ (by simp), stupid_aux2']
    simp

  suffices HomologicalComplex.homologyMap (horseshoeToSingle₁ A) (n + 1) = (z2.iso z1).hom by
    rw [this]
    exact IsIso.of_iso _
  exact IsZero.eq_of_tgt z1 _ _

instance (n : ℕ) : QuasiIsoAt (horseshoeToSingle₂ A) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have z1 : IsZero <| ((ChainComplex.single₀ _).obj A.X₂).homology (n + 1) := by
    apply HomologicalComplex.isZero_single_obj_homology
    simp

  have z2 : IsZero <| HomologicalComplex.homology (horseshoeChainComplex₂ A) (n + 1) := by
    suffices e : HomologicalComplex.homology (horseshoeChainComplex₂ A) (n + 1) ≅ 0 from
      e.isZero_iff.mpr (isZero_zero _)

    refine exact_iff_homology_iso_zero _ |>.mp ?_ |>.some
    rw [← exact_iff_shortComplex_exact]
    have := horseshoeExact₂ A n
    simp only [Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₂_obj,
      Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, Category.id_comp, dite_eq_ite,
      π₂_map, ↓reduceDite] at this
    rw [if_pos (by abel)] at this

    simp only [HomologicalComplex.shortComplexFunctor_obj_X₁, Functor.mapHomologicalComplex_obj_X,
      horseshoe_X, π₂_obj, HomologicalComplex.shortComplexFunctor_obj_X₂,
      HomologicalComplex.shortComplexFunctor_obj_X₃, HomologicalComplex.shortComplexFunctor_obj_f,
      Functor.mapHomologicalComplex_obj_d, horseshoe_d, ChainComplex.prev, ↓reduceDite, π₂_map,
      comp_τ₂, HomologicalComplex.shortComplexFunctor_obj_g, ChainComplex.next_nat_succ,
      exact_iso_comp]

    set g := _; change CategoryTheory.Exact _ g
    dsimp at g
    suffices g_eq : g = (horseshoeD A n).τ₂ ≫ eqToHom (by simp) by
      rw [g_eq, exact_comp_iso]
      exact this
    simp only [g]
    generalize_proofs h1 h2
    rw [show (eqToHom h1).τ₂ = eqToHom (by simp) from stupid_aux' _ _ (by simp), stupid_aux2'']
    simp

  suffices HomologicalComplex.homologyMap (horseshoeToSingle₂ A) (n + 1) = (z2.iso z1).hom by
    rw [this]
    exact IsIso.of_iso _
  exact IsZero.eq_of_tgt z1 _ _

instance (n : ℕ) : QuasiIsoAt (horseshoeToSingle₃ A) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have z1 : IsZero <| ((ChainComplex.single₀ _).obj A.X₃).homology (n + 1) := by
    apply HomologicalComplex.isZero_single_obj_homology
    simp

  have z2 : IsZero <| HomologicalComplex.homology (horseshoeChainComplex₃ A) (n + 1) := by
    suffices e : HomologicalComplex.homology (horseshoeChainComplex₃ A) (n + 1) ≅ 0 from
      e.isZero_iff.mpr (isZero_zero _)

    refine exact_iff_homology_iso_zero _ |>.mp ?_ |>.some
    rw [← exact_iff_shortComplex_exact]
    have := horseshoeExact₃ A n
    simp only [Functor.mapHomologicalComplex_obj_X, horseshoe_X, π₂_obj,
      Functor.mapHomologicalComplex_obj_d, horseshoe_d, eqToHom_refl, Category.id_comp, dite_eq_ite,
      π₂_map, ↓reduceDite] at this
    rw [if_pos (by abel)] at this

    simp only [HomologicalComplex.shortComplexFunctor_obj_X₁, Functor.mapHomologicalComplex_obj_X,
      horseshoe_X, π₃_obj, HomologicalComplex.shortComplexFunctor_obj_X₂,
      HomologicalComplex.shortComplexFunctor_obj_X₃, HomologicalComplex.shortComplexFunctor_obj_f,
      Functor.mapHomologicalComplex_obj_d, horseshoe_d, ChainComplex.prev, ↓reduceDite, π₃_map,
      comp_τ₃, HomologicalComplex.shortComplexFunctor_obj_g, ChainComplex.next_nat_succ,
      exact_iso_comp]

    set g := _; change CategoryTheory.Exact _ g
    dsimp at g
    suffices g_eq : g = (horseshoeD A n).τ₃ ≫ eqToHom (by simp) by
      rw [g_eq, exact_comp_iso]
      exact this
    simp only [g]
    generalize_proofs h1 h2
    rw [show (eqToHom h1).τ₃ = eqToHom (by simp) from stupid_aux'' _ _ (by simp), stupid_aux2''']
    simp

  suffices HomologicalComplex.homologyMap (horseshoeToSingle₃ A) (n + 1) = (z2.iso z1).hom by
    rw [this]
    exact IsIso.of_iso _
  exact IsZero.eq_of_tgt z1 _ _

instance : _root_.QuasiIso (horseshoeToSingle₁ A) where
  quasiIsoAt n := by
    cases n <;> infer_instance

instance : _root_.QuasiIso (horseshoeToSingle₂ A) where
  quasiIsoAt n := by
    cases n <;> infer_instance

instance : _root_.QuasiIso (horseshoeToSingle₃ A) where
  quasiIsoAt n := by
    cases n <;> infer_instance

/--
the first column is a projective resolution
-/
def horseshoeProjectiveResolution₁ : ProjectiveResolution A.X₁ where
  complex := horseshoeChainComplex₁ A
  π := horseshoeToSingle₁ A

/--
the second column is a projective resolution
-/
def horseshoeProjectiveResolution₂ : ProjectiveResolution A.X₂ where
  complex := horseshoeChainComplex₂ A
  π := horseshoeToSingle₂ A

/--
the third column is a projective resolution
-/
def horseshoeProjectiveResolution₃ : ProjectiveResolution A.X₃ where
  complex := horseshoeChainComplex₃ A
  π := horseshoeToSingle₃ A

/--
each row splits
-/
def horseshoe_splitting (n : ℕ) : ((horseshoe A).X n).Splitting :=
match n with
| 0 =>
{ r := biprod.fst
  s := biprod.inr
  f_r := by simp [horseshoeObj, horseshoeStep]
  s_g := by simp [horseshoeObj, horseshoeStep]
  id := by simp [horseshoeObj, horseshoeStep] }
| n + 1 =>
{ r := biprod.fst
  s := biprod.inr
  f_r := by simp [horseshoeObj, horseshoeStep]
  s_g := by simp [horseshoeObj, horseshoeStep]
  id := by simp [horseshoeObj, horseshoeStep] }

lemma horseshoe_g_comp_toSingle₃_f_commute (n : ℕ) :
    ((horseshoe A).X n).g ≫ (horseshoeToSingle₃ A).f n =
    (horseshoeToSingle₂ A).f n ≫ ((ChainComplex.single₀ _).map A.g).f n := by
  rcases n with (_|n)
  · simp only [Nat.zero_eq, horseshoe_X, horseshoeObj, horseshoeStep, horseshoeBase_X₂,
    ChainComplex.single₀_obj_zero, horseshoeBase_X₃, horseshoeBase_g,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero, π₃_map, horseshoeBaseπ_τ₃,
    Functor.mapHomologicalComplex_obj_X, π₂_obj, π₂_map, horseshoeBaseπ_τ₂,
    ChainComplex.single₀_map_f_zero]
    aesop_cat
  · simp only [horseshoe_X, horseshoeObj, horseshoeStep, horseshoeBase_X₂, horseshoeBase_X₃,
    horseshoeBase_g, horseshoeToSingle₃, Functor.mapHomologicalComplex_obj_X, π₃_obj,
    horseshoeKer_X₃, horseshoeBaseπ_τ₃, Functor.mapHomologicalComplex_obj_d, horseshoe_d,
    eqToHom_refl, dite_eq_ite, π₃_map, ChainComplex.toSingle₀Equiv,
    HomologicalComplex.mkHomToSingle, Equiv.coe_fn_symm_mk, Nat.succ_ne_zero, ↓reduceDite,
    comp_zero, π₂_obj, horseshoeToSingle₂, horseshoeKer_X₁, horseshoeBase_X₁, horseshoeBaseπ_τ₁,
    π₂_map, horseshoeBaseπ_τ₂, zero_comp]

end CategoryTheory.ShortComplex

end
