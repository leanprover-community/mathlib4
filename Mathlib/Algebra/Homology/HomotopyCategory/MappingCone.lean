/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCofiber

/-! # The mapping cone of a morphism of cochain complexes

In this file, we study the homotopy cofiber `HomologicalComplex.homotopyCofiber`
of a morphism `φ : F ⟶ G` of cochain complexes indexed by `ℤ`. In this case,
we redefine it as `CochainComplex.mappingCone φ`. The API involves definitions
- `mappingCone.inl φ : Cochain F (mappingCone φ) (-1)`,
- `mappingCone.inr φ : G ⟶ mappingCone φ`,
- `mappingCone.fst φ : Cocycle (mappingCone φ) F 1` and
- `mappingCone.snd φ : Cochain (mappingCone φ) G 0`.

-/

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

section

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    {F G : CochainComplex C ι} (φ : F ⟶ G)

instance [∀ p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
    HasHomotopyCofiber φ where
  hasBinaryBiproduct := by
    rintro i _ rfl
    infer_instance

end

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)
variable [HasHomotopyCofiber φ]

/-- The mapping cone of a morphism of cochain complexes indexed by `ℤ`. -/
noncomputable def mappingCone := homotopyCofiber φ

namespace mappingCone

open HomComplex

/-- The left inclusion in the mapping cone, as a cochain of degree `-1`. -/
noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q  (by dsimp; omega))

/-- The right inclusion in the mapping cone. -/
noncomputable def inr : G ⟶ mappingCone φ := homotopyCofiber.inr φ

/-- The first projection from the mapping cone, as a cocyle of degree `1`. -/
noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by omega) (by
    ext p _ rfl
    simp [δ_v 1 2 (by omega) _ p (p + 2) (by omega) (p + 1) (p + 1) (by omega) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

/-- The second projection from the mapping cone, as a cochain of degree `0`. -/
noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.ofHoms (homotopyCofiber.sndX φ)

@[reassoc (attr := simp)]
lemma inl_v_fst_v (p q : ℤ) (hpq : q + 1 = p) :
    (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  simp [inl, fst]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  simp [inl, snd]

@[reassoc (attr := simp)]
lemma inr_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).f p ≫ (fst φ).1.v p q hpq = 0 := by
  simp [inr, fst]

@[reassoc (attr := simp)]
lemma inr_f_snd_v (p : ℤ) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
lemma inl_fst :
    (inl φ).comp (fst φ).1 (neg_add_self 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_self 1) p (p-1) p rfl (by omega)]

@[simp]
lemma inl_snd :
    (inl φ).comp (snd φ) (add_zero (-1)) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (add_zero (-1)) p q q (by omega) (by omega)]

@[simp]
lemma inr_fst :
    (Cochain.ofHom (inr φ)).comp (fst φ).1 (zero_add 1) = 0 := by
  ext p q hpq
  simp [Cochain.comp_v _ _ (zero_add 1) p p q (by omega) (by omega)]

@[simp]
lemma inr_snd :
    (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by aesop_cat

/-! In order to obtain identities of cochains involving `inl`, `inr`, `fst` and `snd`,
it is often convenient to use an `ext` lemma, and use simp lemmas like `inl_v_f_fst_v`,
but it is sometimes possible to get identities of cochains by using rewrites of
identities of cochains like `inl_fst`. Then, similarly as in category theory,
if we associate the compositions of cochains to the right as much as possible,
it is also interesting to have `reassoc` variants of lemmas, like `inl_fst_assoc`. -/

@[simp]
lemma inl_fst_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ).comp ((fst φ).1.comp γ he) (by rw [← he, neg_add_cancel_left]) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_self 1) (by omega) (by omega), inl_fst,
    Cochain.id_comp]

@[simp]
lemma inl_snd_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain G K d)
    (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ).comp ((snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by omega
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, inl_snd, Cochain.zero_comp]

@[simp]
lemma inr_fst_assoc {K : CochainComplex C ℤ} {d e f : ℤ} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)).comp ((fst φ).1.comp γ he) hf = 0 := by
  obtain rfl : e = f := by omega
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_fst, Cochain.zero_comp]

@[simp]
lemma inr_snd_assoc {K : CochainComplex C ℤ} {d e : ℤ} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ he) (by simp only [← he, zero_add]) = γ := by
  obtain rfl : d = e := by omega
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, inr_snd, Cochain.id_comp]

lemma ext_to (i j : ℤ) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
    (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij)
    (h₂ : f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)) :
    f = g :=
  homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using h₂)

lemma ext_to_iff (i j : ℤ) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) :
    f = g ↔ f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij ∧
      f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

lemma ext_from (i j : ℤ) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
    (h₁ : (inl φ).v i j (by omega) ≫ f = (inl φ).v i j (by omega) ≫ g)
    (h₂ : (inr φ).f j ≫ f = (inr φ).f j ≫ g) :
    f = g :=
  homotopyCofiber.ext_from_X φ i j hij h₁ h₂

lemma ext_from_iff (i j : ℤ) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) :
    f = g ↔ (inl φ).v i j (by omega) ≫ f = (inl φ).v i j (by omega) ≫ g ∧
      (inr φ).f j ≫ f = (inr φ).f j ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

lemma ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain K (mappingCone φ) i} :
    γ₁ = γ₂ ↔ γ₁.comp (fst φ).1 hij = γ₂.comp (fst φ).1 hij ∧
      γ₁.comp (snd φ) (add_zero i) = γ₂.comp (snd φ) (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by omega)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain.comp_zero_cochain_v] at h₂
    exact ⟨h₁, h₂⟩

lemma ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain (mappingCone φ) K j} :
    γ₁ = γ₂ ↔
      (inl φ).comp γ₁ (show _ = i by omega) = (inl φ).comp γ₂ (by omega) ∧
        (Cochain.ofHom (inr φ)).comp γ₁ (zero_add j) =
          (Cochain.ofHom (inr φ)).comp γ₂ (zero_add j) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by omega)
    replace h₂ := Cochain.congr_v h₂ p q (by omega)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by omega) hpq] at h₁
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h₂
    exact ⟨h₁, h₂⟩

lemma id :
    (fst φ).1.comp (inl φ) (add_neg_self 1) +
      (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _) := by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_self 1)]

lemma id_X (p q : ℤ) (hpq : p + 1 = q) :
    (fst φ).1.v p q hpq ≫ (inl φ).v q p (by omega) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p = 𝟙 ((mappingCone φ).X p) := by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_self 1) p q p hpq (by omega)]
    using Cochain.congr_v (id φ) p p (add_zero p)

@[reassoc]
lemma inl_v_d (i j k : ℤ) (hij : i + (-1) = j) (hik : k + (-1) = i) :
    (inl φ).v i j hij ≫ (mappingCone φ).d j i =
      φ.f i ≫ (inr φ).f i - F.d i k ≫ (inl φ).v _ _ hik := by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; omega) (by dsimp; omega)]
  abel

@[reassoc (attr := simp 1100)]
lemma inr_f_d (n₁ n₂ : ℤ) :
    (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (inr φ).f n₂ := by
  apply Hom.comm

@[reassoc]
lemma d_fst_v (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone φ).d i j ≫ (fst φ).1.v j k hjk =
      -(fst φ).1.v i j hij ≫ F.d j k := by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]
lemma d_fst_v' (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d (i - 1) i ≫ (fst φ).1.v i j hij =
      -(fst φ).1.v (i - 1) i (by omega) ≫ F.d i j :=
  d_fst_v φ (i - 1) i j (by omega) hij

@[reassoc]
lemma d_snd_v (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) =
      (fst φ).1.v i j hij ≫ φ.f j + (snd φ).v i i (add_zero i) ≫ G.d i j := by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]
lemma d_snd_v' (n : ℤ) :
    (mappingCone φ).d (n - 1) n ≫ (snd φ).v n n (add_zero n) =
    (fst φ : Cochain (mappingCone φ) F 1).v (n - 1) n (by omega) ≫ φ.f n +
      (snd φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n := by
  apply d_snd_v

@[simp]
lemma δ_inl :
    δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  ext p
  simp [δ_v (-1) 0 (neg_add_self 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by omega) (by omega)]

@[simp]
lemma δ_snd :
    δ 0 1 (snd φ) = -(fst φ).1.comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

section

variable {K : CochainComplex C ℤ} {n m : ℤ} (α : Cochain F K m)
    (β : Cochain G K n) (h : m + 1 = n)

/-- Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Cochain F K n`. -/
noncomputable def descCochain : Cochain (mappingCone φ) K n :=
  (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

@[simp]
lemma inl_descCochain :
    (inl φ).comp (descCochain φ α β h) (by omega) = α := by
  simp [descCochain]

@[simp]
lemma inr_descCochain :
    (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β := by
  simp [descCochain]

@[reassoc (attr := simp)]
lemma inl_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) :
    (inl φ).v p₁ p₂ h₁₂ ≫ (descCochain φ α β h).v p₂ p₃ h₂₃ =
        α.v p₁ p₃ (by rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left]) := by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by omega) p₁ p₂ p₃
    (by omega) (by omega)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by omega)

@[reassoc (attr := simp)]
lemma inr_f_descCochain_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by omega)

lemma δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (descCochain φ α β h) =
      (fst φ).1.comp (δ m n α +
          n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (by omega) +
      (snd φ).comp (δ n n' β) (zero_add n') := by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (fst φ).1 α _ 2 n n' hn' (by omega) (by omega),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_units_smul, ← hn',
    Int.negOnePow_succ, Units.neg_smul, Cochain.comp_neg]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle (mappingCone φ) K n` that is
constructed from `α : Cochain F K m` (with `m + 1 = n`) and `β : Cocycle F K n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
noncomputable def descCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain F K m) (β : Cocycle G K n)
    (h : m + 1 = n) (eq : δ m n α = n.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n)) :
    Cocycle (mappingCone φ) K n :=
  Cocycle.mk (descCochain φ α β.1 h) (n + 1) rfl
    (by simp [δ_descCochain _ _ _ _ _ rfl, eq, Int.negOnePow_succ])

section

variable {K : CochainComplex C ℤ} (α : Cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

/-- Given `φ : F ⟶ G`, this is the morphism `mappingCone φ ⟶ K` that is constructed
from a cochain `α : Cochain F K (-1)` and a morphism `β : G ⟶ K` such that
`δ (-1) 0 α = Cochain.ofHom (φ ≫ β)`. -/
noncomputable def desc : mappingCone φ ⟶ K :=
  Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_self 1) (by simp [eq]))

@[simp]
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β eq) = descCochain φ α (Cochain.ofHom β) (neg_add_self 1) := by
  simp [desc]

@[reassoc (attr := simp)]
lemma inl_v_desc_f (p q : ℤ) (h : p + (-1) = q) :
    (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h := by
  simp [desc]

lemma inl_desc :
    (inl φ).comp (Cochain.ofHom (desc φ α β eq)) (add_zero _) = α := by
  simp

@[reassoc (attr := simp)]
lemma inr_f_desc_f (p : ℤ) :
    (inr φ).f p ≫ (desc φ α β eq).f p = β.f p := by
  simp [desc]

@[reassoc (attr := simp)]
lemma inr_desc : inr φ ≫ desc φ α β eq = β := by aesop_cat

lemma desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (desc φ α β eq).f p = (fst φ).1.v p q hpq ≫ α.v q p (by omega) +
      (snd φ).v p p (add_zero p) ≫ β.f p := by
  simp [ext_from_iff _ _ _ hpq]

end

/-- Constructor for homotopies between morphisms from a mapping cone. -/
noncomputable def descHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : mappingCone φ ⟶ K)
    (γ₁ : Cochain F K (-2)) (γ₂ : Cochain G K (-1))
    (h₁ : (inl φ).comp (Cochain.ofHom f₁) (add_zero (-1))  =
      δ (-2) (-1) γ₁ + (Cochain.ofHom φ).comp γ₂ (zero_add (-1)) +
      (inl φ).comp (Cochain.ofHom f₂) (add_zero (-1)))
    (h₂ : Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨descCochain φ γ₁ γ₂ (by norm_num), by
    simp only [Cochain.ofHom_comp] at h₂
    simp [ext_cochain_from_iff _ _ _ (neg_add_self 1),
      δ_descCochain _ _ _ _ _ (neg_add_self 1), h₁, h₂]⟩

section

variable {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

/-- Given `φ : F ⟶ G`, this is the cochain in `Cochain (mappingCone φ) K n` that is
constructed from two cochains `α : Cochain F K m` (with `m + 1 = n`) and `β : Cochain F K n`. -/
noncomputable def liftCochain : Cochain K (mappingCone φ) n :=
  α.comp (inl φ) (by omega) + β.comp (Cochain.ofHom (inr φ)) (add_zero n)

@[simp]
lemma liftCochain_fst :
    (liftCochain φ α β h).comp (fst φ).1 h = α := by
  simp [liftCochain]

@[simp]
lemma liftCochain_snd :
    (liftCochain φ α β h).comp (snd φ) (add_zero n) = β := by
  simp [liftCochain]

@[reassoc (attr := simp)]
lemma liftCochain_v_fst_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α.v p₁ p₃ (by omega) := by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by omega)

@[reassoc (attr := simp)]
lemma liftCochain_v_snd_v (p₁ p₂ : ℤ) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by omega)

lemma δ_liftCochain (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (liftCochain φ α β h) = -(δ m m' α).comp (inl φ) (by omega) +
      (δ n m β + α.comp (Cochain.ofHom φ) (add_zero m)).comp
        (Cochain.ofHom (inr φ)) (add_zero m) := by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp α (inl φ) _ m' _ _ h hm' (neg_add_self 1),
    δ_comp_zero_cochain _ _ _ h, δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle K (mappingCone φ) n` that is
constructed from `α : Cochain K F m` (with `n + 1 = m`) and `β : Cocycle K G n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
noncomputable def liftCocycle {K : CochainComplex C ℤ} {n m : ℤ}
    (α : Cocycle K F m) (β : Cochain K G n) (h : n + 1 = m)
    (eq : δ n m β + α.1.comp (Cochain.ofHom φ) (add_zero m) = 0) :
    Cocycle K (mappingCone φ) n :=
  Cocycle.mk (liftCochain φ α β h) m h (by
    simp only [δ_liftCochain φ α β h (m+1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

section

variable {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

/-- Given `φ : F ⟶ G`, this is the morphism `K ⟶ mappingCone φ` that is constructed
from a cocycle `α : Cochain K F 1` and a cochain `β : Cochain K G 0`
when a suitable cocycle relation is satisfied. -/
noncomputable def lift :
    K ⟶ mappingCone φ :=
  Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1) := by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

@[reassoc (attr := simp)]
lemma lift_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p ≫ (fst φ).1.v p q hpq = α.1.v p q hpq := by
  simp [lift]

lemma lift_fst :
    (Cochain.ofHom (lift φ α β eq)).comp (fst φ).1 (zero_add 1) = α.1 := by simp

@[reassoc (attr := simp)]
lemma lift_f_snd_v (p q : ℤ) (hpq : p + 0 = q) :
    (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : q = p := by omega
  simp [lift]

lemma lift_snd :
    (Cochain.ofHom (lift φ α β eq)).comp (snd φ) (zero_add 0) = β := by simp

lemma lift_f (p q : ℤ) (hpq : p + 1 = q) :
    (lift φ α β eq).f p = α.1.v p q hpq ≫
      (inl φ).v q p (by omega) + β.v p p (add_zero p) ≫ (inr φ).f p := by
  simp [ext_to_iff _ _ _ hpq]

end

/-- Constructor for homotopies between morphisms to a mapping cone. -/
noncomputable def liftHomotopy {K : CochainComplex C ℤ} (f₁ f₂ : K ⟶ mappingCone φ)
    (α : Cochain K F 0) (β : Cochain K G (-1))
    (h₁ : (Cochain.ofHom f₁).comp (fst φ).1 (zero_add 1) =
      -δ 0 1 α + (Cochain.ofHom f₂).comp (fst φ).1 (zero_add 1))
    (h₂ : (Cochain.ofHom f₁).comp (snd φ) (zero_add 0) =
      δ (-1) 0 β + α.comp (Cochain.ofHom φ) (zero_add 0) +
        (Cochain.ofHom f₂).comp (snd φ) (zero_add 0)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_self 1), by
    simp [δ_liftCochain _ _ _ _ _ (zero_add 1), ext_cochain_to_iff _ _ _ (zero_add 1), h₁, h₂]⟩

section

variable {K L : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K F m) (β : Cochain K G n) {n' m' : ℤ} (α' : Cochain F L m') (β' : Cochain G L n')
  (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ) (hp : n + n' = p)

@[simp]
lemma liftCochain_descCochain :
    (liftCochain φ α β h).comp (descCochain φ α' β' h') hp =
      α.comp α' (by omega) + β.comp β' (by omega) := by
  simp [liftCochain, descCochain,
    Cochain.comp_assoc α (inl φ) _ _ (show -1 + n' = m' by omega) (by linarith)]

lemma liftCochain_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
    (q : ℤ) (hq : p₁ + m = q) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (descCochain φ α' β' h').v p₂ p₃ h₂₃ =
      α.v p₁ q hq ≫ α'.v q p₃ (by omega) + β.v p₁ p₂ h₁₂ ≫ β'.v p₂ p₃ h₂₃ := by
  have eq := Cochain.congr_v (liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by omega)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by omega)] using eq

end

lemma lift_desc_f {K L : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : ℤ) (hnn' : n + 1 = n') :
    (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n =
    α.1.v n n' hnn' ≫ α'.v n' n (by omega) + β.v n n (add_zero n) ≫ β'.f n := by
  simp only [lift, desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_self 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]

end mappingCone

end CochainComplex
