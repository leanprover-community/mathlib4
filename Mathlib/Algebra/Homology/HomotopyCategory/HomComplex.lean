/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The cochain complex of homomorphisms between cochain complexes

If `F` and `G` are cochain complexes (indexed by `ℤ`) in a preadditive category,
there is a cochain complex of abelian groups whose `0`-cocycles identify to
morphisms `F ⟶ G`. Informally, in degree `n`, this complex shall consist of
cochains of degree `n` from `F` to `G`, i.e. arbitrary families for morphisms
`F.X p ⟶ G.X (p + n)`. This complex shall be denoted `HomComplex F G`.

In order to avoid type theoretic issues, a cochain of degree `n : ℤ`
(i.e. a term of type of `Cochain F G n`) shall be defined here
as the data of a morphism `F.X p ⟶ G.X q` for all triplets
`⟨p, q, hpq⟩` where `p` and `q` are integers and `hpq : p + n = q`.
If `α : Cochain F G n`, we shall define `α.v p q hpq : F.X p ⟶ G.X q`.

We follow the signs conventions appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

TODO:
* Define the differential `Cochain F G n ⟶ Cochain F G m`, and develop the API.
* Identify morphisms of complexes to `0`-cocycles.
* Identify homotopies to `-1`-cochains satisfying certain relations.
* Behaviour with respect to shifting the cochain complexes `F` and `G`.

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

variable {F G K L M : CochainComplex C ℤ} (n m : ℤ)

namespace HomComplex

/-- A term of type `HomComplex.Triplet n` consists of two integers `p` and `q`
such that `p + n = q`. (This type is introduced so that the instance
`AddCommGroup (Cochain F G n)` defined below can be found automatically.) -/
structure Triplet (n : ℤ) where
  /-- a first integer -/
  p : ℤ
  /-- a second integer -/
  q : ℤ
  /-- the condition on the two integers -/
  hpq : p + n = q

variable (F G)

/-- A cochain of degree `n : ℤ` between to cochain complexes `F` and `G` consists
of a family of morphisms `F.X p ⟶ G.X q` whenever `p + n = q`, i.e. for all
triplets in `HomComplex.Triplet n`. -/
def Cochain := ∀ (T : Triplet n), F.X T.p ⟶ G.X T.q

instance : AddCommGroup (Cochain F G n) := by
  dsimp only [Cochain]
  infer_instance

namespace Cochain

variable {F G n}

/-- A practical constructor for cochains. -/
def mk (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) : Cochain F G n :=
  fun ⟨p, q, hpq⟩ => v p q hpq

/-- The value of a cochain on a triplet `⟨p, q, hpq⟩`. -/
@[pp_dot]
def v (γ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    F.X p ⟶ G.X q := γ ⟨p, q, hpq⟩

@[simp]
lemma mk_v (v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) (p q : ℤ) (hpq : p + n = q) :
    (Cochain.mk v).v p q hpq = v p q hpq := rfl

lemma congr_v {z₁ z₂ : Cochain F G n} (h : z₁ = z₂) (p q : ℤ) (hpq : p + n = q) :
    z₁.v p q hpq = z₂.v p q hpq := by subst h; rfl

@[ext]
lemma ext (z₁ z₂ : Cochain F G n)
    (h : ∀ (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂ := by
  funext ⟨p, q, hpq⟩
  apply h

@[ext 1100]
lemma ext₀ (z₁ z₂ : Cochain F G 0)
    (h : ∀ (p : ℤ), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂ := by
  ext p q hpq
  obtain rfl : q = p := by rw [← hpq, add_zero]
  exact h q

@[simp]
lemma zero_v {n : ℤ} (p q : ℤ) (hpq : p + n = q) :
    (0 : Cochain F G n).v p q hpq = 0 := rfl

@[simp]
lemma add_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁ + z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq := rfl

@[simp]
lemma sub_v {n : ℤ} (z₁ z₂ : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (z₁ - z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq := rfl

@[simp]
lemma neg_v {n : ℤ} (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (-z).v p q hpq = - (z.v p q hpq) := rfl

@[simp]
lemma zsmul_v {n k : ℤ} (z : Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (k • z).v p q hpq = k • (z.v p q hpq) := rfl

/-- A cochain of degree `0` from `F` to `G` can be constructed from a family
of morphisms `F.X p ⟶ G.X p` for all `p : ℤ`. -/
def ofHoms (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) : Cochain F G 0 :=
  Cochain.mk (fun p q hpq => ψ p ≫ eqToHom (by rw [← hpq, add_zero]))

@[simp]
lemma ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
    (ofHoms ψ).v p p (add_zero p) = ψ p := by
  simp only [ofHoms, mk_v, eqToHom_refl, comp_id]

@[simp]
lemma ofHoms_zero : ofHoms (fun p => (0 : F.X p ⟶ G.X p)) = 0 := by aesop_cat

@[simp]
lemma ofHoms_v_comp_d (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHoms ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q' := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

@[simp]
lemma d_comp_ofHoms_v (ψ : ∀ (p : ℤ), F.X p ⟶ G.X p) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHoms ψ).v p q hpq = F.d p' q ≫ ψ q := by
  rw [add_zero] at hpq
  subst hpq
  rw [ofHoms_v]

/-- The `0`-cochain attached to a morphism of cochain complexes. -/
def ofHom (φ : F ⟶ G) : Cochain F G 0 := ofHoms (fun p => φ.f p)

variable (F G)

@[simp]
lemma ofHom_zero : ofHom (0 : F ⟶ G) = 0 := by
  simp only [ofHom, HomologicalComplex.zero_f_apply, ofHoms_zero]

variable {F G}

@[simp]
lemma ofHom_v (φ : F ⟶ G) (p : ℤ) : (ofHom φ).v p p (add_zero p) = φ.f p := by
  simp only [ofHom, ofHoms_v]

@[simp]
lemma ofHom_v_comp_d (φ : F ⟶ G) (p q q' : ℤ) (hpq : p + 0 = q) :
    (ofHom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' :=
by simp only [ofHom, ofHoms_v_comp_d]

@[simp]
lemma d_comp_ofHom_v (φ : F ⟶ G) (p' p q : ℤ) (hpq : p + 0 = q) :
    F.d p' p ≫ (ofHom φ).v p q hpq = F.d p' q ≫ φ.f q := by
  simp only [ofHom, d_comp_ofHoms_v]

@[simp]
lemma ofHom_add (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ + φ₂) = Cochain.ofHom φ₁ + Cochain.ofHom φ₂ := by aesop_cat

@[simp]
lemma ofHom_sub (φ₁ φ₂ : F ⟶ G) :
    Cochain.ofHom (φ₁ - φ₂) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by aesop_cat

@[simp]
lemma ofHom_neg (φ : F ⟶ G) :
    Cochain.ofHom (-φ) = -Cochain.ofHom φ := by aesop_cat

/-- The cochain of degree `-1` given by an homotopy between two morphism of complexes. -/
def ofHomotopy {φ₁ φ₂ : F ⟶ G} (ho : Homotopy φ₁ φ₂) : Cochain F G (-1) :=
  Cochain.mk (fun p q _ => ho.hom p q)

@[simp]
lemma ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    ofHomotopy (Homotopy.ofEq h) = 0 := rfl

@[simp]
lemma ofHomotopy_refl (φ : F ⟶ G) :
    ofHomotopy (Homotopy.refl φ) = 0 := rfl

@[reassoc]
lemma v_comp_XIsoOfEq_hom
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

@[reassoc]
lemma v_comp_XIsoOfEq_inv
    (γ : Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q' = q) :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').inv = γ.v p q' (by rw [hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, comp_id]

@[reassoc]
lemma XIsoOfEq_hom_comp_v
    (γ : Cochain F G n) (p p' q : ℤ) (hpq' : p' + n = q) (hp' : p = p') :
    (HomologicalComplex.XIsoOfEq F hp').hom ≫ γ.v p' q hpq' = γ.v p q (by rw [hp', hpq']) := by
  subst hp'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp]

@[reassoc]
lemma XIsoOfEq_inv_comp_v
    (γ : Cochain F G n) (p p' q : ℤ) (hpq' : p' + n = q) (hp' : p' = p) :
    (HomologicalComplex.XIsoOfEq F hp').inv ≫ γ.v p' q hpq' = γ.v p q (by rw [← hp', hpq']) := by
  subst hp'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, id_comp]

/-- The composition of cochains. -/
@[pp_dot]
def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
    Cochain F K n₁₂ :=
  Cochain.mk (fun p q hpq => z₁.v p (p + n₁) rfl ≫ z₂.v (p + n₁) q (by linarith))

/-! If `z₁` is a cochain of degree `n₁` and `z₂` is a cochain of degree `n₂`, and that
we have a relation `h : n₁ + n₂ = n₁₂`, then `z₁.comp z₂ h` is a cochain of degree `n₁₂`.
The following lemma `comp_v` computes the value of this composition `z₁.comp z₂ h`
on a triplet `⟨p₁, p₃, _⟩` (with `p₁ + n₁₂ = p₃`). In order to use this lemma,
we need to provide an intermediate integer `p₂` such that `p₁ + n₁ = p₂`.
It is advisable to use a `p₂` that has good definitional properties
(i.e. `p₁ + n₁` is not always the best choice.)

When `z₁` or `z₂` is a `0`-cochain, there is a better choice of `p₂`, and this leads
to the two simplification lemmas `comp_zero_cochain_v` and `zero_cochain_comp_v`.

-/

lemma comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (p₁ p₂ p₃ : ℤ) (h₁ : p₁ + n₁ = p₂) (h₂ : p₂ + n₂ = p₃) :
    (z₁.comp z₂ h).v p₁ p₃ (by rw [← h₂, ← h₁, ← h, add_assoc]) =
      z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by
  subst h₁; rfl

@[simp]
lemma comp_zero_cochain_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (add_zero n)).v p q hpq = z₁.v p q hpq ≫ z₂.v q q (add_zero q) :=
  comp_v z₁ z₂ (add_zero n) p q q hpq (add_zero q)

@[simp]
lemma zero_cochain_comp_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : ℤ) (hpq : p + n = q) :
    (z₁.comp z₂ (zero_add n)).v p q hpq = z₁.v p p (add_zero p) ≫ z₂.v p q hpq :=
  comp_v z₁ z₂ (zero_add n) p p q (add_zero p) hpq

/-- The associativity of the composition of cochains. -/
lemma comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    (z₁.comp z₂ h₁₂).comp z₃ (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      z₁.comp (z₂.comp z₃ h₂₃) (by rw [← h₂₃, ← h₁₂₃, add_assoc]) := by
  substs h₁₂ h₂₃ h₁₂₃
  ext p q hpq
  rw [comp_v _ _ rfl p (p + n₁ + n₂) q (by linarith) (by linarith),
    comp_v z₁ z₂ rfl p (p + n₁) (p + n₁ + n₂) (by linarith) (by linarith),
    comp_v z₁ (z₂.comp z₃ rfl) (add_assoc n₁ n₂ n₃).symm p (p + n₁) q (by linarith) (by linarith),
    comp_v z₂ z₃ rfl (p + n₁) (p + n₁ + n₂) q (by linarith) (by linarith), assoc]

/-! The formulation of the associativity of the composition of cochains given by the
lemma `comp_assoc` often requires a careful selection of degrees with good definitional
properties. In a few cases, like when one of the three cochains is a `0`-cochain,
there are better choices, which provides the following simplification lemmas. -/

@[simp]
lemma comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : ℤ}
    (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂) (z₃ : Cochain K L n₃)
    (h₂₃ : n₂ + n₃ = n₂₃) :
    (z₁.comp z₂ (zero_add n₂)).comp z₃ h₂₃ = z₁.comp (z₂.comp z₃ h₂₃) (zero_add n₂₃) :=
  comp_assoc _ _ _ _ _ (by linarith)

@[simp]
lemma comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0) (z₃ : Cochain K L n₃) (h₁₃ : n₁ + n₃ = n₁₃) :
    (z₁.comp z₂ (add_zero n₁)).comp z₃ h₁₃ = z₁.comp (z₂.comp z₃ (zero_add n₃)) h₁₃ :=
  comp_assoc _ _ _ _ _ (by linarith)

@[simp]
lemma comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L 0) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃ (add_zero n₁₂) = z₁.comp (z₂.comp z₃ (add_zero n₂)) h₁₂ :=
  comp_assoc _ _ _ _ _ (by linarith)

@[simp]
lemma comp_assoc_of_second_degree_eq_neg_third_degree {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K (-n₂)) (z₃ : Cochain K L n₂) (h₁₂ : n₁ + (-n₂) = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + n₂ = n₁ by rw [← h₁₂, add_assoc, neg_add_self, add_zero]) =
      z₁.comp (z₂.comp z₃ (neg_add_self n₂)) (add_zero n₁) :=
  comp_assoc _ _ _ _ _ (by linarith)

@[simp]
lemma comp_assoc_of_third_degree_eq_neg_second_degree {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (z₃ : Cochain K L (-n₂)) (h₁₂ : n₁ + n₂ = n₁₂) :
    (z₁.comp z₂ h₁₂).comp z₃
      (show n₁₂ + (-n₂) = n₁ by rw [← h₁₂, add_neg_cancel_right]) =
      z₁.comp (z₂.comp z₃ (add_neg_self n₂)) (add_zero n₁) :=
  comp_assoc _ _ _ _ _ (by linarith)

@[simp]
protected lemma zero_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (0 : Cochain F G n₁).comp z₂ h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), zero_v, zero_comp]

@[simp]
protected lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ + z₁').comp z₂ h = z₁.comp z₂ h + z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), add_v, add_comp]

@[simp]
protected lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (z₁ - z₁').comp z₂ h = z₁.comp z₂ h - z₁'.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), sub_v, sub_comp]

@[simp]
protected lemma neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₁).comp z₂ h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), neg_v, neg_comp]

@[simp]
protected lemma zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : (k • z₁).comp z₂ h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), zsmul_v, zsmul_comp]

@[simp]
protected lemma id_comp {n : ℤ} (z₂ : Cochain F G n) :
    (Cochain.ofHom (𝟙 F)).comp z₂ (zero_add n) = z₂ := by
  ext p q hpq
  simp only [zero_cochain_comp_v, ofHom_v, HomologicalComplex.id_f, id_comp]

@[simp]
protected lemma comp_zero {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (0 : Cochain G K n₂) h = 0 := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), zero_v, comp_zero]

@[simp]
protected lemma comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ + z₂') h = z₁.comp z₂ h + z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), add_v, comp_add]

@[simp]
protected lemma comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ z₂' : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (z₂ - z₂') h = z₁.comp z₂ h - z₁.comp z₂' h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), sub_v, comp_sub]

@[simp]
protected lemma comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂) : z₁.comp (-z₂) h = -z₁.comp z₂ h := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), neg_v, comp_neg]

@[simp]
protected lemma comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂)
    (h : n₁ + n₂ = n₁₂ ) : z₁.comp (k • z₂) h = k • (z₁.comp z₂ h) := by
  ext p q hpq
  simp only [comp_v _ _ h p _ q rfl (by linarith), zsmul_v, comp_zsmul]

@[simp]
protected lemma comp_id {n : ℤ} (z₁ : Cochain F G n) :
    z₁.comp (Cochain.ofHom (𝟙 G)) (add_zero n) = z₁ := by
  ext p q hpq
  simp only [comp_zero_cochain_v, ofHom_v, HomologicalComplex.id_f, comp_id]

@[simp]
lemma ofHoms_comp (φ : ∀ (p : ℤ), F.X p ⟶ G.X p) (ψ : ∀ (p : ℤ), G.X p ⟶ K.X p) :
    (ofHoms φ).comp (ofHoms ψ) (zero_add 0) = ofHoms (fun p => φ p ≫ ψ p) := by aesop_cat

@[simp]
lemma ofHom_comp (f : F ⟶ G) (g : G ⟶ K) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0) := by
  simp only [ofHom, HomologicalComplex.comp_f, ofHoms_comp]

variable (K)

/-- The differential on a cochain complex, as a cochain of degree `1`. -/
def diff : Cochain K K 1 := Cochain.mk (fun p q _ => K.d p q)

@[simp]
lemma diff_v (p q : ℤ) (hpq : p + 1 = q) : (diff K).v p q hpq = K.d p q := rfl

end Cochain

variable {F G}

/-- The differential on the complex of morphisms between cochain complexes. -/
def δ (z : Cochain F G n) : Cochain F G m :=
  Cochain.mk (fun p q hpq => z.v p (p + n) rfl ≫ G.d (p + n) q +
    m.negOnePow • F.d p (p + m - n) ≫ z.v (p + m - n) q (by rw [hpq, sub_add_cancel]))

/-! Similarly as for the composition of cochains, if `z : Cochain F G n`,
we usually need to carefully select intermediate indices with
good definitional properties in order to obtain a suitable expansion of the
morphisms which constitute `δ n m z : Cochain F G m` (when `n + 1 = m`, otherwise
it shall be zero). The basic equational lemma is `δ_v` below. -/

lemma δ_v (hnm : n + 1 = m) (z : Cochain F G n) (p q : ℤ) (hpq : p + m = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) : (δ n m z).v p q hpq =
    z.v p q₁ (by rw [hq₁, ← hpq, ← hnm, ← add_assoc, add_sub_cancel]) ≫ G.d q₁ q
      + m.negOnePow • F.d p q₂ ≫ z.v q₂ q
          (by rw [← hq₂, add_assoc, add_comm 1, hnm, hpq]) := by
  obtain rfl : q₁ = p + n := by linarith
  obtain rfl : q₂ = p + m - n := by linarith
  rfl

notation a " •[" h "] " b:80 => Cochain.comp a b h

lemma δ_eq (hnm : n + 1 = m) (z : Cochain F G n) :
    δ n m z = z •[hnm] (Cochain.diff G) +
      m.negOnePow • (Cochain.diff F)•[by rw [← hnm, add_comm 1]] z := by
  ext p q hpq
  dsimp
  simp only [δ_v n m hnm z p q hpq (q-1) (p+1) rfl rfl,
    Cochain.comp_v _ _ hnm p (q-1) q (by linarith) (by linarith),
    Cochain.comp_v _ _ (show 1+n = m by linarith) p (p+1) q (by linarith) (by linarith),
    Cochain.diff_v]

@[simp]
lemma δ_zero_cochain_v (z : Cochain F G 0) (p q : ℤ) (hpq : p + 1 = q) :
    (δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q):= by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by linarith) hpq, zero_add,
    Int.negOnePow_one, neg_smul, one_smul, sub_eq_add_neg]

lemma δ_shape (hnm : ¬ n + 1 = m) (z : Cochain F G n) : δ n m z = 0 := by
  ext p q hpq
  dsimp [δ, Cochain.v, Cochain.mk]
  rw [F.shape, G.shape, comp_zero, zero_add, zero_comp, smul_zero]
  . rfl
  all_goals
    change ¬ _=_
    rintro h
    apply hnm
    linarith

variable (F G)

@[simps]
def δ_hom : Cochain F G n →+ Cochain F G m where
  toFun := δ n m
  map_zero' := by
    ext p q hpq
    simp [δ]
  map_add' _ _ := by
    dsimp only
    by_cases n + 1 = m
    . ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, zsmul_add]
      abel
    . simp only [δ_shape _ _ h, add_zero]

variable {F G}

@[simp] lemma δ_add (z₁ z₂ : Cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom F G n m).map_add z₁ z₂

@[simp] lemma δ_sub (z₁ z₂ : Cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom F G n m).map_sub z₁ z₂

@[simp] lemma δ_zero : δ n m (0 : Cochain F G n) = 0 := (δ_hom F G n m).map_zero

@[simp] lemma δ_neg (z : Cochain F G n) : δ n m (-z) = - δ n m z :=
  (δ_hom F G n m).map_neg z

@[simp] lemma δ_zsmul (k : ℤ) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom F G n m).map_zsmul z k

lemma δδ (n₀ n₁ n₂ : ℤ) (z : Cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂ ; swap ; rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁ ; swap ; rw [δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  have : n₂.negOnePow = n₀.negOnePow := by
    subst h₁₂ h₀₁
    simp only [Int.negOnePow_succ, neg_neg]
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q-1) (by linarith) (q-2) _ (by linarith) rfl,
    δ_v n₀ n₁ h₀₁ z (p+1) q (by linarith) _ (p+2) rfl (by linarith),
    ← h₀₁, Int.negOnePow_succ, neg_smul, sub_add_cancel, add_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, neg_comp, zero_add, neg_neg, comp_add,
    comp_neg, comp_zsmul, HomologicalComplex.d_comp_d_assoc, zero_comp, zsmul_zero,
    neg_zero, add_zero, zsmul_comp, add_left_neg, this]

-- TODO use the external multiplication instead of composition, with reverse order of parameters
-- so that this reads as `δ (α • β) = (δ α) • β + (-1)^(deg α) α • δ β`
-- update: better not do that actually
lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
  δ n₁₂ m₁₂ (z₁ •[h] z₂) = z₁ •[by rw [← h₁₂, ← h₂, ← h, add_assoc]] (δ n₂ m₂ z₂) +
    n₂.negOnePow • (δ n₁ m₁ z₁) •[by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]] z₂ := by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by linarith),
    Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by linarith) p (p+n₁+1) q (by linarith) (by linarith),
    δ_v (n₁ + n₂) _ rfl (z₁ •[rfl] z₂) p q hpq (p + n₁ + n₂) _ (by linarith) rfl,
    z₁.comp_v z₂ rfl p _ _ rfl rfl,
    z₁.comp_v z₂ rfl (p+1) (p+n₁+1) q (by linarith) (by linarith),
    δ_v n₂ (n₂+1) rfl z₂ (p+n₁) q (by linarith) (p+n₁+n₂) _ (by linarith) rfl]
  rw [δ_v n₁ (n₁+1) rfl z₁ p (p+n₁+1) (by linarith) (p+n₁) _ (by linarith) rfl]
  simp only [assoc, comp_add, add_comp, zpow_one,
    Int.negOnePow_add, mul_neg, mul_one, zsmul_add, neg_zsmul,
    neg_comp, zsmul_neg, zsmul_comp, smul_smul, comp_neg, comp_zsmul,
    mul_comm n₁.negOnePow n₂.negOnePow, Int.negOnePow_one]
  abel

lemma δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
    (m₂ : ℤ) (h₂ : n₂+1 = m₂) :
    δ n₂ m₂ (z₁ •[zero_add n₂] z₂) =
      z₁ •[zero_add m₂] (δ n₂ m₂ z₂) + n₂.negOnePow • ((δ 0 1 z₁) •[by rw [add_comm, h₂]] z₂):=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

lemma δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) : δ n₁ m₁ (z₁ •[add_zero n₁] z₂) =
      z₁ •[h₁] (δ 0 1 z₂) + (δ n₁ m₁ z₁) •[add_zero m₁] z₂ := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_zsmul,
    Int.negOnePow_zero]

@[simp]
lemma δ_ofHom {p : ℤ} (φ : F ⟶ G) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : p = 1
  . subst h
    ext
    simp
  . rw [δ_shape]
    intro
    apply h
    linarith

@[simp]
lemma δ_ofHomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel p (p+1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (p-1) p by simp)] at eq
  rw [Cochain.ofHomotopy, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [Cochain.mk_v, ComplexShape.up_Rel, sub_add_cancel, not_true, add_left_neg,
    Int.negOnePow_zero, one_smul, Cochain.zero_v, Cochain.sub_v, Cochain.ofHom_v, eq]
  abel

lemma δ_neg_one_cochain (z : Cochain F G (-1)) :
    δ (-1) 0 z = Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij ; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [neg_add_self, one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p-1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p+1) by simp)]
  abel

end HomComplex

variable (F G)

open HomComplex

@[simps! X d_apply]
def HomComplex : CochainComplex AddCommGroupCat ℤ where
  X i := AddCommGroupCat.of (Cochain F G i)
  d i j := AddCommGroupCat.ofHom (δ_hom F G i j)
  shape _ _ hij := by ext ; apply δ_shape _ _ hij
  d_comp_d' _ _ _ _ _  := by ext ; apply δδ

namespace HomComplex

def cocycle : AddSubgroup (Cochain F G n) :=
  AddMonoidHom.ker (δ_hom F G n (n+1))

def Cocycle : Type _ := cocycle F G n

instance : AddCommGroup (Cocycle F G n) := by
  dsimp only [Cocycle]
  infer_instance

namespace Cocycle

variable {F G n}

instance : Coe (Cocycle F G n) (Cochain F G n) where
  coe x := x.1

@[ext]
lemma ext (z₁ z₂ : Cocycle F G n) (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

lemma ext_iff (z₁ z₂ : Cocycle F G n) : z₁ = z₂ ↔ (z₁ : Cochain F G n) = z₂ := by
  constructor
  . rintro rfl
    rfl
  . apply ext

variable (F G n)

@[simp]
lemma coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0 := by rfl

variable {F G n}

@[simp]
lemma coe_add (z₁ z₂ : Cocycle F G n) : (↑(z₁ + z₂) : Cochain F G n) =
  (z₁ : Cochain F G n) + (z₂ : Cochain F G n) := rfl

@[simp]
lemma coe_neg (z : Cocycle F G n) : (↑(-z) : Cochain F G n) =
  -(z : Cochain F G n):= rfl

@[simp]
lemma coe_zsmul (z : Cocycle F G n) (x : ℤ) : (↑(x • z) : Cochain F G n) =
  x • (z : Cochain F G n) := rfl

@[simp]
lemma coe_sub (z₁ z₂ : Cocycle F G n) : (↑(z₁ - z₂) : Cochain F G n) =
  (z₁ : Cochain F G n) - (z₂ : Cochain F G n) := rfl

variable (n)

lemma mem_iff (hnm : n+1=m) (z : Cochain F G n) :
    z ∈ cocycle F G n ↔ δ n m z = 0 := by
  subst hnm
  rfl

variable {n}

@[simps]
def mk (z : Cochain F G n) (m : ℤ) (hnm : n+1 = m) (h : δ n m z = 0) : Cocycle F G n :=
  ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
lemma δ_eq_zero {n : ℤ} (z : Cocycle F G n) (m : ℤ) : δ n m (z : Cochain F G n) = 0 := by
  by_cases h : n+1 = m
  . rw [← mem_iff n m h]
    exact z.2
  . apply δ_shape n m h

@[simps!]
def ofHom (φ : F ⟶ G) : Cocycle F G 0 := mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

@[simps]
def homOf (z : Cocycle F G 0) : F ⟶ G where
  f i := (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, ComplexShape.up_Rel, not_true, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i+1) rfl

@[simp]
lemma homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ := by aesop_cat

@[simp]
lemma ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z := by aesop_cat

@[simp]
lemma cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) :
    (Cochain.ofHom (homOf z) : Cochain F G 0) = (z : Cochain F G 0) := by
  simpa only [ext_iff] using ofHom_homOf_eq_self z

variable (F G)

@[simps]
def equivHom : (F ⟶ G) ≃+ Cocycle F G 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by aesop_cat

variable (K)

@[simps!]
def diff : Cocycle K K 1 :=
  Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    dsimp
    simp only [δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

end Cocycle

namespace Cochain

variable {F G}

/-- Given two morphisms of complexes `φ₁ φ₂ : F ⟶ G`, the datum of an homotopy between `φ₁` and
`φ₂` is equivalent to the datum of a `1`-cochain `z` such that `δ (-1) 0 z` is the difference
of the zero cochains associated to `φ₂` and `φ₁`. -/
@[simps]
def equivHomotopy (φ₁ φ₂ : F ⟶ G) :
    Homotopy φ₁ φ₂ ≃
      { z : Cochain F G (-1) // Cochain.ofHom φ₁ = δ (-1) 0 z + Cochain.ofHom φ₂ } where
  toFun ho := ⟨Cochain.ofHomotopy ho, by simp only [δ_ofHomotopy, sub_add_cancel]⟩
  invFun z :=
    { hom := fun i j => if hij : i + (-1) = j then z.1.v i j hij else 0
      zero := fun i j (hij : j + 1 ≠ i) => dif_neg (fun _ => hij (by linarith))
      comm := fun p => by
        have eq := Cochain.congr_v z.2 p p (add_zero p)
        have h₁ : (ComplexShape.up ℤ).Rel (p - 1) p := by simp
        have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := by simp
        simp only [δ_neg_one_cochain, Cochain.ofHom_v, ComplexShape.up_Rel, Cochain.add_v,
          Homotopy.nullHomotopicMap'_f h₁ h₂] at eq
        rw [dNext_eq _ h₂, prevD_eq _ h₁, eq, dif_pos, dif_pos] }
  left_inv := fun ho => by
    ext i j
    dsimp
    split_ifs with h
    · rfl
    · rw [ho.zero i j (fun h' => h (by dsimp at h'; linarith))]
  right_inv := fun z => by
    ext p q hpq
    dsimp [Cochain.ofHomotopy]
    rw [dif_pos hpq]

@[simp]
lemma equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    (equivHomotopy _ _ (Homotopy.ofEq h)).1 = 0 := rfl

lemma ofHom_injective {f₁ f₂ : F ⟶ G} (h : ofHom f₁ = ofHom f₂) : f₁ = f₂ :=
  (Cocycle.equivHom F G).injective (by ext1; exact h)

end Cochain

section

variable {n} {D : Type _} [Category D] [Preadditive D] (z z' : Cochain K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

namespace Cochain

/-- If `Φ : C ⥤ D` is an additive functor, a cochain `z : Cochain K L n` between
cochain complexes in `C` can be mapped to a cochain between the cochain complexes
in `D` obtained by applying the functor
`Φ.mapHomologicalComplex _ : CochainComplex C ℤ ⥤ CochainComplex D ℤ`. -/
def map : Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cochain.mk (fun p q hpq => Φ.map (z.v p q hpq))

@[simp]
lemma map_v (p q : ℤ) (hpq : p + n = q) : (z.map Φ).v p q hpq = Φ.map (z.v p q hpq) := rfl

@[simp]
lemma map_add : (z + z').map Φ = z.map Φ + z'.map Φ := by aesop_cat

@[simp]
lemma map_neg : (-z).map Φ = -z.map Φ := by aesop_cat

@[simp]
lemma map_sub : (z - z').map Φ = z.map Φ - z'.map Φ := by aesop_cat

variable (K L n)

@[simp]
lemma map_zero : (0 : Cochain K L n).map Φ = 0 := by aesop_cat

@[simp]
lemma map_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (Φ : C ⥤ D) [Φ.Additive] :
    (Cochain.comp z₁ z₂ h).map Φ = Cochain.comp (z₁.map Φ) (z₂.map Φ) h := by
  ext p q hpq
  dsimp
  simp only [map_v, comp_v _ _ h p _ q rfl (by linarith), Φ.map_comp]

@[simp]
lemma map_ofHom :
    (Cochain.ofHom f).map Φ = Cochain.ofHom ((Φ.mapHomologicalComplex _).map f) := by aesop_cat

end Cochain

variable (n)

@[simp]
lemma δ_map : δ n m (z.map Φ) = (δ n m z).map Φ := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl,
      Functor.map_add, Functor.map_comp, Functor.map_zsmul,
      Cochain.map_v, Functor.mapHomologicalComplex_obj_d]
  · simp only [δ_shape _ _ hnm, Cochain.map_zero]

variable {F G}

namespace Cocycle

variable {n} {D : Type _} [Category D] [Preadditive D] (z z' : Cocycle K L n) (f : K ⟶ L)
  (Φ : C ⥤ D) [Φ.Additive]

@[simps!]
def map : Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map Φ) (n+1) rfl (by simp)

@[simp]
lemma map_add : Cocycle.map (z + z') Φ = Cocycle.map z Φ + Cocycle.map z' Φ := by aesop_cat

@[simp]
lemma map_neg : Cocycle.map (-z) Φ = -Cocycle.map z Φ := by aesop_cat

@[simp]
lemma map_sub : Cocycle.map (z-z') Φ = Cocycle.map z Φ - Cocycle.map z' Φ := by aesop_cat

@[simp]
lemma map_of_hom : Cocycle.map (Cocycle.ofHom f) Φ =
  Cocycle.ofHom ((Φ.mapHomologicalComplex _).map f) := by aesop_cat

variable (K L n)

@[simp]
lemma map_zero : Cocycle.map (0 : Cocycle K L n) Φ = 0 := by aesop_cat

end Cocycle

/-variable ( G)

/-- The differential on the complex of morphisms between cochain complexes, as an
additive homomorphism. -/
@[simps!]
def δ_hom : Cochain F G n →+ Cochain F G m :=
  AddMonoidHom.mk' (δ n m) (fun α β => by
    by_cases n + 1 = m
    · ext p q hpq
      dsimp
      simp only [δ_v n m h _ p q hpq _ _ rfl rfl, Cochain.add_v, add_comp, comp_add, zsmul_add]
      abel
    · simp only [δ_shape _ _ h, add_zero])

variable {F G}

@[simp] lemma δ_add (z₁ z₂ : Cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom F G n m).map_add z₁ z₂

@[simp] lemma δ_sub (z₁ z₂ : Cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom F G n m).map_sub z₁ z₂

@[simp] lemma δ_zero : δ n m (0 : Cochain F G n) = 0 := (δ_hom F G n m).map_zero

@[simp] lemma δ_neg (z : Cochain F G n) : δ n m (-z) = - δ n m z :=
  (δ_hom F G n m).map_neg z

@[simp] lemma δ_zsmul (k : ℤ) (z : Cochain F G n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom F G n m).map_zsmul z k

lemma δ_δ (n₀ n₁ n₂ : ℤ) (z : Cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap; rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap; rw [δ_shape _ _ h₀₁, δ_zero]
  ext p q hpq
  dsimp
  simp only [δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
    δ_v n₀ n₁ h₀₁ z p (q-1) (by linarith) (q-2) _ (by linarith) rfl,
    δ_v n₀ n₁ h₀₁ z (p+1) q (by linarith) _ (p+2) rfl (by linarith),
    ← h₁₂, Int.negOnePow_succ, sub_add_cancel, add_comp, assoc,
    HomologicalComplex.d_comp_d, comp_zero, zsmul_comp, zero_add, comp_add,
    comp_zsmul, HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero,
    add_zero, neg_smul, add_right_neg]

lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂)
    (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁) (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₁.comp z₂ h) = z₁.comp (δ n₂ m₂ z₂) (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
      n₂.negOnePow • (δ n₁ m₁ z₁).comp z₂
        (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  subst h₁₂ h₁ h₂ h
  ext p q hpq
  dsimp
  rw [z₁.comp_v _ (add_assoc n₁ n₂ 1).symm p _ q rfl (by linarith),
    Cochain.comp_v _ _ (show n₁ + 1 + n₂ = n₁ + n₂ + 1 by linarith) p (p+n₁+1) q
      (by linarith) (by linarith),
    δ_v (n₁ + n₂) _ rfl (z₁.comp z₂ rfl) p q hpq (p + n₁ + n₂) _ (by linarith) rfl,
    z₁.comp_v z₂ rfl p _ _ rfl rfl,
    z₁.comp_v z₂ rfl (p+1) (p+n₁+1) q (by linarith) (by linarith),
    δ_v n₂ (n₂+1) rfl z₂ (p+n₁) q (by linarith) (p+n₁+n₂) _ (by linarith) rfl,
    δ_v n₁ (n₁+1) rfl z₁ p (p+n₁+1) (by linarith) (p+n₁) _ (by linarith) rfl]
  simp only [assoc, comp_add, add_comp, Int.negOnePow_succ, Int.negOnePow_add n₁ n₂,
    neg_smul, comp_neg, neg_comp, comp_zsmul, zsmul_comp, zsmul_add, smul_neg, smul_smul,
    mul_comm n₁.negOnePow n₂.negOnePow]
  abel

lemma δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain F G 0) (z₂ : Cochain G K n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₁.comp z₂ (zero_add n₂)) =
      z₁.comp (δ n₂ m₂ z₂) (zero_add m₂) +
      n₂.negOnePow • ((δ 0 1 z₁).comp z₂ (by rw [add_comm, h₂])) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

lemma δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₁.comp z₂ (add_zero n₁)) =
      z₁.comp (δ 0 1 z₂) h₁ + (δ n₁ m₁ z₁).comp z₂ (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), one_zsmul,
    Int.negOnePow_zero]

@[simp]
lemma δ_zero_cochain_v (z : Cochain F G 0) (p q : ℤ) (hpq : p + 1 = q) :
    (δ 0 1 z).v p q hpq = z.v p p (add_zero p) ≫ G.d p q - F.d p q ≫ z.v q q (add_zero q) := by
  simp only [δ_v 0 1 (zero_add 1) z p q hpq p q (by linarith) hpq, zero_add,
    Int.negOnePow_one, neg_smul, one_smul, sub_eq_add_neg]

@[simp]
lemma δ_ofHom {p : ℤ} (φ : F ⟶ G) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases p = 1
  · subst h
    ext
    simp
  · rw [δ_shape]
    intro
    exact h (by linarith)


@[simp]
lemma δ_ofHomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom φ₁ - Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel p (p+1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (p-1) p by simp)] at eq
  rw [Cochain.ofHomotopy, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [Cochain.mk_v, add_left_neg, one_zsmul, Int.negOnePow_zero,
    Cochain.sub_v, Cochain.ofHom_v, eq]
  abel

lemma δ_neg_one_cochain (z : Cochain F G (-1)) :
    δ (-1) 0 z = Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p) (p-1) (p+1) rfl rfl]
  simp only [neg_add_self, one_smul, Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p-1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p+1) by simp)]
  abel
end HomComplex

variable (F G)

open HomComplex

/-- The cochain complex of homomorphisms between two cochain complexes `F` and `G`.
In degree `n : ℤ`, it consists of the abelian group `HomComplex.Cochain F G n`. -/
@[simps! X d_apply]
def HomComplex : CochainComplex AddCommGroupCat ℤ where
  X i := AddCommGroupCat.of (Cochain F G i)
  d i j := AddCommGroupCat.ofHom (δ_hom F G i j)
  shape _ _ hij := by ext; apply δ_shape _ _ hij
  d_comp_d' _ _ _ _ _  := by ext; apply δ_δ

namespace HomComplex

/-- The subgroup of cocycles in `Cochain F G n`. -/
def cocycle : AddSubgroup (Cochain F G n) :=
  AddMonoidHom.ker (δ_hom F G n (n+1))

/-- The type of `n`-cocycles, as a subtype of `Cochain F G n`. -/
def Cocycle : Type v := cocycle F G n

instance : AddCommGroup (Cocycle F G n) := by
  dsimp only [Cocycle]
  infer_instance

namespace Cocycle

variable {F G n}

instance : Coe (Cocycle F G n) (Cochain F G n) where
  coe x := x.1

@[ext]
lemma ext (z₁ z₂ : Cocycle F G n) (h : (z₁ : Cochain F G n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

lemma ext_iff (z₁ z₂ : Cocycle F G n) : z₁ = z₂ ↔ (z₁ : Cochain F G n) = z₂ :=
  Subtype.ext_iff

variable (F G n)

@[simp]
lemma coe_zero : (↑(0 : Cocycle F G n) : Cochain F G n) = 0 := by rfl

variable {F G n}

@[simp]
lemma coe_add (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ + z₂) : Cochain F G n) = (z₁ : Cochain F G n) + (z₂ : Cochain F G n) := rfl

@[simp]
lemma coe_neg (z : Cocycle F G n) :
    (↑(-z) : Cochain F G n) = -(z : Cochain F G n) := rfl

@[simp]
lemma coe_zsmul (z : Cocycle F G n) (x : ℤ) :
    (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n) := rfl

@[simp]
lemma coe_sub (z₁ z₂ : Cocycle F G n) :
    (↑(z₁ - z₂) : Cochain F G n) = (z₁ : Cochain F G n) - (z₂ : Cochain F G n) := rfl

variable (n)

lemma mem_iff (hnm : n + 1 = m) (z : Cochain F G n) :
    z ∈ cocycle F G n ↔ δ n m z = 0 := by subst hnm; rfl

variable {n}

/-- Constructor for `Cocycle F G n`, taking as inputs `z : Cochain F G n`, an integer
`m : ℤ` such that `n + 1 = m`, and the relation `δ n m z = 0`. -/
@[simps]
def mk (z : Cochain F G n) (m : ℤ) (hnm : n + 1 = m) (h : δ n m z = 0) : Cocycle F G n :=
  ⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
lemma δ_eq_zero {n : ℤ} (z : Cocycle F G n) (m : ℤ) : δ n m (z : Cochain F G n) = 0 := by
  by_cases h : n + 1 = m
  · rw [← mem_iff n m h]
    exact z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism in `CochainComplex C ℤ`. -/
@[simps!]
def ofHom (φ : F ⟶ G) : Cocycle F G 0 := mk (Cochain.ofHom φ) 1 (zero_add 1) (by simp)

/-- The morphism in `CochainComplex C ℤ` associated to a `0`-cocycle. -/
@[simps]
def homOf (z : Cocycle F G 0) : F ⟶ G where
  f i := (z : Cochain _ _ _).v i i (add_zero i)
  comm' := by
    rintro i j rfl
    rcases z with ⟨z, hz⟩
    dsimp
    rw [mem_iff 0 1 (zero_add 1)] at hz
    simpa only [δ_zero_cochain_v, Cochain.zero_v, sub_eq_zero]
      using Cochain.congr_v hz i (i + 1) rfl

@[simp]
lemma homOf_ofHom_eq_self (φ : F ⟶ G) : homOf (ofHom φ) = φ := by aesop_cat

@[simp]
lemma ofHom_homOf_eq_self (z : Cocycle F G 0) : ofHom (homOf z) = z := by aesop_cat

@[simp]
lemma cochain_ofHom_homOf_eq_coe (z : Cocycle F G 0) :
    Cochain.ofHom (homOf z) = (z : Cochain F G 0) := by
  simpa only [ext_iff] using ofHom_homOf_eq_self z

variable (F G)

/-- The additive equivalence between morphisms in `CochainComplex C ℤ` and `0`-cocycles. -/
@[simps]
def equivHom : (F ⟶ G) ≃+ Cocycle F G 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' := by aesop_cat

variable (K)

/-- The `1`-cocycle given by the differential on a cochain complex. -/
@[simps!]
def diff : Cocycle K K 1 :=
  Cocycle.mk (Cochain.diff K) 2 rfl (by
    ext p q hpq
    simp only [Cochain.zero_v, δ_v 1 2 rfl _ p q hpq _ _ rfl rfl, Cochain.diff_v,
      HomologicalComplex.d_comp_d, smul_zero, add_zero])

end Cocycle-/

section Shift

variable {n : ℤ}

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by linarith)).inv)

lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
  (p' : ℤ) (hp' : p + n = p') :
  (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
    (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

def rightUnshift {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

lemma rightUnshift_v {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

@[simp]
lemma rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').rightUnshift n hn' = γ := by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

@[simp]
lemma rightShift_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => (a * n' + (a*(a-1)/2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p+a) rfl).hom ≫ γ.v (p+a) q (by linarith))

lemma leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + (a*(a-1)/2)).negOnePow • (K.shiftFunctorObjXIso a p p'
      (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p+a := by linarith
  dsimp only [leftShift]
  simp only [mk_v]

def leftUnshift {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => (a * n' + (a*(a-1)/2)).negOnePow •
    (K.shiftFunctorObjXIso a (p-a) p (by linarith)).inv ≫ γ.v (p-a) q (by linarith))

lemma leftUnshift_v {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + (a*(a-1)/2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by linarith)).inv ≫ γ.v p' q (by linarith) := by
  obtain rfl : p' = p - a := by linarith
  rfl

@[simp]
lemma leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').leftUnshift n hn' = γ := by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q-n') (by linarith),
    γ.leftShift_v a n' hn' (q-n') q (by linarith) p hpq,
    comp_zsmul, Iso.inv_hom_id_assoc, smul_smul, Int.negOnePow_mul_self, one_smul]

@[simp]
lemma leftShift_leftUnshift {a n' : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn' : n + a = n') :
    (γ.leftUnshift n hn').leftShift a n' hn' = γ := by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q-n) (by linarith),
    γ.leftUnshift_v n hn' (q-n) q (by linarith) p hpq, comp_zsmul, smul_smul,
    Iso.hom_inv_id_assoc, Int.negOnePow_mul_self, one_smul]

lemma leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (γ' : Cochain L M m)
    (h : n + m = t) (ht' : t + a = t'):
    (γ •[h] γ').leftShift a t' ht' =  (a * m).negOnePow • (γ.leftShift a n' hn') •[by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]] γ' := by
  ext p q hpq
  have h' : n' + m = t' := by linarith
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p+n') q rfl (by linarith),
    γ.leftShift_v a n' hn' p (p+n') rfl (p+a) (by linarith),
    (γ •[h] γ').leftShift_v a t' (by linarith) p q hpq (p+a) (by linarith),
    smul_smul, zsmul_comp, comp_v _ _ h (p+a) (p+n') q (by linarith) (by linarith), assoc,
    Int.negOnePow_add, ← mul_assoc, ← h']
  congr 2
  rw [add_comm n', mul_add, Int.negOnePow_add]

@[simp]
lemma leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (γ' : Cochain L M 0) :
    (γ •[add_zero n] γ').leftShift a n' hn' = (γ.leftShift a n' hn') •[add_zero n'] γ' := by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn', mul_zero, Int.negOnePow_zero, one_smul]

def shift (a : ℤ) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p+a) (q+a) (by linarith) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)

lemma shift_v' (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

@[simp]
lemma shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p+a) (q+a) (by rw [← hpq, add_assoc, add_comm a, add_assoc]) := by
  simp only [shift_v' γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

variable (K L)

@[simp]
lemma rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  ext p q hpq
  dsimp
  rw [rightShift_v _ a n' hn' p q hpq _ rfl, zero_v, zero_comp]

@[simp]
lemma leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain K L n).leftShift a n' hn' = 0 := by
  ext p q hpq
  dsimp
  rw [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), zero_v, comp_zero, zsmul_zero]

@[simp]
lemma shift_zero (a : ℤ) :
    (0 : Cochain K L n).shift a = 0 := by aesop_cat

variable {K L}

@[simp]
lemma rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
  (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, neg_v, neg_comp]

@[simp]
lemma leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), neg_v,
    comp_neg, neg_zsmul, zsmul_neg]

@[simp]
lemma shift_neg (a : ℤ) :
    (-γ).shift a = -γ.shift a := by aesop_cat

@[simp]
lemma rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
  (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

@[simp]
lemma leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), add_v,
    comp_add, zsmul_add]

variable (K L)

@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃+ Cochain K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp
  right_inv γ := by simp
  map_add' γ γ' := by simp

@[simps]
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain K L n ≃+ Cochain (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp
  right_inv γ := by simp
  map_add' γ γ' := by simp

variable {K L}

@[simp]
lemma shift_add (a : ℤ) :
    (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a := by aesop_cat

@[simp]
lemma rightShift_zsmul (a n' : ℤ) (hn' : n' + a = n) (x : ℤ) :
  (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, zsmul_v, zsmul_comp]

@[simp]
def rightUnshift_zsmul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (x : ℤ) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  ext p q hpq
  dsimp
  simp only [rightUnshift_v _ n hn p q hpq _ rfl, zsmul_v, Preadditive.zsmul_comp]

@[simp]
lemma leftShift_zsmul (a n' : ℤ) (hn' : n + a = n') (x : ℤ):
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p+a) (by linarith), zsmul_v, smul_smul,
    comp_zsmul, mul_comm x]

@[simp]
lemma shift_zsmul (a : ℤ) (x : ℤ):
    (x • γ).shift a = x • γ.shift a := by aesop_cat

lemma rightShift_comp {m : ℤ} (γ' : Cochain L M m) {nm : ℤ} (hnm : n + m = nm) (a nm' : ℤ) (hnm' : nm' + a = nm)
    (n' : ℤ) (hn' : n' + a = n) :
    (γ.comp γ' hnm).rightShift a nm' hnm' =
      (γ.rightShift a n' hn').comp (γ'.shift a) (by linarith) := by
  ext p q hpq
  rw [rightShift_v (γ.comp γ' hnm) a nm' hnm' p q (by linarith) (q + a) (by linarith),
    comp_v γ γ' hnm p (p + n) (q + a) rfl (by linarith), assoc,
    comp_v _ _ (show n' + m = nm' by linarith) p (p + n') q (by linarith) (by linarith),
    γ.rightShift_v a n' hn' p (p + n') rfl (p + n) rfl,
    γ'.shift_v a (p + n') q (by linarith)]
  simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, comp_id, assoc, XIsoOfEq_inv_comp_v]

lemma rightUnshift_comp {m : ℤ} {a : ℤ} (γ' : Cochain L (M⟦a⟧) m) {nm : ℤ} (hnm : n + m = nm)
    (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by linarith) := by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by linarith),
    γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl,
    comp_v _ _ (show n + m' = nm' by linarith) p (p + n) q (by linarith) (by linarith),
    γ'.rightUnshift_v m' hm' (p + n) q (by linarith) (p + n + m) rfl, assoc]

lemma δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  . have hnm' : n' + 1 = m' := by linarith
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p+m) rfl (p+n) (p+1) (by linarith) rfl,
      δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by linarith) rfl,
      γ.rightShift_v a n' hn' p (p+n') rfl (p+n) rfl,
      γ.rightShift_v a n' hn' (p+1) q _ (p+m) (by linarith)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      comp_zsmul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, zsmul_comp, smul_add,
      smul_smul, add_right_inj]
    congr
    rw [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc, Int.negOnePow_mul_self, one_mul]
  . have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by linarith)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

lemma δ_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (γ.rightUnshift n hn) = a.negOnePow • (δ n' m' γ).rightUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [γ'.δ_rightShift a n' m' hn m hm', rightUnshift_rightShift, rightUnshift_zsmul,
    smul_smul, Int.negOnePow_mul_self, one_smul]

lemma δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = a.negOnePow • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  . have hnm' : n' + 1 = m' := by linarith
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p+a) (by linarith)]
    rw [δ_v n m hnm _ (p+a) q (by linarith) (p+n') (p+1+a) (by linarith) (by
      linarith)]
    rw [δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by linarith) rfl]
    rw [γ.leftShift_v a n' hn' p (p+n') rfl (p+a) (by linarith)]
    rw [γ.leftShift_v a n' hn' (p+1) q (by linarith) (p+1+a) (by linarith)]
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp,
      shiftFunctor_obj_d', comp_add, smul_add, shiftFunctor_obj_X, smul_smul, zsmul_comp,
      comp_zsmul]
    congr 2
    . rw [Int.negOnePow_add, Int.negOnePow_add, ← mul_assoc, ← hnm', add_comm n', mul_add,
        Int.negOnePow_add, mul_one, ← mul_assoc, Int.negOnePow_mul_self, one_mul]
    . simp only [Int.negOnePow_add, Int.negOnePow_one, mul_one, ← hn', ← hm', mul_add, ← hnm,
        mul_neg]
      ring
  . have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by linarith)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

@[simp]
lemma δ_shift (a m : ℤ) :
    δ n m (γ.shift a) = a.negOnePow • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  . ext p q hpq
    dsimp
    simp only [shift_v, sub_add_cancel, shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl,
      δ_v n m hnm _ (p+a) (q+a) (by linarith) (q-1+a) (p+1+a) (by linarith) (by linarith),
      smul_add, comp_zsmul, zsmul_comp, smul_smul, mul_comm a.negOnePow]
  . rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

def single {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) :
    Cochain K L n :=
  Cochain.mk (fun p' q' _ =>
    if h : p = p' ∧ q = q'
      then (K.XIsoOfEq h.1).inv ≫ f ≫ (L.XIsoOfEq h.2).hom
      else 0)

@[simp]
lemma single_v {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (hpq : p + n = q) :
    (single f n).v p q hpq = f := by
  dsimp [single]
  rw [if_pos, id_comp, comp_id]
  tauto

lemma single_v_eq_zero {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hp' : p' ≠ p) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hp' (by linarith)

lemma single_v_eq_zero' {p q : ℤ} (f : K.X p ⟶ L.X q) (n : ℤ) (p' q' : ℤ) (hpq' : p' + n = q')
    (hq' : q' ≠ q) :
    (single f n).v p' q' hpq' = 0 := by
  dsimp [single]
  rw [dif_neg]
  intro h
  exact hq' (by linarith)

lemma δ_single {p q : ℤ} (f : K.X p ⟶ L.X q) (n m : ℤ) (hm : n + 1 = m)
    (p' q' : ℤ) (hp' : p' + 1 = p) (hq' : q + 1 = q') :
    δ n m (single f n) = single (f ≫ L.d q q') m + m.negOnePow • single (K.d p' p ≫ f) m := by
  ext p'' q'' hpq''
  rw [δ_v n m hm (single f n) p'' q'' (by linarith) (q''-1) (p''+1) rfl (by linarith),
    add_v, zsmul_v]
  congr 1
  · by_cases p'' = p
    · subst h
      by_cases q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by linarith
        simp only [single_v]
      · rw [single_v_eq_zero', single_v_eq_zero', zero_comp]
        all_goals
          intro
          exact h (by linarith)
    · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero _ _ _ _ _ h, zero_comp]
  · subst hm
    by_cases q'' = q
    · subst h
      by_cases p'' = p'
      · subst h
        obtain rfl : p = p''+1 := by linarith
        simp
      · rw [single_v_eq_zero _ _ _ _ _ h, single_v_eq_zero, comp_zero, smul_zero]
        intro
        apply h
        linarith
    · simp only [single_v_eq_zero' _ _ _ _ _ h, comp_zero, smul_zero]

end Cochain

namespace Cocycle

variable (γ : Cocycle K L n)

@[simps!]
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk ((γ : Cochain K L n).rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n'+1) hn' (n+1) (by linarith),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

@[simps!]
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cocycle (K⟦a⟧) L n' :=
  Cocycle.mk ((γ : Cochain K L n).leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n'+1) hn' (n+1) (by linarith),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

@[simps!]
def shift (a : ℤ) : Cocycle (K⟦a⟧) (L⟦a⟧) n :=
  Cocycle.mk ((γ : Cochain K L n).shift a) _ rfl (by simp)

end Cocycle

end Shift

--variable {F G K L : CochainComplex C ℤ}

@[simp]
lemma δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain F G n) (z₂ : Cocycle G K 0) (m : ℤ) :
    δ n m (z₁ •[add_zero n] (z₂ : Cochain G K 0)) =
      (δ n m z₁) •[add_zero m] (z₂ : Cochain G K 0) := by
  by_cases hnm : n + 1 = m
  . simp only [δ_comp_zero_cochain _ _ _ hnm, Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add]
  . simp only [δ_shape _ _ hnm, Cochain.zero_comp]

@[simp]
lemma δ_comp_ofHom {n : ℤ} (z₁ : Cochain F G n) (f : G ⟶ K) (m : ℤ) :
    δ n m (z₁ •[add_zero n] (Cochain.ofHom f)) =
      (δ n m z₁) •[add_zero m] (Cochain.ofHom f) := by
  rw [← Cocycle.ofHom_coe, δ_comp_zero_cocycle]

@[simp]
lemma δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle F G 0) (z₂ : Cochain G K n) (m : ℤ) :
    δ n m ((z₁ : Cochain F G 0) •[zero_add n] z₂) =
      (z₁ : Cochain F G 0) •[zero_add m] (δ n m z₂) := by
  by_cases hnm : n + 1 = m
  . simp only [δ_zero_cochain_comp _ _ _ hnm, Cocycle.δ_eq_zero, Cochain.zero_comp,
      smul_zero, add_zero]
  . simp only [δ_shape _ _ hnm, Cochain.comp_zero]

@[simp]
lemma δ_ofHom_comp {n : ℤ} (f : F ⟶ G) (z : Cochain G K n) (m : ℤ) :
    δ n m ((Cochain.ofHom f) •[zero_add n] z) =
      (Cochain.ofHom f) •[zero_add m] (δ n m z) := by
  rw [← Cocycle.ofHom_coe, δ_zero_cocycle_comp]

end

end HomComplex

end CochainComplex
