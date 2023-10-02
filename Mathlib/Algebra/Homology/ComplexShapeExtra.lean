import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.Tactic.Linarith

variable {I I₁ I₂ I₃ : Type*} (c : ComplexShape I)
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)

/-- A total complex shape for three complexes shapes `c₁`, `c₂`, `c₃` on three types `I₁`, `I₂`,
`I₃`, consists of the data and properties that will allow the construction of a total
complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₃`
(when suitable coproducts exists). -/
class TotalComplexShape  where
  π : I₁ × I₂ → I₃
  /-- the sign of the horizontal differential in the differential of the total complex -/
  ε₁ : I₁ × I₂ → ℤ -- it seems this is usually the constant `1`, but some applications *may* need others signs?
  /-- the sign of the vertical differential in the differential of the total complex -/
  ε₂ : I₁ × I₂ → ℤ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₃.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₃.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  add_eq_zero {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩ + ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = 0

namespace ComplexShape

section

variable [TotalComplexShape c₁ c₂ c₃]

abbrev π (i : I₁ × I₂) : I₃ := TotalComplexShape.π c₁ c₂ c₃ i
abbrev ε₁ (i : I₁ × I₂) : ℤ := TotalComplexShape.ε₁ c₁ c₂ c₃ i
abbrev ε₂ (i : I₁ × I₂) : ℤ := TotalComplexShape.ε₂ c₁ c₂ c₃ i

variable {c₁}

lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₃.Rel (π c₁ c₂ c₃ ⟨i₁, i₂⟩) (π c₁ c₂ c₃ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₃.next (π c₁ c₂ c₃ ⟨i₁, i₂⟩) = π c₁ c₂ c₃ ⟨i₁', i₂⟩ :=
  c₃.next_eq' (rel_π₁ c₂ c₃ h i₂)

variable (c₁) {c₂}

lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₃.Rel (π c₁ c₂ c₃ ⟨i₁, i₂⟩) (π c₁ c₂ c₃ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₃.next (π c₁ c₂ c₃ ⟨i₁, i₂⟩) = π c₁ c₂ c₃ ⟨i₁, i₂'⟩ :=
  c₃.next_eq' (rel_π₂ c₁ c₃ i₁ h)

variable {c₁}

lemma add_eq_zero
    {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₃ ⟨i₁', i₂⟩ + ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₃ ⟨i₁, i₂'⟩ = 0 :=
  TotalComplexShape.add_eq_zero h₁ h₂

end

section

variable [AddMonoid I] (c : ComplexShape I)

/-- If `I` is an additive monoid and `c : ComplexShape I`, `c.TensorSigns` contains the data of
map `ε : I → ℤ` and properties which allows the construction of a `TotalComplexShape c c c`,
which will allow the construction of a monoidal category structure on homological complex
(when suitable coproducts exist). -/
class TensorSigns where
  ε : I → ℤ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε_succ (p q : I) (hpq : c.Rel p q) : ε q = - ε p
  ε_zero : ε 0 = 1
  ε_add (p q : I) : ε (p + q) = ε p * ε q

variable [TensorSigns c]

abbrev ε (i : I) : ℤ := TensorSigns.ε c i

lemma rel_add {p q : I} (hpq : c.Rel p q) (r : I) : c.Rel (p + r) (q + r) :=
  TensorSigns.rel_add _ _ _ hpq

lemma add_rel (r : I) {p q : I} (hpq : c.Rel p q) : c.Rel (r + p) (r + q) :=
  TensorSigns.add_rel _ _ _ hpq

lemma ε_succ {p q : I} (hpq : c.Rel p q) : c.ε q = - c.ε p :=
  TensorSigns.ε_succ p q hpq

lemma ε_add (p q : I) : c.ε (p + q) = c.ε p * c.ε q :=
  TensorSigns.ε_add p q

@[simp]
lemma ε_zero : c.ε 0 = 1 :=
  TensorSigns.ε_zero

lemma next_add (p q : I) (hp : c.Rel p (c.next p)) :
    c.next (p + q) = c.next p + q :=
  c.next_eq' (c.rel_add hp q)

lemma next_add' (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q :=
  c.next_eq' (c.add_rel p hq)

@[simps]
instance : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  add_eq_zero h _ := by
    dsimp
    rw [one_mul, mul_one, c.ε_succ h, add_left_neg]

@[simps]
instance : TensorSigns (ComplexShape.down ℕ) where
  ε p := (-1) ^ p
  rel_add p q r (hpq : q + 1 = p) := by
    simp only [down_Rel]
    linarith
  add_rel p q r (hpq : q + 1 = p) := by
    simp only [down_Rel]
    linarith
  ε_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one, neg_neg]
  ε_add p q := by
    dsimp
    rw [pow_add]
  ε_zero := by simp

@[simps]
instance : TensorSigns (ComplexShape.up ℤ) where
  ε := Int.negOnePow
  rel_add p q r (hpq : p + 1 = q) := by
    simp only [up_Rel]
    linarith
  add_rel p q r (hpq : p + 1 = q) := by
    simp only [up_Rel]
    linarith
  ε_succ := by
    rintro p _ rfl
    rw [Int.negOnePow_succ]
  ε_add := Int.negOnePow_add
  ε_zero := Int.negOnePow_zero

end

end ComplexShape

section

variable [TotalComplexShape c₁ c₂ c₃] [TotalComplexShape c₂ c₁ c₃]

/-- A total complex shape symmetry contains the data and properties which allow the
identification of the two total complex functors
`HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₃`
and `HomologicalComplex₂ C c₂ c₁ ⥤ HomologicalComplex C c₃` via the flip. -/
class TotalComplexShapeSymmetry where
  symm (i₁ : I₁) (i₂ : I₂) : ComplexShape.π c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₃ ⟨i₁, i₂⟩
  σ (i₁ : I₁) (i₂ : I₂) : ℤ
  σ_mul_self (i₁ : I₁) (i₂ : I₂) : σ i₁ i₂ * σ i₁ i₂ = 1
  compatibility₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ i₁ i₂ * ComplexShape.ε₂ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ i₁' i₂
  compatibility₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ i₁ i₂ * ComplexShape.ε₁ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ i₁ i₂'

variable [TotalComplexShapeSymmetry c₁ c₂ c₃]

namespace ComplexShape

abbrev σ (i₁ : I₁) (i₂ : I₂) : ℤ := TotalComplexShapeSymmetry.σ c₁ c₂ c₃ i₁ i₂

lemma π_symm (i₁ : I₁) (i₂ : I₂) :
    ComplexShape.π c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₃ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm

@[simp]
lemma σ_mul_self (i₁ : I₁) (i₂ : I₂) : σ c₁ c₂ c₃ i₁ i₂ * σ c₁ c₂ c₃ i₁ i₂ = 1 := by
  apply TotalComplexShapeSymmetry.σ_mul_self

variable {c₁}

lemma σ_compatibility₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ c₁ c₂ c₃ i₁ i₂ * ComplexShape.ε₂ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ c₁ c₂ c₃ i₁' i₂ :=
  TotalComplexShapeSymmetry.compatibility₁ h₁ i₂

variable (c₁) {c₂}

lemma σ_compatibility₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ c₁ c₂ c₃ i₁ i₂ * ComplexShape.ε₁ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ c₁ c₂ c₃ i₁ i₂' :=
  TotalComplexShapeSymmetry.compatibility₂ i₁ h₂

@[simps]
instance : TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  symm p q := add_comm q p
  σ p q := (-1) ^ (p * q)
  σ_mul_self p q := by
    dsimp
    rw [← mul_pow, neg_mul, mul_neg, neg_neg, one_mul, one_pow]
  compatibility₁ := by
    rintro _ p rfl q
    dsimp
    rw [add_mul, one_mul, pow_add, mul_assoc, ← mul_pow, neg_mul, mul_neg, neg_neg, one_mul, one_pow, mul_one, one_mul]
  compatibility₂ := by
    rintro p _ q rfl
    dsimp
    rw [mul_one, ← pow_add, add_comm q 1, mul_add, mul_one]

@[simps]
instance : TotalComplexShapeSymmetry (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_mul_self := by aesop
  compatibility₁ := by
    rintro p _ rfl q
    dsimp
    rw [one_mul, ← Int.negOnePow_add, add_mul, one_mul]
  compatibility₂ := by
    rintro p q _ rfl
    dsimp
    rw [mul_one, add_comm q 1, mul_add, mul_one, Int.negOnePow_add, ← mul_assoc, Int.negOnePow_mul_self, one_mul]

end ComplexShape

end

namespace ComplexShape

section

variable [AddMonoid I]

/-- If `I` is an additive monoid, these compatibilities allow the construction of a braiding
isomorphism for the tensor product of complexes. -/
class Braided extends c.TensorSigns,
    TotalComplexShapeSymmetry c c c where
  σ_add₁ (i₁ i₁' i₂ : I) :
    ComplexShape.σ c c c (i₁ + i₁') i₂ = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁' i₂
  σ_add₂ (i₁ i₂ i₂' : I) :
    ComplexShape.σ c c c i₁ (i₂ + i₂') = ComplexShape.σ c c c i₁ i₂ * ComplexShape.σ c c c i₁ i₂'

lemma σ_add₁ (i₁ i₁' i₂ : I) [c.Braided] :
  σ c c c (i₁ + i₁') i₂ = σ c c c i₁ i₂ * σ c c c i₁' i₂ := by
  apply ComplexShape.Braided.σ_add₁

lemma σ_add₂ (i₁ i₂ i₂' : I) [c.Braided] :
  σ c c c i₁ (i₂ + i₂') = σ c c c i₁ i₂ * σ c c c i₁ i₂' := by
  apply ComplexShape.Braided.σ_add₂

instance : (ComplexShape.down ℕ).Braided where
  σ_add₁ p p' q := by
    dsimp
    rw [← pow_add, add_mul]
  σ_add₂ p q q' := by
    dsimp
    rw [← pow_add, mul_add]

instance : (ComplexShape.up ℤ).Braided where
  σ_add₁ p p' q := by
    dsimp
    rw [← Int.negOnePow_add, add_mul]
  σ_add₂ p q q' := by
    dsimp
    rw [← Int.negOnePow_add, mul_add]

end

section

variable [AddCommMonoid I]

/-- If `I` is a commutative additive monoid, this compatibility allows the verification
that the braiding for the tensor product of complexes is symmetric. -/
class Symmetry extends c.Braided where
  σ_symm (i₁ i₂ : I) : ComplexShape.σ c c c i₁ i₂ = ComplexShape.σ c c c i₂ i₁

lemma σ_ε_symm [c.Symmetry] (i₁ i₂ : I) : ComplexShape.σ c c c i₁ i₂ = ComplexShape.σ c c c i₂ i₁ := by
  apply Symmetry.σ_symm

instance : (ComplexShape.down ℕ).Symmetry where
  σ_symm p q := by
    dsimp
    rw [mul_comm]

instance : (ComplexShape.up ℤ).Symmetry where
  σ_symm p q := by
    dsimp
    rw [mul_comm]

end

end ComplexShape
