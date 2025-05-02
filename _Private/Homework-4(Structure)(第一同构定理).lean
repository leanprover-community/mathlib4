import Mathlib.Tactic



section Special_Example_070303
/-
Let $G$ be the set of pairs of real numbers $(x, y)$ with $x \ne 0$. Define the multiplication on $G$ by $(x, y)(z, w) = (xz, xw + y)$. Prove that $G$ is a group.
-/
@[ext]
structure pt where
  -- fill in the rest
  x : ℝ
  y : ℝ
  property : x ≠ 0

instance mul (a b : pt) : pt :=
  ⟨a.x * b.x, a.x * b.y + a.y, mul_ne_zero a.property b.property⟩

-- instance : Mul (pt) where
--   mul := mul
noncomputable instance inv (a: pt) : pt :=
  ⟨a.x⁻¹, -a.y / a.x, inv_ne_zero a.property⟩

theorem mul_assoc₁ (a b c : pt) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]
  ext<;>dsimp
  repeat' ring

noncomputable instance : Group pt where
  mul := mul
  mul_assoc := mul_assoc₁
  one := ⟨1,0, by norm_num ⟩
  one_mul := by
    intro ⟨x₁, x₂, hx⟩
    ext<;> dsimp
    · show 1 * x₁ = x₁
      ring
    · show 1 * x₂ + 0 = x₂
      ring
  mul_one := by
    intro ⟨x₁, x₂, hx⟩
    ext<;> dsimp
    · show x₁ * 1 = x₁
      ring
    · show x₁ * 0 + x₂ = x₂
      ring
  inv := inv
  mul_left_inv := by
    intro ⟨x₁, x₂, hx⟩
    ext<;> dsimp
    · show x₁⁻¹ * x₁ = 1
      exact inv_mul_cancel hx
    · show x₁⁻¹ * x₂ + -x₂ / x₁ = 0
      ring

end Special_Example_070303




section Special_Example_070603
/-
Let $G$ be the group of pairs of real numbers $(x, y)$ with $x \neq 0$, equipped with the multiplication $(x, y)(z, w) = (xz, xw + y)$. Prove that $K = \{ (1, b) \mid b \in \mathbb{R} \}$ is a normal subgroup of $G$ and that $G / K \cong \mathbb{R}^{\times}$, where $\mathbb{R}^{\times}$ is the multiplicative group of non-zero real numbers.
-/
@[ext]
structure G where
  x : ℝ
  y : ℝ
  h : x ≠ 0

noncomputable instance :Group G where
  mul a b := ⟨a.x * b.x, a.x * b.y + a.y, mul_ne_zero a.h b.h⟩
  mul_assoc := by
    intro a b c
    ext
    · exact mul_assoc a.x b.x c.x
    · show (a.x * b.x) * c.y + (a.x * b.y + a.y) = a.x * (b.x * c.y + b.y) + a.y
      ring
  one := ⟨1, 0, one_ne_zero⟩
  one_mul := by
    intro a
    ext
    · exact one_mul a.x
    · show 1 * a.y + 0 = a.y
      simp only [one_mul, add_zero]
  mul_one := by
    intro a
    ext
    · exact mul_one a.x
    · show a.x * 0 + a.y = a.y
      simp only [mul_zero, zero_add]
  inv a := ⟨a.x⁻¹, - a.x⁻¹ * a.y, inv_ne_zero a.h⟩
  mul_left_inv := by
    intro a
    ext
    · exact inv_mul_cancel a.h
    · show a.x⁻¹ * a.y + (- a.x⁻¹ * a.y) = 0
      simp only [neg_mul, _root_.add_right_neg]

noncomputable instance K : Subgroup G where
  carrier := {a : G | a.x = 1}
  one_mem' := by
    show ⟨1, 0, one_ne_zero⟩ ∈ {a : G | a.x = 1}
    exact rfl
  mul_mem' := by
    intro a b ha hb
    dsimp
    show a.x * b.x =1
    rw [ha, hb]
    norm_num
  inv_mem' := by
    intro x hx
    dsimp
    show x.x⁻¹ = 1
    rw [hx]
    norm_num

instance : K.Normal where
  conj_mem := by
    intro x hx a
    show (a.x * x.x) * a.x⁻¹= 1
    rw[hx]
    simp only [mul_one, ne_eq, a.h, not_false_eq_true, mul_inv_cancel]

lemma hint(x y :ℝ)(h₁ : x ≠ 0)(h₂ : x⁻¹ * y = 1) : y = x := by
  calc
    _ = x * (x⁻¹ * y) := Eq.symm (mul_inv_cancel_left₀ h₁ y)
    _ = x * 1 := by rw [h₂]
    _ = _ := MulOneClass.mul_one x

noncomputable def α' : G ⧸ K ≃* ℝˣ where
  toFun := by
    intro X
    use (Quotient.out' X).x
    exact 1/(Quotient.out' X).x
    · field_simp [(Quotient.out' X).h]
    · field_simp [(Quotient.out' X).h]
  invFun := by
    intro x
    rcases x with ⟨x, invx, eq₁, _⟩
    use QuotientGroup.mk ⟨x , (1:ℝ), left_ne_zero_of_mul_eq_one eq₁⟩
  left_inv := by
    intro X
    show QuotientGroup.mk ⟨ (Quotient.out' X).x, (1:ℝ), (Quotient.out' X).h⟩ = X
    let Y := Quotient.out' X
    have : Y = Quotient.out' X := by rfl
    rw [← this, ← QuotientGroup.out_eq' X]
    apply QuotientGroup.eq'.mpr
    -- show (⟨ Y.x⁻¹, _, _⟩ * Y).x = 1
    show Y.x⁻¹ * Y.x = 1
    exact inv_mul_cancel Y.h
  right_inv := by
    intro a
    rcases a with ⟨a, inva,eq₁,eq₂⟩
    let X  := QuotientGroup.mk (s := K) ⟨a , (1:ℝ), left_ne_zero_of_mul_eq_one eq₁⟩
    let Y : G := Quotient.out' X
    have : QuotientGroup.mk Y = QuotientGroup.mk ⟨a , (1:ℝ), left_ne_zero_of_mul_eq_one eq₁⟩ := by rw [QuotientGroup.out_eq' X]
    have feq: ⟨a , (1:ℝ), left_ne_zero_of_mul_eq_one eq₁⟩⁻¹ * Y ∈ K := QuotientGroup.eq'.mp (id (Eq.symm this))
    have : (Quotient.out' X).x = a := by
      have : Y = Quotient.out' X := rfl
      rw [← this]
      exact hint a Y.x (left_ne_zero_of_mul_eq_one eq₁) feq
    exact Units.eq_iff.mp this
  map_mul' := by
    intro X Y
    ext
    simp only [one_div, Units.val_mul]
    let A := Quotient.out' X
    let B := Quotient.out' Y
    let C := Quotient.out' (X * Y)
    have ha : Quotient.out' X = A := rfl
    have hb : Quotient.out' Y = B := rfl
    have hc : Quotient.out' (X * Y) = C := rfl
    rw [ha, hb, hc]
    have : QuotientGroup.mk C = QuotientGroup.mk (A * B) := by
      rw[QuotientGroup.out_eq' (X * Y), ←QuotientGroup.out_eq' X, ←QuotientGroup.out_eq' Y]
      rfl
    have : (A * B)⁻¹ * C ∈ K := QuotientGroup.eq'.mp (id (Eq.symm this))
    have : (A * B).x⁻¹ * C.x = 1 := this
    exact hint (A * B).x C.x (A * B).h this

--**Another Method 同构定理**

noncomputable def f: G →* ℝˣ where
  toFun := by
    intro X
    use X.x
    exact 1/X.x
    · field_simp [X.h]
    · field_simp [X.h]
  map_one' := by
    ext
    constructor
  map_mul' := by
    intro X Y
    ext
    constructor

#check QuotientGroup.quotientKerEquivRange

noncomputable def β : G ⧸ K ≃* ℝˣ := by
  have keris: f.ker = K := by
    apply Subgroup.ext
    intro X
    constructor
    · intro hx
      show X.x = (1 : ℝˣ)
      rw [←hx]; rfl
    · intro hx
      ext; exact hx
  have t1: G ⧸ K ≃* G ⧸ f.ker := QuotientGroup.quotientMulEquivOfEq (id (Eq.symm keris))
  have t2: G ⧸ f.ker ≃* f.range := by apply QuotientGroup.quotientKerEquivRange
  have rangeis: f.range = ⊤:= by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨_, h⟩
      rw [←h]
      exact trivial
    · intro
      show ∃ Y : G , f Y = x
      use ⟨x.val , 0, (left_ne_zero_of_mul_eq_one x.val_inv)⟩
      ext
      dsimp [f]
  have im_top: f.range ≃* (⊤:Subgroup ℝˣ ) := by
    apply MulEquiv.subsemigroupCongr
    exact congrArg Submonoid.toSubsemigroup (congrArg Subgroup.toSubmonoid rangeis)
  have t3: f.range ≃* ℝˣ := im_top.trans Subsemigroup.topEquiv
  exact ((id t3.symm).trans (id (t1.trans t2).symm)).symm

end Special_Example_070603



section

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] (N₁ : Subgroup G₁) (N₂ : Subgroup G₂)
  [h₁ : N₁.Normal] [h₂ : N₂.Normal]

instance : (Subgroup.prod N₁ N₂).Normal := Subgroup.prod_normal N₁ N₂

def f' : (G₁ × G₂) →* ((G₁ ⧸ N₁) × (G₂ ⧸ N₂)) where
  toFun := fun x => (QuotientGroup.mk x.1, QuotientGroup.mk x.2)
  map_one' := by
    dsimp
    rfl
  map_mul' := by
    intro x y
    dsimp

noncomputable example : (G₁ × G₂) ⧸ (Subgroup.prod N₁ N₂) ≃* (G₁ ⧸ N₁) × (G₂ ⧸ N₂) :=
  let e₁ : (G₁ × G₂) ⧸ (Subgroup.prod N₁ N₂) ≃* (G₁ × G₂) ⧸ (f' N₁ N₂).ker :=
  QuotientGroup.quotientMulEquivOfEq (by
    ext x
    constructor
    · intro h
      show (f' N₁ N₂) x = 1
      unfold f'
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, QuotientGroup.eq_one_iff]
      tauto
    · intro h
      have : (f' N₁ N₂) x = 1 := h
      unfold f' at this
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, QuotientGroup.eq_one_iff] at this
      exact this
  )
  let e₂ : (G₁ × G₂) ⧸ (f' N₁ N₂).ker ≃* (G₁ ⧸ N₁) × (G₂ ⧸ N₂) :=
  QuotientGroup.quotientKerEquivOfSurjective (f' N₁ N₂) (by
    intro x
    use (Quotient.out' x.1, Quotient.out' x.2)
    unfold f'
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.out_eq', Prod.mk.eta]
  )
  e₁.trans e₂

#check QuotientGroup.lift

def f'' : (G₁ × G₂) ⧸ (Subgroup.prod N₁ N₂) →* ((G₁ ⧸ N₁) × (G₂ ⧸ N₂)) :=
  QuotientGroup.lift (Subgroup.prod N₁ N₂) (f' N₁ N₂) (by
    intro x hx
    show (f' N₁ N₂) x = 1
    unfold f'
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, QuotientGroup.eq_one_iff]
    exact hx
  )

lemma surj : Function.Surjective (f' N₁ N₂) := by
  intro x
  use (Quotient.out' x.1, Quotient.out' x.2)
  unfold f'
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.out_eq', Prod.mk.eta]

lemma inj : Function.Injective (f' N₁ N₂) := by sorry

noncomputable example : (G₁ × G₂) ⧸ (Subgroup.prod N₁ N₂) ≃* (G₁ ⧸ N₁) × (G₂ ⧸ N₂) where
  toFun := (f'' N₁ N₂).toFun
  invFun := by sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := (f'' N₁ N₂).map_mul'

end
