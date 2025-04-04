import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

-- Task 2
/-
Suppose that $G$ is a group and $a, b \in G$ satisfy $a * b=b * a^{-1}$. Prove that $b * a=a^{-1} * b$.
-/
example {G : Type*} [Group G] (a b : G) (h : a * b = b * a⁻¹) : b * a = a⁻¹ * b := by
  --We have h i.e. $ a ^ {-1} * a * b = a ^ {-1} * b * a ^ {-1}$.So $b = a ^ {-1} * b * a ^ {-1}$.Thus $b * a = a ^ {-1} * b * a ^ {-1}a = a ^ {-1} * b$
  nth_rw 1 [← one_mul b]
  rw [← mul_left_inv a, mul_assoc a⁻¹, h, ← mul_assoc, mul_assoc, mul_left_inv, mul_one]


-- Task 3
/-
Suppose that $G$ is a group, $g \in G$, and suppose that $g^{2}=g$. Prove that $g$ is the identity.
-/
example {G : Type*} [Group G] {g : G} (h : g ^ 2 = g) : g = 1 := by
  --We have $g ^ {-1} * g ^ {2} = g ^ {-1} * g$
  have h' : g⁻¹ * g ^ 2 = g⁻¹ * g := by
    rw [h]
  --Thus we have $g = 1$
  rw [pow_two, ← mul_assoc, mul_left_inv g, one_mul] at h'
  exact h'


-- Task 4
/-
Suppose that $G$ is a group, $g \in G$, and suppose that $g^{2}=e$. Prove that $g=g^{-1}$.
-/
example {G : Type*} [Group G] {g : G} (h : g ^ 2 = 1) : g = g⁻¹ := by
  --We have h i.e. $g g =1$, so $g g g ^ {-1} = g ^ {-1}$, which is $g = g ^ {-1}
  rw [pow_two, ← mul_left_inv g] at h
  apply mul_right_cancel at h
  exact h
-- mul_right_cancel 只能apply 不能←

-- apply mul_right_cancel

-- Task 5
example {G : Type*} [Group G] (a b a₁ a₂ : G) : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ ∧ (b * a₁ * b⁻¹) * (b * a₂ * b⁻¹) = b * a₁ * a₂ * b⁻¹ := by
  constructor
  group

-- Task 6
/-
Suppose that $G$ is a group and $a, b, c\in G$. Prove that $a * x * b=c$ has a unique solution.
-/
example {G : Type*} [Group G] (a b c : G) : ∃! x : G, a * x * b = c := by
  --We prove $a ^ {-1} c b ^ {-1}$ is the only $x$
  use (a⁻¹ * c * b⁻¹)
  constructor
  --It's easy to caculate $aa ^ {-1} c b ^ {-1}b = c$
  group
  --If $axb = c$, we have $x = a ^ {-1} (axb) b ^ {-1} = a ^ {-1} c b ^ {-1}$
  intro y h₁
  rw [← one_mul y, ← mul_one y, ← mul_assoc]
  nth_rw 1 [← mul_left_inv a, ← mul_right_inv b]
  rw [← mul_assoc, mul_assoc a⁻¹, mul_assoc a⁻¹, h₁]
  group

-- Task 7
example {G : Type*} [Group G] {x y : G} (h : (x * y) * (x * y) = (x * x) * (y * y)): x * y = y * x := by
  rw [← mul_assoc, ← mul_assoc] at h
  apply mul_right_cancel at h
  nth_rw 1 [← one_mul x]
  nth_rw 2 [← one_mul y]
  rw [← mul_left_inv x]
  symm
  rw [mul_assoc x⁻¹, mul_assoc x⁻¹, mul_assoc x⁻¹, mul_assoc x⁻¹, h]

-- symm at h

-- Task 8
/-
Let $G$ be a group. Prove that $\left(a^{-1}\right)^{-1}=a$ for any element $a\in G$.
-/
example {G : Type*}[Group G]{a :G}: (a⁻¹)⁻¹=a := by
  --We have $a * a ^ {-1} = 1$ and $(a ^ {-1}) ^ {-1} * a ^ {-1} = 1$ .Thus $(a ^ {-1}) ^ {-1} = a ^ {-1} $
  rw [← mul_one a⁻¹⁻¹, ← mul_left_inv a, ← mul_assoc, mul_left_inv a⁻¹, one_mul]

-- Task 9
/-Suppose that $G$ is a group with operation $\circ$; suppose that $x, y \in G$. Show that if
$$
	(x \circ y) \circ(x \circ y)=(x \circ x) \circ(y \circ y),
$$
then $x \circ y=y \circ x$.
-/
example {G : Type*} [Group G]: ∀ (g : G), ∃! (y : G), g * y = 1 := by
  --We prove $g ^ {-1}$ is the only $y$
  intro g'
  use g'⁻¹
  constructor
  --It's easy to caculate $gg ^ {-1} = 1$
  · group
  --If $gy=1$,we have $y = g ^ {-1} gy = g ^ {-1}$
  · intro y₁ h₀
    rw [← mul_right_inv g'] at h₀
    group
    nth_rw 1 [← one_mul y₁]
    rw [zpow_neg_one]
    nth_rw 1 [← one_mul g'⁻¹]
    rw [← mul_left_inv g', mul_assoc, mul_assoc, h₀]

-- Task 10
example {G : Type*} [Group G]: ∃! (le : G), ∃! (re : G), ∀ (g : G), le * g = g ∧ g * re = g := by
  use 1
  constructor
  · use 1
    constructor
    · intro g
      constructor
      · rw [one_mul]
      · rw [mul_one]
    · intro y hy
      have : 1 * y = 1 := (hy 1).2
      rw [@mul_right_eq_self] at this
      exact this
  · intro y ⟨g, h₁, h₂⟩
    dsimp at h₁ h₂
    sorry

-- ring
-- field simp可以把分母乘上去
-- field simp + ring
-- 0 < 1 norm_num




-- Task 11
/-
Let $G$ be a group and suppose that $a * b * c=e$ for $a, b, c \in G$. Show that $b * c * a=e$ and $c*a*b=e$ are also true.
-/
-- lemma.we have $(a ^ {-1}) ^ {-1} = a ^ {-1} $
theorem doulbe_inv {G : Type*}[Group G]{a :G}: (a⁻¹)⁻¹=a := by
  --proof.$a * a ^ {-1} = 1$ and $(a ^ {-1}) ^ {-1} * a ^ {-1} = 1$
  rw [← mul_one a⁻¹⁻¹, ← mul_left_inv a, ← mul_assoc, mul_left_inv a⁻¹, one_mul]

example {G : Type*} [Group G] {a b c : G} (h : a * b * c = 1) : b * c * a = 1 ∧ c * a * b = 1 := by
  constructor
  -- we have $bc = a ^ {-1} $,so $bca = a ^ {-1} a= 1$
  rw [← mul_left_inv a, ← one_mul b, ← mul_left_inv a, mul_assoc a⁻¹, mul_assoc a⁻¹, h, mul_one]
  ---- we have $ab = c ^ {-1} $,so $cab = c c ^ {-1} = 1$
  rw [← mul_one b]
  nth_rw 1 [← mul_left_inv c⁻¹, doulbe_inv, ← mul_assoc, ← mul_assoc, mul_assoc c, mul_assoc c, h, mul_one, mul_right_inv]

#check zpow_neg_one

-- Task 12
/-
Let $G$ is a group and $a b \in G$, prove that $(a b)^{-1} = b^{-1}a^{-1}$.
-/
example {G : Type*}[Group G]{a b : G}:(a * b)⁻¹= b⁻¹ * a⁻¹ :=by
  -- group
  --We have : $(a b) b^{-1}a^{-1} = a a^{-1} = 1$ and $b^{-1}a^{-1} (a b) = b^{-1} a = 1$
  have h : a * b * (a * b)⁻¹ * a * b = a * b * b⁻¹ * a⁻¹ * a * b := by
    group
  --Hence $(a b)^{-1} = b^{-1}a^{-1}$.
  apply mul_right_cancel at h
  apply mul_right_cancel at h
  rw [← one_mul (a * b)⁻¹, ← one_mul b⁻¹, ← mul_left_inv (a * b), mul_assoc (a * b)⁻¹, mul_assoc (a * b)⁻¹, mul_assoc (a * b)⁻¹, h]

-- Task 13
example {G : Type*} [Group G] (a b : G) : ((a * b)⁻¹ = a⁻¹ * b⁻¹ ↔ a * b = b * a) ∧ (a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1) := by
  --constructor
  --constructor
  sorry


-- Task 17
/-
Show that every group $G$ with identity $e$ and such that $x * x=e$ for all $x \in G$ is Abelian.
-/
example {G : Type*} [hG : Group G] (h: ∀ (x : G), x * x = 1) : CommGroup G := {
  --1.We have G is a group already
  hG with
  --2.Prove G have mul_comm law
  mul_comm := by
    intro a b
    have h₁ := h a
    have h₂ := h (b * a)
    have h₃ := h b
    symm
    have h₀ :  b * a * (b * a) = b * a * a * b := by
      rw [h₂, mul_assoc b, h₁, mul_one, h₃]
    nth_rw 1 [← one_mul b]
    nth_rw 2 [← one_mul a]
    rw [← mul_left_inv (b * a), mul_assoc, mul_assoc, h₀]
    group
    -- exact mul_left_cancel h₂
}




-- Task 19
/-
Show that if $(x y)^{-1}=x^{-1} y^{-1}$ for all $x$ and $y$ in the group $G$, then $G$ is Abelian.
-/
example {G : Type*} [hG : Group G] (h: ∀ (x y : G), (x * y)⁻¹ = x⁻¹ * y⁻¹) : CommGroup G := {
  --1.We have G is a group already
  hG with
  --2.Prove G have mul_comm law by $\forall a,b \in G$ have $a * b = b * a$
  mul_comm := by
    intro a b
    have h₁ := h a b
    rw [← inv_inj, h₁]
    group
}

    --  a * b
    -- injective 单射
     -- have : (a * b)⁻¹ = a⁻¹ * b⁻¹ := h a b

example {G : Type*} [Group G] (h: ∀ (x y : G), (x * y)⁻¹ = x⁻¹ * y⁻¹) : CommGroup G := by
  apply CommGroup.mk
  intro a b
  have h₁ : (a * b)⁻¹ = a⁻¹ * b⁻¹ := h a b
  rw [← inv_inj, h₁]
  group






  -- intro a b
  -- nth_rw 1 [← one_mul b]
  -- rw [← mul_left_inv (a * b)⁻¹]
  -- apply h
  -- nth_rw 1 [← one_mul b, ← mul_one a, ← mul_assoc, ← mul_left_inv a⁻¹, ← mul_left_inv b, ← mul_assoc, ← mul_assoc,mul_assoc ( a * a⁻¹⁻¹) ]
  -- symm h





-- rcases解决∃



  -- ∃!先找一个可以的（use）然后变成且后constructor
  -- task 10 rcases with ⟨x₁, Exist, Unique⟩

-- 任意命题要intro 进那个参数 → 也要intro进命题

-- Task 21
/-
Show that for group $G$ and $a, b \in G$, $a b=1$ if and only if $b a=1$.
-/
example {G : Type*} [Group G] {a b : G} : (a * b = 1)  ↔ (b * a = 1) := by
  constructor
  · --Prove if $a * b = 1$ , then $b * a = 1$ is correct
    intro h
    rw [← one_mul b, ← mul_left_inv a, mul_assoc a⁻¹, h, mul_one]
  · --Prove if $b * a = 1$ , then $a * b = 1$ is correct
    intro h
    rw [← one_mul a, ← mul_left_inv b, mul_assoc b⁻¹, h, mul_one]



-- Task 34
/-
Let $M$ be a monoid, that is a set together with an associated binary operation and an identity element. Suppose that $a\in M$ admits a left inverse. Show that  if  the right inverse of $a$ exists, it is unique.
-/

example {G : Type*} [Monoid G] {g : G} (h₁: ∃ (li : G), li * g = 1) (h₂ : ∃ (ri : G), g * ri = 1) : ∃! (ri: G), g * ri = 1 := by
  rcases h₁ with ⟨l, hl⟩
  rcases h₂ with ⟨r, hr⟩
  --We will prove that $s$ is the unique answer
  use r
  constructor -- 拆分成了存在性证明（证明刚刚use带入的数是正确的）和唯一性证明
  · --Show that r is correct
    exact hr
  · --Show that r is unique
    intro y h -- r 唯一 ∀ (y : G), (fun ri => g * ri = 1) y → y = r
    -- have : g * r = g * y := by
    --   rw [h, hr]
    -- rw [← one_mul y, ← one_mul r]
    -- symm
    --nrw [← mul_left_inv g] g没有逆inv
    calc
      y = 1 * y := by exact Eq.symm (one_mul y)
      _ = (l * g) * y := by rw [hl]
      _ = l * (g * y) := by rw [mul_assoc]
      _ = l * 1 := by rw [h]
      _ = l * (g * r) := by rw [hr]
      _ = (l * g) * r := by rw [← mul_assoc]
      _ = 1 * r := by rw [hl]
      _ = r := by exact one_mul r

-- Example_2304B
def centre_carrier {G : Type*} [Group G] : Set G := { g | ∀ h : G, g * h = h * g }
-- Set G 是一个集合，可以做Subgroup G的carrier

def centre {G : Type*} [Group G]: Subgroup G where
  carrier := centre_carrier
  mul_mem' := by
    intro a b ha hb
    rw [centre_carrier] at ha hb
    simp only [Set.mem_setOf_eq] at ha hb
    -- Set.mem_setOf_eq: 把set中的性质拿出来
    rw [centre_carrier]
    simp only [Set.mem_setOf_eq, mul_assoc]
    intro h
    -- 条件里有∀ 传数
    rw [hb h, ha, mul_assoc, hb a]
  one_mem' := by
    intro h
    rw [one_mul, mul_one]
  inv_mem' := by
    intro a ha
    simp only
    simp only at ha
    rw [centre_carrier, Set.mem_setOf_eq] at ha
    rw [centre_carrier, Set.mem_setOf_eq]
    intro h
    nth_rw 2 [← one_mul h]
    rw [← mul_left_inv a, mul_assoc a⁻¹, ha, ← mul_assoc, mul_assoc, mul_right_inv, mul_one]

-- theorem practice₃ {N: Subgroup P} {a b : P ⧸ N}: a * b = b * a := CommGroup.mul_comm a b

#check SetCoe.ext


example {G : Type*} [Group G] : CommGroup (centre : Subgroup G) := by
  constructor
  intro a b
  have ha : (a : G) ∈ centre_carrier := by
    exact (SetLike.coe_mem a)
  -- have ha : (a : G) ∈ centre.carrier := by
  --   refine Subgroup.mem_carrier.mpr ?_
  --   exact a.2
  -- have : (a : G) ∈ (centre : Subgroup G) := a.2
  have hb : (b : G) ∈ centre_carrier := by
    exact (SetLike.coe_mem b)
  simp only [centre_carrier] at ha hb
  apply SetCoe.ext
  apply ha

example {G : Type*} [Group G] : (centre : Subgroup G).Normal where
  conj_mem := by
    intro n hn g
    have hb : (n : G) ∈ centre_carrier := by
      exact hn
    simp only [centre_carrier, Set.mem_setOf_eq] at hb
    rw [mul_assoc, hb, ← mul_assoc, mul_right_inv, one_mul]
    exact hn

-- Example_1110B Task 56
/-
Prove that the elements $\{z:z\in\mathbb C:|z|=1\}$ form an Abelian group under multiplication.
-/
noncomputable instance : CommGroup {z : ℂ // ‖z‖ = 1} where
  --To prove if $|a|=1$ and $|b|=1$,then $|a b|=1$.Then prove it is a group
  mul := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Complex.norm_eq_abs] at ha
    simp only [Complex.norm_eq_abs] at hb
    use a * b
    simp only [Complex.norm_eq_abs, norm_mul]
    rw [ha, hb, one_mul]
  mul_assoc := by
    intro a b c
    ext
    show a.1 * b.1 * c.1= a.1 * (b.1 * c.1)
    rw [mul_assoc]
  one := by
    use 1
    norm_num
  one_mul := by
    intro a
    ext
    show 1 * a.1 = a.1
    rw [one_mul]
  mul_one := by
    intro a
    ext
    show a.1 * 1 = a.1
    rw [mul_one]
  inv := by
    intro a
    use (a.1)⁻¹
    simp only [Complex.norm_eq_abs] at a
    simp only [Complex.norm_eq_abs, norm_inv, inv_eq_one]
    exact a.2
  -- mul_left_inv := by
  --   intro ⟨a, ha⟩
  --   apply Subtype.val_inj.1 --很常用，化成只是value相等
  --   show a⁻¹ * a = 1
  --   apply inv_mul_cancel
  --   simp only [Complex.norm_eq_abs] at ha
  --   rw [← sq_eq_sq] at ha
  --   rw [← Complex.normSq_eq_abs] at ha
  --   have h : 1 ^ 2 > 0 := by norm_num
  --   apply Complex.normSq_pos.mp
  --   · rw [ha]
  --     linarith
  --   · exact AbsoluteValue.nonneg Complex.abs a
  --   · linarith
  mul_left_inv := by
    intro ⟨a, ha⟩
    apply Subtype.val_inj.1
    show a⁻¹ * a = 1
    apply inv_mul_cancel
    simp only [Complex.norm_eq_abs] at ha
    rintro ⟨a ,pa⟩
    have ha' : Complex.abs 0 =0 := by simp only [map_zero]
    linarith
  --To prove it have mul_comm law to make it a commgroup
  mul_comm := by
    intro a b
    ext
    show a.1 * b.1 = b.1 * a.1
    rw [mul_comm]















-- -- Task 15



-- def Func (S : Type*) := S → ℝ

-- instance (S : Type*) : Add (Func S) where
--   add := sorry

-- instance (S : Type*) : Neg (Func S) where
--   neg := sorry

-- instance (S : Type*) : Zero (Func S) where
--   zero := sorry

-- noncomputable instance (S : Type*) : AddGroup (Func S) := by
--   apply AddGroup.ofLeftAxioms
--   · sorry
--   · sorry
--   · sorry

-- def mul (f g : S → S) : S → S := by


-- -- Task 16
-- instance (S : Type*) : Group {f : S → S // f.Bijective} where
--   mul := fun f g => ⟨f.1 ∘ g.1, Function.Bijective.comp f.2 g.2⟩
--   mul_assoc := by
--     intro f g h
--     simp only [mul]

--   one_mul := by

--   mul_one := sorry
--   inv := sorry
--   mul_left_inv := sorry


-- -- Task 22
-- example {G : Type*} [Monoid G] (h: ∀ (g h : G), Unique {x : G // x * g = h}) : Group G := sorry


-- -- Task 23
-- example {G : Type*} [Monoid G] {g : G} (h₁: ∃ (li : G), li * g = 1) (h₂ : ∃ (ri : G), g * ri = 1) : ∃! (ri: G), g * ri = 1 := by sorry


-- -- Task 24
-- example {G: Type*} [CommGroup G] {H: Subgroup G} : CommGroup H := H.toCommGroup


-- -- Task 25
-- def int_add_subgroup (r s : ℤ): Set ℤ := {h | ∃ n m : ℤ, h = n * r + m * s}

-- def int_add_add_subgroup (r s: ℤ) : AddSubgroup ℤ where
--   carrier := int_add_subgroup r s
--   add_mem' := by sorry
--   zero_mem' := by sorry
--   neg_mem' := by sorry

-- def gcd_r_s (r s : ℤ) : int_add_add_subgroup r s := sorry

-- example (r s: ℤ) : ∀ (x : int_add_add_subgroup r s), x ∈ AddSubgroup.zmultiples (gcd_r_s r s) := by sorry

-- -- Task 61
-- def normaliser_carrier {G : Type*} [Group G] (S: Subgroup G): Set G := { g | ∀ h : S, ∃ h' : S, h = g * h' * g⁻¹ }

-- def normaliser {G : Type*} [Group G] (S: Subgroup G): Subgroup G where
--   carrier := normaliser_carrier S
--   mul_mem' := by sorry
--   one_mem' := by sorry
--   inv_mem' := by sorry
