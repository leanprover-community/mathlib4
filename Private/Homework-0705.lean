import Mathlib.Tactic



section Special_Example_070501
--Let $\alpha$ be an automorphism of the group $G$. If for any $g \in G$, we have $g^{-1} * \alpha(g) \in Z(G)$, then for any element $a, b \in G$, we have $\alpha (a * b * a^{-1} * b^{-1}) = a * b * a^{-1} * b^{-1}$.
variable {G : Type*} [Group G] (α : G →* G) (a b g x : G)

def centre_carrier {G : Type*} [Group G] : Set G := { g | ∀ h : G, g * h = h * g }

def centre {G : Type*} [Group G]: Subgroup G where
  carrier := centre_carrier
  -- To show the center is closed under multiplication, we take $a, b \in Z(G)$ and show $ab \in Z(G)$.
  mul_mem' := by
    intro a b ha hb h
    -- We use associativity and the commutative property of elements in the center.
    rw [mul_assoc, hb h, ← mul_assoc, ha h, mul_assoc]
  -- The identity element is in the center since $1g = g1 = g$ for any $g \in G$.
  one_mem' := by
    intro g
    group
  -- The inverse of any element in the center is also in the center.
  inv_mem' := by
    intro x hx g
    calc
      -- We use the properties of the inverse and the commutativity of $x$ with any $g \in G$.
      _= x⁻¹ * (g * x) * x⁻¹ := by group
      _= x⁻¹ * (x * g) * x⁻¹ := by rw [hx g]
      _= g * x⁻¹ := by group

/-
Given that for all $g \in G$, $(g^{-1} \alpha(g)) \in Z(G)$, we need to prove that for all $a, b \in G$, $\alpha(a * b * a^{-1} * b^{-1}) = a * b * a^{-1} * b^{-1}$.
-/
example (h₀ : ∀ g , (g⁻¹ * α g) ∈ centre): ∀ a , ∀ b , α (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by
  intro a b
  -- First, we show that for any $g, h \in G$, $g * h * g^{-1} = \alpha(g) * h * \alpha(g)^{-1}$.
  have (g h : G) : g * h * g⁻¹ = α g * h * α g⁻¹ := by
    calc
      _ = g * (h * (g⁻¹ * α g)) * α g⁻¹ := by simp only [map_inv, mul_right_inv, mul_one]; group
      _ = _ := by rw [fun g h ↦ Eq.symm (SemiconjBy.eq (h₀ g h))]; group
  -- Now we use the property of $\alpha$ being a homomorphism and the result from above to complete the proof.
  calc
    _ = α a * α b * α a⁻¹ * α b⁻¹ := by simp only [map_mul, map_inv]
    _ = a * (α b * a⁻¹ * α b⁻¹) := by rw [← this]; group
    _ = _ := by rw [← this]; group

end Special_Example_070501



section Special_Example_070502

/-
Let $f: G \to H$ be a group homomorphism and $M$ is a subgroup of $G$. Prove that $f^{-1}(f(M)) = KM$ where $K = \ker f$.
-/
--Let $G$ and $H$ be groups, $\alpha: G \to H$ be a group homomorphism, and $M$ be a subgroup of $G$.
--We want to prove that the preimage of the image of $M$ under $\alpha$ is the set of elements $x \in G$ such that $x$ can be written as $h \cdot k$, where $h \in \ker(\alpha)$ and $k \in M$.
example {G H : Type*} [Group G] [Group H] (α : G →* H) (M : Subgroup G) :
     α⁻¹' (α '' M.carrier) = {x : G | ∃ h ∈ α.ker ,∃ k ∈ M , x= h * k } := by
  -- We prove the subset inclusion in both directions.
  apply Set.Subset.antisymm
  -- First, we show that if $x \in \alpha^{-1}(\alpha(M))$, then $x$ can be written as $h \cdot k$, where $h \in \ker(\alpha)$ and $k \in M$.
  · intro x hx
    have hx: α x ∈ α '' M.carrier := by exact hx
    rcases hx with ⟨y, hy, feq⟩
    -- We use $y \in M$ to construct $x$.
    use x * y⁻¹
    constructor
    -- Show that $x \cdot y^{-1} \in \ker(\alpha)$.
    · have : α (x * y⁻¹) = 1 := by
        calc
          _ = α x * α y⁻¹ := by rw [MonoidHom.map_mul α x y⁻¹]
          _ = α y * α y⁻¹ := by rw [← feq]
          _ = α (y * y⁻¹) := by rw [MonoidHom.map_mul α y y⁻¹]
          _ = α 1 := by group
          _ = _ := by rw [MonoidHom.map_one α]
      exact this
    -- Show that $x = (x \cdot y^{-1}) \cdot y$.
    · use y
      constructor
      · exact hy
      · group
  -- Next, we show that if $x$ can be written as $h \cdot k$ with $h \in \ker(\alpha)$ and $k \in M$, then $x \in \alpha^{-1}(\alpha(M))$.
  · intro x hx
    rcases hx with ⟨k, hk, m, hm, feq⟩
    show ∃ y ∈ M , α y = α x
    use m
    constructor
    · exact hm
    -- Show that $\alpha x = \alpha m$ using the properties of $\alpha$ and $h \in \ker(\alpha)$.
    · have : α k = 1 := by exact hk
      calc
        _ = 1 * α m  := by group
        _ = α k * α m := by rw [← hk]
        _ = α (k * m) := by rw [MonoidHom.map_mul α k m]
        _ = _ := by rw [← feq]

end Special_Example_070502



section Special_Example_070503

/-
Let $G$ and $H$ be groups, and let $f: G \to H$ be a group homomorphism. If $g \in G$, then the order of $f(g)$ divides the order of $g$.
-/
--We want to prove that the order of $f(g)$ divides the order of $g$ for any $g \in G$.
-- example { G H: Type* } [AddGroup G][AddGroup H](f : G →+ H)(g : G): orderOf (f g) ∣ orderOf g := by sorry
example { G H: Type* } [ Group G][ Group H](f : G →* H)(g : G) : orderOf (f g) ∣ orderOf g:= by
  -- exact orderOf_map_dvd f g
  -- We show that $(f g)^{\text{orderOf } g} = 1$.
  have : (f g) ^ orderOf g = 1 := by
    calc
      _ = f (g ^ orderOf g) := by rw [← MonoidHom.map_pow f g (orderOf g)]
      -- Since $g^{\text{orderOf } g} = 1$ by definition of order.
      _ = f 1 := by rw [pow_orderOf_eq_one g]
      -- Since $f(1) = 1$ for any group homomorphism $f$.
      _ = _ := MonoidHom.map_one f
  -- Thus, the order of $f(g)$ divides the order of $g$.
  exact orderOf_dvd_of_pow_eq_one this

end Special_Example_070503
