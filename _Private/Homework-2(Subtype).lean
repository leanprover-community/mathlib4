import Mathlib.Tactic


section Example_2305B

def conj {G : Type*} [Group G] (S: Subgroup G) (g : G) : Set G := { p | ∃ s : S, p = g * s * g⁻¹ }

def normaliser_carrier {G : Type*} [Group G] (S: Subgroup G): Set G := { g | (conj S g) = S }

#check conj_mul
#check conj_inv

lemma conj_inS {G : Type*} [Group G] (S: Subgroup G)(x : G)(s : S)(hx : x ∈ normaliser_carrier S) : x * s * x⁻¹ ∈ S := by
  apply Subgroup.mem_carrier.mpr
  have : x * s * x⁻¹ ∈ conj S x := by use s
  rw [hx] at this
  exact this

lemma inv_conj_In {G : Type*} [Group G] (S: Subgroup G)(x : G)(s : S)(hx : x ∈ normaliser_carrier S): x⁻¹ * s * x ∈ S := by
  have : ↑S ⊆ conj S x := by exact Eq.subset (id (Eq.symm hx))
  have : (s : G) ∈ conj S x := by exact this (SetLike.coe_mem s)
  rcases this with ⟨x,hx⟩
  rw [hx]
  group
  exact SetLike.coe_mem x

def normaliser {G : Type*} [Group G] (S: Subgroup G): Subgroup G where
  carrier := normaliser_carrier S
  mul_mem' := by
    rintro a b ha hb
    apply Set.Subset.antisymm
    · intro p ⟨s, h'⟩
      rw [h']
      have conjb_inS: b * s * b⁻¹ ∈ S := conj_inS S b s hb
      have conja_inS: a * (b * s * b⁻¹) * a⁻¹ ∈ S := by
        apply Subgroup.mem_carrier.mpr
        show a * (b * s * b⁻¹) * a⁻¹ ∈ S.carrier
        have : a * (b * s * b⁻¹) * a⁻¹ ∈ conj S a := by use ⟨b * s * b⁻¹, conjb_inS⟩--类型转化,将其type从G变为subtype S
        rw [ha] at this
        exact this

      --have conja_inS: a * (b * s * b⁻¹) * a⁻¹ ∈ S := conj_inS S a ⟨b * s * b⁻¹, conj_inS S b s hb⟩ ha
      --运用conj_inS引理的一行化证明
      have : (a * b) * ↑s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
      rw [this]
      exact conja_inS
    · intro p h'
      have : (a * b)⁻¹ * p * (a * b) ∈ S := by
        have ht: b⁻¹ * (a⁻¹ * p * a) * b ∈ S := inv_conj_In S b ⟨(a⁻¹ * p * a), inv_conj_In S a ⟨p, h'⟩  ha⟩ hb
        have : (a * b)⁻¹ * p * (a * b) = b⁻¹ * (a⁻¹ * p * a) * b := by group
        rw [this]
        exact ht
      use ⟨ (a * b)⁻¹ * p * (a * b), this⟩
      group

  one_mem' := by
    apply Set.Subset.antisymm
    · rintro s ⟨s₁, hs₁⟩
      have : s = s₁ := by
        rw [hs₁]
        group
      rw [this]
      exact Subtype.coe_prop s₁
    · intro s hs
      use ⟨s, hs⟩
      group

  inv_mem' := by
    intro x hx
    apply Set.Subset.antisymm
    · rintro s ⟨s₁, hs₁⟩
      rw [hs₁]
      have : x⁻¹ * s₁ * x⁻¹⁻¹ = x⁻¹ * s₁ * x := by group
      rw [this]
      exact inv_conj_In S x s₁ hx
    · intro s hs
      have : x * s * x⁻¹ ∈ S := conj_inS S x ⟨s,hs⟩ hx
      use ⟨ x * s * x⁻¹, this⟩
      group

end Example_2305B


/-
The center $Z(G):=\{g\in G:gh=hg\ \forall h\in G\}$ of any group $G$ is a abelian normal subgroup of $G$.
-/
section Example_2304B
def centre_carrier {G : Type*} [Group G] : Set G := { g | ∀ h : G, g * h = h * g }
def centre {G : Type*} [Group G]: Subgroup G where
  carrier := centre_carrier
  mul_mem' := by
    intro a b ha hb
    intro h
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  one_mem' := by
    intro h
    calc
      _ = h := by exact LeftCancelMonoid.one_mul h
      _ =_ := by exact Eq.symm (LeftCancelMonoid.mul_one h)
  inv_mem' := by
    intro h h' h₁
    calc
      _ = h⁻¹ * (h₁ * h) * h⁻¹:= by group
      _ = h⁻¹ * (h * h₁) * h⁻¹ := by rw [← h']
      _ = h₁ * h⁻¹ := by group
--Method 1
example {G : Type*} [Group G]: CommGroup (centre : Subgroup G) := {
  mul_comm := by
    intro a b
    let h := a.property b
    exact Subtype.val_inj.mp h
}

--Method 2
example {G : Type*} [Group G]: CommGroup (centre : Subgroup G) := by
  constructor
  intro a b
  let h := a.property b
  exact Subtype.val_inj.mp h

--Method 3
example {G : Type*} [Group G] : CommGroup (centre : Subgroup G) := by
  apply CommGroup.mk
  rintro ⟨a, ha⟩ b
  have : ∀ g : G, a * g = g * a := fun g => ha g
  ext
  exact this b
-- I'm inspired from the last exercise problem in "20240703 Structures"
/-
#check CommGroup.mk
-- Every cyclic group is a abelian group.
instance {G : Type*} [Group G] (h : IsCyclic G) : CommGroup G := by
-/
example {G : Type*} [Group G] : (centre : Subgroup G).Normal where
  conj_mem := by
    intro x hx g
    have hx: ∀ h : G, x * h = h * x :=  fun h => hx h
    show ∀ h : G, (g * x * g⁻¹) * h = h * (g * x * g⁻¹)
    intro h
    calc
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by rw [hx (g⁻¹ * h * g)]
      _ = h * (g * x * g⁻¹) := by group

end Example_2304B





/-
Let $r$ and $s$ be integers. Show that $\{n r+m s \mid n, m \in \mathbb{Z}\}$ is a subgroup of $\mathbb{Z}$, and every element in this subgroup is a multiple of $\gcd(r, s)$.
-/
section Example_2202B
def int_add_subgroup (r s : ℤ): Set ℤ := {h | ∃ n m : ℤ, h = n * r + m * s}
def int_add_add_subgroup (r s: ℤ) : AddSubgroup ℤ where
  carrier := int_add_subgroup r s
  add_mem' := by
    intro a b ⟨na, ma, ha⟩ ⟨nb, mb, hb⟩
    use na + nb, ma + mb
    linarith
  zero_mem' := by
    use 0, 0
    linarith
  neg_mem' := by
    intro x ⟨nx, mx, hx⟩
    use -nx, -mx
    linarith

#check Nat.xgcd
#check Int.gcdA
def gcd_r_s (r s : ℤ) : int_add_add_subgroup r s := by
  use Int.gcd r s
  use Int.gcdA r s, Int.gcdB r s
  rw [Int.gcd_eq_gcd_ab r s]
  group
--Use Bezout theorem to prove $\exists a b \in \mathbb{Z}$ which have $a r + b s = gcd(r,s)$,then$gcd(r,s) \in$ the set
#check Subtype.val_inj
example (r s: ℤ) : ∀ (x : int_add_add_subgroup r s), x ∈ AddSubgroup.zmultiples (gcd_r_s r s) := by
  intro ⟨x, hx⟩
  rcases hx with ⟨m, n, h⟩
  have : gcd r s ∣ x := by
    rw [h]
    apply dvd_add
    · exact Dvd.dvd.mul_left (gcd_dvd_left r s) m
    · exact Dvd.dvd.mul_left (gcd_dvd_right r s) n
  rcases this with ⟨t,ht⟩
  use t
  dsimp
  apply Subtype.val_inj.mp--*** two subtype equal iff their values equal
  dsimp
  rw [ht,mul_comm]
  rfl

end Example_2202B
