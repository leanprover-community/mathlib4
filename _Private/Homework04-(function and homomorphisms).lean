import Mathlib


section Example_3201B


open Function
/-
Let $G_{1}, G_{2}$, and $G_{3}$ be groups, and let $f: G_{1} \rightarrow G_{2}$ and $g: G_{2} \rightarrow G_{3}$ be isomorphisms. Prove that $g \circ f : G_{1} \rightarrow G_{3},f^{-1} \circ g^{-1} : G_{3} \rightarrow G_{1}$ are isomorphisms.
-/
#check invFun_comp

--We have $g \circ f$ is injective and surjective
lemma inj {G₁ G₂ G₃: Type*} [Group G₁] [Group G₂] [Group G₃] (f : G₁ ≃* G₂) (g : G₂ ≃* G₃) :
    Injective (g ∘ f) := (EmbeddingLike.comp_injective (⇑f) g).mpr (MulEquiv.injective f)

lemma surj {G₁ G₂ G₃: Type*} [Group G₁] [Group G₂] [Group G₃] (f : G₁ ≃* G₂) (g : G₂ ≃* G₃) :
    Surjective (g ∘ f) := (EquivLike.comp_surjective (⇑f) g).mpr (MulEquiv.surjective f)

--And we have $f^{-1} \circ g^{-1} = (g \circ f)^{-1}$
lemma eq {G₁ G₂ G₃: Type*} [Group G₁] [Group G₂] [Group G₃] (f : G₁ ≃* G₂) (g : G₂ ≃* G₃) :
    invFun f ∘ invFun g = invFun (g ∘ f) := by
  refine Eq.symm (invFun_eq_of_injective_of_rightInverse (inj f g) ?hg)
  refine RightInverse.comp ?hg.hf ?hg.hh
  exact rightInverse_invFun (MulEquiv.surjective g)
  exact rightInverse_invFun (MulEquiv.surjective f)

--And as we have all $f : G \rightarrow H$ is a isomorphism, then $f^{-1}$ is a homomorphism from $H \rightarrow G$
lemma feq {G₁ G₂: Type*} {x y : G₂}[Group G₁] [Group G₂]  (f : G₁ ≃* G₂) :
    invFun f (x * y) = invFun f x * invFun f y := by
  have ha: f (invFun f x) = x := invFun_eq (MulEquiv.surjective f x)
  have hb: f (invFun f y) = y := invFun_eq (MulEquiv.surjective f y)
  have : f (invFun f (x * y)) = f ((invFun f x) * (invFun f y)) := by
    calc
      _ = f (invFun f (f (invFun f x) * f (invFun f y))) := by rw [ha, hb]
      _ = f (invFun f (f ((invFun f x) * (invFun f y)))) := by rw [MulEquiv.map_mul f (invFun f x) (invFun f y)]
      _ = _ := by apply apply_invFun_apply
  exact MulEquiv.injective f this

--Hence we have $g \circ f$ is a homomorphism, then $g \circ f$ is a isomorphism
noncomputable example {G₁ G₂ G₃: Type*} [Group G₁] [Group G₂] [Group G₃] (f : G₁ ≃* G₂) (g : G₂ ≃* G₃) : G₁ ≃* G₃ where
  toFun := g ∘ f
  invFun := invFun (g ∘ f)
  left_inv := rightInverse_iff_comp.mpr
    (Eq.mpr (id (congrArg (fun _a => _a = id) (invFun_comp (inj f g)))) (Eq.refl id))
  right_inv := by
    apply rightInverse_invFun
    exact surj f g
  map_mul' := by simp only [Function.comp_apply, map_mul, implies_true]

-- So $(f^{-1} \circ g^{-1})^{-1} = g \circ f$ and it is a isomorphism
noncomputable example {G₁ G₂ G₃: Type*} [Group G₁] [Group G₂] [Group G₃] (f : G₁ ≃* G₂) (g : G₂ ≃* G₃) : G₃ ≃* G₁ where
  toFun := invFun f ∘ invFun g
  invFun := g ∘ f
  left_inv := by
    rw [eq]
    apply rightInverse_iff_comp.mpr (rightInverse_iff_comp.mp (rightInverse_invFun (surj f g)))
  right_inv := by
    rw [eq]
    apply rightInverse_iff_comp.mpr (invFun_comp (inj f g))
  map_mul' := by
    simp only [comp_apply]
    intro x y
    calc
      _ = invFun f ((invFun g x) * (invFun g y)) := by rw [@feq]
      _ = invFun f (invFun g x) * invFun f (invFun g y) := by rw [@feq]

end Example_3201B



section Example_3221B
/-
Let $G$ and $H$ be groups. Prove that $G \times H \cong H \times G$.
-/
def exchangeiso {G H : Type*} [Group G] [Group H] : (G × H) ≃* (H × G) where
  toFun := by
    --We construct a map from $G \times H \to H \times G$ by $(x,y)$ maps to $(y,x)$
    intro x
    use x.2,x.1
  invFun := by
    --And its inverse is $(y,x)$ maps to $(x,y)$
    intro y
    use y.2,y.1
  left_inv := by
    --It is trivial to check inverse is well defined
    intro x
    simp only [Prod.mk.eta]
  right_inv := by
    intro y
    simp only [Prod.mk.eta]
  map_mul' := by
    --It is a homomorphism because the property of direct product
    intro x₁ x₂
    simp only [Prod.snd_mul, Prod.fst_mul, Prod.mk_mul_mk]

end Example_3221B



section Exercise_2294

open scoped Pointwise
open Function MulOpposite Set
/-
Let $H$ be a subgroup of a group $G$ and let $a, b \in G$. Prove the statement.

1.If $H a=H b$, then $b \in H a$.

2.If $a H=b H$, then $H a^{-1}=H b^{-1}$.
-/
example {G : Type*}[Group G](H : Subgroup G)(a b : G)(h : op a • (H : Set G) = op b • (H : Set G)) :
    b ∈ op a • (H : Set G) := by
  --We have $b \in H b$ beacuse $b = b \cdot 1 $ which $1 \in H$
  have : b ∈ op b • (H : Set G) := by
    use 1
    simp only [SetLike.mem_coe, smul_eq_mul_unop, unop_op, one_mul, and_true]
    exact Subgroup.one_mem H
  --Hence $b \in H a$ and we are done
  rw [h]; exact this

example {G : Type*}[Group G](H : Subgroup G)(a b : G)(h : a • (H : Set G) = b • (H : Set G)) :
    op a⁻¹ • (H : Set G) =  op b⁻¹ • (H : Set G) := by
  --We have $a \in b H$ because
  have : a ∈ b • (H : Set G) := by
    --Only need to prove $a \ in a H$ as $a H = b H$
    rw [← h]
    --$a = a \cdot 1$ where $a \ in a H$ and so we are done
    use 1
    simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true]
    exact Subgroup.one_mem H
  --Hence we supposs $b g = a$
  rcases this with ⟨g, gin, hg⟩
  dsimp at hg
  --and we have $b ^ {-1} a = g \in H$ ,Hence $H a = H b$ and we are done
  refine (rightCoset_eq_iff H).mpr ?intro.intro.a
  rw [← hg]
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_left]
  exact gin

end Exercise_2294
