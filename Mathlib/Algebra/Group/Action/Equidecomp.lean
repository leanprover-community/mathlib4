import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Pointwise.Basic

variable {X G : Type*} {A B C: Set X}

open Function Set Pointwise

section SMul

variable [SMul G X]

--maybe this should be private? or have a better name?
def MovesBy (f : A → B) (S : Finset G) : Prop :=  ∀ a : A, ∃ g ∈ S, f a = g • (a : X)

variable (G)

structure Embeddidecomp (A B : Set X) where
    toFun : A → B
    injective' : Injective toFun
    moves_by : ∃ S : Finset G, MovesBy toFun S

structure Equidecomp (A B : Set X) extends A ≃ B where
    moves_by : ∃ S : Finset G, MovesBy toFun S

notation:50 A " ↪ₑ[" G:50 "] " B:50 => Embeddidecomp G A B
notation:50 A " ≃ₑ[" G:50 "] " B:50 => Equidecomp G A B

instance embeddidecompFunLike : FunLike (A ↪ₑ[G] B) A B where
  coe f:= f.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance embeddidecompEmbeddingLike : EmbeddingLike (A ↪ₑ[G] B) A B where
  injective' f:= f.injective'

instance equidecompEquivLike : EquivLike (A ≃ₑ[G] B) A B where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.toEquiv.left_inv
  right_inv f := f.toEquiv.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

theorem Embeddidecomp.def (f : A ↪ₑ[G] B) : ∃ S : Finset G, MovesBy f S := f.moves_by

theorem Equidecomp.def (f : A ≃ₑ[G] B) : ∃ S : Finset G, MovesBy f S := f.moves_by

variable {G}

def Equidecomp.embeddidecomp (f : A ≃ₑ[G] B) : A ↪ₑ[G] B where
  toFun := f
  injective' := EquivLike.injective f
  moves_by := f.moves_by

theorem MovesBy.mono {f : A → B} {S : Finset G} (h : MovesBy f S)
    {A' B': Set X} (hA' : A' ⊆ A) (hB' : B' ⊆ B) (f' : A' → B')
    (hf' : ∀ a : A', (inclusion hB') (f' a) = f (inclusion hA' a)) : MovesBy f' S := by
  intro a
  rcases h (inclusion hA' a) with ⟨g, gmem, hg⟩
  use g, gmem
  rw [coe_inclusion] at hg
  rw [← hg, ← hf', coe_inclusion]

noncomputable def Embeddidecomp.equidecompRange (f : A ↪ₑ[G] B) :
    A ≃ₑ[G] (range <| Subtype.val ∘ f) where
  toEquiv := Equiv.ofInjective (Subtype.val ∘ f) (Subtype.val_injective.comp f.injective')
  moves_by := by
    rcases f.moves_by with ⟨S, hS⟩
    refine ⟨S, hS.mono ?_ ?_ _ ?_⟩
    · rfl
    · refine (range_comp_subset_range _ _).trans ?_
      rw [Subtype.range_val]
    intro a
    simp only [Equiv.toFun_as_coe, Equiv.ofInjective_apply, comp_apply, Subtype.map_id, id_eq]
    rfl

--theorem recovering partition phrasing

end SMul

open scoped Classical

section Monoid

variable [Monoid G] [MulAction G X]

def Equidecomp.refl (A : Set X) : A ≃ₑ[G] A where
  toEquiv := Equiv.refl A
  moves_by := ⟨{1}, by simp [MovesBy]⟩

@[simp] theorem Equidecomp.coe_refl (A : Set X) : ↑(Equidecomp.refl A (G := G)) = id := rfl

theorem MovesBy.comp  {g : B → C} {f : A → B} {T S : Finset G}
    (hg : MovesBy g T) (hf : MovesBy f S) : MovesBy (g ∘ f) (T * S) := by
  intro a
  rcases hf a with ⟨γ, γ_mem, hγ⟩
  rcases hg (f a) with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rw [mul_smul, ← hγ, ← hδ]
  rfl

def Embeddidecomp.trans (f : A ↪ₑ[G] B) (g : B ↪ₑ[G] C) : A ↪ₑ[G] C where
  toFun := g ∘ f
  injective' := g.injective'.comp f.injective'
  moves_by := by
    rcases f.moves_by with ⟨S, hS⟩
    rcases g.moves_by with ⟨T, hT⟩
    exact ⟨T * S, hT.comp hS⟩

def Equidecomp.trans (f : A ≃ₑ[G] B) (g : B ≃ₑ[G] C) : A ≃ₑ[G] C where
  toEquiv := f.toEquiv.trans g.toEquiv
  moves_by := by
    rcases f.moves_by with ⟨S, hS⟩
    rcases g.moves_by with ⟨T, hT⟩
    exact ⟨T * S, hT.comp hS⟩

@[simp] theorem Embeddidecomp.coe_trans (f : A ↪ₑ[G] B) (g : B ↪ₑ[G] C) : ↑(f.trans g) = g ∘ f
  := rfl

@[simp] theorem Equidecomp.coe_trans (f : A ≃ₑ[G] B) (g : B ≃ₑ[G] C) : ↑(f.trans g) = g ∘ f := rfl

end Monoid

section Group

variable [Group G] [MulAction G X]

theorem MovesBy.of_rightInverse {f : A → B} {g : B → A} {S : Finset G}
    (hf : MovesBy f S) (h : RightInverse g f) : MovesBy g S⁻¹ := by
  intro b
  rcases hf (g b) with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  apply smul_left_cancel γ
  rw [smul_inv_smul, ← hγ, h]

def Equidecomp.symm (f : A ≃ₑ[G] B) : B ≃ₑ[G] A where
  toEquiv := f.toEquiv.symm
  moves_by := by
    rcases f.moves_by with ⟨S, hS⟩
    refine ⟨S⁻¹, hS.of_rightInverse <| Equiv.right_inv' _⟩

end Group
