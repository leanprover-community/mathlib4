import Mathlib.InformationTheory.Code.Linear.Mathieu.BGolay
import Mathlib.InformationTheory.Code.Linear.Mathieu.Hexads_two

namespace GolayCode

abbrev weird_aut' (x: golay_code_space') : golay_code_space' :=
  to_gc !![x (0,0), x (1,0), x (2,0), x (3,0), x (5,1), x (4,1);
           x (0,1), x (1,1), x (2,1), x (3,1), x (5,0), x (4,0);
           x (1,ω), x (0,ω), x (3,ω), x (2,ω), x (4,ω⁻¹), x (5,ω⁻¹);
           x (1,ω⁻¹), x (0,ω⁻¹), x (3,ω⁻¹), x (2,ω⁻¹), x (4,ω), x (5,ω)]

def weird_aut_index_perm' : golay_code_index → golay_code_index := fun
  | .mk i x =>
    if x = 0 ∨ x = 1 then
      if i < 4 then
        ⟨i,x⟩
      else if i = 4 then
        ⟨5,1 + x⟩
      else
        ⟨4,1 + x⟩
    else
      if 4 ≤ i then
        ⟨i,x⁻¹⟩
      else if i = 0 ∨ i = 2 then
        ⟨i+1,x⟩
      else
        ⟨i-1,x⟩

lemma weird_aut_index_perm'_self_inv (c:golay_code_index):
    weird_aut_index_perm' (weird_aut_index_perm' c) = c := by
  dsimp [weird_aut_index_perm']
  simp only [Fin.isValue, Prod.mk.eta]
  fin_cases c <;> decide

def weird_aut_index_perm : golay_code_index ≃ golay_code_index where
  toFun := weird_aut_index_perm'
  invFun := weird_aut_index_perm'
  left_inv := weird_aut_index_perm'_self_inv
  right_inv := weird_aut_index_perm'_self_inv

@[simps]
def weird_aut'' : golay_code_space' ≃ golay_code_space' where
  toFun := fun x => x ∘ weird_aut_index_perm
  invFun := fun x => x ∘ ⇑(weird_aut_index_perm⁻¹)
  left_inv := fun x => by
    ext i
    simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]
  right_inv := fun x => by
    ext i
    simp only [Function.comp_apply, Equiv.Perm.inv_apply_self]

@[simps]
def weird_aut_lin : golay_code_space' ≃ₗ[ZMod 2] golay_code_space' := {
  weird_aut'' with
  map_add' := fun x y => by
    ext i
    simp only [Pi.add_apply]
    fin_cases i <;> rfl
  map_smul' := fun r x => by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> rfl
}

lemma weird_aut_lin_map_code ⦃x:golay_code_space'⦄ (hx : x ∈ GolayCode):
    weird_aut_lin x ∈ GolayCode := by
  rw [gc_span_is_gc.symm] at hx
  refine Submodule.span_induction hx ?basis ?zero ?add ?smul
  . simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
    Set.union_insert, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    decide
  . decide
  . intro x y hx hy
    rw [map_add]
    exact add_mem hx hy
  . intro r x hx
    rw [weird_aut_lin.map_smul]
    exact GolayCode.smul_mem r hx

lemma weird_aut_lin_auto_symm (x:golay_code_space'): weird_aut_lin (weird_aut_lin x) = x := by
  ext i
  fin_cases i <;> rfl

def golay_aut_of_index_perm (σ : Equiv.Perm golay_code_index) (hmap_code :
  ∀ x ∈ GolayCode, x ∘ ⇑σ⁻¹ ∈ GolayCode) : LinearCodeAut (ZMod 2) trivdist hdist GolayCode where
    toFun := fun x => x ∘ ⇑σ⁻¹
    map_add' := fun x y => by
      ext i
      simp only [Function.comp_apply, Pi.add_apply]
    map_smul' := fun r m => by
      ext i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    invFun := fun x => x ∘ ⇑σ
    left_inv := fun x => by
      ext i
      simp only [Function.comp_apply, Equiv.Perm.inv_apply_self]
    right_inv := fun x => by
      ext i
      simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]
    map_dist := fun x y => by
      sorry
    map_code := fun x hx => by
      simp only [SetLike.mem_coe]
      exact hmap_code x hx
    invMap_code := fun x hx => by
      simp only [SetLike.mem_coe]
      simp only [SetLike.mem_coe] at hx
      suffices (. ∘ ⇑σ) '' GolayCode = (GolayCode : Set golay_code_space') by
        rw [Set.ext_iff] at this
        specialize this x
        simp only [Set.mem_image, SetLike.mem_coe] at this
        rw [this.symm]
        use x ∘ ⇑σ⁻¹, hx
        ext i
        simp only [Function.comp_apply, Equiv.Perm.inv_apply_self]
      symm
      letI : ∀ s :Set golay_code_space', Fintype s := by exact fun s ↦ Fintype.ofFinite ↑s
      apply Set.eq_of_subset_of_card_le
      . intro y hy
        simp only [SetLike.mem_coe, Set.mem_image] at hy ⊢
        use y ∘ ⇑σ⁻¹, hmap_code y hy
        ext i
        simp only [Function.comp_apply, Equiv.Perm.inv_apply_self]
      . apply Eq.le
        simp only [SetLike.coe_sort_coe]
        rw [Fintype.card_eq]
        apply Nonempty.intro
        refine Set.BijOn.equiv ?hcard.a.val.f ?hcard.a.val.h
        . exact fun x => x ∘ ⇑σ⁻¹
        . dsimp [Set.BijOn]
          simp only [Set.mapsTo_image_iff]
          repeat' constructor
          . intro x hx
            simp only [SetLike.mem_coe, Function.comp_apply] at hx ⊢
            suffices (x ∘ ⇑σ) ∘ ⇑σ⁻¹ = x by
              rw [this]
              exact hx
            ext i
            simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]
          . intro x hx y hy
            simp only [Set.mem_image, SetLike.mem_coe] at hx hy
            simp only
            obtain ⟨x',hx',rfl⟩ := hx
            obtain ⟨y',hy',rfl⟩ := hy
            intro h
            rw [Function.funext_iff] at h
            simp only [Function.comp_apply, Equiv.Perm.apply_inv_self] at h
            ext c
            simp only [Function.comp_apply]
            rw [h]
          . intro x hx
            simp only [SetLike.mem_coe, Set.mem_image, exists_exists_and_eq_and] at hx ⊢
            use x, hx
            ext i
            simp only [Function.comp_apply, Equiv.Perm.apply_inv_self]

def weird_aut : LinearCodeAut (ZMod 2) trivdist hdist GolayCode := {
  weird_aut_lin with
  map_dist := fun x y => by
    simp only
    dsimp [weird_aut_lin,weird_aut'']
    simp only [Nat.cast_inj]
    dsimp [hammingDist]
    apply Finset.card_bij (fun x _ => weird_aut_index_perm⁻¹ x)
    . simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.apply_inv_self, imp_self,
      implies_true]
    . simp only [Finset.mem_filter, Finset.mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq,
      imp_self, implies_true]
    . simp only [Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
      intro b hb
      use weird_aut_index_perm b
      simp only [Equiv.Perm.inv_apply_self, and_true]
      exact hb
  map_code := by
    simp only [SetLike.mem_coe, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    intro x hx
    exact weird_aut_lin_map_code hx
  invMap_code := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, SetLike.mem_coe]
    intro x hx
    rw [← weird_aut_lin_auto_symm x]
    exact weird_aut_lin_map_code hx
}

#check GolayCode.rep1_val


lemma weird_aut_map_repr1_val_repr2 :
  (Sextet.mk' (weird_aut rep1_val) (by sorry)) ∈ orbit2 := sorry

/-
(2^6 ⋊ 3)•S₆? (2^6) ⋊ (3 • S₆)?
fancygroup is generated by:
- ![0,1,0,1,ω,ω⁻¹] : Fin 6 → F4
- ⟨(1,2,3,4,5), ![↑ω,1,↑ω⁻¹,↑ω,?,1]⟩ : LinearCodeAut ...
- ⟨(5,6), 1⟩ ∘ (λ x. x⁻¹) : GolayCode ≃ₛₗc[(λ x. x⁻¹)]


to extend to M₂₄ :
- apply ⟨(1,2)(3,4),1⟩, then apply
  λ ⟨i,x⟩, ⟨if i ∈ {5,6} then (5,6) i else i,if i ∈ {5,6} then x + 1 else x⟩

turns out, M₂₄ is 5-transitive on (Fin 6) × F4

take subgroups to other groups:
- Stabiliser of a single point, (Fin 6) × F4: M₂₃
- Stabiliser of two points: M₂₂
- Stabiliser of three points: M₂₁ ≃* PSL₃(4)
  (the remaining 21 points form a projective plane of order 4)


lemma : M₂₄ acts transitively on words of weight 12 (dodecad)

- Stabiliser of a dodecad in GolayCode : M₁₂


- Fix a dodecad, and a point in it: M₁₁
-/
