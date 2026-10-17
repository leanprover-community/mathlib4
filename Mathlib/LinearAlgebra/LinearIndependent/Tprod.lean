import Mathlib

set_option linter.style.longLine false

open TensorProduct

class DualSeparated (R M : Type*) [CommSemiring R] [AddCommGroup M] [Module R M] : Prop where
    separatesPoints (R M) (x y : M) : (∀ u : Module.Dual R M, u x = u y) → x = y

--we may also need finiteness here.
instance (R M : Type*) [CommSemiring R] [AddCommGroup M] [Module R M] [Module.Free R M] :
    DualSeparated R M where
      separatesPoints := sorry


variable {R M N : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Pointwise

lemma Finsupp.curry_sum {α : Type*} {β : Type*} {M : Type*}
  [AddCommMonoid M] (f g : α × β →₀ M) : (f + g).curry = f.curry + g.curry := by
  ext a a
  simp [curry_apply, coe_add, Pi.add_apply]

lemma Finsupp.curry_single {α : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] (x : α × β) (y : M) :
    (fun₀ | x => y).curry =  (fun₀ | x.fst => fun₀ | x.snd => y) := by
  --TODO: this proof should be shorter!
  ext u v
  by_cases H : (u, v) = (x.1, x.2)
  · simp [H, Prod.mk_inj.mp H]
  · obtain h | ⟨rfl, h⟩ : (u ≠ x.1) ∨ ((u = x.1) ∧ v ≠ x.2) := by
      rw [Prod.eq_iff_fst_eq_snd_eq, not_and] at H
      by_cases Hu : u = x.1
      · right; exact ⟨Hu, H Hu⟩
      · left; exact Hu
    · classical simp [Finsupp.single_apply, h.symm, (Ne.symm H)]
    · classical simp only [curry_apply, single_apply, single_eq_same, ne_eq, h.symm, if_true,
         if_false]
      rw [ite_cond_eq_false]
      simp [← Prod.snd_eq_iff, h.symm]

@[simp]
lemma Finsupp.curry_zero {α : Type*} {β : Type*} {M : Type*} [AddCommMonoid M] :
    (0 : α × β →₀ M).curry = 0 := by
  rfl

lemma Finsupp.sum_curry_apply {α : Type*} {β : Type*} {M N : Type*}
  [AddCommMonoid M] [AddCommMonoid N] (f : α × β →₀ M) (x : α)  :
    (f.curry x).sum (fun _ b => b) = (Finsupp.mapDomain Prod.fst) f x := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f hb hf hind =>
    rw [Finsupp.curry_sum, Finsupp.add_apply]
    have :=Finsupp.sum_hom_add_index (f := (fun₀ | a => b).curry x)
      (g:= f.curry x) (h := fun a => (.id M  : M →+ M)) (M := M) (N := M)
    simp only [AddMonoidHom.coe_id] at this
    rw [show (fun (a : β) => (id : M → M)) = fun (a : β) (b : M) ↦ b by ext; simp] at this
    rw [this, hind, Finsupp.mapDomain_add]
    · congr
      rw [Finsupp.mapDomain_single,  Finsupp.curry_single]
      by_cases H : a.1 ≠ x
      · simp [H]
      · classical rw [Finsupp.single_apply]
        simp [of_not_not H]

@[simp]
lemma Finsupp.fun_smul_single {α : Type*} {β : Type*} [Semiring β] (f : α → β) (a : α) (b : β) :
    f • (fun₀ | a => b) = fun₀ | a => f a * b := by
  ext x
  by_cases hx : a = x  <;> simp [hx]

lemma Finsupp.sum_curry_apply' {α : Type*} {β : Type*} {R : Type*} [Semiring R]
  (f : α × β →₀ R) (g : β → R) (x : α)  :
    (f.curry x).sum (fun b m => g b * m) = (Finsupp.mapDomain Prod.fst)
      ((fun (ab : α × β) => g ab.snd) • f) x := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f hb hf hind =>
    rw [Finsupp.curry_sum, Finsupp.add_apply]
    have := Finsupp.sum_hom_add_index (f := (fun₀ | a => b).curry x)
      (g:= f.curry x) (h := fun b => g b • (.id R : R →+ R))
    simp only [AddMonoidHom.coe_smul, AddMonoidHom.coe_id] at this
    rw [show (fun b => g b • id : β → R → R) = fun (b : β) (a : R) ↦ g b * a by ext; simp] at this
    rw [this, hind]
    simp only [smul_eq_mul, smul_add]
    rw [Finsupp.mapDomain_add]
    · congr
      rw [Finsupp.fun_smul_single]
      rw [Finsupp.mapDomain_single,  Finsupp.curry_single]
      by_cases H : a.1 ≠ x
      · simp [H]
      · classical rw [Finsupp.single_apply]
        simp [of_not_not H]

@[simp]
theorem sum_hom_add_index'' {α F : Type*} {M N : Type*} [AddZeroClass M] [AddCommMonoid N]
     {f g : α →₀ M}  [FunLike F M N] [AddMonoidHomClass F M N] (h : α → F) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x := by
  have : (fun x ↦ ⇑(h x)) = fun x ↦ ⇑(AddMonoidHomClass.toAddMonoidHom (h x : F)) := rfl
  rw [this, Finsupp.sum_hom_add_index]

lemma Finsupp.function_smul_sum {α : Type*} {M N : Type*} [CommSemiring N]
    [AddCommMonoid M] [Module N M]
    (f : α →₀ N) (g : α → N) (h : α → N →ₗ[N] M) :
    (g • f).sum (fun a => h a) = f.sum (g • fun a => ⇑(h a)) := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f hb hf hind =>
    set v : α → N →ₗ[N] M := fun a ↦ ((DistribMulAction.toLinearMap N M (g a))).comp (h a) with hv
    have : (g • fun a ↦ ⇑(h a)) = fun a => ⇑(v a) := by ext; simp [hv]
    simp only [smul_add, fun_smul_single, sum_hom_add_index, sum_hom_add_index'', this, hind]
    simp only [hv, LinearMap.coe_comp, Function.comp_apply, map_zero, ←smul_eq_mul, (h a).map_smul,
      DistribMulAction.toLinearMap_apply, smul_zero, sum_single_index]

theorem Finsupp.sum_mapDomain_index_addMonoidHomClass {α β M N F : Type*}
    [AddCommMonoid M] [AddCommMonoid N] {f : α → β} {s : α →₀ M} (h : β → F) [FunLike F M N]
      [AddMonoidHomClass F M N] :
    ((mapDomain f s).sum fun (b : β) (m : M) => (h b) m) = s.sum fun (a : α) (m : M) => (h (f a)) m := by
  have (b : β) (m : M) : (h b) m = (AddMonoidHomClass.toAddMonoidHom <| h b) m := by rfl
  simp_rw [this, Finsupp.sum_mapDomain_index_addMonoidHom]

-- lemma Finsupp.smul_mapDomain {α β M : Type*} [Semiring M] (f : α → β)
--     (v : α →₀ M) (g : β → M) :
--     ((g ∘ f) • v).mapDomain f = g • v.mapDomain f := by
--   sorry

protected lemma LinearIndependent.tmul {ι κ : Type*} {f : ι → M} {g : κ → N} [DualSeparated R M]
    [DualSeparated R N]
    (hf : LinearIndependent R f) (hg : LinearIndependent R g)  :
    LinearIndependent R (fun ik : ι × κ ↦ f ik.1 ⊗ₜ[R] g ik.2) := by
  rintro μ ρ hμρ
  set x := (Finsupp.linearCombination R fun ik ↦ f ik.1 ⊗ₜ[R] g ik.2) μ with hx
  set y := (Finsupp.linearCombination R fun ik ↦ f ik.1 ⊗ₜ[R] g ik.2) ρ with hy
  have (u : Module.Dual R M) (v : Module.Dual R N) :
      dualDistrib R M N (u ⊗ₜ v) x = TensorProduct.dualDistrib R M N (u ⊗ₜ v) y := by
    rw [hμρ]
  have (u : Module.Dual R M) (v : Module.Dual R N) :
    u (μ.sum fun ik => ⇑(LinearMap.smulRight (DistribMulAction.toLinearMap R R (v (g ik.snd))) (f ik.fst)))
      = u (ρ.sum fun ik => ⇑(LinearMap.smulRight (DistribMulAction.toLinearMap R R (v (g ik.snd))) (f ik.fst))) := by
    have := this u v
    rw [hx, hy, LinearMap.map_finsupp_linearCombination, LinearMap.map_finsupp_linearCombination] at this
    calc u (μ.sum fun ⟨i, k⟩ a => (v (g k) * a) • (f i))
        = (Finsupp.linearCombination R (fun ik => ((dualDistrib R M N) (u ⊗ₜ v)) (f ik.1 ⊗ₜ g ik.2))) μ := by
          simp only [dualDistrib_apply, Finsupp.linearCombination_apply, map_finsuppSum]
          congr
          ext a b
          simp only [map_smul, smul_eq_mul]
          ring
      _ = (Finsupp.linearCombination R (fun ik => ((dualDistrib R M N) (u ⊗ₜ v)) (f ik.1 ⊗ₜ g ik.2))) ρ := by
          convert this
      _ = u (ρ.sum fun ⟨i, k⟩ a => (v (g k) * a) • (f i)) := by
          simp only [dualDistrib_apply, Finsupp.linearCombination_apply, map_finsuppSum]
          congr
          ext a b
          simp only [map_smul, smul_eq_mul]
          ring
  have (v : Module.Dual R N) :
    ((((fun (ik : ι × κ) => v (g ik.snd)) • μ).mapDomain Prod.fst).sum fun i =>
      ⇑(LinearMap.smulRight (LinearMap.id (R := R)) (f i)))
      = ((((fun (ik : ι × κ) => v (g ik.snd)) • ρ).mapDomain Prod.fst).sum fun i =>
        ⇑(LinearMap.smulRight (LinearMap.id (R := R)) (f i))) := by
    apply DualSeparated.separatesPoints R M
    intro u
    have := this u v
    have funeq : ((fun (ik : ι × κ) ↦ v (g ik.snd)) • fun (a : ι × κ) ↦
      ⇑((LinearMap.id : R →ₗ[R] R).smulRight (f a.1))) = fun (ik : ι × κ) ↦
        ⇑((DistribMulAction.toLinearMap R R (v (g ik.2))).smulRight (f ik.1)) := by
      ext ik
      simp_rw [Pi.smul_apply', LinearMap.coe_smulRight, LinearMap.id_apply,
        DistribMulAction.toLinearMap_apply, Pi.smul_def, smul_assoc]
    rw [Finsupp.sum_mapDomain_index_addMonoidHomClass, Finsupp.sum_mapDomain_index_addMonoidHomClass,
    Finsupp.function_smul_sum, Finsupp.function_smul_sum, funeq, this]
  have (v : Module.Dual R N) (i : ι) :
    ((μ.curry i).sum fun k => ⇑(LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) (v (g k))))
      = (ρ.curry i).sum fun k => ⇑(LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) (v (g k))) := by
    specialize hf (this v)
    rw [Finsupp.ext_iff] at hf
    specialize hf i
    simp_rw [← Finsupp.sum_curry_apply' _ (fun k ↦ v (g k))] at hf
    convert hf <;> simp [funext_iff, LinearMap.coe_smulRight, mul_comm, LinearMap.smulRight_apply]
  have (v : Module.Dual R N) (i : ι) : v ((μ.curry i).sum fun k =>
      ⇑(LinearMap.smulRight (LinearMap.id (R := R)) (g k)))
        = v ((ρ.curry i).sum fun k => ⇑(LinearMap.smulRight (LinearMap.id (R := R)) (g k))) := by
    simpa [map_finsuppSum, map_finsuppSum, mul_comm] using this v i
  have (i : ι) : ((μ.curry i).sum fun k a => a • (g k)) =  ((ρ.curry i).sum fun k a => a • (g k)) :=
    DualSeparated.separatesPoints R N _ _ <| fun _ => this _ i
  have (i : ι) (k : κ) : ((μ.curry i k)) = ((ρ.curry i k)) := by
    have := this i
    rw [← Finsupp.linearCombination_apply, ← Finsupp.linearCombination_apply] at this
    rw [hg this]
  ext ⟨i, k⟩
  simpa using this i k
