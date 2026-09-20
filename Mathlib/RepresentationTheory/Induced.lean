/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Induced representations

Given a commutative ring `k`, a group homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the induced representation $Ind_G^H(A)$ of `A` as
an `H`-representation.

By `ind φ A` we mean the `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
We define a representation of `H` on this submodule by sending `h : H` and `⟦h₁ ⊗ₜ a⟧` to
`⟦h₁h⁻¹ ⊗ₜ a⟧`.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is right adjoint to the
induction functor and hence that the induction functor preserves colimits.

Additionally, we show that the functor `Rep k H ⥤ ModuleCat k` sending `B : Rep k H` to
`(Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B` to `(A ⊗ Res(φ)(B))_G`. This
is used to prove Shapiro's lemma in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Shapiro.lean`.

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.
* `Rep.coinvariantsTensorIndNatIso φ A` : given a group homomorphism `φ : G →* H` and
  `A : Rep k G`, this is a natural isomorphism between the functor sending `B : Rep k H` to
  `(Ind(φ)(A) ⊗ B))_H` and the one sending `B` to `(A ⊗ Res(φ)(B))_G`. Used to prove Shapiro's
  lemma.

-/

@[expose] public section

open Representation

universe t w w' u u' v v'

namespace Representation

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] (ρ : Representation k G A)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
See `Representation.ind` for the induced `H`-representation on `indV φ ρ`. -/
@[implicit_reducible]
def indV := Coinvariants (tprod ((leftRegular k H).comp φ) ρ)

noncomputable instance : AddCommGroup (indV φ ρ) := inferInstanceAs <|
  AddCommGroup (Coinvariants (tprod ((leftRegular k H).comp φ) ρ))

noncomputable instance : Module k (indV φ ρ) := inferInstanceAs <|
  Module k (Coinvariants (tprod ((leftRegular k H).comp φ) ρ))

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`. -/
noncomputable def indV.mk (h : H) : A →ₗ[k] indV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext]
lemma indV.hom_ext {f g : indV φ ρ →ₗ[k] B}
    (hfg : ∀ h : H, f ∘ₗ indV.mk φ ρ h = g ∘ₗ indV.mk φ ρ h) : f = g :=
  Coinvariants.hom_ext <| TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun h =>
    LinearMap.ext_ring <| hfg h

variable {φ ρ} in
@[elab_as_elim]
lemma indV.inductionOn {p : indV φ ρ → Prop} (v : indV φ ρ) (mk : ∀ h a, p (indV.mk φ ρ h a))
    (add : ∀ x y : indV φ ρ, p x → p y → p (x + y)) : p v := by
  refine Coinvariants.induction_on v fun w => ?_
  refine w.inductionOn (fun m a => ?_) (fun _ _ hx hy => by simpa [map_add] using add _ _ hx hy)
  refine m.induction_linear (by simpa using mk 1 0) ?_ ?_
  · exact fun _ _ hx hy => by simpa [TensorProduct.add_tmul, map_add] using add _ _ hx hy
  · intro h r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', TensorProduct.smul_tmul]
    exact mk h (r • a)

@[simp]
lemma indV.mk_map_mul (g : G) (h : H) (a : A) :
    indV.mk φ ρ ((φ g) * h) a = indV.mk φ ρ h (ρ g⁻¹ a) := by
  simp [mk, Coinvariants.mk_tmul_inv (g := g)]

@[simp]
lemma indV.mk_map_inv_mul (g : G) (h : H) (a : A) :
    indV.mk φ ρ ((φ g)⁻¹ * h) a = indV.mk φ ρ h (ρ g a) := by
  simp [← map_inv]

@[simp]
lemma indV.mk_map_eq (g : G) (a : A) :
    indV.mk φ ρ (φ g) a = indV.mk φ ρ 1 (ρ g⁻¹ a) := by
  simpa using indV.mk_map_mul φ ρ g 1 a

@[simp]
lemma indV.mk_map_inv_eq (g : G) (a : A) :
    indV.mk φ ρ (φ g)⁻¹ a = indV.mk φ ρ 1 (ρ g a) := by
  simp [← map_inv]

/-- Construct a linear map `indV φ ρ →ₗ[k] B` from a compatible family of linear maps
`f : H → A →ₗ[k] B`, whose composition with `indV.mk φ ρ h : A →ₗ[k] indV φ ρ` is `f h`. -/
noncomputable def indV.lift (f : H → A →ₗ[k] B)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    indV φ ρ →ₗ[k] B :=
  Coinvariants.lift _ (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => f h) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by ext; simp [hf]

@[simp]
lemma indV.lift_apply_mk (f : H → A →ₗ[k] B) (h : H) (a : A)
    (hf : ∀ (g : G) (h : H) (a : A), f (φ g * h) a = f h (ρ g⁻¹ a)) :
    lift φ ρ f hf (mk φ ρ h a) = f h a := by
  simp [lift, mk, Coinvariants.lift_mk (tprod (MonoidHom.comp (leftRegular k H) φ) ρ)]

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
@[simps -isSimp]
noncomputable def ind : Representation k H (indV φ ρ) where
  toFun h := indV.lift φ ρ (fun x => indV.mk φ ρ (x * h⁻¹)) (by simp [mul_assoc])
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
lemma ind_apply_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (indV.mk _ _ h₂ a) = indV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp [ind]

@[deprecated (since := "2026-09-19")] alias ind_mk := ind_apply_mk

lemma ind_conj_map_apply (g : G) (h : H) (a : A) :
    ind φ ρ (h⁻¹ * (φ g) * h) (indV.mk _ _ h a) = indV.mk _ _ h (ρ g a) := by
  simp

variable {ρ : Representation k G A} {σ : Representation k H B} {τ : Representation k G B}

/-- Construct an `IntertwiningMap` starting from an induced representation by lifting an
`IntertwiningMap` with a `res` representation as target. -/
noncomputable def ind.lift (f : IntertwiningMap ρ (σ.comp φ)) :
    (ind φ ρ).IntertwiningMap σ :=
  ⟨indV.lift φ ρ (fun h => σ h⁻¹ ∘ₗ f) (by simp [f.isIntertwining]), fun g => by ext; simp⟩

@[simp]
lemma ind.lift_apply_mk (f : ρ.IntertwiningMap (σ.comp φ)) (h : H) (a : A) :
    ind.lift φ f (indV.mk φ ρ h a) = σ h⁻¹ (f a) := by
  simp [ind.lift]

/-- The canonical equivariant map from a representation to the restriction of its induction. -/
noncomputable def ind.unit (ρ : Representation k G A) :
    ρ.IntertwiningMap ((ind φ ρ).comp φ) := ⟨indV.mk φ ρ 1, fun g => by ext; simp⟩

@[simp]
lemma ind.unit_apply (a : A) : ind.unit φ ρ a = indV.mk φ ρ 1 a := rfl

/-- Evaluate the induction of a restricted representation using its original group action. -/
noncomputable def ind.counit (σ : Representation k H B) :
    (ind φ (σ.comp φ)).IntertwiningMap σ :=
  ind.lift φ (IntertwiningMap.id (σ.comp φ))

@[simp]
lemma ind.counit_apply_mk (h : H) (b : B) :
    ind.counit φ σ (indV.mk φ (σ.comp φ) h b) = σ h⁻¹ b := by simp [ind.counit]

/-- Restrict an equivariant map out of an induced representation to the generators at `1`. -/
noncomputable def ind.evalOne (f : (ind φ ρ).IntertwiningMap σ) : ρ.IntertwiningMap (σ.comp φ) :=
  ⟨f.toLinearMap ∘ₗ indV.mk φ ρ 1 , fun _ => by ext; simp [← f.isIntertwining]⟩

@[simp]
lemma ind.evalOne_apply (f : (ind φ ρ).IntertwiningMap σ) (a : A) :
    ind.evalOne φ f a = f (indV.mk φ ρ 1 a) := rfl

/-- An equivariant map from an induced representation is determined by the generators at `1`. -/
@[ext]
lemma ind.hom_ext {f g : (ind φ ρ).IntertwiningMap σ}
    (hfg : ∀ a, f (indV.mk φ ρ 1 a) = g (indV.mk φ ρ 1 a)) : f = g := by
  ext h a
  simpa [← IntertwiningMap.isIntertwining] using congrArg (fun x => σ h⁻¹ x) (hfg a)

/-- The universal property of induction, without bundled representation objects. -/
noncomputable def indResHomEquiv (ρ : Representation k G A) (σ : Representation k H B) :
    (ind φ ρ).IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap (σ.comp φ) where
  toFun := ind.evalOne φ
  invFun := ind.lift φ
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma indResHomEquiv_apply (f : (ind φ ρ).IntertwiningMap σ) (a : A) :
    indResHomEquiv φ ρ σ f a = f (indV.mk φ ρ 1 a) := rfl

@[simp]
lemma indResHomEquiv_symm_apply_mk (f : ρ.IntertwiningMap (σ.comp φ)) (h : H) (a : A) :
    (indResHomEquiv φ ρ σ).symm f (indV.mk φ ρ h a) = σ h⁻¹ (f a) :=
  ind.lift_apply_mk φ f h a

noncomputable def indMap (f : IntertwiningMap ρ τ) :
    (ind φ ρ).IntertwiningMap (ind φ τ) :=
  ind.lift φ ⟨indV.mk φ τ 1 ∘ₗ f, fun g => by ext; simp [IntertwiningMap.isIntertwining]⟩

@[simp]
lemma indMap_apply_mk (f : ρ.IntertwiningMap τ) (h : H) (a : A) :
    indMap φ f (indV.mk φ ρ h a) = indV.mk φ τ h (f a) := by simp [indMap]

end Representation

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

section Ind

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/-- Given a group homomorphism `φ : G →* H`, a morphism of `G`-representations `f : A ⟶ B` induces
a morphism of `H`-representations `(k[H] ⊗[k] A)_G ⟶ (k[H] ⊗[k] B)_G`. -/
noncomputable abbrev indMap {A B : Rep k G} (f : A ⟶ B) :
    ind φ A ⟶ ind φ B := Rep.ofHom <| A.ρ.indMap φ f.hom

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[implicit_reducible, simps obj map]
noncomputable def indFunctor : Rep.{w} k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

end Ind

section Adjunction

/-- Given a group homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `H`-representation morphisms `ind φ A ⟶ B` and
the `G`-representation morphisms `A ⟶ res φ B`. -/
noncomputable def indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) :=
(homLinearEquiv _ B).trans <| (A.ρ.indResHomEquiv φ B.ρ).trans (homLinearEquiv A (res φ B)).symm

@[simp]
lemma indResHomEquiv_apply_hom (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H)
    (f : ind φ A ⟶ B) :
    (indResHomEquiv φ A B f).hom = Representation.ind.evalOne φ f.hom := rfl

@[simp]
lemma indResHomEquiv_symm_apply_hom (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H)
    (f : A ⟶ res φ B) :
    (show ind φ A ⟶ B from (indResHomEquiv φ A B).symm f).hom = ind.lift φ f.hom := rfl

/-- Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k H` is left
adjoint to the restriction functor along `φ`. -/
noncomputable def indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B := (indResHomEquiv.{w} φ A B).toEquiv
      homEquiv_naturality_left_symm f g := by simp only [indFunctor_obj]; ext; simp
      homEquiv_naturality_right f g := by ext; simp }

@[simp]
lemma indResAdjunction_unit_app_hom (A : Rep.{max w v' u} k G) :
    (show A ⟶ (A.ind φ).res φ  from (indResAdjunction φ).unit.app A).hom = ind.unit φ A.ρ := rfl

@[simp]
lemma indResAdjunction_counit_app_hom (B : Rep.{max w v' u} k H) :
    (show (B.res φ).ind φ ⟶ B from (indResAdjunction φ).counit.app B).hom = ind.counit φ B.ρ := rfl

@[simp]
lemma indResAdjunction_homEquiv :
    (indResAdjunction φ (k := k)).homEquiv = fun A B => (indResHomEquiv φ A B).toEquiv :=
  Adjunction.mkOfHomEquiv_homEquiv _

noncomputable instance : (indFunctor.{max u v' w} k φ).IsLeftAdjoint :=
  (indResAdjunction φ).isLeftAdjoint

noncomputable instance : (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint :=
  (indResAdjunction φ).isRightAdjoint

end Adjunction

variable {G H : Type u} [Group G] [Group H] (φ : G →* H) (A : Rep k G) (B : Rep k H)

/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧` for all
`h : H`, `a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndHom :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ⟶
      ((coinvariantsTensor k G).obj A).obj (res φ B) :=
  ModuleCat.ofHom <| Coinvariants.lift _
    (TensorProduct.lift <| indV.lift φ A.ρ
      (fun h => (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ h))
      (fun g h a => by ext; simp [coinvariantsTensorMk]))
    (fun h => by
        simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V]
        ext; simp)

variable {A B} in
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (Coinvariants.mk ((Representation.ind φ A.ρ).tprod B.ρ)
      ((indV.mk φ _ h x) ⊗ₜ[k] y)) = Coinvariants.mk (A.ρ.tprod (res φ B).ρ) (x ⊗ₜ[k] (B.ρ h y))
  := by simp [coinvariantsTensorIndHom]

/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` for all
`a : A`, and `b : B`. -/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj (res φ B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ indV.mk _ _ 1) fun s ↦ by
      simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V]
      ext x y
      simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff] using Coinvariants.mem_ker_of_eq (φ s)
        ((indV.mk φ A.ρ (1 : H) x) ⊗ₜ[k] y) _ (by simp)

variable {A B} in
lemma coinvariantsTensorIndInv_mk_tmul_indVMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk (A.ρ.tprod (res φ B).ρ) (x ⊗ₜ y)) =
      Coinvariants.mk ((Representation.ind φ A.ρ).tprod B.ρ) ((indV.mk φ _ 1 x) ⊗ₜ[k] y) := by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

@[deprecated (since := "2026-09-19")]
alias coinvariantsTensorIndInv_mk_tmul_indMk := coinvariantsTensorIndInv_mk_tmul_indVMk

/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`. -/
@[simps]
noncomputable def coinvariantsTensorIndIso :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ≅
      ((coinvariantsTensor k G).obj A).obj (res φ B) where
  hom := coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext
    simp [coinvariantsTensorIndInv_mk_tmul_indVMk φ, coinvariantsTensorIndHom_mk_tmul_indVMk φ,
      ← Coinvariants.mk_inv_tmul]
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv_mk_tmul_indVMk φ, coinvariantsTensorIndHom_mk_tmul_indVMk φ]

/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom_mk_tmul_indVMk φ, hom_comm_apply]

end Rep
