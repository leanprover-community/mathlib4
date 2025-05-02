import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow




open Classical
open Pointwise


variable {p : ℕ} [Fact p.Prime](pp : Nat.Prime p)
variable {G : Type} [Group G] [Fintype G] [Fintype (Sylow p G)]

lemma card_eq_subtype_self (N : Subgroup G) (Q : Subgroup ↥N) : Fintype.card (Q.map N.subtype) = Fintype.card Q :=
  have : (Q.map N.subtype) ≃* Q := by
    apply (Q.equivMapOfInjective N.subtype _).symm
    exact Subgroup.subtype_injective N
  Fintype.card_eq.mpr (Nonempty.intro this.toEquiv)

lemma card_eq_inf (N : Subgroup G) : Fintype.card (N ⊓ P : Subgroup G) = Fintype.card ((N ⊓ ↑P).subgroupOf N) :=
    have : (N ⊓ P : Subgroup G) ≃* (N ⊓ P).subgroupOf N :=
      have : N ⊓ P ≤ N := inf_le_left
      (Subgroup.subgroupOfEquivOfLe this).symm
    Fintype.card_eq.mpr (Nonempty.intro this.toEquiv)

lemma Subgroup_eq (A B : Subgroup G)(grouple : A ≤ B)(cardle : Fintype.card B ≤ Fintype.card A) : A = B := by
  have A_eq_B : A.carrier = B.carrier := Set.eq_of_subset_of_card_le grouple cardle
  apply Subgroup.ext
  intro x
  constructor
  · intro hx; exact grouple hx
  · intro hx;
    have : x ∈ B.carrier := hx
    rw [← A_eq_B] at this
    exact this





section Special_Example_071303

variable {N : Subgroup G} {P : Sylow p G}[N.Normal]
/-
Let $N$ be a normal subgroup of a finite group $G$, $p$ be a prime, and $P$ be a Sylow $p$-subgroup of $G$. Then $N \cap P$ is a Sylow $p$-subgroup of $N$.
-/

--It is obvious that $P\cap N$ is a p-group.
lemma N_P_IsPGroup : IsPGroup p ((N ⊓ P).subgroupOf N) := by
  have t1: (N ⊓ P).subgroupOf N ≤ P.subgroupOf N := by
    have NP_le_P : N ⊓ P ≤ P := inf_le_right
    intro x hx
    exact NP_le_P hx
  have t2: IsPGroup p (P.subgroupOf N) := IsPGroup.comap_subtype P.isPGroup'
  exact IsPGroup.to_le t2 t1

lemma MAX : ∀ {Q : Subgroup ↥N}, IsPGroup p ↥Q → (N ⊓ P).subgroupOf N ≤ Q → Q = (N ⊓ P).subgroupOf N := by
  --Suppose $\forall Q \in N$ is a p-subgroup which $N \cap P \leqslant Q$,and we shall show that $Q = N \cap P$
  intro Q PGroupQ hQ
  --According to Sylow 1st Thm,There exist $P' ∈ \operatorname{Syl} _p(N)$ which $Q \leqslant P'$
  have : ∃ P' : Sylow p G , (Q.map N.subtype : Subgroup G) ≤ (P' : Subgroup G) := by
    have : IsPGroup p (Q.map N.subtype : Subgroup G) := IsPGroup.map PGroupQ N.subtype
    exact IsPGroup.exists_le_sylow this
-- According to Sylow 2th Thm, We suppose $P' = gPg^{-1}$ for some $g \in G$
  rcases this with ⟨P',hP'⟩
  have : ∃ g : G , MulAut.conj g • P' = P := MulAction.exists_smul_eq G P' P
  rcases this with ⟨g, hg⟩
  have hg' : MulAut.conj g • (P' : Subgroup G) = P := by rwa [Sylow.ext_iff] at hg
  --We will prove $g^{-1} Q g \leqslant P \cap N$ because
  have imp : MulAut.conj g • (Q.map N.subtype) ≤ N ⊓ P := by
    --$g^{-1} Q g \leqslant g^{-1} P' g = P$
    have conjQ_in_P : MulAut.conj g • (Q.map N.subtype) ≤ MulAut.conj g • P' := by
      simp only [Subgroup.pointwise_smul_le_pointwise_smul_iff, hP']
    rw [hg'] at conjQ_in_P
    --and $g^{-1} Q g \leqslant g^{-1} N g$ where $N \triangleleft G$,i.e $g^{-1} N g = N$
    have conjQ_in_N : MulAut.conj g • (Q.map N.subtype) ≤ MulAut.conj g • N := by
      have : Q.map N.subtype ≤ N := Subgroup.map_subtype_le Q
      --Hence we have $g^{-1} Q g \leqslant N$
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr this
    --By these two, we are done
    rw [Subgroup.smul_normal g N] at conjQ_in_N
    exact le_inf conjQ_in_N conjQ_in_P

  have t1 : Fintype.card Q = Fintype.card (Q.map N.subtype) := Eq.symm (card_eq_subtype_self N Q)

  --And we have $card (g^{-1} Q g) \leqslant card (P \cap N)$ by exact this
  have t2 : Fintype.card (Q.map N.subtype) ≤ Fintype.card (N ⊓ P : Subgroup G) :=
    let f : (Q.map N.subtype) →* (N ⊓ P : Subgroup G) := {
    toFun := by
      intro x
      use MulAut.conj g (x : G)
      have inQ: (x : G) ∈ (Q.map N.subtype) := by simp only [Subgroup.coe_map,
          Subgroup.coeSubtype, SetLike.coe_mem]
      have : MulAut.conj g (x : G) ∈ MulAut.conj g • (Q.map N.subtype) := by
        use (x :G)
        constructor
        · exact inQ
        · dsimp
      exact imp this
    map_one' := by simp only [Subgroup.coe_map, Subgroup.coeSubtype, OneMemClass.coe_one, map_one,
      Submonoid.mk_eq_one]
    map_mul' := by simp only [Subgroup.coe_map, Subgroup.coeSubtype, Submonoid.coe_mul,
      Subgroup.coe_toSubmonoid, map_mul, MulAut.conj_apply, conj_mul, Submonoid.mk_mul_mk,
      implies_true]
  }
    have : Function.Injective f := by
      intro x y feq
      have inj : Function.Injective (MulAut.conj g ) := MulEquiv.injective (MulAut.conj g)
      have feq :(f x : G) = (f y : G) := congrArg Subtype.val feq
      have : MulAut.conj g (x : G) = MulAut.conj g (y : G) :=
        inj (inj (congrArg (⇑(MulAut.conj g)) (congrArg (⇑(MulAut.conj g)) feq)))
      exact SetCoe.ext (inj (inj (congrArg (⇑(MulAut.conj g)) feq)))
    Fintype.card_le_of_injective (⇑f) this

  have t3 : Fintype.card (N ⊓ P : Subgroup G) = Fintype.card ((N ⊓ P).subgroupOf N) := card_eq_inf N

  --Hence $card (Q) \leqslant card (P \cap N)$
  have : Fintype.card Q ≤ Fintype.card ((N ⊓ P).subgroupOf N) := by linarith
  --So $Q = P \cap N$ as this and $N\cap P \leqslant Q$,we are done
  exact Eq.symm (Subgroup_eq ((N ⊓ P).subgroupOf N) Q hQ this)

example : Sylow p N where
  toSubgroup := (N ⊓ P).subgroupOf N
  isPGroup' := N_P_IsPGroup
  is_maximal' := MAX

end Special_Example_071303





section Special_Example_071305

/-
Let $P$ be a Sylow $p$-subgroup of a finite group $G$, and let $H$ be a subgroup of $G$, $p$ be a prime such that $p$ divides $|H|$. Then there exists $g \in G$ such that $gPg^{-1} \cap H$ is a Sylow $p$-subgroup of $H$.
-/

variable {H : Subgroup G} {P : Sylow p G} {Q : Sylow p H}

#check Sylow.ofCard

def MAX₁ (P' : Sylow p G)(hQ : Subgroup.map H.subtype Q ≤ P')(hh : Nonempty H) : Sylow p H where
  toSubgroup := P'.subgroupOf H
  isPGroup' := IsPGroup.comap_subtype P'.isPGroup'
  is_maximal' := by
    intro R pR leR

    have t1 : Fintype.card Q = Fintype.card (Q.map H.subtype) := Eq.symm (card_eq_subtype_self H Q)

    have t2 : Fintype.card (Subgroup.map H.subtype Q) ≤ Fintype.card (H ⊓ P' : Subgroup G) :=
      --Also $Q \leqslant H$ as $Q \in Syl_p H$,Hence $Q \leqslant g P g^{-1} \cap H$.
      have : Subgroup.map H.subtype Q ≤ (H ⊓ P':Subgroup G) := by
        apply Lattice.le_inf (Subgroup.map H.subtype Q) H P' _ hQ
        apply Subgroup.map_subtype_le
      Set.card_le_card this
    --Then $|Q|=p^{V_p(|H|)} \leqslant\left|gPg^{-1} \cap H\right|=p^n$, ie. $V_p(|H|) \leqslant n$

    have t3 : Fintype.card (H ⊓ P' : Subgroup G) = Fintype.card (P'.subgroupOf H) := by
      rw [← (Subgroup.inf_subgroupOf_left P' H)]
      exact card_eq_inf H

    have t4 : Fintype.card (P'.subgroupOf H) ≤ Fintype.card R := Set.card_le_card leR

    have imp : Fintype.card Q ≤ Fintype.card R := by linarith

    --Here, $gPg^{-1} \cap H \leqslant g P g^{-1} \in S y I_p G$, it is a $p$-group. We suppose $\left|gPg^{-1} \cap H\right|=p^n$
    have : ∃ n : ℕ,Fintype.card R = p ^ n := IsPGroup.exists_card_eq pR
    rcases this with ⟨n,cardR⟩
    have cardQ : Fintype.card Q = p ^ (Fintype.card H).factorization p := Sylow.card_eq_multiplicity Q

    have : Fintype.card R ∣ Fintype.card H := Subgroup.card_subgroup_dvd_card R
    rw [cardR] at this
    have : n ≤ (Fintype.card H).factorization p := by
      refine (Nat.Prime.pow_dvd_iff_le_factorization pp ?hn).mp this
      exact Fintype.card_ne_zero

    rw [cardR, cardQ] at imp
    -- Also $g^{-1} \cap H \leqslant H$ means $p^n\mid \left| H \right|$, ie. $n \leqslant V_p(|H|)$
    have s1: (Fintype.card H).factorization p ≤ n := by
      apply (Nat.pow_le_pow_iff_right _).mp imp
      exact Nat.Prime.one_lt pp
    -- Hence, $n=V_p(|H|)$ and $\left|gPg^{-1} \cap H\right|=p^{V_p(|H|)}$
    have s2: (Fintype.card H).factorization p = n := by linarith

    have s3: Fintype.card R = Fintype.card Q := by
      rw [cardR, cardQ]
      exact congrArg (HPow.hPow p) (id (Eq.symm s2))

    have s4 : Fintype.card ↥R ≤ Fintype.card (P'.subgroupOf H) := by linarith
    -- $\Rightarrow g P g^{-1} \cap H \in Syl_p H$
    apply Eq.symm (Subgroup_eq (P'.subgroupOf H) R leR s4)

noncomputable example  : ∃ a : G ,∃ Q : Sylow p H, (MulAut.conj a • P).subgroupOf H = Q := by
  have hh : Nonempty H := by exact One.instNonempty
  --We choose $Q \in Syl_p H$ and there are some $g$ where $Q \leqslant {gPg}^{-1}$ by Sylow-second Theorem
  have : ∃ P' : Sylow p G , (Q.map H.subtype : Subgroup G) ≤ (P' : Subgroup G) := by
    --because $Q$ is a $p$-subgroup
    have PGroupQ : IsPGroup p (Q.map H.subtype : Subgroup G) := by
      have : IsPGroup p Q := by exact Q.isPGroup'
      exact IsPGroup.map this H.subtype
    exact IsPGroup.exists_le_sylow PGroupQ
  rcases this with ⟨P', HQ⟩
  have : ∃ g : G , MulAut.conj g • P = P' := MulAction.exists_smul_eq G P P'
  rcases this with ⟨g, hg⟩
  use g
  rw [hg]
  use MAX₁ pp P' HQ hh
  exact rfl

end Special_Example_071305





section

def inclusion_map {K : Type*}[Group K](H : Subgroup K)(L : Subgroup H): L →* K where
  toFun := fun x => x.1.1
  map_one' := by simp only [OneMemClass.coe_one]
  map_mul' := fun x y => by simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid]

def Aut_Sylow {G : Type*} [Group G] {p : ℕ}[Fact p.Prime] [Fintype G] (P : Sylow p G) (f : MulAut G) : Sylow p G :=
  letI : Fintype (P : Subgroup G) := by apply Fintype.ofFinite
  letI : Fintype (Subgroup.map f.toMonoidHom (P : Subgroup G)) := by apply Fintype.ofFinite
  letI : Fintype (((f.toMonoidHom).restrict (P : Subgroup G)).range) := by apply Fintype.ofFinite
  Sylow.ofCard (Subgroup.map f.toMonoidHom (P : Subgroup G)) (by
    rw [←Sylow.card_eq_multiplicity P]
    have : Fintype.card (((f.toMonoidHom ).restrict (P : Subgroup G)).range) = Fintype.card (Subgroup.map f.toMonoidHom (P : Subgroup G)) := by
      apply Fintype.card_congr'
      rw [MonoidHom.restrict_range (P : Subgroup G) f.toMonoidHom]
    rw [←this]
    have : Function.Injective ((f.toMonoidHom).restrict (P : Subgroup G)) := by
      intro x y heq
      simp only [MonoidHom.restrict_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.apply_eq_iff_eq, SetLike.coe_eq_coe] at heq
      exact heq
    convert Set.card_range_of_injective this
    -- apply Fintype.ofFinite
    )

end
