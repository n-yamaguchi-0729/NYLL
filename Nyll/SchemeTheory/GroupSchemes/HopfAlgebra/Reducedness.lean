/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.CharZeroLocal

/-! # Reducedness of finite type commutative Hopf algebras -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.FrobeniusReducedness


open scoped TensorProduct

universe u v

theorem _root_.HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    ∃ (r : ℕ) (K' : Subalgebra k H), K' ≤ K ∧ K'.FG ∧ IsReduced ↥K' ∧
      (K' : Set H) = {y : H | ∃ x ∈ K, y = x ^ p ^ r} ∧
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') := by
  classical
  have hp : p.Prime := Fact.out
  have : Algebra.FiniteType k ↥K := ⟨(Subalgebra.fg_top K).mpr hfg⟩
  have : IsNoetherianRing ↥K := Algebra.FiniteType.isNoetherianRing k ↥K
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical ↥K
  obtain ⟨r, hr⟩ : ∃ r : ℕ, m ≤ p ^ r := ⟨m, (Nat.lt_pow_self hp.one_lt).le⟩
  have hq0 : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  have hadd : ∀ x y : H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    rcases subsingleton_or_nontrivial H with hH | hH
    · intro x y; exact Subsingleton.elim _ _
    · have : CharP H p := charP_of_injective_algebraMap (algebraMap k H).injective p
      intro x y; exact add_pow_char_pow x y p r
  have hadd₂ : ∀ x y : H ⊗[k] H, (x + y) ^ p ^ r = x ^ p ^ r + y ^ p ^ r := by
    rcases subsingleton_or_nontrivial (H ⊗[k] H) with hH | hH
    · intro x y; exact Subsingleton.elim _ _
    · have : CharP (H ⊗[k] H) p :=
        charP_of_injective_algebraMap (algebraMap k (H ⊗[k] H)).injective p
      intro x y; exact add_pow_char_pow x y p r
  have hroot : ∀ c : k, ∃ d : k, d ^ p ^ r = c := fun c =>
    ⟨(frobeniusEquiv k p).symm^[r] c, iterate_frobeniusEquiv_symm_pow_p_pow k p c r⟩
  have hSpow (x : H) (n : ℕ) :
      HopfAlgebra.antipode k (x ^ n) = (HopfAlgebra.antipode k x) ^ n :=
    map_pow (HopfAlgebra.antipodeAlgHom k H) x n
  let K' : Subalgebra k H :=
    { carrier := {y : H | ∃ x ∈ K, y = x ^ p ^ r}
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, K.mul_mem hx hy, (mul_pow x y _).symm⟩
      one_mem' := ⟨1, K.one_mem, (one_pow _).symm⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, (hadd x y).symm⟩
      zero_mem' := ⟨0, K.zero_mem, (zero_pow hq0).symm⟩
      algebraMap_mem' := fun c => by
        obtain ⟨d, hd⟩ := hroot c
        exact ⟨algebraMap k H d, K.algebraMap_mem d, by rw [← map_pow, hd]⟩ }
  have memK' : ∀ y : H, y ∈ K' ↔ ∃ x ∈ K, y = x ^ p ^ r := fun _ => Iff.rfl
  have hpowK' : ∀ x ∈ K, x ^ p ^ r ∈ K' := fun x hx => ⟨x, hx, rfl⟩
  refine ⟨r, K', ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact K.pow_mem hx _
  · obtain ⟨t, ht⟩ := hfg
    refine ⟨t.image fun x => x ^ p ^ r, le_antisymm ?_ ?_⟩
    · apply Algebra.adjoin_le
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hpowK' x (ht ▸ Algebra.subset_adjoin hx)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← ht] at hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
          apply Algebra.subset_adjoin
          rw [Finset.coe_image]
          exact ⟨y, hy, rfl⟩
      | algebraMap c => rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _
      | add y z _ _ hy hz => rw [hadd]; exact Subalgebra.add_mem _ hy hz
      | mul y z _ _ hy hz => rw [mul_pow]; exact Subalgebra.mul_mem _ hy hz
  · refine ⟨fun y hy => ?_⟩
    obtain ⟨n, hn⟩ := hy
    obtain ⟨x, hx, hxq⟩ := (memK' y).mp y.2
    have hyn : (y : H) ^ n = 0 := by
      exact congrArg Subtype.val hn
    have hxn : (⟨x, hx⟩ : ↥K) ∈ nilradical ↥K := by
      refine ⟨p ^ r * n, Subtype.ext ?_⟩
      change x ^ (p ^ r * n) = 0
      rw [pow_mul, ← hxq]
      exact hyn
    have hxm : x ^ m = 0 := by
      have h1 := Ideal.pow_mem_pow hxn m
      rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
      exact congrArg Subtype.val h1
    apply Subtype.ext
    change (y : H) = 0
    rw [hxq, ← Nat.add_sub_cancel' hr, pow_add, hxm, zero_mul]
  · rintro _ ⟨x, hx, rfl⟩
    have hpow : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
        t ^ p ^ r ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b} := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem s hs =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hs
          rw [Algebra.TensorProduct.tmul_pow]
          exact Submodule.subset_span ⟨_, hpowK' a ha, _, hpowK' b hb, rfl⟩
      | zero => rw [zero_pow hq0]; exact Submodule.zero_mem _
      | add s t _ _ hs ht => rw [hadd₂]; exact Submodule.add_mem _ hs ht
      | smul c s _ hs => rw [smul_pow]; exact Submodule.smul_mem _ _ hs
    have : Coalgebra.comul (R := k) (x ^ p ^ r) = (Coalgebra.comul (R := k) x) ^ p ^ r := by
      rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rw [this]
    exact hpow _ (hΔ x hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [hSpow]
    exact hpowK' _ (hS x hx)

end AbelianVarieties.NOSProofs.FrobeniusReducedness
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GeometricReducedness

noncomputable section

theorem _root_.HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  refine isReduced_ofLocalizationMaximal A ?_
  intro J hJ
  obtain ⟨χ, hχ⟩ : ∃ χ : A →ₐ[K] K, J = RingHom.ker χ.toRingHom := by
    have : J.IsMaximal := hJ
    let : Field (A ⧸ J) := Ideal.Quotient.field J
    have : Algebra.FiniteType K (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) Ideal.Quotient.mk_surjective
    have : Module.Finite K (A ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ J)
    have hbij : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hbij
    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K J), ?_⟩
    ext a
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
    rw [show ∀ x, e.symm.toAlgHom x = e.symm x from fun _ => rfl,
      map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  subst hχ
  have : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
  have : IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) :=
    HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero K A χ
  infer_instance

end

end AbelianVarieties.NOSProofs.GeometricReducedness
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.Reducedness

open scoped TensorProduct

theorem _root_.HopfAlgebra.isReduced_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  let Ω := AlgebraicClosure K
  have : IsReduced (Ω ⊗[K] A) :=
    HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero Ω (Ω ⊗[K] A)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (R := K) (A := Ω) (B := A)
      (algebraMap K Ω).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] Ω ⊗[K] A).toRingHom hinj

end AbelianVarieties.NOSProofs.Reducedness
end
