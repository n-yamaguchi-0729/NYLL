/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.RingTheory.Smooth.DifferentialCriteria

/-! # Smoothening bounds and affine smooth/free loci -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.SmootheningBounds


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

universe v w

open TensorProduct IsLocalRing

noncomputable section

namespace NeronSmootheningBound

section TorsionExponent

variable {S : Type u} [CommRing S] [IsDomain S]
variable {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module S F₁] [AddCommGroup F₀] [Module S
  F₀]

theorem smul_eq_zero_of_mem_torsion_of_comp_comp_eq_smul [Module.IsTorsionFree S F₀]
    (N : F₁ →ₗ[S] F₀) (H : F₀ →ₗ[S] F₁) (r : S) (hH : N ∘ₗ H ∘ₗ N = r • N)
    (x : F₀ ⧸ LinearMap.range N) (hx : x ∈ Submodule.torsion S (F₀ ⧸ LinearMap.range N)) :
    r • x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨s, hs⟩, hsx⟩ := (Submodule.mem_torsion_iff _).mp hx
  have hsx' : (s : S) • x ∈ LinearMap.range N := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hsx
  obtain ⟨y, hy⟩ := hsx'
  have key : s • (r • x - N (H x)) = 0 := by
    have h1 : N (H (N y)) = r • N y := by
      have := congrArg (fun φ => φ y) hH
      exact this
    rw [smul_sub, smul_comm s r x, ← hy, ← h1, hy, LinearMap.map_smul, LinearMap.map_smul]
    exact sub_self _
  have hs0 : (s : S) ≠ 0 := nonZeroDivisors.ne_zero hs
  have : r • x - N (H x) = 0 := by
    rcases smul_eq_zero.mp key with h | h
    · exact absurd h hs0
    · exact h
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨H x, (sub_eq_zero.mp this).symm⟩

end TorsionExponent

section LengthBound

variable {S : Type u} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem length_quotient_span_pow (ϖ : S) (hϖ : Irreducible ϖ) (c : ℕ) :
    Module.length S (S ⧸ Ideal.span {ϖ ^ c}) = c := by
  have : Ideal.span {ϖ ^ c} = maximalIdeal S ^ c := by
    rw [← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]
  rw [this]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal S c

variable {C : Type v} [AddCommGroup C] [Module S C]

omit [IsDiscreteValuationRing S] in
theorem torsion_inf_pow_smul_eq_bot (ϖ : S) (c : ℕ)
    (hkill : ∀ x ∈ Submodule.torsion S C, ϖ ^ c • x = 0) :
    Submodule.torsion S C ⊓ (Ideal.span {ϖ ^ c} • ⊤ : Submodule S C) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, ht'⟩
  rw [Submodule.mem_bot]
  rw [Submodule.ideal_span_singleton_smul, SetLike.mem_coe,
    Submodule.mem_smul_pointwise_iff_exists] at ht'
  obtain ⟨y, -, rfl⟩ := ht'
  by_cases hc : ϖ ^ c = 0
  · simp only [hc, zero_smul]
  have hy : y ∈ Submodule.torsion S C := by
    obtain ⟨⟨s, hs⟩, hsy⟩ := (Submodule.mem_torsion_iff _).mp ht
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s * ϖ ^ c, ?_⟩, ?_⟩
    · exact mul_mem_nonZeroDivisors.mpr ⟨hs, mem_nonZeroDivisors_of_ne_zero hc⟩
    · change (s * ϖ ^ c) • y = 0
      rw [mul_smul]; exact hsy
  exact hkill y hy

theorem length_torsion_le (ϖ : S) (hϖ : Irreducible ϖ) (c n : ℕ)
    (g : (Fin n → S) →ₗ[S] C) (hg : Function.Surjective g)
    (hkill : ∀ x ∈ Submodule.torsion S C, ϖ ^ c • x = 0) :
    Module.length S (Submodule.torsion S C) ≤ (n * c : ℕ) := by
  classical
  set I : Ideal S := Ideal.span {ϖ ^ c} with hI
  have hinj : Function.Injective ((I • (⊤ : Submodule S C)).mkQ ∘ₗ (Submodule.torsion S
    C).subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at ht
    have : (t : C) ∈ Submodule.torsion S C ⊓ (I • ⊤ : Submodule S C) := ⟨t.2, ht⟩
    rw [torsion_inf_pow_smul_eq_bot ϖ c hkill, Submodule.mem_bot] at this
    exact (Submodule.mem_bot S).mpr (Subtype.ext this)
  have h1 := Module.length_le_of_injective _ hinj
  let m : Fin n → C ⧸ (I • (⊤ : Submodule S C)) := fun i => Submodule.Quotient.mk (g (Pi.single
    i 1))
  have hm : ∀ i, I ≤ LinearMap.ker (LinearMap.toSpanSingleton S _ (m i)) := by
    intro i r hr
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    change r • Submodule.Quotient.mk _ = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let φ : Fin n → ((S ⧸ I) →ₗ[S] C ⧸ (I • (⊤ : Submodule S C))) := fun i => I.liftQ _ (hm i)
  let ψ : (Fin n → S ⧸ I) →ₗ[S] C ⧸ (I • (⊤ : Submodule S C)) := ∑ i, φ i ∘ₗ LinearMap.proj i
  have hφ : ∀ (i : Fin n) (s : S), φ i (Submodule.Quotient.mk s) = s • m i := by
    intro i s
    simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
  have hψv : ∀ v : Fin n → S, ψ (fun i => Submodule.Quotient.mk (v i)) = Submodule.Quotient.mk
    (g v) := by
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : S) := by
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
        ((Pi.basisFun S (Fin n)).sum_repr v).symm
    simp only [ψ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, hφ, m]
    conv_rhs => rw [hv, map_sum]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨v, rfl⟩ := ((Submodule.mkQ_surjective _).comp hg) z
    exact ⟨fun i => Submodule.Quotient.mk (v i), by rw [hψv]; rfl⟩
  have h2 := Module.length_le_of_surjective _ hψ
  have h3 : Module.length S (Fin n → S ⧸ I) = (n * c : ℕ) := by
    rw [Module.length_pi_of_fintype]
    have : Module.length S (S ⧸ I) = c := length_quotient_span_pow ϖ hϖ c
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  calc Module.length S (Submodule.torsion S C)
      ≤ Module.length S (C ⧸ (I • (⊤ : Submodule S C))) := h1
    _ ≤ Module.length S (Fin n → S ⧸ I) := h2
    _ = (n * c : ℕ) := h3

end LengthBound

section GeneralizedInverse

open TensorProduct

variable {A : Type u} [CommRing A]

theorem exists_comp_comp_eq_self_of_projective_coker
    {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module A F₁] [AddCommGroup F₀] [Module A F₀]
    [Module.Projective A F₀] (N : F₁ →ₗ[A] F₀)
    [Module.Projective A (F₀ ⧸ LinearMap.range N)] :
    ∃ H : F₀ →ₗ[A] F₁, N ∘ₗ H ∘ₗ N = N := by
  set q : F₀ →ₗ[A] F₀ ⧸ LinearMap.range N := (LinearMap.range N).mkQ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id)
    (Submodule.mkQ_surjective _)
  set e : F₀ →ₗ[A] F₀ := LinearMap.id - s ∘ₗ q
  have he : ∀ y, e y ∈ LinearMap.range N := by
    intro y
    have : q (e y) = 0 := by
      simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
      have := congrArg (fun φ => φ (q y)) hs
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this, sub_self]
    rwa [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  have heN : ∀ z, e (N z) = N z := by
    intro z
    simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    have : q (N z) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨z, rfl⟩
    rw [this, map_zero, sub_zero]
  let e' : F₀ →ₗ[A] LinearMap.range N := LinearMap.codRestrict _ e he
  obtain ⟨H, hH⟩ := Module.projective_lifting_property N.rangeRestrict e'
    N.surjective_rangeRestrict
  refine ⟨H, ?_⟩
  ext z
  have := congrArg (fun φ => ((φ (N z) : LinearMap.range N) : F₀)) hH
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, e'] at this
  simp only [LinearMap.comp_apply]
  rw [this, heN]

variable (π : A) (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away π B]

/-- Scalar extension commutes with the cokernel of a linear map. -/
noncomputable def baseChangeCokerEquiv (Q : Type u) [CommRing Q] [Algebra A Q]
    {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module A F₁] [AddCommGroup F₀] [Module A F₀]
    (N : F₁ →ₗ[A] F₀) :
    ((Q ⊗[A] F₀) ⧸ LinearMap.range (N.baseChange Q)) ≃ₗ[Q] Q ⊗[A] (F₀ ⧸ LinearMap.range N) := by
  refine (LinearMap.range (N.baseChange Q)).quotEquivOfEq _ ?_ ≪≫ₗ
    ((LinearMap.range N).mkQ.baseChange Q).quotKerEquivOfSurjective ?_
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : (LinearMap.range N).mkQ ∘ₗ N = 0 := LinearMap.range_mkQ_comp N
      rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]
    · intro x hx
      have hx' : x ∈ LinearMap.ker (((LinearMap.range N).mkQ).lTensor Q) := hx
      rw [lTensor_mkQ] at hx'
      obtain ⟨y, rfl⟩ := hx'
      obtain ⟨w, rfl⟩ := (LinearMap.lTensor_surjective Q N.surjective_rangeRestrict) y
      refine ⟨w, ?_⟩
      change (N.lTensor Q) w = _
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]; rfl
  · exact LinearMap.lTensor_surjective Q (Submodule.mkQ_surjective _)

end GeneralizedInverse

section ClearDenominators

open TensorProduct

variable {A : Type u} [CommRing A] (π : A) (B : Type u) [CommRing B] [Algebra A B]
  [IsLocalization.Away π B]

theorem exists_pow_smul_eq_zero_of_baseChange_eq_zero {n m : ℕ}
    (D : (Fin m → A) →ₗ[A] (Fin n → A)) (hD : D.baseChange B = 0) :
    ∃ k : ℕ, (π ^ k) • D = 0 := by
  classical
  have hentry : ∀ i j, algebraMap A B (LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A
    (Fin n)) D i j)
      = 0 := by
    intro i j
    have h := LinearMap.toMatrix_baseChange (A := B) D (Pi.basisFun A (Fin m)) (Pi.basisFun A
      (Fin n))
    have := congrArg (fun M => M i j) h
    simp only [hD, map_zero, Matrix.zero_apply, Matrix.map_apply] at this
    exact this.symm
  have hk : ∀ ij : Fin n × Fin m, ∃ k : ℕ, π ^ k *
      LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n)) D ij.1 ij.2 = 0 := by
    intro ij
    obtain ⟨⟨b, hb⟩, hb'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers π) B _).mp
      (hentry ij.1 ij.2)
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hb
    exact ⟨k, hb'⟩
  choose k hk using hk
  refine ⟨∑ ij, k ij, ?_⟩
  apply (LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n))).injective
  rw [map_smul, map_zero]
  ext i j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
  have hle : k (i, j) ≤ ∑ ij, k ij := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (i, j))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, add_comm, pow_add, mul_assoc, hk (i, j), mul_zero]

theorem exists_pow_smul_eq_baseChange {n m : ℕ}
    (H : (B ⊗[A] (Fin n → A)) →ₗ[B] (B ⊗[A] (Fin m → A))) :
    ∃ (c : ℕ) (H₀ : (Fin n → A) →ₗ[A] (Fin m → A)), H₀.baseChange B = (algebraMap A B (π ^ c)) •
      H := by
  classical
  let bn := Algebra.TensorProduct.basis B (Pi.basisFun A (Fin n))
  let bm := Algebra.TensorProduct.basis B (Pi.basisFun A (Fin m))
  let M : Matrix (Fin m) (Fin n) B := LinearMap.toMatrix bn bm H
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers π)
    (fun ij : Fin m × Fin n => M ij.1 ij.2)
  obtain ⟨c, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hb
  choose a ha using fun ij : Fin m × Fin n => hint ij
  let M₀ : Matrix (Fin m) (Fin n) A := fun i j => a (i, j)
  refine ⟨c, Matrix.toLin (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin m)) M₀, ?_⟩
  apply (LinearMap.toMatrix bn bm).injective
  rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin, map_smul]
  ext i j
  change algebraMap A B (a (i, j)) = algebraMap A B (π ^ c) * M i j
  exact (ha (i, j)).trans (Algebra.smul_def _ _)

theorem exists_comp_comp_eq_pow_smul {n m : ℕ}
    (N : (Fin m → A) →ₗ[A] (Fin n → A))
    [Module.Projective B (B ⊗[A] ((Fin n → A) ⧸ LinearMap.range N))] :
    ∃ (c : ℕ) (H : (Fin n → A) →ₗ[A] (Fin m → A)), N ∘ₗ H ∘ₗ N = (π ^ c) • N := by
  classical
  have : Module.Projective B ((B ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange B)) :=
    Module.Projective.of_equiv (baseChangeCokerEquiv B N).symm
  obtain ⟨HB, hHB⟩ := exists_comp_comp_eq_self_of_projective_coker (A := B) (N.baseChange B)
  obtain ⟨c, H₀, hH₀⟩ := exists_pow_smul_eq_baseChange π B HB
  have hz : (N ∘ₗ H₀ ∘ₗ N - (π ^ c) • N).baseChange B = 0 := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_comp, LinearMap.baseChange_comp, hH₀,
      LinearMap.baseChange_smul, LinearMap.smul_comp, LinearMap.comp_smul, hHB, algebraMap_smul]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply]
    exact sub_self _
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_baseChange_eq_zero π B _ hz
  refine ⟨k + c, (π ^ k) • H₀, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hk
  rw [LinearMap.smul_comp, LinearMap.comp_smul, hk]

end ClearDenominators

section Core

open TensorProduct

theorem length_torsion_eq_of_equiv {S : Type u} [CommRing S] {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
    Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
  have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
    constructor
    · rintro ⟨x, ⟨a, ha⟩, rfl⟩
      refine ⟨a, ?_⟩
      change (a : S) • (e : M →ₗ[S] M') x = 0
      change (a : S) • x = 0 at ha
      rw [← map_smul, ha, map_zero]
    · rintro ⟨a, ha⟩
      refine ⟨e.symm y, ⟨a, ?_⟩, e.apply_symm_apply y⟩
      change (a : S) • e.symm y = 0
      change (a : S) • y = 0 at ha
      rw [← map_smul, ha, map_zero]
  rw [← this]
  exact (e.submoduleMap (Submodule.torsion S M)).length_eq

theorem exists_bound_length_torsion_baseChange_kaehlerDifferential
    {R : Type u} [CommRing R] [IsNoetherianRing R] (π : R)
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (algebraMap R A π) B]
    [Module.Projective B (B ⊗[A] Ω[A⁄R])] :
    ∃ C : ℕ, ∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra A S],
      Irreducible (algebraMap A S (algebraMap R A π)) →
      Module.length S (Submodule.torsion S (S ⊗[A] Ω[A⁄R])) ≤ C := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite A _
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin A Ω[A⁄R]
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let N : (Fin m → A) →ₗ[A] (Fin n → A) := Fintype.linearCombination A s
  have hN : LinearMap.range N = K := by rw [Fintype.range_linearCombination, hs]
  let eN : ((Fin n → A) ⧸ LinearMap.range N) ≃ₗ[A] Ω[A⁄R] :=
    (Submodule.quotEquivOfEq _ _ hN).trans e.symm
  have : Module.Projective B (B ⊗[A] ((Fin n → A) ⧸ LinearMap.range N)) :=
    Module.Projective.of_equiv (eN.baseChange A B _ _ ).symm
  obtain ⟨c, H, hH⟩ := exists_comp_comp_eq_pow_smul (algebraMap R A π) B N
  refine ⟨n * c, fun S _ _ _ _ hπ => ?_⟩
  set ϖ : S := algebraMap A S (algebraMap R A π) with hϖ
  have hHS : N.baseChange S ∘ₗ H.baseChange S ∘ₗ N.baseChange S = (ϖ ^ c) • N.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hH, LinearMap.baseChange_smul]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hϖ, ← map_pow (algebraMap A S),
      algebraMap_smul (A := S)]
  have hkill : ∀ x ∈ Submodule.torsion S ((S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S)),
      ϖ ^ c • x = 0 :=
    fun x hx => smul_eq_zero_of_mem_torsion_of_comp_comp_eq_smul _ _ _ hHS x hx
  let g : (Fin n → S) →ₗ[S] (S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S) :=
    (LinearMap.range (N.baseChange S)).mkQ ∘ₗ (TensorProduct.piScalarRight A S S (Fin
      n)).symm.toLinearMap
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (TensorProduct.piScalarRight A S S (Fin n)).symm.surjective
  have hle := length_torsion_le ϖ hπ c n g hg hkill
  have eS : ((S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S)) ≃ₗ[S] S ⊗[A] Ω[A⁄R] :=
    (baseChangeCokerEquiv S N).trans (eN.baseChange A S _ _)
  rw [← length_torsion_eq_of_equiv eS]
  exact hle

end Core

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)

/-- The base algebra on global sections induced by the structure morphism. -/
abbrev globalAlgebra : Algebra R Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

/-- Evaluation of global sections at a local-ring-valued point. -/
abbrev globalPointAlgebra : Algebra Γ(X, ⊤) R' :=
  ((Scheme.stalkClosedPointTo a).hom.comp
    (X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom).toAlgebra

theorem smoothnessDefect_eq_length_torsion_global [IsAffine X] :
    let : Algebra R Γ(X, ⊤) := globalAlgebra f
    let : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
    smoothnessDefect f a =
      Module.length R' (Submodule.torsion R' (R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R])) := by
  intro iRA iAR'
  rw [smoothnessDefect_def]
  set x : X := a (IsLocalRing.closedPoint R') with hx
  let iRO : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  let iOR' : Algebra (X.presheaf.stalk x) R' := pointAlgebra a
  let iAO : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have : IsScalarTower R Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) R' :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have : Algebra.FormallyEtale Γ(X, ⊤) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal.primeCompl)
  let e₁ : (X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] ≃ₗ[X.presheaf.stalk x]
    Ω[X.presheaf.stalk x⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, ⊤) (X.presheaf.stalk x)
  let e₂ : R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] ≃ₗ[R']
      R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    (e₁.symm.baseChange (X.presheaf.stalk x) R' _ _)
  let e₃ : R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) ≃ₗ[R']
      R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, ⊤) (X.presheaf.stalk x) R' R' Ω[Γ(X,
      ⊤)⁄R]
  exact length_torsion_eq_of_equiv (e₂.trans e₃)

theorem algebraMap_globalPointAlgebra_globalAlgebra [Algebra R R']
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) (r : R) :
    let : Algebra R Γ(X, ⊤) := globalAlgebra f
    let : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
    algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) r) = algebraMap R R' r := by
  intro iRA iAR'
  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R'))
    trivial).hom
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r
  have h1 := Scheme.Hom.germ_stalkMap_apply f ⊤ (a (IsLocalRing.closedPoint R')) trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ (f ⁻¹ᵁ ⊤) (a
    (IsLocalRing.closedPoint R')) trivial).hom
    ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r
  rw [← h1]
  rw [← CommRingCat.comp_apply, ← Scheme.stalkClosedPointTo_comp]
  have key : ∀ (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      g = Spec.map (CommRingCat.ofHom (algebraMap R R')) → ∀ s,
      (Scheme.stalkClosedPointTo g).hom
        (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint R'))
          trivial).hom s) =
        algebraMap R R' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
    rintro g rfl s
    have h3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap R R'))
    have := congrArg (fun φ : (Spec (CommRingCat.of R)).presheaf.obj (Opposite.op ⊤) ⟶
      CommRingCat.of R' =>
      φ.hom s) h3
    exact this
  refine (key (a ≫ f) ha _).trans ?_
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]



section GenericFibreSmooth

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (K : Type u) [CommRing K] [Algebra R K]

theorem eq_isoSpec_hom_comp_Spec_map [IsAffine X] :
    (let : Algebra R Γ(X, ⊤) := globalAlgebra f
     f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) := by
  intro alg
  have h1 : CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := rfl
  rw [h1, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
    Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

theorem projective_baseChange_kaehlerDifferential_of_smooth_genericFibre [IsAffine X]
    (hK : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    (let : Algebra R Γ(X, ⊤) := globalAlgebra f
     Module.Projective (Γ(X, ⊤) ⊗[R] K) ((Γ(X, ⊤) ⊗[R] K) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R])) := by
  intro alg
  set A : Type u := Γ(X, ⊤) with hA
  let : Algebra K (A ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  have hf := eq_isoSpec_hom_comp_Spec_map f
  have hf' : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ 𝟙 _ = X.isoSpec.inv ≫ f := by
    rw [Category.comp_id, hf, Iso.inv_hom_id_assoc]
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) f (Spec.map (CommRingCat.ofHom (algebraMap R
      K)))
    X.isoSpec.inv (𝟙 _) (𝟙 _) hf' (by rw [Category.comp_id, Category.id_comp])
  have hm : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      m ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [pullback.lift_snd, Category.comp_id]
  have := hK
  have h2 : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [hm]; infer_instance
  have h3 : Smooth (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) : K →ₐ[R] A ⊗[R] K) : K
        →+* A ⊗[R] K))) := by
    have := pullbackSpecIso_hom_snd R A K
    have e : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := R) (A := A)
      (B := K) : K →ₐ[R] A ⊗[R] K) : K →+* A ⊗[R] K))
        = (pullbackSpecIso R A K).inv ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R
          A)))
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
      rw [← this, Iso.inv_hom_id_assoc]
    rw [e]; infer_instance
  have h4 : RingHom.Smooth ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) : K
    →ₐ[R] A ⊗[R] K) : K →+* A ⊗[R] K) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h3
  have h5 : Algebra.Smooth K (A ⊗[R] K) := h4
  have : Algebra.FormallySmooth K (A ⊗[R] K) := h5.formallySmooth
  have : Module.Projective (A ⊗[R] K) Ω[A ⊗[R] K⁄K] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  have : Algebra.IsPushout R K A (A ⊗[R] K) := Algebra.IsPushout.symm inferInstance
  exact Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R K A (A ⊗[R] K)).symm

end GenericFibreSmooth

theorem irreducible_algebraMap_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (h : IsIndexOneExtension R R') (π : R) (hπ : Irreducible π) :
    Irreducible (algebraMap R R' π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← h.map_maximalIdeal, hπ, Ideal.map_span, Set.image_singleton]

theorem finiteType_appTop_comp {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).FiniteType := by
  have h : f.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P :=
    @LocallyOfFiniteType)).mp ‹_›
  exact h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)

section Invariance

open TensorProduct

theorem smoothnessDefect_comp_eq {R : Type u} [CommRing R] {U X : Scheme.{u}} (g : U ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ U) [IsIso (g.stalkMap (a (IsLocalRing.closedPoint R')))] :
    smoothnessDefect (g ≫ f) a = smoothnessDefect f (a ≫ g) := by
  rw [smoothnessDefect_def, smoothnessDefect_def]
  set p : U := a (IsLocalRing.closedPoint R') with hp
  change _ = (let : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
    let : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
    Module.length R' (Submodule.torsion R' (R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g
      p)⁄R])))
  let iRO : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
  let iOR' : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
  let iRO' : Algebra R (U.presheaf.stalk p) := stalkAlgebra (g ≫ f) p
  let iO'R' : Algebra (U.presheaf.stalk p) R' := pointAlgebra a
  let iOO' : Algebra (X.presheaf.stalk (g p)) (U.presheaf.stalk p) := (g.stalkMap p).hom.toAlgebra
  have : IsScalarTower R (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change stalkAlgebraMap (g ≫ f) p r = (g.stalkMap p).hom (stalkAlgebraMap f (g p) r)
      rw [stalkAlgebraMap_apply, stalkAlgebraMap_apply, Scheme.Hom.germ_stalkMap_apply g ⊤ p
        trivial]
      rfl)
  have : IsScalarTower (X.presheaf.stalk (g p)) (U.presheaf.stalk p) R' :=
    IsScalarTower.of_algebraMap_eq' (by
      change (Scheme.stalkClosedPointTo (a ≫ g)).hom = (Scheme.stalkClosedPointTo a).hom.comp
        (g.stalkMap p).hom
      rw [Scheme.stalkClosedPointTo_comp]
      rfl)
  have : IsLocalization.Away (1 : X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (g.stalkMap p))
  have : Algebra.FormallyEtale (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : X.presheaf.stalk (g p)))
  let e₁ : (U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R]
    ≃ₗ[U.presheaf.stalk p]
      Ω[U.presheaf.stalk p⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (X.presheaf.stalk (g p))
      (U.presheaf.stalk p)
  let e₂ : R' ⊗[U.presheaf.stalk p] Ω[U.presheaf.stalk p⁄R] ≃ₗ[R']
      R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)]
        Ω[X.presheaf.stalk (g p)⁄R]) :=
    (e₁.symm.baseChange (U.presheaf.stalk p) R' _ _)
  let e₃ : R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)]
    Ω[X.presheaf.stalk (g p)⁄R])
      ≃ₗ[R'] R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk (g p))
      (U.presheaf.stalk p) R' R'
      Ω[X.presheaf.stalk (g p)⁄R]
  exact length_torsion_eq_of_equiv (e₂.trans e₃)

end Invariance

section Affine

theorem bound_of_isAffine {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (hK : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R
      R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ a : Spec (CommRingCat.of R') ⟶ X, a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
        smoothnessDefect f a ≤ c := by
  let iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  have : Algebra.FiniteType R Γ(X, ⊤) := finiteType_appTop_comp f
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := NeronModelInfra.isLocalizationAway_of_irreducible K hπ
  have : IsLocalization.Away (algebraMap R Γ(X, ⊤) π) (Γ(X, ⊤) ⊗[R] K) :=
    IsLocalization.Away.tensor (S := Γ(X, ⊤)) π K
  have : Module.Projective (Γ(X, ⊤) ⊗[R] K) ((Γ(X, ⊤) ⊗[R] K) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    projective_baseChange_kaehlerDifferential_of_smooth_genericFibre f K hK
  obtain ⟨C, hC⟩ := exists_bound_length_torsion_baseChange_kaehlerDifferential π (A := Γ(X, ⊤))
    (Γ(X, ⊤) ⊗[R] K)
  refine ⟨C, fun R' _ _ _ _ h a ha => ?_⟩
  rw [smoothnessDefect_eq_length_torsion_global f a]
  let iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  have hirr : Irreducible (algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) π)) := by
    rw [algebraMap_globalPointAlgebra_globalAlgebra f a ha π,
      IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
        Set.image_singleton]
  exact_mod_cast hC R' hirr

end Affine

end NeronSmootheningBound

open NeronSmootheningBound in
theorem _root_.NeronModelInfra.exists_forall_smoothnessDefect_le_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R
      R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
        smoothnessDefect f x.1 ≤ c  := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have hsm : ∀ i, Smooth (pullback.snd (𝒰.f i ≫ f) (specGenericFibreInclusion R K)) := by
    intro i
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f (specGenericFibreInclusion R K) (𝒰.f i)]
    have := hK
    infer_instance
  have hb : ∀ i, ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing
    R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ a : Spec (CommRingCat.of R') ⟶ 𝒰.X i, a ≫ (𝒰.f i ≫ f) = Spec.map (CommRingCat.ofHom
        (algebraMap R R')) →
        smoothnessDefect (𝒰.f i ≫ f) a ≤ c := fun i =>
    bound_of_isAffine K (𝒰.f i ≫ f) (by simpa only [specGenericFibreInclusion_eq] using hsm i)
  choose c hc using hb
  refine ⟨∑ i, c i, fun R' _ _ _ _ h x => ?_⟩
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (x.1 (IsLocalRing.closedPoint R'))
  have hrange : Set.range x.1 ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨z, rfl⟩
    have hz : x.1 z ⤳ x.1 (IsLocalRing.closedPoint R') :=
      (IsLocalRing.specializes_closedPoint z).map x.1.continuous
    exact (𝒰.f i).isOpenEmbedding.isOpen_range.stableUnderGeneralization hz ⟨y, hy⟩
  let a' := IsOpenImmersion.lift (𝒰.f i) x.1 hrange
  have ha' : a' ≫ 𝒰.f i = x.1 := IsOpenImmersion.lift_fac _ _ _
  have h1 : smoothnessDefect f x.1 = smoothnessDefect (𝒰.f i ≫ f) a' := by
    rw [← ha', smoothnessDefect_comp_eq]
  have h2 := hc i R' h a' (by rw [← Category.assoc, ha']; exact x.2)
  rw [h1]
  refine h2.trans ?_
  exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i)

end

end NeronModelInfra.SmootheningBounds
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.SmootheningLocalization


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace LocalizedLoci

open TensorProduct

theorem core_smooth {R k A A' : Type u} [CommRing R] [CommRing k] [CommRing A] [CommRing A']
    [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] (h : A)
      [IsLocalization.Away h A']
    (J : Ideal A) (J' : Ideal A') (hJ' : J' = J.map (algebraMap A A')) (hle : J ≤ J'.comap
      (algebraMap A A'))
    (φ : k →+* A ⧸ J) (hφ : φ.comp (algebraMap R k) = algebraMap R (A ⧸ J))
    (𝔮' : Ideal (A' ⧸ J')) [𝔮'.IsPrime]
    (hsm : ∀ [Algebra k (A ⧸ J)] [IsScalarTower R k (A ⧸ J)],
      Algebra.IsSmoothAt k (𝔮'.comap (Ideal.quotientMap J' (algebraMap A A') hle)))
    [Algebra k (A' ⧸ J')] [IsScalarTower R k (A' ⧸ J')] :
    Algebra.IsSmoothAt k 𝔮' := by
  classical
  set ι : A ⧸ J →+* A' ⧸ J' := Ideal.quotientMap J' (algebraMap A A') hle with hι
  let algBB' : Algebra (A ⧸ J) (A' ⧸ J') := ι.toAlgebra
  have hιalg : algebraMap (A ⧸ J) (A' ⧸ J') = ι := rfl
  have : IsScalarTower A (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hιalg, hι, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl
  have : IsScalarTower R (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ J), IsScalarTower.algebraMap_apply R A' (A' ⧸ J'),
      IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A (A ⧸ J) (A' ⧸ J'),
      IsScalarTower.algebraMap_apply A A' (A' ⧸ J')]
  have hloc : IsLocalization.Away (algebraMap A (A ⧸ J) h) (A' ⧸ J') := by
    have := IsLocalization.of_surjective (.powers h) A' (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
      (by ext a; rw [RingHom.comp_apply, RingHom.comp_apply, hιalg, hι, Ideal.quotientMap_mk])
      (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ'])
    rwa [Submonoid.map_powers] at this
  let : Algebra k (A ⧸ J) := φ.toAlgebra
  have : IsScalarTower R k (A ⧸ J) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, hφ]
  have : IsScalarTower k (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨r, rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply R k (A' ⧸ J'), ← IsScalarTower.algebraMap_apply R k (A
      ⧸ J),
      ← IsScalarTower.algebraMap_apply R (A ⧸ J) (A' ⧸ J')]
  have hmem : (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈ Algebra.smoothLocus k (A' ⧸ J') := by
    rw [← Algebra.smoothLocus_comap_of_isLocalization (R := k) (algebraMap A (A ⧸ J) h),
      Set.mem_preimage]
    change Algebra.IsSmoothAt k (𝔮'.comap (algebraMap (A ⧸ J) (A' ⧸ J')))
    exact hsm
  exact hmem

theorem core_free {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] (h : A)
      [IsLocalization.Away h A']
    (J : Ideal A) (J' : Ideal A') (hJ' : J' = J.map (algebraMap A A')) (hle : J ≤ J'.comap
      (algebraMap A A'))
    (𝔮' : Ideal (A' ⧸ J')) [𝔮'.IsPrime]
    (hfr : (⟨𝔮'.comap (Ideal.quotientMap J' (algebraMap A A') hle), inferInstance⟩ :
        PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈ Module.freeLocus (A' ⧸ J') ((A' ⧸ J') ⊗[A'] Ω[A'⁄R])
      := by
  classical
  set ι : A ⧸ J →+* A' ⧸ J' := Ideal.quotientMap J' (algebraMap A A') hle with hι
  let algBB' : Algebra (A ⧸ J) (A' ⧸ J') := ι.toAlgebra
  have hιalg : algebraMap (A ⧸ J) (A' ⧸ J') = ι := rfl
  have : IsScalarTower A (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hιalg, hι, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl
  have : IsScalarTower R (A ⧸ J) (A' ⧸ J') := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ J), IsScalarTower.algebraMap_apply R A' (A' ⧸ J'),
      IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A (A ⧸ J) (A' ⧸ J'),
      IsScalarTower.algebraMap_apply A A' (A' ⧸ J')]
  have hloc : IsLocalization.Away (algebraMap A (A ⧸ J) h) (A' ⧸ J') := by
    have := IsLocalization.of_surjective (.powers h) A' (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
      (by ext a; rw [RingHom.comp_apply, RingHom.comp_apply, hιalg, hι, Ideal.quotientMap_mk])
      (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ'])
    rwa [Submonoid.map_powers] at this
  have h1 : (⟨𝔮', ‹_›⟩ : PrimeSpectrum (A' ⧸ J')) ∈
      Module.freeLocus (A' ⧸ J') ((A' ⧸ J') ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R])) :=
    Module.comap_freeLocus_le (Set.mem_preimage.mpr hfr)
  have hbc : IsBaseChange A' (KaehlerDifferential.map R R A A') :=
    (isLocalizedModule_iff_isBaseChange (.powers h) A' _).mp inferInstance
  let e₁ := AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A' ⧸ J') (A' ⧸ J') Ω[A⁄R]
  let e₂ := (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ J') (A' ⧸ J') Ω[A⁄R]).symm
  let e₃ : (A' ⧸ J') ⊗[A'] (A' ⊗[A] Ω[A⁄R]) ≃ₗ[A' ⧸ J'] (A' ⧸ J') ⊗[A'] Ω[A'⁄R] :=
    AlgebraTensorModule.congr (LinearEquiv.refl (A' ⧸ J') (A' ⧸ J')) hbc.equiv
  rw [Module.freeLocus_congr (e₁.trans (e₂.trans e₃))] at h1
  exact h1

end LocalizedLoci

namespace AffineRestriction

theorem comap_primeIdealOf_basicOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (h :
  Γ(X, U))
    (z : X) (hz : z ∈ U) (hz' : z ∈ X.basicOpen h) :
    ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩).asIdeal.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen
      h)) =
      (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  have key : PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) ((hU.basicOpen
    h).primeIdealOf ⟨z, hz'⟩) =
      hU.primeIdealOf ⟨z, hz⟩ := by
    rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint, IsAffineOpen.primeIdealOf_eq_map_closedPoint]
    change (Spec.map (X.presheaf.germ (X.basicOpen h) z hz') ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) Γ(X, X.basicOpen h)))).base
        (IsLocalRing.closedPoint _) = _
    rw [← Spec.map_comp]
    have hg : CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) ≫ X.presheaf.germ
      (X.basicOpen h) z hz' =
        X.presheaf.germ U z hz :=
      TopCat.Presheaf.germ_res X.presheaf (homOfLE (X.basicOpen_le h)) z hz'
    rw [hg]
  exact congrArg PrimeSpectrum.asIdeal key

theorem algebraMap_mem_primeIdealOf_of_mem_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) (z : U) (hz : f z.1 = IsLocalRing.closedPoint R)
    (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :
    let : Algebra R Γ(X, U) := f.sectionsAlgebra U
    algebraMap R Γ(X, U) r ∈ (hU.primeIdealOf z).asIdeal := by
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at hsq
  have h1 := congrArg (fun g : Spec Γ(X, U) ⟶ Spec (CommRingCat.of R) => g.base (hU.primeIdealOf
    z)) hsq
  have h1' : (Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv).base ((Spec.map (f.appLE ⊤ U
    le_top)).base (hU.primeIdealOf z)) =
      f.base (hU.fromSpec.base (hU.primeIdealOf z)) := h1
  rw [hU.fromSpec_primeIdealOf] at h1'
  replace h1 := h1'.trans hz
  have h2 : r ∈ (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (PrimeSpectrum.comap (f.appLE ⊤ U le_top).hom (hU.primeIdealOf z))).asIdeal := by
    have : (PrimeSpectrum.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (PrimeSpectrum.comap (f.appLE ⊤ U le_top).hom (hU.primeIdealOf z))) =
        IsLocalRing.closedPoint R := h1
    rw [this]
    exact hr
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.mem_comap] at h2
  have happ : (f.appLE ⊤ U le_top).hom = (X.presheaf.map (homOfLE le_top).op).hom.comp
    f.appTop.hom := by
    have : f.appLE ⊤ U le_top = f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
      rfl
    rw [this, CommRingCat.hom_comp]
  rw [happ] at h2
  exact h2

end AffineRestriction

theorem _root_.NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (C : Set X) (hC : ∀ y ∈ C, f y = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) (h : Γ(X, U)) (y : X) (hyU : y ∈ U) (hyh : y ∈
      X.basicOpen h) :
    let : Algebra R Γ(X, U) := f.sectionsAlgebra U
    let : Algebra R Γ(X, X.basicOpen h) := f.sectionsAlgebra (X.basicOpen h)
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
    let J' : Ideal Γ(X, X.basicOpen h) :=
      PrimeSpectrum.vanishingIdeal ((fun z : X.basicOpen h => (hU.basicOpen h).primeIdealOf z) ''
        {z : X.basicOpen h | (z : X) ∈ C})
    (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
      𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
      (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
        Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) →
    ∀ (𝔮' : Ideal (Γ(X, X.basicOpen h) ⧸ J')) [𝔮'.IsPrime],
      𝔮'.comap (Ideal.Quotient.mk J') = ((hU.basicOpen h).primeIdealOf ⟨y, hyh⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮') ∧
      (⟨𝔮', ‹_›⟩ : PrimeSpectrum (Γ(X, X.basicOpen h) ⧸ J')) ∈
        Module.freeLocus (Γ(X, X.basicOpen h) ⧸ J')
          ((Γ(X, X.basicOpen h) ⧸ J') ⊗[Γ(X, X.basicOpen h)] Ω[Γ(X, X.basicOpen h)⁄R]) := by
  intro algA algA' J J' hgood 𝔮' _ h𝔮'
  classical
  have : IsLocalization.Away h Γ(X, X.basicOpen h) := hU.isLocalization_basicOpen h
  have halg : ∀ t : Γ(X, U), algebraMap Γ(X, U) Γ(X, X.basicOpen h) t = (X.presheaf.map (homOfLE
    (X.basicOpen_le h)).op).hom t :=
    fun t => rfl
  have : IsScalarTower R Γ(X, U) Γ(X, X.basicOpen h) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg]
    change (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso
      (CommRingCat.of R)).inv.hom r)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom
        ((X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso
          (CommRingCat.of R)).inv.hom r)))
    rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE le_top).op) (X.presheaf.map (homOfLE
      (X.basicOpen_le h)).op),
      ← X.presheaf.map_comp]
    rfl
  have hS2 : ∀ (z : X) (hz : z ∈ U) (hz' : z ∈ X.basicOpen h),
      ((hU.basicOpen h).primeIdealOf ⟨z, hz'⟩).asIdeal.comap (algebraMap Γ(X, U) Γ(X,
        X.basicOpen h)) =
        (hU.primeIdealOf ⟨z, hz⟩).asIdeal := AffineRestriction.comap_primeIdealOf_basicOpen hU h
  have hbo : ∀ (z : X) (hz : z ∈ U), z ∉ X.basicOpen h → h ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal
    := by
    intro z hz hzh
    by_contra hh
    apply hzh
    have h1 : hU.primeIdealOf ⟨z, hz⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hh
    have h2 : hU.fromSpec (hU.primeIdealOf ⟨z, hz⟩) ∈ X.basicOpen h := h1
    rwa [hU.fromSpec_primeIdealOf] at h2
  have hJle : J ≤ J'.comap (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) := by
    intro g hg
    rw [Ideal.mem_comap]
    change _ ∈ PrimeSpectrum.vanishingIdeal _
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro _ ⟨⟨z, hz'⟩, hzC, rfl⟩
    have hzU : z ∈ U := X.basicOpen_le h hz'
    rw [← Ideal.mem_comap, hS2 z hzU hz']
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg _ ⟨⟨z, hzU⟩, hzC, rfl⟩
  have hJ' : J' = J.map (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) := by
    apply le_antisymm _ (Ideal.map_le_iff_le_comap.mpr hJle)
    intro g' hg'
    obtain ⟨⟨g, s⟩, hgs⟩ := IsLocalization.surj (Submonoid.powers h) g'
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h)]
    refine ⟨⟨⟨g * h, ?_⟩, ⟨(s : Γ(X, U)) * h, Submonoid.mul_mem _ s.2 (Submonoid.mem_powers
      h)⟩⟩, ?_⟩
    · change g * h ∈ PrimeSpectrum.vanishingIdeal _
      rw [PrimeSpectrum.mem_vanishingIdeal]
      rintro _ ⟨⟨z, hzU⟩, hzC, rfl⟩
      by_cases hz' : z ∈ X.basicOpen h
      · have h1 : algebraMap Γ(X, U) Γ(X, X.basicOpen h) g ∈ ((hU.basicOpen h).primeIdealOf ⟨z,
        hz'⟩).asIdeal := by
          rw [← hgs]
          exact Ideal.mul_mem_right _ _ ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hg' _ ⟨⟨z,
            hz'⟩, hzC, rfl⟩)
        rw [← Ideal.mem_comap, hS2 z hzU hz'] at h1
        exact Ideal.mul_mem_right _ _ h1
      · exact Ideal.mul_mem_left _ _ (hbo z hzU hz')
    · change g' * algebraMap Γ(X, U) Γ(X, X.basicOpen h) ((s : Γ(X, U)) * h) = algebraMap Γ(X,
      U) Γ(X, X.basicOpen h) (g * h)
      rw [map_mul, map_mul, ← hgs, mul_assoc]
  set ι' : Γ(X, U) ⧸ J →+* Γ(X, X.basicOpen h) ⧸ J' :=
    Ideal.quotientMap J' (algebraMap Γ(X, U) Γ(X, X.basicOpen h)) hJle with hι'
  have : (𝔮'.comap ι').IsPrime := Ideal.comap_isPrime ι' 𝔮'
  have h𝔮 : (𝔮'.comap ι').comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [Ideal.comap_comap, hι', Ideal.quotientMap_comp_mk hJle, ← Ideal.comap_comap, h𝔮', hS2 y
      hyU hyh]
  obtain ⟨hsm, hfr⟩ := hgood (𝔮'.comap ι') h𝔮
  have hmJ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R Γ(X, U) r ∈ J := by
    intro r hr
    change _ ∈ PrimeSpectrum.vanishingIdeal _
    rw [PrimeSpectrum.mem_vanishingIdeal]
    rintro _ ⟨z, hzC, rfl⟩
    exact AffineRestriction.algebraMap_mem_primeIdealOf_of_mem_maximalIdeal f hU z (hC _ hzC) r hr
  let φ : IsLocalRing.ResidueField R →+* Γ(X, U) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (Γ(X, U) ⧸ J)) (fun r hr => by
      rw [IsScalarTower.algebraMap_apply R Γ(X, U) (Γ(X, U) ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hmJ r hr)
  have hφ : φ.comp (algebraMap R (IsLocalRing.ResidueField R)) = algebraMap R (Γ(X, U) ⧸ J) := by
    ext r; rfl
  have hk : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) :=
    Ideal.Quotient.mk_surjective
  refine ⟨?_, ?_⟩
  · intro instK instT
    exact LocalizedLoci.core_smooth hk h J J' hJ' hJle φ hφ 𝔮' hsm
  · exact LocalizedLoci.core_free (R := R) h J J' hJ' hJle 𝔮' hfr

end NeronModelInfra.SmootheningLocalization
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.SmootheningConormal


open TensorProduct KaehlerDifferential NeronModelInfra

universe u

theorem _root_.NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A]
      [IsScalarTower R C A]
    (_hsurj : Function.Surjective (algebraMap C A))
    {n : ℕ} (z : Fin n → C)
    (hIJ : RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)))
    (hlin : LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
      fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
        D R A (algebraMap C A (z j)))
    (hN : ∀ g : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C A) ≤ RingHom.ker c.toRingHom →
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ≤ (IsLocalRing.maximalIdeal
            R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g ∈ Ideal.span (insert (algebraMap R C π) (Set.range z))) :
    RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)) ^ 2 := by
  classical
  set π' : C := algebraMap R C π with hπ'
  set J : Ideal C := Ideal.span (insert π' (Set.range z)) with hJ
  have hπJ : π' ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hzJ : ∀ j, z j ∈ J := fun j => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  intro f hf
  have hfJ : f ∈ J := hIJ hf
  rw [hJ, Ideal.mem_span_insert] at hfJ
  obtain ⟨g, h, hh, hfgh⟩ := hfJ
  obtain ⟨gj, hgj⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hh
  let φ := algebraMap C A
  have hφf : φ f = 0 := hf
  let ι : Ω[A⁄R] →ₗ[C] (C ⧸ J) ⊗[C] Ω[A⁄R] := TensorProduct.mk C (C ⧸ J) Ω[A⁄R] 1
  have hιsmul : ∀ (c : C) (ω : Ω[A⁄R]), ι (φ c • ω) = (Ideal.Quotient.mk J c) • ι ω := by
    intro c ω
    rw [algebraMap_smul, map_smul]
    change c • ((1 : C ⧸ J) ⊗ₜ[C] ω) = (Ideal.Quotient.mk J c) • ((1 : C ⧸ J) ⊗ₜ[C] ω)
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      smul_eq_mul, mul_one]
    rfl
  have hιJ : ∀ (c : C), c ∈ J → ∀ ω : Ω[A⁄R], ι (φ c • ω) = 0 := by
    intro c hc ω
    rw [hιsmul, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_smul]
  have hDπ : D R A (φ π') = 0 := by
    change D R A (algebraMap C A (algebraMap R C π)) = 0
    rw [← IsScalarTower.algebraMap_apply R C A π, Derivation.map_algebraMap]
  have hDf : D R A (φ f) = φ π' • D R A (φ g) +
      ∑ j, (φ (gj j) • D R A (φ (z j)) + φ (z j) • D R A (φ (gj j))) := by
    rw [hfgh, ← hgj, map_add, map_mul, map_sum, map_add, Derivation.leibniz, hDπ, smul_zero,
      zero_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Derivation.leibniz]
  have hsum : ∑ j, (Ideal.Quotient.mk J (gj j)) • ι (D R A (φ (z j))) = 0 := by
    have h0 : ι (D R A (φ f)) = 0 := by rw [hφf, map_zero, map_zero]
    rw [hDf, map_add, hιJ π' hπJ, zero_add, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, hιJ (z j) (hzJ j), add_zero, hιsmul]
  have hgjJ : ∀ j, gj j ∈ J := by
    intro j
    have := Fintype.linearIndependent_iff.mp hlin (fun j => Ideal.Quotient.mk J (gj j)) hsum j
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hhJ2 : h ∈ J ^ 2 := by
    rw [← hgj, pow_two]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul (hgjJ j) (hzJ j)
  have hgJ : g ∈ J := by
    refine hN g fun R'' _ _ _ _ _ hR'' c hker hspec => ?_
    have hm : IsLocalRing.maximalIdeal R'' = Ideal.span {algebraMap R R'' π} := by
      rw [← hR''.map_maximalIdeal, hπ, Ideal.map_span, Set.image_singleton]
    have hπ''ne : algebraMap R R'' π ≠ 0 := by
      intro h0
      have : IsLocalRing.maximalIdeal R'' = ⊥ := by rw [hm, h0, Ideal.span_singleton_eq_bot]
      exact IsDiscreteValuationRing.not_isField R'' (IsLocalRing.isField_iff_maximalIdeal_eq.mpr
        this)
    have hcf : c f = 0 := by
      have : f ∈ RingHom.ker c.toRingHom := hker hf
      exact this
    have hch : c h ∈ IsLocalRing.maximalIdeal R'' ^ 2 := by
      have h1 : J ^ 2 ≤ ((IsLocalRing.maximalIdeal R'').comap c) ^ 2 := Ideal.pow_right_mono
        hspec 2
      have h2 := (h1.trans (Ideal.le_comap_pow _ 2)) hhJ2
      exact h2
    have hcπ : c π' = algebraMap R R'' π := by rw [hπ']; exact c.commutes π
    rw [Ideal.mem_comap]
    have hrel : algebraMap R R'' π * c g = - c h := by
      have := congrArg c hfgh
      rw [hcf, map_add, map_mul, hcπ] at this
      linear_combination -this
    rw [hm, pow_two, Ideal.span_singleton_mul_span_singleton] at hch
    rw [hm, Ideal.mem_span_singleton]
    have : algebraMap R R'' π * algebraMap R R'' π ∣ algebraMap R R'' π * c g := by
      rw [hrel]; exact (Ideal.mem_span_singleton.mp hch).neg_right
    exact (mul_dvd_mul_iff_left hπ''ne).mp this
  rw [hfgh, pow_two]
  exact Ideal.add_mem _ (Ideal.mul_mem_mul hgJ hπJ) (pow_two J ▸ hhJ2)

end NeronModelInfra.SmootheningConormal
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.SmootheningClosure


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem _root_.NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ :
      IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1
        (IsLocalRing.closedPoint R') = s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    let : Algebra R Γ(X, U) := f.sectionsAlgebra U
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈
        closure S})
    ∀ g : Γ(X, U),
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J := by
  intro algA J g hg
  rw [PrimeSpectrum.mem_vanishingIdeal]
  rintro 𝔭 ⟨y, hy, rfl⟩
  let Z : Set U := {z : U | g ∈ (hU.primeIdealOf z).asIdeal}
  have hZ : IsClosed Z := by
    have : Z = hU.isoSpec.hom.base ⁻¹' PrimeSpectrum.zeroLocus {g} := by
      ext z
      change g ∈ (hU.isoSpec.hom.base z).asIdeal ↔ ({g} : Set Γ(X, U)) ⊆ ((hU.isoSpec.hom.base
        z).asIdeal : Set Γ(X, U))
      rw [Set.singleton_subset_iff]
      rfl
    rw [this]
    exact (PrimeSpectrum.isClosed_zeroLocus _).preimage hU.isoSpec.hom.base.hom.continuous
  let A : Set U := {s : U | (s : X) ∈ S}
  have hAZ : A ⊆ Z := by
    intro s hs
    obtain ⟨R', _, _, _, _, _, hR', x, hx⟩ := hS s.1 hs
    have hxU : x.1 (IsLocalRing.closedPoint R') ∈ U := by rw [hx]; exact s.2
    obtain ⟨c₀, hc₀⟩ :=
      NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
        f R' x U hU hxU
    let c : Γ(X, U) →ₐ[R] R' := c₀
    have hc : (IsLocalRing.maximalIdeal R').comap c =
        (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := hc₀
    have hs' : (⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩ : U) = s := Subtype.ext hx
    have hJc : J ≤ (IsLocalRing.maximalIdeal R').comap c := by
      rw [hc]
      intro j hj
      rw [PrimeSpectrum.mem_vanishingIdeal] at hj
      exact hj _ ⟨_, by rw [hs']; exact subset_closure hs, rfl⟩
    have := hg R' hR' c hJc
    rw [hc, hs'] at this
    exact this
  have hyA : y ∈ closure A := by
    have hind : Topology.IsInducing ((↑) : U → X) := Topology.IsInducing.subtypeVal
    have key : y ∈ ((↑) : U → X) ⁻¹' closure (((↑) : U → X) '' A) := by
      rw [Set.mem_preimage]
      refine closure_mono ?_ (show (y : X) ∈ closure ((U : Set X) ∩ S) from U.2.inter_closure
        ⟨y.2, hy⟩)
      rintro _ ⟨hzU, hzS⟩
      exact ⟨⟨_, hzU⟩, hzS, rfl⟩
    exact (hind.closure_eq_preimage_closure_image A).symm ▸ key
  exact hZ.closure_subset_iff.mpr hAZ hyA

end NeronModelInfra.SmootheningClosure
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.SmootheningStrata


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace SpecialFibreStrata

section ResidueAlgebra

variable {R : Type u} [CommRing R] [IsLocalRing R] {B : Type u} [CommRing B] [Algebra R B]

/-- The residue-field algebra induced by annihilation of the maximal ideal. -/
@[reducible] noncomputable def residueFieldAlgebra
    (h : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R B r = 0) :
    Algebra (IsLocalRing.ResidueField R) B :=
  (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R B) h).toAlgebra

theorem residueFieldAlgebra_algebraMap_residue
    (h : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R B r = 0) (r : R) :
    @algebraMap (IsLocalRing.ResidueField R) B _ _ (residueFieldAlgebra h) (IsLocalRing.residue
      R r) =
      algebraMap R B r := rfl

theorem isScalarTower_residueFieldAlgebra
    (h : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R B r = 0) :
    let : Algebra (IsLocalRing.ResidueField R) B := residueFieldAlgebra h
    IsScalarTower R (IsLocalRing.ResidueField R) B := by
  intro alg
  exact IsScalarTower.of_algebraMap_eq fun r => rfl

theorem algebra_residueField_ext (i₁ i₂ : Algebra (IsLocalRing.ResidueField R) B)
    (h₁ : ∀ r : R, @algebraMap _ _ _ _ i₁ (IsLocalRing.residue R r) = algebraMap R B r)
    (h₂ : ∀ r : R, @algebraMap _ _ _ _ i₂ (IsLocalRing.residue R r) = algebraMap R B r) : i₁ =
      i₂ :=
  Algebra.algebra_ext _ _ fun x => by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [h₁, h₂]

theorem algebraMap_residue_of_isScalarTower [i : Algebra (IsLocalRing.ResidueField R) B]
    [IsScalarTower R (IsLocalRing.ResidueField R) B] (r : R) :
    algebraMap (IsLocalRing.ResidueField R) B (IsLocalRing.residue R r) = algebraMap R B r := by
  rw [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) B r]
  rfl

end ResidueAlgebra

theorem isSmoothAt_of_algebra_eq {k B : Type u} [CommRing k] [CommRing B] (i₁ i₂ : Algebra k B)
    (e : i₁ = i₂) (𝔮 : Ideal B) [𝔮.IsPrime] (h : @Algebra.IsSmoothAt k B _ _ i₂ 𝔮 _) :
    @Algebra.IsSmoothAt k B _ _ i₁ 𝔮 _ := by
  subst e; exact h

theorem setOf_coe_mem_closure {X : Type u} [TopologicalSpace X] (U : TopologicalSpace.Opens X)
    (S : Set X) : {z : U | (z : X) ∈ closure S} = closure {z : U | (z : X) ∈ S} := by
  have h : IsOpenMap (Subtype.val : U → X) := U.2.isOpenMap_subtype_val
  exact h.preimage_closure_eq_closure_preimage continuous_subtype_val S

theorem image_primeIdealOf_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (S : Set
  X) :
    (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S} =
      closure ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ S}) := by
  have e : (fun z : U => hU.primeIdealOf z) = Scheme.homeoOfIso hU.isoSpec := rfl
  rw [e, setOf_coe_mem_closure U S]
  exact (Scheme.homeoOfIso hU.isoSpec).image_closure _

theorem finiteType_chart {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec
  (CommRingCat.of R))
    [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).FiniteType := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType := by
    refine RingHom.FiniteType.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of
      R)).hom.hom x, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of
      R)).inv).hom x = x
    rw [Iso.hom_inv_id]; rfl
  exact h1.comp h2

end SpecialFibreStrata

open SpecialFibreStrata

theorem _root_.NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ :
      IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1
        (IsLocalRing.closedPoint R') = s)
    (_hSk : ∀ s ∈ S, f s = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) :
    let : Algebra R Γ(X, U) := f.sectionsAlgebra U
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈
        closure S})
    ∃ W : X.Opens, (W : Set X) ⊆ U ∧
      ((closure S ∩ (U : Set X)).Nonempty → (closure S ∩ (W : Set X)).Nonempty) ∧
      ∀ (y : X) (hyU : y ∈ U), y ∈ closure S →
        (y ∈ W ↔
          ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
            𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
            (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
              [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
              Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
            (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
              Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) := by
  intro iRA J
  set S₀ : Set (PrimeSpectrum Γ(X, U)) := (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ S}
    with hS₀def
  have hT : (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S} = closure S₀ :=
    image_primeIdealOf_closure hU S
  have hJ : J = PrimeSpectrum.vanishingIdeal S₀ := by
    change PrimeSpectrum.vanishingIdeal _ = _
    rw [hT, PrimeSpectrum.vanishingIdeal_closure]
  have hZ : PrimeSpectrum.zeroLocus (J : Set Γ(X, U)) = closure S₀ := by
    rw [hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = closure S₀ := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hZ]
  have key : ∀ p ∈ S₀, ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')),
      Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R') ∧
      ∃ c : Γ(X, U) →ₐ[R] R', (IsLocalRing.maximalIdeal R').comap c = p.asIdeal := by
    rintro p ⟨z, hz, rfl⟩
    obtain ⟨R', _, _, _, _, _, hidx, x, hx⟩ := hS z hz
    have hxU : x.1 (IsLocalRing.closedPoint R') ∈ U := by rw [hx]; exact z.2
    obtain ⟨c₀, hc₀⟩ :=
      NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
        f R' x U hU hxU
    let c : Γ(X, U) →ₐ[R] R' := c₀
    have hc : (IsLocalRing.maximalIdeal R').comap c =
        (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := hc₀
    have hz' : (⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩ : U) = z := Subtype.ext hx
    refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance,
      hidx.formallySmooth_residueField, c, ?_⟩
    rw [hc, hz']
  have hmJ : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R Γ(X, U) r ∈ J := by
    intro r hr
    rw [hJ, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    obtain ⟨R', _, _, _, _, -, c, hc⟩ := key p hp
    rw [← hc, Ideal.mem_comap, AlgHom.commutes]
    exact (IsLocalRing.mem_maximalIdeal _).2
      ((map_mem_nonunits_iff (algebraMap R R') r).2 ((IsLocalRing.mem_maximalIdeal r).1 hr))
  have hmB : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (Γ(X, U) ⧸ J) r = 0 := by
    intro r hr
    rw [← Ideal.Quotient.mk_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ r hr)
  let ikB : Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J) := residueFieldAlgebra hmB
  have itow : IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J) :=
    isScalarTower_residueFieldAlgebra hmB
  have : IsReduced (Γ(X, U) ⧸ J) :=
    (Ideal.isRadical_iff_quotient_reduced J).1 (PrimeSpectrum.isRadical_vanishingIdeal _)
  have iFT : Algebra.FiniteType R Γ(X, U) := finiteType_chart f U hU
  have : Algebra.FiniteType R (Γ(X, U) ⧸ J) := inferInstance
  have : Algebra.FiniteType (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : Algebra.FinitePresentation R Γ(X, U) := Algebra.FinitePresentation.of_finiteType.1 iFT
  have : Module.FinitePresentation Γ(X, U) Ω[Γ(X, U)⁄R] := inferInstance
  set S' : Set (PrimeSpectrum (Γ(X, U) ⧸ J)) := PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' S₀
    with hS'def
  have hdense : ∀ g : Γ(X, U) ⧸ J, (∀ 𝔰 ∈ S', g ∈ 𝔰.asIdeal) → g = 0 := by
    intro g hg
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective g
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [hJ, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    obtain ⟨𝔰, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
      rw [hrange]; exact subset_closure hp
    exact Ideal.mem_comap.1 (hg 𝔰 hp)
  have hsep : ∀ 𝔰 ∈ S', ∃ (K : Type u) (_ : Field K) (_ : Algebra (IsLocalRing.ResidueField R) K),
      Algebra.FormallySmooth (IsLocalRing.ResidueField R) K ∧
        Nonempty (𝔰.asIdeal.ResidueField →ₐ[IsLocalRing.ResidueField R] K) := by
    intro 𝔰 h𝔰
    obtain ⟨R', _, _, _, _, hfs, c, hc⟩ := key _ h𝔰
    have hc' : ∀ a : Γ(X, U), Ideal.Quotient.mk J a ∈ 𝔰.asIdeal ↔ c a ∈ IsLocalRing.maximalIdeal
      R' := by
      intro a
      have h1 : a ∈ (IsLocalRing.maximalIdeal R').comap c ↔ c a ∈ IsLocalRing.maximalIdeal R' :=
        Ideal.mem_comap
      rw [← h1, hc]
      exact Ideal.mem_comap.symm
    let ψ₀ : Γ(X, U) ⧸ J →+* IsLocalRing.ResidueField R' :=
      Ideal.Quotient.lift J ((IsLocalRing.residue R').comp c.toRingHom) fun a ha => by
        have : Ideal.Quotient.mk J a ∈ 𝔰.asIdeal := by
          rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact 𝔰.asIdeal.zero_mem
        change IsLocalRing.residue R' (c a) = 0
        exact (IsLocalRing.residue_eq_zero_iff _).2 ((hc' a).1 this)
    have hψcomm : ∀ x, ψ₀ (algebraMap (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J) x) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R') x := by
      intro x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
      change IsLocalRing.residue R' (c (algebraMap R Γ(X, U) r)) = _
      rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_residue]
    let ψ : Γ(X, U) ⧸ J →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R' := AlgHom.mk
      ψ₀ hψcomm
    have hψ : ∀ a, ψ (Ideal.Quotient.mk J a) = IsLocalRing.residue R' (c a) := fun a => rfl
    refine ⟨IsLocalRing.ResidueField R', inferInstance, inferInstance, hfs,
      ⟨Ideal.ResidueField.liftₐ 𝔰.asIdeal ψ ?_ ?_⟩⟩
    · intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker]
      change ψ (Ideal.Quotient.mk J a) = 0
      rw [hψ]
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((hc' a).1 hx)
    · intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      change IsUnit (ψ (Ideal.Quotient.mk J a))
      rw [hψ]
      exact isUnit_iff_ne_zero.2 fun h0 => hx ((hc' a).2 ((IsLocalRing.residue_eq_zero_iff _).1
        h0))
  obtain ⟨hopen, hmin⟩ :=
    Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
      (k := IsLocalRing.ResidueField R) Ω[Γ(X, U)⁄R] J S' hdense hsep
  obtain ⟨O, hO, hOG⟩ :=
    ((PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isInducing.isOpen_iff).1 hopen
  have hGiff : ∀ 𝔮 : PrimeSpectrum (Γ(X, U) ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) 𝔮 ∈ O ↔
      (Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮.asIdeal ∧
        𝔮 ∈ Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) := fun 𝔮 =>
    Set.ext_iff.1 hOG 𝔮
  let W : X.Opens := hU.fromSpec ''ᵁ ⟨O, hO⟩
  have hWmem : ∀ (y : X) (hy : y ∈ U), y ∈ W ↔ hU.primeIdealOf ⟨y, hy⟩ ∈ O := by
    intro y hy
    have := hU.fromSpec.apply_mem_image_iff (U := ⟨O, hO⟩) (x := hU.primeIdealOf ⟨y, hy⟩)
    rw [hU.fromSpec_primeIdealOf] at this
    exact this
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro x ⟨q, -, rfl⟩
    have := hU.range_fromSpec
    rw [Set.ext_iff] at this
    exact (this _).1 ⟨q, rfl⟩
  · rintro ⟨x, hxc, hxU⟩
    obtain ⟨𝔮₁, h𝔮₁⟩ : hU.primeIdealOf ⟨x, hxU⟩ ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk J)) := by
      rw [hrange, ← hT]; exact ⟨⟨x, hxU⟩, hxc, rfl⟩
    obtain ⟨q, hqmin, -⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (Γ(X, U) ⧸ J))) (J := 𝔮₁.asIdeal) bot_le
    have hqprime : q.IsPrime := hqmin.1.1
    have hqO : PrimeSpectrum.comap (Ideal.Quotient.mk J) ⟨q, hqprime⟩ ∈ O :=
      (hGiff _).2 (hmin ⟨q, hqprime⟩ hqmin)
    obtain ⟨z, hz, hzq⟩ : PrimeSpectrum.comap (Ideal.Quotient.mk J) ⟨q, hqprime⟩ ∈
        (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S} := by
      rw [hT, ← hrange]; exact ⟨_, rfl⟩
    refine ⟨z, hz, (hWmem z z.2).2 ?_⟩
    have hzq' : hU.primeIdealOf z = _ := hzq
    change hU.primeIdealOf z ∈ O
    rw [hzq']; exact hqO
  · intro y hyU hyc
    obtain ⟨𝔮₁, h𝔮₁⟩ : hU.primeIdealOf ⟨y, hyU⟩ ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk J)) := by
      rw [hrange, ← hT]; exact ⟨⟨y, hyU⟩, hyc, rfl⟩
    rw [hWmem y hyU, ← h𝔮₁, hGiff]
    constructor
    · rintro ⟨hsm, hfr⟩ 𝔮 _ h𝔮
      have e : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) = 𝔮₁ := by
        apply PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
        apply PrimeSpectrum.ext
        change 𝔮.comap (Ideal.Quotient.mk J) = _
        rw [h𝔮]
      have e' : 𝔮 = 𝔮₁.asIdeal := congrArg PrimeSpectrum.asIdeal e
      subst e'
      refine ⟨?_, hfr⟩
      intro inst tow
      exact isSmoothAt_of_algebra_eq inst _ (algebra_residueField_ext inst _
        (fun r => @algebraMap_residue_of_isScalarTower R _ _ _ _ _ inst tow r)
        (residueFieldAlgebra_algebraMap_residue hmB)) _ hsm
    · intro h
      obtain ⟨hsm, hfr⟩ := h 𝔮₁.asIdeal rfl
      exact ⟨hsm, hfr⟩

end NeronModelInfra.SmootheningStrata
end
