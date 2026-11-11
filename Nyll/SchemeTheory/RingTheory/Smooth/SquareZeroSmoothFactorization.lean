/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.NilpotentSmoothFactorizationLift
public import Nyll.SchemeTheory.RingTheory.Smooth.SquareZeroFlatRelationLift
public import Nyll.SchemeTheory.RingTheory.Smooth.NilpotentFlatRelationLift
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Removing relations across a square-zero base ideal

The factorization hypothesis modulo the base ideal is the original
ind-smooth hypothesis in the nilpotent reduction. It is used on the
explicit finitely presented relation algebra constructed by the flatness
criterion. Its actual factorization is lifted, and formal smoothness
then removes the relation without changing the map to the target.

This is the relation-removal construction of Stacks Project, Lemma 16.5.2:
https://stacks.math.columbia.edu/tag/07CL
The modulo-ideal factorization hypothesis is not asserted for an
arbitrary completion here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {L : Type v}
  [CommRing R] [CommRing L] [Algebra R L]
  (I : Ideal R)
  (hmod : ∀ (A₀ : Type u) [CommRing A₀] [Algebra (R ⧸ I) A₀]
      [FinitePresentation (R ⧸ I) A₀]
      (φ₀ : A₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra (R ⧸ I) B₀),
      IsStandardSmooth (R ⧸ I) B₀ ∧
        ∃ (α₀ : A₀ →ₐ[R ⧸ I] B₀)
          (β₀ : B₀ →ₐ[R ⧸ I] L ⧸ I.map (algebraMap R L)),
          β₀.comp α₀ = φ₀)

include hmod

/-- A finite presentation over the original base descends to a finite
presentation over the quotient base. Applying the supplied modulo-ideal
factorization and lifting gives an actual smooth quotient stage. -/
theorem exists_smooth_quotient_factorization_of_modulo_factorizations
    {A : Type u} [CommRing A] [Algebra R A] [FinitePresentation R A]
    (hI : IsNilpotent I) (φ : A →ₐ[R] L) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ J : Ideal B, J.FG ∧ J ≤ I.map (algebraMap R B) ∧
        ∃ (α : A →ₐ[R] B ⧸ J) (β : B ⧸ J →ₐ[R] L), β.comp α = φ := by
  let IA := I.map (algebraMap R A)
  let IL := I.map (algebraMap R L)
  have : FinitePresentation (R ⧸ I) (A ⧸ IA) :=
    FinitePresentation.equiv (TensorProduct.quotIdealMapEquivQuotTensor A I).symm
  have hmap : IA ≤ IL.comap φ.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change φ (algebraMap R A r) ∈ IL
    rw [φ.commutes]
    exact Ideal.mem_map_of_mem (algebraMap R L) hr
  let φq : A ⧸ IA →ₐ[R] L ⧸ IL := Ideal.quotientMapₐ IL φ hmap
  let φ₀ : A ⧸ IA →ₐ[R ⧸ I] L ⧸ IL :=
    φq.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  obtain ⟨B₀, _, _, hB₀, α₀, β₀, hfac₀⟩ := hmod (A ⧸ IA) φ₀
  have : IsStandardSmooth (R ⧸ I) B₀ := hB₀
  let _ : Algebra R B₀ :=
    ((algebraMap (R ⧸ I) B₀).comp (algebraMap R (R ⧸ I))).toAlgebra
  have : IsScalarTower R (R ⧸ I) B₀ := IsScalarTower.of_algebraMap_eq' rfl
  let α : A →ₐ[R] B₀ :=
    (α₀.restrictScalars R).comp (Ideal.Quotient.mkₐ R IA)
  let β : B₀ →ₐ[R] L ⧸ IL := β₀.restrictScalars R
  have hfac : β.comp α = (Ideal.Quotient.mkₐ R IL).comp φ := by
    apply AlgHom.ext
    intro a
    have h := AlgHom.congr_fun hfac₀ (Ideal.Quotient.mk IA a)
    change β₀ (α₀ (Ideal.Quotient.mk IA a)) = φq (Ideal.Quotient.mk IA a) at h
    exact h
  exact exists_smooth_quotient_factorization_of_nilpotent I hI φ α β hfac

/-- Under the original modulo-ideal factorization hypothesis, a weighted
relation with coefficients in `K` moves into `K * I` at an actual smooth
stage. -/
theorem exists_smooth_factorization_relation_mem_mul_of_nilpotent
    [Module.Flat R L] (hI : IsNilpotent I) (K : Ideal R)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) {ι : Type*} [Fintype ι]
    (ε : ι → R) (hε : ∀ i, ε i ∈ K) (b : ι → B)
    (h : φ (∑ i, ε i • b i) = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ α (∑ i, ε i • b i) ∈ (K * I).map (algebraMap R D) := by
  obtain ⟨m, a, C, _, _, hC, γ, δ, ξ, hγδ, hb, ha⟩ :=
    exists_finitePresentation_trivializing_relation φ ε b h
  have : FinitePresentation R C := hC
  obtain ⟨D, _, _, hD, J, _hJfg, hJI, η, β, hηβ⟩ :=
    exists_smooth_quotient_factorization_of_modulo_factorizations I hmod hI δ
  obtain ⟨α, hmem, hcomp⟩ :=
    exists_lift_relation_mem_mul_of_nilpotent I hI K J hJI γ η β ε hε b a ξ hb ha
  refine ⟨D, inferInstance, inferInstance, hD,
    α, β.comp (Ideal.Quotient.mkₐ R J), ?_, hmem⟩
  rw [hcomp, ← AlgHom.comp_assoc, hηβ, hγδ]

/-- A single kernel element in `K B` moves into `(K * I) D` through an
actual smooth factorization. -/
theorem exists_smooth_factorization_element_mem_mul_of_nilpotent
    [Module.Flat R L] (hI : IsNilpotent I) (K : Ideal R)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (x : B)
    (hx : x ∈ K.map (algebraMap R B)) (hφx : φ x = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ α x ∈ (K * I).map (algebraMap R D) := by
  classical
  change x ∈ Submodule.span B ((algebraMap R B) '' (K : Set R)) at hx
  obtain ⟨s, hs, b, hb⟩ := (Submodule.mem_span_image_iff_exists_fun B).mp hx
  have hsum : (∑ i : s, (i.1 : R) • b i) = x := by
    calc
      (∑ i : s, (i.1 : R) • b i) =
          ∑ i : s, b i • algebraMap R B i.1 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Algebra.smul_def, smul_eq_mul, mul_comm]
      _ = x := hb
  have hε (i : s) : (i.1 : R) ∈ K := hs i.property
  obtain ⟨D, _, _, hD, α, β, hfac, hmem⟩ :=
    exists_smooth_factorization_relation_mem_mul_of_nilpotent
      I hmod hI K φ (fun i : s => i.1) hε b (hsum.symm ▸ hφx)
  exact ⟨D, inferInstance, inferInstance, hD, α, β, hfac, hsum ▸ hmem⟩

/-- Iterating ideal-order increase removes a kernel element in `I B`
after finitely many actual smooth stages. -/
theorem exists_smooth_factorization_killing_element_of_nilpotent
    [Module.Flat R L] (hI : IsNilpotent I)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) (hφx : φ x = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ α x = 0 := by
  have hpow (n : ℕ) :
      ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
        Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
          β.comp α = φ ∧ α x ∈ (I ^ (n + 1)).map (algebraMap R D) := by
    induction n with
    | zero =>
      refine ⟨B, inferInstance, inferInstance, inferInstance,
        AlgHom.id R B, φ, AlgHom.comp_id φ, ?_⟩
      change x ∈ (I ^ (0 + 1)).map (algebraMap R B)
      rw [Nat.zero_add, pow_one]
      exact hx
    | succ n ih =>
      obtain ⟨D, _, _, hD, α, β, hfac, hmem⟩ := ih
      have : Smooth R D := hD
      have hβx : β (α x) = 0 := (AlgHom.congr_fun hfac x).trans hφx
      obtain ⟨E, _, _, hE, γ, δ, hγδ, hγx⟩ :=
        exists_smooth_factorization_element_mem_mul_of_nilpotent
          I hmod hI (I ^ (n + 1)) β (α x) hmem hβx
      refine ⟨E, inferInstance, inferInstance, hE, γ.comp α, δ, ?_, ?_⟩
      · rw [← AlgHom.comp_assoc, hγδ, hfac]
      · change γ (α x) ∈ (I ^ (n.succ + 1)).map (algebraMap R E)
        rw [show I ^ (n.succ + 1) = I ^ (n + 1) * I from pow_succ I (n + 1)]
        exact hγx
  obtain ⟨n, hn⟩ := hI
  obtain ⟨D, _, _, hD, α, β, hfac, hmem⟩ := hpow n
  have hzero : I ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]
  rw [hzero, Ideal.map_bot] at hmem
  exact ⟨D, inferInstance, inferInstance, hD, α, β, hfac, Ideal.mem_bot.mp hmem⟩

/-- The square-zero specialization of weighted relation removal. -/
theorem exists_smooth_factorization_killing_weighted_relation_of_squareZero
    [Module.Flat R L] (hI : I ^ 2 = ⊥)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) {ι : Type*} [Fintype ι]
    (ε : ι → R) (hε : ∀ i, ε i ∈ I) (b : ι → B)
    (h : φ (∑ i, ε i • b i) = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ α (∑ i, ε i • b i) = 0 := by
  obtain ⟨D, _, _, hD, α, β, hfac, hmem⟩ :=
    exists_smooth_factorization_relation_mem_mul_of_nilpotent
      I hmod ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ I φ ε hε b h
  rw [← pow_two, hI, Ideal.map_bot] at hmem
  exact ⟨D, inferInstance, inferInstance, hD, α, β, hfac, Ideal.mem_bot.mp hmem⟩

/-- The square-zero specialization of removing a kernel element in the
extended base ideal. -/
theorem exists_smooth_factorization_killing_element_of_squareZero
    [Module.Flat R L] (hI : I ^ 2 = ⊥)
    {B : Type u} [CommRing B] [Algebra R B] [Smooth R B]
    (φ : B →ₐ[R] L) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) (hφx : φ x = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Smooth R D ∧ ∃ (α : B →ₐ[R] D) (β : D →ₐ[R] L),
        β.comp α = φ ∧ α x = 0 :=
  exists_smooth_factorization_killing_element_of_nilpotent
    I hmod ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ φ x hx hφx

end Algebra
