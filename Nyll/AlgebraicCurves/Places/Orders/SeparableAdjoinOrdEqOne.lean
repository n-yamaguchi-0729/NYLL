/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.FunctionFields.FrobeniusSubfield
public import Nyll.AlgebraicCurves.Differentials.Basic
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.IsAlgebraicAdjoinTranscendental
public import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Unramified.Field

/-!
# Place is Separable adjoin of ord eq one
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlaceSeparableAdjoinOrdOne
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace SEPEngine
open _root_.AlgebraicCurve

open IntermediateField Polynomial

private def frobeniusSubfield (M : Type*) [Field M] (p : ℕ) [ExpChar M p] : Subfield M :=
  (frobenius M p).fieldRange

end AlgebraicCurve.SEPEngine

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace SEPEngine
open _root_.AlgebraicCurve

open KaehlerDifferential IntermediateField

private theorem not_pow_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) {p : ℕ} (hp : 2 ≤ p) (a : F) :
    a ^ p ≠ t := by
  intro h
  have h2 : (p : ℤ) * v.ord a = 1 := by
    rw [← v.ord_zpow, zpow_natCast, h, ht]
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h2
  omega

private theorem D_pow_eq_zero {E M : Type*} [CommRing E] [CommRing M]
    [Algebra E M] (p : ℕ) [Fact p.Prime] [CharP M p] (a : M) :
    D E M (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul M, CharP.cast_eq_zero M p, zero_smul]

private theorem isSeparable_of_not_pow_mem_range {E M : Type*} [Field E] [Field M]
    [Algebra E M] (p : ℕ) [hp : Fact p.Prime] [CharP M p]
    [FiniteDimensional E M]
    (hfr : haveI : ExpChar M p := ExpChar.prime hp.out
      Module.finrank (frobeniusSubfield M p) M = p)
    {t : M} (htE : t ∈ (algebraMap E M).range) (htp : ∀ a : M, a ^ p ≠ t) :
    Algebra.IsSeparable E M := by
  have : ExpChar M p := ExpChar.prime hp.out
  obtain ⟨tE, rfl⟩ := htE
  have hDt : D E M (algebraMap E M tE) = 0 := (D E M).map_algebraMap tE
  have hDzero : ∀ m : M, D E M m = 0 := by
    intro m
    obtain ⟨a, rfl⟩ := pDigits_exists_of_finrank_eq p hfr htp m
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Derivation.leibniz, D_pow_eq_zero p (a i),
      smul_zero, add_zero, Derivation.leibniz_pow, hDt, smul_zero,
      ← Nat.cast_smul_eq_nsmul M, smul_zero, smul_zero]
  have hsubsingleton : Subsingleton (Ω[M⁄E]) := by
    refine ⟨fun ω₁ ω₂ ↦ ?_⟩
    have htop : (⊤ : Submodule M (Ω[M⁄E])) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨m, rfl⟩; exact hDzero m
    have h1 : ω₁ ∈ (⊥ : Submodule M (Ω[M⁄E])) := htop ▸ Submodule.mem_top
    have h2 : ω₂ ∈ (⊥ : Submodule M (Ω[M⁄E])) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at h1 h2; rw [h1, h2]
  have : Algebra.FormallyUnramified E M := ⟨hsubsingleton⟩
  exact Algebra.FormallyUnramified.isSeparable E M

end AlgebraicCurve.SEPEngine

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.PlaceSeparableAdjoinOrdOne.AlgebraicCurve
  AlgebraicCurve.SEPEngine IntermediateField in
open scoped IntermediateField in
theorem _root_.AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one {K F : Type*} [Field K]
  [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  have ht0 : v.ord t ≠ 0 := by rw [ht]; exact one_ne_zero
  have htr : Transcendental K t := v.transcendental_of_ord_ne_zero ht0
  have halg : Algebra.IsAlgebraic (↥K⟮t⟯) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x htr
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have := hq
  cases hq with
  | zero =>
    have : CharZero (↥K⟮t⟯) := charZero_of_injective_algebraMap (algebraMap K _).injective
    infer_instance
  | prime hqp =>
    have : Fact q.Prime := ⟨hqp⟩
    have htp : ∀ a : F, a ^ q ≠ t := fun a ↦ not_pow_of_ord_eq_one v ht hqp.two_le a
    have hEq : ExpChar (↥K⟮t⟯) q :=
      expChar_of_injective_algebraMap (algebraMap K _).injective q
    have hEqC : CharP (↥K⟮t⟯) q :=
      charP_of_injective_algebraMap (algebraMap K _).injective q
    have hEfr : Module.finrank (frobeniusSubfield (↥K⟮t⟯) q) (↥K⟮t⟯) = q :=
      finrank_frobeniusSubfield_adjoin_transcendental q htr
    have hEfd : FiniteDimensional (frobenius (↥K⟮t⟯) q).fieldRange (↥K⟮t⟯) :=
      .of_finrank_pos (by
        change 0 < Module.finrank (frobeniusSubfield (↥K⟮t⟯) q) (↥K⟮t⟯)
        rw [hEfr]
        exact hqp.pos)
    refine ⟨fun y ↦ ?_⟩
    have hMfd : FiniteDimensional (↥K⟮t⟯) (↥(↥K⟮t⟯)⟮y⟯) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    suffices hMsep : Algebra.IsSeparable (↥K⟮t⟯) (↥(↥K⟮t⟯)⟮y⟯) from
      isSeparable_of_mem_isSeparable _ F (mem_adjoin_simple_self (↥K⟮t⟯) y)
    have hMq : CharP (↥(↥K⟮t⟯)⟮y⟯) q :=
      charP_of_injective_algebraMap (algebraMap (↥K⟮t⟯) _).injective q
    have hMqe : ExpChar (↥(↥K⟮t⟯)⟮y⟯) q := ExpChar.prime hqp
    have hMfr : Module.finrank (frobeniusSubfield (↥(↥K⟮t⟯)⟮y⟯) q) (↥(↥K⟮t⟯)⟮y⟯) = q := by
      exact (finrank_frobeniusSubfield_eq
        (E := ↥K⟮t⟯) (M := ↥(↥K⟮t⟯)⟮y⟯) q).trans hEfr
    refine isSeparable_of_not_pow_mem_range q hMfr (t := algebraMap (↥K⟮t⟯) _
        ⟨t, mem_adjoin_simple_self K t⟩) ⟨_, rfl⟩ ?_
    intro a ha
    apply htp ((a : F))
    have h1 : ((a ^ q : ↥(↥K⟮t⟯)⟮y⟯) : F) =
        ((algebraMap (↥K⟮t⟯) _ ⟨t, mem_adjoin_simple_self K t⟩ : ↥(↥K⟮t⟯)⟮y⟯) : F) :=
      congrArg _ ha
    simpa using h1

end
end AlgebraicCurves.Places.Proofs.PlaceSeparableAdjoinOrdOne
end ProofImplementation
