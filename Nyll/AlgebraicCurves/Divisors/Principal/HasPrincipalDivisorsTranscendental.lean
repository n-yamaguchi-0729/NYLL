/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.NormTrace.OrdNormEqSumFiberOverSeparable
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteSetOfOrdNeZero
public import Nyll.AlgebraicCurves.Places.Rational.RatFuncDegreeEqZeroEqOrd
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Nyll.AlgebraicCurves.Places.Orders.MinpolyCoefficientOrder

/-!
# Has Principal Divisors of transcendental
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.HasPrincipalDivisors_of_transcendental

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

section SupportTransfer

open Polynomial

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford :
  w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 :=
  _root_.AlgebraicCurve.Place.exists_minpoly_coeff_ord_ne_zero (F := F) w hf hford

open _root_.AlgebraicCurve.Place
end SupportTransfer

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

end Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

private scoped instance (v : Place K F) : CharZero v.toValuationSubring :=
  ⟨fun a b hab => Nat.cast_injective (R := F)
    (by simpa using congrArg (Subtype.val : v.toValuationSubring → F) hab)⟩

section ElementNorm

variable (v : Place K F)

omit [CharZero F] in
private theorem ord_norm_eq_sum_fiberOver {f : F'} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f :=
  _root_.AlgebraicCurve.Place.ord_norm_eq_sum_fiberOver_of_isSeparable v hf

end ElementNorm

end Place

namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor

omit [CharZero F] in
private theorem pushforwardNormFormula_of_finiteDimensional :
    Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  rw [Divisor.pushforward_apply, Place.ord_norm_eq_sum_fiberOver v hf]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiberOver F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiberOver F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [ite_eq_right fun h => hw ((Place.mem_fiberOver v).mpr h)]
    _ = ∑ w ∈ v.fiberOver F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [ite_eq_left ((Place.mem_fiberOver v).mp hw), hD w, mul_comm]

end Divisor

section T029

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

private theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : F'} (hf : f ≠ 0) :
    {w : Place K F' | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · refine Set.finite_empty.subset ?_
      intro v hv
      exact (hv (by rw [h0, Place.ord_zero])).elim
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  · intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

end T029

private theorem hasPrincipalDivisors_of_finiteDimensional_ratFunc (K : Type*) [Field K] [CharZero
  K] (F' : Type*)
    [Field F'] [Algebra K F'] [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
      [FiniteDimensional (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by
  have : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  constructor
  intro f hf
  classical
  have hfin : {w : Place K F' | w.ord f ≠ 0}.Finite :=
    finite_setOf_ord_ne_zero_of_finiteDimensional hf
  refine ⟨Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw), fun v => rfl, ?_⟩
  set D : Divisor K F' := Finsupp.onFinset hfin.toFinset (fun w => w.ord f)
      (fun w hw => hfin.mem_toFinset.mpr hw) with hDdef
  have hD : ∀ w : Place K F', D w = w.ord f := fun w => rfl
  have h0 : Divisor.degree (Divisor.pushforward (RatFunc K) D) = 0 :=
    RationalFunctionField.degree_eq_zero_of_forall_eq_ord _
      (fun v => Divisor.pushforwardNormFormula_of_finiteDimensional f hf D hD v)
  rw [← Divisor.degree_pushforward (F := RatFunc K) D]
  exact h0

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K]
  [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F :=
      by
  classical
  let e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) :=
    e.toAlgHom.toRingHom.toAlgebra
  let : Algebra (RatFunc K) F :=
    ((algebraMap (↥(IntermediateField.adjoin K ({x} : Set F))) F).comp
      e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) F :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  have : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap K F r = algebraMap (↥(IntermediateField.adjoin K ({x} : Set F))) F (e
      (algebraMap K (RatFunc K) r))
    rw [AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply K (↥(IntermediateField.adjoin K ({x} : Set F))) F r
  have : Module.Finite (RatFunc K) (↥(IntermediateField.adjoin K ({x} : Set F))) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) (↥(IntermediateField.adjoin K ({x} :
      Set F)))) e.surjective
  have : FiniteDimensional (RatFunc K) F := Module.Finite.trans (↥(IntermediateField.adjoin K ({x}
    : Set F))) F
  exact AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc K F
end
end AlgebraicCurves.Divisors.Proofs.HasPrincipalDivisors_of_transcendental
end ProofImplementation
