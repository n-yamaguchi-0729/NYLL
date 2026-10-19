/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.TameTestFactorization
import Nyll.AlgebraicCurves.Places.Orders.SeparableAdjoinOrdNeZeroCastNatAbsNeZero
import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteDimensionalAdjoinSimple

/-! # Reducing modulus tests to finite-separable reciprocal parameters

One positive contact order invertible in the constant field makes the
reciprocal of `g - 1` a separating transcendental parameter. Essential finite
type supplies the actual finite extension. Exact-contact factorization then
reduces the full principal-divisor modulus test to these parameters.

The vanishing of principal evaluation for the finite-separable tame tests
remains an explicit hypothesis. This is a reduction criterion, not a proof
of general group-valued reciprocity or general modulus existence.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

private theorem exists_large_nonzero_cast (N : ℕ) :
    ∃ e : ℕ, N < e ∧ (e : K) ≠ 0 := by
  by_cases h : ((N + 1 : ℕ) : K) ≠ 0
  · exact ⟨N + 1, Nat.lt_succ_self N, h⟩
  have hzero : ((N + 1 : ℕ) : K) = 0 := not_ne_iff.mp h
  refine ⟨N + 2, by omega, ?_⟩
  have heq : ((N + 2 : ℕ) : K) = 1 := by
    calc
      _ = ((N + 1 : ℕ) : K) + 1 := by
        rw [show N + 2 = (N + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
      _ = 1 := by rw [hzero, zero_add]
  rw [heq]
  exact one_ne_zero

/-- A single positive tame contact order can be chosen above every bound
on a fixed finite boundary, in every characteristic. -/
theorem exists_common_tame_order (S : Finset (Place K F)) (bound : Place K F → ℕ) :
    ∃ e : ℕ, 0 < e ∧ (e : K) ≠ 0 ∧ ∀ v ∈ S, bound v < e := by
  obtain ⟨e, he, heK⟩ := exists_large_nonzero_cast (K := K) (S.sup bound)
  exact ⟨e, lt_of_le_of_lt (Nat.zero_le _) he, heK,
    fun v hv => lt_of_le_of_lt (Finset.le_sup hv) he⟩

/-- One boundary point of positive tame contact supplies the actual
finite-separable reciprocal parameter over a perfect constant field. -/
theorem tame_reciprocal_parameter
    [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v : Place K F) (g : Fˣ) (e : ℕ) (hepos : 0 < e) (he : (e : K) ≠ 0)
    (hg : v.ord ((g : F) - 1) = (e : ℤ)) :
    Transcendental K (((g : F) - 1)⁻¹) ∧
      FiniteDimensional (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F := by
  let z : F := ((g : F) - 1)⁻¹
  have hzord : v.ord z = -(e : ℤ) := by rw [ord_inv, hg]
  have hzord0 : v.ord z ≠ 0 := by rw [hzord]; omega
  have hztr : Transcendental K z := v.transcendental_of_ord_ne_zero hzord0
  have hfinite : FiniteDimensional (IntermediateField.adjoin K {z}) F :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hztr
  have htame : (((v.ord z).natAbs : ℕ) : K) ≠ 0 := by
    rw [hzord, Int.natAbs_neg, Int.natAbs_natCast]
    exact he
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K {z}) F :=
    Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero z v hzord0 htame
  exact ⟨hztr, hfinite, hsep⟩

end Place

namespace Modulus

variable {A : Type*} [AddCommGroup A]

/-- For nonempty boundary, it suffices to establish principal-evaluation
vanishing for exact tame contact tests whose reciprocal parameters give
actual finite-separable presentations. The original test functions may be
inseparable: exact-contact factorization supplies the separating factors. -/
theorem hasModulus_of_finiteSeparable_reciprocal_tests
    [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (D : Modulus K F) (hD : D.support.Nonempty)
    (a : Place K F → A) (n : Place K F → ℕ)
    (hn : ∀ v ∈ D.support, 0 < n v)
    (hnD : ∀ v ∈ D.support, n v < D v)
    (hntame : ∀ v ∈ D.support, (n v : K) ≠ 0)
    (htest : ∀ g : Fˣ,
      (∀ v ∈ D.support, v.ord ((g : F) - 1) = (n v : ℤ)) →
      Transcendental K (((g : F) - 1)⁻¹) →
      FiniteDimensional (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F →
      Algebra.IsSeparable (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F →
      principalEvaluation a (Additive.ofMul g) = 0) : D.HasModulus a := by
  obtain ⟨v, hv⟩ := hD
  apply hasModulus_of_exact_contact_orders D a n hn hnD
  intro g hg
  obtain ⟨htr, hfinite, hsep⟩ := v.tame_reciprocal_parameter g (n v)
    (hn v hv) (hntame v hv) (hg v hv)
  exact htest g hg htr hfinite hsep

end Modulus

end AlgebraicCurve
