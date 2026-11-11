/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitIsoDegree
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.KummerPowerCoefficients
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Boundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Native H2 for an automorphism semilinear for a Frobenius power

The original degree invariance under scheme isomorphisms and the
original Kummer coefficient comparison give the factor q^m for an
actual automorphism whose base action is inverse Frobenius to the
m-th power. No m-th root of that automorphism is assumed. The same
calculation passes through the original finite groups, inverse limit,
and scalar extension and computes the original rank-one trace.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable (k K : Type) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  {F : Type} [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
  (m : ℕ) (e : M.C ≅ M.C)
  (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
    ((FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm ^ m).toRingHom))

include hℓ he

private theorem nativeFiniteDivisorClass_inverseArithmeticPower
    (n : ℕ) (a : Sheaf.H.{0} (etaleGenericUnitQuotient M.C) 0) :
    finiteLevelCohomologyPullback ℓ e.hom n 2
        (M.nativeFiniteDivisorClass ℓ hℓ n (M.genericUnitDivisorH0Equiv a)) =
      (Fintype.card k ^ m) • M.nativeFiniteDivisorClass ℓ hℓ n
        (M.genericUnitDivisorH0Equiv
          (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a)) := by
  apply (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).injective
  rw [finiteLevelKummerCohomologyEquiv_inverseArithmeticPower k K M.toBase ℓ hℓ
    m e.hom he, map_nsmul]
  simp only [nativeFiniteDivisorClass_genericUnitBoundary, AddEquiv.apply_symm_apply]
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnM : IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(M.C, ⊤)) :=
    etaleKummerExponentUnit_of_base M.toBase
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
  have hgeneric := etaleGenericUnitBoundary_zero_pullback e.hom a
  have hkummer := etaleKummerBoundary_one_pullback e.hom hn hnM
    (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a)
  have hboundary := congrArg
    (fun z : Sheaf.H.{0} (etaleMultiplicativeGroupSheaf M.C) 1 =>
      Sheaf.H.δ (etaleKummerComplex_shortExact M.C hn hnM) 1 2 rfl z) hgeneric
  exact congrArg
    (fun z : Sheaf.H.{0} (etaleRootsOfUnitySheaf M.C (ℓ ^ (n + 1))) 2 =>
      (Fintype.card k ^ m) • z) (hkummer.trans hboundary)

/-- The actual semilinear automorphism acts by q^m on the original
finite coefficient H2, via actual divisor classes and their degree. -/
theorem nativeFiniteLevelH2_inverseArithmeticPower (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ n 2) :
    finiteLevelCohomologyPullback ℓ e.hom n 2 a = (Fintype.card k ^ m) • a := by
  obtain ⟨D, rfl⟩ := M.nativeFiniteDivisorClass_surjective ℓ hℓ n a
  let b := M.genericUnitDivisorH0Equiv.symm D
  have hb : M.genericUnitDivisorH0Equiv b = D := M.genericUnitDivisorH0Equiv.apply_symm_apply D
  have ha : finiteLevelCohomologyPullback ℓ e.hom n 2 (M.nativeFiniteDivisorClass ℓ hℓ n D) =
      (Fintype.card k ^ m) • M.nativeFiniteDivisorClass ℓ hℓ n
        (M.genericUnitDivisorH0Equiv
          (etaleGenericUnitQuotientCohomologyPullback e.hom 0 b)) := by
    simpa only [hb] using nativeFiniteDivisorClass_inverseArithmeticPower k K M ℓ hℓ m e he n b
  apply (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).injective
  simp only [ha, map_nsmul, nativeFiniteLevelH2DegreeEquiv_divisor,
    M.genericUnitDivisorH0Equiv_degree_iso_pullback M e b, hb]

/-- The same actual q^m action is retained at every projection of
the original integral inverse limit. -/
theorem nativeEllAdicH2_inverseArithmeticPower_apply
    (a : ellAdicCohomology M.C ℓ 2) :
    ellAdicCohomologyPullback ℓ e.hom 2 a = (Fintype.card k ^ m) • a := by
  apply ellAdicCohomology_ext M.C ℓ 2
  intro n
  change finiteLevelCohomologyPullback ℓ e.hom n 2 (a.val n) =
    (Fintype.card k ^ m) • a.val n
  exact M.nativeFiniteLevelH2_inverseArithmeticPower k K ℓ hℓ m e he n (a.val n)

/-- The original rational scalar extension retains this actual
q^m action on every original cohomology class. -/
theorem nativeRationalEllAdicH2_inverseArithmeticPower_apply
    (a : rationalEllAdicCohomology ℓ M.C 2) :
    rationalEllAdicCohomologyPullback ℓ e.hom 2 a = (Fintype.card k ^ m) • a := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
      rw [rationalEllAdicCohomologyPullback_tmul,
        nativeEllAdicH2_inverseArithmeticPower_apply k K M ℓ hℓ m e he]
      exact map_nsmul (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (ellAdicCohomology M.C ℓ 2) q)
        (Fintype.card k ^ m) a
  | add a b ha hb =>
      have hmap := (rationalEllAdicCohomologyPullback ℓ e.hom 2).map_add a b
      have hsum := congrArg₂
        (fun x y : rationalEllAdicCohomology ℓ M.C 2 => x + y) ha hb
      exact hmap.trans (hsum.trans (smul_add (Fintype.card k ^ m) a b).symm)

/-- The original rational endomorphism is precisely scalar
multiplication by the actual cardinality power. -/
theorem nativeRationalEllAdicH2_inverseArithmeticPower :
    rationalEllAdicCohomologyPullback ℓ e.hom 2 =
      (Fintype.card k ^ m) •
        (1 : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)) := by
  apply LinearMap.ext
  intro a
  exact M.nativeRationalEllAdicH2_inverseArithmeticPower_apply k K ℓ hℓ m e he a

/-- Its original rank-one trace is q^m, even if the given component
automorphism does not have a Frobenius root on that component. -/
theorem trace_nativeRationalEllAdicH2_inverseArithmeticPower :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2)
        (rationalEllAdicCohomologyPullback ℓ e.hom 2) = (Fintype.card k : ℚ_[ℓ]) ^ m := by
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) :=
    M.nativeRationalEllAdicH2_finiteDimensional ℓ hℓ
  rw [nativeRationalEllAdicH2_inverseArithmeticPower k K M ℓ hℓ m e he,
    map_nsmul, LinearMap.trace_one, M.nativeRationalEllAdicH2_finrank ℓ hℓ,
    Nat.cast_one, nsmul_eq_mul, mul_one, Nat.cast_pow]

end AlgebraicCurve.CurveModel
