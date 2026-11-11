/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitIsoDegree
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Degree of native H¹(Gm) under an actual scheme isomorphism

Degree on the original Picard group and the proved native H¹ comparison
define the original cohomological degree. The generic-unit boundary
retains the original divisor degree. Its actual surjectivity and actual
pullback naturality then show that every scheme isomorphism preserves
native H¹ degree, including semilinear constant-field isomorphisms.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- Degree on original native H¹(Gm), through the proved comparison
with the original Picard group. Principal-divisor existence is derived
from the actual smooth integral curve model. -/
def multiplicativeGroupH1Degree :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 →+ ℤ := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hPrincipal : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  exact (H1Gm.degree K F).comp M.multiplicativeGroupH1PicardEquiv.toAddMonoidHom

/-- The original generic-unit boundary has the degree of its original
divisor, under the actual native H¹ degree map. -/
theorem multiplicativeGroupH1Degree_connecting
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.multiplicativeGroupH1Degree
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a) =
      Divisor.degree (M.genericUnitDivisorH0Equiv a) := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hPrincipal : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  exact congrArg (H1Gm.degree K F) (M.multiplicativeGroupH1PicardEquiv_connecting a)

/-- Every actual scheme isomorphism of the original curve models
preserves the native H¹(Gm) degree; no base-linearity condition is required. -/
theorem multiplicativeGroupH1Degree_iso_pullback
    {L : Type w} [Field L] [Algebra K L] (N : CurveModel K L)
    (e : N.C ≅ M.C) (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) :
    N.multiplicativeGroupH1Degree
        (etaleMultiplicativeGroupCohomologyPullback e.hom 1 a) =
      M.multiplicativeGroupH1Degree a := by
  obtain ⟨b, hb⟩ := Sheaf.H.longSequence_exact₁
    (etaleGenericUnitShortComplex_shortExact M.C) a
    (genericPoint_units_H1_eq_zero M.C _) rfl
  have hbNative :
      (show Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 from
        Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl b) = a := hb
  have hnatural := etaleGenericUnitBoundary_zero_pullback e.hom b
  have hdegree := congrArg N.multiplicativeGroupH1Degree hnatural
  have htarget := N.multiplicativeGroupH1Degree_connecting
    (etaleGenericUnitQuotientCohomologyPullback e.hom 0 b)
  have hdivisor := M.genericUnitDivisorH0Equiv_degree_iso_pullback N e b
  have hsource := M.multiplicativeGroupH1Degree_connecting b
  have hresult := hdegree.trans (htarget.trans (hdivisor.trans hsource.symm))
  exact (congrArg
    (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 =>
      N.multiplicativeGroupH1Degree
        (etaleMultiplicativeGroupCohomologyPullback e.hom 1 z)) hbNative).symm.trans
    (hresult.trans (congrArg M.multiplicativeGroupH1Degree hbNative))

end AlgebraicCurve.CurveModel
