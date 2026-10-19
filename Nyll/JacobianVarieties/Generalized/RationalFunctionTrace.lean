/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTrace
import Nyll.JacobianVarieties.Generalized.FiniteCurveTraceDomain
import Nyll.AlgebraicCurves.FunctionFields.Rational.FunctionFieldRatFuncAlgHomApplyXEq
import Nyll.AlgebraicCurves.FunctionFields.Rational.FunctionFieldFiniteRatFuncAlgHom
import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.AlgebraicCurves.Models.FunctionFields.FiniteFlatHomAlgHom
import Nyll.AlgebraicCurves.Models.Rational.CurveModelRatFunc
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralAlgClosed

/-! # A regular trace constructed from a nonconstant rational function

A nonconstant function embeds the rational-function field in the given
curve function field. Finiteness is derived from the curve model, using
one separating rational presentation. The resulting finite flat curve map
retains its actual function-field comparison. Its graph family constructs
a regular trace on a nonempty dense open of the rational curve model.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open AlgebraicCurves.RelativeDivisors.Proofs

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

include M in
/-- The finite extension along a rational coordinate is derived from the
actual smooth curve model, independently of any chosen rational presentation. -/
theorem finiteAlong_ratFunc_of_curveModel (φ : RatFunc K →ₐ[K] F) :
    FiniteAlong K φ ∧ φ.toRingHom.IsIntegral := by
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨rationalAlgebra, rationalTower, rationalFinite, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := K) (F := F)
  have hfinite : FiniteAlong K φ := FunctionField.finite_of_ratFuncAlgHom φ
  refine ⟨hfinite, ?_⟩
  let _ : Algebra (RatFunc K) F := algebraAlong φ
  have : Module.Finite (RatFunc K) F := hfinite
  change (algebraMap (RatFunc K) F).IsIntegral
  exact algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite (RatFunc K) F)

/-- A nonconstant rational function constructs an actual finite flat map
to a rational curve model, with the prescribed generic-point map. -/
theorem exists_finiteFlatMap_of_nonconstant (g : F)
    (hg : g ∉ Set.range (algebraMap K F)) :
    ∃ (P : CurveModel K (RatFunc K)) (φ : RatFunc K →ₐ[K] F),
      φ RatFunc.X = g ∧ φ.toRingHom.IsIntegral ∧ FiniteAlong K φ ∧
      ∃ π : M.C ⟶ P.C,
        π ≫ P.toBase = M.toBase ∧
        IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
        (∀ y : P.C, π.finrank y = finrankAlong K φ) ∧
        M.C.fromSpecStalk (genericPoint M.C) ≫ π =
          Spec.map (CommRingCat.ofHom
            (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
              P.C.fromSpecStalk (genericPoint P.C) := by
  have : Fact ((RatFunc.X : RatFunc K) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
  obtain ⟨P, _, _⟩ := CurveModel.exists_curveModel_ratFunc K
  obtain ⟨φ, hφX⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hg
  obtain ⟨hfinite, hintegral⟩ := finiteAlong_ratFunc_of_curveModel M φ
  obtain ⟨π, hπ, hfin, hflat, hlfp, hrank, hgeneric, _, _⟩ :=
    P.exists_finite_flat_hom_of_algHom M φ hintegral hfinite
  exact ⟨P, φ, hφX, hintegral, hfinite, π, hπ, hfin, hflat, hlfp, hrank, hgeneric⟩

/-- A rational group-valued map and a nonconstant rational function supply
the finite map, its nonempty dense trace domain, and the actual regular
trace with full Cartier fibre evaluation. None of these data is assumed. -/
theorem exists_rationalFunctionTrace (g : F)
    (hg : g ∉ Set.range (algebraMap K F)) (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) :
    ∃ (P : CurveModel K (RatFunc K)) (φ : RatFunc K →ₐ[K] F)
      (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
      (_ : IsFinite π) (_ : Flat π) (_ : LocallyOfFinitePresentation π)
      (hn : ∀ y : P.C, π.finrank y = finrankAlong K φ),
      φ RatFunc.X = g ∧ φ.toRingHom.IsIntegral ∧ FiniteAlong K φ ∧
      M.C.fromSpecStalk (genericPoint M.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
            P.C.fromSpecStalk (genericPoint P.C) ∧
      let V := finiteMapTraceLocus M.toBase P.toBase π hπ (finrankAlong K φ) hn U
      let A := finiteMapTraceFamily M.toBase P.toBase π hπ (finrankAlong K φ) hn U
      let hA := finiteMapTraceFamily_supported M.toBase P.toBase π hπ (finrankAlong K φ) hn U
      (V : Set P.C).Nonempty ∧ Dense (V : Set P.C) ∧ ((V : Set P.C)ᶜ).Finite ∧
      ∃ τ : SchemeHomOver (V.ι ≫ P.toBase) G.X.hom,
        ∀ {L : Type u} [Field L] [IsAlgClosed L] (a : Spec (CommRingCat.of L) ⟶ V),
          ∃ xs : Fin (finrankAlong K φ) →
            SchemeHomOver (a ≫ (V.ι ≫ P.toBase)) (U.ι ≫ M.toBase),
            ((A.pullbackAlong a rfl).restrictToOpen M.toBase U (hA.pullbackAlong a rfl)).I =
              prodKerGraph (U.ι ≫ M.toBase) (fun i => (xs i).1) (fun i => (xs i).2) ∧
            GoodReductionJacobian.schemeHomOverComp a rfl τ =
              (commGroupRelativeLaw G).sumList (a ≫ (V.ι ≫ P.toBase))
                (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  obtain ⟨P, φ, hφX, hintegral, hfinite, π, hπ, hfin, hflat, hlfp, hn, hgeneric⟩ :=
    exists_finiteFlatMap_of_nonconstant M g hg
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  have : GeometricallyIntegral P.toBase := geometricallyIntegral_of_isAlgClosed P.toBase
  refine ⟨P, φ, π, hπ, hfin, hflat, hlfp, hn, hφX, hintegral, hfinite, hgeneric, ?_⟩
  refine ⟨finiteMapTraceLocus_nonempty M.toBase P.toBase π hπ (finrankAlong K φ) hn U hU,
    finiteMapTraceLocus_dense M.toBase P.toBase π hπ (finrankAlong K φ) hn U hU,
    finite_finiteMapTraceLocus_compl M.toBase P.toBase π hπ (finrankAlong K φ) hn U hU, ?_⟩
  exact exists_finiteCurveTrace M.toBase P.toBase π hπ (finrankAlong K φ) hn U G q hU

end AlgebraicGeometry.GeneralizedJacobian
