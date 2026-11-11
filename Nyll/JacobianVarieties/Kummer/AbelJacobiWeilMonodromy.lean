/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.ActualGenericWeilComparison
public import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints
public import Nyll.AlgebraicCurves.Models.ConstantExtension.ExtensionCoordinates
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationAlgebraicPoints
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Abel--Jacobi multiplication monodromy and the curve Kummer character

At an invertible index, the actual multiplication fibre determines the Weil
character of the original curve. We construct the divisor-class identification,
its torsion restriction, and all constant-extension coordinates over the
algebraic closure of the curve's function field. The result works in positive
characteristic without requiring that algebraic closure to be separable.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve AlgebraicCurve.CurveModel NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The actual Abel--Jacobi division monodromy has the original Kummer
character under the divisorial Weil pairing. The same constructed Picard point
equivalence and its actual torsion restriction work for every torsion class. -/
theorem exists_abelJacobi_weil_kummer_monodromy
    {K F₀ : Type} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀) [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (w : DivisorialWeilPairingData K F₀ (n : ℕ)) :
    let _ : Algebra K M₀.C.functionField := M₀.functionFieldAlgebra
    let Ω := AlgebraicClosure M₀.C.functionField
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
    let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
    ∃ e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K,
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = v.1 ≫ aj.1) ∧
      ∃ τn : Pic0.torsion K F₀ (n : ℕ) ≃+
          ProCGroups.torsionLevel (G.AlgPoints hc K) n,
        (∀ a, (τn a).1 = e₀ a.1) ∧
        (∀ a, (G.torsionLevelEquivSchemeKerPoints hc n (τn a)).1 ≫
          pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e₀ a.1)).1) ∧
        ∀ (a : Pic0.torsion K F₀ (n : ℕ))
          (τ : FiniteEtale.fiber (η ≫ q ≫ aj.1) ≅
            FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
          (_ : (FiniteEtale.fiber (η ≫ q ≫ aj.1)).obj
            (RelativeGroupLaw.UnitMultiplication.cover G hc ⟨n, hn⟩)),
          ∃ u : Pic0.kummerUnits K F₀ n,
            Multiplicative.toAdd (Pic0.kummerClass n u) = a ∧
            ∀ σ : Ω ≃ₐ[M₀.C.functionField] Ω,
              w.pair a (τn.symm
                (RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩
                  (continuousConjAut τ
                    (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
                      (toAut (FiniteEtale.fiber η)
                        (Ω ≃ₐ[M₀.C.functionField] Ω) σ))))) =
                ((M₀.kummerMonodromyCharacter n u hn (η ≫ q)
                  (FiniteEtale.fundamentalGroupHom q η
                    (toAut (FiniteEtale.fiber η)
                      (Ω ≃ₐ[M₀.C.functionField] Ω) σ)) : Kˣ) : K) := by
  intro hbase Ω G hc η q
  obtain ⟨e₀, hpoint, htorsion⟩ :=
    JacobianVarieties.Picard.exists_pic0_addEquiv_algPoints_of_abelJacobi
      M₀ ε D hD aj hclass
  obtain ⟨τn, hτn, hker⟩ := htorsion n
  refine ⟨e₀, hpoint, τn, hτn, hker, ?_⟩
  intro a τ z
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  apply M₀.with_constantExtension_coordinates Ω
  intro F hF hΩF hcurve hF₀F hKF htower₀ htowerΩ hfg hfg' hgen M eC heC hsq
  exact exists_actual_abelJacobi_generic_weil_kummer M₀ rfl
    hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn w a e₀ τn hτn hpoint τ z

end JacobianVarieties.Kummer
