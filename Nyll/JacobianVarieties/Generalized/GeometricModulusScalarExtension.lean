/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusRegularMap
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapRestriction
import Nyll.JacobianVarieties.Generalized.ModulusEmptyRegularMap
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapTranslation
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme

/-! # Scalar extension of the geometric full-modulus factor

For positive degree and an actual point outside the modulus, the group
factor over the original field supplies the extended modulus condition.
Its comparison with the extended group factor follows from Abel uniqueness.
No algebraic closedness of either ground field is required.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) G.X.hom)
  (hmod : geometricRegularMapHasModulus c D G (Over.homMk q.1 q.2))

include ε hmod in
/-- The positive geometric full modulus survives an arbitrary field extension.
The required group factor is the one already constructed over the ground field. -/
theorem geometricRegularMapHasModulus_scalarExtension
    (hd : 0 < d) (L : Type u) [Field L] [Algebra K L] :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
    let qL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶ G_L.X :=
      modulusGroupMapScalarExtension c D L G (Over.homMk q.1 q.2)
    geometricRegularMapHasModulus cL DL G_L qL := by
  intro cL DL G_L qL
  let εL := modulusBasepointScalarExtension c D L (Over.homMk ε.1 ε.2)
  let φ := geometricGroupHomFromModulus c D ε G q hmod hd
  let φL : groupScheme cL DL ⟶ G_L :=
    (groupActualScalarExtensionIso c D L).inv ≫
      (GroupSchemes.baseChange (specMap K L)).map φ
  let bL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
    Over.homMk _ (Category.comp_id _)
  have hfac : modulusAbelMap cL DL εL ≫ φL.hom.hom.hom =
      qL / (bL ≫ εL ≫ qL) := by
    have h := modulusGroupMapScalarExtension_abel_comp c D L G φ
      (Over.homMk ε.1 ε.2)
    rw [geometricGroupHomFromModulus_abel_translation c D ε G q hmod hd,
      modulusGroupMapScalarExtension_normalization] at h
    exact h
  have hn : geometricRegularMapHasModulus cL DL G_L (qL / (bL ≫ εL ≫ qL)) := by
    rw [← hfac]
    exact geometricRegularMapHasModulus_comp cL DL (groupScheme cL DL) G_L
      (modulusAbelMap cL DL εL) (geometricRegularMapHasModulus_abel cL DL εL) φL
  exact (geometricRegularMapHasModulus_translate_iff cL DL G_L qL (εL ≫ qL)).mpr hn

/-- The actual positive-degree group factor commutes with the canonical
generalized-Jacobian scalar-extension isomorphism over arbitrary fields. -/
theorem geometricGroupHomFromModulus_scalarExtension
    (hd : 0 < d) (L : Type u) [Field L] [Algebra K L] :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let εL := modulusBasepointScalarExtension c D L (Over.homMk ε.1 ε.2)
    let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : IsSeparated G_L.X.hom := by
      change IsSeparated (CategoryTheory.Limits.pullback.snd G.X.hom (specMap K L))
      infer_instance
    let qL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶ G_L.X :=
      modulusGroupMapScalarExtension c D L G (Over.homMk q.1 q.2)
    let hmodL := geometricRegularMapHasModulus_scalarExtension c D ε G q hmod hd L
    geometricGroupHomFromModulus cL DL ⟨εL.left, Over.w εL⟩ G_L
        ⟨qL.left, Over.w qL⟩ hmodL hd =
      (groupActualScalarExtensionIso c D L).inv ≫
        (GroupSchemes.baseChange (specMap K L)).map
          (geometricGroupHomFromModulus c D ε G q hmod hd) := by
  intro cL DL εL G_L separatedGL qL hmodL
  let φ := geometricGroupHomFromModulus c D ε G q hmod hd
  have hfac := modulusGroupMapScalarExtension_abel_comp c D L G φ
    (Over.homMk ε.1 ε.2)
  rw [geometricGroupHomFromModulus_abel_translation c D ε G q hmod hd,
    modulusGroupMapScalarExtension_normalization] at hfac
  apply modulusAbel_groupHom_ext cL DL εL G_L
  have hL := geometricGroupHomFromModulus_abel_translation_over cL DL G_L εL qL hmodL hd
  exact hL.trans hfac.symm

end AlgebraicGeometry.GeneralizedJacobian

open AlgebraicGeometry AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Over an algebraically closed ground field, the geometric condition is
equivalent to the original principal-divisor condition in every degree.
For empty modulus a rational degree-one enlargement supplies the factor,
and density extends its Abel identity to the original curve. -/
theorem geometricRegularMapHasModulus_iff
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
    [GeometricallyIntegral M.toBase]
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom) :
    geometricRegularMapHasModulus M.toBase D G (Over.homMk q.1 q.2) ↔
      M.regularMapHasModulus D G q := by
  refine ⟨?_, fun h => M.regularMapHasModulus_geometric D G q h⟩
  intro hmod
  obtain ⟨ε⟩ := modulusComplement_point M.toBase D
  let ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) :=
    ⟨ε.left, Over.w ε⟩
  let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  have hfactor : ∃ φ : groupScheme M.toBase D ⟶ G,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
        Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨E, hED, ⟨εE⟩⟩ := exists_degreeOneModulus_with_point M.toBase D
      let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve M.toBase E D hED)
      let εData : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
          ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) :=
        ⟨εE.left, Over.w εE⟩
      let qE : SchemeHomOver
          ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) G.X.hom :=
        ⟨(r ≫ Over.homMk q.1 q.2).left, Over.w (r ≫ Over.homMk q.1 q.2)⟩
      have hmodE : geometricRegularMapHasModulus M.toBase E G
          (Over.homMk qE.1 qE.2) :=
        geometricRegularMapHasModulus_restrict M.toBase D E hED G
          (Over.homMk q.1 q.2) hmod
      let φE := geometricGroupHomFromModulus M.toBase E εData G qE hmodE Nat.zero_lt_one
      exact (M.existsUnique_groupHom_zeroModulus_of_degreeOneFactor D ε G q E hED εE φE
        (geometricGroupHomFromModulus_abel_translation M.toBase E εData G qE hmodE
          Nat.zero_lt_one)).exists
    · exact ⟨geometricGroupHomFromModulus M.toBase D ε₀ G q hmod hd,
        geometricGroupHomFromModulus_abel_translation M.toBase D ε₀ G q hmod hd⟩
  obtain ⟨φ, hfac⟩ := hfactor
  let a : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
      (groupScheme M.toBase D).X.hom :=
    ⟨(modulusAbelMap M.toBase D ε).left, Over.w (modulusAbelMap M.toBase D ε)⟩
  have h := M.regularMapHasModulus_comp D (groupScheme M.toBase D) a
    (M.regularMapHasModulus_abel D ε) G φ
  change M.regularMapHasModulus D G
    ((commGroupPointEquiv G
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
        (modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom)) at h
  rw [hfac] at h
  exact (M.regularMapHasModulus_translate_iff D G q (ε ≫ Over.homMk q.1 q.2)).mpr h

end AlgebraicCurve.CurveModel
