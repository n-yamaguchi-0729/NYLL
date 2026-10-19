/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedEmptyAffineNeighborhood
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint
import Nyll.AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Descent.FppfCoverRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatProperties
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ConnectedSmoothDimensionDescent
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusBaseChange
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-!
# The degree-zero modulus over a curve without a rational point

The actual empty-modulus Picard-zero sheaf descends from its pointed ordinary
Picard representation over a finite residue extension. This proves its global
representation and properness without assuming that the curve has a basepoint.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))

/-- The degree-zero modulus is actually empty, so its group sheaf is ordinary Picard-zero. -/
def zeroDegreeSheafIso :
    modulusPicardZeroGroupSheaf c (modulusCurveMap D) ≅ ordinaryRelativePicardZeroGroupSheaf c :=
  Pointed.zeroDegreeSheafIso c D

/-- The actual ordinary carrier after scalar extension represents the restriction
of the original empty-modulus group sheaf. -/
def zeroDegreeScalarExtensionRepresentable (L : Type u) [Field L] [Algebra K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L)) :
    ((Over.map (specMap K L)).op ⋙
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      (Pointed.zeroDegreeGroupScheme (baseChange K c L) ε
        (RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D)).X :=
  (Pointed.zeroDegreeGroupRepresentable (baseChange K c L) ε
    (RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D)).ofIso
      (Functor.isoWhiskerRight
        ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
          CommGrpCat.{u + 1}).mapIso
            (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L))
        (forget CommGrpCat.{u + 1}))

/-- All data in this completed degree-zero representation are supplied by the
finite faithfully flat construction below. -/
structure ZeroDegreePresentation where
  /-- The descended ordinary Picard carrier over the original field. -/
  carrier : Over (Spec (CommRingCat.of K))
  /-- Its universal class in the actual empty-modulus zero sheaf. -/
  representation :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy carrier
  /-- The dimension is the geometric genus, including for genus zero. -/
  dimension : SmoothOfRelativeDimension (geometricGenus K c) carrier.hom
  /-- The ordinary carrier is proper. -/
  proper : IsProper carrier.hom
  /-- The same carrier is geometrically connected. -/
  geometricallyConnected : GeometricallyConnected carrier.hom

/-- Degree-zero modulus Picard-zero has a smooth proper genus-dimensional
representation over the original arbitrary field. -/
theorem nonempty_zeroDegreePresentation : Nonempty (ZeroDegreePresentation c D) := by
  obtain ⟨x₀, -⟩ := c.surjective (default : Spec (CommRingCat.of K))
  have : Nonempty C := ⟨x₀⟩
  obtain ⟨x, -, hfin⟩ := Scheme.exists_finite_pointResidueAlgebra c
  let a : Algebra K (C.residueField x) := Scheme.pointResidueAlgebra c x
  have : Module.Finite K (C.residueField x) := hfin
  let L := C.residueField x
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L) :=
    Scheme.pointResidueSection c x
  let DL := RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D
  let J := Pointed.zeroDegreeGroupScheme (baseChange K c L) ε DL
  let F := (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙ forget CommGrpCat.{u + 1}
  let eJ : ((Over.map (specMap K L)).op ⋙ F).RepresentableBy (Over.mk J.X.hom) :=
    zeroDegreeScalarExtensionRepresentable c D L ε
  let A : DescentAction (specMap K L) J.X.hom :=
    DescentAction.ofRepresentableBy (specMap K L) F J.X.hom eJ
  have haff : ∀ S : Finset J.X.left,
      ∃ U : J.X.left.Opens, IsAffineOpen U ∧ ∀ y ∈ S, y ∈ U :=
    Pointed.zeroDegree_exists_isAffineOpen_forall_mem (baseChange K c L) ε DL
  obtain ⟨P, p, e, he, hc⟩ :=
    DescentAction.effective_of_finite_fieldExtension K L A haff
  have : Algebra.FinitePresentation K L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Flat (specMap K L) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (specMap K L) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : LocallyOfFinitePresentation (specMap K L) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hF : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) F :=
    (Presheaf.isSheaf_of_iso_iff
      (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D))).mpr
        (modulusPicardZeroSheaf c (modulusCurveMap D)).property
  let eP : F.RepresentableBy (Over.mk p) :=
    DescentAction.globalRepresentation (specMap K L) F J.X.hom eJ p e he
      (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K L) F hF) hc
  have hlocal := Pointed.zeroDegreeGeometry (baseChange K c L) ε DL
  have : SmoothOfRelativeDimension (geometricGenus L (baseChange K c L))
      J.X.hom := hlocal.1
  have hsm : Smooth J.X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus L (baseChange K c L)) J.X.hom
  have hpr : IsProper J.X.hom := hlocal.2.1
  have hgc : GeometricallyConnected J.X.hom := hlocal.2.2
  obtain ⟨hsmP, hprP, hgcP⟩ :=
    smooth_isProper_geometricallyConnected_of_faithfullyFlat_baseChange
      K L p J.X.hom hsm hpr hgc e he
  have : Smooth p := hsmP
  have : GeometricallyConnected p := hgcP
  have : ConnectedSpace J.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton J.X.hom
  have hdim : SmoothOfRelativeDimension (geometricGenus K c) J.X.hom := by
    rw [← geometricGenus_baseChange_of_finite_of_section K c L ε]
    exact hlocal.1
  have hdimP : SmoothOfRelativeDimension (geometricGenus K c) p :=
    smoothOfRelativeDimension_of_connected_scalarExtension K L p J.X.hom
      (Classical.choice (inferInstance : Nonempty J.X.left)) (geometricGenus K c) e he
  exact ⟨⟨Over.mk p, eP, hdimP, hprP, hgcP⟩⟩

/-- One fixed complete representation of the degree-zero modulus sheaf. -/
def zeroDegreePresentation : ZeroDegreePresentation c D :=
  Classical.choice (nonempty_zeroDegreePresentation c D)

/-- The tensor-product group on the same descended ordinary Picard carrier. -/
def zeroDegreeGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (zeroDegreePresentation c D).representation

/-- The constructed group represents the actual degree-zero modulus group sheaf. -/
def zeroDegreeGroupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (zeroDegreeGroupScheme c D).X :=
  (zeroDegreePresentation c D).representation

/-- Empty-modulus comparison gives the ordinary Picard-zero group sheaf on this
same carrier, without any rational section over the base field. -/
def zeroDegreeOrdinaryGroupRepresentable :
    ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (zeroDegreeGroupScheme c D).X :=
  (zeroDegreeGroupRepresentable c D).ofIso
    (Functor.isoWhiskerRight
      ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        CommGrpCat.{u + 1}).mapIso (Pointed.zeroDegreeSheafIso c D))
      (forget CommGrpCat.{u + 1}))

/-- In degree zero the descended group is proper and has genus dimension. -/
theorem zeroDegreeGeometry :
    SmoothOfRelativeDimension (geometricGenus K c) (zeroDegreeGroupScheme c D).X.hom ∧
      IsProper (zeroDegreeGroupScheme c D).X.hom ∧
      GeometricallyConnected (zeroDegreeGroupScheme c D).X.hom :=
  ⟨(zeroDegreePresentation c D).dimension,
    (zeroDegreePresentation c D).proper, (zeroDegreePresentation c D).geometricallyConnected⟩

/-- Any available rational section gives the same represented group scheme. -/
def zeroDegreePointedComparison
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    zeroDegreeGroupScheme c D ≅ Pointed.zeroDegreeGroupScheme c ε D :=
  SchemeTheory.RepresentedGroups.iso
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (zeroDegreeGroupRepresentable c D) (Pointed.zeroDegreeGroupRepresentable c ε D) (Iso.refl _)

end AlgebraicGeometry.GeneralizedJacobian.Unpointed
