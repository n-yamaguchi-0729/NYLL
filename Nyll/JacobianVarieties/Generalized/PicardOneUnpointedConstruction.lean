/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneLocalTranslation
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.UnpointedConstruction
import Nyll.JacobianVarieties.Generalized.UnpointedEmptyConstruction
import Nyll.JacobianVarieties.Generalized.PointedAffineNeighborhood
import Nyll.JacobianVarieties.Generalized.PointedEmptyAffineNeighborhood
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint
import Nyll.AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Descent.FppfCoverRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatFiniteTypeGeometry
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ConnectedSmoothDimensionDescent
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusBaseChange

/-!
# Intrinsic Picard-one without a rational point

A closed point of the actual open complement gives a finite residue extension.
Its local tensor translation represents the restriction of the intrinsic
Picard-one sheaf on the actual pointed Picard-zero scheme. The canonical action
then descends this scheme and its universal class to the original field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The intrinsic degree-one sheaf has an actual scheme representative over the original field. -/
theorem exists_picardOneRepresentation :
    ∃ P : Over (Spec (CommRingCat.of K)),
      Nonempty ((modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy P) ∧
      SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) P.hom ∧
        QuasiCompact P.hom ∧ IsSeparated P.hom ∧ GeometricallyConnected P.hom := by
  let U := modulusComplement (modulusCurveMap D)
  let u : U.toScheme ⟶ Spec (CommRingCat.of K) := U.ι ≫ c
  have : Nonempty U := modulusComplement_nonempty c D
  obtain ⟨x, -, hfin⟩ := Scheme.exists_finite_pointResidueAlgebra u
  let a : Algebra K (U.toScheme.residueField x) := Scheme.pointResidueAlgebra u x
  have : Module.Finite K (U.toScheme.residueField x) := hfin
  let L := U.toScheme.residueField x
  let P : Over.mk (specMap K L) ⟶ Over.mk u :=
    Over.homMk (U.toScheme.fromSpecResidueField x) (Scheme.pointResidueAlgebra_specMap u x).symm
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L) :=
    ⟨pullback.lift (P.left ≫ U.ι) (𝟙 _)
      (((Category.assoc _ _ _).trans (Over.w P)).trans (Category.id_comp _).symm),
      pullback.lift_snd _ _ _⟩
  let F := (modulusPicardOneSheaf c (modulusCurveMap D)).obj
  obtain ⟨J, hJ, haff, hdimJ, hqcJ, hsepJ, hgcJ⟩ :
      ∃ J : Over (Spec (CommRingCat.of L)),
        Nonempty (((Over.map (specMap K L)).op ⋙ F).RepresentableBy J) ∧
        (∀ S : Finset J.left, ∃ V : J.left.Opens, IsAffineOpen V ∧ ∀ y ∈ S, y ∈ V) ∧
        SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) J.hom ∧
          QuasiCompact J.hom ∧ IsSeparated J.hom ∧ GeometricallyConnected J.hom := by
    cases d with
    | zero =>
      let DL := RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D
      let J := Pointed.zeroDegreeGroupScheme (baseChange K c L) ε DL
      let eZ : ((Over.map (specMap K L)).op ⋙
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj).RepresentableBy J.X :=
        (Unpointed.zeroDegreeScalarExtensionRepresentable c D L ε).ofIso
          (Functor.isoWhiskerLeft (Over.map (specMap K L)).op
            (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)))
      let eOne : ((Over.map (specMap K L)).op ⋙ F).RepresentableBy J.X :=
        eZ.ofIso (modulusPicardOneLocalTranslationSheafIso c (modulusCurveMap D)
          (specMap K L) P)
      have hgeom := Pointed.zeroDegreeGeometry (baseChange K c L) ε DL
      have : SmoothOfRelativeDimension (geometricGenus L (baseChange K c L)) J.X.hom := hgeom.1
      have : IsProper J.X.hom := hgeom.2.1
      have hdim : SmoothOfRelativeDimension (geometricGenus K c) J.X.hom := by
        rw [← geometricGenus_baseChange_of_finite_of_section K c L ε]
        exact hgeom.1
      exact ⟨J.X, ⟨eOne⟩,
        Pointed.zeroDegree_exists_isAffineOpen_forall_mem (baseChange K c L) ε DL,
        hdim, inferInstance, inferInstance, hgeom.2.2⟩
    | succ n =>
      let DL := RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D
      let J := Pointed.groupScheme (baseChange K c L) ε DL (Nat.zero_lt_succ n)
      let eZ : ((Over.map (specMap K L)).op ⋙
          (modulusPicardZeroSheaf c (modulusCurveMap D)).obj).RepresentableBy J.X :=
        (Unpointed.scalarExtensionRepresentable c D (Nat.zero_lt_succ n) L ε).ofIso
          (Functor.isoWhiskerLeft (Over.map (specMap K L)).op
            (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)))
      let eOne : ((Over.map (specMap K L)).op ⋙ F).RepresentableBy J.X :=
        eZ.ofIso (modulusPicardOneLocalTranslationSheafIso c (modulusCurveMap D)
          (specMap K L) P)
      have hgeom := Pointed.geometry (baseChange K c L) ε DL (Nat.zero_lt_succ n)
      have : SmoothOfRelativeDimension (geometricGenus L (baseChange K c L) + (n + 1) - 1)
          J.X.hom := hgeom.1
      have hdim : SmoothOfRelativeDimension (geometricGenus K c + (n + 1 - 1))
          J.X.hom := by
        rw [← geometricGenus_baseChange_of_finite_of_section K c L ε]
        simpa only [Nat.succ_sub_one, Nat.add_succ] using hgeom.1
      exact ⟨J.X, ⟨eOne⟩,
        Pointed.exists_isAffineOpen_forall_mem (baseChange K c L) ε DL (Nat.zero_lt_succ n),
        hdim, hgeom.2.2.1, hgeom.2.2.2.1, hgeom.2.2.2.2⟩
  let eJ : ((Over.map (specMap K L)).op ⋙ F).RepresentableBy (Over.mk J.hom) :=
    Classical.choice hJ
  let A : DescentAction (specMap K L) J.hom :=
    DescentAction.ofRepresentableBy (specMap K L) F J.hom eJ
  obtain ⟨X, f, e, he, hc⟩ :=
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
  have hsmJ : Smooth J.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) J.hom
  have hgeom :=
    smooth_isSeparated_quasiCompact_geometricallyConnected_of_faithfullyFlat_baseChange
      K L f J.hom hsmJ hsepJ hqcJ hgcJ e he
  have : Smooth f := hgeom.1
  have : GeometricallyConnected f := hgeom.2.2.2
  have : ConnectedSpace J.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton J.hom
  have hdim : SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) f :=
    smoothOfRelativeDimension_of_connected_scalarExtension K L f J.hom
      (Classical.choice (inferInstance : Nonempty J.left))
      (geometricGenus K c + (d - 1)) e he
  exact ⟨Over.mk f, ⟨DescentAction.globalRepresentation (specMap K L) F J.hom eJ f e he
    (DescentAction.isSheafFor_coverT_of_isSheaf (specMap K L) F
      (modulusPicardOneSheaf c (modulusCurveMap D)).property) hc⟩,
    hdim, hgeom.2.2.1, hgeom.2.1, hgeom.2.2.2⟩

/-- The chosen actual representative of intrinsic Picard-one over the original field. -/
def picardOne : Over (Spec (CommRingCat.of K)) :=
  (exists_picardOneRepresentation c D).choose

/-- The universal classifying equivalence on that same descended scheme. -/
def picardOneRepresentable :
    (modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy (picardOne c D) :=
  Classical.choice (exists_picardOneRepresentation c D).choose_spec.1

/-- The intrinsic degree-one representative has the same relative dimension as Picard-zero. -/
theorem picardOne_dimension :
    SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) (picardOne c D).hom :=
  (exists_picardOneRepresentation c D).choose_spec.2.1

/-- Smooth finite-type separated geometry and geometric connectedness on the same carrier. -/
theorem picardOne_geometry :
    Smooth (picardOne c D).hom ∧ LocallyOfFiniteType (picardOne c D).hom ∧
      QuasiCompact (picardOne c D).hom ∧ IsSeparated (picardOne c D).hom ∧
        GeometricallyConnected (picardOne c D).hom := by
  have h := (exists_picardOneRepresentation c D).choose_spec.2
  have : SmoothOfRelativeDimension (geometricGenus K c + (d - 1))
      (picardOne c D).hom := h.1
  have hsm : Smooth (picardOne c D).hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) _
  exact ⟨hsm, inferInstance, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The intrinsic degree-one scheme is an actual fppf cover of the ground field. -/
theorem picardOne_fppf :
    Flat (picardOne c D).hom ∧ LocallyOfFinitePresentation (picardOne c D).hom ∧
      Surjective (picardOne c D).hom := by
  have h := picardOne_geometry c D
  have : Smooth (picardOne c D).hom := h.1
  have : GeometricallyConnected (picardOne c D).hom := h.2.2.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.GeneralizedJacobian
