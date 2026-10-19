/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedAffineNeighborhood
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint
import Nyll.AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Descent.FppfCoverRepresentation
import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatFiniteTypeGeometry
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ConnectedSmoothDimensionDescent
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusBaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups

/-!
# The positive-modulus generalized Jacobian over an arbitrary field

An actual closed point supplies a finite residue extension and a section there.
The constructed Poincaré frame scheme represents the restriction of the actual
modulus Picard-zero fppf sheaf. Its canonical descent action is effective because
the frame scheme has affine neighborhoods of finite sets. Fppf matching then
descends the universal class and its complete representation to the base field.

No rational point over the ground field, separability, representation, or
surjectivity is supplied as an additional assumption.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- The actual scalar-extended frame scheme represents the restriction of the
original group sheaf, including the whole scalar-extended modulus. -/
def scalarExtensionRepresentable (L : Type u) [Field L] [Algebra K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L)) :
    ((Over.map (specMap K L)).op ⋙
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
        forget CommGrpCat.{u + 1}).RepresentableBy
      (Pointed.groupScheme (baseChange K c L) ε
        (RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D) hd).X :=
  (Pointed.groupRepresentable (baseChange K c L) ε
    (RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D) hd).ofIso
      (Functor.isoWhiskerRight
        ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
          CommGrpCat.{u + 1}).mapIso
            (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L))
        (forget CommGrpCat.{u + 1}))

/-- The canonical action is induced by the same actual fppf group sheaf over the
original field, rather than by a separately postulated descent datum. -/
def scalarExtensionDescentAction (L : Type u) [Field L] [Algebra K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L)) :
    DescentAction (specMap K L)
      (Pointed.groupScheme (baseChange K c L) ε
        (RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D) hd).X.hom :=
  DescentAction.ofRepresentableBy (specMap K L)
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙ forget CommGrpCat)
    _ (scalarExtensionRepresentable c D hd L ε)

/-- A completed representation together with the geometry proved by descent.
The existence theorem below constructs every field of this record. -/
structure Presentation where
  /-- The descended scheme over the original field. -/
  carrier : Over (Spec (CommRingCat.of K))
  /-- The actual universal-class equivalence with the modulus zero group sheaf. -/
  representation :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy carrier
  /-- Its smooth dimension is determined by the actual finite-extension scheme. -/
  dimension : SmoothOfRelativeDimension (geometricGenus K c + d - 1) carrier.hom
  /-- Finite type follows from smoothness and this quasi-compactness. -/
  quasiCompact : QuasiCompact carrier.hom
  /-- Separation descends along the finite faithfully flat cover. -/
  separated : IsSeparated carrier.hom
  /-- Geometric connectedness descends along the same cover. -/
  geometricallyConnected : GeometricallyConnected carrier.hom

include hd in
/-- Positive-modulus Picard-zero is represented over the original arbitrary
field. All local data and the required descent properties are constructed. -/
theorem nonempty_presentation : Nonempty (Presentation c D) := by
  obtain ⟨x₀, -⟩ := c.surjective (default : Spec (CommRingCat.of K))
  have : Nonempty C := ⟨x₀⟩
  obtain ⟨x, -, hfin⟩ := Scheme.exists_finite_pointResidueAlgebra c
  let a : Algebra K (C.residueField x) := Scheme.pointResidueAlgebra c x
  have : Module.Finite K (C.residueField x) := hfin
  let L := C.residueField x
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L) :=
    Scheme.pointResidueSection c x
  let DL := RelEffCartierDiv.changeBaseOfIdentity (specMap K L) D
  let J := Pointed.groupScheme (baseChange K c L) ε DL hd
  let F := (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙ forget CommGrpCat.{u + 1}
  let eJ : ((Over.map (specMap K L)).op ⋙ F).RepresentableBy (Over.mk J.X.hom) :=
    scalarExtensionRepresentable c D hd L ε
  let A : DescentAction (specMap K L) J.X.hom :=
    DescentAction.ofRepresentableBy (specMap K L) F J.X.hom eJ
  have haff : ∀ S : Finset J.X.left,
      ∃ U : J.X.left.Opens, IsAffineOpen U ∧ ∀ y ∈ S, y ∈ U :=
    Pointed.exists_isAffineOpen_forall_mem (baseChange K c L) ε DL hd
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
  have hlocal := Pointed.geometry (baseChange K c L) ε DL hd
  have : SmoothOfRelativeDimension (geometricGenus L (baseChange K c L) + d - 1)
      J.X.hom := hlocal.1
  have hsm : Smooth J.X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus L (baseChange K c L) + d - 1) J.X.hom
  have hqc : QuasiCompact J.X.hom := hlocal.2.2.1
  have hsep : IsSeparated J.X.hom := hlocal.2.2.2.1
  have hgc : GeometricallyConnected J.X.hom := hlocal.2.2.2.2
  obtain ⟨hsmP, hsepP, hqcP, hgcP⟩ :=
    smooth_isSeparated_quasiCompact_geometricallyConnected_of_faithfullyFlat_baseChange
      K L p J.X.hom hsm hsep hqc hgc e he
  have : Smooth p := hsmP
  have : GeometricallyConnected p := hgcP
  have : ConnectedSpace J.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton J.X.hom
  have hdim : SmoothOfRelativeDimension (geometricGenus K c + d - 1) J.X.hom := by
    rw [← geometricGenus_baseChange_of_finite_of_section K c L ε]
    exact hlocal.1
  have hdimP : SmoothOfRelativeDimension (geometricGenus K c + d - 1) p :=
    smoothOfRelativeDimension_of_connected_scalarExtension K L p J.X.hom
      (Classical.choice (inferInstance : Nonempty J.X.left))
      (geometricGenus K c + d - 1) e he
  exact ⟨⟨Over.mk p, eP, hdimP, hqcP, hsepP, hgcP⟩⟩

/-- One fixed choice of the proved complete representation. -/
def presentation : Presentation c D := Classical.choice (nonempty_presentation c D hd)

/-- The actual generalized Jacobian group scheme, with no rational basepoint. -/
def groupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (presentation c D hd).representation

/-- The tensor-product group sheaf is represented by the same descended carrier. -/
def groupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (groupScheme c D hd).X :=
  (presentation c D hd).representation

/-- The type-valued modulus zero sheaf has the same actual representation. -/
def picardZeroRepresentable :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.RepresentableBy
      (groupScheme c D hd).X :=
  (groupRepresentable c D hd).ofIso (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D))

/-- The final group scheme is smooth of the expected dimension, of finite type,
separated and geometrically connected over the original field. -/
theorem geometry :
    SmoothOfRelativeDimension (geometricGenus K c + d - 1) (groupScheme c D hd).X.hom ∧
      LocallyOfFiniteType (groupScheme c D hd).X.hom ∧
      QuasiCompact (groupScheme c D hd).X.hom ∧
      IsSeparated (groupScheme c D hd).X.hom ∧
      GeometricallyConnected (groupScheme c D hd).X.hom := by
  let M := presentation c D hd
  have : SmoothOfRelativeDimension (geometricGenus K c + d - 1) M.carrier.hom := M.dimension
  have : Smooth M.carrier.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + d - 1) M.carrier.hom
  change SmoothOfRelativeDimension (geometricGenus K c + d - 1) M.carrier.hom ∧
    LocallyOfFiniteType M.carrier.hom ∧ QuasiCompact M.carrier.hom ∧
      IsSeparated M.carrier.hom ∧ GeometricallyConnected M.carrier.hom
  exact ⟨M.dimension, inferInstance, M.quasiCompact, M.separated, M.geometricallyConnected⟩

/-- Geometric integrality concerns the same constructed generalized Jacobian. -/
theorem geometricallyIntegral : GeometricallyIntegral (groupScheme c D hd).X.hom := by
  have h := geometry c D hd
  have : SmoothOfRelativeDimension (geometricGenus K c + d - 1)
      (groupScheme c D hd).X.hom := h.1
  have : Smooth (groupScheme c D hd).X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + d - 1) _
  have : GeometricallyConnected (groupScheme c D hd).X.hom := h.2.2.2.2
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected _

end AlgebraicGeometry.GeneralizedJacobian.Unpointed
