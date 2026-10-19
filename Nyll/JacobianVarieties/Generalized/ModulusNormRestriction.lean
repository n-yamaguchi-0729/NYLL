/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRestrictionComparison
import Nyll.JacobianVarieties.Generalized.ModulusUnitRestrictionBoundary
import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionGroup
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionGeometry

/-! # Actual norm quotient restriction and its generalized Jacobian boundary -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {R : Type u} [CommRing R] {Y Y' : Scheme.{u}}
  {q r : Y ⟶ Spec (CommRingCat.of R)} {q' r' : Y' ⟶ Spec (CommRingCat.of R)}

/-- Actual unit restriction commutes with equality transport of the structural maps. -/
theorem modulusUnitRestrictionSheaf_congr (j : Y' ⟶ Y) (w : j ≫ q = q')
    (hq : q = r) (hq' : q' = r') :
    modulusUnitRestrictionSheaf j w ≫ eqToHom (congrArg modulusUnitQuotientGroupSheaf hq') =
      eqToHom (congrArg modulusUnitQuotientGroupSheaf hq) ≫
        modulusUnitRestrictionSheaf j (by rw [← hq, ← hq']; exact w) := by
  cases hq
  cases hq'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

open ScalarFrames ScalarQuotientSchemePresheaf

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

include w in
/-- A commuting actual modulus inclusion respects its original finite structural maps. -/
theorem modulusRestriction_toBase : j ≫ modulusBaseMap D = modulusBaseMap D' := by
  rw [← modulusCurveMap_toBase D, ← Category.assoc, ← w, modulusCurveMap_toBase D']

/-- The restriction homomorphism of the entire actual finite modulus algebra. -/
def modulusAlgebraRestriction : modulusAlgebra D →ₐ[K] modulusAlgebra D' :=
  coordinateRestriction (modulusBaseMap D) (modulusBaseMap D') j
    (modulusRestriction_toBase D D' j w)

/-- The corresponding actual scalar-unit group sheaf restriction. -/
def modulusNormRestrictionSheaf : scalarQuotientGroupSheaf K (modulusAlgebra D) ⟶
    scalarQuotientGroupSheaf K (modulusAlgebra D') :=
  algebraRestrictionGroupSheaf (modulusAlgebraRestriction D D' j w)

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- The existing intrinsic norm comparison is natural for the actual changing modulus. -/
theorem modulusAlgebraUnitGroupSheafIso_restriction :
    modulusNormRestrictionSheaf D D' j w ≫ (modulusAlgebraUnitGroupSheafIso D').hom =
      (modulusAlgebraUnitGroupSheafIso D).hom ≫
        modulusUnitRestrictionSheaf j (by rw [← Category.assoc, ← w]) := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  have : IsFinite (modulusBaseMap D') := D'.isFinite
  have ha := modulusUnitGroupSheafComparisonIso_restriction j
    (modulusRestriction_toBase D D' j w)
  have he := modulusUnitRestrictionSheaf_congr j (modulusRestriction_toBase D D' j w)
    (modulusCurveMap_toBase D).symm (modulusCurveMap_toBase D').symm
  change modulusNormRestrictionSheaf D D' j w ≫
      ((modulusUnitGroupSheafComparisonIso (modulusBaseMap D')).hom ≫
        eqToHom (congrArg modulusUnitQuotientGroupSheaf (modulusCurveMap_toBase D').symm)) =
    ((modulusUnitGroupSheafComparisonIso (modulusBaseMap D)).hom ≫
      eqToHom (congrArg modulusUnitQuotientGroupSheaf (modulusCurveMap_toBase D).symm)) ≫ _
  change modulusNormRestrictionSheaf D D' j w ≫
      (modulusUnitGroupSheafComparisonIso (modulusBaseMap D')).hom = _ at ha
  calc
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ eqToHom
      (congrArg modulusUnitQuotientGroupSheaf (modulusCurveMap_toBase D').symm)) ha
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun k =>
      (modulusUnitGroupSheafComparisonIso (modulusBaseMap D)).hom ≫ k) he
    _ = _ := (Category.assoc _ _ _).symm

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- Actual norm restriction and actual rigidification restriction commute with the boundary. -/
theorem modulusNormBoundarySheaf_restriction :
    modulusNormRestrictionSheaf D D' j w ≫ modulusNormBoundarySheaf D' =
      modulusNormBoundarySheaf D ≫ modulusRestrictionZeroSheaf c j w := by
  change modulusNormRestrictionSheaf D D' j w ≫
      ((modulusAlgebraUnitGroupSheafIso D').hom ≫
        modulusUnitBoundarySheaf c (modulusCurveMap D')) =
    ((modulusAlgebraUnitGroupSheafIso D).hom ≫
      modulusUnitBoundarySheaf c (modulusCurveMap D)) ≫ _
  rw [← Category.assoc, modulusAlgebraUnitGroupSheafIso_restriction, Category.assoc,
    modulusUnitBoundarySheaf_restriction, ← Category.assoc]

variable (hd : 0 < d) (hd' : 0 < d')

/-- The actual canonical restriction of the concrete norm quotient schemes. -/
def modulusNormRestriction : (modulusUnitQuotient D hd).X ⟶
    (modulusUnitQuotient D' hd').X :=
  quotientRestrictionOver (positiveModulusBasis D hd) (positiveModulusBasis D' hd')
    (modulusAlgebraRestriction D D' j w)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- This concrete morphism represents the actual scalar-unit group sheaf restriction. -/
theorem modulusNormRestriction_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (a : T ⟶ (modulusUnitQuotient D hd).X) :
    (modulusUnitQuotientRepresentable D' hd').homEquiv
        (a ≫ modulusNormRestriction D D' j w hd hd') =
      ((modulusNormRestrictionSheaf D D' j w).hom.app (op T)).hom
        ((modulusUnitQuotientRepresentable D hd).homEquiv a) :=
  quotientRestrictionOver_homEquiv (positiveModulusBasis D hd)
    (positiveModulusBasis D' hd') (modulusAlgebraRestriction D D' j w) a

/-- The concrete scalar restriction and constructed Jacobian transition have the same boundary. -/
@[reassoc] theorem modulusNormBoundary_restriction :
    modulusNormRestriction D D' j w hd hd' ≫ (modulusNormBoundary c D' hd').hom.hom.hom =
      (modulusNormBoundary c D hd).hom.hom.hom ≫
        (transitionAlong c D D' j w).hom.hom.hom := by
  apply (groupRepresentable c D').homEquiv.injective
  rw [modulusNormBoundary_homEquiv, transitionAlong_homEquiv]
  have hr := modulusNormRestriction_homEquiv D D' j w hd hd'
    (𝟙 (modulusUnitQuotient D hd).X)
  rw [Category.id_comp] at hr
  have hb := modulusNormBoundary_homEquiv c D hd (𝟙 (modulusUnitQuotient D hd).X)
  rw [Category.id_comp] at hb
  rw [hr, hb]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun a => a.hom) (modulusNormBoundarySheaf_restriction D D' j w))
      (op (modulusUnitQuotient D hd).X))
    ((modulusUnitQuotientRepresentable D hd).homEquiv (𝟙 _))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

variable [IsClosedImmersion j]

/-- Closedness of the actual inclusion supplies the required algebra surjection. -/
theorem modulusAlgebraRestriction_surjective :
    Function.Surjective (modulusAlgebraRestriction D D' j w) := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  exact coordinateRestriction_surjective (modulusBaseMap D) (modulusBaseMap D') j
    (modulusRestriction_toBase D D' j w)

include w in
/-- The actual closed inclusion cannot increase the full finite modulus degree. -/
theorem modulusDegree_le_of_inclusion : d' ≤ d := by
  have : Module.Finite K (modulusAlgebra D) := Module.Finite.of_basis (modulusBasis D)
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (modulusAlgebraRestriction D D' j w).toLinearMap)
    (modulusAlgebraRestriction_surjective D D' j w)
  rw [finrank_modulusAlgebra, finrank_modulusAlgebra] at h
  exact h

/-- Actual changing-modulus norm restriction is smooth. -/
theorem modulusNormRestriction_smooth : Smooth (modulusNormRestriction D D' j w hd hd').left :=
  smooth_quotientRestrictionMap (positiveModulusBasis D hd) (positiveModulusBasis D' hd')
    (modulusAlgebraRestriction D D' j w) (modulusAlgebraRestriction_surjective D D' j w)

/-- Every point of the smaller actual norm quotient has a lift. -/
theorem modulusNormRestriction_surjective :
    Surjective (modulusNormRestriction D D' j w hd hd').left :=
  surjective_quotientRestrictionMap (positiveModulusBasis D hd) (positiveModulusBasis D' hd')
    (modulusAlgebraRestriction D D' j w) (modulusAlgebraRestriction_surjective D D' j w)

/-- The actual norm restriction has irreducible geometric fibres. -/
theorem modulusNormRestriction_geometricallyIrreducible :
    GeometricallyIrreducible (modulusNormRestriction D D' j w hd hd').left :=
  geometricallyIrreducible_quotientRestrictionMap
    (positiveModulusBasis D hd) (positiveModulusBasis D' hd')
    (modulusAlgebraRestriction D D' j w) (modulusAlgebraRestriction_surjective D D' j w)

/-- In particular the actual changing-modulus norm restriction has connected geometric fibres. -/
theorem modulusNormRestriction_geometricallyConnected :
    GeometricallyConnected (modulusNormRestriction D D' j w hd hd').left :=
  geometricallyConnected_quotientRestrictionMap
    (positiveModulusBasis D hd) (positiveModulusBasis D' hd')
    (modulusAlgebraRestriction D D' j w) (modulusAlgebraRestriction_surjective D D' j w)

end AlgebraicGeometry.GeneralizedJacobian
