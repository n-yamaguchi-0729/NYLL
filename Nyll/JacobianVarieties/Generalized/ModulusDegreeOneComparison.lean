/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDegreeOneSheaf
import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.EmptyOrdinaryComparison
import Nyll.JacobianVarieties.Generalized.ModulusTransitionTorsor

/-! # A single rational reduced modulus gives the ordinary Jacobian -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  (D : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))))

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The actual forgetting homomorphism is an isomorphism of constructed group schemes. -/
def degreeOneGroupIso : groupScheme c D ≅ ordinaryGroupScheme c :=
  SchemeTheory.RepresentedGroups.iso _ _ (groupRepresentable c D)
    (ordinaryGroupRepresentable c)
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      CommGrpCat.{u + 1}).mapIso (degreeOneForgetfulSheafIso D))

/-- The comparison uses the actual modulus-forgetting group map. -/
theorem degreeOneGroupIso_hom : (degreeOneGroupIso D).hom = groupProjection c D := rfl

/-- The resulting group scheme is the previously constructed ordinary Jacobian with its
existing group law. -/
def degreeOneOrdinaryComparison :
    groupScheme c D ≅ JacobianVarieties.Picard.Unpointed.groupScheme K c :=
  degreeOneGroupIso D ≪≫
    (emptyModulusGroupIso c (RelEffCartierDiv.empty c (𝟙 _))).symm ≪≫
      zeroDegreeOrdinaryComparison c (RelEffCartierDiv.empty c (𝟙 _))

/-- The actual degree-one-to-empty transition is the comparison through the
ordinary Jacobian; the modulus restriction is not replaced by an unrelated map. -/
theorem transitionAlong_degreeOne_zero_eq
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))
    (j : D₀.I.subscheme ⟶ D.I.subscheme)
    (w : modulusCurveMap D₀ = j ≫ modulusCurveMap D) :
    transitionAlong c D D₀ j w =
      (degreeOneGroupIso D ≪≫ (emptyModulusGroupIso c D₀).symm).hom := by
  apply (cancel_mono (emptyModulusGroupIso c D₀).hom).mp
  change transitionAlong c D D₀ j w ≫ (emptyModulusGroupIso c D₀).hom =
    ((degreeOneGroupIso D).hom ≫ (emptyModulusGroupIso c D₀).inv) ≫
      (emptyModulusGroupIso c D₀).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    emptyModulusGroupIso_hom, degreeOneGroupIso_hom]
  apply CommGrp.hom_ext
  exact transitionAlong_groupProjection c D D₀ j w

/-- Forgetting a single rational reduced modulus to any degree-zero modulus is
an isomorphism for the actual canonical transition. -/
theorem transitionAlong_degreeOne_zero_isIso
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))
    (j : D₀.I.subscheme ⟶ D.I.subscheme)
    (w : modulusCurveMap D₀ = j ≫ modulusCurveMap D) :
    IsIso (transitionAlong c D D₀ j w) := by
  rw [transitionAlong_degreeOne_zero_eq D D₀ j w]
  infer_instance

end AlgebraicGeometry.GeneralizedJacobian
