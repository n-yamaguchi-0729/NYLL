/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoPullback
import Nyll.AlgebraicCurves.Models.Construction.Transport

/-! # Intrinsic uniqueness for the pointed generalized Abel morphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Actual Abel points generate the field-point group intrinsically for
any smooth proper geometrically integral curve over an algebraically
closed field. -/
theorem modulusAbel_points_addHom_ext_of_isAlgClosed
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {A : Type*} [AddCommGroup A]
    (φ ψ : Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (groupScheme c D).X) →+ A)
    (heq : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c),
      φ (Additive.ofMul (x ≫ modulusAbelMap c D ε)) =
        ψ (Additive.ofMul (x ≫ modulusAbelMap c D ε))) : φ = ψ := by
  obtain ⟨L, _, _, _, _, M, e, he⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed K c K (𝟙 _)
  let e' : M.C ≅ C := e ≪≫ asIso (pullback.fst c (𝟙 _))
  have he' : e'.hom ≫ c = M.toBase := by
    change (e.hom ≫ pullback.fst c (𝟙 _)) ≫ c = M.toBase
    rw [Category.assoc, pullback.condition, Category.comp_id]
    exact he
  have : GeometricallyIntegral (M.transport c e' he').toBase := by
    change GeometricallyIntegral c
    infer_instance
  exact (M.transport c e' he').modulusAbel_points_addHom_ext D ε φ ψ heq

/-- Actual group morphisms out of the generalized Jacobian are determined
by their composition with the actual pointed Abel morphism. The curve
model used in the proof is supplied by the smooth proper curve itself. -/
theorem modulusAbel_groupHom_ext_of_isAlgClosed
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    [IsSeparated G.X.hom]
    (f g : groupScheme c D ⟶ G)
    (heq : modulusAbelMap c D ε ≫ f.hom.hom.hom =
      modulusAbelMap c D ε ≫ g.hom.hom.hom) : f = g := by
  obtain ⟨L, _, _, _, _, M, e, he⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed K c K (𝟙 _)
  let e' : M.C ≅ C := e ≪≫ asIso (pullback.fst c (𝟙 _))
  have he' : e'.hom ≫ c = M.toBase := by
    change (e.hom ≫ pullback.fst c (𝟙 _)) ≫ c = M.toBase
    rw [Category.assoc, pullback.condition, Category.comp_id]
    exact he
  have : GeometricallyIntegral (M.transport c e' he').toBase := by
    change GeometricallyIntegral c
    infer_instance
  exact (M.transport c e' he').modulusAbel_groupHom_ext D ε G f g heq

end AlgebraicGeometry.GeneralizedJacobian
