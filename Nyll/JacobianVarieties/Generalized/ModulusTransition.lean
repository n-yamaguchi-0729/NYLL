/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.Construction
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMapSheaf
import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Canonical transitions between constructed generalized Jacobians

The transition represents restriction of the actual trivialization on the
whole modulus. Ideal containment supplies a canonical closed inclusion, so
no auxiliary modulus morphism is needed when divisors are ordered.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)

/-- The group morphism representing restriction of the whole modulus rigidification. -/
def transitionAlong : groupScheme c D ⟶ groupScheme c D' := by
  cases d <;> cases d' <;>
    exact SchemeTheory.RepresentedGroups.map
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D')).obj
      (groupRepresentable c D) (groupRepresentable c D')
      (modulusRestrictionZeroSheaf c j w).hom

/-- The represented transition sends every class to its actual restricted trivialization. -/
theorem transitionAlong_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (groupScheme c D).X) :
    (groupRepresentable c D').homEquiv
        (f ≫ (transitionAlong c D D' j w).hom.hom.hom) =
      ((modulusRestrictionZeroSheaf c j w).hom.app (op T)).hom
        ((groupRepresentable c D).homEquiv f) := by
  cases d <;> cases d' <;>
    exact SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _ _ _ _ f

/-- The point classification of the transition preserves the tensor-product operation. -/
theorem transitionAlong_pointEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (groupScheme c D).X) :
    pointEquiv c D' T (f ≫ (transitionAlong c D D' j w).hom.hom.hom) =
      ((modulusRestrictionZeroSheaf c j w).hom.app (op T)).hom (pointEquiv c D T f) := by
  cases d <;> cases d' <;> exact transitionAlong_homEquiv c D D' j w f

theorem transitionAlong_id :
    transitionAlong c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm =
      𝟙 (groupScheme c D) := by
  apply CommGrp.hom_ext
  apply (groupRepresentable c D).homEquiv.injective
  change (groupRepresentable c D).homEquiv
      (transitionAlong c D D (𝟙 _) (Category.id_comp (modulusCurveMap D)).symm).hom.hom.hom =
    (groupRepresentable c D).homEquiv (𝟙 _)
  have h := transitionAlong_homEquiv c D D (𝟙 _)
    (Category.id_comp (modulusCurveMap D)).symm (𝟙 (groupScheme c D).X)
  rw [Category.id_comp, modulusRestrictionZeroSheaf_id] at h
  exact h

theorem transitionAlong_comp {d'' : ℕ}
    (D'' : RelEffCartierDiv c d'' (𝟙 (Spec (CommRingCat.of K))))
    (k : D''.I.subscheme ⟶ D'.I.subscheme)
    (w' : modulusCurveMap D'' = k ≫ modulusCurveMap D') :
    transitionAlong c D D' j w ≫ transitionAlong c D' D'' k w' =
      transitionAlong c D D'' (k ≫ j) (by rw [w', w, Category.assoc]) := by
  apply CommGrp.hom_ext
  apply (groupRepresentable c D'').homEquiv.injective
  change (groupRepresentable c D'').homEquiv
      ((transitionAlong c D D' j w).hom.hom.hom ≫
        (transitionAlong c D' D'' k w').hom.hom.hom) =
    (groupRepresentable c D'').homEquiv
      (transitionAlong c D D'' (k ≫ j) _).hom.hom.hom
  rw [transitionAlong_homEquiv]
  have h₁ := transitionAlong_homEquiv c D D' j w (𝟙 (groupScheme c D).X)
  have h₂ := transitionAlong_homEquiv c D D'' (k ≫ j)
    (by rw [w', w, Category.assoc]) (𝟙 (groupScheme c D).X)
  rw [Category.id_comp] at h₁ h₂
  rw [h₁, h₂]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun a => a.hom) (modulusRestrictionZeroSheaf_comp c j w k w'))
      (op (groupScheme c D).X)) ((groupRepresentable c D).homEquiv (𝟙 _))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- Ideal containment gives the actual commuting inclusion of the smaller modulus.
The order of ideals is opposite to the order of effective divisors. -/
theorem modulusIdealInclusion_curve (h : D.I ≤ D'.I) :
    modulusCurveMap D' = Scheme.IdealSheafData.inclusion h ≫ modulusCurveMap D := by
  simp only [modulusCurveMap, ← Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- The canonical morphism furnished by ideal containment is a closed immersion. -/
theorem modulusIdealInclusion_isClosedImmersion (h : D.I ≤ D'.I) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ D.I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ D.I.subschemeι

/-- The canonical transition to a smaller effective modulus. -/
def transition (h : D.I ≤ D'.I) : groupScheme c D ⟶ groupScheme c D' :=
  transitionAlong c D D' (Scheme.IdealSheafData.inclusion h)
    (modulusIdealInclusion_curve c D D' h)

theorem transition_id : transition c D D le_rfl = 𝟙 (groupScheme c D) := by
  simpa only [transition, Scheme.IdealSheafData.inclusion_id] using transitionAlong_id c D

theorem transition_comp {d'' : ℕ}
    (D'' : RelEffCartierDiv c d'' (𝟙 (Spec (CommRingCat.of K))))
    (h : D.I ≤ D'.I) (h' : D'.I ≤ D''.I) :
    transition c D D' h ≫ transition c D' D'' h' =
      transition c D D'' (h.trans h') := by
  simpa only [transition, Scheme.IdealSheafData.inclusion_comp] using
    transitionAlong_comp c D D' (Scheme.IdealSheafData.inclusion h)
      (modulusIdealInclusion_curve c D D' h) D'' (Scheme.IdealSheafData.inclusion h')
      (modulusIdealInclusion_curve c D' D'' h')

end AlgebraicGeometry.GeneralizedJacobian
