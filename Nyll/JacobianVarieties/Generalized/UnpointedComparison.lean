/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.UnpointedConstruction
import Nyll.JacobianVarieties.Generalized.PointedComparison
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # Compatibility of the descended generalized Jacobian with every pointed construction -/

noncomputable section

universe u

open CategoryTheory NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- Whenever a rational section is available, the unpointed construction agrees
with the actual frame construction, including the tensor-product group law. -/
def pointedComparison : groupScheme c D hd ≅ Pointed.groupScheme c ε D hd :=
  SchemeTheory.RepresentedGroups.iso
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (groupRepresentable c D hd) (Pointed.groupRepresentable c ε D hd) (Iso.refl _)

/-- Comparison preserves the classified modulus bundle on every test scheme. -/
theorem pointedComparison_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (groupScheme c D hd).X) :
    (Pointed.groupRepresentable c ε D hd).homEquiv
        (f ≫ (pointedComparison c ε D hd).hom.hom.hom.hom) =
      (groupRepresentable c D hd).homEquiv f :=
  SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _
    (groupRepresentable c D hd) (Pointed.groupRepresentable c ε D hd) (𝟙 _) f

/-- Changing the auxiliary rational section is compatible with the unique
comparison defined by the actual classifying equivalences. -/
theorem pointedComparison_comp
    (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    (pointedComparison c ε D hd).hom ≫ (Pointed.sectionComparison c ε ε' D hd).hom =
      (pointedComparison c ε' D hd).hom := by
  apply CommGrp.hom_ext
  apply (Pointed.groupRepresentable c ε' D hd).homEquiv.injective
  change (Pointed.groupRepresentable c ε' D hd).homEquiv
      ((pointedComparison c ε D hd).hom.hom.hom.hom ≫
        (Pointed.sectionComparison c ε ε' D hd).hom.hom.hom.hom) =
    (Pointed.groupRepresentable c ε' D hd).homEquiv
      (pointedComparison c ε' D hd).hom.hom.hom.hom
  rw [Pointed.sectionComparison_homEquiv]
  have h₁ := pointedComparison_homEquiv c ε D hd (𝟙 (groupScheme c D hd).X)
  have h₂ := pointedComparison_homEquiv c ε' D hd (𝟙 (groupScheme c D hd).X)
  rw [Category.id_comp] at h₁ h₂
  exact h₁.trans h₂.symm

end AlgebraicGeometry.GeneralizedJacobian.Unpointed
