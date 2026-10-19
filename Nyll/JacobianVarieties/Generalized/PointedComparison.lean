/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedConstruction
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # Independence of the section used in the positive-modulus construction -/

noncomputable section

universe u

open CategoryTheory NeronModelInfra Opposite

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- Two actual curve sections give canonically isomorphic represented group schemes.
Neither section is required to avoid the modulus. -/
def sectionComparison : groupScheme c ε D hd ≅ groupScheme c ε' D hd :=
  SchemeTheory.RepresentedGroups.iso
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (groupRepresentable c ε D hd) (groupRepresentable c ε' D hd) (Iso.refl _)

/-- The comparison preserves the actual represented modulus class on every test scheme. -/
theorem sectionComparison_homEquiv {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (groupScheme c ε D hd).X) :
    (groupRepresentable c ε' D hd).homEquiv
        (f ≫ (sectionComparison c ε ε' D hd).hom.hom.hom.hom) =
      (groupRepresentable c ε D hd).homEquiv f :=
  SchemeTheory.RepresentedGroups.mapMorphism_homEquiv _ _
    (groupRepresentable c ε D hd) (groupRepresentable c ε' D hd) (𝟙 _) f

/-- Comparison with the same section is the identity, including the group structure. -/
theorem sectionComparison_refl :
    (sectionComparison c ε ε D hd).hom = 𝟙 (groupScheme c ε D hd) := by
  apply CommGrp.hom_ext
  apply (groupRepresentable c ε D hd).homEquiv.injective
  change (groupRepresentable c ε D hd).homEquiv
      (sectionComparison c ε ε D hd).hom.hom.hom.hom =
    (groupRepresentable c ε D hd).homEquiv (𝟙 (groupScheme c ε D hd).X)
  simpa only [Category.id_comp] using
    sectionComparison_homEquiv c ε ε D hd (𝟙 (groupScheme c ε D hd).X)

/-- All three section choices use the same classifying equivalence and obey the cocycle law. -/
theorem sectionComparison_comp (ε'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    (sectionComparison c ε ε' D hd).hom ≫ (sectionComparison c ε' ε'' D hd).hom =
      (sectionComparison c ε ε'' D hd).hom := by
  apply CommGrp.hom_ext
  apply (groupRepresentable c ε'' D hd).homEquiv.injective
  change (groupRepresentable c ε'' D hd).homEquiv
      ((sectionComparison c ε ε' D hd).hom.hom.hom.hom ≫
        (sectionComparison c ε' ε'' D hd).hom.hom.hom.hom) =
    (groupRepresentable c ε'' D hd).homEquiv
      (sectionComparison c ε ε'' D hd).hom.hom.hom.hom
  rw [sectionComparison_homEquiv]
  have h₁ := sectionComparison_homEquiv c ε ε' D hd (𝟙 (groupScheme c ε D hd).X)
  have h₂ := sectionComparison_homEquiv c ε ε'' D hd (𝟙 (groupScheme c ε D hd).X)
  rw [Category.id_comp] at h₁ h₂
  exact h₁.trans h₂.symm

end AlgebraicGeometry.GeneralizedJacobian.Pointed
