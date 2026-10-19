/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRawInjectivity
import Nyll.JacobianVarieties.Generalized.PoincareRawLocalBijection
import Nyll.JacobianVarieties.Generalized.PoincareSheafSurjectivity

/-!
# The constructed Poincaré frame scheme represents modulus Picard-zero

Actual raw frames are locally bijective onto both the represented total family
and the modulus zero sheaf. Thus the existing comparison is an isomorphism.
For positive modulus degree, the scheme already glued from frame quotients
represents the zero sheaf. No new representability assumption is introduced.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- Equality of total frame-family classes is detected locally by modulus zero classes. -/
instance poincareFrameTotalToModulusPicardZero_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareFrameTotalToModulusPicardZero D h) := by
  have : Presheaf.IsLocallyInjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawFrameToModulusZero D h) :=
    Presheaf.isLocallyInjective_of_injective _ _
      (fun T => poincareRawFrameToModulusZero_injective D h T.unop)
  have : Presheaf.IsLocallyInjective
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawToFrameFamily D h ≫ poincareFrameTotalToModulusPicardZero D h) := by
    rw [poincareRawToFrameFamily_comp_toModulusPicardZero D h]
    exact Presheaf.isLocallyInjective_comp
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (poincareRawFrameToModulusZero D h)
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroPresheaf c (modulusCurveMap D)))
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (poincareRawToFrameFamily D h) (poincareFrameTotalToModulusPicardZero D h)

/-- The actual comparison identifies the represented total family with the zero sheaf. -/
def poincareFramePicardZeroIso (hd : 0 < d) :
    poincareFrameTotalFamily D h ≅ (modulusPicardZeroSheaf c (modulusCurveMap D)).obj := by
  let F : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1)) :=
    ⟨poincareFrameTotalFamily D h, poincareFrameTotalFamily_isSheaf D h hd⟩
  let f : F ⟶ modulusPicardZeroSheaf c (modulusCurveMap D) :=
    ⟨poincareFrameTotalToModulusPicardZero D h⟩
  have hi : Sheaf.IsLocallyInjective f :=
    poincareFrameTotalToModulusPicardZero_isLocallyInjective D h
  have hs : Sheaf.IsLocallySurjective f :=
    poincareFrameTotalToModulusPicardZero_isLocallySurjective D h
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨hi, hs⟩
  exact (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (Type (u + 1))).mapIso (asIso f)

/-- The identification uses the original modulus comparison. -/
theorem poincareFramePicardZeroIso_hom (hd : 0 < d) :
    (poincareFramePicardZeroIso D h hd).hom = poincareFrameTotalToModulusPicardZero D h := rfl

/-- The concrete frame quotient represents the modulus Picard-zero sheaf. -/
def poincareModulusPicardZeroRepresentable (hd : 0 < d) :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.RepresentableBy
      ((Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :=
  (poincareFrameTotalRepresentable D h hd).ofIso (poincareFramePicardZeroIso D h hd)

end AlgebraicGeometry.GeneralizedJacobian
