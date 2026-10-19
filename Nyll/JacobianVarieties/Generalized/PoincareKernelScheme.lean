/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareGroupProjection
import Nyll.JacobianVarieties.Generalized.PoincareZeroFibre

/-!
# The scheme fibre at the identity of the modulus-forgetting group morphism

Both the projection and the ordinary identity are identified with their
geometric constructions. The scheme-theoretic fibre at that identity is
therefore the scalar-unit quotient of the full modulus.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

/-- The scheme-theoretic fibre of the actual group morphism over its actual identity. -/
def poincareModulusKernelScheme : Over (Spec (CommRingCat.of K)) :=
  Over.mk (pullback.snd (poincareModulusGroupProjection D h hd).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryZeroCommGroupScheme h).X).left)

/-- The actual identity fibre, as a scheme over the field, is the full scalar-unit quotient. -/
def poincareModulusKernelSchemeIso :
    poincareModulusKernelScheme D h hd ≅ (modulusUnitQuotient D hd).X := by
  change Over.mk (pullback.snd (poincareModulusGroupProjection D h hd).hom.hom.hom.left
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ordinaryZeroCommGroupScheme h).X).left) ≅ _
  rw [poincareModulusGroupProjection_eq, ordinaryZeroCommGroupScheme_one]
  exact poincareZeroFibreIso D h hd

end AlgebraicGeometry.GeneralizedJacobian
