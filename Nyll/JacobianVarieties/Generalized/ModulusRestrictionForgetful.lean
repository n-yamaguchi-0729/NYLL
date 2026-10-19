/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMapSheaf
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup

/-! # Compatibility of modulus restriction with the ordinary Picard class -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i)

/-- Restricting the chosen trivialization leaves the underlying ordinary zero class unchanged. -/
@[reassoc] theorem modulusRestrictionZeroPresheaf_forget :
    modulusRestrictionZeroPresheaf c j w ≫ forgetModulusZeroGroupPresheaf c i' =
      forgetModulusZeroGroupPresheaf c i := by
  apply NatTrans.ext
  funext T
  refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
  apply Subtype.ext
  exact modulusRestrictionClasses_forget c j w T.unop.hom x.val

/-- The same compatibility holds for the actual fppf group sheaves. -/
@[reassoc] theorem modulusRestrictionZeroSheaf_forget :
    modulusRestrictionZeroSheaf c j w ≫ forgetModulusZeroGroupSheaf c i' =
      forgetModulusZeroGroupSheaf c i := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}
  exact (H.map_comp (modulusRestrictionZeroPresheaf c j w)
    (forgetModulusZeroGroupPresheaf c i')).symm.trans
      (congrArg (fun v => H.map v) (modulusRestrictionZeroPresheaf_forget c j w))

end AlgebraicGeometry.GeneralizedJacobian
