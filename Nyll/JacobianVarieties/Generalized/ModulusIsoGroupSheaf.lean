/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusIsoComparison
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf

/-! # Picard-zero group sheaves for isomorphic whole moduli -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (a : D' ≅ D) (w : i' = a.hom ≫ i)

/-- Restriction of the actual modulus comparison to its geometric-fibre zero subgroup. -/
def modulusIsoZeroClassesEquiv (T : Over (Spec (CommRingCat.of R))) :
    (modulusPicardZeroGroupPresheaf c i).obj (op T) ≃*
      (modulusPicardZeroGroupPresheaf c i').obj (op T) where
  toFun x := ⟨modulusIsoClassesEquiv c a w T.hom x.val,
    (modulusIsoClassesEquiv_zero_iff c a w T.hom x.val).mpr x.property⟩
  invFun y := ⟨(modulusIsoClassesEquiv c a w T.hom).symm y.val,
    (modulusIsoClassesEquiv_zero_iff c a w T.hom _).mp (by
      rw [MulEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((modulusIsoClassesEquiv c a w T.hom).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((modulusIsoClassesEquiv c a w T.hom).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext ((modulusIsoClassesEquiv c a w T.hom).map_mul x.val y.val)

/-- Natural comparison of the actual zero class groups before sheafification. -/
def modulusPicardZeroGroupModulusIso :
    modulusPicardZeroGroupPresheaf c i ≅ modulusPicardZeroGroupPresheaf c i' :=
  NatIso.ofComponents (fun T => (modulusIsoZeroClassesEquiv c a w T.unop).toCommGrpIso)
    (fun f => by
      refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      apply Subtype.ext
      exact modulusIsoClassesEquiv_naturality c a w f.unop x.val)

/-- The actual comparison after fppf sheafification. -/
def modulusPicardZeroGroupSheafModulusIso :
    modulusPicardZeroGroupSheaf c i ≅ modulusPicardZeroGroupSheaf c i' :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).mapIso (modulusPicardZeroGroupModulusIso c a w)

end AlgebraicGeometry.GeneralizedJacobian
