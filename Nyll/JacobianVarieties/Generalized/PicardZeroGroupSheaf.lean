/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Nyll.JacobianVarieties.Generalized.PicardGroupSheaf

/-!
# The group sheaf underlying modulus Picard-zero

Sheafifying the actual zero subgroup in commutative groups supplies its group
law. Compatibility of sheafification with the forgetful functor identifies
its underlying sheaf with the previously defined modulus Picard-zero sheaf.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The group sheaf obtained from actual fibrewise-zero rigidified tensor classes. -/
def modulusPicardZeroGroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).obj (modulusPicardZeroGroupPresheaf c i)

/-- The actual group sheaf has the canonical zero sheaf as its underlying presheaf. -/
def modulusPicardZeroGroupSheafForgetIso :
    (modulusPicardZeroGroupSheaf c i).obj ⋙ forget CommGrpCat.{u + 1} ≅
      (modulusPicardZeroSheaf c i).obj :=
  (sheafifyComposeIso (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (modulusPicardZeroGroupPresheaf c i)).symm

/-- Forgetting the group sheafification sends each actual zero class to its original sheaf class. -/
@[reassoc] theorem toModulusPicardZeroGroupSheaf_forgetIso :
    Functor.whiskerRight
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)) (forget CommGrpCat.{u + 1}) ≫
      (modulusPicardZeroGroupSheafForgetIso c i).hom =
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardZeroPresheaf c i) :=
  sheafComposeIso_inv_fac (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (modulusPicardZeroGroupPresheaf c i)

end AlgebraicGeometry.GeneralizedJacobian
