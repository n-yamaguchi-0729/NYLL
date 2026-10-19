/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedGroupComparison

/-!
# Forgetting the modulus as a morphism of Picard-zero group sheaves

The actual forgetful map preserves rigidified tensor products. Normalization
along an existing curve section gives the ordinary pointed group presheaf,
using the already proved multiplicative normalization equivalence.
-/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- Forgetting the chosen modulus trivialization preserves the actual tensor group law. -/
def forgetModulusZeroGroupPresheaf :
    modulusPicardZeroGroupPresheaf c i ⟶ Unrigidified.zeroCommGrpPresheaf c where
  app T :=
    let : CommGroup ((Unrigidified.zeroPresheaf c).obj T) := Unrigidified.zeroCommGroup T
    CommGrpCat.ofHom (MonoidHom.mk' ((forgetModulusZeroPresheaf c i).app T) (by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      induction x using Quotient.ind
      induction y using Quotient.ind
      rfl))
  naturality {T T'} s := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom ((forgetModulusZeroPresheaf c i).naturality s) x

/-- The ordinary unrigidified Picard-zero group sheaf. -/
def ordinaryRelativePicardZeroGroupSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).obj (Unrigidified.zeroCommGrpPresheaf c)

/-- The group structure has exactly the previously constructed ordinary underlying sheaf. -/
def ordinaryRelativePicardZeroGroupSheafForgetIso :
    (ordinaryRelativePicardZeroGroupSheaf c).obj ⋙ forget CommGrpCat.{u + 1} ≅
      (ordinaryRelativePicardZeroSheaf c).obj :=
  (sheafifyComposeIso (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (forget CommGrpCat.{u + 1}) (Unrigidified.zeroCommGrpPresheaf c)).symm

/-- Sheafification of the actual tensor-preserving forgetful map. -/
def forgetModulusZeroGroupSheaf :
    modulusPicardZeroGroupSheaf c i ⟶ ordinaryRelativePicardZeroGroupSheaf c :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).map (forgetModulusZeroGroupPresheaf c i)

/-- Forgetting the group law commutes with the actual modulus-forgetting sheaf map. -/
@[reassoc] theorem forgetModulusZeroGroupSheaf_forgetIso :
    Functor.whiskerRight (forgetModulusZeroGroupSheaf c i).hom
        (forget CommGrpCat.{u + 1}) ≫
      (ordinaryRelativePicardZeroGroupSheafForgetIso c).hom =
        (modulusPicardZeroGroupSheafForgetIso c i).hom ≫
          (forgetModulusZeroSheaf c i).hom := by
  exact congrArg (fun f => f.hom)
    ((sheafComposeNatIso (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (forget CommGrpCat.{u + 1})
      (sheafificationAdjunction (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        CommGrpCat.{u + 1})
      (sheafificationAdjunction (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Type (u + 1)))).inv.naturality (forgetModulusZeroGroupPresheaf c i))

variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- Normalization at the section is a natural isomorphism of ordinary zero group presheaves. -/
def ordinaryZeroGroupPresheafIso :
    Unrigidified.zeroCommGrpPresheaf c ≅
      relSubPicCommGrpPresheaf c ε (algEquivZeroGroupCut c ε) :=
  NatIso.ofComponents (fun T => (Unrigidified.normalizeZeroMulEquiv ε T).toCommGrpIso)
    (fun s => by
      refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      exact ConcreteCategory.congr_hom ((Unrigidified.zeroPresheafIso ε).hom.naturality s) x)

end AlgebraicGeometry.GeneralizedJacobian
