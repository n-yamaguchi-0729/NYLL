/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardSheaf
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.Unrigidified

/-!
# Forgetting the modulus and the ordinary relative Picard sheaf

The target first quotients actual line bundles by twists from the base, and then
takes fppf sheafification. Thus the ordinary relative Picard sheaf, used for empty
modulus, is distinguished from naive isomorphism classes of line bundles.

Forgetting a chosen modulus trivialization gives an actual natural transformation
and an induced morphism of fppf sheaves. No surjectivity on rational points or
identification of the kernel is asserted here.
-/

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- Forget the chosen modulus trivialization and pass to the actual relative
line-bundle class, including the quotient by line bundles from the base. -/
def forgetModulusClasses {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i t) →
      RelPicard.Unrigidified.Classes c t :=
  Quotient.lift
    (fun M : RigidifiedLineBundle (modulusBaseChange c i t) =>
      Quot.mk _ (⟨M.L, M.isInvertible⟩ : RelPicard.Unrigidified.LineBundle c t))
    (fun _ _ h => Quot.sound (RelPicard.Unrigidified.baseTwist_of_iso h.some.toIso))

/-- Forgetting the modulus commutes with every change of the test scheme. -/
def forgetModulusPresheaf :
    modulusPicardPresheaf c i ⟶ RelPicard.Unrigidified.presheaf c where
  app T := TypeCat.ofHom (forgetModulusClasses c i T.unop.hom)
  naturality {T T'} s := by
    apply TypeCat.homEquiv.injective
    funext x
    induction x using Quotient.ind with
    | _ M => rfl

/-- The ordinary relative Picard sheaf, formed from line bundles modulo base
twists and fppf sheafification. This is the separate ordinary construction used
when the modulus is empty. -/
def ordinaryRelativePicardSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).obj
    (RelPicard.Unrigidified.presheaf c)

/-- The forgetful morphism from the modulus Picard sheaf to the ordinary relative
Picard sheaf is obtained from the actual forgetful map on classes. -/
def forgetModulusSheaf : modulusPicardSheaf c i ⟶ ordinaryRelativePicardSheaf c :=
  modulusPicardSheafLift
    (forgetModulusPresheaf c i ≫
      toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (RelPicard.Unrigidified.presheaf c))

/-- On actual chosen-rigidified classes, sheaf-level forgetting is the ordinary
relative class of the very same underlying line bundle. -/
@[reassoc] theorem toModulusPicardSheaf_forget :
    toModulusPicardSheaf c i ≫ (forgetModulusSheaf c i).hom =
      forgetModulusPresheaf c i ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (RelPicard.Unrigidified.presheaf c) :=
  toModulusPicardSheaf_lift _

end AlgebraicGeometry.GeneralizedJacobian
