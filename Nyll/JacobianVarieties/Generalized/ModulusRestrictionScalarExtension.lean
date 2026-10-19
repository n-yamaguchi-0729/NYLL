/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMap
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionNaturality

/-! # Restriction of actual rigidifications commutes with scalar extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i) (R' : Type u) [CommRing R'] [Algebra R R']

/-- The actual pullback of a morphism of full moduli. -/
def modulusRestrictionScalarMap :
    pullback (i' ≫ c) (specMap R R') ⟶ pullback (i ≫ c) (specMap R R') :=
  modulusRestrictionPullback c j w (specMap R R')

/-- Its inclusion square commutes with the inclusions into the scalar-extended curve. -/
theorem modulusRestrictionScalarMap_square :
    modulusBaseChange c i' (specMap R R') =
      modulusRestrictionScalarMap c j w R' ≫ modulusBaseChange c i (specMap R R') :=
  (Category.comp_id _).symm.trans (modulusRestrictionPullback_square c j w (specMap R R'))

/-- The full iterated-pullback isomorphism respects restriction of the modulus. -/
theorem modulusRestrictionScalarMap_hom_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) :
    modulusRestrictionPullback (baseChange R c R') (modulusRestrictionScalarMap c j w R')
        (modulusRestrictionScalarMap_square c j w R') t ≫
      (modulusScalarExtensionIso c i R' t).hom =
    (modulusScalarExtensionIso c i' R' t).hom ≫
      modulusRestrictionPullback c j w (t ≫ specMap R R') := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modulusScalarExtensionIso_hom_fst,
      modulusScalarExtensionIso_hom_fst_assoc, modulusRestrictionPullback,
      modulusRestrictionScalarMap, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, modulusScalarExtensionIso_hom_snd,
      modulusRestrictionPullback, pullback.lift_snd]

/-- The inverse comparison has the same actual restriction square. -/
theorem modulusRestrictionScalarMap_inv_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) :
    (modulusScalarExtensionIso c i' R' t).inv ≫
      modulusRestrictionPullback (baseChange R c R') (modulusRestrictionScalarMap c j w R')
        (modulusRestrictionScalarMap_square c j w R') t =
    modulusRestrictionPullback c j w (t ≫ specMap R R') ≫
      (modulusScalarExtensionIso c i R' t).inv := by
  apply (cancel_mono (modulusScalarExtensionIso c i R' t).hom).mp
  rw [Category.assoc, modulusRestrictionScalarMap_hom_square,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The existing actual scalar-extension class comparison preserves modulus restriction. -/
theorem scalarExtensionClassesEquiv_restriction {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R'))
    (x : RigidifiedLineBundle.Classes
      (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t)) :
    scalarExtensionClassesEquiv c i' R' t
      (modulusRestrictionClasses (baseChange R c R') (modulusRestrictionScalarMap c j w R')
        (modulusRestrictionScalarMap_square c j w R') t x) =
      modulusRestrictionClasses c j w (t ≫ specMap R R')
        (scalarExtensionClassesEquiv c i R' t x) := by
  change RigidifiedLineBundle.classesPullback (κ c R' t).inv
      (modulusScalarExtensionIso c i' R' t).inv
      (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i' R' t))
      (RigidifiedLineBundle.classesPullback (𝟙 _)
        (modulusRestrictionPullback (baseChange R c R') (modulusRestrictionScalarMap c j w R')
          (modulusRestrictionScalarMap_square c j w R') t) _ x) =
    RigidifiedLineBundle.classesPullback (𝟙 _)
      (modulusRestrictionPullback c j w (t ≫ specMap R R')) _
      (RigidifiedLineBundle.classesPullback (κ c R' t).inv
        (modulusScalarExtensionIso c i R' t).inv
        (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i R' t)) x)
  rw [RigidifiedLineBundle.classesPullback_comp, RigidifiedLineBundle.classesPullback_comp]
  simp only [Category.id_comp, Category.comp_id, modulusRestrictionScalarMap_inv_square]

end AlgebraicGeometry.GeneralizedJacobian
