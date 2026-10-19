/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneRestriction
import Nyll.JacobianVarieties.Generalized.PicardOneIntrinsicAction

/-! # Restriction of whole modulus frames is equivariant for the actual sheaf action -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  [IsClosedImmersion i] [IsClosedImmersion i'] (j : D' ⟶ D) (w : i' = j ≫ i)
  [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The intrinsic tensor action commutes with actual whole-modulus restriction. -/
theorem modulusRestrictionOneSheaf_action
    (T : Over (Spec (CommRingCat.of R)))
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusRestrictionOneSheaf c j w).hom.app (op T)
        (modulusPicardOneIntrinsicAction c i T g x) =
      modulusPicardOneIntrinsicAction c i' T
        (((modulusRestrictionZeroSheaf c j w).hom.app (op T)).hom g)
        ((modulusRestrictionOneSheaf c j w).hom.app (op T) x) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let ηG := toSheafify J (modulusPicardZeroGroupPresheaf c i)
  let ηP := toSheafify J (modulusPicardOnePresheaf c i)
  let ηG' := toSheafify J (modulusPicardZeroGroupPresheaf c i')
  let ηP' := toSheafify J (modulusPicardOnePresheaf c i')
  let rG := modulusRestrictionZeroSheaf c j w
  let rP := modulusRestrictionOneSheaf c j w
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 (modulusPicardOneSheaf c i').2).isSeparated _
    (J.intersection_covering (Presheaf.imageSieve_mem J ηG g)
      (Presheaf.imageSieve_mem J ηP x))).ext
  rintro Y f ⟨⟨g₀, hg⟩, ⟨x₀, hx⟩⟩
  change (ηG.app (op Y)).hom g₀ = (modulusPicardZeroGroupSheaf c i).obj.map f.op g at hg
  change ηP.app (op Y) x₀ = (modulusPicardOneSheaf c i).obj.map f.op x at hx
  rw [← rP.hom.naturality_apply f.op, modulusPicardOneIntrinsicAction_naturality,
    modulusPicardOneIntrinsicAction_naturality, ← rG.hom.naturality_apply f.op,
    ← rP.hom.naturality_apply f.op, ← hg, ← hx]
  have hp (y : ModulusPicardOneClasses c i Y) :
      rP.hom.app (op Y) (ηP.app (op Y) y) =
        ηP'.app (op Y) (modulusRestrictionOneClasses c j w Y y) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_modulusRestrictionOneSheaf c j w) (op Y)) y
  have hgp : (rG.hom.app (op Y)).hom ((ηG.app (op Y)).hom g₀) =
      (ηG'.app (op Y)).hom (modulusRestrictionZeroClasses c j w Y g₀) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_modulusRestrictionZeroSheaf c j w) (op Y)) g₀
  exact (congrArg (rP.hom.app (op Y))
    (modulusPicardOneIntrinsicAction_actual c i Y g₀ x₀)).trans
      ((hp (modulusPicardOneAction c i Y g₀ x₀)).trans
        ((congrArg (ηP'.app (op Y))
          (modulusRestrictionOneClasses_action c j w Y g₀ x₀)).trans
            ((modulusPicardOneIntrinsicAction_actual c i' Y
              (modulusRestrictionZeroClasses c j w Y g₀)
              (modulusRestrictionOneClasses c j w Y x₀)).symm.trans
                (congrArg₂ (modulusPicardOneIntrinsicAction c i' Y) hgp.symm (hp x₀).symm))))

end AlgebraicGeometry.GeneralizedJacobian
