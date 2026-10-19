/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.KernelGroup
import Nyll.JacobianVarieties.Generalized.PoincareProjectionGeometry

/-! # Geometry of the actual projection after choosing a curve section -/

noncomputable section
universe u
open CategoryTheory Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

private theorem projection_property (P : MorphismProperty Scheme.{u})
    (hbc : P.IsStableUnderBaseChange)
    (hP : P (poincareModulusGroupProjection D
      (Pointed.ordinaryRepresentation c ε) hd).hom.hom.hom.left) :
    P (groupProjection c D).hom.hom.hom.left := by
  have : P.RespectsIso := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  let h := Pointed.ordinaryRepresentation c ε
  let a := groupRepresentable c D
  let b : ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy
      (poincareModulusCommGroupScheme D h hd).X :=
    poincareModulusPicardZeroGroupRepresentable D h hd
  let j : ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (ordinaryGroupScheme c).X := ordinaryGroupRepresentable c
  let k : ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙ forget CommGrpCat.{u + 1}).RepresentableBy
      (ordinaryZeroCommGroupScheme h).X := ordinaryZeroGroupSheafRepresentable h
  let eM := a.uniqueUpToIso b
  let eJ := j.uniqueUpToIso k
  have hM {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ (groupScheme c D).X) :
      b.homEquiv (f ≫ eM.hom) = a.homEquiv f := by
    change b.homEquiv (f ≫ b.homEquiv.symm (a.homEquiv (𝟙 _))) = _
    rw [b.homEquiv_comp, Equiv.apply_symm_apply, ← a.homEquiv_comp, Category.comp_id]
  have hJ {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ (ordinaryGroupScheme c).X) :
      k.homEquiv (f ≫ eJ.hom) = j.homEquiv f := by
    change k.homEquiv (f ≫ k.homEquiv.symm (j.homEquiv (𝟙 _))) = _
    rw [k.homEquiv_comp, Equiv.apply_symm_apply, ← j.homEquiv_comp, Category.comp_id]
  have hs : (groupProjection c D).hom.hom.hom ≫ eJ.hom =
      eM.hom ≫ (poincareModulusGroupProjection D h hd).hom.hom.hom := by
    apply k.homEquiv.injective
    have hp := groupProjection_homEquiv c D (𝟙 (groupScheme c D).X)
    have hm := hM (𝟙 (groupScheme c D).X)
    change j.homEquiv (𝟙 (groupScheme c D).X ≫ (groupProjection c D).hom.hom.hom) = _ at hp
    rw [Category.id_comp] at hp hm
    exact (hJ (groupProjection c D).hom.hom.hom).trans
      (hp.trans ((congrArg ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app
        (op (groupScheme c D).X)).hom hm.symm).trans
          (poincareModulusGroupProjection_homEquiv D h hd eM.hom).symm))
  apply (P.cancel_right_of_respectsIso _ eJ.hom.left).mp
  change P (((groupProjection c D).hom.hom.hom ≫ eJ.hom).left)
  rw [hs]
  exact (P.cancel_left_of_respectsIso eM.hom.left _).mpr hP

include ε hd in
/-- The actual arbitrary-field projection has the concrete frame-projection geometry
whenever a section is present; the comparison preserves the classified forgetful map. -/
theorem groupProjection_pointed_geometry :
    IsAffineHom (groupProjection c D).hom.hom.hom.left ∧
    SmoothOfRelativeDimension (d - 1) (groupProjection c D).hom.hom.hom.left ∧
    GeometricallyConnected (groupProjection c D).hom.hom.hom.left :=
  ⟨projection_property c ε D hd (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      (poincareModulusGroupProjection_isAffineHom D (Pointed.ordinaryRepresentation c ε) hd),
    projection_property c ε D hd (@SmoothOfRelativeDimension (d - 1)) inferInstance
      (poincareModulusGroupProjection_smoothOfRelativeDimension D
        (Pointed.ordinaryRepresentation c ε) hd),
    projection_property c ε D hd (@GeometricallyConnected)
      (GeometricallyConnected.eq_geometrically ▸ inferInstance)
      (poincareModulusGroupProjection_geometricallyConnected D
        (Pointed.ordinaryRepresentation c ε) hd)⟩

end AlgebraicGeometry.GeneralizedJacobian
