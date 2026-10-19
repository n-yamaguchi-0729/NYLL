/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GroupProjectionGeometry
import Nyll.SchemeTheory.Morphisms.GeometricallyConnectedDescent

/-! # Geometrically connected fibres of the arbitrary-field forgetting projection -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem connected_of_overPullback {S S' : Scheme.{u}} (s : S' ⟶ S)
    [Surjective s] {X Y : Over S} (m : X ⟶ Y)
    (h : GeometricallyConnected ((Over.pullback s).map m).left) :
    GeometricallyConnected m.left :=
  MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective)
    (overPullback_map_isPullback s m) inferInstance h

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual forgetful homomorphism has geometrically connected fibres over every field. -/
theorem groupProjection_geometricallyConnected :
    GeometricallyConnected (groupProjection c D).hom.hom.hom.left := by
  cases d with
  | zero =>
      let e : (groupScheme c D).X.left ≅ (ordinaryGroupScheme c).X.left :=
        (CommGrp.forget _ ⋙ Over.forget _).mapIso (emptyModulusGroupIso c D)
      change GeometricallyConnected e.hom
      constructor
      intro F _ t Z a b hb
      have : IsIso b := hb.isIso_snd_of_isIso
      exact b.homeomorph.connectedSpace_iff.mpr inferInstance
  | succ n =>
      obtain ⟨x₀, -⟩ := c.surjective (default : Spec (CommRingCat.of K))
      have : Nonempty C := ⟨x₀⟩
      obtain ⟨x, -, hfin⟩ := Scheme.exists_finite_pointResidueAlgebra c
      let a : Algebra K (C.residueField x) := Scheme.pointResidueAlgebra c x
      have : Module.Finite K (C.residueField x) := hfin
      let L := C.residueField x
      let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L) :=
        Scheme.pointResidueSection c x
      let DL := D.changeBaseOfIdentity (specMap K L)
      have hgc := (groupProjection_pointed_geometry (baseChange K c L) ε DL
        (Nat.zero_lt_succ n)).2.2
      have : MorphismProperty.RespectsIso
          (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
        apply MorphismProperty.RespectsIso.of_respects_arrow_iso
        intro f g e
        have hbc : MorphismProperty.IsStableUnderBaseChange
            (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
          GeometricallyConnected.eq_geometrically ▸ inferInstance
        exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
      exact connected_of_overPullback (specMap K L) (groupProjection c D).hom.hom.hom
        (groupProjection_scalarExtension_property c D L (@GeometricallyConnected) hgc)

end AlgebraicGeometry.GeneralizedJacobian
