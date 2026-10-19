/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedProjectionGeometry
import Nyll.JacobianVarieties.Generalized.ProjectionScalarExtension
import Nyll.SchemeTheory.Morphisms.OverPullbackDescent
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothDescendsAlongSurjectiveInfFlatInfQuasiCompact
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint

/-! # Smoothness of the actual forgetting projection over an arbitrary field -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The proved projection square transfers any isomorphism-invariant property
from the extended curve to the literal pullback of the original arrow. -/
theorem groupProjection_scalarExtension_property
    (L : Type u) [Field L] [Algebra K L]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hp : P (groupProjection (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L))).hom.hom.hom.left) :
    P ((Over.pullback (specMap K L)).map (groupProjection c D).hom.hom.hom).left := by
  let eM : (groupScalarExtension c D L).X.left ≅
      (groupScheme (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))).X.left :=
    (CommGrp.forget _ ⋙ Over.forget _).mapIso (groupScalarExtensionIso c D L)
  let eJ : (ordinaryGroupScalarExtension c L).X.left ≅
      (ordinaryGroupScheme (baseChange K c L)).X.left :=
    (CommGrp.forget _ ⋙ Over.forget _).mapIso (ordinaryGroupScalarExtensionIso c L)
  have : IsIso eM.hom := eM.isIso_hom
  have : IsIso eJ.hom := eJ.isIso_hom
  let p := (groupProjectionScalarExtension c D L).hom.hom.hom.left
  let p' := (groupProjection (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L))).hom.hom.hom.left
  have hs : eM.hom ≫ p' = p ≫ eJ.hom :=
    congrArg (fun f => f.hom.hom.hom.left) (groupProjection_scalarExtension_square c D L)
  have hpull : p =
      ((Over.pullback (specMap K L)).map (groupProjection c D).hom.hom.hom).left :=
    congrArg Over.Hom.left (groupProjectionScalarExtension_eq c D L)
  rw [← hpull]
  apply (P.cancel_right_of_respectsIso p eJ.hom).mp
  rw [← hs]
  exact (P.cancel_left_of_respectsIso eM.hom p').mpr hp

/-- No rational point on the original curve is required for smoothness of forgetting. -/
theorem groupProjection_smooth : Smooth (groupProjection c D).hom.hom.hom.left := by
  cases d with
  | zero =>
      let e : (groupScheme c D).X.left ≅ (ordinaryGroupScheme c).X.left :=
        (CommGrp.forget _ ⋙ Over.forget _).mapIso (emptyModulusGroupIso c D)
      change Smooth e.hom
      infer_instance
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
      have hd : 0 < n + 1 := Nat.zero_lt_succ n
      have hsm : Smooth (groupProjection (baseChange K c L) DL).hom.hom.hom.left := by
        have : SmoothOfRelativeDimension n
            (groupProjection (baseChange K c L) DL).hom.hom.hom.left :=
          (groupProjection_pointed_geometry (baseChange K c L) ε DL hd).2.1
        exact SmoothOfRelativeDimension.smooth n _
      have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) := by
        apply MorphismProperty.RespectsIso.of_respects_arrow_iso
        intro f g e
        exact smooth_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
      have : MorphismProperty.DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
          (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
        Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact
      exact property_of_overPullback_map (specMap K L) (groupProjection c D).hom.hom.hom
        (@Smooth) (groupProjection_scalarExtension_property c D L (@Smooth) hsm)

end AlgebraicGeometry.GeneralizedJacobian
