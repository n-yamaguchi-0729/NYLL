/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameRepresentability
import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitDimension
import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitGeometric

/-! Geometry of the actual glued scalar-frame scheme over its parameter scheme. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Module
open SchemeTheory.WeilRestriction SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S) [IsFinite q]
  {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
  {W : Over S} (h : (modulusUnitQuotientSheaf q).obj.RepresentableBy W)

/-- Target-local properties stable under base change pass to the actual frame scheme. -/
theorem scalarFrameRepresenter_property (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange] (hW : P W.hom) :
    P (scalarFrameRepresenter q hM h).hom := by
  apply IsZariskiLocalAtTarget.of_openCover (frameCover q hM)
  intro U
  let e : (Over.pullback ((frameCover q hM).f U)).obj W ≅
      (Over.pullback ((frameCover q hM).f U)).obj (scalarFrameRepresenter q hM h) :=
    gluedLocalRepresenterPullbackIso (scalarFrameSheaf q M).obj (frameCover q hM)
    (fun V => (Over.pullback ((frameCover q hM).f V)).obj W)
    (frameLocalRepresentable q hM h) U
  change P ((Over.pullback ((frameCover q hM).f U)).obj
    (scalarFrameRepresenter q hM h)).hom
  apply (P.cancel_left_of_respectsIso e.hom.left _).mp
  exact (congrArg (fun k : ((Over.pullback ((frameCover q hM).f U)).obj W).left ⟶
    (frameCover q hM).X U => P k) e.hom.w).mpr (P.pullback_snd _ _ hW)

variable {K : Type u} [Field K] {D : Scheme.{u}}
  (q₀ : D ⟶ Spec (CommRingCat.of K)) [IsFinite q₀]
  {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q₀))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
  {L : (pullback q₀ t).Modules} (hL : Scheme.Modules.IsInvertible L)

/-- The frame quotient is affine over the parameter scheme, without a global frame. -/
theorem finiteScalarFrameRepresenter_isAffineHom :
    IsAffineHom (finiteScalarFrameRepresenter q₀ b t hL).hom := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine).1
  apply scalarFrameRepresenter_property (pullback.snd q₀ t) hL
    (finiteModulusUnitRelativeRepresentable q₀ b t) (@IsAffineHom)
  change IsAffineHom (pullback.snd (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  apply MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  rw [ScalarQuotientSchemePresheaf.representingObject_hom]
  exact AlgebraicGeometry.isAffineHom_of_isAffine (f := ProjectiveUnitOpen.toBase b)

/-- The full rank of the finite modulus gives the relative dimension of its frame quotient. -/
theorem finiteScalarFrameRepresenter_smoothOfRelativeDimension :
    SmoothOfRelativeDimension n (finiteScalarFrameRepresenter q₀ b t hL).hom := by
  have : IsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp
      (HasRingHomProperty.HasAffineProperty (@SmoothOfRelativeDimension n :
        MorphismProperty Scheme.{u})
        (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))).1
  apply scalarFrameRepresenter_property (pullback.snd q₀ t) hL
    (finiteModulusUnitRelativeRepresentable q₀ b t) (@SmoothOfRelativeDimension n)
  change SmoothOfRelativeDimension n
    (pullback.snd (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  apply MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  rw [ScalarQuotientSchemePresheaf.representingObject_hom]
  exact ProjectiveUnitOpen.smoothOfRelativeDimension_toBase b

/-- The same glued frame quotient has geometrically connected fibres. -/
theorem finiteScalarFrameRepresenter_geometricallyConnected :
    GeometricallyConnected (finiteScalarFrameRepresenter q₀ b t hL).hom := by
  have : IsZariskiLocalAtTarget (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  apply scalarFrameRepresenter_property (pullback.snd q₀ t) hL
    (finiteModulusUnitRelativeRepresentable q₀ b t) (@GeometricallyConnected)
  change GeometricallyConnected
    (pullback.snd (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  apply MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@GeometricallyConnected : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback (ScalarQuotientSchemePresheaf.representingObject b).hom t)
  rw [ScalarQuotientSchemePresheaf.representingObject_hom]
  exact ProjectiveUnitOpen.geometricallyConnected_toBase b

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
