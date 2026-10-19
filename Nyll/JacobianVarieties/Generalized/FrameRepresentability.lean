/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameBaseChange
import Nyll.JacobianVarieties.Generalized.FrameCover
import Nyll.JacobianVarieties.Generalized.ModulusUnitRelativeRepresentation
import Nyll.SchemeTheory.WeilRestriction.GluedRepresentable

/-!
# Representing the scalar frames of an invertible family

The actual frame cover supplies local trivializations. Their scalar-frame
sheaves are represented by pullbacks of the modulus-unit representer.
The intrinsic frame sheaf supplies the transition maps, so gluing retains
the changes of frame rather than replacing the family by a product.
For a finite positive-rank scheme over a field the unit representer is
supplied by the concrete projective norm open, without an extra hypothesis.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Module Opposite
open AlgebraicGeometry.Scheme.Modules SchemeTheory.WeilRestriction
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S) [IsFinite q]
  {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)

/-- The chosen local frame transferred to the pullback used for base change. -/
def frameCoverPulledFrame (U : (frameCover q hM).I₀) :
    (Scheme.Modules.pullback (pullback.fst q ((frameCover q hM).f U))).obj M ≅
      𝟙_ (pullback q ((frameCover q hM).f U)).Modules :=
  frameMap M
    (T := Over.mk (pullback.snd ((frameCover q hM).f U) q))
    (T' := Over.mk (pullback.fst q ((frameCover q hM).f U)))
    (Over.homMk (pullbackSymmetry q ((frameCover q hM).f U)).hom
      (pullbackSymmetry_hom_comp_snd q ((frameCover q hM).f U)))
    (frameCoverFrame q hM U)

variable {W : Over S} (h : (modulusUnitQuotientSheaf q).obj.RepresentableBy W)

/-- Each actual restriction of the frame sheaf has a concrete relative representer. -/
def frameLocalRepresentable (U : (frameCover q hM).I₀) :
    ((Over.map ((frameCover q hM).f U)).op ⋙ (scalarFrameSheaf q M).obj).RepresentableBy
      ((Over.pullback ((frameCover q hM).f U)).obj W) :=
  (scalarFrameRepresentableBaseChange q ((frameCover q hM).f U) h
    (frameCoverPulledFrame q hM U)).ofIso
      ((sheafToPresheaf (Scheme.fppfTopology.over ((frameCover q hM).X U))
        (Type (u + 1))).mapIso
          (scalarFrameSheafBaseChangeIso q ((frameCover q hM).f U) M).symm)

omit [IsFinite q] in
/-- The actual fppf frame sheaf satisfies Zariski descent as well. -/
theorem scalarFrameSheaf_isZariskiSheaf :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (scalarFrameSheaf q M).obj := by
  apply Presheaf.IsSheaf.of_le _ (scalarFrameSheaf q M).property
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ hR

/-- The scheme obtained by gluing the actual local scalar-frame models. -/
def scalarFrameRepresenter : Over S :=
  gluedLocalRepresenter (scalarFrameSheaf q M).obj (frameCover q hM)
    (fun U => (Over.pullback ((frameCover q hM).f U)).obj W)
    (frameLocalRepresentable q hM h)

/-- The glued scheme represents the intrinsic scalar-frame sheaf. -/
def scalarFrameRepresentable :
    (scalarFrameSheaf q M).obj.RepresentableBy (scalarFrameRepresenter q hM h) :=
  gluedLocalRepresentable.{u, u, u + 1} (scalarFrameSheaf q M).obj (frameCover q hM)
    (fun U => (Over.pullback ((frameCover q hM).f U)).obj W)
    (frameLocalRepresentable q hM h) (scalarFrameSheaf_isZariskiSheaf q)

variable {K : Type u} [Field K] {D : Scheme.{u}}
  (q₀ : D ⟶ Spec (CommRingCat.of K)) [IsFinite q₀]
  {n : ℕ} (b : Basis (Fin (n + 1)) K (coordinateAlgebra q₀))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
  {L : (pullback q₀ t).Modules} (hL : Scheme.Modules.IsInvertible L)

/-- A finite field modulus supplies every local model of an arbitrary invertible family. -/
def finiteScalarFrameRepresenter : Over T :=
  scalarFrameRepresenter (pullback.snd q₀ t) hL
    (finiteModulusUnitRelativeRepresentable q₀ b t)

/-- The concrete glued scheme represents the actual family, without a global frame. -/
def finiteScalarFrameRepresentable :
    (scalarFrameSheaf (pullback.snd q₀ t) L).obj.RepresentableBy
      (finiteScalarFrameRepresenter q₀ b t hL) :=
  scalarFrameRepresentable (pullback.snd q₀ t) hL
    (finiteModulusUnitRelativeRepresentable q₀ b t)

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
