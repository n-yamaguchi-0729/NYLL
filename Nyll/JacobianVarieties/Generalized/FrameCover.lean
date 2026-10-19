/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameCoordinates
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.InvertiblePullbackPreimageIsoTensorUnit
import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# A genuine directed open cover carrying modulus frames

An invertible module on a finite scheme over the parameter scheme becomes
trivial over inverse images of an open cover of the parameter scheme. We
transfer the supplied trivializations to the actual categorical pullbacks
used in the frame functor. All opens with such a frame form a small basis;
the resulting locally directed cover is suitable for scheme gluing.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S) (M : Y.Modules)

/-- Transfer an actual frame on the inverse-image open to the chosen pullback. -/
def frameOnPullbackOpen (U : S.Opens)
    (e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅
      𝟙_ (q ⁻¹ᵁ U).toScheme.Modules) :
    (relativeFramePresheaf q M).obj (op (Over.mk U.ι)) := by
  let g : Over.mk (pullback.snd U.ι q) ⟶ Over.mk (q ⁻¹ᵁ U).ι :=
    Over.homMk (isPullback_morphismRestrict q U).isoPullback.inv
      (isPullback_morphismRestrict q U).isoPullback_inv_snd
  exact frameMap M g e

variable {M}

/-- Finiteness supplies actual frames near every parameter point. -/
theorem exists_frameOpen [IsFinite q] (hM : Scheme.Modules.IsInvertible M) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((relativeFramePresheaf q M).obj (op (Over.mk U.ι))) := by
  obtain ⟨U, hs, ⟨e⟩⟩ :=
    hM.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite q s
  exact ⟨U, hs, ⟨frameOnPullbackOpen q M U e⟩⟩

/-- A smaller parameter open retains an actual frame by functorial restriction. -/
def restrictOpenFrame {U V : S.Opens} (hUV : U ≤ V)
    (e : (relativeFramePresheaf q M).obj (op (Over.mk V.ι))) :
    (relativeFramePresheaf q M).obj (op (Over.mk U.ι)) :=
  (relativeFramePresheaf q M).map
    (Over.homMk (S.homOfLE hUV) (S.homOfLE_ι hUV)).op e

/-- The small family of opens on which the actual modulus family has a frame. -/
abbrev FrameOpen := {U : S.Opens //
  Nonempty ((relativeFramePresheaf q M).obj (op (Over.mk U.ι)))}

theorem frameOpens_isBasis [IsFinite q] (hM : Scheme.Modules.IsInvertible M) :
    TopologicalSpace.Opens.IsBasis (Set.range fun U : FrameOpen q (M := M) => U.1) := by
  apply TopologicalSpace.Opens.isBasis_iff_nbhd.mpr
  intro U s hs
  obtain ⟨V, hVs, ⟨e⟩⟩ := exists_frameOpen q hM s
  refine ⟨U ⊓ V, ?_, ⟨hs, hVs⟩, inf_le_left⟩
  exact ⟨⟨U ⊓ V, ⟨restrictOpenFrame q inf_le_right e⟩⟩, rfl⟩

/-- The actual trivializing opens cover every parameter point. -/
theorem frameOpens_isOpenCover [IsFinite q] (hM : Scheme.Modules.IsInvertible M) :
    TopologicalSpace.IsOpenCover (fun U : FrameOpen q (M := M) => U.1) := by
  apply TopologicalSpace.IsOpenCover.mk
  apply le_antisymm le_top
  intro s _
  obtain ⟨U, hs, hU⟩ := exists_frameOpen q hM s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hs⟩

/-- A concrete open cover, indexed by all trivializing parameter opens. -/
def frameCover [IsFinite q] (hM : Scheme.Modules.IsInvertible M) : S.OpenCover :=
  S.openCoverOfIsOpenCover (fun U : FrameOpen q (M := M) => U.1)
    (frameOpens_isOpenCover q hM)

instance frameCoverPreorder [IsFinite q] (hM : Scheme.Modules.IsInvertible M) :
    Preorder (frameCover q hM).I₀ :=
  inferInstanceAs (Preorder (FrameOpen q (M := M)))

/-- The cover has actual transition maps and covering intersections. -/
instance frameCoverLocallyDirected [IsFinite q] (hM : Scheme.Modules.IsInvertible M) :
    (frameCover q hM).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
    (by
      intro U V
      change U.1 ≤ V.1 ↔ U.1.ι.opensRange ≤ V.1.ι.opensRange
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])
    (by
      change TopologicalSpace.Opens.IsBasis
        (Set.range fun U : FrameOpen q (M := M) => U.1.ι.opensRange)
      simp only [Scheme.Opens.opensRange_ι]
      exact frameOpens_isBasis q hM)

/-- Each chart carries an actual chosen trivialization of the restricted family. -/
def frameCoverFrame [IsFinite q] (hM : Scheme.Modules.IsInvertible M)
    (U : (frameCover q hM).I₀) :
    (relativeFramePresheaf q M).obj (op (Over.mk ((frameCover q hM).f U))) :=
  U.2.some

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
