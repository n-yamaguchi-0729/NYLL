/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorFrameTrivialization
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sets.Opens

/-!
# Quasicoherence and finite type after an actual invertible twist

The original local trivializations of an invertible sheaf give frames,
and their actual tensor powers trivialize every nonnegative twist. The
native tensor-section isomorphisms identify the twisted sheaf with the
original sheaf on those slice sites. Locality then transports actual
quasicoherent presentations and finite local generating families.

No separate quasicoherence or flatness assumption on the invertible
sheaf, and no Noetherian hypothesis on the scheme, is needed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules} (M : X.Modules)

/-- Actual invertible tensor powers preserve the original quasicoherent local presentations. -/
theorem IsInvertible.isQuasicoherent_tensorPow (hL : IsInvertible L)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] (d : ℕ) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (tensor (X := X) M (L.tensorPow d)) := by
  obtain ⟨U, s, hs, hcover⟩ := hL.exists_frame_cover
  have hlocal : ∀ x : X,
      SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf.over (U x))
        ((tensor (X := X) M (L.tensorPow d)).over (U x)) :=
    fun x => IsFrameOn.isQuasicoherent_tensor_over M
      ((hs x).tensorPowSection_monoidalV2 d) le_rfl
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    (R := X.ringCatSheaf) (tensor (X := X) M (L.tensorPow d)) U
    ((Opens.coversTop_iff X U).mpr hcover)

/-- Actual invertible tensor powers preserve the original finite local generating families. -/
theorem IsInvertible.isFiniteType_tensorPow (hL : IsInvertible L)
    [SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M] (d : ℕ) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf)
      (tensor (X := X) M (L.tensorPow d)) := by
  obtain ⟨U, s, hs, hcover⟩ := hL.exists_frame_cover
  apply SheafOfModules.IsFiniteType.of_coversTop
    (R := X.ringCatSheaf) (tensor (X := X) M (L.tensorPow d)) U
    ((Opens.coversTop_iff X U).mpr hcover)
  intro x
  exact IsFrameOn.isFiniteType_tensor_over M
    ((hs x).tensorPowSection_monoidalV2 d) le_rfl

end AlgebraicGeometry.Scheme.Modules
