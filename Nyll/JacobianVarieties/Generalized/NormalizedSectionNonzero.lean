/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.NormalizedSectionDivisor
import Mathlib.AlgebraicGeometry.Properties

/-! # Nonvanishing of a section normalized on a nonempty modulus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

/-- A section restricting to one on a nonempty modulus cannot be zero. -/
theorem normalizedSection_ne_zero {X D : Scheme.{u}} {i : D ⟶ X} [Nonempty D]
    (M : RigidifiedLineBundle i) (s : 𝟙_ X.Modules ⟶ M.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules)) : s ≠ 0 := by
  intro hzero
  have hp : pullbackSection i s = 0 :=
    (congrArg (fun t => (pullbackUnitIso i).inv ≫ (Scheme.Modules.pullback i).map t)
      hzero).trans
      ((congrArg ((pullbackUnitIso i).inv ≫ ·)
        (CategoryTheory.Functor.map_zero (Scheme.Modules.pullback i) _ _)).trans comp_zero)
  have h01 : (0 : 𝟙_ D.Modules ⟶ 𝟙_ D.Modules) = 𝟙 (𝟙_ D.Modules) := by
    simpa only [hp, zero_comp] using hs
  have : Nonempty (⊤ : D.Opens) := ⟨⟨Classical.arbitrary D, trivial⟩⟩
  have h := congrArg
    (fun f : 𝟙_ D.Modules ⟶ 𝟙_ D.Modules =>
      ofUnitSection ⊤ (f.app ⊤ (toUnitSection ⊤ 1))) h01
  exact (zero_ne_one : (0 : Γ(D, ⊤)) ≠ 1) h

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
