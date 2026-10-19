/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.AbelianScheme

/-! # The actual trivial group is an abelian scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupSchemes

/-- The identity of the base, with its canonical trivial group law, is an abelian scheme. -/
instance trivial_isAbelianScheme (S : Scheme.{u}) :
    IsAbelianScheme (CommGrp.trivial (Over S)) where
  toSmooth := by
    change Smooth (𝟙 S)
    infer_instance
  toIsProper := by
    change IsProper (𝟙 S)
    infer_instance
  toGeometricallyConnected := by
    change GeometricallyConnected (𝟙 S)
    constructor
    intro K _ y Z a b hb
    have : IsIso b := hb.isIso_snd_of_isIso
    exact b.homeomorph.connectedSpace_iff.mpr inferInstance

end AlgebraicGeometry.GroupSchemes
