/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelTwists
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionPushforwardUnit
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Iso

/-!
# Original quotient units on the finite étale cover tower

Each constructed cover module is the actual direct image of its
module on the original closed level. Consequently its unit for
restriction back to that level is invertible. The same holds for
its quasicoherent twists by the original projection formula.

A morphism to a cover module that becomes invertible on its level
therefore constructs an isomorphism from the original pullback
quotient, and composition with the original unit recovers that morphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The original cover module is unchanged by its original
pullback quotient on its own closed level. -/
theorem isIso_moduleSheaf_levelUnit (n : ℕ) :
    IsIso (levelPullbackUnit f I (moduleSheaf f I V n) n) :=
  isIso_pullbackUnit_of_iso_pushforward
    (Limits.pullback.fst f (baseInclusion I n)) (moduleSheaf f I V n)
    (coverLevelModule f I V n) (moduleSheafLevelIso f I V n)

/-- The quotient unit also preserves the original quasicoherent
twist of the cover module at its own level. -/
theorem isIso_moduleSheaf_twisted_levelUnit (L : X.Modules) [L.IsQuasicoherent] (n : ℕ) :
    IsIso (levelPullbackUnit f I (moduleSheaf f I V n ⊗ L) n) :=
  isIso_pullbackUnit_of_iso_pushforward
    (Limits.pullback.fst f (baseInclusion I n)) (moduleSheaf f I V n ⊗ L)
    (coverLevelTwistedModule f I V L n) (moduleSheafTwistedLevelIso f I V L n)

variable (M : X.Modules) (n : ℕ) (σ : M ⟶ moduleSheaf f I V n)
  [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).map σ)]

/-- An actual isomorphism after pullback identifies the original
module quotient with the original finite étale cover module. -/
def moduleSheafLevelQuotientIso :
    levelPullbackModule f I M n ≅ moduleSheaf f I V n := by
  have : IsIso ((pullbackPushforwardAdjunction
      (Limits.pullback.fst f (baseInclusion I n))).unit.app (moduleSheaf f I V n)) :=
    isIso_moduleSheaf_levelUnit f I V n
  exact pullbackQuotientComparisonIso (Limits.pullback.fst f (baseInclusion I n)) σ

/-- This comparison retains the supplied original map after
composition with the original quotient unit. -/
theorem levelUnit_moduleSheafLevelQuotientIso_hom :
    levelPullbackUnit f I M n ≫ (moduleSheafLevelQuotientIso f I V M n σ).hom = σ := by
  have : IsIso ((pullbackPushforwardAdjunction
      (Limits.pullback.fst f (baseInclusion I n))).unit.app (moduleSheaf f I V n)) :=
    isIso_moduleSheaf_levelUnit f I V n
  exact unit_pullbackQuotientComparisonIso_hom
    (Limits.pullback.fst f (baseInclusion I n)) σ

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
