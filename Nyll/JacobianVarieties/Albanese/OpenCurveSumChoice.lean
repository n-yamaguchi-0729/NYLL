/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.OpenCurveDivisorSums
import Nyll.JacobianVarieties.Albanese.CorrectedDivisorSums

/-!
# Chosen actual regular divisor sums

The data below are constructed from the proved divisor representer and
descent theorem. Choosing them once for each degree gives regular family
sum maps with the actual finite flat tuple cover available for evaluation.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

variable {K : Type u} [Field K] {C B : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (U : C.Opens)
  {b : B ⟶ Spec (CommRingCat.of K)}
  (G : RelativeGroupLaw K b) (q : SchemeHomOver (U.ι ≫ c) b) (n : ℕ)

/-- Concrete data of a represented divisor sum, including its actual tuple evaluation. -/
structure OpenCurveSum where
  /-- The actual divisor parameter scheme. -/
  Y : Scheme.{u}
  /-- Its structure morphism. -/
  toBase : Y ⟶ Spec (CommRingCat.of K)
  /-- The represented universal divisor. -/
  divisor : RelEffCartierDiv (U.ι ≫ c) n toBase
  /-- The full test-scheme universal property. -/
  universal : divisor.IsUniversal
  /-- The map from ordered tuples. -/
  tupleMap : finFibrePow (U.ι ≫ c) n ⟶ Y
  /-- The tuple map is over the ground field. -/
  tupleMap_toBase : tupleMap ≫ toBase = finFibrePow.toBase (U.ι ≫ c) n
  /-- The descended regular sum morphism. -/
  sum : SchemeHomOver toBase b
  /-- The actual tuple divisor ideal is its pullback. -/
  tuple_ideal : divisor.I.comap (mapOnProdOver (U.ι ≫ c) tupleMap tupleMap_toBase) =
    fibrePowOver.tautIdeal (U.ι ≫ c) n
  /-- The tuple map is finite. -/
  tuple_finite : IsFinite tupleMap
  /-- The tuple map is flat. -/
  tuple_flat : Flat tupleMap
  /-- The tuple map is surjective. -/
  tuple_surjective : Surjective tupleMap
  /-- The sum evaluates to the regular ordered tuple sum. -/
  tuple_sum : tupleMap ≫ sum.1 = (G.finiteSumMap (U.ι ≫ c) q n).1

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  [IsSeparated b] (hc : G.IsCommutative)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ c))

include hc ε in
/-- The data are supplied by actual construction, with no representability or descent input. -/
theorem nonempty_openCurveSum : Nonempty (OpenCurveSum c U G q n) := by
  obtain ⟨Y, y, E, hE, σ, hσ, sum, hI, hfin, hflat, hsurj, hsum, _⟩ :=
    exists_openCurveDivisorSum c U ε.1 ε.2 G hc q n
  exact ⟨⟨Y, y, E, hE, σ, hσ, sum, hI, hfin, hflat, hsurj, hsum⟩⟩

/-- A specified actual regular divisor-sum map in every degree. -/
def chooseOpenCurveSum : OpenCurveSum c U G q n :=
  Classical.choice (nonempty_openCurveSum c U G q n hc ε)

end JacobianVarieties.Albanese
