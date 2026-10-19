/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SndApplyEqNotMemSupport

/-! # The open complement of an actual relative modulus is nonempty -/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- A finite effective modulus misses an actual point of the smooth curve. -/
theorem modulusComplement_nonempty : Nonempty (modulusComplement (modulusCurveMap D)) := by
  obtain ⟨x, -, hx⟩ := RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support c
    (𝟙 (Spec (CommRingCat.of K))) D (default : Spec (CommRingCat.of K))
  refine ⟨⟨pullback.fst c (𝟙 (Spec (CommRingCat.of K))) x, ?_⟩⟩
  change pullback.fst c (𝟙 (Spec (CommRingCat.of K))) x ∉ (modulusCurveMap D).ker.support
  intro hmem
  have hs : ((modulusCurveMap D).ker.support : Set C) =
      Set.range (modulusCurveMap D) :=
    (Scheme.Hom.support_ker (modulusCurveMap D)).trans
      (modulusCurveMap D).isClosedEmbedding.isClosed_range.closure_eq
  have hrange : pullback.fst c (𝟙 (Spec (CommRingCat.of K))) x ∈
      Set.range (modulusCurveMap D) :=
    Eq.mp (congrArg (fun S : Set C =>
      pullback.fst c (𝟙 (Spec (CommRingCat.of K))) x ∈ S) hs) hmem
  obtain ⟨y, hy⟩ := hrange
  apply hx
  have hi : D.I.subschemeι y = x :=
    (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))).isClosedEmbedding.injective hy
  have hr : x ∈ Set.range D.I.subschemeι := ⟨y, hi⟩
  exact D.I.range_subschemeι.le hr

/-- Over an algebraically closed field the actual nonempty complement has a
rational point, constructed from a closed point of this open subscheme. -/
theorem modulusComplement_point [IsAlgClosed K] :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) := by
  let U := modulusComplement (modulusCurveMap D)
  let u : U.toScheme ⟶ Spec (CommRingCat.of K) := U.ι ≫ c
  have : Nonempty U := modulusComplement_nonempty c D
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace u
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U).Nonempty) isClosed_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint u x hx) (pointOfClosedPoint_comp u x hx)⟩

/-- A degree-zero modulus can be enlarged to an actual rational reduced
point, whose complement still has a rational point. Both points are constructed. -/
theorem exists_degreeOneModulus_with_point [IsAlgClosed K]
    (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) :
    ∃ E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))),
      E.I ≤ D₀.I ∧
        Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
          Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c)) := by
  obtain ⟨δ⟩ := modulusComplement_point c D₀
  let E : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))) :=
    RelEffCartierDiv.ofPoint c
      (δ.left ≫ (modulusComplement (modulusCurveMap D₀)).ι)
      ((Category.assoc _ _ _).trans (Over.w δ))
  refine ⟨E, ?_, modulusComplement_point c E⟩
  rw [D₀.I_eq_top_of_degree_zero]
  exact le_top

end AlgebraicGeometry.GeneralizedJacobian
