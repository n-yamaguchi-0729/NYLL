/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethMap
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Actual Künneth edge splitting for smooth proper integral curves

The genuine curve model on each original scheme supplies an actual
rational point over the algebraically closed field. The corresponding
point sections therefore split the two original product-cohomology edge
images, without points or curve-model comparisons as extra hypotheses.
The original middle Künneth image lies in the kernel of this retraction.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

variable (K : Type) [Field K] [IsAlgClosed K]
  {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  [IsProper f] [SmoothOfRelativeDimension 1 f]
  [IsProper g] [SmoothOfRelativeDimension 1 g]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual edge retraction on the original product cohomology.
Its points come from the actual models of the original curves. -/
def rationalEllAdicProductEdgeRetraction (i : ℕ) :
    rationalEllAdicCohomology ℓ (pullback f g) i →ₗ[ℚ_[ℓ]]
      (rationalEllAdicCohomology ℓ X i × rationalEllAdicCohomology ℓ Y i) :=
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  let pX := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve f).nonempty_rationalPoint
  let : Algebra K Y.functionField := (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let pY := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve g).nonempty_rationalPoint
  rationalEllAdicEdgeRetraction K ℓ f g pX.1 pX.2 pY.1 pY.2 i

/-- Actual rational points supplied by the curves give a left inverse
to the original positive-degree edge map, with no auxiliary point input. -/
theorem rationalEllAdicProductEdgeRetraction_leftInverse (i : ℕ) :
    Function.LeftInverse (rationalEllAdicProductEdgeRetraction K f g ℓ (i + 1))
      (rationalEllAdicEdgeMap ℓ f g (i + 1)) := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  let pX := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve f).nonempty_rationalPoint
  let : Algebra K Y.functionField := (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let pY := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve g).nonempty_rationalPoint
  exact rationalEllAdicEdgeRetraction_leftInverse K ℓ f g pX.1 pX.2 pY.1 pY.2 i

/-- The original projection edge map is injective for actual smooth
proper integral curves over an algebraically closed field. -/
theorem rationalEllAdicProductEdgeMap_injective (i : ℕ) :
    Function.Injective (rationalEllAdicEdgeMap ℓ f g (i + 1)) :=
  (rationalEllAdicProductEdgeRetraction_leftInverse K f g ℓ i).injective

/-- The actual middle Künneth component is killed by the edge
retraction supplied by the original curves. -/
theorem rationalEllAdicProductEdgeRetraction_comp_middle :
    (rationalEllAdicProductEdgeRetraction K f g ℓ 2).comp
        (rationalEllAdicKunnethComponent ℓ f g 1 1 2 rfl) = 0 := by
  let : Algebra K X.functionField := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  let pX := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve f).nonempty_rationalPoint
  let : Algebra K Y.functionField := (AlgebraicCurve.baseToFunctionField g).toAlgebra
  let pY := Classical.choice
    (AlgebraicCurve.CurveModel.ofSmoothProperCurve g).nonempty_rationalPoint
  exact rationalEllAdicEdgeRetraction_comp_middle K ℓ f g pX.1 pX.2 pY.1 pY.2

end AlgebraicGeometry.SmoothProperCurve
