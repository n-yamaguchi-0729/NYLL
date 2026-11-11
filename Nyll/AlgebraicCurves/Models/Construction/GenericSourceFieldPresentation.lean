/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.GenericSourceCurveModel
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation

/-!
# Function-field presentations from the actual generic source

The original dominant generic preimmersion gives its source field the
curve axioms and essential finite type over the original constants. A
separating parameter then supplies the rational-function-field algebra,
its scalar tower, finite dimension and separability. These are ordinary
algebra presentations derived from the actual smooth curve; no class
field comparison or reconstruction statement is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open EtaleFundamentalGroups

namespace AlgebraicCurve.CurveModel

universe u

variable {k K : Type u} [Field k] [PerfectField k] [Field K] [Algebra k K]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    (p : Spec (.of K) ⟶ C) [IsDominant p] [IsPreimmersion p]
    (hbase : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k K)))

include hbase in
/-- The curve axioms on the specified generic field follow from the
actual smooth curve and its literal structural-coefficient square. -/
theorem genericFieldSource_isCurveOver : IsCurveOver k K := by
  apply isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
    (genericFieldSourceRingEquiv p).symm
  intro a
  apply (genericFieldSourceRingEquiv p).injective
  rw [RingEquiv.apply_symm_apply, genericFieldSourceRingEquiv_base c p hbase]

include hbase in
omit [PerfectField k] in
/-- Essential finite type is transported along the actual generic-source
field isomorphism, with its proved base-field compatibility. -/
theorem genericFieldSource_essFiniteType : Algebra.EssFiniteType k K := by
  have : Smooth c := SmoothOfRelativeDimension.smooth (f := c) (n := 1)
  let aC : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofRingEquiv (f := genericFieldSourceRingEquiv p)
      (genericFieldSourceRingEquiv_base c p hbase)
  exact (Algebra.EssFiniteType.iff_of_algEquiv e).mp (essFiniteType_functionField c)

include hbase in
/-- Principal divisors belong to the actual source field, independently
of the rational parameter later used for class field theory. -/
theorem genericFieldSource_hasPrincipalDivisors : HasPrincipalDivisors k K :=
  (genericFieldSource_isCurveOver c p hbase).toHasPrincipalDivisors

/-- A chosen separating rational presentation supplied by the actual
smooth generic source. Its scalar tower and finite separable degree are
proved together with the algebra, so callers do not supply extra data. -/
def genericFieldSourceRatFuncAlgebra :
    {a : Algebra (RatFunc k) K //
      let _ : Algebra (RatFunc k) K := a
      IsScalarTower k (RatFunc k) K ∧
        FiniteDimensional (RatFunc k) K ∧ Algebra.IsSeparable (RatFunc k) K} := by
  have hcurve : IsCurveOver k K := genericFieldSource_isCurveOver c p hbase
  have hfinite : Algebra.EssFiniteType k K := genericFieldSource_essFiniteType c p hbase
  let h :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := k) (F := K)
  refine ⟨h.choose, ?_⟩
  obtain ⟨htower, hdimension, hseparable⟩ := h.choose_spec
  exact ⟨htower, hdimension, hseparable⟩

end AlgebraicCurve.CurveModel
