/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
public import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
public import Nyll.GaloisCohomology.Cyclic.TateH0.Main

/-! Provides the public declarations in the `CyclicCohomology.Herbrand.LowDegree` Lean module. -/

@[expose] public section

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u v

/-- Integral Tate degree zero and the arithmetic norm quotient have the
same cardinality even when the base and extension fields have different universes. -/
theorem herbrand_integralTate_zero_units_cardinal_eq_normQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Cardinal.lift.{u} (Cardinal.mk
      (IntegralGroupCohomology.tate (Rep.ofAlgebraAutOnUnits K L) 0)) =
      Cardinal.lift.{v} (Cardinal.mk (Additive (NormQuotient K L))) :=
  Cardinal.lift_mk_eq'.mpr ⟨(integralH0TateUnitsAddEquivNormQuotient K L).toEquiv⟩

/-- Degree-zero Tate cohomology of field units is equipotent to the norm quotient. -/
theorem herbrand_tateCohomology_zero_units_cardinal_eq_normQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) =
      Cardinal.mk (Additive (NormQuotient K L)) :=
  Cardinal.mk_congr
    (H0TateUnitsIsoNormQuotient K L).toLinearEquiv.toEquiv

end
end CyclicCohomology
