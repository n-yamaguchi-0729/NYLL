/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.AdditiveLocalSymbolFormula
import Nyll.AlgebraicCurves.Divisors.Modulus.MultiplicativeModulus
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality

/-!
# Moduli for vector and split-torus rational maps

Finite coordinate families of actual rational functions admit a common full
modulus. This applies in arbitrary characteristic and makes no assumption
that a general commutative unipotent group is a vector group.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]
  [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F] [Finite ι]

local instance : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors

/-- A rational map to a finite-dimensional vector group has a full modulus. -/
theorem exists_vector_modulus (f : ι → F) :
    ∃ D : Modulus K F, D.HasModulus (fun v i => v.evalAt (f i)) := by
  apply exists_modulus_pi
  intro i
  obtain ⟨D, _hD, hm⟩ := exists_additive_modulus (K := K) (f i)
  exact ⟨D, hm⟩

/-- Its local symbols exist uniquely with values in the actual vector group. -/
theorem exists_vector_localSymbol (f : ι → F) :
    ∃ D : Modulus K F, ∃! σ : Place K F → Additive Fˣ →+ (ι → K),
      D.IsLocalSymbol (fun v i => v.evalAt (f i)) σ := by
  obtain ⟨D, hm⟩ := exists_vector_modulus (K := K) f
  exact ⟨D, (hasModulus_iff_existsUnique_localSymbol D _).mp hm⟩

variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]

omit [Algebra.EssFiniteType K F] in
/-- A finite family of nonzero rational functions, viewed as a rational map
to a split torus, has an actual common full modulus. -/
theorem exists_splitTorus_modulus (f : ι → F) (hf : ∀ i, f i ≠ 0) :
    ∃ D : Modulus K F,
      D.HasModulus (fun v i => multiplicativeValues (f i) (hf i) v) := by
  apply exists_modulus_pi
  intro i
  obtain ⟨D, _hD, _hred, hm⟩ := exists_reduced_multiplicative_modulus (K := K) (f i) (hf i)
  exact ⟨D, hm⟩

end AlgebraicCurve.Modulus
