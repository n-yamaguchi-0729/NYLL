/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Ideal.Finsupp
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Original quotient-free coefficient maps

The free module over a coefficient quotient retains its original basis
indices. Its coefficient map and the transition for an inclusion of
ideals are the literal maps on each finitely supported coordinate.
The transition is surjective and has precisely the original ideal
multiple as kernel.

Linear combination with quotient coefficients agrees with the original
linear combination after the coefficient map. Thus an original generating
family gives the corresponding actual quotient-free presentation, without
choosing a different family or assuming the factorization.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R) (K : Type v)

/-- The actual coefficient quotient map on the original free module. -/
def quotientFreeCoefficients : (K →₀ R) →ₗ[R] (K →₀ R ⧸ I) :=
  Finsupp.mapRange.linearMap (Ideal.Quotient.mkₐ R I).toLinearMap

/-- The coefficient map preserves the original basis index and quotient coefficient. -/
theorem quotientFreeCoefficients_single (k : K) (a : R) :
    quotientFreeCoefficients I K (Finsupp.single k a) =
      Finsupp.single k (Ideal.Quotient.mk I a) :=
  Finsupp.mapRange_single (f := (Ideal.Quotient.mkₐ R I).toLinearMap)
    (hf := (Ideal.Quotient.mkₐ R I).toLinearMap.map_zero)

/-- Every finite family of quotient coefficients has an original coefficient lift. -/
theorem quotientFreeCoefficients_surjective : Function.Surjective (quotientFreeCoefficients I K) :=
  Finsupp.mapRange_surjective (Ideal.Quotient.mkₐ R I).toLinearMap
    (Ideal.Quotient.mkₐ R I).toLinearMap.map_zero (Ideal.Quotient.mkₐ_surjective R I)

/-- The ideal defining the quotient annihilates the actual quotient-free module. -/
theorem quotientFree_isTorsionBySet : Module.IsTorsionBySet R (K →₀ R ⧸ I) I := by
  intro x a
  apply Finsupp.ext
  intro k
  change (a : R) • x k = 0
  calc
    (a : R) • x k = Ideal.Quotient.mk I a.val • x k :=
      (IsScalarTower.algebraMap_smul (R ⧸ I) a.val (x k)).symm
    _ = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property, zero_smul]

variable {I} (J : Ideal R) (hJI : J ≤ I)

/-- The literal coordinatewise quotient transition, with the same original basis. -/
def quotientFreeFactor : (K →₀ R ⧸ J) →ₗ[R] (K →₀ R ⧸ I) :=
  Finsupp.mapRange.linearMap (Ideal.Quotient.factorₐ R hJI).toLinearMap

/-- Each original coefficient is mapped by the actual quotient factor. -/
theorem quotientFreeFactor_single (k : K) (a : R ⧸ J) :
    quotientFreeFactor K J hJI (Finsupp.single k a) =
      Finsupp.single k (Ideal.Quotient.factor hJI a) :=
  Finsupp.mapRange_single (f := (Ideal.Quotient.factorₐ R hJI).toLinearMap)
    (hf := (Ideal.Quotient.factorₐ R hJI).toLinearMap.map_zero)

/-- The actual free transition is surjective. -/
theorem quotientFreeFactor_surjective : Function.Surjective (quotientFreeFactor K J hJI) :=
  Finsupp.mapRange_surjective (Ideal.Quotient.factorₐ R hJI).toLinearMap
    (Ideal.Quotient.factorₐ R hJI).toLinearMap.map_zero (Ideal.Quotient.factor_surjective hJI)

/-- Reduction of an original coefficient vector commutes with the actual free transition. -/
theorem quotientFreeFactor_coefficients :
    (quotientFreeFactor K J hJI).comp (quotientFreeCoefficients J K) =
      quotientFreeCoefficients I K := by
  apply Finsupp.lhom_ext
  intro k a
  change quotientFreeFactor K J hJI
      (quotientFreeCoefficients J K (Finsupp.single k a)) = _
  rw [quotientFreeCoefficients_single, quotientFreeFactor_single,
    Ideal.Quotient.factor_mk, quotientFreeCoefficients_single]

/-- The original quotient-free transition has exactly the original ideal multiple as kernel. -/
theorem quotientFreeFactor_ker :
    (quotientFreeFactor K J hJI).ker = I • (⊤ : Submodule R (K →₀ R ⧸ J)) := by
  let q : R ⧸ J →ₗ[R] R ⧸ I := (Ideal.Quotient.factorₐ R hJI).toLinearMap
  have hq : q.ker = I • (⊤ : Submodule R (R ⧸ J)) := by
    change (RingHom.ker (Ideal.Quotient.factor hJI)).restrictScalars R =
      I • (⊤ : Submodule R (R ⧸ J))
    rw [Ideal.smul_top_eq_map]
    exact congrArg (fun L : Ideal (R ⧸ J) => L.restrictScalars R)
      (Ideal.Quotient.factor_ker hJI)
  change (Finsupp.mapRange.linearMap (α := K) q).ker = _
  rw [Finsupp.ker_mapRange, hq, Finsupp.submodule_smul, Finsupp.submodule_top]

section LinearCombination

variable (I) {M : Type w} [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
  [IsScalarTower R (R ⧸ I) M] (v : K → M)

/-- The quotient-free presentation retains the original linear combination on coefficients. -/
theorem quotientLinearCombination_coefficients :
    ((Finsupp.linearCombination (R ⧸ I) v).restrictScalars R).comp
        (quotientFreeCoefficients I K) = Finsupp.linearCombination R v := by
  apply Finsupp.lhom_ext
  intro k a
  change Finsupp.linearCombination (R ⧸ I) v
      (quotientFreeCoefficients I K (Finsupp.single k a)) = _
  rw [quotientFreeCoefficients_single, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single]
  exact IsScalarTower.algebraMap_smul (R ⧸ I) a (v k)

/-- The original generating family gives an actual surjective quotient-free presentation. -/
theorem quotientLinearCombination_surjective
    (hv : Function.Surjective (Finsupp.linearCombination R v)) :
    Function.Surjective (Finsupp.linearCombination (R ⧸ I) v) := by
  intro y
  obtain ⟨c, hc⟩ := hv y
  exact ⟨quotientFreeCoefficients I K c,
    (LinearMap.congr_fun (quotientLinearCombination_coefficients (K := K) I v) c).trans hc⟩

end LinearCombination

end AdicModuleSystem
