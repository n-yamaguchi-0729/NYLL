/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Residue.Tame
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Tameness of the actual normalization from the Galois degree

In a finite Galois extension of the fraction field of a Dedekind domain,
each branch ramification index divides the degree. If this degree is
prime to the exponential characteristic of a specified nonzero residue
field, every branch over it has separable residue extension and prime
to characteristic ramification index.

The normalization ring and its Galois action are constructed from the
original field extension. Residue separability is deduced from the
inertia cardinality formula, including its inseparable-degree factor;
it is not an additional assumption. The degree itself therefore gives
the common exponent needed in the prime to characteristic case of
Stacks Project, Proposition 58.30.3:
https://stacks.math.columbia.edu/tag/0C0R.
-/

noncomputable section

namespace TameAbhyankar.SGA1

universe uV uK uL

attribute [local instance] Ideal.Quotient.field

/-- For a Galois extension whose degree is prime to the residue
characteristic, the actual normalization has separable residue fields
and branch indices dividing that same prime to characteristic degree. -/
theorem normalization_ramification_dvd_degree_and_residue_separable_of_coprime
    (V : Type uV) (K : Type uK) (L : Type uL)
    [CommRing V] [IsDedekindDomain V] [Field K] [Field L]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K L] [Algebra V L] [IsScalarTower V K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : Ideal V) [p.IsMaximal] (hp : p ≠ ⊥)
    (hcoprime : Nat.Coprime (Module.finrank K L) (ringExpChar (V ⧸ p)))
    (P : Ideal (integralClosure V L)) [P.IsMaximal] [P.LiesOver p] :
    P.ramificationIdx V ∣ Module.finrank K L ∧
      Nat.Coprime (P.ramificationIdx V) (ringExpChar (V ⧸ p)) ∧
      Algebra.IsSeparable (V ⧸ p) (integralClosure V L ⧸ P) := by
  let C := integralClosure V L
  have : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain V K L C
  have : Module.Finite V C := IsIntegralClosure.finite V K L C
  have : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L C
  have : Module.IsTorsionFree V L := Module.IsTorsionFree.trans_faithfulSMul V K L
  have : Module.IsTorsionFree V C := IsIntegralClosure.isTorsionFree V L
  have : Finite Gal(L/K) := IsGaloisGroup.finite Gal(L/K) K L
  let : MulSemiringAction Gal(L/K) C := IsIntegralClosure.MulSemiringAction V K L C
  have : IsGaloisGroup Gal(L/K) V C :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V C K L
  let I := P.toAddSubgroup.inertia Gal(L/K)
  have hInertiaDegree : Nat.card I ∣ Module.finrank K L := by
    rw [← IsGaloisGroup.card_eq_finrank Gal(L/K) K L]
    exact Subgroup.card_subgroup_dvd_card I
  have hIndexInertia : P.ramificationIdx V ∣ Nat.card I := by
    have hformula := inertia_card_eq_ramificationIdx_mul_finInsepDegree
      (A := V) (B := C) (G := Gal(L/K)) p hp P
    rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp] at hformula
    exact ⟨Field.finInsepDegree (V ⧸ p) (C ⧸ P), hformula⟩
  have hIndexDegree : P.ramificationIdx V ∣ Module.finrank K L :=
    hIndexInertia.trans hInertiaDegree
  refine ⟨hIndexDegree, hcoprime.of_dvd_left hIndexDegree, ?_⟩
  exact residue_isSeparable_of_inertia_card_coprime_ringExpChar
    (A := V) (B := C) (G := Gal(L/K)) p hp P
    (hcoprime.of_dvd_left hInertiaDegree)

end TameAbhyankar.SGA1
