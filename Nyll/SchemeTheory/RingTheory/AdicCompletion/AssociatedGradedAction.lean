/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AssociatedGradedModule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The residual Rees action on the constructed associated graded module

The coefficient ideal acts by zero on the actual quotient of a filtered
Rees module. Consequently its native polynomial action descends to the
quotient of the Rees algebra by the extended coefficient ideal. The
construction retains both original scalar actions and proves finiteness
over this residual Rees algebra for a stable finite filtration.
-/

noncomputable section

open scoped DirectSum

namespace Ideal.Filtration

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Ideal R} (F : I.Filtration M)

private theorem grade_smul_eq_zero {r : R} (hr : r ∈ I) (n : ℕ)
    (x : (F.N n) ⧸ gradeSubmodule F n) : r • x = 0 := by
  refine Quotient.inductionOn' x ?_
  intro p
  change Submodule.Quotient.mk (p := gradeSubmodule F n) (r • p) = 0
  apply (Submodule.Quotient.mk_eq_zero (gradeSubmodule F n)).mpr
  exact F.smul_le n (Submodule.smul_mem_smul hr p.property)

/-- A coefficient in the filtration ideal raises every coefficient into
the shifted filtration and hence kills the associated graded quotient. -/
theorem associatedGraded_smul_eq_zero {r : R} (hr : r ∈ I)
    (x : associatedGraded F) : r • x = 0 := by
  apply (associatedGradedEquiv F).injective
  rw [map_smul, map_zero]
  apply DFinsupp.ext
  intro n
  exact grade_smul_eq_zero F hr n (associatedGradedEquiv F x n)

/-- The extended coefficient ideal annihilates the actual Rees quotient. -/
theorem associatedGraded_isTorsionBySet :
    Module.IsTorsionBySet (reesAlgebra I) (associatedGraded F)
      (I.map (algebraMap R (reesAlgebra I))) := by
  apply (Module.isTorsionBySet_iff_subset_annihilator
    (reesAlgebra I) (associatedGraded F)).mpr
  change I.map (algebraMap R (reesAlgebra I)) ≤
    Module.annihilator (reesAlgebra I) (associatedGraded F)
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change algebraMap R (reesAlgebra I) r ∈
    Module.annihilator (reesAlgebra I) (associatedGraded F)
  apply Module.mem_annihilator.mpr
  intro x
  rw [algebraMap_smul]
  exact associatedGraded_smul_eq_zero F hr x

/-- The polynomial action descends through the extended coefficient ideal. -/
instance associatedGradedResidualModule :
    Module ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (associatedGraded F) := by
  let m := (associatedGraded_isTorsionBySet F).module
  exact m

/-- The descended action agrees with the original Rees action. -/
instance associatedGradedResidualScalarTower :
    IsScalarTower (reesAlgebra I)
      ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) (associatedGraded F) := by
  have h := (associatedGraded_isTorsionBySet F).isScalarTower (S := reesAlgebra I)
  exact h

/-- The original base-ring action is preserved by descent of the Rees action. -/
instance associatedGradedResidualBaseScalarTower :
    IsScalarTower R ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (associatedGraded F) := by
  have h := (associatedGraded_isTorsionBySet F).isScalarTower (S := R)
  exact h

/-- A residual Rees class acts by its original polynomial representative. -/
theorem associatedGraded_residual_mk_smul (r : reesAlgebra I) (x : associatedGraded F) :
    Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))) r • x = r • x :=
  Module.IsTorsionBySet.mk_smul (associatedGraded_isTorsionBySet F) r x

/-- The constructed graded module is finite over the actual residual Rees algebra. -/
theorem associatedGraded_residual_finite [IsNoetherianRing R] [Module.Finite R M]
    (hF : F.Stable) :
    Module.Finite ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I)))
      (associatedGraded F) := by
  have : Module.Finite (reesAlgebra I) (associatedGraded F) :=
    associatedGraded_finite F hF
  exact Module.Finite.of_restrictScalars_finite (reesAlgebra I)
    ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) (associatedGraded F)

end Ideal.Filtration
