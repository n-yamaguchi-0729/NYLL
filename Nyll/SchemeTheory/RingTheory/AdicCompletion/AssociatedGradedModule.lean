/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.ReesAlgebra

/-!
# Associated graded modules from the actual Rees module

For an ideal filtration, the quotient of its Rees module by the shifted
filtration is identified with the direct sum of the actual successive
quotients. The Rees action is the native polynomial action on this quotient;
no graded module structure or quotient comparison is supplied as an input.

For a stable filtration of a finite module over a Noetherian ring, this
quotient is finite over the Rees algebra. This is the affine finiteness
construction used for the successive kernels of a coherent formal system.
-/

noncomputable section

open scoped DirectSum

namespace Ideal.Filtration

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Ideal R} (F : I.Filtration M)

private def coefficientFamily (p : F.submodule) : ⨁ n : ℕ, F.N n := by
  classical
  exact DFinsupp.mk p.val.coeff.support (fun n => ⟨p.val.coeff n.val, p.property n.val⟩)

private theorem coefficientFamily_apply (p : F.submodule) (n : ℕ) :
    coefficientFamily F p n = ⟨p.val.coeff n, p.property n⟩ := by
  classical
  apply Subtype.ext
  by_cases hn : n ∈ p.val.coeff.support
  · simp only [coefficientFamily, DFinsupp.mk_apply, dite_eq_left hn]
  · have hz : p.val.coeff n = 0 := Finsupp.notMem_support_iff.mp hn
    simp only [coefficientFamily, DFinsupp.mk_apply, dite_eq_right hn,
      ZeroMemClass.coe_zero, hz]

private def ofCoefficientFamily (x : ⨁ n : ℕ, F.N n) : F.submodule := by
  classical
  let p : ℕ →₀ M := Finsupp.onFinset x.support (fun n => (x n).val) (by
    intro n hn
    apply DFinsupp.mem_support_iff.mpr
    intro hz
    exact hn (congrArg Subtype.val hz))
  exact ⟨PolynomialModule.ofCoeff R p, fun n => (x n).property⟩

private theorem ofCoefficientFamily_coeff (x : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (ofCoefficientFamily F x).val.coeff n = (x n).val := rfl

/-- Coefficients identify the actual Rees module with the direct sum of the
members of the filtration, without changing any coefficient. -/
def reesCoefficientEquiv : F.submodule ≃ₗ[R] ⨁ n : ℕ, F.N n where
  toFun := coefficientFamily F
  invFun := ofCoefficientFamily F
  left_inv p := by
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext n
    rw [ofCoefficientFamily_coeff, coefficientFamily_apply]
  right_inv x := by
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    rw [coefficientFamily_apply]
    exact ofCoefficientFamily_coeff F x n
  map_add' p q := by
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    change (coefficientFamily F (p + q) n).val =
      (coefficientFamily F p n).val + (coefficientFamily F q n).val
    simp only [coefficientFamily_apply]
    exact congrArg (fun a : ℕ →₀ M => a n)
      ((PolynomialModule.coeffLinearEquiv R R).map_add p.val q.val)
  map_smul' r p := by
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    change (coefficientFamily F (r • p) n).val = r • (coefficientFamily F p n).val
    simp only [coefficientFamily_apply]
    exact congrArg (fun a : ℕ →₀ M => a n)
      ((PolynomialModule.coeffLinearEquiv R R).map_smul r p.val)

/-- The coefficient comparison keeps the original polynomial coefficient. -/
theorem reesCoefficientEquiv_apply (p : F.submodule) (n : ℕ) :
    reesCoefficientEquiv F p n = ⟨p.val.coeff n, p.property n⟩ :=
  coefficientFamily_apply F p n

/-- The filtration shifted by one step. -/
def successor : I.Filtration M where
  N n := F.N (n + 1)
  mono n := F.mono (n + 1)
  smul_le n := F.smul_le (n + 1)

/-- The shifted Rees module as a submodule of the original Rees module. -/
def successorSubmodule : Submodule (reesAlgebra I) F.submodule :=
  (successor F).submodule.comap F.submodule.subtype

/-- The next filtration member as a submodule of the current member. -/
def gradeSubmodule (n : ℕ) : Submodule R (F.N n) :=
  (F.N (n + 1)).comap (F.N n).subtype

/-- The actual successive quotient, retaining its native module structure
when a concrete filtration is substituted. -/
def gradeModule (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R ((F.N n) ⧸ gradeSubmodule F n)

/-- The actual quotient of the Rees module by the shifted filtration. -/
def associatedGraded : Type v :=
  Quotient (Submodule.quotientRel (R := reesAlgebra I) (M := F.submodule)
    (successorSubmodule F))

-- The quotient's coefficient ring must be specified before Lean compares
-- the native Rees semiring and ring projections.
instance associatedGradedAddCommGroup : AddCommGroup (associatedGraded F) := by
  let g := Submodule.Quotient.addCommGroup (R := reesAlgebra I) (M := F.submodule)
    (p := successorSubmodule F)
  exact g

instance associatedGradedModule : Module (reesAlgebra I) (associatedGraded F) := by
  let m := Submodule.Quotient.module (R := reesAlgebra I) (M := F.submodule)
    (successorSubmodule F)
  exact m

instance associatedGradedModuleBase : Module R (associatedGraded F) := by
  let m := Submodule.Quotient.module' (R := reesAlgebra I) (M := F.submodule) (S := R)
    (successorSubmodule F)
  exact m

instance associatedGradedScalarTower : IsScalarTower R (reesAlgebra I) (associatedGraded F) := by
  have h := Submodule.Quotient.isScalarTower (R := reesAlgebra I) (M := F.submodule) (S := R)
    (successorSubmodule F) (reesAlgebra I)
  exact h

/-- Taking every coefficient modulo the next filtration member. -/
def associatedGradedCoefficients : F.submodule →ₗ[R]
    ⨁ n : ℕ, ((F.N n) ⧸ gradeSubmodule F n) :=
  (DirectSum.lmap (fun n => (gradeSubmodule F n).mkQ)).comp
    (reesCoefficientEquiv F).toLinearMap

theorem associatedGradedCoefficients_apply (p : F.submodule) (n : ℕ) :
    associatedGradedCoefficients F p n =
      (gradeSubmodule F n).mkQ ⟨p.val.coeff n, p.property n⟩ := by
  change (gradeSubmodule F n).mkQ (reesCoefficientEquiv F p n) = _
  rw [reesCoefficientEquiv_apply]

/-- Every finite family of successive quotient classes has a polynomial lift. -/
theorem associatedGradedCoefficients_surjective :
    Function.Surjective (associatedGradedCoefficients F) :=
  ((DirectSum.lmap_surjective (fun n => (gradeSubmodule F n).mkQ)).mpr
    (fun n => (gradeSubmodule F n).mkQ_surjective)).comp
      (reesCoefficientEquiv F).surjective

/-- Vanishing of every quotient coefficient is exactly the shifted filtration. -/
theorem ker_associatedGradedCoefficients :
    (associatedGradedCoefficients F).ker = (successorSubmodule F).restrictScalars R := by
  ext p
  rw [LinearMap.mem_ker]
  constructor
  · intro hp n
    have hz := congrArg (fun x : ⨁ n : ℕ, ((F.N n) ⧸ gradeSubmodule F n) => x n) hp
    rw [associatedGradedCoefficients_apply] at hz
    exact (Submodule.Quotient.mk_eq_zero (gradeSubmodule F n)).mp hz
  · intro hp
    apply DFinsupp.ext
    intro n
    rw [associatedGradedCoefficients_apply]
    exact (Submodule.Quotient.mk_eq_zero (gradeSubmodule F n)).mpr (hp n)

/-- The actual Rees quotient is the direct sum of the actual successive
filtration quotients. -/
def associatedGradedEquiv : associatedGraded F ≃ₗ[R]
    ⨁ n : ℕ, ((F.N n) ⧸ gradeSubmodule F n) := by
  let e₁ := (Submodule.Quotient.restrictScalarsEquiv
    (R := reesAlgebra I) (M := F.submodule) R (successorSubmodule F)).symm
  let e₂ := Submodule.quotEquivOfEq (R := R) (M := F.submodule)
    ((successorSubmodule F).restrictScalars R)
    (associatedGradedCoefficients F).ker (ker_associatedGradedCoefficients F).symm
  let e₃ := LinearMap.quotKerEquivOfSurjective (R := R) (M := F.submodule)
    (M₂ := ⨁ n : ℕ, ((F.N n) ⧸ gradeSubmodule F n))
    (associatedGradedCoefficients F) (associatedGradedCoefficients_surjective F)
  let e := e₁.trans (e₂.trans e₃)
  exact e

/-- Each graded coefficient of a quotient class is the original polynomial
coefficient modulo the next filtration member. -/
theorem associatedGradedEquiv_mk (p : F.submodule) (n : ℕ) :
    associatedGradedEquiv F (Submodule.Quotient.mk p) n =
      (gradeSubmodule F n).mkQ ⟨p.val.coeff n, p.property n⟩ := by
  have h := LinearMap.quotKerEquivOfSurjective_apply_mk (R := R) (M := F.submodule)
    (M₂ := ⨁ k : ℕ, ((F.N k) ⧸ gradeSubmodule F k))
    (f := associatedGradedCoefficients F) (associatedGradedCoefficients_surjective F) p
  have hn := congrArg (fun x : ⨁ k : ℕ, ((F.N k) ⧸ gradeSubmodule F k) => x n) h
  exact hn.trans (associatedGradedCoefficients_apply F p n)

/-- Stability makes the concrete associated graded module finite over the
Rees algebra. -/
theorem associatedGraded_finite [IsNoetherianRing R] [Module.Finite R M]
    (hF : F.Stable) : Module.Finite (reesAlgebra I) (associatedGraded F) := by
  have : Module.Finite (reesAlgebra I) F.submodule :=
    Module.Finite.of_fg ((F.submodule_fg_iff_stable
      (fun n => IsNoetherian.noetherian (F.N n))).mpr hF)
  let q := Submodule.mkQ (R := reesAlgebra I) (M := F.submodule)
    (successorSubmodule F)
  have hq := Submodule.mkQ_surjective (R := reesAlgebra I) (M := F.submodule)
    (successorSubmodule F)
  have h := Module.Finite.of_surjective q hq
  exact h

end Ideal.Filtration
