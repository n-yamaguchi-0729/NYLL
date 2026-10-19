/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClassRigidification
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorDegree

/-! # Degree-zero divisor classes and actual algebraically trivial rigidified bundles -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)
  (𝒱 : M.C.TwoAffineOpenCover)

/-- The actual divisor homomorphism restricts to degree zero. -/
def rigidifiedDivisorZeroHom : (M.cartierModulus I hI).divAwayZero →+
    (eulerDegree M.toBase 𝒱 I.subschemeι).ker := by
  let f : (M.cartierModulus I hI).divAwayZero →+ Additive (Classes I.subschemeι) :=
    (M.rigidifiedDivisorHom I hI).comp (M.cartierModulus I hI).divAwayZero.subtype
  exact f.codRestrict (eulerDegree M.toBase 𝒱 I.subschemeι).ker (fun E =>
    (M.eulerDegree_rigidifiedDivisorAwayHom I hI 𝒱 ⟨E.1, E.2.1⟩).trans
      (Divisor.mem_degZero.mp E.2.2))

/-- Full congruence is the relation defining the actual degree-zero class map. -/
def rigidifiedZeroClassHom : (M.cartierModulus I hI).ClassGroupZero →+
    (eulerDegree M.toBase 𝒱 I.subschemeι).ker :=
  QuotientAddGroup.lift _ (M.rigidifiedDivisorZeroHom I hI 𝒱)
    (fun E hE => Subtype.ext
      (M.principal_le_rigidifiedDivisorAwayHom_ker I hI ⟨E.1, E.2.1⟩ hE))

/-- The degree-zero class map is the originally constructed actual divisor map. -/
theorem rigidifiedZeroClassHom_mkZero
    (E : (M.cartierModulus I hI).divAwayZero) :
    M.rigidifiedZeroClassHom I hI 𝒱 ((M.cartierModulus I hI).mkZero E) =
      M.rigidifiedDivisorZeroHom I hI 𝒱 E := rfl

/-- Exactness of the full principal kernel gives injectivity on degree zero. -/
theorem rigidifiedZeroClassHom_injective :
    Function.Injective (M.rigidifiedZeroClassHom I hI 𝒱) := by
  apply (injective_iff_map_eq_zero (M.rigidifiedZeroClassHom I hI 𝒱)).mpr
  intro x hx
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  have he : M.rigidifiedDivisorAwayHom I hI ⟨E.1, E.2.1⟩ = 0 :=
    congrArg Subtype.val hx
  exact (QuotientAddGroup.eq_zero_iff E).mpr
    (M.rigidifiedDivisorAwayHom_ker_le_principal I hI ⟨E.1, E.2.1⟩ he)

variable [GeometricallyIntegral M.toBase]

/-- An actual degree-zero rigidified class has an actual degree-zero divisor
representative; its degree follows from the proved Euler calculation. -/
theorem rigidifiedZeroClassHom_surjective :
    Function.Surjective (M.rigidifiedZeroClassHom I hI 𝒱) := by
  intro x
  obtain ⟨E, hE⟩ := M.rigidifiedDivisorAwayHom_surjective I hI x.1
  have hdeg : Divisor.degree E.1 = 0 := by
    rw [← M.eulerDegree_rigidifiedDivisorAwayHom I hI 𝒱 E, hE]
    exact x.2
  let E₀ : (M.cartierModulus I hI).divAwayZero :=
    ⟨E.1, E.2, Divisor.mem_degZero.mpr hdeg⟩
  exact ⟨(M.cartierModulus I hI).mkZero E₀, Subtype.ext hE⟩

/-- The genuine full-modulus degree-zero divisor class group identifies with
the actual degree-zero rigidified bundle classes, with no assumed comparison. -/
def rigidifiedZeroClassEquiv : (M.cartierModulus I hI).ClassGroupZero ≃+
    (eulerDegree M.toBase 𝒱 I.subschemeι).ker :=
  AddEquiv.ofBijective (M.rigidifiedZeroClassHom I hI 𝒱)
    ⟨M.rigidifiedZeroClassHom_injective I hI 𝒱,
      M.rigidifiedZeroClassHom_surjective I hI 𝒱⟩

/-- The concrete zero-class equivalence is induced by canonical inverse point ideals. -/
theorem rigidifiedZeroClassEquiv_mkZero
    (E : (M.cartierModulus I hI).divAwayZero) :
    (M.rigidifiedZeroClassEquiv I hI 𝒱 ((M.cartierModulus I hI).mkZero E)).1 =
      M.rigidifiedDivisorHom I hI E.1 := rfl

end AlgebraicCurve.CurveModel
