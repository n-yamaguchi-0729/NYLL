/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedCommutativity
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgebraicEquivalenceIffEulerCharSectionsOfEq
import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.ModulesInvertibleEulerCharSectionsOfTensorEqAddSub
import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.InvertibleIdealEulerCharSectionsOfTensorInvModuleEq
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgebraicEquivalenceEulerCharSectionsOfTensorEq

/-! # Euler degree of actual modulus-rigidified classes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicCurves.Cohomology.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {K : Type u} [Field K] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (𝒱 : X.TwoAffineOpenCover) (i : D ⟶ X)

/-- Euler characteristic of the actual underlying module. -/
def moduleEulerCharacteristic (L : X.Modules) : ℤ :=
  (Module.finrank K (𝒱.sectionsOf c L).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf c L).H1

/-- An actual sheaf isomorphism preserves its Euler characteristic. -/
theorem moduleEulerCharacteristic_iso {L L' : X.Modules} (e : L ≅ L') :
    moduleEulerCharacteristic c 𝒱 L = moduleEulerCharacteristic c 𝒱 L' := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso c 𝒱 e
  exact congrArg₂ (fun a b : ℕ => (a : ℤ) - b) e0.finrank_eq e1.finrank_eq

variable [IsAlgClosed K] [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- Euler degree is an additive invariant of actual compatible-isomorphism
classes; its additivity is supplied by the curve tensor Euler theorem. -/
def eulerDegree : Additive (Classes i) →+ ℤ := by
  let f : Classes i → Multiplicative ℤ := Quotient.lift
    (fun M : RigidifiedLineBundle i => Multiplicative.ofAdd
      (moduleEulerCharacteristic c 𝒱 M.L - moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules)))
    (by
      rintro M N ⟨e⟩
      exact congrArg (fun n : ℤ => Multiplicative.ofAdd
        (n - moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules)))
        (moduleEulerCharacteristic_iso c 𝒱 e.toIso))
  have hf : ∀ a b : Classes i, f (a * b) = f a * f b := by
    intro a b
    induction a using Quotient.ind with
    | _ M =>
      induction b using Quotient.ind with
      | _ N =>
        change Multiplicative.ofAdd
            (moduleEulerCharacteristic c 𝒱 (M.L ⊗ N.L) -
              moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules)) =
          Multiplicative.ofAdd ((moduleEulerCharacteristic c 𝒱 M.L -
              moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules)) +
            (moduleEulerCharacteristic c 𝒱 N.L -
              moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules)))
        apply congrArg Multiplicative.ofAdd
        have h := Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub
          K c M.L N.L M.isInvertible N.isInvertible 𝒱
        change moduleEulerCharacteristic c 𝒱 (M.L ⊗ N.L) =
          moduleEulerCharacteristic c 𝒱 M.L + moduleEulerCharacteristic c 𝒱 N.L -
            moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules) at h
        rw [h]
        ring
  exact (MonoidHom.mk' f hf).toAdditive

/-- The degree formula evaluates the actual underlying line bundle. -/
theorem eulerDegree_classOf (M : RigidifiedLineBundle i) :
    eulerDegree c 𝒱 i (Additive.ofMul (classOf M)) =
      moduleEulerCharacteristic c 𝒱 M.L -
        moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules) := rfl

/-- An algebraically trivial actual bundle has Euler degree zero. -/
theorem eulerDegree_eq_zero_of_isAlgEquivZero (M : RigidifiedLineBundle i)
    (hM : RelPicard.IsAlgEquivZero c M.L) :
    eulerDegree c 𝒱 i (Additive.ofMul (classOf M)) = 0 := by
  rw [eulerDegree_classOf]
  have h := RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq c 𝒱 M.L
    (𝟙_ X.Modules) M.isInvertible (Scheme.Modules.isInvertible_unit X) hM
  change moduleEulerCharacteristic c 𝒱 (M.L ⊗ 𝟙_ X.Modules) =
    moduleEulerCharacteristic c 𝒱 (𝟙_ X.Modules) at h
  rw [moduleEulerCharacteristic_iso c 𝒱 (ρ_ M.L)] at h
  exact sub_eq_zero.mpr h

/-- Euler degree zero is precisely algebraic triviality of the actual bundle. -/
theorem eulerDegree_classOf_eq_zero_iff (M : RigidifiedLineBundle i) :
    eulerDegree c 𝒱 i (Additive.ofMul (classOf M)) = 0 ↔
      RelPicard.IsAlgEquivZero c M.L := by
  rw [eulerDegree_classOf, sub_eq_zero,
    RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq K c M.L M.isInvertible 𝒱]
  rfl

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
