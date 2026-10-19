/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorKernelReverse
import Nyll.JacobianVarieties.Generalized.DivisorRigidificationSurjective

/-! # Full divisor classes identify with actual rigidified line-bundle classes -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- The concrete map descends through precisely the full-modulus principal relation. -/
def rigidifiedClassHom : (M.cartierModulus I hI).ClassGroup →+
    Additive (RigidifiedLineBundle.Classes I.subschemeι) :=
  QuotientAddGroup.lift _ (M.rigidifiedDivisorAwayHom I hI)
    (fun E hE => M.principal_le_rigidifiedDivisorAwayHom_ker I hI E hE)

/-- Descent preserves the concrete divisor class map. -/
theorem rigidifiedClassHom_mk (E : (M.cartierModulus I hI).divAway) :
    M.rigidifiedClassHom I hI (QuotientAddGroup.mk E) =
      M.rigidifiedDivisorAwayHom I hI E := rfl

/-- Exactness of the proved principal kernel gives injectivity. -/
theorem rigidifiedClassHom_injective : Function.Injective (M.rigidifiedClassHom I hI) := by
  apply (injective_iff_map_eq_zero (M.rigidifiedClassHom I hI)).mpr
  intro x hx
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (QuotientAddGroup.eq_zero_iff E).mpr
    (M.rigidifiedDivisorAwayHom_ker_le_principal I hI E hx)

variable [GeometricallyIntegral M.toBase]

/-- Every actual rigidified bundle class is reached by the descended divisor map. -/
theorem rigidifiedClassHom_surjective : Function.Surjective (M.rigidifiedClassHom I hI) := by
  intro x
  obtain ⟨E, hE⟩ := M.rigidifiedDivisorAwayHom_surjective I hI x
  exact ⟨QuotientAddGroup.mk E, hE⟩

/-- The concrete full-modulus divisor class group is the actual group of
line bundles trivialized on the original closed subscheme. -/
def rigidifiedClassEquiv : (M.cartierModulus I hI).ClassGroup ≃+
    Additive (RigidifiedLineBundle.Classes I.subschemeι) :=
  AddEquiv.ofBijective (M.rigidifiedClassHom I hI)
    ⟨M.rigidifiedClassHom_injective I hI, M.rigidifiedClassHom_surjective I hI⟩

/-- The equivalence is induced by the actual canonical inverse point ideals. -/
theorem rigidifiedClassEquiv_mk (E : (M.cartierModulus I hI).divAway) :
    M.rigidifiedClassEquiv I hI (QuotientAddGroup.mk E) =
      M.rigidifiedDivisorAwayHom I hI E := rfl

end AlgebraicCurve.CurveModel
