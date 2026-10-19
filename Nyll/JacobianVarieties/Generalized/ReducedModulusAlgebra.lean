/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.AffineKernel
import Nyll.JacobianVarieties.Generalized.ModulusFramePicard
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBaseSubscheme
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedFiniteAlgebraSplit
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Splitting the entire algebra of an actual geometrically reduced modulus -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- Geometric reducedness applies to the entire actual scalar-extended modulus. -/
theorem modulus_changeBase_isReduced [GeometricallyReduced (modulusBaseMap D)]
    {L : Type u} [Field L] (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    IsReduced (D.changeBaseOfIdentity f).I.subscheme :=
  GeometricallyReduced.geometrically_isReduced f _ _ (D.changeBaseOfIdentity_isPullback f)

variable [IsAlgClosed K] [IsReduced D.I.subscheme]

/-- The algebra of a reduced modulus over an algebraically closed field is the actual
product of one coefficient-field copy for every unit of its divisor degree. -/
def reducedModulusAlgebraSplit : modulusAlgebra D ≃ₐ[K] (Fin d → K) := by
  have : Module.Finite K (modulusAlgebra D) := Module.Finite.of_basis (modulusBasis D)
  have : _root_.IsReduced (modulusAlgebra D) :=
    inferInstanceAs (_root_.IsReduced Γ(D.I.subscheme, ⊤))
  exact SchemeTheory.reducedFiniteAlgebraSplitFin K (modulusAlgebra D)
    (finrank_modulusAlgebra D)

/-- The positive-degree indexing is the one used by the concrete scalar-unit quotient. -/
def positiveReducedModulusAlgebraSplit (hd : 0 < d) :
    modulusAlgebra D ≃ₐ[K] (Fin (d - 1 + 1) → K) :=
  (reducedModulusAlgebraSplit D).trans
    (AlgEquiv.piCongrLeft' K (fun _ : Fin d => K)
      (finCongr (Nat.sub_add_cancel (Nat.succ_le_of_lt hd)).symm))

end AlgebraicGeometry.GeneralizedJacobian
