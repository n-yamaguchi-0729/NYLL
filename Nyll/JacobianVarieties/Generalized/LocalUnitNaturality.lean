/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalUnitTransition

/-!
# Naturality of the local-unit description of the forgetful kernel

The isomorphism from truncated local units modulo scalars to the forgetful
kernel is compatible with shrinking the modulus. Its formula on representatives
uses the already constructed finite-jet boundary.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F]
variable {D E : Modulus K F}

/-- Shrinking the modulus maps the corresponding forgetful kernels. -/
def kernelTransition (h : E ≤ D) : D.toPic0.ker →+ E.toPic0.ker where
  toFun x := ⟨transition h x.1, by
    change E.toPic0 (transition h x.1) = 0
    rw [toPic0_transition]
    exact x.2⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; exact map_add _ x.1 y.1

/-- The quotient-kernel equivalence has the actual finite-jet boundary as its formula. -/
@[simp]
theorem localUnitQuotientEquivKernel_mk (D : Modulus K F) (hC : ConstantsAreBase K F)
    (q : D.LocalJetUnits) :
    D.localUnitQuotientEquivKernel hC (QuotientGroup.mk q) = D.jetBoundaryToKernel q := by
  unfold localUnitQuotientEquivKernel
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The local-unit quotient-kernel isomorphisms form a commutative transition diagram. -/
theorem localUnitQuotientEquivKernel_natural (h : E ≤ D) (hC : ConstantsAreBase K F)
    (x : D.LocalJetUnits ⧸ D.scalarJets.range) :
    E.localUnitQuotientEquivKernel hC (localUnitQuotientTransition h x) =
      Multiplicative.ofAdd
        (kernelTransition h (D.localUnitQuotientEquivKernel hC x).toAdd) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
  change E.localUnitQuotientEquivKernel hC (QuotientGroup.mk (jetReduction h q)) =
    Multiplicative.ofAdd
      (kernelTransition h (D.localUnitQuotientEquivKernel hC (QuotientGroup.mk q)).toAdd)
  rw [localUnitQuotientEquivKernel_mk, localUnitQuotientEquivKernel_mk]
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd (jetBoundary_reduction h q)

end AlgebraicCurve.Modulus
