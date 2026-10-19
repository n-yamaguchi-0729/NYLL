/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Divisors.Modulus.AdditiveModulus

/-!
# The explicit additive local symbol

The actual residue expression `Res_v(f dlog(g))` gives the unique local
symbol for the additive rational function `f`. The full modulus and the
reciprocity law come from the proved additive-modulus construction.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

local instance : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
local instance : Nontrivial Ω[F⁄K] := IsCurveOver.instNontrivialKaehler
local instance : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : HasCanonicalLocalResidueKStar K F :=
  _root_.AlgebraicCurve.instHasCanonicalLocalResidueKStar

/-- The additive local symbol is the actual residue of `f dlog(g)`. -/
def additiveResidueSymbol (f : F) (v : Place K F) : Additive Fˣ →+ K where
  toFun g := Algebra.trace K v.ResidueField
    (v.localResidue (f * v.differentialCoeff
      (dlog K ((Additive.toMul g : Fˣ) : F))))
  map_zero' := by
    change Algebra.trace K v.ResidueField
      (v.localResidue (f * v.differentialCoeff (dlog K (1 : F)))) = 0
    rw [dlog_one, v.differentialCoeff_zero, mul_zero, map_zero, map_zero]
  map_add' g h := by
    change Algebra.trace K v.ResidueField
      (v.localResidue (f * v.differentialCoeff (dlog K
        (((Additive.toMul g : Fˣ) : F) * ((Additive.toMul h : Fˣ) : F))))) = _
    rw [dlog_mul (Additive.toMul g).ne_zero (Additive.toMul h).ne_zero,
      Place.differentialCoeff_add, mul_add, map_add, map_add]

/-- Evaluation of the concrete symbol on a nonzero rational function. -/
theorem additiveResidueSymbol_apply (f : F) (v : Place K F) (g : Fˣ) :
    additiveResidueSymbol f v (Additive.ofMul g) = Algebra.trace K v.ResidueField
      (v.localResidue (f * v.differentialCoeff (dlog K (g : F)))) := rfl

/-- The full pole-order-plus-one modulus obtained by the residue construction. -/
def additiveModulus (f : F) : Modulus K F := (exists_additive_modulus (K := K) f).choose

/-- Its multiplicities are the explicit additive pole bounds. -/
theorem additiveModulus_apply (f : F) (v : Place K F) :
    additiveModulus (K := K) f v =
      if 0 ≤ v.ord f then 0 else (-v.ord f).toNat + 1 :=
  (exists_additive_modulus (K := K) f).choose_spec.1 v

/-- The constructed divisor really is a modulus for additive evaluation. -/
theorem hasModulus_additiveModulus (f : F) :
    (additiveModulus (K := K) f).HasModulus (fun v => v.evalAt f) :=
  (exists_additive_modulus (K := K) f).choose_spec.2

/-- The residue formula satisfies all local-symbol axioms, including the
global reciprocity law and vanishing on the full higher-unit filtration. -/
theorem isLocalSymbol_additiveResidueSymbol (f : F) :
    (additiveModulus (K := K) f).IsLocalSymbol (fun v => v.evalAt f)
      (additiveResidueSymbol f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v g hg
    rw [additiveResidueSymbol_apply]
    by_cases hv : 0 ≤ v.ord f
    · rw [v.trace_localResidue_mul_dlog_of_integral
        (v.mem_toValuationSubring_of_ord_nonneg hv) g, hg.ord_eq_zero, zero_zsmul]
    · rw [additiveModulus_apply, ite_eq_right hv] at hg
      have hbound : -(((-v.ord f).toNat : ℕ) : ℤ) ≤ v.ord f := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [hg.localResidue_mul_dlog_eq_zero hbound, map_zero]
  · intro v hv g
    have hregular : 0 ≤ v.ord f := by
      by_contra hn
      rw [additiveModulus_apply, ite_eq_right hn] at hv
      omega
    rw [additiveResidueSymbol_apply]
    exact v.trace_localResidue_mul_dlog_of_integral
      (v.mem_toValuationSubring_of_ord_nonneg hregular) g
  · intro g
    exact finsum_trace_localResidue_mul_dlog (K := K) f g

/-- The abstract symbol constructed by approximation equals the actual
residue formula. This is equality of homomorphisms, not just of scalar values. -/
theorem localSymbol_additiveModulus_eq_residue (f : F) :
    (hasModulus_additiveModulus (K := K) f).localSymbol = additiveResidueSymbol f :=
  (hasModulus_additiveModulus (K := K) f).isLocalSymbol.unique
    (isLocalSymbol_additiveResidueSymbol f)

end AlgebraicCurve.Modulus
