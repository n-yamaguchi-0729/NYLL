/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Logarithmic.PrincipalUnitDifferential
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolExistence
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremFunctionField

/-!
# A modulus for additive rational functions

Over an algebraically closed field, a rational function with values in the
additive group has a modulus supported at its poles, with multiplicity the
pole order plus one. The proof uses the actual residue theorem for smooth
function fields and the principal-unit differential estimate. It also gives
the unique local symbols through the proved modulus construction.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Logarithmic differentiation as a homomorphism on actual nonzero functions. -/
def logarithmicDifferential : Additive Fˣ →+ Ω[F⁄K] where
  toFun g := dlog K ((Additive.toMul g : Fˣ) : F)
  map_zero' := dlog_one
  map_add' g h := dlog_mul (Additive.toMul g).ne_zero (Additive.toMul h).ne_zero

/-- Integral powers act as integer multiples under logarithmic differentiation. -/
theorem logarithmicDifferential_zpow (g : Fˣ) (n : ℤ) :
    dlog K ((g : F) ^ n) = n • dlog K (g : F) := by
  have h := (logarithmicDifferential (K := K) (F := F)).map_zsmul
    n (Additive.ofMul g)
  simpa only [logarithmicDifferential, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    toMul_zsmul, toMul_ofMul, Units.val_zpow_eq_zpow_val] using h

variable [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

local instance : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
local instance : Nontrivial Ω[F⁄K] := IsCurveOver.instNontrivialKaehler
local instance : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : HasCanonicalLocalResidueKStar K F := instHasCanonicalLocalResidueKStar

namespace Place

/-- Residue of `f dlog(g)` at a point where the additive rational function is
regular. This identifies the residue expression with divisor evaluation. -/
theorem trace_localResidue_mul_dlog_of_integral (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (g : Fˣ) :
    Algebra.trace K v.ResidueField
      (v.localResidue (f * v.differentialCoeff (dlog K (g : F)))) =
        v.ord (g : F) • v.evalAt f := by
  let n : ℤ := v.ord (g : F)
  let u : F := (g : F) * v.uniformizer ^ (-n)
  have hu : u ≠ 0 := mul_ne_zero g.ne_zero (zpow_ne_zero _ v.uniformizer_ne_zero)
  have huord : v.ord u = 0 := by
    dsimp only [u]
    rw [v.ord_mul g.ne_zero (zpow_ne_zero _ v.uniformizer_ne_zero),
      v.ord_zpow, v.ord_uniformizer, mul_one]
    exact add_neg_cancel _
  have hgu : (g : F) = u * v.uniformizer ^ n := by
    dsimp only [u]
    rw [mul_assoc, ← zpow_add₀ v.uniformizer_ne_zero, neg_add_cancel,
      zpow_zero, mul_one]
  have hpow := logarithmicDifferential_zpow (K := K)
    (Units.mk0 v.uniformizer v.uniformizer_ne_zero) n
  simp only [Units.val_mk0] at hpow
  have hcoordlog : v.differentialCoeff (dlog K v.uniformizer) =
      v.uniformizer⁻¹ := by
    rw [dlog, v.differentialCoeff_smul, ← v.dCoord_eq,
      v.differentialCoeff_dCoord, mul_one]
  have hcoeff : v.differentialCoeff (dlog K (g : F)) =
      v.differentialCoeff (dlog K u) + n • v.uniformizer⁻¹ := by
    rw [hgu, dlog_mul hu (zpow_ne_zero _ v.uniformizer_ne_zero), hpow,
      Place.differentialCoeff_add, ← Int.cast_smul_eq_zsmul F n,
      v.differentialCoeff_smul, hcoordlog]
    rw [zsmul_eq_mul]
  have humem : u ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg (by rw [huord])
  have huinv : u⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg (by rw [v.ord_inv, huord, neg_zero])
  have hregular : v.localResidue (f * v.differentialCoeff (dlog K u)) = 0 := by
    apply v.localResidue_of_mem
    rw [dlog, v.differentialCoeff_smul]
    exact mul_mem hf (mul_mem huinv (v.differentialCoeff_D_mem_of_integral humem))
  have hsimple : v.uniformizer * (f * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [mul_left_comm, mul_inv_cancel₀ v.uniformizer_ne_zero, mul_one]
    exact hf
  have hres : v.localResidue (f * v.uniformizer⁻¹) =
      IsLocalRing.residue _ (⟨f, hf⟩ : v.toValuationSubring) := by
    rw [v.localResidue_simplePole _ hsimple]
    congr 1
    apply Subtype.ext
    exact (mul_left_comm _ _ _).trans
      (by rw [mul_inv_cancel₀ v.uniformizer_ne_zero, mul_one])
  have hv : v.IsRational := (v.isRational_iff_deg_eq_one).mpr
    (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hdeg : Module.finrank K v.ResidueField = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hscale : f * (n • v.uniformizer⁻¹) = n • (f * v.uniformizer⁻¹) := by
    simp only [zsmul_eq_mul]
    ring
  rw [hcoeff, mul_add, hscale, map_add, hregular, zero_add, map_zsmul,
    hres, ← v.algebraMap_evalAt hv hf, map_zsmul, Algebra.trace_algebraMap,
    hdeg, one_smul]

end Place

local instance : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver

open AlgebraicCurves.Differentials.Residues.Proofs in
open ResidueTheorem_functionField_of_smoothOfRelativeDimension_one.FFP in
/-- The global residue theorem applied to the explicit additive-symbol formula. -/
theorem finsum_trace_localResidue_mul_dlog (f : F) (g : Fˣ) :
    ∑ᶠ v : Place K F, Algebra.trace K v.ResidueField
      (v.localResidue (f * v.differentialCoeff (dlog K (g : F)))) = 0 := by
  by_cases hzero : dlog K (g : F) = 0
  · apply finsum_eq_zero_of_forall_eq_zero
    intro v
    rw [hzero, v.differentialCoeff_zero, mul_zero, map_zero, map_zero]
  · have hrec := residueTheorem_of_isCurveOver K F hzero f
    rw [weilOfKaehler_apply] at hrec
    exact hrec

namespace Modulus

/-- A nonzero additive rational function has the explicit modulus with
pole-order-plus-one multiplicities. All values are actual residue evaluations. -/
theorem exists_additive_modulus_of_ne_zero (f : F) (hf : f ≠ 0) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = if 0 ≤ v.ord f then 0 else (-v.ord f).toNat + 1) ∧
      D.HasModulus (fun v => v.evalAt f) := by
  classical
  obtain ⟨E, hE, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  let D : Modulus K F := E.mapRange
    (fun n : ℤ => if 0 ≤ n then 0 else (-n).toNat + 1)
    (by rw [ite_eq_left le_rfl])
  have hD (v : Place K F) :
      D v = if 0 ≤ v.ord f then 0 else (-v.ord f).toNat + 1 := by
    dsimp only [D]
    rw [Finsupp.mapRange_apply, hE v]
  refine ⟨D, hD, ?_⟩
  intro g hg
  have hterm (v : Place K F) : v.ord (g : F) • v.evalAt f =
      Algebra.trace K v.ResidueField
        (v.localResidue (f * v.differentialCoeff (dlog K (g : F)))) := by
    by_cases hv : 0 ≤ v.ord f
    · exact (v.trace_localResidue_mul_dlog_of_integral
        (v.mem_toValuationSubring_of_ord_nonneg hv) g).symm
    · have hDv : D v ≠ 0 := by rw [hD, ite_eq_right hv]; omega
      have hcong : v.CongruentOne ((-v.ord f).toNat + 1) (g : F) := by
        simpa only [hD, ite_eq_right hv] using hg.2 v hDv
      have hbound : -(((-v.ord f).toNat : ℕ) : ℤ) ≤ v.ord f := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [hg.ord_eq_zero v hDv, zero_zsmul,
        hcong.localResidue_mul_dlog_eq_zero hbound, map_zero]
  rw [finsum_congr hterm]
  exact finsum_trace_localResidue_mul_dlog f g

/-- Every additive rational function has a full modulus. -/
theorem exists_additive_modulus (f : F) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = if 0 ≤ v.ord f then 0 else (-v.ord f).toNat + 1) ∧
      D.HasModulus (fun v => v.evalAt f) := by
  by_cases hf : f = 0
  · subst f
    refine ⟨0, ?_, ?_⟩
    · intro v
      rw [Finsupp.zero_apply, v.ord_zero, ite_eq_left le_rfl]
    · intro g _hg
      apply finsum_eq_zero_of_forall_eq_zero
      intro v
      have heval : v.evalAt (0 : F) = 0 := by
        rw [v.evalAt_of_mem (zero_mem _)]
        change v.residueInv (IsLocalRing.residue v.toValuationSubring 0) = 0
        rw [map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
      change v.ord (g : F) • v.evalAt (0 : F) = 0
      rw [heval, zsmul_zero]
  · exact exists_additive_modulus_of_ne_zero f hf

/-- The additive rational map has unique local symbols, with an actual
modulus supplied by its finite pole divisor. -/
theorem exists_additive_localSymbol (f : F) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = if 0 ≤ v.ord f then 0 else (-v.ord f).toNat + 1) ∧
      ∃! σ : Place K F → Additive Fˣ →+ K,
        D.IsLocalSymbol (fun v => v.evalAt f) σ := by
  obtain ⟨D, hD, hm⟩ := exists_additive_modulus (K := K) f
  exact ⟨D, hD, (hasModulus_iff_existsUnique_localSymbol D _).mp hm⟩

end Modulus

end AlgebraicCurve
