/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mk_taylorCoeff_aeval.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mk_taylorCoeff_evalEval.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero.lean
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Basic
import Nyll.AlgebraicCurves.Places.Taylor.Taylor
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Mathlib.Algebra.Polynomial.Bivariate
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.LocalRingHenselLiftUnique
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Place mk taylor Coeff aeval
-/

section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_aeval

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace JetBridge

section TaylorHom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mk_taylorCoeff_add (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    (PowerSeries.mk fun n => taylorCoeff v t n (f + g))
      = (PowerSeries.mk fun n => taylorCoeff v t n f) + (PowerSeries.mk fun n => taylorCoeff v t n
        g) := by
  ext n
  rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    taylorCoeff_add v hv ht hf hg]

theorem mk_taylorCoeff_mul (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    (PowerSeries.mk fun n => taylorCoeff v t n (f * g))
      = (PowerSeries.mk fun n => taylorCoeff v t n f) * (PowerSeries.mk fun n => taylorCoeff v t n
        g) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, taylorCoeff_mul v hv ht hf hg n]
  exact Finset.sum_congr rfl fun x _ => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem mk_taylorCoeff_algebraMap (v : Place K F) (t : F) (c : K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (algebraMap K F c)) = PowerSeries.C c := by
  ext n
  rw [PowerSeries.coeff_mk, taylorCoeff_algebraMap, PowerSeries.coeff_C]

theorem aeval_mem_toValuationSubring (v : Place K F) {σ : Type*} (f : σ → F)
    (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    MvPolynomial.aeval f H ∈ v.toValuationSubring := by
  induction H using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact v.algebraMap_mem' c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p s hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf s)

theorem mk_taylorCoeff_aeval (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {σ : Type*} (f : σ → F) (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (MvPolynomial.aeval f H))
      = MvPolynomial.aeval (fun s => PowerSeries.mk fun n => taylorCoeff v t n (f s)) H := by
  induction H using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, mk_taylorCoeff_algebraMap]
    exact PowerSeries.C_eq_algebraMap (R := K) ▸ rfl
  | add p q hp hq =>
    rw [map_add, map_add, mk_taylorCoeff_add v hv ht (aeval_mem_toValuationSubring v f hf p)
      (aeval_mem_toValuationSubring v f hf q), hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      mk_taylorCoeff_mul v hv ht (aeval_mem_toValuationSubring v f hf p) (hf s), hp]

end TaylorHom

end JetBridge

theorem _root_.AlgebraicCurve.Place.mk_taylorCoeff_aeval {K F : Type*} [Field K] [Field F] [Algebra
  K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {σ : Type*} (f : σ → F) (hf : ∀ s, f s ∈ v.toValuationSubring) (H : MvPolynomial σ K) :
    (PowerSeries.mk fun n => taylorCoeff v t n (MvPolynomial.aeval f H))
      = MvPolynomial.aeval (fun s => PowerSeries.mk fun n => taylorCoeff v t n (f s)) H :=
  JetBridge.mk_taylorCoeff_aeval v hv ht f hf H
end AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_aeval
end ProofImplementation

end

section

/-!
# Place mk taylor Coeff eq C add X
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_eq_C_add_X

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem _root_.AlgebraicCurve.Place.mk_taylorCoeff_eq_C_add_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (_hv : v.IsRational) {z : F} (_hz : z ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1) :
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n z)
      = PowerSeries.C (v.evalAt z) + PowerSeries.X := by
  set t : F := z - algebraMap K F (v.evalAt z) with htdef
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at ht
    exact zero_ne_one ht
  have h1 : taylorRem v t z 1 = 1 := by
    change (taylorRem v t z 0 - _) * t⁻¹ = 1
    rw [taylorRem_zero, ← htdef, mul_inv_cancel₀ ht0]
  ext n
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  rcases n with _ | n
  · rw [taylorCoeff_zero]
    exact (add_zero (v.evalAt z)).symm
  · rw [taylorCoeff_succ_eq_taylorCoeff_taylorRem_one, h1, ← map_one (algebraMap K F),
      taylorCoeff_algebraMap]
    rcases n with _ | n
    · exact (zero_add (1 : K)).symm
    · rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.succ_ne_zero _),
        ite_eq_right (by omega), add_zero]
end AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_eq_C_add_X
end ProofImplementation

end

section

/-!
# Place mk taylor Coeff eval Eval
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_evalEval

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem _root_.AlgebraicCurve.Place.mk_taylorCoeff_evalEval
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K)) :
    (PowerSeries.mk fun n =>
        taylorCoeff v t n ((G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y))
      = (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
          (PowerSeries.mk fun n => taylorCoeff v t n z) (PowerSeries.mk fun n => taylorCoeff v t n
            y) := by
  let O := v.toValuationSubring
  let φ : O →+* PowerSeries K :=
    { toFun := fun f => PowerSeries.mk fun n => taylorCoeff v t n (f : F)
      map_one' := by
        ext n
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_one, OneMemClass.coe_one, ← map_one (algebraMap
          K F),
          taylorCoeff_algebraMap]
      map_mul' := fun f g => by
        ext n
        rw [PowerSeries.coeff_mk, MulMemClass.coe_mul, PowerSeries.coeff_mul,
          taylorCoeff_mul v hv ht f.2 g.2 n]
        simp only [PowerSeries.coeff_mk]
      map_zero' := by
        ext n
        rw [PowerSeries.coeff_mk, ZeroMemClass.coe_zero, taylorCoeff_zero_fun, map_zero]
      map_add' := fun f g => by
        ext n
        rw [PowerSeries.coeff_mk, AddMemClass.coe_add, taylorCoeff_add v hv ht f.2 g.2 n, map_add,
          PowerSeries.coeff_mk, PowerSeries.coeff_mk] }
  have hφ : ∀ f : O, φ f = PowerSeries.mk fun n => taylorCoeff v t n (f : F) := fun _ => rfl
  have hφC : φ.comp (algebraMap K O) = algebraMap K (PowerSeries K) := by
    refine RingHom.ext fun c => ?_
    ext n
    rw [RingHom.comp_apply, hφ, PowerSeries.coeff_mk, Place.coe_algebraMap,
      taylorCoeff_algebraMap, ← PowerSeries.C_eq_algebraMap, PowerSeries.coeff_C]
  have hOF : (algebraMap O F).comp (algebraMap K O) = algebraMap K F :=
    (IsScalarTower.algebraMap_eq K O F).symm
  have hsub : ∀ f : O, algebraMap O F f = (f : F) := fun _ => rfl
  have hA : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y
      = (((G.map (Polynomial.mapRingHom (algebraMap K O))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ : O) : F) := by
    rw [← hsub, ← Polynomial.map_mapRingHom_evalEval (algebraMap O F), Polynomial.map_map,
      Polynomial.mapRingHom_comp, hOF]
    rfl
  rw [hA, ← hφ, ← Polynomial.map_mapRingHom_evalEval φ, Polynomial.map_map,
    Polynomial.mapRingHom_comp, hφC]
  rfl
end AlgebraicCurves.Places.Proofs.Place_mk_taylorCoeff_evalEval
end ProofImplementation

end

section

/-!
# Place eval Eval C add X mk taylor Coeff eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem _root_.AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0) :
    (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C (v.evalAt z) + PowerSeries.X)
        (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) = 0 := by
  have h := mk_taylorCoeff_evalEval v hv ht hz hy G
  rw [hG, mk_taylorCoeff_eq_C_add_X v hv hz ht] at h
  rw [← h]
  ext n
  rw [PowerSeries.coeff_mk, taylorCoeff_zero_fun, map_zero]
end AlgebraicCurves.Places.Proofs.Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero
end ProofImplementation

end

section

/-!
# Place eq map mk taylor Coeff of eval Eval C add X eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem _root_.AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] {L : Type*} [Field L] (ι : K →+* L)
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (Y : PowerSeries L) (hY0 : PowerSeries.constantCoeff Y = ι (v.evalAt y))
    (hY : (G.map (Polynomial.mapRingHom (PowerSeries.C.comp ι))).evalEval
        (PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X) Y = 0) :
    Y = PowerSeries.map ι
          (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) := by
  set a : PowerSeries L := PowerSeries.map ι
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) with ha
  set x : PowerSeries L := PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X with hx
  set p : Polynomial (Polynomial (PowerSeries L)) := G.map (Polynomial.mapRingHom
    (PowerSeries.C.comp ι))
    with hp
  set f : Polynomial (PowerSeries L) := p.map (Polynomial.evalRingHom x) with hf
  have hfeval : ∀ b, f.eval b = p.evalEval x b := fun b => Polynomial.map_evalRingHom_eval x b p
  have hK := evalEval_C_add_X_mk_taylorCoeff_eq_zero v hv hz hy ht G hG
  have ha_root : f.IsRoot a := by
    rw [Polynomial.IsRoot, hfeval]
    have := congrArg (PowerSeries.map ι) hK
    rw [map_zero, ← Polynomial.map_mapRingHom_evalEval, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
      at this
    have hcomp : (PowerSeries.map ι).comp (algebraMap K (PowerSeries K)) = PowerSeries.C.comp ι :=
      by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, ← PowerSeries.C_eq_algebraMap, PowerSeries.map_C]
    rw [hcomp, map_add, PowerSeries.map_C, PowerSeries.map_X] at this
    exact this
  have hb_root : f.IsRoot Y := by rw [Polynomial.IsRoot, hfeval]; exact hY
  have ha0 : PowerSeries.constantCoeff a = ι (v.evalAt y) := by
    rw [ha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, taylorCoeff_zero]
  have hmem : Y - a ∈ IsLocalRing.maximalIdeal (PowerSeries L) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, map_sub, hY0, ha0, sub_self]
  have hunit : IsUnit (f.derivative.eval a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    rw [hf, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval, hp,
      Polynomial.derivative_map,
      ← Polynomial.map_mapRingHom_evalEval PowerSeries.constantCoeff, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
    have hcc : PowerSeries.constantCoeff.comp (PowerSeries.C.comp ι) = ι := by
      refine RingHom.ext fun c => ?_
      exact PowerSeries.constantCoeff_C (ι c)
    rw [hcc, hx, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero, ha0,
      Polynomial.map_mapRingHom_evalEval ι, _root_.map_ne_zero ι]
    exact hsep
  exact (IsLocalRing.hensel_lift_unique ha_root hb_root hmem hunit).symm
end AlgebraicCurves.Places.Proofs.Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
end ProofImplementation

open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.adicCompletionComapIntegers_coe

end
