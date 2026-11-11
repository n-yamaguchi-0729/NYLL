/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Gauss specialization at an actual transcendental element

The given bivariate polynomial is specialized into the actual intermediate field generated
by the transcendental element. It is the evaluated leading coefficient times the minimal
polynomial in the outer variable. Evaluation at a coefficient-field element is a corollary.
-/

@[expose] public section

namespace Polynomial

open scoped Polynomial.Bivariate

/-- Specialization of an irreducible bivariate relation is the scalar multiple of the actual
minimal polynomial, with its evaluated leading coefficient retained. -/
theorem map_evalRingHom_eq_C_mul_minpoly_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {z : F} (hz : Transcendental K z) (y : F)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0) :
    (G.map (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
        (evalRingHom (⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ :
          IntermediateField.adjoin K ({z} : Set F))) =
      C (((G.leadingCoeff).map
        (algebraMap K (IntermediateField.adjoin K ({z} : Set F)))).eval
          ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩) *
        minpoly (IntermediateField.adjoin K ({z} : Set F)) y := by
  set zz : IntermediateField.adjoin K ({z} : Set F) :=
    ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ with hzzdef
  have hzzF : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F zz = z := rfl
  set φ : K[X] →+* IntermediateField.adjoin K ({z} : Set F) :=
    (evalRingHom zz).comp (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))
    with hφdef
  have hφapply : ∀ p : K[X], φ p = aeval zz p := by
    intro p
    simp only [hφdef, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_evalRingHom,
      eval_map_algebraMap]
  have hψ : ∀ p : K[X], RatFunc.algEquivOfTranscendental z hz (algebraMap K[X] (RatFunc K) p) = φ p
    := by
    intro p
    rw [RatFunc.algEquivOfTranscendental_algebraMap, hφapply]
    rfl
  have hφinj : Function.Injective φ := by
    intro p q hpq
    rw [← hψ, ← hψ] at hpq
    exact IsFractionRing.injective K[X] (RatFunc K)
      ((RatFunc.algEquivOfTranscendental z hz).injective hpq)
  have hGz : (G.map (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
      (evalRingHom zz) = G.map φ := Polynomial.map_map _ _ _
  have hφF : (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).comp φ
      = (evalRingHom z).comp (mapRingHom (algebraMap K F)) := by
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_C, eval_C]
      rw [hφapply, aeval_C]
      exact (IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({z} : Set F)) F k).symm
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_X, eval_X]
      rw [hφapply, aeval_X]
      exact hzzF
  have hroot : aeval y (G.map φ) = 0 := by
    rw [aeval_def, eval₂_map, hφF, ← eval_map, ← Polynomial.map_map, map_evalRingHom_eval]
    exact hG
  have hdeg : G.natDegree ≠ 0 := by
    intro h0
    have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have h1 : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F (φ (G.coeff 0)) = 0 := by
      rw [← hroot, hGC, Polynomial.map_C, aeval_C, coeff_C_zero]
    have h2 : φ (G.coeff 0) = 0 := by
      rwa [map_eq_zero_iff _ (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).injective]
        at h1
    have hc : G.coeff 0 = 0 := hφinj (by rw [h2, map_zero])
    exact hGirr.ne_zero (by rw [hGC, hc, map_zero])
  have hprim : G.IsPrimitive := hGirr.isPrimitive hdeg
  have hirrQ : Irreducible (G.map (algebraMap K[X] (RatFunc K))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mp hGirr
  have hmapψ : Polynomial.mapEquiv (RatFunc.algEquivOfTranscendental z hz).toRingEquiv
      (G.map (algebraMap K[X] (RatFunc K))) = G.map φ := by
    rw [mapEquiv_apply, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, ← hψ p]
    rfl
  have hirr : Irreducible (G.map φ) := by
    rw [← hmapψ]
    exact (MulEquiv.irreducible_iff _).mpr hirrQ
  exact hGz.trans ((minpoly.Irreducible.eq_minpoly hirr hroot).trans
    (congrArg (fun c => C c * minpoly (IntermediateField.adjoin K ({z} : Set F)) y)
      (leadingCoeff_map_of_injective hφinj G)))

/-- Evaluate the same Gauss-specialization equality at an element of the generated field. -/
theorem eval_map_evalRingHom_eq_mul_minpoly_of_transcendental
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {z : F} (hz : Transcendental K z) (y : F)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (c : IntermediateField.adjoin K ({z} : Set F)) :
    ((G.map (Polynomial.mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
        (evalRingHom (⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ :
          IntermediateField.adjoin K ({z} : Set F)))).eval c
      = ((G.leadingCoeff).map (algebraMap K (IntermediateField.adjoin K ({z} : Set F)))).eval
            ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
        * (minpoly (IntermediateField.adjoin K ({z} : Set F)) y).eval c := by
  rw [map_evalRingHom_eq_C_mul_minpoly_of_transcendental hz y G hGirr hG,
    eval_mul, eval_C]

end Polynomial
