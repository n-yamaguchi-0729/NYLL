/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Places.RingEquiv

/-!
# Transport of principal degree-zero divisors

Transporting a place along a constant-field-preserving equivalence preserves both
its order and its residue degree. This transports principal divisors of degree zero.
-/

public section

namespace AlgebraicCurve.Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include e he

/-- Principality of all degree-zero divisors is preserved by transport of the function field. -/
theorem forall_isPrincipal_of_ringEquiv
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal)
    (D' : Divisor K F') (hD' : Divisor.degree D' = 0) : D'.IsPrincipal := by
  classical
  set c := Place.congrEquiv e he with hc
  set D : Divisor K F := Finsupp.equivMapDomain c.symm D' with hD_def
  have happly : ∀ v' : Place K F', D (c.symm v') = D' v' := by
    intro v'
    rw [hD_def, Finsupp.equivMapDomain_apply, Equiv.symm_symm, c.apply_symm_apply]
  have hdeg : Divisor.degree D = 0 := by
    rw [← hD']
    rw [hD_def]
    have h1 : Divisor.degree (Finsupp.equivMapDomain c.symm D')
        = (Finsupp.equivMapDomain c.symm D').sum fun v n => n * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    have h2 : Divisor.degree D' = D'.sum fun v n => n * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    rw [h1, h2, Finsupp.sum_equivMapDomain]
    refine Finsupp.sum_congr fun v' _ => ?_
    congr 1
    exact_mod_cast congrArg (Nat.cast (R := ℤ))
      (Place.deg_congrRingEquiv e.symm (Place.symm_algebraMap_comm e he) v')
  obtain ⟨f, hf, hf_ord⟩ := h D hdeg
  refine ⟨e f, fun h0 => hf (e.injective (h0.trans e.map_zero.symm)), fun v' => ?_⟩
  calc D' v' = D (c.symm v') := (happly v').symm
    _ = (c.symm v').ord f := hf_ord (c.symm v')
    _ = (Place.congrRingEquiv e he (c.symm v')).ord (e f) :=
        (Place.ord_congrRingEquiv e he (c.symm v') f).symm
    _ = v'.ord (e f) := by rw [show Place.congrRingEquiv e he (c.symm v') = v' from
        c.apply_symm_apply v']


end AlgebraicCurve.Pic0
