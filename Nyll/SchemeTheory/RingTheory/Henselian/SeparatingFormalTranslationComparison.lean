/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FiniteSeparableFormalLiftEmbedding
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Comparing actual formal translations by a separating parameter

Agreement on a separating parameter and on the residue embedding determines
a formal field homomorphism. Consequently every actual formal deformation
is obtained from a fixed translation by substituting the actual displacement
of that parameter. No compatibility of the two deformations is assumed.
-/

noncomputable section

namespace PowerSeries

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L]

/-- Two formal lifts of the same residue embedding agree if they agree on
a transcendental parameter over which the source is finite separable. -/
theorem formalLift_ext_of_separating_parameter
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (i : F →ₐ[K] L) (θ ρ : F →ₐ[K] PowerSeries L)
    (htheta : θ t = ρ t)
    (hθ0 : constantCoeff.comp θ.toRingHom = i.toRingHom)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom) : θ = ρ := by
  let R : IntermediateField K F := IntermediateField.adjoin K {t}
  let e : RatFunc K ≃ₐ[K] R := RatFunc.algEquivOfTranscendental t ht
  have heX : ((e RatFunc.X : R) : F) = t :=
    RatFunc.algEquivOfTranscendental_X t ht
  have hrat : (θ.comp R.val).comp e.toAlgHom = (ρ.comp R.val).comp e.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change θ ((e RatFunc.X : R) : F) = ρ ((e RatFunc.X : R) : F)
    rw [heX]
    exact htheta
  have hbase : θ.toRingHom.comp (algebraMap R F) =
      ρ.toRingHom.comp (algebraMap R F) := by
    apply RingHom.ext
    intro x
    have h := AlgHom.congr_fun hrat (e.symm x)
    change θ ((e (e.symm x) : R) : F) = ρ ((e (e.symm x) : R) : F) at h
    rw [e.apply_symm_apply] at h
    exact h
  let τ : R →+* PowerSeries L := ρ.toRingHom.comp (algebraMap R F)
  have hτ : constantCoeff.comp τ = i.toRingHom.comp (algebraMap R F) := by
    change constantCoeff.comp (ρ.toRingHom.comp (algebraMap R F)) = _
    rw [← RingHom.comp_assoc, hρ0]
  obtain ⟨φ, _hφ, hUnique⟩ :=
    existsUnique_formalLift_finiteSeparable_embedding (R := R) i.toRingHom τ hτ
  apply AlgHom.coe_ringHom_injective
  exact (hUnique θ.toRingHom ⟨hbase, hθ0⟩).trans
    (hUnique ρ.toRingHom ⟨rfl, hρ0⟩).symm

/-- Every actual formal lift is obtained by substituting the displacement
of the separating parameter into the fixed global formal translation.
The coefficient embedding and the parameter displacement are both actual
maps, and equality follows from finite-separable lifting uniqueness. -/
theorem formalTranslation_substitution
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = C t + X)
    (hσ0 : constantCoeff.comp σ.toRingHom = RingHom.id F)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom) (f : F) :
    subst (ρ t - C (i t)) (map i.toRingHom (σ f)) = ρ f := by
  let δ : PowerSeries L := ρ t - C (i t)
  have hδ : constantCoeff δ = 0 := by
    change constantCoeff (ρ t - C (i t)) = 0
    have ht0 : constantCoeff (ρ t) = i t := RingHom.congr_fun hρ0 t
    rw [map_sub, constantCoeff_C, ht0, sub_self]
  let S : PowerSeries L →ₐ[L] PowerSeries L :=
    substAlgHom (HasSubst.of_constantCoeff_zero' hδ)
  let θ : F →ₐ[K] PowerSeries L :=
    (S.restrictScalars K).comp ((mapAlgHom i).comp σ)
  have hθt : θ t = ρ t := by
    change S (map i.toRingHom (σ t)) = ρ t
    rw [hσt, map_add, map_C, map_X, map_add]
    have hC : S (C (i t)) = C (i t) := S.commutes (i t)
    have hX : S X = δ := substAlgHom_X (HasSubst.of_constantCoeff_zero' hδ)
    change S (C (i t)) + S X = ρ t
    rw [hC, hX]
    change C (i t) + (ρ t - C (i t)) = ρ t
    abel
  have hθ0 : constantCoeff.comp θ.toRingHom = i.toRingHom := by
    apply RingHom.ext
    intro x
    change constantCoeff (S (map i.toRingHom (σ x))) = i x
    change constantCoeff
      (substAlgHom (HasSubst.of_constantCoeff_zero' hδ) (map i.toRingHom (σ x))) = i x
    rw [coe_substAlgHom]
    change MvPowerSeries.constantCoeff (subst δ (map i.toRingHom (σ x))) = i x
    rw [constantCoeff_subst_of_constantCoeff_zero hδ]
    change i (constantCoeff (σ x)) = i x
    exact congrArg i (RingHom.congr_fun hσ0 x)
  have hθ : θ = ρ :=
    formalLift_ext_of_separating_parameter t ht i θ ρ hθt hθ0 hρ0
  have h := AlgHom.congr_fun hθ f
  change substAlgHom (HasSubst.of_constantCoeff_zero' hδ)
    (map i.toRingHom (σ f)) = ρ f at h
  rw [coe_substAlgHom] at h
  exact h

end PowerSeries
