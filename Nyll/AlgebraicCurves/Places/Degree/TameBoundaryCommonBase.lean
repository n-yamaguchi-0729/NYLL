/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.TameCompletedTensorSplitting

/-! # One completed base for all equally ramified boundary factors

The exact-contact factorization uses one common boundary order. The normalized
Laurent equivalences at those points therefore agree on the whole original
base completion, not just its parameter. The finite-flat interior block is
not split or subjected to this equal-contact hypothesis.
-/

noncomputable section

open scoped Topology AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicCurve.Place

variable {K B F : Type*} [Field K] [Field B] [Field F] [Algebra K B] [Algebra K F]
  [Algebra B F] [IsScalarTower K B F]
  [Algebra.IsIntegral B F]
  [HasPrincipalDivisors K F]

private theorem continuous_fiberCompletion_algebraMap
    (v : Place K B) (w : v.fiber F) :
    Continuous (algebraMap v.adicCompletion w.val.adicCompletion) := by
  rcases w with ⟨w, hw⟩
  have hv : w.restrict B = v := Place.mem_fiber.mp hw
  subst v
  exact continuous_adicCompletionComap B w

/-- Boundary normalizations with the same exact parameter image induce the
same native completed-base map. Thus all their split tensor factors can use
one and the same scalar algebra on the Laurent coefficient field. -/
theorem normalized_boundary_completed_base_eq
    (v : Place K B) (w₁ w₂ : v.fiber F)
    (E₁ : w₁.val.adicCompletion ≃ₐ[K] LaurentSeries K)
    (E₂ : w₂.val.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE₁ : Continuous E₁) (hE₂ : Continuous E₂)
    (p : RatFunc K ≃ₐ[K] B) (e : ℕ)
    (hs₁ : E₁ (algebraMap F w₁.val.adicCompletion
      (algebraMap B F (p RatFunc.X))) = HahnSeries.single (e : ℤ) (1 : K))
    (hs₂ : E₂ (algebraMap F w₂.val.adicCompletion
      (algebraMap B F (p RatFunc.X))) = HahnSeries.single (e : ℤ) (1 : K)) :
    E₁.toRingHom.comp (algebraMap v.adicCompletion w₁.val.adicCompletion) =
      E₂.toRingHom.comp (algebraMap v.adicCompletion w₂.val.adicCompletion) := by
  let j₁ : B →ₐ[K] LaurentSeries K :=
    E₁.toAlgHom.comp ((IsScalarTower.toAlgHom K F w₁.val.adicCompletion).comp
      (IsScalarTower.toAlgHom K B F))
  let j₂ : B →ₐ[K] LaurentSeries K :=
    E₂.toAlgHom.comp ((IsScalarTower.toAlgHom K F w₂.val.adicCompletion).comp
      (IsScalarTower.toAlgHom K B F))
  have hjq : j₁.comp p.toAlgHom = j₂.comp p.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    exact hs₁.trans hs₂.symm
  have hj : j₁ = j₂ := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := p.surjective x
    exact AlgHom.congr_fun hjq y
  apply RingHom.ext
  intro a
  refine (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap B
    v.heightOneSpectrum).induction_on a ?_ ?_
  · exact isClosed_eq
      (hE₁.comp (continuous_fiberCompletion_algebraMap v w₁))
      (hE₂.comp (continuous_fiberCompletion_algebraMap v w₂))
  · intro x
    change E₁ (algebraMap v.adicCompletion w₁.val.adicCompletion
      (algebraMap B v.adicCompletion x)) =
        E₂ (algebraMap v.adicCompletion w₂.val.adicCompletion
          (algebraMap B v.adicCompletion x))
    rw [← IsScalarTower.algebraMap_apply B v.adicCompletion
      w₁.val.adicCompletion, ← IsScalarTower.algebraMap_apply B
      v.adicCompletion w₂.val.adicCompletion]
    rw [IsScalarTower.algebraMap_apply B F w₁.val.adicCompletion,
      IsScalarTower.algebraMap_apply B F w₂.val.adicCompletion]
    exact AlgHom.congr_fun hj x

end AlgebraicCurve.Place
