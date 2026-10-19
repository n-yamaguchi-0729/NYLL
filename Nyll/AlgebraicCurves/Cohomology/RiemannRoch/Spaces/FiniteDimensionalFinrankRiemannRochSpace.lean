/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.MemRiemannRochSpaceHasValueZpowMul
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions

/-!
# Finite dimension and dimension formula for a rational Riemann–Roch space

Transport the existing polynomial description along the given field equivalence.
-/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteDimFinrankRRSpaceRingEquiv

noncomputable section

open _root_.AlgebraicCurve
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs
open ExistsMemRRSpaceAllHasValueZpow.AlgebraicCurve.Place
  ExistsMemRRSpaceAllHasValueZpow.AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve.RationalFunctionField

section ModelRR

variable {k F : Type*} [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [Field F] [Algebra k F]

omit [IsAlgClosed k] [DecidableEq (RatFunc k)] in
theorem riemannRochSpace_eq_map_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) :
    riemannRochSpace E
      = Submodule.map ((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv : RatFunc k →ₗ[k] F)
          (riemannRochSpace (Finsupp.mapDomain (Place.congrEquiv e he).symm E)) := by
  set E₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E with hE₀
  have hEE : E = Finsupp.mapDomain (Place.congrEquiv e he) E₀ :=
    (mapDomain_congrEquiv_mapDomain_symm e he E).symm
  ext f'
  obtain ⟨f, rfl⟩ := e.surjective f'
  constructor
  · intro h
    rw [hEE, mem_riemannRochSpace_mapDomain_congrEquiv_iff] at h
    exact ⟨f, h, rfl⟩
  · rintro ⟨g, hg, hge⟩
    simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, AlgEquiv.ofRingEquiv_apply,
      EmbeddingLike.apply_eq_iff_eq] at hge
    subst hge
    rw [hEE, mem_riemannRochSpace_mapDomain_congrEquiv_iff]
    exact hg

omit [DecidableEq (RatFunc k)] in
theorem finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) :
    FiniteDimensional k (riemannRochSpace E) ∧
      Module.finrank k (riemannRochSpace E) = (E.degree + 1).toNat := by
  classical
  set E₀ : Divisor k (RatFunc k) := Finsupp.mapDomain (Place.congrEquiv e he).symm E with hE₀
  have hEE : E = Finsupp.mapDomain (Place.congrEquiv e he) E₀ :=
    (mapDomain_congrEquiv_mapDomain_symm e he E).symm
  have hd : E₀.degree = E.degree := by rw [hEE, degree_mapDomain_congrEquiv]
  have hmap := riemannRochSpace_eq_map_of_ringEquiv e he E
  have : FiniteDimensional k (riemannRochSpace E₀) := LinearEquiv.finiteDimensional
    (riemannRochSpaceEquiv E₀)
  constructor
  · rw [hmap]
    infer_instance
  · rw [hmap, LinearEquiv.finrank_map_eq, finrank_riemannRochSpace E₀, hd]

end ModelRR

end AlgebraicCurve.RationalFunctionField

open AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
open FiniteDimFinrankRRSpaceRingEquiv.AlgebraicCurve.RationalFunctionField in
theorem _root_.AlgebraicCurve.finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) :
    FiniteDimensional k ↥(riemannRochSpace E) ∧
      Module.finrank k ↥(riemannRochSpace E) = (E.degree + 1).toNat := by
  classical
  exact finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv e he E

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteDimFinrankRRSpaceRingEquiv
