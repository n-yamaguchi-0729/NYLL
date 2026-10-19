/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveQuotientLifting
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveSplittingLift
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations

/-!
# Compatible splittings of successive module reductions

For ideals `J ≤ I`, the native double reduction of a module is identified
with its reduction modulo `I`. This identification is computed on the
actual quotient maps and is natural in linear maps. A prescribed splitting
modulo `I` is then extended to a splitting modulo `J`, using projectivity
over `R/J`, with compatibility along the original quotient maps.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R]

/-- The actual iterated quotient identifies with the smaller quotient. -/
def doubleReductionEquiv (J I : Ideal R) (hJI : J ≤ I)
    (M : Type v) [AddCommGroup M] [Module R M] :
    ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
      (I • (⊤ : Submodule R (M ⧸ (J • (⊤ : Submodule R M)))))) ≃ₗ[R]
        M ⧸ (I • (⊤ : Submodule R M)) := by
  let U : Submodule R M := J • (⊤ : Submodule R M)
  let V : Submodule R M := I • (⊤ : Submodule R M)
  have hmap : V.map U.mkQ = I • (⊤ : Submodule R (M ⧸ U)) := by
    change (I • (⊤ : Submodule R M)).map U.mkQ = I • (⊤ : Submodule R (M ⧸ U))
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  exact (Submodule.quotEquivOfEq _ _ hmap.symm).trans
    (Submodule.quotientQuotientEquivQuotient U V (Submodule.smul_mono_left hJI))

theorem doubleReductionEquiv_mk (J I : Ideal R) (hJI : J ≤ I)
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : M ⧸ (J • (⊤ : Submodule R M))) :
    doubleReductionEquiv J I hJI M (Submodule.Quotient.mk x) =
      Submodule.factor (Submodule.smul_mono_left hJI) x := by
  rw [doubleReductionEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact Submodule.quotientQuotientEquivQuotientAux_mk _ _ _ x

theorem doubleReductionEquiv_mk_mk (J I : Ideal R) (hJI : J ≤ I)
    (M : Type v) [AddCommGroup M] [Module R M] (x : M) :
    doubleReductionEquiv J I hJI M
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x := by
  rw [doubleReductionEquiv_mk]
  exact Submodule.factor_mk _ x

/-- The explicit iterated-quotient identification commutes with the
reduction of the original linear map. -/
theorem doubleReductionEquiv_naturality (J I : Ideal R) (hJI : J ≤ I)
    {F : Type v} [AddCommGroup F] [Module R F]
    {P : Type w} [AddCommGroup P] [Module R P] (f : F →ₗ[R] P)
    (x : (F ⧸ (J • (⊤ : Submodule R F))) ⧸
      (I • (⊤ : Submodule R (F ⧸ (J • (⊤ : Submodule R F)))))) :
    doubleReductionEquiv J I hJI P (reduceMap I (reduceMap J f) x) =
      reduceMap I f (doubleReductionEquiv J I hJI F x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro y
  refine Submodule.Quotient.induction_on _ y ?_
  intro z
  rw [reduceMap_mk, reduceMap_mk, doubleReductionEquiv_mk_mk,
    doubleReductionEquiv_mk_mk, reduceMap_mk]

/-- A surjection stays surjective after the actual module reduction. -/
theorem reduceMap_surjective (I : Ideal R)
    {F : Type v} [AddCommGroup F] [Module R F]
    {P : Type w} [AddCommGroup P] [Module R P]
    (f : F →ₗ[R] P) (hf : Function.Surjective f) : Function.Surjective (reduceMap I f) := by
  intro y
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
  obtain ⟨x, rfl⟩ := hf p
  exact ⟨Submodule.Quotient.mk x, reduceMap_mk I f x⟩

/-- A quotient-ring projective stage supplies the next splitting, with
compatibility along the native transition maps. -/
theorem exists_compatible_quotient_splitting (J I : Ideal R) (hJI : J ≤ I)
    {F : Type v} [AddCommGroup F] [Module R F]
    {P : Type w} [AddCommGroup P] [Module R P]
    [Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P)))]
    (f : F →ₗ[R] P) (hf : Function.Surjective f)
    (s₀ : P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R] F ⧸ (I • (⊤ : Submodule R F)))
    (hs₀ : (reduceMap I f).comp s₀ = LinearMap.id) :
    ∃ s : P ⧸ (J • (⊤ : Submodule R P)) →ₗ[R] F ⧸ (J • (⊤ : Submodule R F)),
      (reduceMap J f).comp s = LinearMap.id ∧
      (Submodule.factor (Submodule.smul_mono_left hJI)).comp s =
        s₀.comp (Submodule.factor (Submodule.smul_mono_left hJI)) := by
  let FJ : Type v := F ⧸ (J • (⊤ : Submodule R F))
  let PJ : Type w := P ⧸ (J • (⊤ : Submodule R P))
  let eF : (FJ ⧸ (I • (⊤ : Submodule R FJ))) ≃ₗ[R]
      F ⧸ (I • (⊤ : Submodule R F)) := doubleReductionEquiv J I hJI F
  let eP : (PJ ⧸ (I • (⊤ : Submodule R PJ))) ≃ₗ[R]
      P ⧸ (I • (⊤ : Submodule R P)) := doubleReductionEquiv J I hJI P
  let s₀' : PJ ⧸ (I • (⊤ : Submodule R PJ)) →ₗ[R]
      FJ ⧸ (I • (⊤ : Submodule R FJ)) :=
    eF.symm.toLinearMap.comp (s₀.comp eP.toLinearMap)
  have hs₀' : (reduceMap I (reduceMap J f)).comp s₀' = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply eP.injective
    calc
      eP (reduceMap I (reduceMap J f) (s₀' x)) = reduceMap I f (eF (s₀' x)) :=
        doubleReductionEquiv_naturality J I hJI f (s₀' x)
      _ = reduceMap I f (s₀ (eP x)) :=
        congrArg (reduceMap I f) (eF.apply_symm_apply (s₀ (eP x)))
      _ = eP x := LinearMap.congr_fun hs₀ (eP x)
  have hJFJ : Module.IsTorsionBySet R FJ J :=
    Module.isTorsionBySet_quotient_ideal_smul F J
  obtain ⟨s, hs, hrec⟩ := exists_splitting_lift_of_projective_quotient J I hJFJ
    (reduceMap J f) (reduceMap_surjective J f hf) s₀' hs₀'
  refine ⟨s, hs, ?_⟩
  apply LinearMap.ext
  intro p
  have hp := congrArg eF (LinearMap.congr_fun hrec p)
  calc
    Submodule.factor (Submodule.smul_mono_left hJI) (s p) =
        eF (Submodule.Quotient.mk (s p)) := (doubleReductionEquiv_mk J I hJI F (s p)).symm
    _ = eF (s₀' (Submodule.Quotient.mk p)) := hp
    _ = s₀ (eP (Submodule.Quotient.mk p)) :=
      eF.apply_symm_apply (s₀ (eP (Submodule.Quotient.mk p)))
    _ = s₀ (Submodule.factor (Submodule.smul_mono_left hJI) p) :=
      congrArg s₀ (doubleReductionEquiv_mk J I hJI P p)

end AdicModuleSystem
