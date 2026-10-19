/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteAlgebraSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveModuleSystem
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Effectivity of finite étale adic algebra systems

The algebra of compatible sequences is finite projective, and its actual
tensor product with each quotient of the base recovers the supplied stage.
The differential module of this algebra vanishes after reduction; Nakayama
then proves that the algebra itself is étale.

The transition hypotheses specify an adic system: its maps are surjective
and their kernels are the extended ideal powers. The annihilation of each
stage is derived from its quotient-ring algebra structure. No algebraization,
projectivity of the limit, or recovery isomorphism is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace AdicAlgebraSystem

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (A : ℕ → Type v) [∀ n : ℕ, CommRing (A n)] [∀ n : ℕ, Algebra R (A n)]
  (t : (n : ℕ) → A (n + 1) →ₐ[R] A n)
  (I : Ideal R) [IsAdicComplete I R]
  [∀ n : ℕ, Module.Finite R (A n)]
  [∀ n : ℕ, Algebra (R ⧸ I ^ (n + 1)) (A n)]
  [∀ n : ℕ, IsScalarTower R (R ⧸ I ^ (n + 1)) (A n)]

omit [IsNoetherianRing R] [IsAdicComplete I R] [∀ n : ℕ, Module.Finite R (A n)] in
/-- The quotient-ring action kills the relevant ideal power at every stage. -/
theorem stage_power_map_eq_bot (n : ℕ) :
    (I ^ (n + 1)).map (algebraMap R (A n)) = ⊥ := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change algebraMap R (A n) r = 0
    calc
      algebraMap R (A n) r =
          algebraMap (R ⧸ I ^ (n + 1)) (A n)
            (algebraMap R (R ⧸ I ^ (n + 1)) r) :=
        IsScalarTower.algebraMap_apply R (R ⧸ I ^ (n + 1)) (A n) r
      _ = 0 := by
        rw [show algebraMap R (R ⧸ I ^ (n + 1)) r = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · exact bot_le

variable
  (ht : ∀ n : ℕ, Function.Surjective (t n))
  (hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
    (I ^ (n + 1)).map (algebraMap R (A (n + 1))))

include ht hker in
/-- Finite projectivity of the stages proves finite projectivity of the
actual compatible-sequence algebra. -/
theorem projective [∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (A n)] :
    Module.Projective R (sections A t) := by
  have hlinear : ∀ n : ℕ, (t n).toLinearMap.ker =
      I ^ (n + 1) • (⊤ : Submodule R (A (n + 1))) := by
    intro n
    rw [Ideal.smul_top_eq_map]
    exact congrArg (Submodule.restrictScalars R) (hker n)
  have hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (A n)) = ⊥ := by
    intro n
    rw [Ideal.smul_top_eq_map, stage_power_map_eq_bot A I n]
    rfl
  have hprojective : Module.Projective R
      (AdicModuleSystem.sections A (fun n => (t n).toLinearMap)) :=
    AdicModuleSystem.projective A (fun n => (t n).toLinearMap) I ht hlinear hpow
  exact Module.Projective.of_equiv' (sectionsLinearEquiv A t)

/-- Actual base change of the constructed algebra recovers the supplied
stage, as an algebra over the quotient of the base. -/
def baseChangeEquiv (n : ℕ) :
    ((R ⧸ I ^ (n + 1)) ⊗[R] sections A t) ≃ₐ[R ⧸ I ^ (n + 1)] A n :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
    (sections A t) (I ^ (n + 1))).symm.trans
      (AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
        (quotientEquiv A t I ht hker (stage_power_map_eq_bot A I) n))

/-- The recovery isomorphism uses the original projection on sections. -/
theorem baseChangeEquiv_one_tmul (n : ℕ) (x : sections A t) :
    baseChangeEquiv A t I ht hker n (1 ⊗ₜ[R] x) = eval A t n x := by
  have hmk := Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk
    (sections A t) (I ^ (n + 1)) x
  have hinv :
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
        (sections A t) (I ^ (n + 1))).symm (1 ⊗ₜ[R] x) =
      Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap R (sections A t))) x :=
    (AlgEquiv.symm_apply_eq _).mpr hmk.symm
  rw [baseChangeEquiv, AlgEquiv.trans_apply, hinv]
  exact quotientEquiv_mk A t I ht hker (stage_power_map_eq_bot A I) n x

omit [IsNoetherianRing R] in
private theorem etale_of_finite_projective_of_quotient
    (B : Type v) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    (J : Ideal R) (hJ : J ≤ (⊥ : Ideal R).jacobson)
    [Algebra.Etale (R ⧸ J) ((R ⧸ J) ⊗[R] B)] : Algebra.Etale R B := by
  let : Algebra B ((R ⧸ J) ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have hfinite : Module.Finite R Ω[B⁄R] := Module.Finite.trans B Ω[B⁄R]
  have htensor : Subsingleton ((R ⧸ J) ⊗[R] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R (R ⧸ J) B
      ((R ⧸ J) ⊗[R] B)).subsingleton
  have hquot : Subsingleton
      (Ω[B⁄R] ⧸ (J • (⊤ : Submodule R Ω[B⁄R]))) :=
    (TensorProduct.quotTensorEquivQuotSMul Ω[B⁄R] J).symm.subsingleton
  have htop : J • (⊤ : Submodule R Ω[B⁄R]) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hquot
  have hzero : (⊤ : Submodule R Ω[B⁄R]) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J ⊤ Module.Finite.fg_top
      htop.ge hJ
  have hdiff : Subsingleton Ω[B⁄R] := by
    have hx0 : ∀ x : Ω[B⁄R], x = 0 := by
      intro x
      have hx : x ∈ (⊤ : Submodule R Ω[B⁄R]) := Submodule.mem_top
      rw [hzero] at hx
      exact hx
    exact ⟨fun x y => (hx0 x).trans (hx0 y).symm⟩
  have hunramified : Algebra.FormallyUnramified R B := ⟨hdiff⟩
  have hpresentation : Module.FinitePresentation R B :=
    Module.finitePresentation_of_projective R B
  exact Algebra.Etale.of_formallyUnramified_of_flat

include ht hker in
/-- A finite étale adic algebra system is effective as the algebra of
compatible sequences over the original complete Noetherian ring. -/
theorem etale [∀ n : ℕ, Algebra.Etale (R ⧸ I ^ (n + 1)) (A n)] :
    Algebra.Etale R (sections A t) := by
  have hprojective : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (A n) := by
    intro n
    have hfinite : Module.Finite (R ⧸ I ^ (n + 1)) (A n) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ I ^ (n + 1)) (A n)
    have hpresentation : Module.FinitePresentation (R ⧸ I ^ (n + 1)) (A n) :=
      Module.finitePresentation_of_finite (R ⧸ I ^ (n + 1)) (A n)
    exact Module.Flat.projective_of_finitePresentation
  have hfinite : Module.Finite R (sections A t) :=
    finite A t I ht hker (stage_power_map_eq_bot A I)
  have hproj : Module.Projective R (sections A t) := projective A t I ht hker
  let B : Type v := sections A t
  let Q : Type u := R ⧸ I ^ (0 + 1)
  have hfiber : Algebra.Etale Q (Q ⊗[R] B) :=
    Algebra.Etale.of_equiv (baseChangeEquiv A t I ht hker 0).symm
  exact etale_of_finite_projective_of_quotient (sections A t) (I ^ (0 + 1))
    ((Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I))

end AdicAlgebraSystem
