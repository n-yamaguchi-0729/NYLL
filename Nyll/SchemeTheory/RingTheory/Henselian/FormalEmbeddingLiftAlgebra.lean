/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalSeparableTensorSplitting

/-! # Ground-field structure of actual finite separable formal factors

The constructed simple-root lift preserves the ground field because it
extends the actual ground-field-linear base deformation. Restricting this
lift along the original function-field embedding therefore produces a
native ground-field algebra homomorphism, with its residue and base-parameter
values proved from the original lift equations. No additional scalar tower
through the coefficient-field inclusion into power series is imposed.
-/

noncomputable section

namespace PowerSeries

variable {K E F L : Type*} [Field K] [Field E] [Field F] [Field L]
  [Algebra K E] [Algebra K F] [Algebra K L]
  [Algebra E F] [Algebra E L] [IsScalarTower K E F] [IsScalarTower K E L]
  [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- The actual simple-root lift, with its ground-field structure derived
from its proved extension equation. -/
def formalEmbeddingLiftAlgHom
    (τ : E →ₐ[K] PowerSeries L)
    (hτ : constantCoeff.comp τ.toRingHom = algebraMap E L)
    (ι : F →ₐ[E] L) : F →ₐ[K] PowerSeries L where
  toRingHom := formalEmbeddingLift τ.toRingHom hτ ι
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply K E F]
    exact (RingHom.congr_fun (formalEmbeddingLift_spec τ.toRingHom hτ ι).1
      (algebraMap K E a)).trans (τ.commutes a)

/-- Restriction to the original curve field retains its actual residue
embedding, through the same native completed-field scalar structures. -/
theorem constantCoeff_formalEmbeddingLiftAlgHom_comp
    {A : Type*} [Field A] [Algebra K A]
    (τ : E →ₐ[K] PowerSeries L)
    (hτ : constantCoeff.comp τ.toRingHom = algebraMap E L)
    (ι : F →ₐ[E] L) (j : A →ₐ[K] F) :
    constantCoeff.comp ((formalEmbeddingLiftAlgHom τ hτ ι).comp j).toRingHom =
      ((ι.restrictScalars K).comp j).toRingHom := by
  apply RingHom.ext
  intro a
  exact RingHom.congr_fun (formalEmbeddingLift_spec τ.toRingHom hτ ι).2 (j a)

omit [IsScalarTower K E L] in
/-- The original parameter equation computes the actual formal factor on
that parameter. This uses the proved extension equation, not any assumed
comparison of the formal factor with a tame coordinate expansion. -/
theorem formalEmbeddingLiftAlgHom_comp_parameter
    {A : Type*} [Field A] [Algebra K A]
    (τ : E →ₐ[K] PowerSeries L)
    (hτ : constantCoeff.comp τ.toRingHom = algebraMap E L)
    (ι : F →ₐ[E] L) (j : A →ₐ[K] F)
    (a : A) (s : E) (has : j a = algebraMap E F s) :
    (formalEmbeddingLiftAlgHom τ hτ ι).comp j a = τ s := by
  change formalEmbeddingLift τ.toRingHom hτ ι (j a) = τ s
  rw [has]
  exact RingHom.congr_fun (formalEmbeddingLift_spec τ.toRingHom hτ ι).1 s

/-- In particular the reciprocal parameter of the original curve has the
actual prescribed shift. Together with the residue formula this is exactly
the finite-separable uniqueness input used by the tame integral comparison. -/
theorem formalEmbeddingLiftAlgHom_comp_reciprocal_shift
    {A : Type*} [Field A] [Algebra K A]
    (τ : E →ₐ[K] PowerSeries L)
    (hτ : constantCoeff.comp τ.toRingHom = algebraMap E L)
    (ι : F →ₐ[E] L) (j : A →ₐ[K] F)
    (a : A) (s : E) (has : j a = algebraMap E F s)
    (hs : τ s = C (algebraMap E L s) + X) :
    (formalEmbeddingLiftAlgHom τ hτ ι).comp j a =
      C (((ι.restrictScalars K).comp j) a) + X := by
  rw [formalEmbeddingLiftAlgHom_comp_parameter τ hτ ι j a s has, hs]
  change C (algebraMap E L s) + X = C (ι (j a)) + X
  rw [has, ι.commutes]

end PowerSeries
