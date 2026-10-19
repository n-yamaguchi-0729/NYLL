/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReesTensorCoefficients
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.ReesAlgebra

/-!
# Naturality of actual Rees tensor coefficients

A ring homomorphism maps the original ideal powers into the powers of
the extended ideal. Polynomial coefficient mapping therefore gives an
actual semilinear map of Rees algebras. Tensor it with an original
semilinear module map. Every coefficient and every homogeneous insertion
then commutes with this map.

This applies to the actual restriction maps between affine section rings;
it does not require the source and target coefficient rings to coincide.
-/

noncomputable section

open scoped TensorProduct

namespace ReesTensorCoefficients

universe u u' v v'

variable {R : Type u} [CommRing R] {S : Type u'} [CommRing S]
  (f : R →+* S) (I : Ideal R)

/-- The original ring map on an original ideal power, corestricted
to the corresponding power of the actual extended ideal. -/
def idealPowerMap (n : ℕ) : ↥(I ^ n) →ₛₗ[f] ↥((I.map f) ^ n) where
  toFun a := ⟨f a.val, by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f a.property⟩
  map_add' a b := Subtype.ext (f.map_add a.val b.val)
  map_smul' a b := Subtype.ext (f.map_mul a b.val)

/-- The coefficientwise original ring map on the original Rees algebra. -/
def reesMap : ↥(reesAlgebra I) →ₛₗ[f] ↥(reesAlgebra (I.map f)) where
  toFun p := ⟨Polynomial.map f p.val, fun n => by
    rw [Polynomial.coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f (p.property n)⟩
  map_add' p q := Subtype.ext (Polynomial.map_add (p := p.val) (q := q.val) f)
  map_smul' a p := by
    apply Subtype.ext
    change Polynomial.map f (a • p.val) = f a • Polynomial.map f p.val
    rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.smul_eq_C_mul]

variable {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module S N] (φ : M →ₛₗ[f] N)

/-- The actual tensor map of the coefficientwise Rees map with the
original semilinear module map. -/
def tensorMap : ↥(reesAlgebra I) ⊗[R] M →ₛₗ[f] ↥(reesAlgebra (I.map f)) ⊗[S] N :=
  TensorProduct.map (reesMap f I) φ

/-- The tensor map retains both original factors on pure tensors. -/
theorem tensorMap_tmul (p : ↥(reesAlgebra I)) (x : M) :
    tensorMap f I φ (p ⊗ₜ[R] x) = reesMap f I p ⊗ₜ[S] φ x :=
  TensorProduct.map_tmul (reesMap f I) φ p x

/-- Extraction of each coefficient commutes with the actual
semilinear tensor map, including the original ideal-power map. -/
theorem coefficient_tensorMap (z : ↥(reesAlgebra I) ⊗[R] M) (n : ℕ) :
    coefficient (I.map f) N n (tensorMap f I φ z) =
      TensorProduct.map (idealPowerMap f I n) φ (coefficient I M n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul p x =>
      rw [tensorMap_tmul, coefficient_tmul, coefficient_tmul, TensorProduct.map_tmul]
      apply congrArg (fun a : ↥((I.map f) ^ n) => a ⊗ₜ[S] φ x)
      apply Subtype.ext
      exact Polynomial.coeff_map (p := p.val) f n
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Inserting one homogeneous coefficient commutes with the same
actual semilinear tensor map. -/
theorem tensorMap_homogeneous (n : ℕ) (x : ↥(I ^ n) ⊗[R] M) :
    tensorMap f I φ (homogeneous I M n x) =
      homogeneous (I.map f) N n (TensorProduct.map (idealPowerMap f I n) φ x) := by
  apply ext_coefficients (I.map f) N
  intro k
  rw [coefficient_tensorMap]
  by_cases hk : k = n
  · subst k
    rw [coefficient_homogeneous, coefficient_homogeneous]
  · rw [coefficient_homogeneous_ne I M n k hk,
      coefficient_homogeneous_ne (I.map f) N n k hk, map_zero]

end ReesTensorCoefficients
