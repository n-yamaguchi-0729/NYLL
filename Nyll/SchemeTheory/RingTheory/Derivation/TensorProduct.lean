/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel

/-!
# Derivations on a tensor factor

A derivation on the left algebra induces a derivation on the tensor
product which fixes the right factor. The underlying linear map is the
existing `LinearMap.rTensor`; only its Leibniz rule is supplied here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace Derivation

variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]

/-- Act by a derivation on the left tensor factor and fix the right factor. -/
def tensorLeft (D : Derivation K A A) (B : Type w) [CommRing B] [Algebra K B] :
    Derivation K (A ⊗[K] B) (A ⊗[K] B) :=
  Derivation.mk' (D.toLinearMap.rTensor B) (by
    intro x y
    change D.toLinearMap.rTensor B (x * y) =
      x * D.toLinearMap.rTensor B y + y * D.toLinearMap.rTensor B x
    refine x.inductionOn (fun a b => ?_) (fun x₁ x₂ h₁ h₂ => ?_)
    · refine y.inductionOn (fun c d => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul]
        change D (a * c) ⊗ₜ[K] (b * d) =
          (a * D c) ⊗ₜ[K] (b * d) + (c * D a) ⊗ₜ[K] (d * b)
        rw [D.leibniz, smul_eq_mul, smul_eq_mul, TensorProduct.add_tmul, mul_comm d b]
      · simp only [mul_add, add_mul, map_add, h₁, h₂]
        abel
    · simp only [mul_add, add_mul, map_add, h₁, h₂]
      abel)

/-- The tensor derivation has its prescribed value on each pure tensor. -/
theorem tensorLeft_tmul (D : Derivation K A A) (B : Type w)
    [CommRing B] [Algebra K B] (a : A) (b : B) :
    D.tensorLeft B (a ⊗ₜ[K] b) = D a ⊗ₜ[K] b := rfl

end Derivation
