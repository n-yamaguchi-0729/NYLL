/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Reduced.NilpotentPrincipalUnits
import Nyll.SchemeTheory.RingTheory.Reduced.NilpotentExponential
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Actual unit kernels of nilpotent algebra extensions -/

noncomputable section

universe u

namespace SchemeTheory

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The actual kernel of restriction on units. -/
abbrev unitKernel : Subgroup Aˣ := (Units.map f.toMonoidHom).ker

/-- The original unit kernel is precisely the principal units of the actual ring kernel. -/
theorem unitKernel_eq_principalUnits : unitKernel f = (RingHom.ker f).principalUnits := by
  ext u
  rw [Ideal.mem_principalUnits]
  change Units.map f.toMonoidHom u = 1 ↔ f ((u : A) - 1) = 0
  rw [← Units.val_inj]
  change f (u : A) = 1 ↔ f ((u : A) - 1) = 0
  rw [map_sub, map_one, sub_eq_zero]

variable (hnil : IsNilpotent (RingHom.ker f))

/-- Subtracting one identifies the entire actual unit kernel with the underlying
nilpotent ideal; the inverse is the actual unit `1 + x`. -/
def nilpotentUnitKernelEquiv : unitKernel f ≃ RingHom.ker f where
  toFun u := ⟨(u.1 : A) - 1, by
    have h := congrArg Units.val u.property
    change f (u.1 : A) = 1 at h
    change f ((u.1 : A) - 1) = 0
    rw [map_sub, map_one, h, sub_self]⟩
  invFun x :=
    let hunit := (Ideal.isNilpotent_element_of_mem hnil x.property).isUnit_one_add
    ⟨hunit.unit, by
      apply Units.ext
      change f (hunit.unit : A) = 1
      rw [hunit.unit_spec, map_add, map_one, x.property, add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    have hx : (u.1 : A) - 1 ∈ RingHom.ker f := by
      have hu := congrArg Units.val u.property
      change f (u.1 : A) = 1 at hu
      change f ((u.1 : A) - 1) = 0
      rw [map_sub, map_one, hu, sub_self]
    change ((Ideal.isNilpotent_element_of_mem hnil hx).isUnit_one_add.unit : A) = (u.1 : A)
    rw [IsUnit.unit_spec]
    ring
  right_inv x := by
    apply Subtype.ext
    change ((Ideal.isNilpotent_element_of_mem hnil x.property).isUnit_one_add.unit : A) - 1 = x.1
    rw [IsUnit.unit_spec, add_sub_cancel_left]

/-- The parameter is literally the original unit minus one. -/
theorem nilpotentUnitKernelEquiv_val (u : unitKernel f) :
    (nilpotentUnitKernelEquiv f hnil u : A) = (u.1 : A) - 1 := rfl

/-- The inverse parameterization is literally the actual unit `1 + x`. -/
theorem nilpotentUnitKernelEquiv_symm_val (x : RingHom.ker f) :
    (((nilpotentUnitKernelEquiv f hnil).symm x).1 : A) = 1 + x.1 :=
  (Ideal.isNilpotent_element_of_mem hnil x.property).isUnit_one_add.unit_spec

/-- The actual group law in ideal coordinates is `x + y + xy`. -/
theorem nilpotentUnitKernelEquiv_mul (u v : unitKernel f) :
    (nilpotentUnitKernelEquiv f hnil (u * v) : A) =
      (nilpotentUnitKernelEquiv f hnil u : A) +
        (nilpotentUnitKernelEquiv f hnil v : A) +
          (nilpotentUnitKernelEquiv f hnil u : A) *
            (nilpotentUnitKernelEquiv f hnil v : A) := by
  change (u.1 : A) * (v.1 : A) - 1 =
    ((u.1 : A) - 1) + ((v.1 : A) - 1) + ((u.1 : A) - 1) * ((v.1 : A) - 1)
  ring

/-- In characteristic zero the actual unit kernel is the additive nilpotent ideal
under the finite exponential, rather than under the nonadditive map `1 + x`. -/
def nilpotentUnitKernelExpEquiv [Algebra ℚ A] :
    Multiplicative (RingHom.ker f) ≃* unitKernel f :=
  ((RingHom.ker f).principalUnitExpEquiv hnil).trans
    (MulEquiv.subgroupCongr (unitKernel_eq_principalUnits f).symm)

end SchemeTheory

namespace SchemeTheory.Affine

open scoped TensorProduct

variable {R A B S : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S]
  (f : A →ₐ[R] B) (hf : Function.Surjective f)
  (hnil : IsNilpotent (RingHom.ker f.toRingHom))

include hf hnil in
/-- Nilpotence of the actual algebra kernel persists on every parameter algebra. -/
theorem tensorRestriction_ker_nilpotent :
    IsNilpotent (RingHom.ker
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom) := by
  obtain ⟨N, hN⟩ := hnil
  refine ⟨N, ?_⟩
  have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom :=
    Algebra.TensorProduct.lTensor_ker f hf
  rw [hker, ← Ideal.map_pow, hN]
  exact Ideal.map_bot

end SchemeTheory.Affine
