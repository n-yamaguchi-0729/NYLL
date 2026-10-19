/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Ring

/-! # Lifting units through quotients of commutative Artinian rings -/

namespace SchemeTheory

variable {A B : Type*} [CommRing A] [CommRing B] [IsArtinianRing A]

/-- A surjective homomorphism from a commutative Artinian ring is surjective on units.
Stabilization of the powers of a lift supplies a correction supported on its
nonunit components, including when the kernel is not nilpotent. -/
theorem artinian_unitsMap_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨x, hx⟩ := hf (u : B)
  obtain ⟨n, y, hxy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  have hrel : x ^ n * (x * y) = x ^ n * 1 := by
    simpa only [smul_eq_mul, pow_succ, mul_assoc] using hxy
  have hzero : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub, hrel, sub_self]
  have hunit : IsUnit (x + (1 - x * y)) := by
    by_contra hn
    obtain ⟨m, hm, hz⟩ := exists_max_ideal_of_mem_nonunits hn
    by_cases hxm : x ∈ m
    · have h1 : (1 : A) ∈ m := by
        have hmem := m.add_mem (m.sub_mem hz hxm) (m.mul_mem_right y hxm)
        convert hmem using 1
        ring
      exact hm.ne_top (m.eq_top_of_isUnit_mem h1 isUnit_one)
    · have hmem : x * y - 1 ∈ m :=
        (hm.isPrime.mem_or_mem_of_mul_eq_zero hzero).resolve_left
          (fun hpow => hxm (hm.isPrime.mem_of_pow_mem n hpow))
      apply hxm
      have hsum := m.add_mem hz hmem
      convert hsum using 1
      ring
  have hfx : IsUnit (f x) := hx.symm ▸ u.isUnit
  have hfxy : f (x * y) = 1 := by
    apply (hfx.pow n).mul_left_cancel
    simpa only [map_mul, map_pow, map_one] using congrArg f hrel
  refine ⟨hunit.unit, ?_⟩
  apply Units.ext
  change f (hunit.unit : A) = (u : B)
  rw [IsUnit.unit_spec, map_add, map_sub, map_one, hfxy, sub_self, add_zero, hx]

end SchemeTheory
