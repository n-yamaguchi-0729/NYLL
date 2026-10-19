/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalUnitKernel

/-!
# The local-unit quotient and the forgetful kernel

Finite jets are realized by weak approximation. Taking the principal divisor
of such a realization gives a well-defined boundary. When the constant field
is the base field, its kernel consists exactly of diagonal base-field units.
Thus the actual product of truncated local units, modulo those scalars, is
isomorphic to the kernel of the forgetful map on degree-zero divisor classes.

These are abstract groups; no representing group scheme is postulated.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F]

/-- A function congruent to one has zero principal boundary. -/
theorem unitBoundary_eq_zero_of_congruentOne (D : Modulus K F) (f : D.awayUnits)
    (hf : D.CongruentOne (f.1 : F)) : D.unitBoundary (Additive.ofMul f) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff (D.unitDivisor f)).mpr
  exact ⟨(f.1 : F), hf, D.unitDivisor_apply f⟩

/-- Finite jets contain all the data needed for the principal boundary. -/
theorem jetMap_ker_le_unitBoundary_ker (D : Modulus K F) :
    D.jetMap.ker ≤ D.unitBoundary.toMultiplicativeRight.ker := by
  intro f hf
  change D.unitBoundary (Additive.ofMul f) = 0
  exact D.unitBoundary_eq_zero_of_congruentOne f ((D.jetMap_eq_one_iff f).mp hf)

/-- The boundary descends from rational units to their finite local jets. -/
def jetBoundary (D : Modulus K F) : D.LocalJetUnits →* Multiplicative D.ClassGroupZero :=
  (QuotientGroup.lift D.jetMap.ker D.unitBoundary.toMultiplicativeRight
    D.jetMap_ker_le_unitBoundary_ker).comp
      (QuotientGroup.quotientKerEquivOfSurjective D.jetMap D.jetMap_surjective).symm.toMonoidHom

/-- A realized finite jet maps to the class of the realizing function's divisor. -/
@[simp]
theorem jetBoundary_jetMap (D : Modulus K F) (f : D.awayUnits) :
    D.jetBoundary (D.jetMap f) = Multiplicative.ofAdd (D.unitBoundary (Additive.ofMul f)) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective D.jetMap D.jetMap_surjective
  have he : e (QuotientGroup.mk f) = D.jetMap f := QuotientGroup.kerLift_mk D.jetMap f
  change QuotientGroup.lift D.jetMap.ker D.unitBoundary.toMultiplicativeRight
    D.jetMap_ker_le_unitBoundary_ker
    (e.symm (D.jetMap f)) = _
  rw [← he, e.symm_apply_apply]
  rfl

omit [HasPrincipalDivisors K F] in
/-- Scalar functions have the expected underlying value in the function field. -/
@[simp]
theorem scalarAway_coe (D : Modulus K F) (c : Kˣ) :
    ((D.scalarAway c).1 : F) = algebraMap K F (c : K) := rfl

omit [HasPrincipalDivisors K F] in
/-- Diagonal scalars form a normal subgroup of the commutative local-unit product. -/
instance scalarJets_range_normal (D : Modulus K F) : D.scalarJets.range.Normal where
  conj_mem a ha b := by
    rw [mul_comm b a, mul_assoc, mul_inv_cancel, mul_one]
    exact ha

/-- The finite-jet boundary has exactly the diagonal scalars as kernel. -/
theorem ker_jetBoundary (D : Modulus K F) (hC : ConstantsAreBase K F) :
    D.jetBoundary.ker = D.scalarJets.range := by
  ext q
  obtain ⟨f, rfl⟩ := D.jetMap_surjective q
  constructor
  · intro hf
    have hzero : D.unitBoundary (Additive.ofMul f) = 0 := by
      change D.jetBoundary (D.jetMap f) = 1 at hf
      rw [jetBoundary_jetMap] at hf
      exact hf
    obtain ⟨c, hc⟩ := (D.unitBoundary_eq_zero_iff hC f).mp hzero
    have hcong : D.CongruentOne (((f / D.scalarAway c).1 : F)) := by
      simpa only [Subgroup.coe_div, Units.val_div_eq_div_val, scalarAway_coe] using hc
    have hjet := (D.jetMap_eq_one_iff (f / D.scalarAway c)).mpr hcong
    rw [map_div, div_eq_one] at hjet
    exact ⟨c, hjet.symm⟩
  · rintro ⟨c, hc⟩
    change D.jetBoundary (D.jetMap f) = 1
    rw [← hc]
    change D.jetBoundary (D.jetMap (D.scalarAway c)) = 1
    rw [jetBoundary_jetMap]
    change D.unitBoundary (Additive.ofMul (D.scalarAway c)) = 0
    apply (D.unitBoundary_eq_zero_iff hC (D.scalarAway c)).mpr
    refine ⟨c, ?_⟩
    rw [scalarAway_coe, div_self ((map_ne_zero (algebraMap K F)).mpr c.ne_zero)]
    exact CongruentOne.one D

/-- The jet boundary takes values in the kernel of forgetting the modulus. -/
theorem toPic0_jetBoundary (D : Modulus K F) (q : D.LocalJetUnits) :
    D.toPic0 (D.jetBoundary q).toAdd = 0 := by
  obtain ⟨f, rfl⟩ := D.jetMap_surjective q
  rw [jetBoundary_jetMap]
  exact D.toPic0_unitBoundary (Additive.ofMul f)

/-- The concrete finite-jet boundary, with its codomain restricted to the forgetful kernel. -/
def jetBoundaryToKernel (D : Modulus K F) :
    D.LocalJetUnits →* Multiplicative D.toPic0.ker where
  toFun q := Multiplicative.ofAdd ⟨(D.jetBoundary q).toAdd, D.toPic0_jetBoundary q⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one D.jetBoundary)
  map_mul' q r := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul D.jetBoundary q r)

/-- Every class in the forgetful kernel is the boundary of actual finite local-unit jets. -/
theorem jetBoundaryToKernel_surjective (D : Modulus K F) :
    Function.Surjective D.jetBoundaryToKernel := by
  intro x
  have hx : x.toAdd.1 ∈ D.unitBoundary.range := by
    rw [range_unitBoundary]
    exact x.toAdd.2
  obtain ⟨f, hf⟩ := hx
  refine ⟨D.jetMap f.toMul, ?_⟩
  apply Subtype.ext
  change (D.jetBoundary (D.jetMap f.toMul)).toAdd = x.toAdd.1
  rw [jetBoundary_jetMap]
  exact hf

/-- Restricting the codomain leaves the diagonal scalar kernel unchanged. -/
theorem ker_jetBoundaryToKernel (D : Modulus K F) (hC : ConstantsAreBase K F) :
    D.jetBoundaryToKernel.ker = D.scalarJets.range := by
  rw [← D.ker_jetBoundary hC]
  ext q
  constructor
  · intro h
    exact congrArg (fun x : Multiplicative D.toPic0.ker => x.toAdd.1) h
  · intro h
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd h

/-- The local-unit description of the kernel of the degree-zero forgetful map.

The source is the product of the units of the actual truncated valuation rings,
modulo diagonal base-field units. The constant-field condition is supplied
independently by `ConstantsAreBase`; all approximation and exactness are proved.
-/
def localUnitQuotientEquivKernel (D : Modulus K F) (hC : ConstantsAreBase K F) :
    D.LocalJetUnits ⧸ D.scalarJets.range ≃* Multiplicative D.toPic0.ker :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_jetBoundaryToKernel hC).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective D.jetBoundaryToKernel
      D.jetBoundaryToKernel_surjective)

end AlgebraicCurve.Modulus
