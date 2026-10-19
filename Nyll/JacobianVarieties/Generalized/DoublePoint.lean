/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalUnitTransition
import Nyll.JacobianVarieties.Generalized.SinglePoint
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseIsRational
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The additive kernel at a double rational point

Principal units at a rational place map onto the forgetful kernel for the
modulus twice that place. Their kernel is the second principal-unit group.
The existing uniformizer coefficient theorem identifies this quotient with
the additive residue field, hence with the additive base field. The resulting
abstract group isomorphism depends on a chosen uniformizer; no representing
group scheme is assumed.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The modulus with multiplicity two at a single place. -/
def doublePoint (v : Place K F) : Modulus K F := Finsupp.single v 2

/-- A valuation-ring unit is a rational function which is a unit along the double point. -/
def unitAtDoublePoint (v : Place K F) : v.toValuationSubringˣ →* (doublePoint v).awayUnits where
  toFun u := ⟨Units.map (algebraMap v.toValuationSubring F) u, by
    intro w hw
    by_cases h : w = v
    · subst w
      exact v.ord_coe_unit u
    · exact False.elim (hw (Finsupp.single_eq_of_ne h))⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' u w := by apply Subtype.ext; exact map_mul _ u w

/-- For an actual local unit, double-point congruence is exactly the second
principal-unit condition, retaining the full multiplicity. -/
theorem congruentOne_doublePoint_iff (v : Place K F) {π : v.toValuationSubring}
    (hπ : Irreducible π) (u : v.toValuationSubringˣ) :
    (doublePoint v).CongruentOne ((u : v.toValuationSubring) : F) ↔
      u ∈ higherUnitSubgroup π 2 := by
  constructor
  · intro hu
    obtain ⟨w, hw, hcong⟩ := ((congruentOne_single v 2 _).mp hu).2 (by decide)
    have hwu : w = u := Units.ext (Subtype.ext hw)
    subst w
    rw [← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ 2]
    exact (v.mem_congruenceUnitSubgroup 2 u).mpr hcong
  · intro hu
    rw [← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ 2] at hu
    apply (congruentOne_single v 2 _).mpr
    refine ⟨?_, fun _ => ⟨u, rfl, (v.mem_congruenceUnitSubgroup 2 u).mp hu⟩⟩
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using u.ne_zero

/-- First principal units have residue value one. -/
theorem higherUnit_hasValue_one (v : Place K F) {π : v.toValuationSubring}
    (hπ : Irreducible π) (u : higherUnitSubgroup π 1) :
    v.HasValue ((u.1 : v.toValuationSubring) : F) 1 := by
  apply (v.congruentOne_one_iff_hasValue _).mp
  refine ⟨u.1, rfl, ?_⟩
  apply (v.mem_congruenceUnitSubgroup 1 u.1).mp
  rw [v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ 1]
  exact u.2

variable [HasPrincipalDivisors K F]

/-- The actual divisor boundary from first principal units to the double-point kernel. -/
def principalUnitBoundary (v : Place K F) (π : v.toValuationSubring) :
    higherUnitSubgroup π 1 →* Multiplicative (doublePoint v).toPic0.ker :=
  ((doublePoint v).jetBoundaryToKernel.comp (doublePoint v).jetMap).comp
    ((unitAtDoublePoint v).comp (higherUnitSubgroup π 1).subtype)

/-- On principal units, the boundary is the class of the actual rational-function divisor. -/
theorem principalUnitBoundary_val (v : Place K F) (π : v.toValuationSubring)
    (u : higherUnitSubgroup π 1) :
    (principalUnitBoundary v π u).toAdd.1 =
      (doublePoint v).unitBoundary (Additive.ofMul (unitAtDoublePoint v u.1)) := by
  change ((doublePoint v).jetBoundary
    ((doublePoint v).jetMap (unitAtDoublePoint v u.1))).toAdd = _
  rw [jetBoundary_jetMap]
  rfl

/-- At a rational place, scalar ambiguity in a first principal unit is forced
to one, so the kernel is exactly the second principal-unit group. -/
theorem ker_principalUnitBoundary (v : Place K F) (hv : v.IsRational)
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    (principalUnitBoundary v π).ker =
      Subgroup.comap (higherUnitSubgroup π 1).subtype (higherUnitSubgroup π 2) := by
  have hC : ConstantsAreBase K F := constantsAreBase_of_exists_isRational v hv (by
    rw [v.isRational_iff_deg_eq_one.mp hv]
    exact one_ne_zero)
  ext u
  constructor
  · intro hu
    have hb : (doublePoint v).unitBoundary
        (Additive.ofMul (unitAtDoublePoint v u.1)) = 0 := by
      rw [← principalUnitBoundary_val]
      exact congrArg (fun a : Multiplicative (doublePoint v).toPic0.ker => a.toAdd.1) hu
    obtain ⟨c, hc⟩ := ((doublePoint v).unitBoundary_eq_zero_iff hC
      (unitAtDoublePoint v u.1)).mp hb
    have hlocal : v.CongruentOne 2
        (((u.1 : v.toValuationSubring) : F) / algebraMap K F (c : K)) :=
      ((congruentOne_single v 2 _).mp hc).2 (by decide)
    have hval := (v.congruentOne_one_iff_hasValue _).mp (hlocal.mono (by decide))
    have hvalc : v.HasValue ((u.1 : v.toValuationSubring) : F) (c : K) := by
      have hmul := hval.mul (v.hasValue_algebraMap (c : K))
      simpa only [div_mul_cancel₀ _ ((map_ne_zero (algebraMap K F)).mpr c.ne_zero), one_mul]
        using hmul
    have hc1 : (c : K) = 1 := hvalc.unique (higherUnit_hasValue_one v hπ u)
    change u.1 ∈ higherUnitSubgroup π 2
    apply (congruentOne_doublePoint_iff v hπ u.1).mp
    change (doublePoint v).CongruentOne
      (((u.1 : v.toValuationSubring) : F) / algebraMap K F (c : K)) at hc
    rw [hc1, map_one, div_one] at hc
    exact hc
  · intro hu
    change principalUnitBoundary v π u = 1
    change (principalUnitBoundary v π u).toAdd = 0
    apply Subtype.ext
    change (principalUnitBoundary v π u).toAdd.1 = 0
    rw [principalUnitBoundary_val]
    exact (doublePoint v).unitBoundary_eq_zero_of_congruentOne
      (unitAtDoublePoint v u.1) ((congruentOne_doublePoint_iff v hπ u.1).mpr hu)

/-- Every double-point kernel class is represented by a first principal unit.
The reduced rational point has trivial forgetful kernel, so its transition
supplies the principal-unit representative. -/
theorem principalUnitBoundary_surjective (v : Place K F) (hv : v.IsRational)
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    Function.Surjective (principalUnitBoundary v π) := by
  intro x
  let D : Modulus K F := doublePoint v
  let E : Modulus K F := Finsupp.single v 1
  have hED : E ≤ D := Finsupp.single_le_single.mpr (by decide)
  obtain ⟨A, hA⟩ := QuotientAddGroup.mk_surjective x.toAdd.1
  change D.mkZero A = x.toAdd.1 at hA
  let B : E.divAwayZero := restrictDivisors hED A
  have hB : E.mkZero B = 0 := by
    apply (toPic0_single_one_injective v hv)
    rw [map_zero]
    change E.toPic0 (transition hED (D.mkZero A)) = 0
    rw [toPic0_transition, hA]
    exact x.toAdd.2
  obtain ⟨g, hg, hdiv⟩ := (QuotientAddGroup.eq_zero_iff B).mp hB
  obtain ⟨u, hu, hunit⟩ := ((congruentOne_single v 1 g).mp hg).2 one_ne_zero
  have hu1 : u ∈ higherUnitSubgroup π 1 := by
    rw [← v.congruenceUnitSubgroup_eq_higherUnitSubgroup hπ 1]
    exact (v.mem_congruenceUnitSubgroup 1 u).mpr hunit
  refine ⟨⟨u, hu1⟩, ?_⟩
  change (principalUnitBoundary v π ⟨u, hu1⟩).toAdd = x.toAdd
  apply Subtype.ext
  rw [principalUnitBoundary_val, ← hA]
  change D.mkZero (D.unitDivisor (unitAtDoublePoint v u)) = D.mkZero A
  congr 1
  apply Subtype.ext
  ext w
  rw [unitDivisor_apply]
  change w.ord ((u : v.toValuationSubring) : F) = (A : Divisor K F) w
  rw [hu]
  have hw := hdiv w
  change (A : Divisor K F) w = w.ord g at hw
  exact hw.symm

/-- The first principal-unit quotient is the actual double-point forgetful kernel. -/
def principalUnitQuotientEquivKernel (v : Place K F) (hv : v.IsRational)
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    (higherUnitSubgroup π 1 ⧸
      Subgroup.comap (higherUnitSubgroup π 1).subtype (higherUnitSubgroup π 2)) ≃*
        Multiplicative (doublePoint v).toPic0.ker :=
  (QuotientGroup.quotientMulEquivOfEq (ker_principalUnitBoundary v hv hπ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (principalUnitBoundary v π)
      (principalUnitBoundary_surjective v hv hπ))

/-- After choosing a uniformizer, the double-point forgetful kernel is the
additive group of the base field, in every characteristic. -/
def doublePointKernelEquiv (v : Place K F) (hv : v.IsRational)
    {π : v.toValuationSubring} (hπ : Irreducible π) :
    (doublePoint v).toPic0.ker ≃+ K :=
  MulEquiv.toAdditive
    (((principalUnitQuotientEquivKernel v hv hπ).symm.trans
      (higherUnitGradedPieceMulEquivResidue hπ 1 (le_refl 1))).trans
        (AddEquiv.toMultiplicative
          (((Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm).trans
            (RingEquiv.ofBijective (algebraMap K v.ResidueField)
              ⟨v.algebraMap_residueField_injective, hv⟩).symm).toAddEquiv)))

end AlgebraicCurve.Modulus
