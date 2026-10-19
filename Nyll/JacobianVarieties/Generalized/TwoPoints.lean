/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalUnitQuotient
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseIsRational
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# The multiplicative kernel at two reduced rational places

At a reduced rational place the truncated local ring is its residue field,
canonically identified with the base field. For two distinct such places the
ratio of the two residue units identifies the local-unit quotient by diagonal
scalars with `Kˣ`. The forgetful kernel therefore is `Kˣ`, as an abstract group.
The required constant-field equality is proved from either rational place.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- Scalar units give all first-order jets at a rational place. -/
def reducedJetScalarEquiv (v : Place K F) (n : ℕ) (hn : n = 1) (hv : v.IsRational) :
    Kˣ ≃* (v.toValuationSubring ⧸ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)ˣ :=
  Units.mapEquiv
    ((RingEquiv.ofBijective (algebraMap K v.ResidueField)
      ⟨v.algebraMap_residueField_injective, hv⟩).trans
        (Ideal.quotEquivOfEq (show
          (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n =
            IsLocalRing.maximalIdeal v.toValuationSubring by rw [hn, pow_one])).symm).toMulEquiv

/-- The residue equivalence sends a scalar unit to its actual quotient-ring reduction. -/
theorem reducedJetScalarEquiv_apply (v : Place K F) (n : ℕ) (hn : n = 1)
    (hv : v.IsRational) (c : Kˣ) :
    v.reducedJetScalarEquiv n hn hv c =
      Units.map (algebraMap K
        (v.toValuationSubring ⧸ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n)) c := by
  apply Units.ext
  change (Ideal.quotEquivOfEq (show
      (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n =
        IsLocalRing.maximalIdeal v.toValuationSubring by rw [hn, pow_one])).symm
      (algebraMap K v.ResidueField (c : K)) = _
  rw [Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk (show IsLocalRing.maximalIdeal v.toValuationSubring =
      (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n by rw [hn, pow_one])
    (algebraMap K v.toValuationSubring (c : K))

end Place

namespace Modulus

/-- The reduced modulus supported at two specified places. -/
def twoPoint (p q : Place K F) : Modulus K F := Finsupp.single p 1 + Finsupp.single q 1

theorem twoPoint_apply_left (p q : Place K F) (hpq : p ≠ q) : twoPoint p q p = 1 := by
  classical
  simp only [twoPoint, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hpq, add_zero]

theorem twoPoint_apply_right (p q : Place K F) (hpq : p ≠ q) : twoPoint p q q = 1 := by
  classical
  simp only [twoPoint, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hpq.symm, zero_add]

/-- Every supported place of the two-point modulus is one of the specified places. -/
theorem twoPoint_support_cases (p q r : Place K F) (hr : twoPoint p q r ≠ 0) :
    r = p ∨ r = q := by
  classical
  by_cases hp : p = r
  · exact Or.inl hp.symm
  by_cases hq : q = r
  · exact Or.inr hq.symm
  have hz : twoPoint p q r = 0 := by
    simp only [twoPoint, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hp),
      Finsupp.single_eq_of_ne (Ne.symm hq), add_zero]
  exact False.elim (hr hz)

/-- The actual support subtype of a reduced two-point modulus. -/
abbrev TwoPointSupport (p q : Place K F) := {r : Place K F // twoPoint p q r ≠ 0}

/-- The first point, regarded as an element of the support. -/
def twoPointLeft (p q : Place K F) (hpq : p ≠ q) : TwoPointSupport p q :=
  ⟨p, by rw [twoPoint_apply_left p q hpq]; exact one_ne_zero⟩

/-- The second point, regarded as an element of the support. -/
def twoPointRight (p q : Place K F) (hpq : p ≠ q) : TwoPointSupport p q :=
  ⟨q, by rw [twoPoint_apply_right p q hpq]; exact one_ne_zero⟩

/-- The scalar description of the local factor at each supported place. -/
def twoPointFiberEquiv (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) (r : TwoPointSupport p q) :
    Kˣ ≃* (r.1.toValuationSubring ⧸
      (IsLocalRing.maximalIdeal r.1.toValuationSubring) ^ twoPoint p q r.1)ˣ :=
  r.1.reducedJetScalarEquiv _ (by
    rcases twoPoint_support_cases p q r.1 r.2 with hr | hr
    · rw [hr, twoPoint_apply_left p q hpq]
    · rw [hr, twoPoint_apply_right p q hpq]) (by
    rcases twoPoint_support_cases p q r.1 r.2 with hr | hr
    · exact hr.symm ▸ hp
    · exact hr.symm ▸ hq)

/-- Local jets at the two reduced rational points are pairs of scalar units,
written as functions on the actual support. -/
def twoPointCoordinates (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) :
    (twoPoint p q).LocalJetUnits ≃* (TwoPointSupport p q → Kˣ) :=
  MulEquiv.piCongrRight (fun r => (twoPointFiberEquiv p q hpq hp hq r).symm)

/-- Diagonal scalar jets have the same scalar at both coordinates. -/
theorem twoPointCoordinates_scalarJets (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) (c : Kˣ) :
    twoPointCoordinates p q hpq hp hq ((twoPoint p q).scalarJets c) = fun _ => c := by
  funext r
  change (twoPointFiberEquiv p q hpq hp hq r).symm
    (((twoPoint p q).scalarJets c) r) = c
  apply (twoPointFiberEquiv p q hpq hp hq r).injective
  rw [MulEquiv.apply_symm_apply]
  rw [twoPointFiberEquiv, Place.reducedJetScalarEquiv_apply]
  apply Units.ext
  change Ideal.Quotient.mk _
      ((twoPoint p q).localUnit ((twoPoint p q).scalarAway c) r.1 r.2 : r.1.toValuationSubring) =
    Ideal.Quotient.mk _ (algebraMap K r.1.toValuationSubring (c : K))
  congr 1

/-- The ratio of the second residue unit to the first residue unit. -/
def twoPointRatio (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) : (twoPoint p q).LocalJetUnits →* Kˣ where
  toFun x := twoPointCoordinates p q hpq hp hq x (twoPointRight p q hpq) /
    twoPointCoordinates p q hpq hp hq x (twoPointLeft p q hpq)
  map_one' := by
    rw [map_one]
    exact div_self' 1
  map_mul' x y := by
    rw [map_mul]
    exact (div_mul_div_comm _ _ _ _).symm

/-- Every scalar unit occurs as a ratio of two local jets. -/
theorem twoPointRatio_surjective (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) :
    Function.Surjective (twoPointRatio p q hpq hp hq) := by
  classical
  intro c
  let a : TwoPointSupport p q → Kˣ := fun r => if r.1 = q then c else 1
  refine ⟨(twoPointCoordinates p q hpq hp hq).symm a, ?_⟩
  change twoPointCoordinates p q hpq hp hq
      ((twoPointCoordinates p q hpq hp hq).symm a) (twoPointRight p q hpq) /
    twoPointCoordinates p q hpq hp hq
      ((twoPointCoordinates p q hpq hp hq).symm a) (twoPointLeft p q hpq) = c
  rw [MulEquiv.apply_symm_apply]
  change (if q = q then c else 1) / (if p = q then c else 1) = c
  rw [ite_eq_left rfl, ite_eq_right hpq, div_one]

/-- The ratio is trivial precisely on the diagonal scalar subgroup. -/
theorem ker_twoPointRatio (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) :
    (twoPointRatio p q hpq hp hq).ker = (twoPoint p q).scalarJets.range := by
  ext x
  constructor
  · intro hx
    change twoPointCoordinates p q hpq hp hq x (twoPointRight p q hpq) /
      twoPointCoordinates p q hpq hp hq x (twoPointLeft p q hpq) = 1 at hx
    have heq := div_eq_one.mp hx
    refine ⟨twoPointCoordinates p q hpq hp hq x (twoPointLeft p q hpq), ?_⟩
    apply (twoPointCoordinates p q hpq hp hq).injective
    rw [twoPointCoordinates_scalarJets]
    funext r
    rcases twoPoint_support_cases p q r.1 r.2 with hr | hr
    · have hindex : r = twoPointLeft p q hpq := Subtype.ext hr
      rw [hindex]
    · have hindex : r = twoPointRight p q hpq := Subtype.ext hr
      rw [hindex]
      exact heq.symm
  · rintro ⟨c, rfl⟩
    change twoPointCoordinates p q hpq hp hq ((twoPoint p q).scalarJets c)
        (twoPointRight p q hpq) /
      twoPointCoordinates p q hpq hp hq ((twoPoint p q).scalarJets c)
        (twoPointLeft p q hpq) = 1
    rw [twoPointCoordinates_scalarJets]
    exact div_self' c

/-- Two reduced rational local factors modulo their diagonal scalars form `Kˣ`. -/
def twoPointLocalUnitQuotientEquiv (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) :
    (twoPoint p q).LocalJetUnits ⧸ (twoPoint p q).scalarJets.range ≃* Kˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_twoPointRatio p q hpq hp hq).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (twoPointRatio p q hpq hp hq)
      (twoPointRatio_surjective p q hpq hp hq))

/-- The forgetful kernel for two distinct reduced rational places is the
multiplicative group of the base field. Constants are supplied by the first
rational place and the existing principal-divisor theorem. -/
def twoPointKernelEquiv [HasPrincipalDivisors K F] (p q : Place K F) (hpq : p ≠ q)
    (hp : p.IsRational) (hq : q.IsRational) :
    Multiplicative (twoPoint p q).toPic0.ker ≃* Kˣ :=
  ((twoPoint p q).localUnitQuotientEquivKernel
    (constantsAreBase_of_exists_isRational p hp (by
      rw [p.isRational_iff_deg_eq_one.mp hp]
      exact one_ne_zero))).symm.trans (twoPointLocalUnitQuotientEquiv p q hpq hp hq)

end Modulus

end AlgebraicCurve
