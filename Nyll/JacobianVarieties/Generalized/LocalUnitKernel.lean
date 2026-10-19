/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClasses
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusJets
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Evaluation.Value

/-!
# The principal boundary for divisor classes with modulus

A rational function which is a unit along a modulus defines a degree-zero
divisor class with that modulus. The image is exactly the kernel of forgetting
the modulus. The independent constant-field condition `ConstantsAreBase`
identifies the kernel of this boundary with constants times congruence-one
functions. This is the rational-function form of Serre's local-unit sequence.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Nonzero rational functions which have no zero or pole along the modulus. -/
def awayUnits (D : Modulus K F) : Subgroup Fˣ where
  carrier := {f | ∀ v, D v ≠ 0 → v.ord (f : F) = 0}
  one_mem' := fun v _ => v.ord_one
  mul_mem' := by
    intro f g hf hg v hv
    rw [Units.val_mul, v.ord_mul f.ne_zero g.ne_zero, hf v hv, hg v hv, zero_add]
  inv_mem' := by
    intro f hf v hv
    rw [Units.val_inv_eq_inv_val, v.ord_inv, hf v hv, neg_zero]

@[simp]
theorem mem_awayUnits (D : Modulus K F) (f : Fˣ) :
    f ∈ D.awayUnits ↔ ∀ v, D v ≠ 0 → v.ord (f : F) = 0 := Iff.rfl

/-- The actual local unit determined by a rational function of order zero. -/
def localUnit (D : Modulus K F) (f : D.awayUnits) (v : Place K F) (hv : D v ≠ 0) :
    v.toValuationSubringˣ :=
  (v.exists_isUnit_of_ord_eq_zero f.1.ne_zero (f.2 v hv)).choose_spec.unit

@[simp]
theorem localUnit_coe (D : Modulus K F) (f : D.awayUnits) (v : Place K F)
    (hv : D v ≠ 0) : ((D.localUnit f v hv : v.toValuationSubring) : F) = (f.1 : F) := by
  rw [localUnit, IsUnit.unit_spec]

/-- All invertible finite jets along the full modulus, retaining multiplicities. -/
abbrev LocalJetUnits (D : Modulus K F) :=
  ∀ v : {v : Place K F // D v ≠ 0},
    (v.1.toValuationSubring ⧸ (IsLocalRing.maximalIdeal v.1.toValuationSubring) ^ D v.1)ˣ

/-- Restrict a rational function which is a local unit to its finite jets. -/
def jetMap (D : Modulus K F) : D.awayUnits →* D.LocalJetUnits where
  toFun f v := LubinTate.Valuations.unitReduction
    ((IsLocalRing.maximalIdeal v.1.toValuationSubring) ^ D v.1) (D.localUnit f v.1 v.2)
  map_one' := by
    funext v
    have h : D.localUnit 1 v.1 v.2 = 1 := by
      apply Units.ext
      apply Subtype.ext
      exact D.localUnit_coe 1 v.1 v.2
    rw [h, map_one]
    rfl
  map_mul' f g := by
    funext v
    have h : D.localUnit (f * g) v.1 v.2 =
        D.localUnit f v.1 v.2 * D.localUnit g v.1 v.2 := by
      apply Units.ext
      apply Subtype.ext
      change ((D.localUnit (f * g) v.1 v.2 : v.1.toValuationSubring) : F) =
        ((D.localUnit f v.1 v.2 : v.1.toValuationSubring) : F) *
          ((D.localUnit g v.1 v.2 : v.1.toValuationSubring) : F)
      rw [localUnit_coe, localUnit_coe, localUnit_coe]
      rfl
    rw [h, map_mul]
    rfl

/-- Weak approximation makes every tuple of invertible finite jets global. -/
theorem jetMap_surjective (D : Modulus K F) : Function.Surjective D.jetMap := by
  classical
  intro q
  let u (v : Place K F) : v.toValuationSubringˣ :=
    if hv : D v ≠ 0 then (v.unitReduction_surjective hv (q ⟨v, hv⟩)).choose else 1
  obtain ⟨f, hf, hlocal⟩ := D.exists_unit_jets u
  have hord : ∀ v, D v ≠ 0 → v.ord f = 0 := by
    intro v hv
    obtain ⟨w, hw, _⟩ := hlocal v hv
    rw [← hw]
    exact v.ord_coe_unit w
  let g : D.awayUnits := ⟨Units.mk0 f hf, hord⟩
  refine ⟨g, ?_⟩
  funext v
  obtain ⟨w, hw, hred⟩ := hlocal v.1 v.2
  have hunit : D.localUnit g v.1 v.2 = w := by
    apply Units.ext
    apply Subtype.ext
    exact (D.localUnit_coe g v.1 v.2).trans hw.symm
  change LubinTate.Valuations.unitReduction _ (D.localUnit g v.1 v.2) = q v
  rw [hunit, hred]
  simpa only [u, dite_eq_left v.2] using
    (v.1.unitReduction_surjective v.2 (q v)).choose_spec

/-- Trivial finite jets mean precisely congruence to one along the modulus. -/
theorem jetMap_eq_one_iff (D : Modulus K F) (f : D.awayUnits) :
    D.jetMap f = 1 ↔ D.CongruentOne (f.1 : F) := by
  constructor
  · intro hf
    refine ⟨f.1.ne_zero, fun v hv => ?_⟩
    refine ⟨D.localUnit f v hv, D.localUnit_coe f v hv, ?_⟩
    apply (v.mem_congruenceUnitSubgroup (D v) _).mp
    exact congrFun hf ⟨v, hv⟩
  · intro hf
    funext v
    obtain ⟨w, hw, hcong⟩ := hf.2 v.1 v.2
    have hunit : D.localUnit f v.1 v.2 = w := by
      apply Units.ext
      apply Subtype.ext
      exact (D.localUnit_coe f v.1 v.2).trans hw.symm
    change LubinTate.Valuations.unitReduction _ (D.localUnit f v.1 v.2) = 1
    rw [hunit]
    exact (v.1.mem_congruenceUnitSubgroup (D v.1) w).mpr hcong

/-- Base-field units regarded as rational functions which are units everywhere. -/
def scalarAway (D : Modulus K F) : Kˣ →* D.awayUnits where
  toFun c := ⟨Units.map (algebraMap K F) c, by
    intro v _
    change v.ord (algebraMap K F (c : K)) = 0
    have h := v.ord_coe_unit (Units.map (algebraMap K v.toValuationSubring) c)
    change v.ord (algebraMap K F (c : K)) = 0 at h
    exact h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

/-- The diagonal base-field scalars in the finite local-unit jets. -/
def scalarJets (D : Modulus K F) : Kˣ →* D.LocalJetUnits :=
  D.jetMap.comp D.scalarAway

/-- The principal divisor of a unit along the modulus, with support and degree proofs. -/
def unitDivisor [HasPrincipalDivisors K F] (D : Modulus K F) (f : D.awayUnits) :
    D.divAwayZero :=
  let E := (HasPrincipalDivisors.exists_divisor (K := K) (f.1 : F) f.1.ne_zero).choose
  let hE := (HasPrincipalDivisors.exists_divisor (K := K) (f.1 : F) f.1.ne_zero).choose_spec
  ⟨E, (fun v hv => (hE.1 v).trans (f.2 v hv)), Divisor.mem_degZero.mpr hE.2⟩

@[simp]
theorem unitDivisor_apply [HasPrincipalDivisors K F] (D : Modulus K F)
    (f : D.awayUnits) (v : Place K F) :
    (D.unitDivisor f : Divisor K F) v = v.ord (f.1 : F) :=
  (HasPrincipalDivisors.exists_divisor (K := K) (f.1 : F) f.1.ne_zero).choose_spec.1 v

@[simp]
theorem unitDivisor_one [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.unitDivisor 1 = 0 := by
  apply Subtype.ext
  ext v
  change (D.unitDivisor 1 : Divisor K F) v = 0
  rw [unitDivisor_apply]
  exact v.ord_one

theorem unitDivisor_mul [HasPrincipalDivisors K F] (D : Modulus K F)
    (f g : D.awayUnits) : D.unitDivisor (f * g) = D.unitDivisor f + D.unitDivisor g := by
  apply Subtype.ext
  ext v
  simp only [AddSubgroup.coe_add, Finsupp.add_apply, unitDivisor_apply,
    Subgroup.coe_mul, Units.val_mul, v.ord_mul f.1.ne_zero g.1.ne_zero]

/-- The principal boundary, with the multiplicative source written additively. -/
def unitBoundary [HasPrincipalDivisors K F] (D : Modulus K F) :
    Additive D.awayUnits →+ D.ClassGroupZero where
  toFun f := D.mkZero (D.unitDivisor f.toMul)
  map_zero' := by
    change D.mkZero (D.unitDivisor 1) = 0
    rw [unitDivisor_one, map_zero]
  map_add' f g := by
    change D.mkZero (D.unitDivisor (f.toMul * g.toMul)) = _
    rw [unitDivisor_mul, map_add]

/-- Forgetting the modulus kills every principal boundary. -/
@[simp]
theorem toPic0_unitBoundary [HasPrincipalDivisors K F] (D : Modulus K F)
    (f : Additive D.awayUnits) : D.toPic0 (D.unitBoundary f) = 0 := by
  apply (D.toPic0_mkZero_eq_zero_iff (D.unitDivisor f.toMul)).mpr
  exact ⟨f.toMul.1, f.toMul.1.ne_zero, D.unitDivisor_apply f.toMul⟩

/-- Every class killed by forgetting the modulus is a principal boundary. -/
theorem range_unitBoundary [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.unitBoundary.range = D.toPic0.ker := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact D.toPic0_unitBoundary f
  · intro hx
    obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨f, hf, hE⟩ := (D.toPic0_mkZero_eq_zero_iff E).mp hx
    let u : D.awayUnits := ⟨Units.mk0 f hf, fun v hv => (hE v).symm.trans (E.2.1 v hv)⟩
    refine ⟨Additive.ofMul u, ?_⟩
    change D.mkZero (D.unitDivisor u) = D.mkZero E
    congr 1
    apply Subtype.ext
    exact Finsupp.ext fun v => (D.unitDivisor_apply u v).trans (hE v).symm

/-- Vanishing boundary is exactly congruence to a nonzero base-field scalar.

The only additional hypothesis is the independent assertion that functions
with no poles are base-field constants. No exactness assertion is assumed.
-/
theorem unitBoundary_eq_zero_iff [HasPrincipalDivisors K F] (D : Modulus K F)
    (hC : ConstantsAreBase K F) (f : D.awayUnits) :
    D.unitBoundary (Additive.ofMul f) = 0 ↔
      ∃ c : Kˣ, D.CongruentOne ((f.1 : F) / algebraMap K F (c : K)) := by
  constructor
  · intro hf
    obtain ⟨g, hg, hfg⟩ := (QuotientAddGroup.eq_zero_iff (D.unitDivisor f)).mp hf
    have hord : ∀ v : Place K F, v.ord ((f.1 : F) / g) = 0 := by
      intro v
      rw [div_eq_mul_inv, v.ord_mul f.1.ne_zero (inv_ne_zero hg.ne_zero), v.ord_inv]
      have hv := hfg v
      change (D.unitDivisor f : Divisor K F) v = v.ord g at hv
      rw [D.unitDivisor_apply] at hv
      omega
    have hL : (f.1 : F) / g ∈ LSpace (0 : Divisor K F) :=
      mem_lSpace_iff_ord.mpr (Or.inr (by
        intro v
        rw [Finsupp.zero_apply, neg_zero, hord v]))
    rw [hC] at hL
    obtain ⟨c, hc⟩ := hL
    change algebraMap K F c = (f.1 : F) / g at hc
    have hc0 : c ≠ 0 := by
      intro h
      have := div_ne_zero f.1.ne_zero hg.ne_zero
      rw [← hc, h, map_zero] at this
      exact this rfl
    refine ⟨Units.mk0 c hc0, ?_⟩
    change D.CongruentOne ((f.1 : F) / algebraMap K F c)
    rw [hc, div_div_cancel₀ f.1.ne_zero]
    exact hg
  · rintro ⟨c, hc⟩
    apply (QuotientAddGroup.eq_zero_iff (D.unitDivisor f)).mpr
    refine ⟨(f.1 : F) / algebraMap K F (c : K), hc, fun v => ?_⟩
    change (D.unitDivisor f : Divisor K F) v =
      v.ord ((f.1 : F) / algebraMap K F (c : K))
    rw [D.unitDivisor_apply, div_eq_mul_inv,
      v.ord_mul f.1.ne_zero (inv_ne_zero ((map_ne_zero (algebraMap K F)).mpr c.ne_zero)),
      v.ord_inv]
    have hconst : v.ord (algebraMap K F (c : K)) = 0 := by
      exact v.ord_coe_unit (Units.map (algebraMap K v.toValuationSubring) c)
    rw [hconst]
    omega

end AlgebraicCurve.Modulus
