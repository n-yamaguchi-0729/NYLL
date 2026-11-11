/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexEqRamificationIdxFiberCenter
public import Nyll.AlgebraicCurves.Places.Ramification.FiberCenterResidueComparison
public import Nyll.AlgebraicCurves.Places.Ramification.NegLogValuationFiberCenterEqOrd
public import Nyll.AlgebraicCurves.Places.Ramification.LeOrdIffMemPowFiberCenter
public import Nyll.AlgebraicCurves.Places.Orders.EqOrdAddHom
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Places.ValuationRings.IntegralClosureAtOrdFiberNonneg
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqOneIsRational
public import Nyll.AlgebraicCurves.Places.Degree.FinrankPrimePow
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Trace.Quotient

/-!
# Residue-field trace on the actual integral closure

The extension of the base maximal ideal factors into the actual ramification powers.
Chinese remainders preserve the specified residue-field action, so quotient traces add.
For rational fibre places this gives the original ramification-weighted evaluation formula.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid
open AlgebraicCurve

namespace AlgebraicCurve.Place.ResidueTrace

section AbstractTrace

/-- The trace vanishes on a subsingleton algebra. -/
theorem trace_of_subsingleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Subsingleton A] (a : A) : Algebra.trace R A a = 0 := by
  rw [Algebra.trace_apply, Subsingleton.elim ((Algebra.lmul R A) a) 0, map_zero]

/-- A scalar plus a nilpotent has trace equal to rank times that scalar. -/
theorem trace_eq_smul_finrank_of_isNilpotent_sub_algebraMap {R A : Type*}
    [CommRing R] [IsReduced R] [StrongRankCondition R] [CommRing A] [Algebra R A]
    [Module.Free R A] {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) :
    Algebra.trace R A a = Module.finrank R A • μ := by
  have hzero : Algebra.trace R A (a - algebraMap R A μ) = 0 :=
    (Algebra.isNilpotent_trace_of_isNilpotent h).eq_zero
  have hsplit : a = (a - algebraMap R A μ) + algebraMap R A μ := by abel
  rw [hsplit, map_add, hzero, zero_add, Algebra.trace_algebraMap]

end AbstractTrace

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- An integral element has nonnegative order at the same place. -/
theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  _root_.AlgebraicCurve.Place.ord_nonneg_of_mem v hf

/-- Membership of a nonzero element is measured by its order at the same place. -/
theorem mem_iff_ord_nonneg (v : Place K F) {f : F} (_hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg v _hf

/-- The existing normalized additive valuation is the place order. -/
theorem eq_ord_of_addHom_of_nonneg_iff (w : Place K F) (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x :=
  _root_.AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w φ hmul hone hiff hx

/-- The residue map preserves the original constant-field algebra map. -/
theorem residue_algebraMap (v : Place K F) (lam : K) :
    IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring lam)
      = algebraMap K v.ResidueField lam := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- Evaluation of an integral element gives its original residue. -/
theorem algebraMap_evalAt_coe (v : Place K F) (hv : v.IsRational) (r : v.toValuationSubring) :
    algebraMap K v.ResidueField
        (v.evalAt (algebraMap v.toValuationSubring F r))
      = IsLocalRing.residue v.toValuationSubring r := by
  have hcoe : algebraMap v.toValuationSubring F r = (r : F) := rfl
  rw [hcoe]
  have hmem : (r : F) ∈ v.toValuationSubring := r.2
  rw [v.algebraMap_evalAt hv hmem]

end PlaceFacts

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Dict

open _root_.AlgebraicCurve.Place hiding mem_iff_ord_nonneg ord_nonneg_of_mem
  le_ord_iff_mem_pow_fiberCenter neg_log_valuation_fiberCenter_eq_ord eq_ord_of_addHom_of_nonneg_iff

variable {v : Place K F} {w : Place K F'}

/-- The fibre-centre valuation computes the extending place order. -/
theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x :=
  _root_.AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord hw hx

/-- Powers of the fibre centre measure the original order bound. -/
theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n :=
  _root_.AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw hc n

/-- The place and ideal ramification indices agree at the actual fibre centre. -/
theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter v hw

/-- The map from the integral closure to the valuation subring of the extending place. -/
def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.toValuationSubringOfRestrictEq hw

omit [FiniteDimensional F F'] in
/-- The restricted inclusion has the original field value. -/
@[scoped simp]
theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_toValuationSubringOfRestrictEq hw c

/-- The residue homomorphism on the integral closure, induced by the place above `v`. -/
def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter hw

omit [FiniteDimensional F F'] in
/-- The centre residue map is the residue of the same restricted inclusion. -/
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueOfCenter_apply hw c

/-- The actual centre residue map has the fibre centre as kernel. -/
theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.ker_residueOfCenter hw

/-- The actual residue map at the fibre centre is surjective. -/
theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.surjective_residueOfCenter hw

/-- The quotient by the fibre centre identified with the residue field of the place. -/
def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueFieldEquivQuotientCenter hw

/-- The quotient comparison evaluates through the same residue map. -/
theorem residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.residueFieldEquivQuotientCenter_mk hw c

/-- The valuation-subring equivalence induced by equality of two places. -/
def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.placeCongrEquiv h
/-- Equality transport of places preserves the underlying field element. -/
@[scoped simp]
theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.coe_placeCongrEquiv h x

/-- The residue-field equivalence induced by equality of the restricted and base places. -/
def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.restrictResidueFieldEquiv hw

omit [FiniteDimensional F F'] in
/-- Restriction transport commutes with the original residue maps. -/
theorem restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (placeCongrEquiv hw a) :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.restrictResidueFieldEquiv_residue hw a

/-- The actual residue comparison identifies the inertia degrees. -/
theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (fiberCenter F' v hw).asIdeal.inertiaDeg v.toValuationSubring :=
  _root_.AlgebraicCurve.Place.FiberCenterResidueComparison.inertiaDeg_eq_inertiaDeg_fiberCenter hw

end Dict

namespace Blocks

open _root_.AlgebraicCurve.Place hiding mem_iff_ord_nonneg ord_nonneg_of_mem
  le_ord_iff_mem_pow_fiberCenter neg_log_valuation_fiberCenter_eq_ord eq_ord_of_addHom_of_nonneg_iff
open Dict

local instance : DecidableEq (Place K F') := Classical.decEq _

variable (v : Place K F)

/-- The integral closure over the base valuation ring is a free module. -/
scoped instance instFreeIntegralClosureAt : Module.Free v.toValuationSubring (integralClosureAt F'
  v) :=
  Module.free_of_finite_type_torsion_free'

/-- The extension of the maximal ideal of the base valuation ring to the integral closure. -/
abbrev conductorIdeal : Ideal (integralClosureAt F' v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (integralClosureAt F' v))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
/-- The extended base maximal ideal is nonzero in the actual integral closure. -/
theorem conductorIdeal_ne_bot : conductorIdeal (F' := F') v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπmem : algebraMap v.toValuationSubring (integralClosureAt F' v) π
      ∈ conductorIdeal (F' := F') v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hπmem
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hπmem, map_zero]))

/-- The base residue field acts on the quotient by its extended maximal ideal. -/
noncomputable scoped instance conductorQuotientAlgebra :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

omit [Algebra K F'] [IsScalarTower K F F'] in
/-- Reduction of the integral trace is the trace on the actual quotient. -/
theorem residue_trace_eq_trace_mk (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c)
      = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) :=
  (Algebra.trace_quotient_mk (R := v.toValuationSubring) (S := integralClosureAt F' v) c).symm

variable {v} {w : Place K F'}

/-- The ideal of the fibre centre raised to its ramification index. -/
abbrev fiberCenterPow (hw : w.restrict F = v) : Ideal (integralClosureAt F' v) :=
  (fiberCenter F' v hw).asIdeal
    ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

/-- The extended maximal ideal lies in the ramification power. -/
theorem conductorIdeal_le_fiberCenterPow (hw : w.restrict F = v) :
    conductorIdeal (F' := F') v ≤ fiberCenterPow hw :=
  Ideal.le_pow_ramificationIdx'

/-- The base residue field acts on the actual ramification-power quotient. -/
noncomputable scoped instance fiberCenterPowQuotientAlgebra (hw : w.restrict F = v) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberCenterPow hw))

/-- The ramification-power quotient is finite over the base residue field. -/
scoped instance instFiniteFiberCenterPowQuot (hw : w.restrict F = v) :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := by
  have : IsScalarTower v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)

/-- The ramification-power quotient is free over the base residue field. -/
scoped instance instFreeFiberCenterPowQuot (hw : w.restrict F = v) :
    Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Module.Free.of_divisionRing _ _

/-- A difference in the fibre centre is nilpotent in its power quotient. -/
theorem isNilpotent_mk_sub_algebraMap (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    IsNilpotent (Ideal.Quotient.mk (fiberCenterPow hw) c
      - algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (IsLocalRing.residue v.toValuationSubring r)) := by
  have halg : algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) (IsLocalRing.residue v.toValuationSubring r)
        = Ideal.Quotient.mk (fiberCenterPow hw)
            (algebraMap v.toValuationSubring (integralClosureAt F' v) r) := rfl
  rw [halg, ← map_sub]
  refine ⟨(IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (fiberCenter F' v hw).asIdeal, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr _

/-- The nilpotent scalar difference computes the trace in the power quotient. -/
theorem trace_mk_fiberCenterPow (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
        (Ideal.Quotient.mk (fiberCenterPow hw) c)
      = Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberCenterPow hw)
          • IsLocalRing.residue v.toValuationSubring r :=
  trace_eq_smul_finrank_of_isNilpotent_sub_algebraMap (isNilpotent_mk_sub_algebraMap hw hr)

/-- At rational places the quotient rank is the actual ramification index. -/
theorem finrank_fiberCenterPow (hw : w.restrict F = v) (hwrat : w.IsRational)
    (hvrat : v.IsRational) :
    Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
      = w.ramificationIndex F := by
  have : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have hne : (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal ≠ 0 := by
    rw [← Dict.ramificationIndex_eq_ramificationIdx_fiberCenter hw]
    exact w.ramificationIndex_pos.ne'
  have := fiberCenter_liesOver hw
  have key : Module.finrank
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal
        ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (fiberCenter F' v hw).asIdeal) = w.ramificationIndex F := by
    rw [AlgebraicCurves.Compat.FinrankPrimePow.finrank_prime_pow_ramificationIdx
        _ _ (fiberCenter F' v hw).ne_bot hne,
      ← Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal v.toValuationSubring)
        (fiberCenter F' v hw).asIdeal,
      ← inertiaDeg_eq_inertiaDeg_fiberCenter hw,
      w.inertiaDeg_eq_one_of_isRational hwrat (hw.symm ▸ hvrat), mul_one,
      ← Dict.ramificationIndex_eq_ramificationIdx_fiberCenter hw]
  exact key

variable (v) [HasPrincipalDivisors K F']

/-- The ramification power for a place above `v`, and the unit ideal for other places. -/
def fiberIdeal (w : Place K F') : Ideal (integralClosureAt F' v) :=
  if hw : w.restrict F = v then fiberCenterPow hw else ⊤

omit [HasPrincipalDivisors K F'] in
/-- A place above the base uses its actual ramification-power ideal. -/
theorem fiberIdeal_of_mem {w : Place K F'} (hw : w.restrict F = v) :
    fiberIdeal v w = fiberCenterPow hw := dite_eq_left hw

omit [HasPrincipalDivisors K F'] in
/-- A place outside the fibre uses the unit ideal. -/
theorem fiberIdeal_of_notMem {w : Place K F'} (hw : ¬w.restrict F = v) :
    fiberIdeal v w = ⊤ := dite_eq_right hw

omit [HasPrincipalDivisors K F'] in
/-- The extended base maximal ideal lies in every chosen fibre ideal. -/
theorem conductorIdeal_le_fiberIdeal (w : Place K F') :
    conductorIdeal (F' := F') v ≤ fiberIdeal v w := by
  by_cases hw : w.restrict F = v
  · rw [fiberIdeal_of_mem v hw]
    exact conductorIdeal_le_fiberCenterPow hw
  · rw [fiberIdeal_of_notMem v hw]
    exact le_top

omit [HasPrincipalDivisors K F'] in
/-- Fibre ideals at distinct places are coprime. -/
theorem isCoprime_fiberIdeal {w w' : Place K F'} (hne : w ≠ w') :
    IsCoprime (fiberIdeal v w) (fiberIdeal v w') := by
  by_cases hw : w.restrict F = v
  · by_cases hw' : w'.restrict F = v
    · rw [fiberIdeal_of_mem v hw, fiberIdeal_of_mem v hw']
      have : (fiberCenter F' v hw).asIdeal.IsMaximal :=
        (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
      have : (fiberCenter F' v hw').asIdeal.IsMaximal :=
        (fiberCenter F' v hw').isPrime.isMaximal (fiberCenter F' v hw').ne_bot
      refine IsCoprime.pow (Ideal.isCoprime_of_isMaximal ?_)
      intro heq
      exact hne (eq_of_fiberCenter_eq hw hw' (HeightOneSpectrum.ext heq))
    · rw [fiberIdeal_of_notMem v hw', ← Ideal.one_eq_top]
      exact isCoprime_one_right
  · rw [fiberIdeal_of_notMem v hw, ← Ideal.one_eq_top]
    exact isCoprime_one_left

omit [HasPrincipalDivisors K F'] in
/-- The multiplicity of the fibre centre is its ramification index. -/
theorem count_normalizedFactors_conductorIdeal {w : Place K F'} (hw : w.restrict F = v) :
    (normalizedFactors (conductorIdeal (F' := F') v)).count (fiberCenter F' v hw).asIdeal
      = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
          (fiberCenter F' v hw).asIdeal := by
  have : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (conductorIdeal_ne_bot (F' := F') v) inferInstance (fiberCenter F' v hw).ne_bot).symm

/-- The extended base maximal ideal factors over the actual finite fibre. -/
theorem conductorIdeal_eq_prod_fiber :
    conductorIdeal (F' := F') v = ∏ w ∈ v.fiber F', fiberIdeal v w := by
  classical
  have hbot := conductorIdeal_ne_bot (F' := F') v
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (conductorIdeal v)
    with hS
  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    have : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩
  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))
  calc
    conductorIdeal (F' := F') v = ∏ Q ∈ S.toFinset, Q ^ S.count Q := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hbot]
    _ = ∏ Q ∈ T, Q ^ S.count Q := by
          refine Finset.prod_subset hsub fun Q _ hQ => ?_
          rw [Multiset.count_eq_zero_of_notMem
            (fun h => hQ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = ∏ w' ∈ (v.fiber F').attach,
          (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
            ^ S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
          rw [hT, Finset.prod_image hinj]
    _ = ∏ w' ∈ (v.fiber F').attach, fiberIdeal v w'.1 := by
          refine Finset.prod_congr rfl fun w' _ => ?_
          rw [hS, count_normalizedFactors_conductorIdeal v (mem_fiber.mp w'.2),
            fiberIdeal_of_mem v (mem_fiber.mp w'.2)]
    _ = ∏ w ∈ v.fiber F', fiberIdeal v w := Finset.prod_attach (v.fiber F') (fiberIdeal v)

omit [HasPrincipalDivisors K F'] in
/-- Adding factors decreases the product of fibre ideals. -/
theorem prod_fiberIdeal_le_of_subset {s t : Finset (Place K F')} (hst : s ⊆ t) :
    ∏ w ∈ t, fiberIdeal v w ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  rw [← Finset.prod_sdiff hst]
  exact Ideal.mul_le_right

/-- The extended base maximal ideal lies in every finite product. -/
theorem conductorIdeal_le_prod_fiberIdeal (s : Finset (Place K F')) :
    conductorIdeal (F' := F') v ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  calc conductorIdeal (F' := F') v
      = ∏ w ∈ v.fiber F', fiberIdeal v w := conductorIdeal_eq_prod_fiber v
    _ = ∏ w ∈ v.fiber F' ∪ s, fiberIdeal v w := by
        refine Finset.prod_subset Finset.subset_union_left fun w _ hw' => ?_
        exact (fiberIdeal_of_notMem v fun hmem => hw' (mem_fiber.mpr hmem)).trans
          Ideal.one_eq_top.symm
    _ ≤ ∏ w ∈ s, fiberIdeal v w :=
        prod_fiberIdeal_le_of_subset v Finset.subset_union_right

/-- The actual fibre-ideal quotient uses the induced base residue action. -/
noncomputable scoped instance fiberIdealQuotientAlgebra (w : Place K F') :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberIdeal v w))

/-- The product-ideal quotient uses the induced base residue action. -/
noncomputable scoped instance prodFiberIdealQuotientAlgebra (s : Finset (Place K F')) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_prod_fiberIdeal v s))

omit [HasPrincipalDivisors K F'] in
omit [Algebra K F'] [IsScalarTower K F F'] in
/-- Restriction of scalars gives finiteness over the base residue field. -/
theorem finite_quotient_of_conductorLE (Q : Ideal (integralClosureAt F' v))
    [Algebra (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)]
    [IsScalarTower v.toValuationSubring (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q)] :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)


/-- The residue-field trace of a finite product quotient is the sum of traces. -/
theorem trace_mk_prod_fiberIdeal (c : integralClosureAt F' v) (s : Finset (Place K F')) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)
        (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c)
      = ∑ w ∈ s,
          Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberIdeal v w)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      have : Subsingleton
          (integralClosureAt F' v ⧸ (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [Finset.prod_empty]; exact Ideal.one_eq_top)
      conv_rhs => rw [Finset.sum_empty]
      exact trace_of_subsingleton
        (Ideal.Quotient.mk (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w) c)
  | cons a s ha ih =>
      have hcop : IsCoprime (fiberIdeal v a) (∏ w ∈ s, fiberIdeal v w) :=
        IsCoprime.prod_right fun w hw => isCoprime_fiberIdeal v (fun h => ha (h ▸ hw))
      have hprod : ∏ w ∈ Finset.cons a s ha, fiberIdeal v w
          = fiberIdeal v a ⊓ ∏ w ∈ s, fiberIdeal v w := by
        rw [Finset.prod_cons, Ideal.mul_eq_inf_of_isCoprime hcop]
      have : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        IsScalarTower.of_algebraMap_eq' rfl
      have := finite_quotient_of_conductorLE v (fiberIdeal v a)
      have := finite_quotient_of_conductorLE v (∏ w ∈ s, fiberIdeal v w)
      have : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := Module.Free.of_divisionRing _ _
      have : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) := Module.Free.of_divisionRing _ _
      set e : (integralClosureAt F' v ⧸ (∏ w ∈ Finset.cons a s ha, fiberIdeal v w)) ≃+*
          (integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        (Ideal.quotEquivOfEq hprod).trans
          (Ideal.quotientInfEquivQuotientProd _ _ hcop) with he
      have hemk : ∀ x : integralClosureAt F' v,
          e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
        intro x
        rw [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact Prod.ext
          (by rw [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk])
          (by rw [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk])
      have hkey : Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)
            = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
                ((integralClosureAt F' v ⧸ fiberIdeal v a)
                  × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w))
                ((Ideal.Quotient.mk (fiberIdeal v a) c,
                  Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) :
                  (integralClosureAt F' v ⧸ fiberIdeal v a)
                    × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)) := by
        refine (@Algebra.trace_eq_of_equiv_equiv
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
          (IsLocalRing.ResidueField v.toValuationSubring)
          ((integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring)) e ?_
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)).trans ?_
        · refine RingHom.ext fun x => ?_
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
          exact (hemk (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm
        · rw [hemk]
          rfl
      calc (Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ ∏ w ∈ Finset.cons a s ha, fiberIdeal v w)
              (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c))
          = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ fiberIdeal v a)
              (Ideal.Quotient.mk (fiberIdeal v a) c)
            + Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)
              (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) := by
            rw [hkey]; exact Algebra.trace_prod_apply _
        _ = ∑ w ∈ Finset.cons a s ha,
              Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
                (integralClosureAt F' v ⧸ fiberIdeal v w)
                (Ideal.Quotient.mk (fiberIdeal v w) c) := by
            rw [Finset.sum_cons, ih]

/-- The trace modulo the extended maximal ideal is the full fibre sum. -/
theorem trace_mk_conductor_eq_sum_fiber (c : integralClosureAt F' v) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
        (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
      = ∑ w ∈ v.fiber F',
          Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
            (integralClosureAt F' v ⧸ fiberIdeal v w)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  rw [← trace_mk_prod_fiberIdeal v c (v.fiber F')]
  have he : (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
        = Ideal.Quotient.mk (∏ w ∈ v.fiber F', fiberIdeal v w) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine @Algebra.trace_eq_of_equiv_equiv
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ ∏ w ∈ v.fiber F', fiberIdeal v w)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (conductorIdeal_eq_prod_fiber (F' := F') v)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

omit [HasPrincipalDivisors K F'] in
/-- The fibre-ideal and ramification-power traces agree with their actual residue actions. -/
theorem trace_mk_fiberIdeal_eq_trace_mk_fiberCenterPow [HasPrincipalDivisors K F']
    {w : Place K F'} (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberIdeal v w)
        (Ideal.Quotient.mk (fiberIdeal v w) c)
      = Algebra.trace (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (Ideal.Quotient.mk (fiberCenterPow hw) c) := by
  have he : (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw))
      (Ideal.Quotient.mk (fiberIdeal v w) c) = Ideal.Quotient.mk (fiberCenterPow hw) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine @Algebra.trace_eq_of_equiv_equiv
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberIdeal v w)
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (fiberIdeal_of_mem v hw)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

end Blocks

namespace Assembly

open _root_.AlgebraicCurve.Place hiding mem_iff_ord_nonneg ord_nonneg_of_mem
  le_ord_iff_mem_pow_fiberCenter neg_log_valuation_fiberCenter_eq_ord eq_ord_of_addHom_of_nonneg_iff
open Blocks

variable {v : Place K F} [HasPrincipalDivisors K F']

omit [HasPrincipalDivisors K F'] in
/-- Subtracting the actual evaluation gives an element of the centre. -/
theorem sub_algebraMap_evalAt_mem_fiberCenter {w : Place K F'} (hw : w.restrict F = v)
    (hwrat : w.IsRational) (c : integralClosureAt F' v) :
    c - algebraMap v.toValuationSubring (integralClosureAt F' v)
        (algebraMap K v.toValuationSubring
          (w.evalAt (algebraMap (integralClosureAt F' v) F' c)))
      ∈ (fiberCenter F' v hw).asIdeal := by
  set lam : K := w.evalAt (algebraMap (integralClosureAt F' v) F' c) with hlam
  set d : integralClosureAt F' v := c - algebraMap v.toValuationSubring
    (integralClosureAt F' v) (algebraMap K v.toValuationSubring lam) with hd
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Ideal.zero_mem _
  rw [mem_fiberCenter_iff_ord_pos hw hd0]
  have hcoe : algebraMap (integralClosureAt F' v) F' d
      = algebraMap (integralClosureAt F' v) F' c - algebraMap K F' lam := by
    rw [hd, map_sub]
    congr 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring
      F F',
      show (algebraMap v.toValuationSubring F) (algebraMap K v.toValuationSubring lam)
        = algebraMap K F lam from v.coe_algebraMap lam,
      ← IsScalarTower.algebraMap_apply]
  have hmem : algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring :=
    forall_mem_of_restrict_eq hw c
  have hres : residue w.toValuationSubring ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
      = algebraMap K w.ResidueField lam := (w.algebraMap_evalAt hwrat hmem).symm
  have hdmem : algebraMap (integralClosureAt F' v) F' d ∈ w.toValuationSubring := by
    rw [hcoe]
    exact sub_mem hmem (w.algebraMap_mem' lam)
  have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hd0
  rw [← w.mem_maximalIdeal_iff_ord_pos hdF hdmem]
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨algebraMap (integralClosureAt F' v) F' d, hdmem⟩ : w.toValuationSubring)
      = ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
        - algebraMap K w.toValuationSubring lam := by
    refine Subtype.ext ?_
    change algebraMap (integralClosureAt F' v) F' d
      = ((⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
          - algebraMap K w.toValuationSubring lam : w.toValuationSubring) : F')
    rw [hcoe]
    push_cast
    rw [w.coe_algebraMap]
  rw [hsplit, map_sub, hres, sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

local instance : DecidableEq (Place K F') := Classical.decEq _

/-- The integral trace reduces to the ramification-weighted evaluation sum. -/
theorem residue_trace_eq_sum_evalAt (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.trace v.toValuationSubring (integralClosureAt F' v) c)
      = ∑ w ∈ v.fiber F',
          w.ramificationIndex F
            • algebraMap K v.ResidueField
                (w.evalAt (algebraMap (integralClosureAt F' v) F' c)) := by
  classical
  rw [residue_trace_eq_trace_mk v c, trace_mk_conductor_eq_sum_fiber v c]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwv : w.restrict F = v := mem_fiber.mp hw
  have hsub := sub_algebraMap_evalAt_mem_fiberCenter hwv (hrat w hw) c
  rw [trace_mk_fiberIdeal_eq_trace_mk_fiberCenterPow v hwv c, trace_mk_fiberCenterPow hwv hsub,
    finrank_fiberCenterPow hwv (hrat w hw) hv, residue_algebraMap]

end Assembly

end AlgebraicCurve.Place.ResidueTrace
