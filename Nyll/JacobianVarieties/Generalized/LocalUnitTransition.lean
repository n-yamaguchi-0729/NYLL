/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalUnitQuotient
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Reduction between moduli and finite local-unit jets

Shrinking a modulus reduces each retained local factor modulo a smaller
maximal-ideal power and forgets the removed places. These concrete reduction
maps are surjective and commute with the principal boundary and the transition
on degree-zero divisor classes. Lifting an ordinary Picard class and then its
local-unit correction proves that the class-group transition is surjective.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

open LubinTate.Valuations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E G : Modulus K F}

/-- A place in the smaller support also belongs to the larger support. -/
theorem ne_zero_of_le (h : E ≤ D) (v : Place K F) (hv : E v ≠ 0) : D v ≠ 0 := by
  intro hd
  apply hv
  exact Nat.eq_zero_of_le_zero (hd ▸ h v)

/-- A function regular and invertible along a larger modulus has the same property
along every smaller modulus. -/
def restrictAwayUnits (h : E ≤ D) : D.awayUnits →* E.awayUnits where
  toFun f := ⟨f.1, fun v hv => f.2 v (ne_zero_of_le h v hv)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Reduce the actual truncated local-unit factors and forget removed places. -/
def jetReduction (h : E ≤ D) : D.LocalJetUnits →* E.LocalJetUnits where
  toFun q v := Units.map
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal
      v.1.toValuationSubring) (h v.1)))
    (q ⟨v.1, ne_zero_of_le h v.1 v.2⟩)
  map_one' := by
    funext v
    exact map_one _
  map_mul' q r := by
    funext v
    exact map_mul _ _ _

/-- Reduction of jets agrees with restriction of their rational-function representative. -/
@[simp]
theorem jetReduction_jetMap (h : E ≤ D) (f : D.awayUnits) :
    jetReduction h (D.jetMap f) = E.jetMap (restrictAwayUnits h f) := by
  funext v
  apply Units.ext
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (I := IsLocalRing.maximalIdeal v.1.toValuationSubring) (h v.1))
    (Ideal.Quotient.mk _
      (D.localUnit f v.1 (ne_zero_of_le h v.1 v.2) : v.1.toValuationSubring)) =
      Ideal.Quotient.mk _
        (E.localUnit (restrictAwayUnits h f) v.1 v.2 : v.1.toValuationSubring)
  rw [Ideal.Quotient.factor_mk]
  congr 1

/-- Every tuple of smaller jets lifts to a tuple of larger jets. -/
theorem jetReduction_surjective (h : E ≤ D) : Function.Surjective (jetReduction h) := by
  classical
  intro q
  let u (v : Place K F) : v.toValuationSubringˣ :=
    if hv : E v ≠ 0 then (v.unitReduction_surjective hv (q ⟨v, hv⟩)).choose else 1
  refine ⟨fun v => unitReduction
    ((IsLocalRing.maximalIdeal v.1.toValuationSubring) ^ D v.1) (u v.1), ?_⟩
  funext v
  apply Units.ext
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (I := IsLocalRing.maximalIdeal v.1.toValuationSubring) (h v.1))
      (Ideal.Quotient.mk _ (u v.1 : v.1.toValuationSubring)) = (q v).val
  rw [Ideal.Quotient.factor_mk]
  have hu : unitReduction ((IsLocalRing.maximalIdeal v.1.toValuationSubring) ^ E v.1)
      (u v.1) = q v := by
    simpa only [u, dite_eq_left v.2] using
      (v.1.unitReduction_surjective v.2 (q v)).choose_spec
  exact congrArg Units.val hu

/-- Reducing diagonal scalars gives the same diagonal scalars. -/
@[simp]
theorem jetReduction_scalarJets (h : E ≤ D) (c : Kˣ) :
    jetReduction h (D.scalarJets c) = E.scalarJets c := by
  change jetReduction h (D.jetMap (D.scalarAway c)) = E.jetMap (E.scalarAway c)
  rw [jetReduction_jetMap]
  congr 1

/-- Reduction to the same modulus is the identity on all local-unit jets. -/
@[simp]
theorem jetReduction_refl (D : Modulus K F) (q : D.LocalJetUnits) :
    jetReduction (le_refl D) q = q := by
  obtain ⟨f, rfl⟩ := D.jetMap_surjective q
  rw [jetReduction_jetMap]
  congr 1

/-- Reducing twice is the same as reducing directly. -/
theorem jetReduction_trans (h : E ≤ D) (h' : G ≤ E) (q : D.LocalJetUnits) :
    jetReduction h' (jetReduction h q) = jetReduction (h'.trans h) q := by
  obtain ⟨f, rfl⟩ := D.jetMap_surjective q
  rw [jetReduction_jetMap, jetReduction_jetMap, jetReduction_jetMap]
  rfl

/-- Reduction descends to the quotient by diagonal scalar units. -/
def localUnitQuotientTransition (h : E ≤ D) :
    D.LocalJetUnits ⧸ D.scalarJets.range →* E.LocalJetUnits ⧸ E.scalarJets.range :=
  QuotientGroup.map _ _ (jetReduction h) (by
    rintro q ⟨c, rfl⟩
    exact ⟨c, (jetReduction_scalarJets h c).symm⟩)

variable [HasPrincipalDivisors K F]

/-- The principal divisor itself is unchanged when the modulus shrinks. -/
theorem restrictDivisors_unitDivisor (h : E ≤ D) (f : D.awayUnits) :
    restrictDivisors h (D.unitDivisor f) = E.unitDivisor (restrictAwayUnits h f) := by
  apply Subtype.ext
  ext v
  change (D.unitDivisor f : Divisor K F) v =
    (E.unitDivisor (restrictAwayUnits h f) : Divisor K F) v
  rw [unitDivisor_apply, unitDivisor_apply]
  rfl

/-- The principal boundary commutes with the transition on divisor classes. -/
theorem transition_unitBoundary (h : E ≤ D) (f : D.awayUnits) :
    transition h (D.unitBoundary (Additive.ofMul f)) =
      E.unitBoundary (Additive.ofMul (restrictAwayUnits h f)) := by
  change transition h (D.mkZero (D.unitDivisor f)) =
    E.mkZero (E.unitDivisor (restrictAwayUnits h f))
  rw [transition_mkZero, restrictDivisors_unitDivisor]

/-- The local-unit boundary commutes with reduction of the modulus. -/
theorem jetBoundary_reduction (h : E ≤ D) (q : D.LocalJetUnits) :
    E.jetBoundary (jetReduction h q) =
      Multiplicative.ofAdd (transition h (D.jetBoundary q).toAdd) := by
  obtain ⟨f, rfl⟩ := D.jetMap_surjective q
  rw [jetReduction_jetMap, jetBoundary_jetMap, jetBoundary_jetMap]
  exact (transition_unitBoundary h f).symm

/-- Every degree-zero divisor class with a smaller modulus lifts to the larger modulus. -/
theorem transition_surjective (h : E ≤ D) : Function.Surjective (transition h) := by
  intro x
  obtain ⟨y, hy⟩ := D.toPic0_surjective (E.toPic0 x)
  have hk : E.toPic0 (x - transition h y) = 0 := by
    rw [map_sub, toPic0_transition, hy, sub_self]
  obtain ⟨q, hq⟩ := E.jetBoundaryToKernel_surjective
    (Multiplicative.ofAdd ⟨x - transition h y, hk⟩)
  obtain ⟨r, hr⟩ := jetReduction_surjective h q
  have hqval : (E.jetBoundary q).toAdd = x - transition h y :=
    congrArg (fun a : Multiplicative E.toPic0.ker => a.toAdd.1) hq
  have hcomm := congrArg Multiplicative.toAdd (jetBoundary_reduction h r)
  change (E.jetBoundary (jetReduction h r)).toAdd = transition h (D.jetBoundary r).toAdd
    at hcomm
  refine ⟨y + (D.jetBoundary r).toAdd, ?_⟩
  rw [map_add, ← hcomm, hr, hqval, add_comm, sub_add_cancel]

end AlgebraicCurve.Modulus
