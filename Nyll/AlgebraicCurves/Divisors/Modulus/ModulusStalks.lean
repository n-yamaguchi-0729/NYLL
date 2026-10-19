/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Modulus congruence in the actual stalks of a smooth proper curve

The input is a scheme over an arbitrary field, integral, proper and smooth of
relative dimension one. The existing valuative-criterion theorem supplies the
closed point belonging to each place of its function field. We construct the
actual ring equivalence between its stalk and the valuation subring, and
transport congruence through every power of the maximal ideal.

This identifies the local rings and their full infinitesimal thickenings; it
does not assert the global correspondence with effective Cartier divisors or
compatibility with extension of the base field. No curve model or stalk
comparison is taken as additional input.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.Modulus

/-- The actual stalk embedding identifies the local ring with a place whenever
their images in the function field agree. -/
def stalkEquivOfRange {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    [Algebra K C.functionField] (x : C) (v : Place K C.functionField)
    (hrange : (algebraMap (C.presheaf.stalk x) C.functionField).range =
      v.toValuationSubring.toSubring) :
    C.presheaf.stalk x ≃+* v.toValuationSubring := by
  let j : C.presheaf.stalk x →+* v.toValuationSubring :=
    (algebraMap (C.presheaf.stalk x) C.functionField).codRestrict
      v.toValuationSubring.toSubring (fun a => by
        rw [← hrange]
        exact ⟨a, rfl⟩)
  apply RingEquiv.ofBijective j
  constructor
  · intro a b hab
    exact IsFractionRing.injective (C.presheaf.stalk x) C.functionField
      (congrArg Subtype.val hab)
  · intro a
    have ha : (a : C.functionField) ∈
        (algebraMap (C.presheaf.stalk x) C.functionField).range := by
      rw [hrange]
      exact a.2
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩

/-- The stalk comparison is induced by its specified function-field embedding. -/
theorem coe_stalkEquivOfRange {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    [Algebra K C.functionField] (x : C) (v : Place K C.functionField)
    (hrange : (algebraMap (C.presheaf.stalk x) C.functionField).range =
      v.toValuationSubring.toSubring) (a : C.presheaf.stalk x) :
    (stalkEquivOfRange x v hrange a : C.functionField) =
      algebraMap (C.presheaf.stalk x) C.functionField a := rfl

private theorem mem_maximalIdeal_pow_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (a : R) :
    e a ∈ (IsLocalRing.maximalIdeal S) ^ n ↔
      a ∈ (IsLocalRing.maximalIdeal R) ^ n := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ :=
      (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp ha
    exact e.injective hba ▸ hb
  · intro ha
    exact Ideal.mem_map_of_mem e.toRingHom ha

/-- Every place belongs to exactly one closed point of the given proper smooth
integral curve. The base-field algebra on the function field is the one induced
by the structure morphism. -/
theorem existsUnique_closedPoint_of_place {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, ∃! x : C, IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range =
        v.toValuationSubring.toSubring := by
  intro _functionFieldAlgebra v
  obtain ⟨x, hx, hrange⟩ := exists_closedPoint_range_stalk_eq c v
  refine ⟨x, ⟨hx, hrange⟩, fun y hy => ?_⟩
  exact eq_of_range_stalk_eq c y x (hy.2.trans hrange.symm)

/-- At the closed point belonging to a place, local modulus congruence is
exactly congruence of a stalk unit modulo the same maximal-ideal power. The
stalk equivalence and its compatibility with the function field are constructed
from the actual scheme. No perfectness or algebraic closure is required. -/
theorem exists_closedPoint_stalkEquiv_congruentOne {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, ∃ x : C, IsClosed ({x} : Set C) ∧
      ∃ e : C.presheaf.stalk x ≃+* v.toValuationSubring,
        (∀ a : C.presheaf.stalk x,
          (e a : C.functionField) = algebraMap (C.presheaf.stalk x) C.functionField a) ∧
        ∀ (n : ℕ) (f : C.functionField), v.CongruentOne n f ↔
          ∃ w : (C.presheaf.stalk x)ˣ,
            algebraMap (C.presheaf.stalk x) C.functionField
              (w : C.presheaf.stalk x) = f ∧
            (w : C.presheaf.stalk x) - 1 ∈
              (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) ^ n := by
  intro _functionFieldAlgebra v
  obtain ⟨x, hx, hrange⟩ := exists_closedPoint_range_stalk_eq c v
  let e : C.presheaf.stalk x ≃+* v.toValuationSubring := stalkEquivOfRange x v hrange
  have hcoe : ∀ a : C.presheaf.stalk x,
      (e a : C.functionField) = algebraMap (C.presheaf.stalk x) C.functionField a :=
    coe_stalkEquivOfRange x v hrange
  refine ⟨x, hx, e, hcoe, fun n f => ?_⟩
  constructor
  · rintro ⟨z, hz, hpow⟩
    let w : (C.presheaf.stalk x)ˣ := Units.map e.symm.toMonoidHom z
    have hew : e (w : C.presheaf.stalk x) = (z : v.toValuationSubring) :=
      e.apply_symm_apply _
    refine ⟨w, ?_, ?_⟩
    · rw [← hcoe, hew]
      exact hz
    · apply (mem_maximalIdeal_pow_iff e n ((w : C.presheaf.stalk x) - 1)).mp
      rw [map_sub, map_one, hew]
      exact hpow
  · rintro ⟨w, hw, hpow⟩
    refine ⟨Units.map e.toMonoidHom w, ?_, ?_⟩
    · change (e (w : C.presheaf.stalk x) : C.functionField) = f
      rw [hcoe]
      exact hw
    · change e (w : C.presheaf.stalk x) - 1 ∈
        (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n
      rw [← map_one e, ← map_sub e]
      exact (mem_maximalIdeal_pow_iff e n ((w : C.presheaf.stalk x) - 1)).mpr hpow

end AlgebraicCurve.Modulus
