/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.LaurentCompletionDegEqOne
import Mathlib.RingTheory.LaurentSeries

/-! # The actual integral completion at a degree-one place

A valuation-preserving Laurent identification restricts to a K-algebra
isomorphism from power series onto the original completed valuation ring.
The constant-field algebra structures remain the native ones. The inclusion
in the completed field is computed explicitly, so pulling a Cartier family
back along the induced spectrum isomorphism preserves its original scalar
map and is compatible with the generic Laurent fibre.
-/

noncomputable section

open scoped WithZero

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Restrict an actual valuation-preserving Laurent field identification to
its integral rings. No new algebra structure on either ring is introduced. -/
def powerSeriesEquivCompletionIntegers
    (v : Place K F) (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : v.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x) :
    PowerSeries K ≃ₐ[K] v.adicCompletionIntegers := by
  have hmem (f : PowerSeries K) :
      E.symm (HahnSeries.ofPowerSeries ℤ K f) ∈ v.adicCompletionIntegers := by
    change (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
      (E.symm (HahnSeries.ofPowerSeries ℤ K f)) ≤ 1
    rw [← hE, E.apply_symm_apply]
    exact (LaurentSeries.val_le_one_iff_eq_coe K _).mpr ⟨f, rfl⟩
  let j : PowerSeries K →ₐ[K] v.adicCompletionIntegers :=
    { toRingHom := (E.symm.toRingHom.comp
        (HahnSeries.ofPowerSeries ℤ K)).codRestrict v.adicCompletionIntegers hmem
      commutes' := fun a => by
        apply Subtype.ext
        change E.symm (algebraMap K (LaurentSeries K) a) =
          algebraMap K v.adicCompletion a
        exact E.symm.commutes a }
  refine AlgEquiv.ofBijective j ⟨?_, ?_⟩
  · intro f g h
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    apply E.symm.injective
    exact congrArg Subtype.val h
  · intro x
    have hx : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
        (E (x : v.adicCompletion)) ≤ 1 := by
      rw [hE]
      exact x.property
    obtain ⟨f, hf⟩ := (LaurentSeries.val_le_one_iff_eq_coe K _).mp hx
    refine ⟨f, Subtype.ext ?_⟩
    change E.symm (HahnSeries.ofPowerSeries ℤ K f) = (x : v.adicCompletion)
    rw [hf, E.symm_apply_apply]

/-- The integral identification is the restriction of the specified field
identification, including the native inclusion into the completed field. -/
theorem powerSeriesEquivCompletionIntegers_coe
    (v : Place K F) (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : v.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x)
    (f : PowerSeries K) :
    algebraMap v.adicCompletionIntegers v.adicCompletion
      (v.powerSeriesEquivCompletionIntegers E hE f) =
        E.symm (HahnSeries.ofPowerSeries ℤ K f) := rfl

/-- At a degree-one place the field and integral identifications are
constructed together from an actual uniformizer, with their inclusion
compatibility retained. -/
theorem exists_completion_and_integers_algEquiv_of_deg_eq_one
    (v : Place K F) (hv : v.deg = 1) (t : F) (ht : v.ord t = 1) :
    ∃ (E : v.adicCompletion ≃ₐ[K] LaurentSeries K)
      (O : PowerSeries K ≃ₐ[K] v.adicCompletionIntegers),
      E (algebraMap F v.adicCompletion t) = HahnSeries.single (1 : ℤ) (1 : K) ∧
      (∀ x : F, (E (algebraMap F v.adicCompletion x)).order = v.ord x) ∧
      Continuous E ∧ Continuous E.symm ∧
      (∀ x : v.adicCompletion,
        (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x) ∧
      ∀ f : PowerSeries K,
        algebraMap v.adicCompletionIntegers v.adicCompletion (O f) =
          E.symm (HahnSeries.ofPowerSeries ℤ K f) := by
  obtain ⟨E, hEt, hEord, hEc, hEic, hEval⟩ :=
    v.exists_adicCompletion_algEquiv_laurentSeries_of_deg_eq_one hv t ht
  exact ⟨E, v.powerSeriesEquivCompletionIntegers E hEval,
    hEt, hEord, hEc, hEic, hEval,
    v.powerSeriesEquivCompletionIntegers_coe E hEval⟩

end AlgebraicCurve.Place
