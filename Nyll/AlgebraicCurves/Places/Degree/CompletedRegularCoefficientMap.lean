/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.LaurentCompletionIntegersDegEqOne
import Nyll.AlgebraicCurves.Places.Degree.TameCompletedTensorSplitting
import Nyll.SchemeTheory.RingTheory.Henselian.RegularReciprocalLaurentDeformation
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The regular coefficient map into the common Laurent valuation ring

The map is constructed through the original completed valuation rings.
Their native local map supplies integrality and residue compatibility on all
power series, not merely on rational functions. A strengthened construction
of the tame normalization retains valuation preservation on the whole
completed field. No continuity assumption on arbitrary formal series maps
is used to infer these integral properties.
-/

noncomputable section

open scoped WithZero AlgebraicCurve.Place

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Tame normalization retaining the full completed-field valuation, which
is required to transport integral group points to a common valuation ring. -/
theorem exists_adicCompletion_tame_normalized_valuation [IsAlgClosed K]
    (w : Place K F) (hw : w.deg = 1) (s : F) (e : ℕ)
    (he : (e : K) ≠ 0) (hs : w.ord s = (e : ℤ)) :
    ∃ E : w.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F w.adicCompletion s) = HahnSeries.single (e : ℤ) (1 : K) ∧
      Continuous E ∧
      (∀ x : F, (E (algebraMap F w.adicCompletion x)).order = w.ord x) ∧
      ∀ x : w.adicCompletion,
        (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x := by
  obtain ⟨t, ht⟩ := w.exists_ord_eq_one
  obtain ⟨E₀, _, hE₀ord, hE₀c, _, hE₀v⟩ :=
    w.exists_adicCompletion_algEquiv_laurentSeries_of_deg_eq_one hw t ht
  obtain ⟨A, hAs, hAord⟩ := LaurentSeries.exists_tameNormalization
    (E₀ (algebraMap F w.adicCompletion s)) e he ((hE₀ord s).trans hs)
  refine ⟨E₀.trans A, hAs,
    (LaurentSeries.continuous_of_order_preserving A.toRingHom hAord).comp hE₀c,
    fun x => (hAord _).trans (hE₀ord x), ?_⟩
  intro x
  exact (LaurentSeries.valuation_eq_of_order_preserving A.toRingHom hAord (E₀ x)).trans
    (hE₀v x)

/-- Restrict the actual normalized completion equivalence to the valuation
ring of the common Laurent parameter. All scalar structures are native. -/
def completionIntegersEquivLaurentOrder
    (w : Place K F) (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : w.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x) :
    w.adicCompletionIntegers ≃ₐ[K] (LaurentSeries.orderPlace (K := K)).toValuationSubring := by
  let j : w.adicCompletionIntegers →ₐ[K]
      (LaurentSeries.orderPlace (K := K)).toValuationSubring :=
    { toRingHom := (E.toRingHom.comp
        (algebraMap w.adicCompletionIntegers w.adicCompletion)).codRestrict _ (fun x => by
          change (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E (x : w.adicCompletion)) ≤ 1
          rw [hE]
          exact x.property)
      commutes' a := Subtype.ext (E.commutes a) }
  refine AlgEquiv.ofBijective j ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (E.injective (congrArg Subtype.val h))
  · intro y
    have hy : E.symm (y : LaurentSeries K) ∈ w.adicCompletionIntegers := by
      change Valued.v (E.symm (y : LaurentSeries K)) ≤ 1
      rw [← hE, E.apply_symm_apply]
      exact y.property
    exact ⟨⟨E.symm (y : LaurentSeries K), hy⟩, Subtype.ext (E.apply_symm_apply _)⟩

section Base

variable {B : Type*} [Field B] [Algebra K B] [Algebra B F]
  [IsScalarTower K B F] [Algebra.IsIntegral B F]

private def completedBaseAlgHom (w : Place K F) :
    (w.restrict B).adicCompletion →ₐ[K] w.adicCompletion where
  toRingHom := kw_ffgc_adicCompletionComap B w
  commutes' a := by
    change algebraMap (w.restrict B).adicCompletion w.adicCompletion
      (algebraMap K (w.restrict B).adicCompletion a) = algebraMap K w.adicCompletion a
    rw [IsScalarTower.algebraMap_apply K B (w.restrict B).adicCompletion,
      ← adicCompletionComap_algebraMap_algebraMap B w,
      ← IsScalarTower.algebraMap_apply K B F,
      ← IsScalarTower.algebraMap_apply K F w.adicCompletion]

private def completedBaseIntegerAlgHom (w : Place K F) :
    (w.restrict B).adicCompletionIntegers →ₐ[K] w.adicCompletionIntegers where
  toRingHom := kw_ffgc_adicCompletionComapIntegers B w
  commutes' a := by
    apply Subtype.ext
    exact (completedBaseAlgHom (B := B) w).commutes a

/-- The actual common Laurent embedding, retaining the original completed
base field and the specified source and target normalizations. -/
def regularCompletedEmbedding (w : Place K F)
    (E₀ : (w.restrict B).adicCompletion ≃ₐ[K] LaurentSeries K)
    (E : w.adicCompletion ≃ₐ[K] LaurentSeries K) :
    LaurentSeries K →ₐ[K] LaurentSeries K :=
  E.toAlgHom.comp ((completedBaseAlgHom (B := B) w).comp E₀.symm.toAlgHom)

/-- Coefficient extension of the regular block into the SAME valuation ring
used by the tame boundary points. It is constructed through the local map
of original completion integers. -/
def regularCompletedIntegralCoefficients (w : Place K F)
    (E₀ : (w.restrict B).adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE₀ : ∀ x : (w.restrict B).adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E₀ x) = Valued.v x)
    (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : w.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x) :
    PowerSeries K →ₐ[K] (LaurentSeries.orderPlace (K := K)).toValuationSubring :=
  (w.completionIntegersEquivLaurentOrder E hE).toAlgHom.comp
    ((completedBaseIntegerAlgHom (B := B) w).comp
      ((w.restrict B).powerSeriesEquivCompletionIntegers E₀ hE₀).toAlgHom)

/-- The integral coefficient map has precisely the generic coefficient map
used by the regular reciprocal Laurent deformation. -/
theorem regularCompletedIntegralCoefficients_coe (w : Place K F)
    (E₀ : (w.restrict B).adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE₀ : ∀ x : (w.restrict B).adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E₀ x) = Valued.v x)
    (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : w.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x)
    (f : PowerSeries K) :
    ((w.regularCompletedIntegralCoefficients E₀ hE₀ E hE f :
        (LaurentSeries.orderPlace (K := K)).toValuationSubring) : LaurentSeries K) =
      LaurentSeries.regularBlockCoefficients (w.regularCompletedEmbedding E₀ E) f := rfl

/-- The coefficient extension is local, including for wildly ramified
regular blocks: the finite extension of completed valuation rings supplies
localness, and both normalizations are valuation-ring equivalences. -/
theorem regularCompletedIntegralCoefficients_isLocalHom (w : Place K F)
    (E₀ : (w.restrict B).adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE₀ : ∀ x : (w.restrict B).adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E₀ x) = Valued.v x)
    (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE : ∀ x : w.adicCompletion,
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (E x) = Valued.v x) :
    IsLocalHom (w.regularCompletedIntegralCoefficients E₀ hE₀ E hE).toRingHom := by
  have ha : IsLocalHom (completedBaseIntegerAlgHom (B := B) w).toRingHom :=
    AlgebraicCurve.adicCompletionComapIntegers_isLocalHom B w
  let O₀ := (w.restrict B).powerSeriesEquivCompletionIntegers E₀ hE₀
  let O := w.completionIntegersEquivLaurentOrder E hE
  have hO₀ : IsLocalHom O₀.toRingHom := isLocalHom_toRingHom O₀.toRingEquiv
  have hO : IsLocalHom O.toRingHom := isLocalHom_toRingHom O.toRingEquiv
  change IsLocalHom (O.toRingHom.comp
    ((completedBaseIntegerAlgHom (B := B) w).toRingHom.comp O₀.toRingHom))
  infer_instance

end Base
end AlgebraicCurve.Place
