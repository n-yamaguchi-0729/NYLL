/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.TameRationalCompletedTensorSplitting
import Nyll.AlgebraicCurves.Places.Degree.TameBoundaryCommonBase

/-! # All boundary embeddings over one actual completed base

The normalized reference component fixes the scalar algebra on the common
Laurent coefficient field. Every other actual tame completed factor is
split by its constructed embeddings. Equality on the whole completed base
then rebundles those same ring maps under the reference scalar algebra.
No comparison of base embeddings, splitting, or valuation estimate is
assumed: exact common contact and the original native field maps supply them.
-/

noncomputable section

open scoped AlgebraicCurve.Place
open scoped AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

namespace AlgebraicCurve.Place

variable {K B F : Type*} [Field K] [Field B] [Field F]
  [Algebra K B] [Algebra K F] [Algebra B F] [IsScalarTower K B F]
  [FiniteDimensional B F] [Algebra.IsSeparable B F]
  [HasPrincipalDivisors K B] [HasPrincipalDivisors K F]

/-- The original completed-base map followed by a specified actual
normalization, retaining its native ground-field structure. -/
def boundaryCompletedBaseMap (v : Place K B) (w₀ : v.fiber F)
    (E₀ : w₀.val.adicCompletion ≃ₐ[K] LaurentSeries K) :
    v.adicCompletion →ₐ[K] LaurentSeries K where
  toRingHom := E₀.toRingHom.comp (algebraMap v.adicCompletion w₀.val.adicCompletion)
  commutes' a := by
    change E₀ (algebraMap v.adicCompletion w₀.val.adicCompletion
      (algebraMap K v.adicCompletion a)) = algebraMap K (LaurentSeries K) a
    rw [IsScalarTower.algebraMap_apply K B v.adicCompletion,
      ← IsScalarTower.algebraMap_apply B v.adicCompletion w₀.val.adicCompletion,
      IsScalarTower.algebraMap_apply B F w₀.val.adicCompletion,
      ← IsScalarTower.algebraMap_apply K B F,
      ← IsScalarTower.algebraMap_apply K F w₀.val.adicCompletion]
    exact E₀.commutes a

private theorem exists_tame_completed_ring_embeddings [IsAlgClosed K]
    (w : Place K F) (hw : w.deg = 1) (p : RatFunc K ≃ₐ[K] B)
    (hs : (w.restrict B).ord (p RatFunc.X) = 1)
    (he : (w.ramificationIndex B : K) ≠ 0) :
    ∃ E : w.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F w.adicCompletion (algebraMap B F (p RatFunc.X))) =
        HahnSeries.single (w.ramificationIndex B : ℤ) (1 : K) ∧
      Continuous E ∧
      ∃ ρ : Fin (w.ramificationIndex B) → w.adicCompletion →+* LaurentSeries K,
        Function.Injective ρ ∧
        (∀ a z, ρ a (algebraMap (w.restrict B).adicCompletion w.adicCompletion z) =
          E (algebraMap (w.restrict B).adicCompletion w.adicCompletion z)) ∧
        ∀ a f, (ρ a (algebraMap F w.adicCompletion f)).order = w.ord f := by
  obtain ⟨E, hEs, hEc, hlocal⟩ :=
    w.exists_tame_rational_completed_tensor_splitting hw p hs he
  let algL : Algebra (w.restrict B).adicCompletion (LaurentSeries K) :=
    (E.toRingHom.comp
      (algebraMap (w.restrict B).adicCompletion w.adicCompletion)).toAlgebra
  let modL : Module (w.restrict B).adicCompletion (LaurentSeries K) := algL.toModule
  obtain ⟨ρ, hρ, horder, _split, _hformula⟩ := hlocal
  refine ⟨E, hEs, hEc, fun a => (ρ a).toRingHom, ?_, ?_, horder⟩
  · intro a b hab
    apply hρ
    apply AlgHom.ext
    intro f
    exact RingHom.congr_fun hab f
  · intro a z
    exact (ρ a).commutes z

omit [FiniteDimensional B F] [HasPrincipalDivisors K B] in
private theorem fiber_embedding_base_eq
    (v : Place K B) (w : v.fiber F)
    (ρ : w.val.adicCompletion →+* LaurentSeries K)
    (E : w.val.adicCompletion ≃ₐ[K] LaurentSeries K)
    (h : ∀ z, ρ (algebraMap (w.val.restrict B).adicCompletion w.val.adicCompletion z) =
      E (algebraMap (w.val.restrict B).adicCompletion w.val.adicCompletion z)) :
    ∀ z, ρ (algebraMap v.adicCompletion w.val.adicCompletion z) =
      E (algebraMap v.adicCompletion w.val.adicCompletion z) := by
  rcases w with ⟨w, hw⟩
  have hv : w.restrict B = v := Place.mem_fiber.mp hw
  subst v
  exact h

private theorem fiber_finrank_of_deg_one
    (v : Place K B) (w : v.fiber F) (hw : w.val.deg = 1) :
    Module.finrank v.adicCompletion w.val.adicCompletion = w.val.ramificationIndex B := by
  rcases w with ⟨w, hfiber⟩
  have hv : w.restrict B = v := Place.mem_fiber.mp hfiber
  subst v
  have hinertia : w.inertiaDeg B = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := B)
    rw [hw] at h
    exact Nat.eq_one_of_mul_eq_one_left h
  have h := w.finrank_adicCompletion_restrict (K := B)
  rw [hinertia, Nat.cast_one, mul_one] at h
  exact_mod_cast h

/-- All selected boundary factors have complete labelled embeddings into
one Laurent field with one scalar algebra. Their native completed degrees,
original-field orders, and exact normalized contact are retained. The
selected family may repeat labels; no distinctness between different
completed factors is needed. -/
theorem exists_common_boundary_completed_embeddings [IsAlgClosed K]
    (v : Place K B) (p : RatFunc K ≃ₐ[K] B)
    (hs : v.ord (p RatFunc.X) = 1)
    (g : Fˣ) (hparameter : algebraMap B F (p RatFunc.X) = (g : F) - 1)
    (e : ℕ) (he : (e : K) ≠ 0)
    (w₀ : v.fiber F) (E₀ : w₀.val.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hE₀c : Continuous E₀)
    (hE₀s : E₀ (algebraMap F w₀.val.adicCompletion
      (algebraMap B F (p RatFunc.X))) = HahnSeries.single (e : ℤ) (1 : K))
    {I : Type*} (w : I → v.fiber F)
    (hw : ∀ i, (w i).val.deg = 1)
    (hcontact : ∀ i, (w i).val.ord ((g : F) - 1) = (e : ℤ)) :
    let β := boundaryCompletedBaseMap v w₀ E₀
    let _ : Algebra v.adicCompletion (LaurentSeries K) := β.toRingHom.toAlgebra
    IsScalarTower K v.adicCompletion (LaurentSeries K) ∧
      (∀ i, IsScalarTower K v.adicCompletion (w i).val.adicCompletion) ∧
      (∀ i, Algebra.IsSeparable v.adicCompletion (w i).val.adicCompletion) ∧
      ∃ ι : ∀ i, Fin e → (w i).val.adicCompletion →ₐ[v.adicCompletion] LaurentSeries K,
        (∀ i, Function.Injective (ι i)) ∧
        (∀ i, Module.finrank v.adicCompletion (w i).val.adicCompletion = e) ∧
        (∀ i a f, (ι i a (algebraMap F (w i).val.adicCompletion f)).order = (w i).val.ord f) ∧
        ∀ i a, ι i a (algebraMap F (w i).val.adicCompletion ((g : F) - 1)) =
          HahnSeries.single (e : ℤ) (1 : K) := by
  classical
  intro β algL
  have htower : IsScalarTower K v.adicCompletion (LaurentSeries K) := by
    constructor
    intro a b f
    rw [Algebra.smul_def a b,
      Algebra.smul_def (algebraMap K v.adicCompletion a * b) f,
      Algebra.smul_def b f]
    change β (algebraMap K v.adicCompletion a * b) * f = a • (β b * f)
    rw [map_mul, β.commutes, mul_assoc]
    change HahnSeries.ofPowerSeries ℤ K (PowerSeries.C a) * (β b * f) = _
    rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
      HahnSeries.single_zero_mul_eq_smul]
  have hsourceTower (i : I) : IsScalarTower K v.adicCompletion (w i).val.adicCompletion := by
    refine IsScalarTower.of_algebraMap_eq
      (R := K) (S := v.adicCompletion) (A := (w i).val.adicCompletion) fun a => ?_
    rw [IsScalarTower.algebraMap_apply K F (w i).val.adicCompletion,
      IsScalarTower.algebraMap_apply K B F,
      IsScalarTower.algebraMap_apply K B v.adicCompletion,
      ← IsScalarTower.algebraMap_apply B v.adicCompletion (w i).val.adicCompletion,
      IsScalarTower.algebraMap_apply B F (w i).val.adicCompletion]
  refine ⟨htower, hsourceTower, fun i => Place.isSeparable_fiberCompletion v (w i), ?_⟩
  have hex (i : I) :
      ∃ ι : Fin e → (w i).val.adicCompletion →ₐ[v.adicCompletion] LaurentSeries K,
        Function.Injective ι ∧
        Module.finrank v.adicCompletion (w i).val.adicCompletion = e ∧
        (∀ a f, (ι a (algebraMap F (w i).val.adicCompletion f)).order = (w i).val.ord f) ∧
        ∀ a, ι a (algebraMap F (w i).val.adicCompletion ((g : F) - 1)) =
          HahnSeries.single (e : ℤ) (1 : K) := by
    have hv : (w i).val.restrict B = v := Place.mem_fiber.mp (w i).property
    have hram : (w i).val.ramificationIndex B = e := by
      have ho := (w i).val.ord_restrict (F := B) (p RatFunc.X)
      rw [hparameter, hcontact i, hv, hs, mul_one] at ho
      exact_mod_cast ho.symm
    have hsi : ((w i).val.restrict B).ord (p RatFunc.X) = 1 := by
      rw [hv]
      exact hs
    have hei : ((w i).val.ramificationIndex B : K) ≠ 0 := by
      rw [hram]
      exact he
    have hraw := exists_tame_completed_ring_embeddings (w i).val (hw i) p hsi hei
    rw [hram] at hraw
    obtain ⟨E, hEs, hEc, ρ, hρ, hnativeBase, horder⟩ := hraw
    have hcommon := normalized_boundary_completed_base_eq v (w i) w₀ E E₀
      hEc hE₀c p e hEs hE₀s
    have hbase (a : Fin e) := fiber_embedding_base_eq v (w i) (ρ a) E (hnativeBase a)
    let ι (a : Fin e) : (w i).val.adicCompletion →ₐ[v.adicCompletion] LaurentSeries K :=
      { toRingHom := ρ a
        commutes' z := (hbase a z).trans (RingHom.congr_fun hcommon z) }
    have hι : Function.Injective ι := by
      intro a b hab
      apply hρ
      exact congrArg AlgHom.toRingHom hab
    have hdegree : Module.finrank v.adicCompletion (w i).val.adicCompletion = e :=
      (fiber_finrank_of_deg_one v (w i) (hw i)).trans hram
    refine ⟨ι, hι, hdegree, horder, ?_⟩
    intro a
    rw [← hparameter, ← IsScalarTower.algebraMap_apply B F (w i).val.adicCompletion,
      IsScalarTower.algebraMap_apply B v.adicCompletion (w i).val.adicCompletion,
      (ι a).commutes]
    change E₀ (algebraMap v.adicCompletion w₀.val.adicCompletion
      (algebraMap B v.adicCompletion (p RatFunc.X))) = _
    rw [← IsScalarTower.algebraMap_apply B v.adicCompletion w₀.val.adicCompletion,
      IsScalarTower.algebraMap_apply B F w₀.val.adicCompletion]
    exact hE₀s
  choose ι hι hdegree horder hnormal using hex
  exact ⟨ι, hι, hdegree, horder, hnormal⟩

end AlgebraicCurve.Place
