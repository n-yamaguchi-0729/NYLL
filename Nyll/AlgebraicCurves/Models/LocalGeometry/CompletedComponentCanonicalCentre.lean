/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.Places.ValuationRings.UniqueCentrePlaceProper

/-! # Canonical centres of the completed Cartier components

The centre obtained by extending a completed generic component through the
actual integral Cartier family is the point specified by the curve model's
place equivalence. This connects Henselian block selection to the original
finite set of boundary places, without an additional matching hypothesis.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicCurve.Place

namespace AlgebraicCurve.CurveModel

/-- The native place-model point satisfies both valuation inequalities
which characterize the centre of its place on the proper curve. -/
theorem centre_placeEquiv_symm_ofSmoothProperCurve
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ w : Place K C.functionField,
      let x : closedPoints C := (ofSmoothProperCurve c).placeEquiv.symm w
      ∀ s : C.presheaf.stalk x.1,
        w.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal _ →
            w.adicValuation (algebraMap _ C.functionField s) < 1) := by
  intro algebraKF w x
  let M := ofSmoothProperCurve c
  let θ := algebraMap (C.presheaf.stalk x.1) C.functionField
  have hx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
  have hrange : θ.range = w.toValuationSubring.toSubring := by
    have h := M.range_stalk_eq x
    change θ.range = (M.placeOfPoint x).toValuationSubring.toSubring at h
    exact h.trans (congrArg (fun v : Place K C.functionField =>
      v.toValuationSubring.toSubring) hx)
  have hmem (s : C.presheaf.stalk x.1) : θ s ∈ w.toValuationSubring := by
    change θ s ∈ w.toValuationSubring.toSubring
    rw [← hrange]
    exact ⟨s, rfl⟩
  let ψ : C.presheaf.stalk x.1 →+* w.toValuationSubring :=
    θ.codRestrict w.toValuationSubring hmem
  let e : C.presheaf.stalk x.1 ≃+* w.toValuationSubring :=
    RingEquiv.ofBijective ψ ⟨fun a b h =>
      IsFractionRing.injective _ _ (congrArg Subtype.val h), by
        intro y
        have hy : (y : C.functionField) ∈ θ.range := by
          rw [hrange]
          exact y.property
        obtain ⟨s, hs⟩ := hy
        exact ⟨s, Subtype.ext hs⟩⟩
  intro s
  refine ⟨w.adicValuation_le_one_of_mem (hmem s), ?_⟩
  intro hs
  apply lt_of_le_of_ne (w.adicValuation_le_one_of_mem (hmem s))
  intro hv
  have hu : IsUnit (e s) := (w.adicValuation_coe_eq_one_iff (e s)).mp hv
  have hsunit : IsUnit s := by
    have h := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (e s)) at h
    rw [e.symm_apply_apply] at h
    exact h
  exact (IsLocalRing.mem_maximalIdeal s).mp hs hsunit

/-- Uniqueness of the proper centre identifies the point obtained by the
valuative criterion with the native model's place correspondence. -/
theorem eq_placeEquiv_symm_of_centre
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (w : Place K C.functionField) (z : C),
      (∀ s : C.presheaf.stalk z,
        w.adicValuation (algebraMap _ C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal _ →
            w.adicValuation (algebraMap _ C.functionField s) < 1)) →
      z = ((ofSmoothProperCurve c).placeEquiv.symm w).1 := by
  intro algebraKF w z hz
  obtain ⟨z₀, _, huniq⟩ := existsUnique_centre_place_of_isProper K c w
  exact (huniq z hz).trans
    (huniq _ (centre_placeEquiv_symm_ofSmoothProperCurve c w)).symm

end AlgebraicCurve.CurveModel
