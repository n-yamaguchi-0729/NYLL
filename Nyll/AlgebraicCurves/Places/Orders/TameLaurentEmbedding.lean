/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.TameLaurentNormalization
import Nyll.AlgebraicCurves.Places.Degree.AlgHomLaurentSeriesDegEqOne

/-! # A place embedding with an exact tame parameter

The whole given function, not only its leading coefficient, maps to the
specified power of the Laurent variable, with every place order preserved.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]

/-- At a degree-one place, a function with positive order invertible in the
constant field admits an actual Laurent embedding sending it to the exact
power of the parameter and preserving the order of every function. -/
theorem exists_algHom_laurentSeries_tame_normalized
    (v : Place K F) (hv : v.deg = 1) (s : F) (e : ℕ)
    (he : (e : K) ≠ 0) (hs : v.ord s = (e : ℤ)) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ s = HahnSeries.single (e : ℤ) (1 : K) ∧
      ∀ x : F, (φ x).order = v.ord x := by
  obtain ⟨t, ht⟩ := v.exists_ord_eq_one
  obtain ⟨φ, _hφt, hφ⟩ := v.exists_algHom_laurentSeries_of_deg_eq_one hv t ht
  obtain ⟨E, hEs, hE⟩ := LaurentSeries.exists_tameNormalization
    (φ s) e he ((hφ s).trans hs)
  refine ⟨E.toAlgHom.comp φ, hEs, ?_⟩
  intro x
  exact (hE (φ x)).trans (hφ x)

end AlgebraicCurve.Place
