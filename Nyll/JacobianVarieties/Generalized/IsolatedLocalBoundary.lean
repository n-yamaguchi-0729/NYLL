/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusClassAbel

/-!
# Actual isolated representatives of local-unit boundaries

Every nonzero function which is a unit at the selected modulus place has
an actual global representative with the same full local jet and trivial
jets at the other modulus places. Its principal boundary is minus the
corresponding Abel local symbol.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]
  {D : Modulus K F} {a : Place K F → A}

/-- Symbols depend only on the full multiplicative local jet. -/
theorem IsLocalSymbol.eq_of_congruent_div {σ : Place K F → Additive Fˣ →+ A}
    (hσ : D.IsLocalSymbol a σ) (v : Place K F) (g h : Fˣ)
    (hjet : v.CongruentOne (D v) ((g / h : Fˣ) : F)) :
    σ v (Additive.ofMul g) = σ v (Additive.ofMul h) := by
  have he := hσ.1 v (g / h) hjet
  rw [ofMul_div, map_sub, sub_eq_zero] at he
  exact he

variable [HasPrincipalDivisors K F]

/-- Construct a global supported-away unit realizing one prescribed unit
jet, together with its actual boundary evaluation. -/
theorem HasModulus.exists_isolated_unitBoundary (ha : D.HasModulus a)
    (v : Place K F) (hv : D v ≠ 0) (g : Fˣ) (hg : v.ord (g : F) = 0) :
    ∃ f : D.awayUnits,
      v.CongruentOne (D v) ((f.1 / g : Fˣ) : F) ∧
      (∀ w : Place K F, D w ≠ 0 → w ≠ v → w.CongruentOne (D w) (f.1 : F)) ∧
      ha.classEvaluationZero (D.unitBoundary (Additive.ofMul f)) =
        -ha.localSymbol v (Additive.ofMul g) := by
  classical
  obtain ⟨f, hf, hjet, hother⟩ := Place.exists_multiplicative_jet_isolated
    D.support v (g : F) g.ne_zero (fun w => D w)
  have hunit : ∀ w : Place K F, D w ≠ 0 → w.ord f = 0 := by
    intro w hw
    by_cases hwv : w = v
    · subst w
      have he := hjet.ord_eq_zero
      rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero g.ne_zero), v.ord_inv,
        hg, neg_zero, add_zero] at he
      exact he
    · exact (hother w (Finsupp.mem_support_iff.mpr hw) hwv).ord_eq_zero
  let u : D.awayUnits := ⟨Units.mk0 f hf, hunit⟩
  have hlocal : v.CongruentOne (D v) ((u.1 / g : Fˣ) : F) := by
    rw [Units.val_div_eq_div_val]
    exact hjet
  have hisolated : ∀ w : Place K F, D w ≠ 0 → w ≠ v →
      w.CongruentOne (D w) (u.1 : F) :=
    fun w hw hwv => hother w (Finsupp.mem_support_iff.mpr hw) hwv
  refine ⟨u, hlocal, hisolated, ?_⟩
  rw [ha.classEvaluationZero_isolated_unitBoundary u v hv hisolated,
    ha.isLocalSymbol.eq_of_congruent_div v u.1 g hlocal]

/-- In particular the class Abel local symbol is the negative of an actual
kernel boundary with the prescribed isolated full local jet. -/
theorem exists_unitBoundary_eq_neg_classAbel_localSymbol (D : Modulus K F)
    (v₀ : Place K F) (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1)
    (v : Place K F) (hv : D v ≠ 0) (g : Fˣ) (hg : v.ord (g : F) = 0) :
    ∃ f : D.awayUnits,
      v.CongruentOne (D v) ((f.1 / g : Fˣ) : F) ∧
      (∀ w : Place K F, D w ≠ 0 → w ≠ v → w.CongruentOne (D w) (f.1 : F)) ∧
      D.unitBoundary (Additive.ofMul f) =
        -(D.hasModulus_classAbel v₀ h₀ hdeg).localSymbol v (Additive.ofMul g) := by
  obtain ⟨f, hf, hisolated, he⟩ :=
    (D.hasModulus_classAbel v₀ h₀ hdeg).exists_isolated_unitBoundary v hv g hg
  rw [D.classEvaluationZero_classAbel v₀ h₀ hdeg] at he
  exact ⟨f, hf, hisolated, he⟩

end AlgebraicCurve.Modulus
