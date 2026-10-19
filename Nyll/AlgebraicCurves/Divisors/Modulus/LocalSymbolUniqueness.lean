/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusMultiplicativeJets
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Uniqueness of local symbols from multiplicative approximation

The four defining local-symbol conditions are additivity in the rational
function, vanishing on local modulus congruences, evaluation by order away from
the modulus, and reciprocity. Additivity is expressed by an actual additive
homomorphism from the additive form of the nonzero rational functions.

Weak approximation isolates one place, and reciprocity then determines its
symbol uniquely. The finite support used in the reciprocity argument follows
from the existing principal-divisor theorem. This file does not assert that
local symbols exist for arbitrary algebraic-group-valued maps.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]

/-- The abstract modulus condition: evaluation on a principal divisor of a
function congruent to one along the whole modulus vanishes. Values on the
modulus support do not contribute because the corresponding orders are zero. -/
def HasModulus (D : Modulus K F) (a : Place K F → A) : Prop :=
  ∀ g : Fˣ, D.CongruentOne (g : F) → ∑ᶠ v : Place K F, v.ord (g : F) • a v = 0

/-- The modulus condition depends only on values away from its support. -/
theorem HasModulus.congr {D : Modulus K F} {a b : Place K F → A}
    (ha : D.HasModulus a) (hab : ∀ v, D v = 0 → a v = b v) :
    D.HasModulus b := by
  intro g hg
  have heq : (fun v : Place K F => v.ord (g : F) • b v) =
      fun v => v.ord (g : F) • a v := by
    funext v
    by_cases hv : D v = 0
    · rw [hab v hv]
    · rw [hg.ord_eq_zero v hv, zero_zsmul, zero_zsmul]
  rw [heq]
  exact ha g hg

/-- The local-symbol axioms at the fixed full modulus. Additivity in the
function is part of the homomorphism type; the remaining conditions are local
vanishing, the order formula off the support, and reciprocity. -/
def IsLocalSymbol (D : Modulus K F) (a : Place K F → A)
    (σ : Place K F → Additive Fˣ →+ A) : Prop :=
  (∀ (v : Place K F) (g : Fˣ), v.CongruentOne (D v) (g : F) →
    σ v (Additive.ofMul g) = 0) ∧
  (∀ (v : Place K F), D v = 0 → ∀ g : Fˣ,
    σ v (Additive.ofMul g) = v.ord (g : F) • a v) ∧
  (∀ g : Fˣ, ∑ᶠ v : Place K F, σ v (Additive.ofMul g) = 0)

namespace IsLocalSymbol

variable {D : Modulus K F} {a : Place K F → A}
  {σ τ : Place K F → Additive Fˣ →+ A}

/-- The local-symbol axioms force finite support on every rational function. -/
theorem finiteSupport [HasPrincipalDivisors K F] (hσ : D.IsLocalSymbol a σ) (g : Fˣ) :
    Function.HasFiniteSupport (fun v => σ v (Additive.ofMul g)) := by
  classical
  obtain ⟨E, hE, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) (g : F) g.ne_zero
  refine (D.support.finite_toSet.union E.support.finite_toSet).subset ?_
  intro v hv
  change σ v (Additive.ofMul g) ≠ 0 at hv
  by_cases hDv : D v = 0
  · right
    apply Finsupp.mem_support_iff.mpr
    intro hEv
    apply hv
    rw [hσ.2.1 v hDv g, ← hE v, hEv, zero_zsmul]
  · exact Or.inl (Finsupp.mem_support_iff.mpr hDv)

/-- A local symbol satisfies the global principal-divisor modulus condition. -/
theorem hasModulus (hσ : D.IsLocalSymbol a σ) : D.HasModulus a := by
  intro g hg
  have heq (v : Place K F) : σ v (Additive.ofMul g) = v.ord (g : F) • a v := by
    by_cases hv : D v = 0
    · exact hσ.2.1 v hv g
    · rw [hσ.1 v g (hg.2 v hv), hg.ord_eq_zero v hv, zero_zsmul]
  rw [← funext heq]
  exact hσ.2.2 g

/-- Approximation and reciprocity determine each local symbol uniquely, even
on functions with a zero or a pole at the place under consideration. -/
theorem unique [HasPrincipalDivisors K F]
    (hσ : D.IsLocalSymbol a σ) (hτ : D.IsLocalSymbol a τ) : σ = τ := by
  classical
  funext v
  apply AddMonoidHom.ext
  intro x
  let g : Fˣ := Additive.toMul x
  obtain ⟨f, hf, hfg, hfother⟩ := Place.exists_multiplicative_jet_isolated
    D.support v (g : F) g.ne_zero (fun w => D w)
  let u : Fˣ := Units.mk0 f hf
  have hquot : v.CongruentOne (D v) ((u / g : Fˣ) : F) := by
    simpa only [u, Units.val_div_eq_div_val, Units.val_mk0] using hfg
  have hσeq : σ v (Additive.ofMul u) = σ v (Additive.ofMul g) := by
    have hz := hσ.1 v (u / g) hquot
    change σ v (Additive.ofMul u - Additive.ofMul g) = 0 at hz
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hτeq : τ v (Additive.ofMul u) = τ v (Additive.ofMul g) := by
    have hz := hτ.1 v (u / g) hquot
    change τ v (Additive.ofMul u - Additive.ofMul g) = 0 at hz
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hvanish (w : Place K F) (hwv : w ≠ v) :
      σ w (Additive.ofMul u) - τ w (Additive.ofMul u) = 0 := by
    by_cases hwD : D w = 0
    · rw [hσ.2.1 w hwD u, hτ.2.1 w hwD u, sub_self]
    · have hwu : w.CongruentOne (D w) (u : F) :=
        hfother w (Finsupp.mem_support_iff.mpr hwD) hwv
      rw [hσ.1 w u hwu, hτ.1 w u hwu, sub_self]
  have hsum : ∑ᶠ w : Place K F,
      (σ w (Additive.ofMul u) - τ w (Additive.ofMul u)) = 0 := by
    rw [finsum_sub_distrib (hσ.finiteSupport u) (hτ.finiteSupport u),
      hσ.2.2 u, hτ.2.2 u, sub_self]
  have heq : σ v (Additive.ofMul u) = τ v (Additive.ofMul u) :=
    sub_eq_zero.mp ((finsum_eq_single
      (fun w => σ w (Additive.ofMul u) - τ w (Additive.ofMul u)) v hvanish).symm.trans hsum)
  exact hσeq.symm.trans (heq.trans hτeq)

end IsLocalSymbol

end AlgebraicCurve.Modulus
