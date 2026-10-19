/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Orders.PrescribedOrders
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolUniqueness
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalEvaluation

/-!
# Factorization into functions with prescribed exact contact orders

Place approximation supplies one fixed factor. Every function congruent to
one to strictly greater orders is its product with a second factor having the
same exact contact orders. The statement includes the identity function and
does not interpret `ord 0` as infinity.

Consequently a principal-divisor modulus condition can be checked only on
functions with these exact orders. Choosing the positive orders prime to the
characteristic gives the tame test functions over a perfect ground field;
neither a characteristic hypothesis nor separability is needed for the
factorization itself.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- Dividing a higher-order congruence by a function of exact positive contact
order retains that exact contact order. Valuation comparison also covers `f = 1`. -/
theorem ord_div_sub_one_of_congruentOne (v : Place K F) {n : ℕ}
    (hn : 0 < n) (f g : Fˣ)
    (hf : v.CongruentOne (n + 1) (f : F))
    (hg : v.ord ((g : F) - 1) = (n : ℤ)) :
    v.ord (((f / g : Fˣ) : F) - 1) = (n : ℤ) := by
  have hg0 : (g : F) - 1 ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hg
    omega
  have hgval : v.adicValuation ((g : F) - 1) = WithZero.exp (-(n : ℤ)) := by
    rw [v.adicValuation_eq_exp_neg_ord hg0, hg]
  have hflt : v.adicValuation ((f : F) - 1) < v.adicValuation ((g : F) - 1) := by
    apply ((v.congruentOne_iff_adicValuation_sub_one_le
      (Nat.succ_ne_zero n) (f : F)).mp hf).trans_lt
    rw [hgval, WithZero.exp_lt_exp]
    omega
  have hnum : v.adicValuation ((f : F) - (g : F)) =
      v.adicValuation ((g : F) - 1) := by
    have heq : (f : F) - (g : F) = ((f : F) - 1) - ((g : F) - 1) := by ring
    rw [heq]
    exact v.adicValuation.map_sub_eq_of_lt_right hflt
  have hglt : v.adicValuation ((g : F) - 1) < 1 := by
    rw [hgval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hgone : v.adicValuation (g : F) = 1 := by
    calc
      v.adicValuation (g : F) = v.adicValuation (1 + ((g : F) - 1)) :=
        congrArg v.adicValuation (by ring)
      _ = 1 := v.adicValuation.map_one_add_of_lt hglt
  have hquot : ((f / g : Fˣ) : F) - 1 =
      ((f : F) - (g : F)) * (g : F)⁻¹ := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, sub_mul,
      mul_inv_cancel₀ g.ne_zero]
  calc
    v.ord (((f / g : Fˣ) : F) - 1) = v.ord ((g : F) - 1) := by
      unfold Place.ord
      rw [hquot, map_mul, map_inv₀, hnum, hgone, inv_one, mul_one]
    _ = (n : ℤ) := hg

/-- One fixed factor of prescribed positive contact orders factors every
strictly higher-order congruence into two functions with those exact orders. -/
theorem exists_fixed_factorization_exact_orders (S : Finset (Place K F))
    (n : Place K F → ℕ) (hn : ∀ v ∈ S, 0 < n v) :
    ∃ g : Fˣ, (∀ v ∈ S, v.ord ((g : F) - 1) = (n v : ℤ)) ∧
      ∀ f : Fˣ, (∀ v ∈ S, v.CongruentOne (n v + 1) (f : F)) →
        ∃ h : Fˣ, f = g * h ∧ ∀ v ∈ S, v.ord ((h : F) - 1) = (n v : ℤ) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨1, (fun v hv => (Finset.notMem_empty v hv).elim), ?_⟩
    intro f _
    exact ⟨f, (one_mul f).symm, fun v hv => (Finset.notMem_empty v hv).elim⟩
  obtain ⟨x, hx0, hx⟩ := exists_forall_ord_eq S (fun v => (n v : ℤ))
  have hg0 : 1 + x ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    have hxlt : v.adicValuation x < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hx0, hx v hv,
        ← WithZero.exp_zero, WithZero.exp_lt_exp]
      have hnv := hn v hv
      omega
    have hval := v.adicValuation.map_one_add_of_lt hxlt
    intro hzero
    rw [hzero, map_zero] at hval
    exact zero_ne_one hval
  let g : Fˣ := Units.mk0 (1 + x) hg0
  have hg (v : Place K F) (hv : v ∈ S) : v.ord ((g : F) - 1) = (n v : ℤ) := by
    change v.ord ((1 + x) - 1) = (n v : ℤ)
    rw [show (1 + x) - 1 = x by ring]
    exact hx v hv
  refine ⟨g, hg, ?_⟩
  intro f hf
  refine ⟨f / g, ?_, fun v hv =>
    v.ord_div_sub_one_of_congruentOne (hn v hv) f g (hf v hv) (hg v hv)⟩
  rw [div_eq_mul_inv, ← mul_assoc, mul_comm g f, mul_assoc, mul_inv_cancel, mul_one]

end Place

namespace Modulus

variable {A : Type*} [AddCommGroup A] [HasPrincipalDivisors K F]

/-- Actual principal-divisor evaluation need only vanish on functions with
fixed exact positive contact orders strictly smaller than the modulus. -/
theorem hasModulus_of_exact_contact_orders (D : Modulus K F)
    (a : Place K F → A) (n : Place K F → ℕ)
    (hn : ∀ v ∈ D.support, 0 < n v)
    (hnD : ∀ v ∈ D.support, n v < D v)
    (hvanish : ∀ g : Fˣ,
      (∀ v ∈ D.support, v.ord ((g : F) - 1) = (n v : ℤ)) →
      principalEvaluation a (Additive.ofMul g) = 0) :
    D.HasModulus a := by
  classical
  obtain ⟨g, hg, hfactor⟩ := Place.exists_fixed_factorization_exact_orders D.support n hn
  intro f hf
  obtain ⟨h, hfh, hh⟩ := hfactor f (fun v hv =>
    (hf.2 v (Finsupp.mem_support_iff.mp hv)).mono (hnD v hv))
  change principalEvaluation a (Additive.ofMul f) = 0
  rw [hfh]
  change principalEvaluation a (Additive.ofMul g + Additive.ofMul h) = 0
  rw [map_add, hvanish g hg, hvanish h hh, add_zero]

end Modulus

end AlgebraicCurve
