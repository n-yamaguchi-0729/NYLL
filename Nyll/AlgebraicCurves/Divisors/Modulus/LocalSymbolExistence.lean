/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolUniqueness
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalEvaluation

/-!
# Construction of local symbols from a modulus

At a place of the modulus, choose a rational function matching the prescribed
germ there and congruent to one at the other places of the modulus. Its negative
divisor evaluation off the modulus defines the symbol. The modulus condition
proves independence of the approximation, and therefore additivity. The product
of the finitely many approximants proves reciprocity.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]

namespace Place.CongruentOne

private theorem unit_mul {v : Place K F} {n : ℕ} {g h : Fˣ}
    (hg : v.CongruentOne n (g : F)) (hh : v.CongruentOne n (h : F)) :
    v.CongruentOne n ((g * h : Fˣ) : F) :=
  hg.mul hh

private theorem unit_div {v : Place K F} {n : ℕ} {g h : Fˣ}
    (hg : v.CongruentOne n (g : F)) (hh : v.CongruentOne n (h : F)) :
    v.CongruentOne n ((g / h : Fˣ) : F) := by
  rw [Units.val_div_eq_div_val, div_eq_mul_inv]
  exact hg.mul hh.inv

private theorem unit_prod {v : Place K F} {n : ℕ} {ι : Type*}
    (S : Finset ι) (g : ι → Fˣ) (hg : ∀ i ∈ S, v.CongruentOne n (g i : F)) :
    v.CongruentOne n ((∏ i ∈ S, g i : Fˣ) : F) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Units.val_one] using Place.CongruentOne.one v n
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact unit_mul (hg i (Finset.mem_insert_self i S))
      (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

end Place.CongruentOne

namespace Modulus

/-- Values outside the modulus, extended by zero on its support. -/
def awayValues (D : Modulus K F) (a : Place K F → A) (v : Place K F) : A :=
  if D v = 0 then a v else 0

/-- A concrete approximation of a germ at one place, with full prescribed
congruences at all the other places of the modulus. -/
def IsSymbolApproximation (D : Modulus K F) (v : Place K F) (g h : Fˣ) : Prop :=
  v.CongruentOne (D v) ((h / g : Fˣ) : F) ∧
    ∀ w : Place K F, D w ≠ 0 → w ≠ v → w.CongruentOne (D w) (h : F)

/-- Existence follows from actual multiplicative approximation, also when the
germ has a zero or pole at the distinguished place. -/
theorem exists_symbolApproximation (D : Modulus K F) (v : Place K F) (g : Fˣ) :
    ∃ h : Fˣ, D.IsSymbolApproximation v g h := by
  classical
  obtain ⟨f, hf, hfg, hother⟩ := Place.exists_multiplicative_jet_isolated
    D.support v (g : F) g.ne_zero (fun w => D w)
  refine ⟨Units.mk0 f hf, ?_, fun w hw hwv => ?_⟩
  · simpa only [Units.val_div_eq_div_val, Units.val_mk0] using hfg
  · exact hother w (Finsupp.mem_support_iff.mpr hw) hwv

/-- A selected actual approximating rational function. -/
def symbolApproximation (D : Modulus K F) (v : Place K F) (g : Fˣ) : Fˣ :=
  (D.exists_symbolApproximation v g).choose

theorem symbolApproximation_spec (D : Modulus K F) (v : Place K F) (g : Fˣ) :
    D.IsSymbolApproximation v g (D.symbolApproximation v g) :=
  (D.exists_symbolApproximation v g).choose_spec

namespace IsSymbolApproximation

variable {D : Modulus K F} {v : Place K F} {g h g' h' : Fˣ}

/-- Multiplication of actual approximants matches multiplication of germs. -/
theorem mul (hgh : D.IsSymbolApproximation v g h)
    (hgh' : D.IsSymbolApproximation v g' h') :
    D.IsSymbolApproximation v (g * g') (h * h') := by
  refine ⟨?_, fun w hw hwv => (hgh.2 w hw hwv).unit_mul (hgh'.2 w hw hwv)⟩
  simpa only [div_mul_div_comm] using hgh.1.unit_mul hgh'.1

/-- Two approximants to the same germ have a ratio congruent to one along the
entire modulus. This retains every multiplicity. -/
theorem div (hgh : D.IsSymbolApproximation v g h)
    (hgh' : D.IsSymbolApproximation v g h') :
    D.CongruentOne ((h / h' : Fˣ) : F) := by
  refine ⟨(h / h').ne_zero, fun w hw => ?_⟩
  by_cases hwv : w = v
  · subst w
    simpa only [div_div_div_cancel_right] using hgh.1.unit_div hgh'.1
  · exact (hgh.2 w hw hwv).unit_div (hgh'.2 w hw hwv)

end IsSymbolApproximation

/-- The product of the finitely many supported approximants is congruent to
the original function simultaneously at every place of the full modulus. -/
theorem HasModulus.product_approximation_congruent (D : Modulus K F) (g : Fˣ) :
    D.CongruentOne (((∏ v ∈ D.support, D.symbolApproximation v g) / g : Fˣ) : F) := by
  classical
  refine ⟨Units.ne_zero _, fun w hw => ?_⟩
  have hwmem : w ∈ D.support := Finsupp.mem_support_iff.mpr hw
  rw [← Finset.prod_erase_mul D.support (fun v => D.symbolApproximation v g) hwmem,
    mul_div_assoc]
  apply Place.CongruentOne.unit_mul
  · apply Place.CongruentOne.unit_prod
    intro v hv
    exact (D.symbolApproximation_spec v g).2 w hw (Finset.ne_of_mem_erase hv).symm
  · exact (D.symbolApproximation_spec w g).1

namespace HasModulus

variable {D : Modulus K F} {a : Place K F → A}

/-- Erasing values on the modulus support preserves its principal-divisor
condition, since admissible functions have order zero there. -/
theorem awayValues (ha : D.HasModulus a) : D.HasModulus (D.awayValues a) := by
  intro g hg
  have heq (v : Place K F) : v.ord (g : F) • D.awayValues a v = v.ord (g : F) • a v := by
    by_cases hv : D v = 0
    · rw [Modulus.awayValues, ite_eq_left hv]
    · rw [hg.ord_eq_zero v hv, zero_zsmul, zero_zsmul]
  rw [funext heq]
  exact ha g hg

variable [HasPrincipalDivisors K F]

/-- Modulus-equivalent nonzero functions have the same evaluation off the
modulus, as an equality in the given actual target group. -/
theorem evaluation_eq_of_congruent (ha : D.HasModulus a) {g h : Fˣ}
    (hgh : D.CongruentOne ((g / h : Fˣ) : F)) :
    principalEvaluation (D.awayValues a) (Additive.ofMul g) =
      principalEvaluation (D.awayValues a) (Additive.ofMul h) := by
  have he := ha.awayValues (g / h) hgh
  change principalEvaluation (D.awayValues a) (Additive.ofMul (g / h)) = 0 at he
  rw [ofMul_div, map_sub] at he
  exact sub_eq_zero.mp he

/-- The local-symbol construction is independent of every choice of rational
function realizing the prescribed finite collection of germs. -/
theorem approximation_evaluation_eq (ha : D.HasModulus a) {v : Place K F}
    {g h h' : Fˣ}
    (hgh : D.IsSymbolApproximation v g h) (hgh' : D.IsSymbolApproximation v g h') :
    principalEvaluation (D.awayValues a) (Additive.ofMul h) =
      principalEvaluation (D.awayValues a) (Additive.ofMul h') :=
  ha.evaluation_eq_of_congruent (hgh.div hgh')

end HasModulus

variable [HasPrincipalDivisors K F]

/-- The value of the local symbol constructed from a modulus condition. -/
def localSymbolValue (D : Modulus K F) (a : Place K F → A) (v : Place K F) (g : Fˣ) : A :=
  if D v = 0 then v.ord (g : F) • a v
  else -principalEvaluation (D.awayValues a) (Additive.ofMul (D.symbolApproximation v g))

namespace HasModulus

variable {D : Modulus K F} {a : Place K F → A}

/-- At a supported place, any valid approximant computes the symbol. -/
theorem localSymbolValue_eq (ha : D.HasModulus a) {v : Place K F} (hv : D v ≠ 0)
    {g h : Fˣ} (hgh : D.IsSymbolApproximation v g h) :
    D.localSymbolValue a v g = -principalEvaluation (D.awayValues a) (Additive.ofMul h) := by
  rw [localSymbolValue, ite_eq_right hv]
  exact congrArg Neg.neg
    (ha.approximation_evaluation_eq (D.symbolApproximation_spec v g) hgh)

/-- The symbol vanishes on the full local congruence subgroup. -/
theorem localSymbolValue_congruent (ha : D.HasModulus a) (v : Place K F) (g : Fˣ)
    (hg : v.CongruentOne (D v) (g : F)) : D.localSymbolValue a v g = 0 := by
  by_cases hv : D v = 0
  · rw [localSymbolValue, ite_eq_left hv, hg.ord_eq_zero, zero_zsmul]
  · have happrox : D.IsSymbolApproximation v g 1 := by
      refine ⟨?_, fun w _ _ => Place.CongruentOne.one w (D w)⟩
      simpa only [one_div, Units.val_inv_eq_inv_val] using hg.inv
    rw [ha.localSymbolValue_eq hv happrox]
    change -principalEvaluation (D.awayValues a) 0 = 0
    rw [map_zero, neg_zero]

/-- Multiplicativity of germs gives additivity of the constructed local value. -/
theorem localSymbolValue_mul (ha : D.HasModulus a) (v : Place K F) (g h : Fˣ) :
    D.localSymbolValue a v (g * h) = D.localSymbolValue a v g + D.localSymbolValue a v h := by
  by_cases hv : D v = 0
  · simp only [localSymbolValue, ite_eq_left hv, Units.val_mul,
      v.ord_mul g.ne_zero h.ne_zero, add_zsmul]
  · rw [ha.localSymbolValue_eq hv
      ((D.symbolApproximation_spec v g).mul (D.symbolApproximation_spec v h)),
      ofMul_mul, map_add, neg_add]
    rw [localSymbolValue, ite_eq_right hv, localSymbolValue, ite_eq_right hv]

/-- The sum of the symbols on the support is the negative of principal
valuation outside it. This is the finite calculation underlying reciprocity. -/
theorem sum_supported_localSymbolValue (ha : D.HasModulus a) (g : Fˣ) :
    ∑ v ∈ D.support, D.localSymbolValue a v g =
      -principalEvaluation (D.awayValues a) (Additive.ofMul g) := by
  classical
  have he := ha.evaluation_eq_of_congruent (product_approximation_congruent D g)
  rw [ofMul_prod, map_sum] at he
  calc
    ∑ v ∈ D.support, D.localSymbolValue a v g =
        ∑ v ∈ D.support,
          -principalEvaluation (D.awayValues a) (Additive.ofMul (D.symbolApproximation v g)) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [localSymbolValue, ite_eq_right (Finsupp.mem_support_iff.mp hv)]
    _ = -(∑ v ∈ D.support,
        principalEvaluation (D.awayValues a) (Additive.ofMul (D.symbolApproximation v g))) :=
      Finset.sum_neg_distrib (fun v =>
        principalEvaluation (D.awayValues a) (Additive.ofMul (D.symbolApproximation v g)))
    _ = -principalEvaluation (D.awayValues a) (Additive.ofMul g) := congrArg Neg.neg he

/-- The constructed symbols satisfy the actual finite-support reciprocity law. -/
theorem localSymbolValue_reciprocity (ha : D.HasModulus a) (g : Fˣ) :
    ∑ᶠ v : Place K F, D.localSymbolValue a v g = 0 := by
  classical
  let b : Place K F → A := fun v => if D v = 0 then 0 else D.localSymbolValue a v g
  have hb : Function.support b ⊆ (D.support : Set (Place K F)) := by
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro hDv
    apply hv
    exact ite_eq_left hDv
  have hbfin : Function.HasFiniteSupport b := D.support.finite_toSet.subset hb
  have heq (v : Place K F) :
      D.localSymbolValue a v g = b v + v.ord (g : F) • D.awayValues a v := by
    by_cases hv : D v = 0
    · simp only [localSymbolValue, Modulus.awayValues, b, ite_eq_left hv, zero_add]
    · simp only [Modulus.awayValues, b, ite_eq_right hv, zsmul_zero, add_zero]
  rw [funext heq, finsum_add_distrib hbfin (principalEvaluation_finiteSupport _ g),
    finsum_eq_sum_of_support_subset b hb]
  have hsum : ∑ v ∈ D.support, b v = ∑ v ∈ D.support, D.localSymbolValue a v g := by
    apply Finset.sum_congr rfl
    intro v hv
    exact ite_eq_right (Finsupp.mem_support_iff.mp hv)
  rw [hsum, ha.sum_supported_localSymbolValue]
  exact neg_add_cancel (principalEvaluation (D.awayValues a) (Additive.ofMul g))

/-- The actual local homomorphisms constructed from the global modulus condition. -/
def localSymbol (ha : D.HasModulus a) (v : Place K F) : Additive Fˣ →+ A where
  toFun g := D.localSymbolValue a v (Additive.toMul g)
  map_zero' := ha.localSymbolValue_congruent v 1 (Place.CongruentOne.one v (D v))
  map_add' g h := ha.localSymbolValue_mul v (Additive.toMul g) (Additive.toMul h)

/-- All four local-symbol axioms are proved for the constructed homomorphisms. -/
theorem isLocalSymbol (ha : D.HasModulus a) : D.IsLocalSymbol a ha.localSymbol := by
  refine ⟨?_, ?_, ?_⟩
  · intro v g hg
    exact ha.localSymbolValue_congruent v g hg
  · intro v hv g
    exact ite_eq_left hv
  · intro g
    exact ha.localSymbolValue_reciprocity g

end HasModulus

/-- The global modulus condition is equivalent to existence of a unique family
of local symbols; existence and uniqueness both use the actual place theory. -/
theorem hasModulus_iff_existsUnique_localSymbol (D : Modulus K F) (a : Place K F → A) :
    D.HasModulus a ↔ ∃! σ : Place K F → Additive Fˣ →+ A, D.IsLocalSymbol a σ := by
  constructor
  · intro ha
    exact ⟨ha.localSymbol, ha.isLocalSymbol, fun σ hσ => hσ.unique ha.isLocalSymbol⟩
  · rintro ⟨σ, hσ, _⟩
    exact hσ.hasModulus

end Modulus

end AlgebraicCurve
