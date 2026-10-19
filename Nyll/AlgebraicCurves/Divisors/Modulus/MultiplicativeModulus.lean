/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolExistence
import Nyll.AlgebraicCurves.Geometry.WeilReciprocityAlgClosed
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Places.Degree.IsRationalAlgClosed

/-!
# A reduced modulus for a multiplicative rational function

For a nonzero rational function, its actual nonzero residue evaluations define
values in the multiplicative group away from its zeros and poles. The reduced
support of its divisor is a modulus: a congruence-one test function has disjoint
divisor, and the existing proved Weil reciprocity theorem evaluates it to one.
The preceding local-symbol construction therefore supplies the unique symbols.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place.CongruentOne

/-- Every positive local congruence evaluates to one in the residue field and
therefore in the existing residue evaluation. -/
theorem evalAt_eq_one {v : Place K F} {n : ℕ} (hn : n ≠ 0) {f : F}
    (hf : v.CongruentOne n f) : v.evalAt f = 1 := by
  obtain ⟨u, rfl, hu⟩ := hf
  have hres : IsLocalRing.residue v.toValuationSubring (u : v.toValuationSubring) = 1 := by
    have hz := (IsLocalRing.residue_eq_zero_iff
      ((u : v.toValuationSubring) - 1)).mpr (Ideal.pow_le_self hn hu)
    rw [map_sub, map_one] at hz
    exact sub_eq_zero.mp hz
  rw [v.evalAt_of_mem (u : v.toValuationSubring).2]
  change v.residueInv (IsLocalRing.residue v.toValuationSubring
    (u : v.toValuationSubring)) = 1
  rw [hres, ← (algebraMap K v.ResidueField).map_one, v.residueInv_algebraMap]

end Place.CongruentOne

namespace Modulus

variable [IsAlgClosed K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]

/-- The actual multiplicative residue value off the zero and pole divisor.
The harmless extension on its support is the identity of the target group. -/
def multiplicativeValues (f : F) (hf : f ≠ 0) (v : Place K F) : Additive Kˣ :=
  if h : v.ord f = 0 then
    Additive.ofMul (Units.mk0 (v.evalAt f)
      (v.evalAt_ne_zero v.isRational_of_isAlgClosed hf h))
  else 0

variable [HasPrincipalDivisors K F]

/-- The reduced zero and pole divisor is a modulus for a nonzero rational
function valued in the multiplicative group. -/
theorem exists_reduced_multiplicative_modulus (f : F) (hf : f ≠ 0) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = 0 ↔ v.ord f = 0) ∧
      (∀ v : Place K F, D v ≤ 1) ∧ D.HasModulus (multiplicativeValues f hf) := by
  classical
  obtain ⟨E, hE, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  let D : Modulus K F := E.mapRange (fun z : ℤ => if z = 0 then 0 else 1)
    (by exact ite_eq_left rfl)
  have hD (v : Place K F) : D v = if v.ord f = 0 then 0 else 1 := by
    change (if E v = 0 then 0 else 1) = _
    rw [hE v]
  have hDzero (v : Place K F) : D v = 0 ↔ v.ord f = 0 := by
    rw [hD v]
    constructor
    · intro hv
      by_contra hn
      rw [ite_eq_right hn] at hv
      exact Nat.one_ne_zero hv
    · intro hv
      exact ite_eq_left hv
  refine ⟨D, hDzero, ?_, ?_⟩
  · intro v
    rw [hD v]
    split_ifs
    · exact Nat.zero_le 1
    · exact le_rfl
  · intro g hg
    obtain ⟨P, hP, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) (g : F) g.ne_zero
    have hdisj (v : Place K F) : v.ord f = 0 ∨ v.ord (g : F) = 0 := by
      by_cases hv : v.ord f = 0
      · exact Or.inl hv
      · exact Or.inr (hg.ord_eq_zero v (fun hd => hv ((hDzero v).mp hd)))
    have hrec := weilReciprocity_of_isAlgClosed K F f (g : F) E P hf g.ne_zero hE hP
      hdisj (fun v _ => v.isRational_of_isAlgClosed)
      (fun v _ => v.isRational_of_isAlgClosed)
    have hright : Divisor.evalFun (g : F) E = 1 := by
      rw [Divisor.evalFun_def]
      apply Finset.prod_eq_one
      intro v hv
      have hDv : D v ≠ 0 := by
        intro hz
        exact (Finsupp.mem_support_iff.mp hv) ((hE v).trans ((hDzero v).mp hz))
      rw [Place.CongruentOne.evalAt_eq_one hDv (hg.2 v hDv), one_zpow]
    have hprod : Divisor.evalFun f P = 1 := hrec.trans hright
    have hsupp : Function.support
        (fun v : Place K F => v.ord (g : F) • multiplicativeValues f hf v) ⊆
          (P.support : Set (Place K F)) := by
      intro v hv
      apply Finsupp.mem_support_iff.mpr
      intro hp
      apply hv
      change v.ord (g : F) • multiplicativeValues f hf v = 0
      rw [← hP v, hp, zero_zsmul]
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    apply Additive.toMul.injective
    change Additive.toMul (∑ v ∈ P.support,
      v.ord (g : F) • multiplicativeValues f hf v) = (1 : Kˣ)
    rw [toMul_sum]
    apply Units.ext
    rw [Units.coe_prod]
    calc
      (∏ v ∈ P.support,
          ((Additive.toMul (v.ord (g : F) • multiplicativeValues f hf v) : Kˣ) : K)) =
          Divisor.evalFun f P := by
        rw [Divisor.evalFun_def]
        apply Finset.prod_congr rfl
        intro v hv
        have hvord : v.ord f = 0 := (hdisj v).resolve_right
          (fun hz => (Finsupp.mem_support_iff.mp hv) ((hP v).trans hz))
        rw [multiplicativeValues, dite_eq_left hvord, toMul_zsmul,
          toMul_ofMul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hP v]
      _ = 1 := hprod

/-- A multiplicative rational function has actual local symbols with a reduced
modulus; their existence is supplied by the construction, not assumed. -/
theorem exists_reduced_multiplicative_localSymbol (f : F) (hf : f ≠ 0) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = 0 ↔ v.ord f = 0) ∧
      (∀ v : Place K F, D v ≤ 1) ∧
      ∃! σ : Place K F → Additive Fˣ →+ Additive Kˣ,
        D.IsLocalSymbol (multiplicativeValues f hf) σ := by
  obtain ⟨D, hD, hred, hm⟩ := exists_reduced_multiplicative_modulus (K := K) f hf
  exact ⟨D, hD, hred, (hasModulus_iff_existsUnique_localSymbol D _).mp hm⟩

end Modulus

end AlgebraicCurve
