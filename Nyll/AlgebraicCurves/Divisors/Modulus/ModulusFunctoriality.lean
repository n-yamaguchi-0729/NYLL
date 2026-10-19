/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolConductor
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Moduli under homomorphisms and finite products

The proofs commute homomorphisms with the genuinely finite support of each
principal-divisor sum. In particular a finite family of rational maps with
proved moduli has a common modulus for its product map.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F A B : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup A] [AddCommGroup B] [HasPrincipalDivisors K F]
  {D : Modulus K F} {a : Place K F → A}

/-- A group homomorphism preserves a full modulus. -/
theorem HasModulus.map (ha : D.HasModulus a) (h : A →+ B) :
    D.HasModulus (fun v => h (a v)) := by
  intro g hg
  have he := h.map_finsum (principalEvaluation_finiteSupport a g)
  rw [ha g hg, map_zero] at he
  simpa only [map_zsmul] using he.symm

/-- An injective homomorphism detects the full modulus property. -/
theorem hasModulus_map_iff (h : A →+ B) (hinj : Function.Injective h) :
    D.HasModulus (fun v => h (a v)) ↔ D.HasModulus a := by
  refine ⟨?_, fun ha => ha.map h⟩
  intro ha g hg
  apply hinj
  rw [map_zero, h.map_finsum (principalEvaluation_finiteSupport a g)]
  simpa only [map_zsmul] using ha g hg

/-- Local symbols commute with every homomorphism of commutative groups. -/
theorem IsLocalSymbol.map {σ : Place K F → Additive Fˣ →+ A}
    (hσ : D.IsLocalSymbol a σ) (h : A →+ B) :
    D.IsLocalSymbol (fun v => h (a v)) (fun v => h.comp (σ v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v g hg
    change h (σ v (Additive.ofMul g)) = 0
    rw [hσ.1 v g hg, map_zero]
  · intro v hv g
    change h (σ v (Additive.ofMul g)) = _
    rw [hσ.2.1 v hv g, map_zsmul]
  · intro g
    have he := h.map_finsum (hσ.finiteSupport g)
    rw [hσ.2.2 g, map_zero] at he
    exact he.symm

/-- The constructed local symbols are functorial under group homomorphisms. -/
theorem HasModulus.localSymbol_map (ha : D.HasModulus a) (h : A →+ B) :
    (ha.map h).localSymbol = fun v => h.comp (ha.localSymbol v) :=
  (ha.map h).isLocalSymbol.unique (ha.isLocalSymbol.map h)

omit [HasPrincipalDivisors K F] in
/-- Over an algebraically closed constant field, every constant group value
has every modulus: its principal evaluation is the degree of the divisor. -/
theorem hasModulus_const [IsAlgClosed K] [IsCurveOver K F] (D : Modulus K F) (b : A) :
    D.HasModulus (fun _ => b) := by
  classical
  intro g _
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (g : F) g.ne_zero
  have hsupport : Function.support (fun v : Place K F => v.ord (g : F) • b) ⊆
      (E.support : Set (Place K F)) := by
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro hzero
    apply hv
    change v.ord (g : F) • b = 0
    rw [← hE v, hzero, zero_zsmul]
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  have hsum : (∑ v ∈ E.support, E v) = 0 := by
    rw [Divisor.degree_eq_sum_support] at hdeg
    simpa only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] using hdeg
  calc
    _ = ∑ v ∈ E.support, E v • b := Finset.sum_congr rfl (fun v _ => by rw [hE v])
    _ = (∑ v ∈ E.support, E v) • b :=
      (Finset.sum_smul (s := E.support) (f := fun v => E v) (x := b)).symm
    _ = 0 := by rw [hsum, zero_zsmul]

omit [HasPrincipalDivisors K F] in
/-- Translation by a fixed value preserves the full principal-divisor modulus. -/
theorem HasModulus.sub_const [IsAlgClosed K] [IsCurveOver K F]
    (ha : D.HasModulus a) (b : A) : D.HasModulus (fun v => a v - b) := by
  intro g hg
  have heq : (fun v : Place K F => v.ord (g : F) • (a v - b)) =
      fun v => v.ord (g : F) • a v - v.ord (g : F) • b :=
    funext (fun v => smul_sub (v.ord (g : F)) (a v) b)
  rw [heq, finsum_sub_distrib (principalEvaluation_finiteSupport a g)
    (principalEvaluation_finiteSupport (fun _ => b) g),
    ha g hg, hasModulus_const D b g hg, sub_zero]

omit [HasPrincipalDivisors K F] in
/-- The full modulus is unchanged by translation of the target values. -/
theorem hasModulus_sub_const_iff [IsAlgClosed K] [IsCurveOver K F] (b : A) :
    D.HasModulus (fun v => a v - b) ↔ D.HasModulus a := by
  refine ⟨fun h => ?_, fun h => h.sub_const b⟩
  have h := h.sub_const (-b)
  simpa only [sub_neg_eq_add, sub_add_cancel] using h

section Products

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
  {a : Place K F → ∀ i, A i}

/-- A product map has a fixed modulus exactly when all coordinates have it.
The index type need not be finite for this assertion about a fixed modulus. -/
theorem hasModulus_pi_iff :
    D.HasModulus a ↔ ∀ i, D.HasModulus (fun v => a v i) := by
  refine ⟨fun ha i => ha.map (Pi.evalAddMonoidHom A i), ?_⟩
  intro ha g hg
  funext i
  have he := (Pi.evalAddMonoidHom A i).map_finsum
    (principalEvaluation_finiteSupport a g)
  change (∑ᶠ v : Place K F, v.ord (g : F) • a v) i =
    ∑ᶠ v : Place K F, v.ord (g : F) • a v i at he
  exact he.trans (ha i g hg)

/-- A finite family of maps with actual moduli has an actual common modulus. -/
theorem exists_modulus_pi [Finite ι]
    (ha : ∀ i, ∃ D : Modulus K F, D.HasModulus (fun v => a v i)) :
    ∃ D : Modulus K F, D.HasModulus a := by
  classical
  let := Fintype.ofFinite ι
  choose d hd using ha
  refine ⟨Finset.univ.sup d, hasModulus_pi_iff.mpr ?_⟩
  intro i
  exact (hd i).mono (Finset.le_sup (Finset.mem_univ i))

end Products

end AlgebraicCurve.Modulus
