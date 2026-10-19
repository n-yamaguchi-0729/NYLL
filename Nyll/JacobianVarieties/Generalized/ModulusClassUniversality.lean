/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusClassAbel

/-!
# Abstract universality of the modulus divisor quotient

A group-valued map with modulus induces the unique homomorphism on the
actual degree-zero divisor quotient that factors the class Abel map.
The point formula retains the residue-field degree. These are statements
about the divisor quotient; algebraicity of the induced scheme map is a
separate geometric assertion.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F A B : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup A] [AddCommGroup B]

/-- Divisor evaluation is natural for homomorphisms of commutative groups. -/
theorem Divisor.evaluation_map (a : Place K F → A) (h : A →+ B) :
    Divisor.evaluation (fun v => h (a v)) = h.comp (Divisor.evaluation a) := by
  apply Finsupp.addHom_ext
  intro v n
  rw [Divisor.evaluation_single]
  change n • h (a v) = h (Divisor.evaluation a (Finsupp.single v n))
  rw [Divisor.evaluation_single, map_zsmul]

namespace Modulus

variable {D : Modulus K F} {a : Place K F → A}

/-- The class Abel map is zero at the discarded modulus places. -/
theorem classAbel_of_mem_modulus (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) (v : Place K F) (hv : D v ≠ 0) :
    D.classAbel v₀ h₀ hdeg v = 0 := by
  classical
  have he : D.awayProjection (Finsupp.single v 1) = 0 :=
    Subtype.ext (Finsupp.filter_single_of_neg (fun w => D w = 0) hv)
  unfold classAbel
  rw [he, map_zero, map_zero]

/-- The induced class evaluation factors the actual class Abel map, with
the required basepoint correction and residue-field degree. -/
theorem HasModulus.classEvaluationZero_classAbel_apply (ha : D.HasModulus a)
    (v₀ : Place K F) (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1)
    (v : Place K F) (hv : D v = 0) :
    ha.classEvaluationZero (D.classAbel v₀ h₀ hdeg v) =
      a v - (v.deg : ℤ) • a v₀ := by
  rw [D.classAbel_of_away v₀ h₀ hdeg v hv, ha.classEvaluationZero_mk]
  change Divisor.evaluation a
    (Finsupp.single v 1 - Divisor.degree (Finsupp.single v 1) • Finsupp.single v₀ 1) = _
  rw [map_sub, map_zsmul, Divisor.evaluation_single, Divisor.evaluation_single,
    one_zsmul, one_zsmul, Divisor.degree_single, one_mul]

/-- Values on the supported-away Abel classes determine an actual group
homomorphism out of the modulus class group. -/
theorem classAbel_addHom_ext (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) (φ ψ : D.ClassGroupZero →+ A)
    (heq : ∀ v : Place K F, D v = 0 →
      φ (D.classAbel v₀ h₀ hdeg v) = ψ (D.classAbel v₀ h₀ hdeg v)) : φ = ψ := by
  have hall : (fun v => φ (D.classAbel v₀ h₀ hdeg v)) =
      fun v => ψ (D.classAbel v₀ h₀ hdeg v) := by
    funext v
    by_cases hv : D v = 0
    · exact heq v hv
    · rw [D.classAbel_of_mem_modulus v₀ h₀ hdeg v hv, map_zero, map_zero]
  apply AddMonoidHom.ext
  intro x
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hsum := congrArg (fun b : Place K F → A => Divisor.evaluation b E.1) hall
  rw [Divisor.evaluation_map, Divisor.evaluation_map] at hsum
  change φ (Divisor.evaluation (D.classAbel v₀ h₀ hdeg) E.1) =
    ψ (Divisor.evaluation (D.classAbel v₀ h₀ hdeg) E.1) at hsum
  rw [D.evaluation_classAbel_degreeZero] at hsum
  exact hsum

/-- The complete abstract factorization theorem for the actual quotient.
No morphism algebraicity is inferred from this abstract group assertion. -/
theorem HasModulus.existsUnique_classAbel_factorization (ha : D.HasModulus a)
    (v₀ : Place K F) (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) :
    ∃! φ : D.ClassGroupZero →+ A,
      ∀ v : Place K F, D v = 0 →
        φ (D.classAbel v₀ h₀ hdeg v) = a v - (v.deg : ℤ) • a v₀ := by
  refine ⟨ha.classEvaluationZero, ha.classEvaluationZero_classAbel_apply v₀ h₀ hdeg, ?_⟩
  intro φ hφ
  apply D.classAbel_addHom_ext v₀ h₀ hdeg
  intro v hv
  exact (hφ v hv).trans (ha.classEvaluationZero_classAbel_apply v₀ h₀ hdeg v hv).symm

end Modulus

end AlgebraicCurve
