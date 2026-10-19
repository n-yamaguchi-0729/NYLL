/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClasses
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolUniqueness

/-!
# Evaluation on divisor classes with modulus

The principal-divisor modulus condition constructs unique additive maps on the
actual divisor class quotients. This is the abstract group-valued part of the
universal property; it does not claim that the resulting maps are scheme
morphisms or identify these quotients with the represented Picard sheaf.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]

namespace Divisor

/-- Evaluation of the finitely supported integer divisor at group-valued places. -/
def evaluation (a : Place K F → A) : Divisor K F →+ A :=
  Finsupp.liftAddHom (fun v =>
    { toFun := fun n : ℤ => n • a v
      map_zero' := zero_zsmul (a v)
      map_add' := fun m n => add_zsmul (a v) m n })

/-- Divisor evaluation is its actual finite-support sum. -/
theorem evaluation_eq_finsum (a : Place K F → A) (E : Divisor K F) :
    evaluation a E = ∑ᶠ v : Place K F, E v • a v := by
  classical
  change (∑ v ∈ E.support, E v • a v) = _
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  apply Finsupp.mem_support_iff.mpr
  intro hEv
  apply hv
  change E v • a v = 0
  rw [hEv, zero_zsmul]

/-- A point divisor evaluates to its specified integer multiple. -/
theorem evaluation_single (a : Place K F → A) (v : Place K F) (n : ℤ) :
    evaluation a (Finsupp.single v n) = n • a v :=
  Finsupp.liftAddHom_apply_single _ v n

end Divisor

namespace Modulus

variable {D : Modulus K F} {a : Place K F → A}

/-- The actual modulus condition annihilates every modulus-principal divisor. -/
theorem HasModulus.evaluation_eq_zero (ha : D.HasModulus a) {E : Divisor K F}
    (hE : E ∈ D.principal) : Divisor.evaluation a E = 0 := by
  obtain ⟨f, hf, hEf⟩ := hE
  rw [Divisor.evaluation_eq_finsum]
  have heq : (fun v : Place K F => E v • a v) = fun v => v.ord f • a v := by
    funext v
    rw [hEf v]
  rw [heq]
  exact ha (Units.mk0 f hf.ne_zero) hf

/-- The uniquely induced evaluation of the full modulus divisor class group. -/
def HasModulus.classEvaluation (ha : D.HasModulus a) : D.ClassGroup →+ A :=
  QuotientAddGroup.lift (D.principal.addSubgroupOf D.divAway)
    ((Divisor.evaluation a).comp D.divAway.subtype)
    (fun _E hE => ha.evaluation_eq_zero hE)

/-- On a representative, the quotient map gives the actual divisor evaluation. -/
theorem HasModulus.classEvaluation_mk (ha : D.HasModulus a) (E : D.divAway) :
    ha.classEvaluation (QuotientAddGroup.mk E) = Divisor.evaluation a E.1 := rfl

/-- The full class-group evaluation is uniquely determined by its values on
actual divisors avoiding the modulus. -/
theorem HasModulus.classEvaluation_unique (ha : D.HasModulus a) (φ : D.ClassGroup →+ A)
    (hφ : ∀ E : D.divAway, φ (QuotientAddGroup.mk E) = Divisor.evaluation a E.1) :
    φ = ha.classEvaluation := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact hφ E

/-- The actual evaluation homomorphism on the degree-zero modulus quotient. -/
def HasModulus.classEvaluationZero (ha : D.HasModulus a) : D.ClassGroupZero →+ A :=
  QuotientAddGroup.lift (D.principal.addSubgroupOf D.divAwayZero)
    ((Divisor.evaluation a).comp D.divAwayZero.subtype)
    (fun _E hE => ha.evaluation_eq_zero hE)

/-- A degree-zero divisor representative is evaluated by its finite sum. -/
theorem HasModulus.classEvaluationZero_mk (ha : D.HasModulus a) (E : D.divAwayZero) :
    ha.classEvaluationZero (D.mkZero E) = Divisor.evaluation a E.1 := rfl

/-- Uniqueness on the actual degree-zero class group follows from its proved
quotient presentation. -/
theorem HasModulus.classEvaluationZero_unique (ha : D.HasModulus a)
    (φ : D.ClassGroupZero →+ A)
    (hφ : ∀ E : D.divAwayZero, φ (D.mkZero E) = Divisor.evaluation a E.1) :
    φ = ha.classEvaluationZero := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact hφ E

end Modulus

end AlgebraicCurve
