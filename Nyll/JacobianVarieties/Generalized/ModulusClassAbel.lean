/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.LocalSymbolBoundary
import Mathlib.Data.Finsupp.Ext

/-!
# The Abel map into the actual modulus divisor class group

At a place away from the modulus, the class-valued Abel map sends `v` to
`[v - deg(v) v₀]`, where the base place `v₀` has degree one. This map has the
full modulus, its induced evaluation on degree-zero classes is the identity,
and its local symbol is the negative of the isolated local-unit boundary.
Over an algebraically closed field this is the usual point-minus-basepoint map.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Discard the coefficients at the modulus, as an actual divisor homomorphism. -/
def awayProjection (D : Modulus K F) : Divisor K F →+ D.divAway := by
  classical
  exact
    { toFun := fun E => ⟨E.filter (fun v => D v = 0), by
        intro v hv
        rw [Finsupp.filter_apply, ite_eq_right hv]⟩
      map_zero' := Subtype.ext (Finsupp.filter_zero _)
      map_add' := fun E E' => Subtype.ext Finsupp.filter_add }

/-- The projection fixes every divisor actually supported away from the modulus. -/
theorem awayProjection_coe (D : Modulus K F) (E : D.divAway) :
    D.awayProjection (E : Divisor K F) = E := by
  classical
  apply Subtype.ext
  ext v
  change (if D v = 0 then (E : Divisor K F) v else 0) = (E : Divisor K F) v
  by_cases hv : D v = 0
  · exact ite_eq_left hv
  · rw [ite_eq_right hv, E.2 v hv]

/-- A point outside the modulus as a supported-away divisor. -/
def awayPoint (D : Modulus K F) (v : Place K F) (hv : D v = 0) : D.divAway := by
  classical
  refine ⟨Finsupp.single v 1, ?_⟩
  intro w hw
  have hwv : w ≠ v := fun he => hw (he.symm ▸ hv)
  exact Finsupp.single_eq_of_ne hwv

/-- Normalize the degree by subtracting the corresponding multiple of a
degree-one base place. -/
def normalizeAway (D : Modulus K F) (v₀ : Place K F) (h₀ : D v₀ = 0)
    (hdeg : v₀.deg = 1) : D.divAway →+ D.divAwayZero where
  toFun E := ⟨(E : Divisor K F) - Divisor.degree (E : Divisor K F) • Finsupp.single v₀ 1,
    D.divAway.sub_mem E.2 (D.divAway.zsmul_mem (D.awayPoint v₀ h₀).2 _), by
      apply Divisor.mem_degZero.mpr
      rw [map_sub, map_zsmul, Divisor.degree_single, hdeg, Nat.cast_one,
        mul_one, zsmul_eq_mul, mul_one, Int.cast_id, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    change (0 : Divisor K F) - Divisor.degree 0 • Finsupp.single v₀ 1 = 0
    rw [map_zero, zero_zsmul, sub_zero]
  map_add' E E' := by
    apply Subtype.ext
    change (E : Divisor K F) + (E' : Divisor K F) -
      Divisor.degree ((E : Divisor K F) + (E' : Divisor K F)) • Finsupp.single v₀ 1 =
        ((E : Divisor K F) - Divisor.degree (E : Divisor K F) • Finsupp.single v₀ 1) +
        ((E' : Divisor K F) - Divisor.degree (E' : Divisor K F) • Finsupp.single v₀ 1)
    rw [map_add, add_zsmul]
    abel

/-- Normalization fixes an actual degree-zero divisor. -/
theorem normalizeAway_degreeZero (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) (E : D.divAwayZero) :
    D.normalizeAway v₀ h₀ hdeg ⟨E.1, E.2.1⟩ = E := by
  apply Subtype.ext
  change E.1 - Divisor.degree E.1 • Finsupp.single v₀ 1 = E.1
  rw [Divisor.mem_degZero.mp E.2.2, zero_zsmul, sub_zero]

/-- The divisor-class Abel map, extended by zero at the modulus. -/
def classAbel (D : Modulus K F) (v₀ : Place K F) (h₀ : D v₀ = 0)
    (hdeg : v₀.deg = 1) (v : Place K F) : D.ClassGroupZero :=
  D.mkZero (D.normalizeAway v₀ h₀ hdeg (D.awayProjection (Finsupp.single v 1)))

/-- Away from the modulus this is the actual normalized point divisor. -/
theorem classAbel_of_away (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) (v : Place K F) (hv : D v = 0) :
    D.classAbel v₀ h₀ hdeg v =
      D.mkZero (D.normalizeAway v₀ h₀ hdeg (D.awayPoint v hv)) := by
  unfold classAbel
  rw [show D.awayProjection (Finsupp.single v 1) = D.awayPoint v hv from
    D.awayProjection_coe (D.awayPoint v hv)]

/-- Divisor evaluation of the class Abel map is exactly projection followed
by normalization and passage to the actual quotient. -/
theorem evaluation_classAbel (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) :
    Divisor.evaluation (D.classAbel v₀ h₀ hdeg) =
      (D.mkZero.comp (D.normalizeAway v₀ h₀ hdeg)).comp D.awayProjection := by
  apply Finsupp.addHom_ext
  intro v n
  rw [Divisor.evaluation_single]
  have he : Finsupp.single v n = n • (Finsupp.single v 1 : Divisor K F) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he, map_zsmul]
  rfl

/-- On degree-zero supported-away divisors, class-Abel evaluation is the
original quotient map. -/
theorem evaluation_classAbel_degreeZero (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) (E : D.divAwayZero) :
    Divisor.evaluation (D.classAbel v₀ h₀ hdeg) E.1 = D.mkZero E := by
  rw [D.evaluation_classAbel v₀ h₀ hdeg]
  change D.mkZero (D.normalizeAway v₀ h₀ hdeg (D.awayProjection E.1)) = D.mkZero E
  rw [D.awayProjection_coe ⟨E.1, E.2.1⟩, D.normalizeAway_degreeZero]

variable [HasPrincipalDivisors K F]

/-- The actual class Abel map has the full modulus, proved from its
principal-divisor quotient relation. -/
theorem hasModulus_classAbel (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) : D.HasModulus (D.classAbel v₀ h₀ hdeg) := by
  intro g hg
  obtain ⟨E, hE, hdegE⟩ := HasPrincipalDivisors.exists_divisor (K := K) (g : F) g.ne_zero
  have haway : E ∈ D.divAway := fun v hv => (hE v).trans (hg.ord_eq_zero v hv)
  let E₀ : D.divAwayZero := ⟨E, haway, Divisor.mem_degZero.mpr hdegE⟩
  have hs : (∑ᶠ v : Place K F, v.ord (g : F) • D.classAbel v₀ h₀ hdeg v) =
      Divisor.evaluation (D.classAbel v₀ h₀ hdeg) E₀.1 := by
    rw [Divisor.evaluation_eq_finsum]
    apply finsum_congr
    intro v
    change v.ord (g : F) • D.classAbel v₀ h₀ hdeg v = E v • D.classAbel v₀ h₀ hdeg v
    rw [hE v]
  rw [hs, D.evaluation_classAbel_degreeZero]
  exact (QuotientAddGroup.eq_zero_iff E₀).mpr ⟨(g : F), hg, hE⟩

/-- The class-group map induced by the class Abel map is the identity. -/
theorem classEvaluationZero_classAbel (D : Modulus K F) (v₀ : Place K F)
    (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1) :
    (D.hasModulus_classAbel v₀ h₀ hdeg).classEvaluationZero =
      AddMonoidHom.id D.ClassGroupZero := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact D.evaluation_classAbel_degreeZero v₀ h₀ hdeg E

/-- The local symbol of the actual class Abel map is minus the principal
boundary of an isolated unit jet. -/
theorem unitBoundary_eq_neg_classAbel_localSymbol (D : Modulus K F)
    (v₀ : Place K F) (h₀ : D v₀ = 0) (hdeg : v₀.deg = 1)
    (f : D.awayUnits) (v : Place K F) (hv : D v ≠ 0)
    (hisolated : ∀ w : Place K F, D w ≠ 0 → w ≠ v →
      w.CongruentOne (D w) (f.1 : F)) :
    D.unitBoundary (Additive.ofMul f) =
      -(D.hasModulus_classAbel v₀ h₀ hdeg).localSymbol v (Additive.ofMul f.1) := by
  have h := (D.hasModulus_classAbel v₀ h₀ hdeg).classEvaluationZero_isolated_unitBoundary
    f v hv hisolated
  rw [D.classEvaluationZero_classAbel v₀ h₀ hdeg] at h
  exact h

end AlgebraicCurve.Modulus
