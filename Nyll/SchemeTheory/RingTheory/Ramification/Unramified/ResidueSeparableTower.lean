/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Separable residue fields in an étale tower

For an integral local map, separability of the actual extension of local
residue fields supplies separability at every prime over the closed point:
integrality and locality force each such prime to be the target closed point.

An étale algebra over an intermediate ring preserves this property.
These results use the actual residue extensions, so they apply when the
base residue field is imperfect. They provide the residue-field step in
the tame ramification-index argument after adjoining a uniformizer root.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- For an integral local map, separability of the local residue extension
controls all primes over the closed point. -/
theorem hasSeparableResidueFieldsAt_maximalIdeal_of_isLocalRing
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.IsIntegral A B]
    [hsep : Algebra.IsSeparable
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    Algebra.HasSeparableResidueFieldsAt A B (IsLocalRing.maximalIdeal A) := by
  constructor
  intro q hq hqp
  have hmaxUnder : (q.under A).IsMaximal := by
    rw [← q.over_def (IsLocalRing.maximalIdeal A)]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hmax : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under q hmaxUnder
  have hqeq : q = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  subst q
  let : Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (Localization.AtPrime (IsLocalRing.maximalIdeal B)) :=
    Localization.AtPrime.algebraOfLiesOver _ _
  exact Algebra.isSeparable_residueField_iff.mpr hsep

/-- Étale extension of the target preserves separability of every residue
extension over a fixed base prime. -/
theorem hasSeparableResidueFieldsAt_of_etale_tower
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.Etale B C]
    (p : Ideal A) [p.IsPrime] [Algebra.HasSeparableResidueFieldsAt A B p] :
    Algebra.HasSeparableResidueFieldsAt A C p := by
  constructor
  intro r hr hrp
  let q := r.under B
  have : q.IsPrime := inferInstance
  have : q.LiesOver p := inferInstance
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p r
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver q r
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := inferInstance
  have : Algebra.IsSeparable q.ResidueField r.ResidueField := inferInstance
  exact Algebra.IsSeparable.trans p.ResidueField q.ResidueField r.ResidueField

end SchemeTheory
