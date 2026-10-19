/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Tame field extensions with respect to a DVR

This is the field-extension condition of Stacks Project, Definition
15.113.7 (tag `09E9`). Its intended application is to a finite separable
extension of the fraction field of the displayed DVR.

Tameness is automatic in residue characteristic zero. Otherwise each
maximal prime of the literal integral closure must have separable residue
extension and ramification index invertible in the base residue field.
For a field of positive characteristic, invertibility of the natural
number is exactly being prime to that characteristic.

The residue algebra below is the canonical map of prime residue fields
induced by the original coefficient map. It is retained explicitly to
avoid reconstructing its localization and scalar-tower dictionaries.
https://stacks.math.columbia.edu/tag/09E9
-/

noncomputable section

universe u v

namespace SchemeTheory

/-- Tameness of a field extension with respect to a DVR, expressed on the
actual maximal primes of its integral closure. Finiteness and separability
of the ambient fraction-field extension are supplied separately by users
of this predicate, as with `IsUnramifiedOverDVR`. -/
def IsTamelyRamifiedOverDVR (R : Type u) (L : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra R L] : Prop :=
  ringChar (IsLocalRing.ResidueField R) = 0 ∨
    ∀ (Q : Ideal (integralClosure R L)) [Q.IsMaximal],
      let : Algebra (Q.under R).ResidueField Q.ResidueField :=
        (Ideal.ResidueField.map (Q.under R) Q
          (algebraMap R (integralClosure R L)) rfl).toAlgebra
      Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
        IsUnit (Ideal.ramificationIdx' (Q.under R) Q : (Q.under R).ResidueField)

end SchemeTheory
