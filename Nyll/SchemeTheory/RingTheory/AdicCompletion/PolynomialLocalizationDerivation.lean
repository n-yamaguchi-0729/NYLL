/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Derivation.Localization
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Partial derivatives on completed polynomial localizations

The partial derivative of the original polynomial ring is extended first
to its localization at a prime, then to that localization's native adic
completion. Its original coordinates still have Kronecker-delta derivatives. The
localization carrier is abstract to retain the canonical integer scalar
structures; `Localization.AtPrime p` is an available concrete carrier.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ : Type*} (p : Ideal (MvPolynomial σ ℤ)) [p.IsPrime]
variable (A : Type*) [CommRing A] [Algebra (MvPolynomial σ ℤ) A]
variable [IsLocalization p.primeCompl A]

/-- The original polynomial partial derivative on the actual localization
at the specified prime ideal. -/
def pderivLocalization (i : σ) :
    Derivation ℤ A A :=
  (pderiv i).localization p.primeCompl A

/-- The localized partial derivative agrees with the polynomial derivative. -/
theorem pderivLocalization_algebraMap (i : σ) (f : MvPolynomial σ ℤ) :
    pderivLocalization p A i (algebraMap (MvPolynomial σ ℤ) A f) =
      algebraMap (MvPolynomial σ ℤ) A (pderiv i f) :=
  Derivation.localization_algebraMap p.primeCompl A (pderiv i) f

variable (I : Ideal A)

/-- The actual extension of the original partial derivative to the adic
completion of the polynomial localization. -/
def pderivLocalizedAdicCompletion (i : σ) :
    Derivation ℤ (AdicCompletion I A)
      (AdicCompletion I A) :=
  (pderivLocalization p A i).adicCompletion I

/-- On the original polynomial elements, the completed localized partial
derivative retains the original values under the canonical algebra map. -/
theorem pderivLocalizedAdicCompletion_algebraMap (i : σ) (f : MvPolynomial σ ℤ) :
    pderivLocalizedAdicCompletion p A I i
        (algebraMap (MvPolynomial σ ℤ) (AdicCompletion I A) f) =
      algebraMap (MvPolynomial σ ℤ) (AdicCompletion I A) (pderiv i f) := by
  change (pderivLocalization p A i).adicCompletion I
      (algebraMap A (AdicCompletion I A)
        (algebraMap (MvPolynomial σ ℤ) A f)) =
    algebraMap A (AdicCompletion I A)
      (algebraMap (MvPolynomial σ ℤ) A (pderiv i f))
  rw [Derivation.adicCompletion_algebraMap, pderivLocalization_algebraMap]

/-- The original polynomial coordinates retain their Kronecker-delta
partial derivatives in the completed local ring. -/
theorem pderivLocalizedAdicCompletion_X [DecidableEq σ] (i j : σ) :
    pderivLocalizedAdicCompletion p A I i
        (algebraMap (MvPolynomial σ ℤ) (AdicCompletion I A) (X j)) =
      if i = j then 1 else 0 := by
  rw [pderivLocalizedAdicCompletion_algebraMap]
  by_cases h : i = j
  · subst j
    rw [pderiv_X_self, map_one, ite_eq_left rfl]
  · rw [pderiv_X_of_ne (Ne.symm h), map_zero, ite_eq_right h]

end MvPolynomial
