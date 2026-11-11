/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Extending derivations to a localization

The existing formally étale comparison of Kähler differentials extends
an actual derivation to a localization. No choice of a quotient-rule
presentation, square-zero algebra, or additional existence hypothesis is
needed. The extension agrees with the original derivation on ring elements.
-/

@[expose] public section

noncomputable section

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (M : Submonoid A) (B : Type*) [CommRing B]
variable [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization M B]

/-- Extension of a derivation through the actual localization map. -/
def localization (D : Derivation R A A) : Derivation R B B :=
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization M
  ((((Algebra.linearMap A B).comp D.liftKaehlerDifferential).liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap).compDer
      (KaehlerDifferential.D R B)

/-- The localization extension retains the original values through the
canonical algebra map. -/
theorem localization_algebraMap (D : Derivation R A A) (a : A) :
    D.localization M B (algebraMap A B a) = algebraMap A B (D a) := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization M
  change (((Algebra.linearMap A B).comp D.liftKaehlerDifferential).liftBaseChange B)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm
      (KaehlerDifferential.D R B (algebraMap A B a))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply,
    Derivation.liftKaehlerDifferential_comp_D, Algebra.linearMap_apply]

end Derivation
