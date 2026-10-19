/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.BoundaryAway
import Nyll.SchemeTheory.FiniteEtale.Henselian.PointedEtale
import Nyll.SchemeTheory.FiniteEtale.Away.AlgEquivTransport

/-!
# The primitive Tag boundary Away map over the Henselian pointed base

At the intermediate Henselian local stage, a pointed etale neighbourhood
with unchanged residue field is canonically the base itself.  This file uses
that equivalence to move the primitive boundary Away map on the Tag local
factor from the pointed localization back to the Henselian base.

This does **not** impose a Henselian hypothesis on a general R4 base.  The
theorem is only for the strict/Henselian intermediate ring where
`HenselianLocalRing` is already available; descent to the original global
base is a separate step.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace EtaleFundamentalGroups

universe uR uC uS

/-- Over the intermediate Henselian local base, the Tag local factor retains
the literal primitive boundary Away map from that base.

The algebra `R → Dₚ` in the conclusion is the actual composite
`R → Cₚ → Dₚ`.  The inverse pointed equivalence is used only to prove
that the corresponding square is a pushout; no root cover or generic
component is an input. -/
theorem etaleChosenLocalFactor_henselian_boundaryAway
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [HenselianLocalRing R] [IsNoetherianRing C]
    [Algebra R C] [Algebra R S] [Algebra.Etale R C]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P
        (Algebra.ofId R C) (P.over_def (maximalIdeal R))))
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    let _ : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    let _ : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    let _ : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    let _ : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let _ : Algebra R Dₚ :=
      ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
    @Algebra.Etale
      (Localization.Away f)
      (Localization.Away (algebraMap R Dₚ f))
      _ _
      (Localization.awayMap (algebraMap R Dₚ) f).toAlgebra := by
  intro Q _ _ _ Cₚ Dₚ _ rDAlgebra
  let _ : SMul R Dₚ := rDAlgebra.toSMul
  let _ : IsScalarTower R Cₚ Dₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact localization_awayMap_etale_of_source_algEquiv
    (A := R) (C := Cₚ) (D := Dₚ)
    (henselianPointedEtaleLocalizationAlgEquiv P hres) f
    (etaleChosenLocalFactor_pointed_boundaryAway
      (R := R) (C := C) (S := S) f hAway P e P' heP' hfinite hunique)

end EtaleFundamentalGroups

end
