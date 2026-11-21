/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.LocalizationComparison
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.LocalFactor
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Tag coordinates starting from an arbitrary normalization prime

The older chosen-factor comparison starts with the Tag 00UJ data and then
extracts a generic-fibre component.  Here the direction is reversed: an
arbitrary prime of the normalization is first supplied to 00UJ itself.
The contraction equality returned by 00UJ recovers the local ring of that
input prime, while smooth normalization base change extracts the actual
generic component selected by the same Tag prime.

Thus the chosen Away factor, the input normalization prime, and the produced
component prime are compared by constructed equivalences.  No comparison
equivalence or ideal equality is an input.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uR uL

/-- Scalar restriction through an integral closure also holds after prime localization. -/
private theorem localIntegralClosure_tower
    {R B M : Type*} [CommRing R] [CommRing B] [CommRing M]
    [Algebra R B] [Algebra R M] [Algebra B M] [IsScalarTower R B M]
    (q : PrimeSpectrum (integralClosure B M)) :
    IsScalarTower R B (Localization.AtPrime q.asIdeal) :=
  IsScalarTower.to₁₂₄ R B (integralClosure B M) (Localization.AtPrime q.asIdeal)

private theorem chosenAwayLocalization_baseTower
    {R : Type uR} {C : Type uR} {L : Type uL}
    [CommRing R] [CommRing C] [Algebra R C] [Field L] [Algebra R L]
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L)) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') :
    let Q := etaleChosenAwayPrime e P'
    let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) := by
  intro Q primeQ overTensor overBase localAlgebra
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : IsScalarTower C Cₚ Dₚ := Localization.AtPrime.instIsScalarTower P Q
  exact IsScalarTower.to₁₃₄ R C Cₚ Dₚ

private theorem componentLocalization_baseTower
    {R : Type uR} {C : Type uR} {L : Type uL}
    [CommRing R] [CommRing C] [Algebra R C] [Field L] [Algebra R L]
    (P : Ideal C) [P.IsPrime]
    (m : MaximalSpectrum (Localization.AtPrime P ⊗[R] L))
    (q : PrimeSpectrum
      (integralClosure (Localization.AtPrime P) (FiniteEtaleGenericFiberComponent m.asIdeal))) :
    IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q.asIdeal) := by
  let Cₚ := Localization.AtPrime P
  let G := Cₚ ⊗[R] L
  let M := FiniteEtaleGenericFiberComponent m.asIdeal
  let : IsScalarTower R Cₚ G := inferInstance
  let : IsScalarTower R Cₚ M := Ideal.Quotient.isScalarTower R Cₚ m.asIdeal
  exact localIntegralClosure_tower (R := R) q

private theorem chosenComponentLocalization_overBase
    {R : Type uR} {C : Type uR} {L : Type uL}
    [CommRing R] [CommRing C] [Algebra R C] [Field L] [Algebra R L]
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L)) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (m : MaximalSpectrum (Localization.AtPrime P ⊗[R] L))
    (q : PrimeSpectrum
      (integralClosure (Localization.AtPrime P) (FiniteEtaleGenericFiberComponent m.asIdeal))) :
    let Q := etaleChosenAwayPrime e P'
    let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    let X := Localization.AtPrime q.asIdeal
    let : CommRing Cₚ := inferInstance
    let : CommRing Dₚ := inferInstance
    let : CommRing X := inferInstance
    let : Algebra Cₚ Dₚ := Localization.AtPrime.algebraOfLiesOver P Q
    let : Algebra R Cₚ := inferInstance
    let : Algebra R Dₚ := inferInstance
    let : Algebra Cₚ X := inferInstance
    let : Algebra R X := inferInstance
    (Dₚ ≃ₐ[Cₚ] X) → Nonempty (Dₚ ≃ₐ[R] X) := by
  intro Q primeQ overQ overP Cₚ Dₚ X ringCₚ ringDₚ ringX algQ baseCₚ baseDₚ localX baseX E
  have sourceTower := chosenAwayLocalization_baseTower P e P' heP'
  have targetTower := componentLocalization_baseTower P m q
  let equiv := @AlgEquiv.restrictScalars R Cₚ Dₚ X
    (inferInstance : CommRing R).toCommSemiring ringCₚ.toCommSemiring
    ringDₚ.toSemiring ringX.toSemiring baseCₚ algQ localX baseDₚ baseX sourceTower targetTower E
  refine ⟨?_⟩
  with_reducible exact equiv

private theorem compareChosenPrimeLocalizations
    {R : Type uR} {L : Type uL} {C : Type uR}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (p : Ideal (integralClosure R L)) [p.IsPrime]
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L)) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') :
    let Q := etaleChosenAwayPrime e P'
    let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    (Dₚ ≃ₐ[R] Localization.AtPrime p) →
    ∃ (m : MaximalSpectrum (Cₚ ⊗[R] L))
      (q : PrimeSpectrum
        (integralClosure Cₚ (FiniteEtaleGenericFiberComponent m.asIdeal))),
      Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime p) ∧
        Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime q.asIdeal) ∧
        Nonempty (Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q.asIdeal) := by
  intro Q hQprime Cₚ Dₚ Einput
  have : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  have : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  obtain ⟨m, q, ⟨Ecomponent⟩⟩ :=
    exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv
      (R := R) (C := C) (L := L) P e P' heP'
  obtain ⟨EcomponentR⟩ := chosenComponentLocalization_overBase P e P' heP' m q Ecomponent
  exact ⟨m, q, ⟨Einput⟩, ⟨EcomponentR⟩, ⟨Einput.symm.trans EcomponentR⟩⟩

/-- Apply Tag 00UJ directly to an arbitrary prime `p` of a finite
normalization over a Henselian local ring.

The theorem returns both canonical views of the same chosen local factor:
the localization at the original input prime and the localization at the
normalization prime in the source-produced generic tensor component. -/
theorem
    exists_etaleChosenLocalFactor_arbitraryNormalizationPrime_component
    {R : Type uR} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [Module.Finite R (integralClosure R L)]
    (p : Ideal (integralClosure R L)) [p.IsPrime]
    [p.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ (C : Type uR) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra.Etale R C)
      (P : Ideal C) (_ : P.IsPrime)
      (_ : P.LiesOver (IsLocalRing.maximalIdeal R))
      (e : C ⊗[R] integralClosure R L) (_ : IsIdempotentElem e)
      (P' : Ideal (C ⊗[R] integralClosure R L))
      (_ : P'.IsPrime) (_ : P'.LiesOver P)
      (heP' : e ∉ P'),
        P'.comap Algebra.TensorProduct.includeRight.toRingHom = p ∧
        Function.Bijective
          (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
            (Algebra.ofId R C)
            (P.over_def (IsLocalRing.maximalIdeal R))) ∧
        Module.Finite C (Localization.Away e) ∧
        (∀ P'' : Ideal (C ⊗[R] integralClosure R L),
          P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') ∧
        let Q := etaleChosenAwayPrime e P'
        let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
        let Cₚ := Localization.AtPrime P
        let Dₚ := Localization.AtPrime Q
        ∃ (m : MaximalSpectrum (Cₚ ⊗[R] L))
          (q : PrimeSpectrum
            (integralClosure Cₚ (FiniteEtaleGenericFiberComponent m.asIdeal))),
          Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime p) ∧
            Nonempty (Dₚ ≃ₐ[R] Localization.AtPrime q.asIdeal) ∧
            Nonempty (Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q.asIdeal) := by
  let S := integralClosure R L
  obtain ⟨C, ringC, algC, etaleC, P, primeP, overP, e, heidem, P', primeP', overP', heP',
      hP'p, hres, hfinite, hunique, ⟨Einput⟩⟩ :=
    exists_etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
      (R := R) (S := S) p
  refine ⟨C, ringC, algC, etaleC, P, primeP, overP, e, heidem,
    P', primeP', overP', heP', hP'p, hres, hfinite, hunique, ?_⟩
  exact compareChosenPrimeLocalizations p P e P' heP' Einput

end EtaleFundamentalGroups.Kummer

end
