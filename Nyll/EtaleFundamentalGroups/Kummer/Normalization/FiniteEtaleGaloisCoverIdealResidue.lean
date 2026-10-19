/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction
import Mathlib.RingTheory.Invariant.Galois
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Mathlib.RingTheory.Ideal.Over

/-!
# Residue actions in finite-etale Galois-cover quotients

The residue action of the normalization-prime decomposition group has ideal
inertia as its kernel, both internally and after mapping the kernel into the
full categorical finite quotient.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped Pointwise

namespace EtaleFundamentalGroups.Kummer

universe u uA uB

/-- Reduction on a normalization prime, expressed directly on the
categorical finite quotient of a Galois cover. -/
noncomputable def finiteEtaleGaloisCoverIdealResidueHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      let _ : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      let p : Ideal A := P.comap (algebraMap A B)
      let _ : P.LiesOver p := ⟨rfl⟩
      MulAction.stabilizer (Aut Y)ᵐᵒᵖ P →*
        ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction hComm p hLiesOver
  exact Ideal.Quotient.stabilizerHom P p (Aut Y)ᵐᵒᵖ

/-- The kernel of the categorical residue action is the ideal inertia inside
the decomposition group. -/
theorem finiteEtaleGaloisCoverIdealResidueHom_ker
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      let _ : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      (finiteEtaleGaloisCoverIdealResidueHom Y hY A B P).ker =
        P.toAddSubgroup.inertia
          (MulAction.stabilizer (Aut Y)ᵐᵒᵖ P) := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction hComm
  let p : Ideal A := P.comap (algebraMap A B)
  let hLiesOver : P.LiesOver p := ⟨rfl⟩
  exact Ideal.Quotient.ker_stabilizerHom P p (Aut Y)ᵐᵒᵖ

/-- Mapping the residue-action kernel back into the finite quotient gives
exactly the normalization-prime ideal inertia image. -/
theorem finiteEtaleGaloisCoverIdealResidueHom_map_ker
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      let _ : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      (finiteEtaleGaloisCoverIdealResidueHom Y hY A B P).ker.map
          (Subgroup.subtype (MulAction.stabilizer (Aut Y)ᵐᵒᵖ P)) =
        P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction hComm
  let p : Ideal A := P.comap (algebraMap A B)
  let hLiesOver : P.LiesOver p := ⟨rfl⟩
  exact Ideal.Quotient.map_ker_stabilizer_subtype P p (Aut Y)ᵐᵒᵖ

end EtaleFundamentalGroups.Kummer
