/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.LocalEtaleFromClosedFiber
public import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteEtaleNeighborhood
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Étale neighborhoods from an actual quotient pushout

The given surjection factors the residue map at a prime containing its
kernel. The existing pushout comparison and cancellation of base change
identify the original residue-fiber algebra with a base change of the
given étale quotient algebra. The local finite-projective criterion and
the existing spreading theorem then give a principal neighborhood.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SchemeTheory

/-- A finite flat, finitely presented algebra is étale on a principal
neighborhood of a base prime if its actual quotient pushout is étale and
the prime contains the kernel of the given coefficient surjection.
Both coefficient actions in the conclusion are retained from the given
ring maps. -/
theorem exists_etale_away_of_isPushout_closedFiber
    {R R₀ C B : CommRingCat.{u}}
    (π : R ⟶ R₀) (c : R ⟶ C) (q : C ⟶ B) (b : R₀ ⟶ B)
    (hπ : Function.Surjective π)
    (hpush : IsPushout c π q b)
    (p : PrimeSpectrum R) (hp : RingHom.ker π.hom ≤ p.asIdeal) :
    let : Algebra R C := c.hom.toAlgebra
    let : Algebra R₀ B := b.hom.toAlgebra
    Module.Finite R C →
      Module.Flat R C →
      Algebra.FinitePresentation R C →
      Algebra.Etale R₀ B →
      ∃ r : R, r ∉ p.asIdeal ∧
        Algebra.Etale R (Localization.Away (algebraMap R C r)) := by
  intro hRC hR₀B hfinite hflat hfp hEtale
  let hRR₀ : Algebra R R₀ := π.hom.toAlgebra
  let hCB : Algebra C B := q.hom.toAlgebra
  let hRB : Algebra R B := (π ≫ b).hom.toAlgebra
  have hRR₀B : IsScalarTower R R₀ B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hRCB : IsScalarTower R C B :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w).symm
  have hbase : Algebra.IsPushout R R₀ C B :=
    CommRingCat.isPushout_iff_isPushout.mp hpush.flip
  let e : R₀ ⊗[R] C ≃ₐ[R₀] B := Algebra.IsPushout.equiv R R₀ C B
  have hTensor : Algebra.Etale R₀ (R₀ ⊗[R] C) :=
    Algebra.Etale.of_equiv e.symm
  have hpPrime : p.asIdeal.IsPrime := p.isPrime
  let κ : Type u := p.asIdeal.ResidueField
  have hκ : RingHom.ker π.hom ≤ RingHom.ker (algebraMap R κ) := by
    rw [Ideal.ker_algebraMap_residueField]
    exact hp
  let ρ : R₀ →+* κ :=
    π.hom.liftOfSurjective hπ ⟨algebraMap R κ, hκ⟩
  let hR₀κ : Algebra R₀ κ := ρ.toAlgebra
  have hRR₀κ : IsScalarTower R R₀ κ :=
    IsScalarTower.of_algebraMap_eq'
      (π.hom.liftOfSurjective_comp hπ ⟨algebraMap R κ, hκ⟩).symm
  have hDouble : Algebra.Etale κ (κ ⊗[R₀] (R₀ ⊗[R] C)) := inferInstance
  have hFiber : Algebra.Etale κ (κ ⊗[R] C) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R R₀ κ κ C)
  let Rp : Type u := Localization.AtPrime p.asIdeal
  let Cp : Type u := Rp ⊗[R] C
  have hLocalFinite : Module.Finite Rp Cp := inferInstance
  have hLocalFlat : Module.Flat Rp Cp := inferInstance
  have hLocalFree : Module.Free Rp Cp := Module.free_of_flat_of_isLocalRing
  have hLocalProjective : Module.Projective Rp Cp := inferInstance
  have hLocalFiber : Algebra.Etale κ (κ ⊗[Rp] Cp) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R Rp κ κ C).symm
  have hLocalEtale : Algebra.Etale Rp Cp :=
    Algebra.etale_of_finite_projective_of_etale_closedFiber Rp Cp
  have hLocalized : Algebra.Etale Rp
      (Localization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl)) :=
    Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl C)
  exact exists_etale_away_of_isEtaleAt_fiber p
    (isEtaleAt_of_localizedAlgebra_etale p hLocalized)

end SchemeTheory
