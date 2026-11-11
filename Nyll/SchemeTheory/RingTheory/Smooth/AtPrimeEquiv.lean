/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Pointwise smoothness under isomorphisms of source and target

A commuting square of ring isomorphisms identifies the actual local rings at
corresponding primes. Formal smoothness of the original localized map therefore
transports to the other localized map without replacing its algebra structure.
-/

@[expose] public section

noncomputable section

namespace RingHom.FormallySmooth

/-- Transport pointwise formal smoothness through a commuting pair of ring
isomorphisms, using the induced isomorphism of the original localizations. -/
theorem atPrime_of_equiv
    {R Q S T : Type*} [CommRing R] [CommRing Q] [CommRing S] [CommRing T]
    (eR : R ≃+* Q) (eS : S ≃+* T) (f : R →+* S) (g : Q →+* T)
    (hcomm : eS.toRingHom.comp f = g.comp eR.toRingHom) (p : PrimeSpectrum T)
    (hf : FormallySmooth ((algebraMap S
      (Localization.AtPrime (PrimeSpectrum.comap eS.toRingHom p).asIdeal)).comp f)) :
    ((algebraMap T (Localization.AtPrime p.asIdeal)).comp g).FormallySmooth := by
  let q : Ideal S := (PrimeSpectrum.comap eS.toRingHom p).asIdeal
  have hmap : q.primeCompl.map eS.toMonoidHom = p.asIdeal.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eS.symm x, ?_, eS.apply_symm_apply x⟩
      change eS (eS.symm x) ∉ p.asIdeal
      rw [eS.apply_symm_apply]
      exact hx
  let e : Localization.AtPrime q ≃+* Localization.AtPrime p.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime q) (Localization.AtPrime p.asIdeal) eS hmap
  have he (s : S) :
      e (algebraMap S (Localization.AtPrime q) s) =
        algebraMap T (Localization.AtPrime p.asIdeal) (eS s) :=
    IsLocalization.ringEquivOfRingEquiv_eq hmap s
  have hs := (RingHom.FormallySmooth.of_bijective
    (f := eR.symm.toRingHom) eR.symm.bijective).comp hf
  have ht := hs.comp (RingHom.FormallySmooth.of_bijective
    (f := e.toRingHom) e.bijective)
  have heq : e.toRingHom.comp
      (((algebraMap S (Localization.AtPrime q)).comp f).comp eR.symm.toRingHom) =
        (algebraMap T (Localization.AtPrime p.asIdeal)).comp g := by
    apply RingHom.ext
    intro x
    change e (algebraMap S (Localization.AtPrime q) (f (eR.symm x))) =
      algebraMap T (Localization.AtPrime p.asIdeal) (g x)
    rw [he]
    have hx := RingHom.congr_fun hcomm (eR.symm x)
    change eS (f (eR.symm x)) = g (eR (eR.symm x)) at hx
    rw [eR.apply_symm_apply] at hx
    rw [hx]
  rw [heq] at ht
  exact ht

end RingHom.FormallySmooth

namespace Algebra.IsSmoothAt

/-- The native algebra smoothness at corresponding primes is preserved by
an isomorphism of the base and the algebra with its original scalar map. -/
theorem of_ringEquiv
    {R Q S T : Type*} [CommRing R] [CommRing Q] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra Q T]
    (eR : R ≃+* Q) (eS : S ≃+* T)
    (hcomm : eS.toRingHom.comp (algebraMap R S) =
      (algebraMap Q T).comp eR.toRingHom) (p : PrimeSpectrum T)
    [IsSmoothAt R (PrimeSpectrum.comap eS.toRingHom p).asIdeal] :
    IsSmoothAt Q p.asIdeal := by
  let q := PrimeSpectrum.comap eS.toRingHom p
  have hf : RingHom.FormallySmooth
      ((algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap R S)) := by
    rw [← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)]
    exact RingHom.formallySmooth_algebraMap.mpr inferInstance
  have ht := RingHom.FormallySmooth.atPrime_of_equiv eR eS
    (algebraMap R S) (algebraMap Q T) hcomm p hf
  rw [← IsScalarTower.algebraMap_eq Q T (Localization.AtPrime p.asIdeal)] at ht
  exact RingHom.formallySmooth_algebraMap.mp ht

end Algebra.IsSmoothAt
