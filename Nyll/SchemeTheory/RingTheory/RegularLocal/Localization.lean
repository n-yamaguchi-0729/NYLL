/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.ProjectiveDimension
public import Nyll.SchemeTheory.RingTheory.RegularLocal.FiniteProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Prime localizations of a regular local ring

The finite module `R/p` has finite projective dimension over the original
regular local ring. Its actual localization is the residue field at `p`.
The Serre criterion therefore proves regularity of that prime localization.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace SchemeTheory.RegularLocalResolution

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Every prime localization of a regular local ring is regular local. -/
theorem isRegularLocalRing_localizationAtPrime (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let Rp := Localization.AtPrime p
  let M := ModuleCat.of R (R ⧸ p)
  let J : Submodule Rp Rp :=
    p.localized' Rp p.primeCompl (Algebra.linearMap R Rp)
  have hJ : J = maximalIdeal Rp := by
    calc
      J = p.map (algebraMap R Rp) := by
        change p.localized' Rp p.primeCompl (Algebra.linearMap R Rp) = _
        rw [Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]
      _ = maximalIdeal Rp := IsLocalization.AtPrime.map_eq_maximalIdeal p Rp
  let f : (R ⧸ p) →ₗ[R] Rp ⧸ J :=
    p.toLocalizedQuotient' Rp p.primeCompl (Algebra.linearMap R Rp)
  have : IsLocalizedModule p.primeCompl (M.localizedModuleMkLinearMap p.primeCompl) :=
    ModuleCat.localizedModule_isLocalizedModule M p.primeCompl
  let e₀ : M.localizedModule p.primeCompl ≃ₗ[Rp] Rp ⧸ J :=
    LinearEquiv.extendScalarsOfIsLocalization p.primeCompl Rp
      (IsLocalizedModule.linearEquiv p.primeCompl
        (M.localizedModuleMkLinearMap p.primeCompl) f)
  let e : M.localizedModule p.primeCompl ≃ₗ[Rp] ResidueField Rp :=
    e₀.trans (Submodule.quotEquivOfEq J (maximalIdeal Rp) hJ)
  have hpd : HasProjectiveDimensionLE (M.localizedModule p.primeCompl)
      (maximalIdeal R).spanFinrank :=
    localized_finite_module_hasProjectiveDimensionLE p.primeCompl (R ⧸ p)
  have hpdResidue : HasProjectiveDimensionLE (ModuleCat.of Rp (ResidueField Rp))
      (maximalIdeal R).spanFinrank :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e (maximalIdeal R).spanFinrank
  exact IsLocalRing.isRegularLocalRing_of_residue_hasProjectiveDimensionLE
    (maximalIdeal R).spanFinrank Rp hpdResidue

/-- A regular local ring is a regular ring. -/
theorem isRegularRing_of_isRegularLocalRing : IsRegularRing R where
  isRegularLocalRing_localization p _ := isRegularLocalRing_localizationAtPrime R p

end SchemeTheory.RegularLocalResolution
