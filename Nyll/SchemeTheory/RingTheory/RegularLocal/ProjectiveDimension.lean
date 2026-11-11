/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalFiniteFreeResolution
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Projective dimension bounds from existing finite free resolutions

NYLL's finite free resolutions are converted to the existing categorical
projective-dimension predicate. Localization preserves the resulting bound.
The converse Serre criterion is in `FiniteProjectiveDimension`; its use for
prime localizations is in `Localization`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace SchemeTheory.RegularLocalResolution

open P2mAB.StablyFree

variable {R : Type u} [CommRing R]

/-- The existing finite free resolution supplies its actual projective
 dimension bound in the category of modules. -/
theorem hasProjectiveDimensionLE_of_hasFFR (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] (h : HasFFR R n M) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing M with
  | zero =>
    have : Module.Free R M := h.2
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      ((IsProjective.iff_projective (R := R) M).mp Module.Projective.of_free)
  | succ n ih =>
    obtain ⟨k, f, hf, hker⟩ := h
    exact ((LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃_iff
      n ((IsProjective.iff_projective (R := R) (Fin k → R)).mp
        Module.Projective.of_free)).mpr (ih (LinearMap.ker f) hker)

/-- Every finite module over a regular local ring has projective dimension
at most the dimension of that local ring. -/
theorem finite_module_hasProjectiveDimensionLE [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLE (ModuleCat.of R M) (IsLocalRing.maximalIdeal R).spanFinrank :=
  hasProjectiveDimensionLE_of_hasFFR _ M
    (hasFFR (IsLocalRing.maximalIdeal R).spanFinrank
      IsRegularLocalRing.spanFinrank_maximalIdeal.symm M)

/-- Localizing an actual finite module over a regular local ring retains
the finite projective-dimension bound. -/
theorem localized_finite_module_hasProjectiveDimensionLE [IsRegularLocalRing R]
    (S : Submonoid R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLE ((ModuleCat.of R M).localizedModule S)
      (IsLocalRing.maximalIdeal R).spanFinrank := by
  have : HasProjectiveDimensionLE (ModuleCat.of R M)
      (IsLocalRing.maximalIdeal R).spanFinrank := finite_module_hasProjectiveDimensionLE M
  exact ModuleCat.localizedModule_hasProjectiveDimensionLE _ S (ModuleCat.of R M)

end SchemeTheory.RegularLocalResolution
