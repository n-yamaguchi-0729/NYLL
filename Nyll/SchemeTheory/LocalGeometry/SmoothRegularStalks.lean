/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Smooth.RegularBase
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular source stalks of a smooth morphism over a regular affine base

On each affine source chart, smoothness supplies a smooth algebra over
the regular base ring. Its prime localizations are regular by the
polynomial and étale factorization of standard smooth algebras. The
canonical identification with the actual scheme stalk transports this
regularity to the source scheme.

In particular, every stalk of a smooth scheme over a DVR is regular.
The result applies after any DVR extension in the normalized-base-change
argument of Stacks Project, Proposition 58.30.2.
https://stacks.math.columbia.edu/tag/0C0Q
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A smooth morphism to an affine scheme with regular coordinate ring
has regular local rings at every source point. -/
theorem Smooth.isRegularLocalRing_stalk_of_isRegularRing
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsAffine S] [IsRegularRing Γ(S, ⊤)] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hle : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  let : Algebra Γ(S, ⊤) Γ(X, U) := (f.appLE ⊤ U hle).hom.toAlgebra
  have : Algebra.Smooth Γ(S, ⊤) Γ(X, U) :=
    Smooth.smooth_appLE f (isAffineOpen_top S) hU hle
  have : IsRegularRing Γ(X, U) :=
    Algebra.Smooth.isRegularRing_of_isRegularRing Γ(S, ⊤) Γ(X, U)
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv

/-- The regularity conclusion uses the original coordinate ring of an
affine base, with its canonical global-sections identification. -/
theorem Smooth.isRegularLocalRing_stalk_over_spec
    {R : Type u} [CommRing R] [IsRegularRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have : IsRegularRing Γ(Spec (.of R), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  exact Smooth.isRegularLocalRing_stalk_of_isRegularRing f x

end AlgebraicGeometry
