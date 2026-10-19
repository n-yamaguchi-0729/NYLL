/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentationCharts
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentAffineLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Localization at projective coordinate sections

The nonvanishing locus of the regular ratio `X j / X i` is the
intersection of the corresponding standard charts. Quasicoherence
then supplies numerator lifting and a power bound on the kernel for
the actual section restriction to that intersection. The two clauses
are retained together because gluing local numerators needs both.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The nonvanishing locus of a coordinate ratio is the standard overlap. -/
theorem coordinateRatioSection_basicOpen (i j : Fin (n + 1)) :
    (Proj 𝒜).basicOpen (coordinateRatioSection R n i j) =
      standardOpen R n i ⊓ standardOpen R n j := by
  apply le_antisymm
  · intro x hx
    have hi : x ∈ standardOpen R n i :=
      (Proj 𝒜).basicOpen_le (coordinateRatioSection R n i j) hx
    have hunit := ((Proj 𝒜).mem_basicOpen (coordinateRatioSection R n i j) x hi).mp hx
    exact ⟨hi, (PresChart.isUnit_germ_ratio_iff R n j i x hi).mp hunit⟩
  · intro x hx
    exact ((Proj 𝒜).mem_basicOpen (coordinateRatioSection R n i j) x hx.1).mpr
      ((PresChart.isUnit_germ_ratio_iff R n j i x hx.1).mpr hx.2)

/-- On a subopen of a standard chart the same ratio cuts out its
intersection with the second standard chart. -/
theorem coordinateRatioSection_restrict_basicOpen (i j : Fin (n + 1))
    {V : (Proj 𝒜).Opens} (hi : V ≤ standardOpen R n i) :
    (Proj 𝒜).basicOpen (rO hi (coordinateRatioSection R n i j)) =
      V ⊓ standardOpen R n j := by
  rw [Scheme.basicOpen_res, coordinateRatioSection_basicOpen, ← inf_assoc,
    inf_eq_left.mpr hi]

/-- The actual section map to a coordinate overlap has both localization
clauses, supplied by quasicoherence on the chosen affine open. -/
theorem coordinateRatioSection_localization
    (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F]
    (i j : Fin (n + 1)) {V : (Proj 𝒜).Opens} (hV : IsAffineOpen V)
    (hi : V ≤ standardOpen R n i) :
    (∀ s : Γ(F, V ⊓ standardOpen R n j),
      ∃ (d : ℕ) (t : Γ(F, V)),
        F.presheaf.map (homOfLE (inf_le_left : V ⊓ standardOpen R n j ≤ V)).op t =
          rO (inf_le_left : V ⊓ standardOpen R n j ≤ V)
            ((rO hi (coordinateRatioSection R n i j)) ^ d) • s) ∧
    (∀ t : Γ(F, V),
      F.presheaf.map (homOfLE (inf_le_left : V ⊓ standardOpen R n j ≤ V)).op t = 0 →
        ∃ d : ℕ, (rO hi (coordinateRatioSection R n i j)) ^ d • t = 0) := by
  let g : Γ(Proj 𝒜, V) := rO hi (coordinateRatioSection R n i j)
  have hloc : BasicOpenLocalization F V g :=
    basicOpenLocalization_of_isQuasicoherent F ⟨V, hV⟩ g
  have htransport (W : (Proj 𝒜).Opens) (hWV : W ≤ V)
      (hW : W = (Proj 𝒜).basicOpen g) :
      (∀ s : Γ(F, W), ∃ (d : ℕ) (t : Γ(F, V)),
        F.presheaf.map (homOfLE hWV).op t = rO hWV (g ^ d) • s) ∧
      (∀ t : Γ(F, V), F.presheaf.map (homOfLE hWV).op t = 0 →
        ∃ d : ℕ, g ^ d • t = 0) := by
    subst W
    exact hloc
  exact htransport (V ⊓ standardOpen R n j) inf_le_left
    (coordinateRatioSection_restrict_basicOpen R n i j hi).symm

end AlgebraicGeometry.ProjSpace
