/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitCharts
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Local sections of the projective-class map

The functions cutting out the standard projective coordinate charts cover
the entire norm open. On each corresponding principal localization, the
normalized unit constructs a section of the map from the affine unit open.
Consequently that map is surjective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization TopologicalSpace
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ProjectiveUnitCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (b : Basis (Fin (n + 1)) R A)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The chart functions cover the whole affine projective norm open. -/
theorem iSup_basicOpen_chartElement :
    (⨆ j, PrimeSpectrum.basicOpen (chartElement b j)) = ⊤ := by
  have hc := (ProjectiveUnitOpen.projectiveι b).iSup_preimage_eq_top
    (Proj.iSup_basicOpen_eq_top 𝒜 (fun j : Fin (n + 1) => MvPolynomial.X j)
      (ProjSpace.irrelevant_le_span_X R n))
  have he (j : Fin (n + 1)) :
      ProjectiveUnitOpen.projectiveι b ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) =
        PrimeSpectrum.basicOpen (chartElement b j) :=
    Proj.awayι_preimage_basicOpen 𝒜 (ProjectiveUnitOpen.norm_mem b) (Nat.succ_pos n)
      (ProjSpace.X_mem_one R n j) one_pos
  simp only [he] at hc
  exact hc

/-- The finite family of chart functions generates the unit ideal. -/
theorem span_chartElement : Ideal.span (Set.range (chartElement b)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (iSup_basicOpen_chartElement b)

/-- The coordinate ring of a principal open in the standard cover. -/
abbrev LocalChart (j : Fin (n + 1)) := Localization.Away (chartElement b j)

/-- The canonical normalized unit gives a local section of the
projective-class map on each principal chart. -/
def localSectionMap (j : Fin (n + 1)) :
    Spec (CommRingCat.of (LocalChart b j)) ⟶ UnitNormPolynomial.unitOpen b :=
  Spec.map (CommRingCat.ofHom (UnitNormPolynomial.unitToHom b
    (normalizedUnit b
      (Algebra.algHom R (ProjectiveUnitOpen.CoordinateRing b) (LocalChart b j)) j
      (IsLocalization.Away.algebraMap_isUnit (S := LocalChart b j) (chartElement b j)))).toRingHom)

/-- Composing the normalized local section with the projective-class map
recovers the actual principal-open inclusion. -/
theorem localSectionMap_quotientMap (j : Fin (n + 1)) :
    localSectionMap b j ≫ ProjectiveUnitOpen.quotientMap b =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ProjectiveUnitOpen.CoordinateRing b) (LocalChart b j))) := by
  unfold localSectionMap ProjectiveUnitOpen.quotientMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : ProjectiveUnitOpen.CoordinateRing b →+* LocalChart b j =>
      Spec.map (CommRingCat.ofHom f))
    (projectivePoint_normalizedUnit b
      (Algebra.algHom R (ProjectiveUnitOpen.CoordinateRing b) (LocalChart b j)) j
      (IsLocalization.Away.algebraMap_isUnit (S := LocalChart b j) (chartElement b j)))

/-- Every point of the projective norm open is in the image of an actual
unit: the map has sections on a concrete finite Zariski cover. -/
theorem surjective_quotientMap : Surjective (ProjectiveUnitOpen.quotientMap b) := by
  constructor
  intro x
  have hx : x ∈ ⨆ j, PrimeSpectrum.basicOpen (chartElement b j) := by
    rw [iSup_basicOpen_chartElement]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  have hrange : x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (ProjectiveUnitOpen.CoordinateRing b) (LocalChart b j))) := by
    rw [PrimeSpectrum.localization_away_comap_range (LocalChart b j) (chartElement b j)]
    exact hj
  obtain ⟨y, hy⟩ := hrange
  refine ⟨localSectionMap b j y, ?_⟩
  have he := congrArg
    (fun f : Spec (CommRingCat.of (LocalChart b j)) ⟶ ProjectiveUnitOpen.carrier b => f y)
    (localSectionMap_quotientMap b j)
  exact he.trans hy

end SchemeTheory.Affine.ProjectiveUnitCharts
