/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalCoordinateAlgebra
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Actual affine coordinates of an integral group point

An integral power-series point reducing to the unit factors through every
chosen affine identity neighbourhood. Its actual generic coordinates therefore
lift to integral series, whose reduction is the unit augmentation in all degrees.
This is the converse to constructing integral points from generator bounds.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.IntegralGroupPowerSeries

variable {K O F k : Type u} [Field K] [CommRing O] [CommRing F] [CommRing k]
  [IsLocalRing O] [IsLocalRing k]
  [Algebra K O] [Algebra K F] [Algebra K k]
  {G : Over (Spec (.of K))} [GrpObj G]

private theorem unit_left {T : Scheme.{u}} (t : T ⟶ Spec (.of K)) :
    (1 : Over.mk t ⟶ G).left = t ≫ (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left := by
  have h := MonObj.comp_one (M := G)
    (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 (Spec (.of K))))
  exact (congrArg (fun a : Over.mk t ⟶ G => a.left) h).symm

/-- Reduction to the actual group unit puts the entire integral local
spectrum in every open identity neighbourhood. -/
theorem integral_point_preimage_identity_open
    (ρ : O →ₐ[K] k) [IsLocalHom ρ.toRingHom]
    (p : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries O)))) ⟶ G)
    (hred : Spec.map (CommRingCat.ofHom (PowerSeries.map ρ.toRingHom)) ≫ p.left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries k)))) ⟶ G).left)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    p.left ⁻¹ᵁ V = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  let z : Spec (.of (PowerSeries k)) := IsLocalRing.closedPoint (PowerSeries k)
  have hc : Spec.map (CommRingCat.ofHom (PowerSeries.map ρ.toRingHom)) z =
      IsLocalRing.closedPoint (PowerSeries O) :=
    IsLocalRing.comap_closedPoint (PowerSeries.map ρ.toRingHom)
  have h := congrArg (fun f : Spec (.of (PowerSeries k)) ⟶ G.left => f z) hred
  change p.left (Spec.map (CommRingCat.ofHom (PowerSeries.map ρ.toRingHom)) z) = _ at h
  rw [hc] at h
  rw [h, unit_left]
  exact hunit ⟨_, rfl⟩

/-- Generic affine coordinates of an integral point reducing to the unit
are actual integral series with the full prescribed residue, without a
finite-generation assumption or a supplied integral chart factorization. -/
theorem exists_coordinate_lift_of_integral_point
    (j : O →ₐ[K] F) (ρ : O →ₐ[K] k) [IsLocalHom ρ.toRingHom]
    (p : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries O)))) ⟶ G)
    (hred : Spec.map (CommRingCat.ofHom (PowerSeries.map ρ.toRingHom)) ≫ p.left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries k)))) ⟶ G).left)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (φ : Γ(G.left, V) →+* PowerSeries F)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom (PowerSeries.map j.toRingHom)) ≫ p.left) :
    ∃ ψ : Γ(G.left, V) →+* PowerSeries O,
      (PowerSeries.map j.toRingHom).comp ψ = φ ∧
      (PowerSeries.map ρ.toRingHom).comp ψ =
        (algebraMap K (PowerSeries k)).comp
          (AffineLineGroupFormalDifference.identityCoordinates V hV hunit) := by
  let l : Spec (.of (PowerSeries O)) ⟶ V := IsOpenImmersion.lift V.ι p.left (by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ p.left ⁻¹ᵁ V := by
      rw [integral_point_preimage_identity_open ρ p hred V hunit]
      trivial
    exact ⟨⟨p.left z, hz⟩, rfl⟩)
  have hl : l ≫ V.ι = p.left := IsOpenImmersion.lift_fac _ _ _
  let ψ : Γ(G.left, V) →+* PowerSeries O :=
    (Spec.preimage (l ≫ hV.isoSpec.hom)).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec = p.left := by
    change Spec.map (Spec.preimage (l ≫ hV.isoSpec.hom)) ≫ hV.fromSpec = _
    rw [Spec.map_preimage, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hl]
  refine ⟨ψ, ?_, ?_⟩
  · have h : CommRingCat.ofHom ((PowerSeries.map j.toRingHom).comp ψ) =
        CommRingCat.ofHom φ := by
      apply Spec.map_injective
      apply (cancel_mono hV.fromSpec).mp
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψ]
      exact hφ.symm
    exact congrArg (fun f : CommRingCat.of Γ(G.left, V) ⟶
      CommRingCat.of (PowerSeries F) => f.hom) h
  · have h : CommRingCat.ofHom ((PowerSeries.map ρ.toRingHom).comp ψ) =
        CommRingCat.ofHom ((algebraMap K (PowerSeries k)).comp
          (AffineLineGroupFormalDifference.identityCoordinates V hV hunit)) := by
      apply Spec.map_injective
      apply (cancel_mono hV.fromSpec).mp
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        Category.assoc, Category.assoc, hψ,
        AffineLineGroupFormalDifference.identityCoordinates_spec, hred, unit_left]
    exact congrArg (fun f : CommRingCat.of Γ(G.left, V) ⟶
      CommRingCat.of (PowerSeries k) => f.hom) h

end AlgebraicGeometry.IntegralGroupPowerSeries
