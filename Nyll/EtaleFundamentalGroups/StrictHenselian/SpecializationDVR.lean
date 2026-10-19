/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVR
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianEmbedding
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.LocalRingValuationSubringDVRDominates
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Strict henselian DVR diagrams for geometric points of a noetherian local ring

For a homomorphism from a noetherian local ring `A` to an algebraically
closed field `Ω` whose kernel is not the maximal ideal, first pass to the
actual quotient by its kernel. Construct a DVR dominating this noetherian
local domain, then take its actual geometric étale stalk. The latter is a
DVR, is henselian, and has separably closed residue field. Its algebraicity
over the original DVR extends the generic embedding to the specified `Ω`.

The result retains a local map from the original, possibly nonreduced `A`,
a map from the actual DVR fraction field to `Ω`, and the native compatible
residue-field map. For a closed geometric point, the geometric stalk of
`Ω⟦X⟧` gives a strict henselian DVR after extending the generic field. Combining
the constructions supplies the ring diagram for every geometric point of
a noetherian local ring. The proper-fibre comparison in Lemma 58.16.4 is a
separate assertion.

Reference: https://stacks.math.columbia.edu/tag/0C0N.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

private theorem exists_strictlyHenselianDVRFactor_of_injective
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (φ : A →+* Ω) (hφ : Function.Injective φ) (hA : ¬ IsField A) :
    ∃ (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (IsLocalRing.ResidueField D) ∧
      ∃ (f : A →+* D) (g : D →+* Ω),
        IsLocalHom f ∧ Function.Injective g ∧ g.comp f = φ := by
  let K : Type u := FractionRing A
  let i : K →+* Ω := IsFractionRing.lift hφ
  obtain ⟨V, hV, hmem, hcenter⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hA K
  have : IsDiscreteValuationRing V := hV
  let j : A →+* V := (algebraMap A K).codRestrict V.toSubring hmem
  have hj : IsLocalHom j := by
    apply ((IsLocalRing.local_hom_TFAE j).out 5 1).mp
    apply Ideal.ext
    intro a
    change j a ∈ IsLocalRing.maximalIdeal V ↔ a ∈ IsLocalRing.maximalIdeal A
    exact (ValuationSubring.coe_mem_nonunits_iff (a := j a)).symm.trans
      (hcenter a).symm
  let k : Type u := AlgebraicClosure (IsLocalRing.ResidueField V)
  let δ : V →+* k :=
    (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  have : IsLocalHom δ := RingHom.isLocalHom_comp _ _
  let D : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom δ))
  have hDomain : IsDomain D := inferInstance
  have hDVR : IsDiscreteValuationRing D := geometricStalk_isDiscreteValuationRing δ
  have hHenselian : HenselianLocalRing D := inferInstance
  have hResidue : IsSepClosed (IsLocalRing.ResidueField D) := inferInstance
  let : Algebra V D := (geometricStalkStructureMap δ).toAlgebra
  let ι : V →+* Ω := i.comp (algebraMap V K)
  let : Algebra V Ω := ι.toAlgebra
  have hι : Function.Injective ι :=
    i.injective.comp (IsFractionRing.injective V K)
  have : Module.IsTorsionFree V Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Module.IsTorsionFree V D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (geometricStalkStructureMap_injective_of_isDomain δ)
  have : Algebra.IsAlgebraic V D := geometricStalk_isAlgebraic δ
  let e : D →ₐ[V] Ω := IsAlgClosed.lift
  let : Algebra D Ω := e.toRingHom.toAlgebra
  have : IsScalarTower V D Ω := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have he : Function.Injective e.toRingHom :=
    Algebra.IsAlgebraic.injective_tower_top D hι
  let f : A →+* D := (geometricStalkStructureMap δ).comp j
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  refine ⟨D, hDomain, hHenselian, hDVR, hResidue, f, e.toRingHom, hf, he, ?_⟩
  apply RingHom.ext
  intro a
  calc
    e (geometricStalkStructureMap δ (j a)) = ι (j a) := e.commutes (j a)
    _ = φ a := IsFractionRing.lift_algebraMap hφ a

/-- A nonclosed geometric point of a noetherian local ring is realized by a
local map to an actual strictly henselian DVR. Its actual fraction field
embeds in the prescribed geometric field, with the original ring map and
the residue-field square preserved. The original ring may have nilpotents. -/
theorem exists_strictlyHenselianDVRFactor_of_ker_ne_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (φ : A →+* Ω) (hφ : RingHom.ker φ ≠ IsLocalRing.maximalIdeal A) :
    ∃ (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (IsLocalRing.ResidueField D) ∧
      ∃ (f : A →+* D) (g : FractionRing D →+* Ω)
        (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D),
        IsLocalHom f ∧ g.comp ((algebraMap D (FractionRing D)).comp f) = φ ∧
        r.comp (IsLocalRing.residue A) = (IsLocalRing.residue D).comp f := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let B : Type u := A ⧸ RingHom.ker φ
  let q : A →+* B := Ideal.Quotient.mk (RingHom.ker φ)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalRing B := IsLocalRing.of_surjective' q hq
  have : IsLocalHom q := IsLocalHom.of_surjective q hq
  have hB : ¬ IsField B := by
    intro hField
    exact hφ (IsLocalRing.eq_maximalIdeal
      (Ideal.Quotient.maximal_of_isField (RingHom.ker φ) hField))
  obtain ⟨D, hDomain, hHenselian, hDVR, hResidue, fB, e, hfB, he, hcomp⟩ :=
    exists_strictlyHenselianDVRFactor_of_injective
      (RingHom.kerLift φ) (RingHom.kerLift_injective φ) hB
  let f : A →+* D := fB.comp q
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  let g : FractionRing D →+* Ω := IsFractionRing.lift he
  let r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D :=
    IsLocalRing.ResidueField.map f
  refine ⟨D, hDomain, hHenselian, hDVR, hResidue, f, g, r, hf, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    calc
      g (algebraMap D (FractionRing D) (f a)) = e (f a) :=
        IsFractionRing.lift_algebraMap he (f a)
      _ = φ a := (RingHom.congr_fun hcomp (q a)).trans (RingHom.kerLift_mk φ a)
  · exact IsLocalRing.ResidueField.map_comp_residue f

private theorem exists_strictlyHenselianDVRDiagram_of_ker_eq_maximalIdeal
    {A Ω : Type u} [CommRing A] [IsLocalRing A] [Field Ω] [IsAlgClosed Ω]
    (φ : A →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal A) :
    ∃ (Ω' : Type u) (_ : Field Ω') (_ : IsAlgClosed Ω') (ι : Ω →+* Ω')
      (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (IsLocalRing.ResidueField D) ∧
      ∃ (f : A →+* D) (g : FractionRing D →+* Ω')
        (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D),
        IsLocalHom f ∧ g.comp ((algebraMap D (FractionRing D)).comp f) = ι.comp φ ∧
        r.comp (IsLocalRing.residue A) = (IsLocalRing.residue D).comp f := by
  have : IsLocalHom φ := by
    apply ((IsLocalRing.local_hom_TFAE φ).out 5 1).mp
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact hφ
  let R : Type u := PowerSeries Ω
  let δ : R →+* Ω := PowerSeries.constantCoeff
  have : IsLocalHom δ :=
    IsLocalHom.of_surjective δ PowerSeries.constantCoeff_surj
  let D : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom δ))
  have hDomain : IsDomain D := inferInstance
  have hDVR : IsDiscreteValuationRing D := geometricStalk_isDiscreteValuationRing δ
  have hHenselian : HenselianLocalRing D := inferInstance
  have hResidue : IsSepClosed (IsLocalRing.ResidueField D) := inferInstance
  let j : Ω →+* D := (geometricStalkStructureMap δ).comp (algebraMap Ω R)
  have : IsLocalHom j := RingHom.isLocalHom_comp _ _
  let f : A →+* D := j.comp φ
  have hf : IsLocalHom f := RingHom.isLocalHom_comp _ _
  let Ω' : Type u := AlgebraicClosure (FractionRing D)
  let g : FractionRing D →+* Ω' := algebraMap (FractionRing D) Ω'
  let ι : Ω →+* Ω' := g.comp ((algebraMap D (FractionRing D)).comp j)
  let r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D :=
    IsLocalRing.ResidueField.map f
  refine ⟨Ω', inferInstance, inferInstance, ι, D, hDomain, hHenselian,
    hDVR, hResidue, f, g, r, hf, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    rfl
  · exact IsLocalRing.ResidueField.map_comp_residue f

/-- The complete local-ring diagram needed for the DVR reduction: every
geometric point of a noetherian local ring admits a strict henselian DVR
realization after an algebraically closed extension of its geometric field.
The generic triangle and residue square use the original ring map.

The DVR and its properties are constructed in both cases, including when
the geometric point lies at the closed point of the original local ring. -/
theorem exists_strictlyHenselianDVRDiagram
    {A Ω : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω) :
    ∃ (Ω' : Type u) (_ : Field Ω') (_ : IsAlgClosed Ω') (ι : Ω →+* Ω')
      (D : CommRingCat.{u}) (_ : IsDomain D) (_ : HenselianLocalRing D),
      IsDiscreteValuationRing D ∧ IsSepClosed (IsLocalRing.ResidueField D) ∧
      ∃ (f : A →+* D) (g : FractionRing D →+* Ω')
        (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField D),
        IsLocalHom f ∧ g.comp ((algebraMap D (FractionRing D)).comp f) = ι.comp φ ∧
        r.comp (IsLocalRing.residue A) = (IsLocalRing.residue D).comp f := by
  by_cases hφ : RingHom.ker φ = IsLocalRing.maximalIdeal A
  · exact exists_strictlyHenselianDVRDiagram_of_ker_eq_maximalIdeal φ hφ
  · obtain ⟨D, hDomain, hHenselian, hDVR, hResidue, f, g, r, hf, hgeneric, hresidue⟩ :=
      exists_strictlyHenselianDVRFactor_of_ker_ne_maximalIdeal φ hφ
    refine ⟨Ω, inferInstance, inferInstance, RingHom.id Ω, D, hDomain, hHenselian,
      hDVR, hResidue, f, g, r, hf, ?_, hresidue⟩
    simpa only [RingHom.id_comp] using hgeneric

end EtaleFundamentalGroups.StrictHenselian
