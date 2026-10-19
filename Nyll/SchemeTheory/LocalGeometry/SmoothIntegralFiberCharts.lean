/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ConnectedComplement
import Nyll.SchemeTheory.LocalGeometry.SmoothRegularStalks
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Maps.Basic

/-!
# Integral affine charts with integral closed fibre

A smooth scheme over a regular local ring has, around every point of
its closed fibre, an affine open whose source and closed fibre are both
integral. The two integral neighbourhoods are constructed simultaneously.

Regularity supplies domain stalks on the source and on the residue-field
fibre. Locally Noetherian domain stalks have irreducible open
neighbourhoods. The closed fibre has the induced topology, so its chosen
neighbourhood lifts to an open of the source, which can then be shrunk
to an affine open. Reducedness turns both irreducible restrictions into
integral schemes.

This is the geometric chart reduction needed before the prime-special-
fibre normalization calculation in Stacks Project 58.30.2 and 58.30.3.
It assumes neither an integral source nor an integral closed fibre.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

private theorem exists_integral_affineOpen_of_closedImmersion
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsReduced X] [IsReduced Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)
    [IsDomain (X.presheaf.stalk (i z))] [IsDomain (Z.presheaf.stalk z)] :
    ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      IsIntegral U ∧ IsIntegral (i ⁻¹ᵁ U) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨V, hV, hizV, hVirr⟩ :=
    Scheme.exists_isIrreducible_open_of_isDomain_stalk (i z)
  obtain ⟨W, hW, hzW, hWirr⟩ :=
    Scheme.exists_isIrreducible_open_of_isDomain_stalk z
  obtain ⟨T, hT, hTW⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp hW
  let O : X.Opens := ⟨V ∩ T, hV.inter hT⟩
  have hizO : i z ∈ O := by
    refine ⟨hizV, ?_⟩
    change z ∈ i ⁻¹' T
    rw [hTW]
    exact hzW
  obtain ⟨U, hU, hizU, hUO⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := i z) (U := O) hizO
  have hUirr : IsIrreducible (U : Set X) :=
    ⟨⟨i z, hizU⟩, hVirr.2.open_subset U.isOpen (fun _ hx ↦ (hUO hx).1)⟩
  have : IrreducibleSpace U := Subtype.irreducibleSpace hUirr
  have hIntegralU : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced U
  have hpreW : (i ⁻¹ᵁ U : Set Z) ⊆ W := by
    intro x hx
    rw [← hTW]
    exact (hUO hx).2
  have hpreIrr : IsIrreducible (i ⁻¹ᵁ U : Set Z) :=
    ⟨⟨z, hizU⟩, hWirr.2.open_subset (i ⁻¹ᵁ U).isOpen hpreW⟩
  have : IrreducibleSpace (i ⁻¹ᵁ U) := Subtype.irreducibleSpace hpreIrr
  exact ⟨U, hU, hizU, hIntegralU,
    isIntegral_of_irreducibleSpace_of_isReduced (i ⁻¹ᵁ U)⟩

/-- Every closed-fibre point of a smooth scheme over a regular local
ring has an affine neighbourhood on which both the source and the
actual closed fibre are integral. -/
theorem Smooth.exists_isAffineOpen_integral_closedFiber
    {B : Type u} [CommRing B] [IsLocalRing B] [IsRegularRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [Smooth f] :
    let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let Z := pullback f s
    let i : Z ⟶ X := pullback.fst f s
    ∀ z : Z, ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      IsIntegral U ∧ IsIntegral (i ⁻¹ᵁ U) := by
  intro s Z i z
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsClosedImmersion s :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  let g : Z ⟶ Spec (.of (IsLocalRing.ResidueField B)) := pullback.snd f s
  have hdomX (x : X) : IsDomain (X.presheaf.stalk x) := by
    have : IsRegularLocalRing (X.presheaf.stalk x) :=
      Smooth.isRegularLocalRing_stalk_over_spec f x
    exact IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hdomZ (x : Z) : IsDomain (Z.presheaf.stalk x) := by
    have : IsRegularLocalRing (Z.presheaf.stalk x) :=
      Smooth.isRegularLocalRing_stalk_over_spec g x
    exact IsRegularLocalRing.isDomain (Z.presheaf.stalk x)
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have : IsDomain (X.presheaf.stalk x) := hdomX x
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have (x : Z) : _root_.IsReduced (Z.presheaf.stalk x) := by
    have : IsDomain (Z.presheaf.stalk x) := hdomZ x
    infer_instance
  have : IsReduced Z := isReduced_of_isReduced_stalk Z
  have : IsDomain (X.presheaf.stalk (i z)) := hdomX (i z)
  have : IsDomain (Z.presheaf.stalk z) := hdomZ z
  exact exists_integral_affineOpen_of_closedImmersion i z

end AlgebraicGeometry
