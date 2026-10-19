/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperHomotopyExact
import Nyll.EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-!
# Geometric-fibre surjectivity over a strictly henselian local base

For a proper flat finitely presented family with geometrically reduced,
geometrically connected fibres over a strictly henselian local ring, the
actual inclusion of every geometric fibre induces a surjection on
fundamental groups. The proper homotopy sequence identifies its image with
the kernel of the map to the base, whose fundamental group is trivial.

This is the local surjectivity argument in Stacks Project, Lemma 58.30.1
(tag `0C0P`). The construction of specialization between two different
geometric fibres also requires the proper closed-fibre equivalence; it is
not asserted here. In particular, neither an inverse closed-fibre map nor
an unproved geometric comparison is an input to these theorems.
-/

noncomputable section

open CategoryTheory
open AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Every geometric-fibre inclusion in a proper flat finitely presented
family with geometrically reduced connected fibres over a strictly
henselian local ring induces a surjection on fundamental groups. -/
@[stacks 0C0P "Geometric-fibre surjectivity over a strictly henselian base."]
theorem fundamentalGroupHom_proper_geometricFiber_surjective_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f] [GeometricallyConnected f]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback s f) :
    Function.Surjective (fundamentalGroupHom (Limits.pullback.snd s f) xi) := by
  have hR : ConnectedSpace (Spec (.of R)) := by
    have : PreconnectedSpace (Spec (.of R)) := by
      refine ⟨?_⟩
      intro U V hU hV hcover hneU hneV
      rcases hcover (Set.mem_univ (IsLocalRing.closedPoint R)) with h | h
      · obtain ⟨v, _, hv⟩ := hneV
        exact ⟨v, trivial, (IsLocalRing.specializes_closedPoint v).mem_open hU h, hv⟩
      · obtain ⟨v, _, hv⟩ := hneU
        exact ⟨v, trivial, hv, (IsLocalRing.specializes_closedPoint v).mem_open hV h⟩
    exact ⟨⟨IsLocalRing.closedPoint R⟩⟩
  have hbase : Subsingleton π₁ᵉᵗ((xi ≫ Limits.pullback.snd s f) ≫ f) :=
    EtaleFundamentalGroups.StrictHenselian.subsingleton_fundamentalGroup_of_strictHenselian
      R ((xi ≫ Limits.pullback.snd s f) ≫ f)
  have hker := fundamentalGroupHom_proper_geometricFiber_ker_eq_range f s xi
  intro a
  have ha : a ∈ (fundamentalGroupHom f (xi ≫ Limits.pullback.snd s f)).toMonoidHom.ker := by
    change fundamentalGroupHom f (xi ≫ Limits.pullback.snd s f) a = 1
    exact hbase.elim _ _
  rw [hker] at ha
  exact ha

/-- Smooth proper families with geometrically connected fibres over a
strictly henselian local ring have surjective geometric-fibre maps on
fundamental groups, in every residue characteristic. -/
theorem fundamentalGroupHom_smoothProper_geometricFiber_surjective_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback s f) :
    Function.Surjective (fundamentalGroupHom (Limits.pullback.snd s f) xi) := by
  have : GeometricallyReduced f :=
    REDsol.geometricallyReduced_of_smooth f
  exact fundamentalGroupHom_proper_geometricFiber_surjective_of_strictHenselian R f s xi

end AlgebraicGeometry.FiniteEtale
