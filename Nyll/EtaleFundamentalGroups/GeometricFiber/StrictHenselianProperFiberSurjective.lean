/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperHomotopyExact
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

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

@[expose] public section

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

/-- Geometric-fibre surjectivity with the family morphism first in the
original pullback, as used by multiplication and specialization covers. -/
theorem fundamentalGroupHom_smoothProper_fiberFst_surjective_of_strictHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback f s) :
    Function.Surjective (fundamentalGroupHom (Limits.pullback.fst f s) xi) := by
  have : ConnectedSpace (show Scheme.{u} from Limits.pullback f s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.snd f s)
  have : ConnectedSpace (show Scheme.{u} from Limits.pullback s f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.fst s f)
  let e := Limits.pullbackSymmetry f s
  let T : FiniteEtale (Limits.pullback s f) ≌ FiniteEtale (Limits.pullback f s) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have : (pullback e.hom).IsEquivalence := T.isEquivalence_functor
  have he := (fundamentalGroupHom_bijective_of_pullback_isEquivalence e.hom xi).2
  have hq := fundamentalGroupHom_smoothProper_geometricFiber_surjective_of_strictHenselian
    R f s (xi ≫ e.hom)
  have hm : Limits.pullback.fst f s = e.hom ≫ Limits.pullback.snd s f :=
    (Limits.pullbackSymmetry_hom_comp_snd f s).symm
  have hpoint : (xi ≫ e.hom) ≫ Limits.pullback.snd s f =
      xi ≫ Limits.pullback.fst f s :=
    (Category.assoc _ _ _).trans (congrArg (xi ≫ ·) hm.symm)
  let transport : π₁ᵉᵗ((xi ≫ e.hom) ≫ Limits.pullback.snd s f) ≃
      π₁ᵉᵗ(xi ≫ Limits.pullback.fst f s) :=
    Equiv.cast (congrArg (fun point => π₁ᵉᵗ(point)) hpoint)
  have transport_apply {p q : Spec (.of Ω) ⟶ X} (h : p = q) (a : π₁ᵉᵗ(p)) :
      Equiv.cast (congrArg (fun point => π₁ᵉᵗ(point)) h) a = h ▸ a := by
    cases h
    rfl
  intro a
  obtain ⟨b, rfl⟩ := transport.surjective a
  obtain ⟨c, rfl⟩ := hq b
  obtain ⟨γ, rfl⟩ := he c
  refine ⟨γ, ?_⟩
  change fundamentalGroupHom (Limits.pullback.fst f s) xi γ =
    Equiv.cast (congrArg (fun point => π₁ᵉᵗ(point)) hpoint)
      (fundamentalGroupHom (Limits.pullback.snd s f) (xi ≫ e.hom)
        (fundamentalGroupHom e.hom xi γ))
  rw [transport_apply]
  exact (fundamentalGroupHom_comp_of_eq e.hom (Limits.pullback.snd s f)
    (Limits.pullback.fst f s) hm xi hpoint γ).symm

end AlgebraicGeometry.FiniteEtale
