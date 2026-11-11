/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationDiagram
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Connected.Clopen

/-!
# Paths on the original total space over an arbitrary base

The original specializing points lift to the actual local geometric-stalk
family. Properness and geometrically connected fibers make that family's
total space connected. A path there induces a path on the original total
space through its actual pullback projection.

This constructs a path without a Noetherian hypothesis. It does not assert
that the generic-fiber group map lifts through the special-fiber group map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

private theorem connectedSpace_of_proper_geometricallyConnected
    {X S : Scheme.{u}} [ConnectedSpace S] (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] : ConnectedSpace X := by
  have hq : Topology.IsCoinducing f :=
    (f.isClosedMap.isQuotientMap f.continuous f.surjective).isCoinducing
  have h := Topology.IsCoinducing.isConnected_preimage_of_isClosed
    f.isConnected_preimage_singleton hq isClosed_univ isConnected_univ
  exact connectedSpace_iff_univ.mpr (by simpa only [Set.preimage_univ] using h)

/-- A specialization of the two base points supplies a path between the
original total-space geometric fiber functors. The construction uses the
actual strict-local pullback and retains the original fiber projections. -/
theorem nonempty_totalSpacePath_of_specializes
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    {ks kt : Type u} [Field ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    {Ωη Ωs : Type u} [Field Ωη] [IsSepClosed Ωη] [Field Ωs] [IsSepClosed Ωs]
    (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f) :
    Nonempty (FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
      FiniteEtale.fiber (xs ≫ pullback.snd s f)) := by
  obtain ⟨ψ, _, hψ⟩ := exists_localGeometricStalk_specifiedSpecializationLift s t h
  let H : CommRingCat.{u} := geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))
  have : PreconnectedSpace (Spec H) :=
    preconnectedSpace_of_forall_constant fun k hk x y =>
      ((specializes_closedPoint x).map hk).eq.trans
        ((specializes_closedPoint y).map hk).eq.symm
  have : ConnectedSpace (Spec H) := ⟨⟨closedPoint H⟩⟩
  let p : Spec H ⟶ S := localGeometricStalkToScheme s
  let l : pullback p f ⟶ X := pullback.snd p f
  have : ConnectedSpace (pullback p f : Scheme.{u}) :=
    connectedSpace_of_proper_geometricallyConnected (pullback.fst p f)
  let qη : pullback t f ⟶ pullback p f := familySpecializationGenericMap f s t ψ hψ
  let qs : pullback s f ⟶ pullback p f := familySpecializationClosedMap f s
  obtain ⟨τ⟩ := FiniteEtale.nonempty_fiber_iso (xη ≫ qη) (xs ≫ qs)
  have hη : (xη ≫ qη) ≫ l = xη ≫ pullback.snd t f := by
    rw [Category.assoc]
    exact congrArg (fun a => xη ≫ a) (familySpecializationGenericMap_snd f s t ψ hψ)
  have hs : (xs ≫ qs) ≫ l = xs ≫ pullback.snd s f := by
    rw [Category.assoc]
    exact congrArg (fun a => xs ≫ a) (familySpecializationClosedMap_snd f s)
  exact ⟨(eqToIso (congrArg FiniteEtale.fiber hη)).symm ≪≫
    (FiniteEtale.pullbackFiberIso l (xη ≫ qη)).symm ≪≫
    Functor.isoWhiskerLeft (FiniteEtale.pullback l) τ ≪≫
    FiniteEtale.pullbackFiberIso l (xs ≫ qs) ≪≫
    eqToIso (congrArg FiniteEtale.fiber hs)⟩

end EtaleFundamentalGroups.StrictHenselian
