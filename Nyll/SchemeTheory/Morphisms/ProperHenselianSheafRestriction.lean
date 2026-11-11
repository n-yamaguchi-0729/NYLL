/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.SchemeTheory.Morphisms.ProperHenselianClosedRestriction
public import Nyll.SchemeTheory.Topology.SpectralClosedSheafRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheaf sections on a proper henselian closed fiber

Every sheaf of sets on the underlying space of an arbitrary proper scheme
over a henselian local ring has the same global sections on its actual
closed fiber. The map is the unit of the topological inverse-image
adjunction. Connected point-closure intersections come from proper
henselian geometry, and the spectral restriction theorem applies directly.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The actual closed-fiber restriction on global sections is bijective
for every topological sheaf on a proper scheme over a henselian local ring. -/
theorem sheaf_closedFiber_restriction_bijective
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.ofHom
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(TopCat.of (f ⁻¹' {IsLocalRing.closedPoint R}), TopCat.of X)))).unit.app F).hom.app
        (op (⊤ : Opens X))) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : SpectralSpace X := {}
  exact SchemeTheory.sheaf_globalSections_restriction_bijective
    ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage f.continuous)
    (isConnected_closedFiber_inter_closure f) F

end AlgebraicGeometry
