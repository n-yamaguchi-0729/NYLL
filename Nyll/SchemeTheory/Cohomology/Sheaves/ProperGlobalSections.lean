/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafH0
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteProper
import Nyll.SchemeTheory.Morphisms.AppTopPullbackMapEqAppTopPullbackFst
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite actual global sections over a proper morphism

The existing proper Čech finiteness theorem is applied to the original
section presheaf of a native quasicoherent finite-type sheaf. An actual
finite ordered affine cover is obtained from compactness. The explicit
native global-section comparison then transports finiteness back to the
original sections with their structural base-ring action.

No finite cover, global generators, cohomology comparison, or finite
generation of the original global sections is supplied as an input.
-/

noncomputable section

universe u

open CategoryTheory
open AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.Modules

/-- A native quasicoherent finite-type sheaf over a proper morphism to
a Noetherian affine base has a finite module of actual global sections. -/
theorem moduleFinite_globalSections_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R (sectionModuleOverBase f M ⊤) := by
  have hCompact : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let K : X.OrderedAffineCover :=
    exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper.SolML0C.cover X
  have hC : (toOModulePresheaf f M).CechFinite K :=
    OModulePresheaf.cechFinite_of_isProper (toOModulePresheaf f M)
      (toOModulePresheaf_isCoherent f M) (toOModulePresheaf_isQuasicoherent f M) K
  have hFinite : Module.Finite R ((toOModulePresheaf f M).H0 K) := hC.1
  exact Module.Finite.of_surjective (globalSectionsCechH0Equiv f M K).symm.toLinearMap
    (globalSectionsCechH0Equiv f M K).symm.surjective

end AlgebraicGeometry.Scheme.Modules
