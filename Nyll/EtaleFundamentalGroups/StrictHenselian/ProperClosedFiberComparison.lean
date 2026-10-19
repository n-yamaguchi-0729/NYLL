/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperFieldBaseChange
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual closed fiber of the strict local specialization model

The residue field of the constructed strict local ring embeds in the originally
specified geometric field. The evaluation identity proves its triangle over
the original base scheme. Thus the original geometric fiber maps to the
closed fiber of the strict local model by the original field embedding.

We construct its map to the strict local total space and prove the defining
square cartesian. For a proper family, separably closed constant-field
invariance proves that the geometric-fiber map is an equivalence on finite
étale covers. This is the field-comparison part of Stacks 58.16; it does not
assert the separate henselian proper comparison with the total space.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ S)

/-- The actual residue-field point of the strict local model over the base. -/
def localGeometricResiduePoint :
    Spec (CommRingCat.of (ResidueField (geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))) ) ⟶ S :=
  Spec.map (CommRingCat.ofHom (residue (geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))))) ≫
    localGeometricStalkToScheme s

/-- The residue embedding retains the original geometric point over the base. -/
theorem localGeometricResiduePoint_triangle :
    Spec.map (CommRingCat.ofHom (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))) ≫
        localGeometricResiduePoint s = s := by
  let p := Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)
  have heval : (geometricStalkResidueEmbedding p).comp (residue (geometricStalk p)) =
      (geometricStalkEvaluation p).hom :=
    IsLocalRing.ResidueField.lift_comp_residue (geometricStalkEvaluation p).hom
  change Spec.map (CommRingCat.ofHom (geometricStalkResidueEmbedding p)) ≫
    (Spec.map (CommRingCat.ofHom (residue (geometricStalk p))) ≫
      localGeometricStalkToScheme s) = s
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, heval]
  exact localGeometricStalkToScheme_evaluation s

variable (f : X ⟶ S)

/-- The closed fiber is mapped to the actual strict local total space. -/
def localGeometricClosedFiberInclusion :
    Limits.pullback f (localGeometricResiduePoint s) ⟶
      Limits.pullback f (localGeometricStalkToScheme s) :=
  Limits.pullback.lift (Limits.pullback.fst f (localGeometricResiduePoint s))
    (Limits.pullback.snd f (localGeometricResiduePoint s) ≫
      Spec.map (CommRingCat.ofHom (residue (geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))))))
    (by
      rw [Category.assoc]
      exact Limits.pullback.condition)

/-- This is the closed fiber of the strict local total space, with its
actual residue morphism and actual projections. -/
theorem localGeometricClosedFiberInclusion_isPullback :
    IsPullback (localGeometricClosedFiberInclusion s f)
      (Limits.pullback.snd f (localGeometricResiduePoint s))
      (Limits.pullback.snd f (localGeometricStalkToScheme s))
      (Spec.map (CommRingCat.ofHom (residue (geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))))) := by
  have hsnd : localGeometricClosedFiberInclusion s f ≫
      Limits.pullback.snd f (localGeometricStalkToScheme s) =
        Limits.pullback.snd f (localGeometricResiduePoint s) ≫
          Spec.map (CommRingCat.ofHom (residue (geometricStalk
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))))) :=
    Limits.pullback.lift_snd _ _ _
  have hfst : localGeometricClosedFiberInclusion s f ≫
      Limits.pullback.fst f (localGeometricStalkToScheme s) =
        Limits.pullback.fst f (localGeometricResiduePoint s) :=
    Limits.pullback.lift_fst _ _ _
  apply IsPullback.of_right (p := hsnd)
    (t := IsPullback.of_hasPullback f (localGeometricStalkToScheme s))
  rw [hfst]
  exact IsPullback.of_hasPullback f (localGeometricResiduePoint s)

/-- The original geometric fiber maps to the closed fiber by the actual
residue embedding, retaining the original morphism to the base scheme. -/
def localGeometricClosedFiberMap :
    Limits.pullback f s ⟶ Limits.pullback f (localGeometricResiduePoint s) :=
  AlgebraicGeometry.FiniteEtale.fieldBaseChangeMap f (localGeometricResiduePoint s) s
    (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))
    (localGeometricResiduePoint_triangle s).symm

/-- The field comparison preserves the map to the original total space. -/
theorem localGeometricClosedFiberMap_fst :
    localGeometricClosedFiberMap s f ≫
      Limits.pullback.fst f (localGeometricResiduePoint s) = Limits.pullback.fst f s :=
  AlgebraicGeometry.FiniteEtale.fieldBaseChangeMap_fst f
    (localGeometricResiduePoint s) s _ (localGeometricResiduePoint_triangle s).symm

/-- Properness gives an actual equivalence between covers of the strict
local closed fiber and covers of the original geometric fiber. -/
theorem pullback_localGeometricClosedFiberMap_isEquivalence
    [IsProper f] [IsSepClosed Ω] :
    (AlgebraicGeometry.FiniteEtale.pullback (localGeometricClosedFiberMap s f)).IsEquivalence :=
  AlgebraicGeometry.FiniteEtale.pullback_fieldBaseChangeMap_isEquivalence f
    (localGeometricResiduePoint s) s
    (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))
    (localGeometricResiduePoint_triangle s).symm

end EtaleFundamentalGroups.StrictHenselian
