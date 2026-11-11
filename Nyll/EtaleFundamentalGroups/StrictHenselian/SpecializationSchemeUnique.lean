/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationHomExt
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeComposition
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Uniqueness of the strict local specialization diagram

The specified geometric lift determines exactly one map between the two
actual strict local models with its prescribed evaluation and ordinary
stalk structure map. The constructed map also commutes with the morphisms
to the original scheme.

Existence uses the original strict-local specialization construction.
Uniqueness is proved from the actual neighborhood lifts across the two
different ordinary stalk rings. This does not assert the separate
proper closed-fiber equivalence on finite étale covers.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A chosen geometric specialization determines a unique strict local
map with its original evaluation, ordinary stalk map, and scheme triangle. -/
theorem existsUnique_localGeometricStalk_map_of_specializationLift
    {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [IsSepClosed Ωs]
    [Field Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃! a : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)),
      a ≫ geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) = CommRingCat.ofHom ψ ∧
      a.hom.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo t).hom).comp
          (S.presheaf.stalkSpecializes h).hom ∧
      Spec.map a ≫ localGeometricStalkToScheme s = localGeometricStalkToScheme t := by
  obtain ⟨a, hevaluation, hbase, htriangle⟩ :=
    exists_localGeometricStalk_map_of_specializationLift s t h ψ hψ
  refine ⟨a, ⟨hevaluation, hbase, htriangle⟩, ?_⟩
  intro b hb
  apply geometricStalk_hom_ext_of_structure_evaluation
    (Scheme.stalkClosedPointTo s).hom
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) b a
  · exact hb.2.1.trans hbase.symm
  · exact hb.1.trans hevaluation.symm

end EtaleFundamentalGroups.StrictHenselian
