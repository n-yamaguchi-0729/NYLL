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
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSchemeUnique
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Identity and composition of the strict local specialization diagram

The unique map associated to a prescribed lift is selected once, with its
evaluation, ordinary stalk structure, and triangle over the original scheme.
For three successively specializing geometric points, the composite of
these actual maps is the map associated to the composite field-valued lift.
Choosing the original evaluation gives the identity.

The final pointing field need not be separably closed. The intermediate
field is separably closed because it also supplies the source of the
second specialization construction. These are laws for the strict local
models; the proper-fiber fundamental-group comparison is separate.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

section Construction

variable {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [IsSepClosed Ωs] [Field Ωt]
  (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
  (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
  (ψ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
  (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom)

/-- The uniquely determined map of the original strict local models
associated to the prescribed geometric specialization lift. -/
def localGeometricStalkSpecializationMap :
    geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) :=
  (existsUnique_localGeometricStalk_map_of_specializationLift s t h ψ hψ).choose

/-- Evaluation of the selected map is the original field-valued lift. -/
theorem localGeometricStalkSpecializationMap_evaluation :
    localGeometricStalkSpecializationMap s t h ψ hψ ≫ geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) =
      CommRingCat.ofHom ψ :=
  (existsUnique_localGeometricStalk_map_of_specializationLift s t h ψ hψ).choose_spec.1.1

/-- The selected map extends the actual ordinary stalk specialization. -/
theorem localGeometricStalkSpecializationMap_comp_structure :
    (localGeometricStalkSpecializationMap s t h ψ hψ).hom.comp
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (geometricStalkStructureMap (Scheme.stalkClosedPointTo t).hom).comp
        (S.presheaf.stalkSpecializes h).hom :=
  (existsUnique_localGeometricStalk_map_of_specializationLift s t h ψ hψ).choose_spec.1.2.1

/-- The strict local spectrum map retains its morphism to the original scheme. -/
theorem localGeometricStalkSpecializationMap_toScheme :
    Spec.map (localGeometricStalkSpecializationMap s t h ψ hψ) ≫
      localGeometricStalkToScheme s = localGeometricStalkToScheme t :=
  (existsUnique_localGeometricStalk_map_of_specializationLift s t h ψ hψ).choose_spec.1.2.2

end Construction

/-- Choosing the original evaluation at a point gives the identity
on its actual strict local model. -/
theorem localGeometricStalkSpecializationMap_evaluation_id
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    localGeometricStalkSpecializationMap s s (specializes_refl _)
        (geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom
        (by
          simpa only [Scheme.stalkSpecializationToField,
            TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
            geometricStalkStructureMap_evaluation (Scheme.stalkClosedPointTo s).hom) =
      𝟙 (geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))) := by
  let ε : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ω :=
    (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))).hom
  have hε : ε.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField
        (s (closedPoint Ω)) s (specializes_refl _)).hom := by
    simpa only [Scheme.stalkSpecializationToField,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
      geometricStalkStructureMap_evaluation (Scheme.stalkClosedPointTo s).hom
  apply geometricStalk_hom_ext_of_structure_evaluation
    (Scheme.stalkClosedPointTo s).hom
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))
  · simpa only [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id,
      RingHom.comp_id, RingHom.id_comp] using
      localGeometricStalkSpecializationMap_comp_structure s s (specializes_refl _) ε hε
  · simpa only [ε, Category.id_comp, CommRingCat.ofHom_hom] using
      localGeometricStalkSpecializationMap_evaluation s s (specializes_refl _) ε hε

section Composition

variable {S : Scheme.{u}} {Ωs Ωt Ωv : Type u}
  [Field Ωs] [IsSepClosed Ωs] [Field Ωt] [IsSepClosed Ωt] [Field Ωv]
  (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S) (v : Spec (.of Ωv) ⟶ S)
  (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
  (k : v (closedPoint Ωv) ⤳ t (closedPoint Ωt))
  (ψ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
  (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
    (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom)
  (χ : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) →+* Ωv)
  (hχ : χ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo t).hom) =
    (Scheme.stalkSpecializationToField (t (closedPoint Ωt)) v k).hom)

omit [IsSepClosed Ωt] in
include hχ in
/-- Composing the next chosen field-valued lift with the first strict local
map gives a lift of the composite ordinary specialization. -/
theorem localGeometricStalkSpecializationLift_comp_structure :
    (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom).comp
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) v (k.trans h)).hom := by
  rw [RingHom.comp_assoc, localGeometricStalkSpecializationMap_comp_structure,
    ← RingHom.comp_assoc, hχ]
  exact congrArg CommRingCat.Hom.hom (Scheme.stalkSpecializationToField_trans v k h)

/-- Successive geometric specializations compose on the actual strict local
models over the original scheme, using the composite of their original lifts. -/
theorem localGeometricStalkSpecializationMap_comp :
    localGeometricStalkSpecializationMap s t h ψ hψ ≫
        localGeometricStalkSpecializationMap t v k χ hχ =
      localGeometricStalkSpecializationMap s v (k.trans h)
        (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
        (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχ) := by
  apply geometricStalk_hom_ext_of_structure_evaluation
    (Scheme.stalkClosedPointTo s).hom
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo v).hom))
  · have hstalk :
        (S.presheaf.stalkSpecializes k).hom.comp (S.presheaf.stalkSpecializes h).hom =
          (S.presheaf.stalkSpecializes (k.trans h)).hom :=
      congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkSpecializes_comp S.presheaf k h)
    rw [CommRingCat.hom_comp, RingHom.comp_assoc,
      localGeometricStalkSpecializationMap_comp_structure, ← RingHom.comp_assoc,
      localGeometricStalkSpecializationMap_comp_structure, RingHom.comp_assoc,
      hstalk, localGeometricStalkSpecializationMap_comp_structure]
  · calc
      (localGeometricStalkSpecializationMap s t h ψ hψ ≫
          localGeometricStalkSpecializationMap t v k χ hχ) ≫ geometricStalkEvaluation
            (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo v).hom)) =
          localGeometricStalkSpecializationMap s t h ψ hψ ≫
            (localGeometricStalkSpecializationMap t v k χ hχ ≫ geometricStalkEvaluation
              (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo v).hom))) :=
        Category.assoc _ _ _
      _ = localGeometricStalkSpecializationMap s t h ψ hψ ≫ CommRingCat.ofHom χ :=
        congrArg (fun q => localGeometricStalkSpecializationMap s t h ψ hψ ≫ q)
          (localGeometricStalkSpecializationMap_evaluation t v k χ hχ)
      _ = CommRingCat.ofHom
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom) := rfl
      _ = localGeometricStalkSpecializationMap s v (k.trans h)
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
          (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχ) ≫
            geometricStalkEvaluation
              (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo v).hom)) :=
        (localGeometricStalkSpecializationMap_evaluation s v (k.trans h)
          (χ.comp (localGeometricStalkSpecializationMap s t h ψ hψ).hom)
          (localGeometricStalkSpecializationLift_comp_structure s t v h k ψ hψ χ hχ)).symm

end Composition

end EtaleFundamentalGroups.StrictHenselian
