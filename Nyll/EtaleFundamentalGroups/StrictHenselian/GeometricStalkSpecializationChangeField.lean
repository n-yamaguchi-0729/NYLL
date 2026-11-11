/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI ChatGPT)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeField
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNeighborhoodLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationMap
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Field extension and chosen geometric specialization

The existing field-change construction alone does not assert compatibility
with specialization. Here extension of the generic pointing field is
compared on the actual neighborhood points. Extension of the special
pointing field is compared using specialization along the extended evaluation
and the composition law for the actual specialization maps.
Both equalities retain the given field-valued lift; neither introduces a
new choice of specialization.

These strict-local equalities are ingredients in the field-extension
squares of Stacks Project, Lemmas 58.16.3 and 58.16.4:
https://stacks.math.columbia.edu/tag/0C0M
https://stacks.math.columbia.edu/tag/0C0N
They do not assert the proper-fibre fundamental-group comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Extending the generic pointing field commutes with the specialization
map for the composite chosen lift. The generic fields need not be separably
closed for this germwise equality. -/
theorem geometricStalkSpecializationMap_changeField_generic
    {R Ω Ψ Ψ' : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Field Ψ] [Field Ψ']
    (s : R →+* Ω) (t : R →+* Ψ)
    (ψ : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ψ)
    (hψ : ψ.comp (geometricStalkStructureMap s) = t) (ι : Ψ →+* Ψ') :
    geometricStalkSpecializationMap s t ψ hψ ≫ geometricStalkChangeField t ι =
      geometricStalkSpecializationMap s (ι.comp t) (ι.comp ψ)
        (by rw [RingHom.comp_assoc, hψ]) := by
  have hψ' : (ι.comp ψ).comp (geometricStalkStructureMap s) = ι.comp t := by
    rw [RingHom.comp_assoc, hψ]
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  have hpoints :
      pointedEtaleChangeField t ι W (pointedEtaleSpecialization s t ψ hψ W w) =
        pointedEtaleSpecialization s (ι.comp t) (ι.comp ψ) hψ' W w := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ι) ≫
        (Spec.map (CommRingCat.ofHom ψ) ≫ geometricStalkNeighborhoodLift s W w) =
      Spec.map (CommRingCat.ofHom (ι.comp ψ)) ≫ geometricStalkNeighborhoodLift s W w
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s t ψ hψ ≫ geometricStalkChangeField t ι =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s (ι.comp t) (ι.comp ψ) hψ'
  rw [← Category.assoc, geometricStalkGerm_specializationMap,
    geometricStalkGerm_changeField, hpoints, geometricStalkGerm_specializationMap]

/-- Extending the pointing field is specialization along the original evaluation
followed by the field embedding. This compares the two independently constructed
maps on their actual neighborhood points. -/
theorem geometricStalkChangeField_eq_specializationMap
    {R Ω Ω' : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω] [Field Ω']
    (s : R →+* Ω) (ι : Ω →+* Ω') :
    geometricStalkChangeField s ι =
      geometricStalkSpecializationMap s (ι.comp s)
        (ι.comp (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom s))).hom)
        (by rw [RingHom.comp_assoc, geometricStalkStructureMap_evaluation]) := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkChangeField s ι =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s (ι.comp s) _ _
  rw [geometricStalkGerm_changeField, geometricStalkGerm_specializationMap]
  apply congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom (ι.comp s))) W)
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ι) ≫ w.left =
    Spec.map (CommRingCat.ofHom
      (ι.comp (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom s))).hom)) ≫
        geometricStalkNeighborhoodLift s W w
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    geometricStalkNeighborhoodLift_evaluation]
  rfl

/-- Restriction of a chosen lift along extension of the special pointing
field agrees with composition of the two actual geometric-stalk maps.
The target pointing field need not be separably closed. -/
theorem geometricStalkSpecializationMap_changeField_special
    {R Ω Ω' Ψ : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Field Ω'] [IsSepClosed Ω'] [Field Ψ]
    (s : R →+* Ω) (ι : Ω →+* Ω') (t : R →+* Ψ)
    (ψ : geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp s))) →+* Ψ)
    (hψ : ψ.comp (geometricStalkStructureMap (ι.comp s)) = t) :
    geometricStalkChangeField s ι ≫
        geometricStalkSpecializationMap (ι.comp s) t ψ hψ =
      geometricStalkSpecializationMap s t
        (ψ.comp (geometricStalkChangeField s ι).hom)
        (by rw [RingHom.comp_assoc, geometricStalkChangeField_comp_structure, hψ]) := by
  simp only [geometricStalkChangeField_eq_specializationMap,
    geometricStalkSpecializationMap_comp]

/-- Simultaneously extending the special and generic pointing fields gives a
commutative square whenever the two prescribed lifts agree after field extension.
Compatibility is imposed only on the field-valued lifts; commutativity on the
entire geometric stalk is a consequence. -/
theorem geometricStalkSpecializationMap_changeField_square
    {R Ω Ω' Ψ Ψ' : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Field Ω'] [IsSepClosed Ω'] [Field Ψ] [Field Ψ']
    (s : R →+* Ω) (ι : Ω →+* Ω') (t : R →+* Ψ) (κ : Ψ →+* Ψ')
    (ψ : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ψ)
    (hψ : ψ.comp (geometricStalkStructureMap s) = t)
    (ψ' : geometricStalk (Spec.map (CommRingCat.ofHom (ι.comp s))) →+* Ψ')
    (hψ' : ψ'.comp (geometricStalkStructureMap (ι.comp s)) = κ.comp t)
    (hcompat : ψ'.comp (geometricStalkChangeField s ι).hom = κ.comp ψ) :
    geometricStalkSpecializationMap s t ψ hψ ≫ geometricStalkChangeField t κ =
      geometricStalkChangeField s ι ≫
        geometricStalkSpecializationMap (ι.comp s) (κ.comp t) ψ' hψ' := by
  simp only [geometricStalkSpecializationMap_changeField_generic,
    geometricStalkSpecializationMap_changeField_special, hcompat]

end EtaleFundamentalGroups.StrictHenselian
