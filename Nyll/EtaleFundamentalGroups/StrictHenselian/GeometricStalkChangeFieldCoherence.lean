/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Coherence of pointing-field extensions

Identity embeddings and successive field embeddings induce the identity and
composite maps on the actual pointed étale colimits. The equalities are proved
on the original neighborhood points, without assumptions that the fields are
separably closed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Extending a neighborhood point by the identity field map preserves it. -/
theorem pointedEtaleChangeField_id
    {R Ω : Type u} [CommRing R] [Field Ω] (s : R →+* Ω)
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    pointedEtaleChangeField s (RingHom.id Ω) W w = w := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of Ω)) ≫ w.left = w.left
  rw [Spec.map_id, Category.id_comp]

/-- Successively extending the field of a neighborhood point agrees with
extension along the composite embedding. -/
theorem pointedEtaleChangeField_comp
    {R Ω Ω' Ω'' : Type u} [CommRing R] [Field Ω] [Field Ω'] [Field Ω'']
    (s : R →+* Ω) (ι : Ω →+* Ω') (κ : Ω' →+* Ω'')
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    pointedEtaleChangeField (ι.comp s) κ W (pointedEtaleChangeField s ι W w) =
      pointedEtaleChangeField s (κ.comp ι) W w := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom κ) ≫
      (Spec.map (CommRingCat.ofHom ι) ≫ w.left) =
    Spec.map (CommRingCat.ofHom (κ.comp ι)) ≫ w.left
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The identity field embedding induces the identity on the geometric stalk. -/
theorem geometricStalkChangeField_id
    {R Ω : Type u} [CommRing R] [Field Ω] (s : R →+* Ω) :
    geometricStalkChangeField s (RingHom.id Ω) =
      𝟙 (geometricStalk (Spec.map (CommRingCat.ofHom s))) := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkChangeField s (RingHom.id Ω) =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ 𝟙 _
  rw [geometricStalkGerm_changeField, pointedEtaleChangeField_id, Category.comp_id]

/-- Field extension on geometric stalks respects composition of the specified
field embeddings, as an equality of the actual colimit maps. -/
theorem geometricStalkChangeField_comp
    {R Ω Ω' Ω'' : Type u} [CommRing R] [Field Ω] [Field Ω'] [Field Ω'']
    (s : R →+* Ω) (ι : Ω →+* Ω') (κ : Ω' →+* Ω'') :
    geometricStalkChangeField s ι ≫ geometricStalkChangeField (ι.comp s) κ =
      geometricStalkChangeField s (κ.comp ι) := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkChangeField s ι ≫ geometricStalkChangeField (ι.comp s) κ =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkChangeField s (κ.comp ι)
  rw [← Category.assoc, geometricStalkGerm_changeField, geometricStalkGerm_changeField,
    geometricStalkGerm_changeField, pointedEtaleChangeField_comp]

end EtaleFundamentalGroups.StrictHenselian
