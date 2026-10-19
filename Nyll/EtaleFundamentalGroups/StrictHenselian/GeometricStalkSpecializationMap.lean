/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNeighborhoodLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Maps of strict local rings induced by a chosen specialization

A field-valued lift of a point to the strict local spectrum determines
new points on every original étale neighborhood. Their germ maps form a
cocone on the existing pointed étale colimit. The resulting ring map
extends the identity on the base ring and has exactly the prescribed
evaluation in the new pointing field.

The construction preserves the chosen lift, and successive choices give
the composite ring map. It supplies the map of strict local rings used
in Stacks Project, Lemma 58.16.2:
https://stacks.math.columbia.edu/tag/0BUP.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω Ψ : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω] [Field Ψ]
  (s : R →+* Ω) (t : R →+* Ψ)
  (ψ : geometricStalk (Spec.map (CommRingCat.ofHom s)) →+* Ψ)
  (hψ : ψ.comp (geometricStalkStructureMap s) = t)

/-- A chosen point on the strict local spectrum supplies a point on each
of the original étale neighborhoods. -/
def pointedEtaleSpecialization
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom t))).fiber.obj W := by
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom s))
  let ψCat : H ⟶ CommRingCat.of Ψ := CommRingCat.ofHom ψ
  let a : CommRingCat.of R ⟶ H := CommRingCat.ofHom (geometricStalkStructureMap s)
  let l : Spec H ⟶ W.left := geometricStalkNeighborhoodLift s W w
  let p : W.left ⟶ Spec (.of R) := W.hom
  have hl : l ≫ p = Spec.map a := geometricStalkNeighborhoodLift_comp s W w
  have ha : a ≫ ψCat = CommRingCat.ofHom t := congrArg CommRingCat.ofHom hψ
  have hcomm : (Spec.map ψCat ≫ l) ≫ p = Spec.map (CommRingCat.ofHom t) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun b : Spec H ⟶ Spec (.of R) => Spec.map ψCat ≫ b) hl).trans
        ((Spec.map_comp a ψCat).symm.trans (congrArg Spec.map ha)))
  change Over.mk (Spec.map (CommRingCat.ofHom t)) ⟶ Over.mk p
  exact Over.homMk (Spec.map ψCat ≫ l) hcomm

/-- The new neighborhood points respect every morphism of neighborhoods. -/
theorem pointedEtaleSpecialization_naturality
    {W V : (Spec (.of R)).Etale} (g : W ⟶ V)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom t))).fiber.map g
        (pointedEtaleSpecialization s t ψ hψ W w) =
      pointedEtaleSpecialization s t ψ hψ V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.map g w) := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom ψ) ≫ geometricStalkNeighborhoodLift s W w) ≫
      g.left = Spec.map (CommRingCat.ofHom ψ) ≫ geometricStalkNeighborhoodLift s V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.map g w)
  rw [Category.assoc, geometricStalkNeighborhoodLift_naturality]

/-- The ring map on the actual geometric stalks associated to the chosen
field-valued lift of the generic point. -/
def geometricStalkSpecializationMap :
    geometricStalk (Spec.map (CommRingCat.ofHom s)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom t)) :=
  (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).presheafFiberDesc
    (fun W w => geometricStalkGerm (Spec.map (CommRingCat.ofHom t)) W
      (pointedEtaleSpecialization s t ψ hψ W w)) (by
      intro W V g w
      have h := (Scheme.pointEtaleNeighborhoods
        (Spec.map (CommRingCat.ofHom t))).toPresheafFiber_w
          g (pointedEtaleSpecialization s t ψ hψ W w) (etaleSections (Spec (.of R)))
      rw [pointedEtaleSpecialization_naturality] at h
      exact h)

/-- The induced map sends every germ to the same section at the new point
on its actual neighborhood. -/
theorem geometricStalkGerm_specializationMap
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
        geometricStalkSpecializationMap s t ψ hψ =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom t)) W
        (pointedEtaleSpecialization s t ψ hψ W w) :=
  (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).toPresheafFiber_presheafFiberDesc _ _ W w

/-- Evaluation of the constructed ring map is the originally chosen
generic lift, including on nilpotent germs. -/
theorem geometricStalkSpecializationMap_evaluation :
    geometricStalkSpecializationMap s t ψ hψ ≫
        geometricStalkEvaluation (Spec.map (CommRingCat.ofHom t)) =
      CommRingCat.ofHom ψ := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s t ψ hψ ≫
        geometricStalkEvaluation (Spec.map (CommRingCat.ofHom t)) =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ CommRingCat.ofHom ψ
  rw [← Category.assoc, geometricStalkGerm_specializationMap,
    geometricStalkGerm_evaluation]
  let H : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom s))
  let ψCat : H ⟶ CommRingCat.of Ψ := CommRingCat.ofHom ψ
  let l : Spec H ⟶ W.left := geometricStalkNeighborhoodLift s W w
  let γ : Γ(W.left, ⊤) ⟶ H := geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w
  let eH : Γ(Spec H, ⊤) ⟶ H := (Scheme.ΓSpecIso H).hom
  let eΨ : Γ(Spec (.of Ψ), ⊤) ⟶ CommRingCat.of Ψ :=
    (Scheme.ΓSpecIso (CommRingCat.of Ψ)).hom
  have hγ : l.appTop ≫ eH = γ := geometricStalkNeighborhoodLift_appTop s W w
  have hNat : (Spec.map ψCat).appTop ≫ eΨ = eH ≫ ψCat :=
    Scheme.ΓSpecIso_naturality ψCat
  change (Spec.map ψCat ≫ l).appTop ≫ eΨ = γ ≫ ψCat
  rw [Scheme.Hom.comp_appTop, Category.assoc, hNat, ← Category.assoc]
  exact congrArg (fun a : Γ(W.left, ⊤) ⟶ H => a ≫ ψCat) hγ

/-- The map of strict local rings preserves the original base-ring map. -/
theorem geometricStalkSpecializationMap_comp_structure :
    (geometricStalkSpecializationMap s t ψ hψ).hom.comp (geometricStalkStructureMap s) =
      geometricStalkStructureMap t := by
  let W : (Spec (.of R)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let w : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom s))).fiber.obj W :=
    Over.homMk (Spec.map (CommRingCat.ofHom s)) (Category.comp_id _)
  let w' : (Scheme.pointEtaleNeighborhoods
      (Spec.map (CommRingCat.ofHom t))).fiber.obj W :=
    Over.homMk (Spec.map (CommRingCat.ofHom t)) (Category.comp_id _)
  have hw : pointedEtaleSpecialization s t ψ hψ W w = w' := by
    apply Over.OverMorphism.ext
    exact (Category.comp_id _).symm.trans (Over.w (pointedEtaleSpecialization s t ψ hψ W w))
  let γ : Γ(Spec (.of R), ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom s)) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w
  let γ' : Γ(Spec (.of R), ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom t)) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom t)) W w'
  have hγ : γ ≫ geometricStalkSpecializationMap s t ψ hψ = γ' :=
    (geometricStalkGerm_specializationMap s t ψ hψ W w).trans
      (congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom t)) W) hw)
  have hcat : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ γ) ≫
      geometricStalkSpecializationMap s t ψ hψ =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ γ' :=
    (Category.assoc _ _ _).trans
      (congrArg (fun a : Γ(Spec (.of R), ⊤) ⟶
        geometricStalk (Spec.map (CommRingCat.ofHom t)) =>
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ a) hγ)
  exact congrArg CommRingCat.Hom.hom hcat

/-- The induced map between strict local spectra intertwines their actual
maps to every original neighborhood. -/
theorem geometricStalkNeighborhoodLift_specializationMap [IsSepClosed Ψ]
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom s))).fiber.obj W) :
    Spec.map (geometricStalkSpecializationMap s t ψ hψ) ≫
        geometricStalkNeighborhoodLift s W w =
      geometricStalkNeighborhoodLift t W (pointedEtaleSpecialization s t ψ hψ W w) := by
  apply (existsUnique_geometricStalkNeighborhoodLift t W
    (pointedEtaleSpecialization s t ψ hψ W w)).unique
  · constructor
    · rw [Category.assoc, geometricStalkNeighborhoodLift_comp, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom
        ((geometricStalkSpecializationMap s t ψ hψ).hom.comp
          (geometricStalkStructureMap s))) =
        Spec.map (CommRingCat.ofHom (geometricStalkStructureMap t))
      rw [geometricStalkSpecializationMap_comp_structure]
    · change Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom t))) ≫
          (Spec.map (geometricStalkSpecializationMap s t ψ hψ) ≫
            geometricStalkNeighborhoodLift s W w) =
        Spec.map (CommRingCat.ofHom ψ) ≫ geometricStalkNeighborhoodLift s W w
      rw [← Category.assoc, ← Spec.map_comp, geometricStalkSpecializationMap_evaluation]
  · exact ⟨geometricStalkNeighborhoodLift_comp t W _,
      geometricStalkNeighborhoodLift_evaluation t W _⟩

/-- The maps of actual geometric stalks compose according to the composite
chosen field-valued lift. This is the ring-level composition law required
for successive specializations. -/
theorem geometricStalkSpecializationMap_comp [IsSepClosed Ψ]
    {Ξ : Type u} [Field Ξ] (v : R →+* Ξ)
    (χ : geometricStalk (Spec.map (CommRingCat.ofHom t)) →+* Ξ)
    (hχ : χ.comp (geometricStalkStructureMap t) = v) :
    geometricStalkSpecializationMap s t ψ hψ ≫ geometricStalkSpecializationMap t v χ hχ =
      geometricStalkSpecializationMap s v
        (χ.comp (geometricStalkSpecializationMap s t ψ hψ).hom)
        (by rw [RingHom.comp_assoc, geometricStalkSpecializationMap_comp_structure, hχ]) := by
  have hcomp : (χ.comp (geometricStalkSpecializationMap s t ψ hψ).hom).comp
      (geometricStalkStructureMap s) = v := by
    rw [RingHom.comp_assoc, geometricStalkSpecializationMap_comp_structure, hχ]
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  have hpoints : pointedEtaleSpecialization t v χ hχ W
      (pointedEtaleSpecialization s t ψ hψ W w) =
    pointedEtaleSpecialization s v
      (χ.comp (geometricStalkSpecializationMap s t ψ hψ).hom) hcomp W w := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom χ) ≫
        geometricStalkNeighborhoodLift t W (pointedEtaleSpecialization s t ψ hψ W w) =
      Spec.map (CommRingCat.ofHom
        (χ.comp (geometricStalkSpecializationMap s t ψ hψ).hom)) ≫
          geometricStalkNeighborhoodLift s W w
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      geometricStalkNeighborhoodLift_specializationMap]
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s t ψ hψ ≫ geometricStalkSpecializationMap t v χ hχ =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s v
        (χ.comp (geometricStalkSpecializationMap s t ψ hψ).hom) hcomp
  rw [← Category.assoc, geometricStalkGerm_specializationMap,
    geometricStalkGerm_specializationMap, geometricStalkGerm_specializationMap, hpoints]

/-- Choosing the original evaluation induces the identity on the strict
local ring. -/
theorem geometricStalkSpecializationMap_evaluation_id :
    geometricStalkSpecializationMap s s
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom s))).hom
      (geometricStalkStructureMap_evaluation s) =
        𝟙 (geometricStalk (Spec.map (CommRingCat.ofHom s))) := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫
      geometricStalkSpecializationMap s s _ _ =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ 𝟙 _
  rw [geometricStalkGerm_specializationMap, Category.comp_id]
  apply congrArg (geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W)
  apply Over.OverMorphism.ext
  exact geometricStalkNeighborhoodLift_evaluation s W w

end EtaleFundamentalGroups.StrictHenselian
