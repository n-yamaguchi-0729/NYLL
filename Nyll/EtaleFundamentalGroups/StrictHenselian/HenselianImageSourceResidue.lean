/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageResidue

/-!
# Residue comparison before passing to henselization images

The actual image stage is a local quotient of its actual ordinary
henselization. The quotient induces an isomorphism on the native residue
fields, preserving both the map to the original ring and the transitions.

This permits a finite étale cover already descended over an image-stage
closed fibre to be regarded over the closed fibre of the original
henselization. It supplies no Artin approximation or smooth factorization.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]

/-- The quotient onto the actual image is local because its composite
with the local image inclusion is the original henselian lift. -/
instance imageProjection_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (imageProjection R A i) := by
  have : IsLocalHom
      ((image R A i).val.toRingHom.comp (imageProjection R A i)) := by
    change IsLocalHom (henselianStageMap R A i)
    infer_instance
  exact isLocalHom_of_comp (imageProjection R A i) (image R A i).val.toRingHom

/-- The native residue map of the actual quotient is bijective. -/
theorem imageProjection_residueMap_bijective (i : FGSubalgebra R A) :
    Function.Bijective (IsLocalRing.ResidueField.map (imageProjection R A i)) := by
  refine ⟨RingHom.injective _, ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := image R A i) x
  obtain ⟨b, rfl⟩ := imageProjection_surjective R A i a
  exact ⟨IsLocalRing.residue (henselianStage R A i) b,
    IsLocalRing.ResidueField.map_residue (imageProjection R A i) b⟩

/-- The residue field before taking the actual image and the residue
field of the actual image are canonically identified. -/
def sourceImageResidueEquiv (i : FGSubalgebra R A) :
    IsLocalRing.ResidueField (henselianStage R A i) ≃+*
      IsLocalRing.ResidueField (image R A i) :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (imageProjection R A i))
    (imageProjection_residueMap_bijective R A i)

theorem sourceImageResidueEquiv_residue (i : FGSubalgebra R A)
    (a : henselianStage R A i) :
    sourceImageResidueEquiv R A i
        (IsLocalRing.residue (henselianStage R A i) a) =
      IsLocalRing.residue (image R A i) (imageProjection R A i a) :=
  IsLocalRing.ResidueField.map_residue (imageProjection R A i) a

/-- Both routes to the original residue field are the native residue
map of the original henselian lift. -/
theorem sourceImageResidueEquiv_comp_to_original (i : FGSubalgebra R A) :
    (IsLocalRing.ResidueField.map (image R A i).val.toRingHom).comp
        (sourceImageResidueEquiv R A i).toRingHom =
      IsLocalRing.ResidueField.map (henselianStageMap R A i) := by
  change (IsLocalRing.ResidueField.map (image R A i).val.toRingHom).comp
      (IsLocalRing.ResidueField.map (imageProjection R A i)) =
    IsLocalRing.ResidueField.map (henselianStageMap R A i)
  exact (IsLocalRing.ResidueField.map_comp
    (imageProjection R A i) (image R A i).val.toRingHom).symm

/-- The actual source transitions descend to the existing image
inclusions, without requiring either henselian lift to be injective. -/
theorem imageProjection_comp_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (imageProjection R A j).comp (henselianTransition R A h) =
      (Subalgebra.inclusion (image_mono R A h)).toRingHom.comp
        (imageProjection R A i) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact RingHom.congr_fun (henselianStageMap_comp_transition R A h) a

/-- The residue identifications retain the original transition maps. -/
theorem sourceImageResidueEquiv_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    let _ : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
      image_inclusion_isLocalHom R A h
    (sourceImageResidueEquiv R A j).toRingHom.comp
        (IsLocalRing.ResidueField.map (henselianTransition R A h)) =
      (IsLocalRing.ResidueField.map
        (Subalgebra.inclusion (image_mono R A h)).toRingHom).comp
          (sourceImageResidueEquiv R A i).toRingHom := by
  intro inclusionLocal
  change (IsLocalRing.ResidueField.map (imageProjection R A j)).comp
      (IsLocalRing.ResidueField.map (henselianTransition R A h)) =
    (IsLocalRing.ResidueField.map
      (Subalgebra.inclusion (image_mono R A h)).toRingHom).comp
      (IsLocalRing.ResidueField.map (imageProjection R A i))
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective
    (R := henselianStage R A i) x
  simp only [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue (image R A j))
    (RingHom.congr_fun (imageProjection_comp_transition R A h) a)

end AlgebraicGeometry.HenselianNoetherianImageStages
