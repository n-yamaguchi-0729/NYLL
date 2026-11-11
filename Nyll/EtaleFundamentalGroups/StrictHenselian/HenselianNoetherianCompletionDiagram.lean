/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageResidue
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.MapAlongIdeal
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
public import Nyll.SchemeTheory.RingTheory.Flat.FilteredColimit
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# The actual filtered diagram of completed henselian Noetherian images

Each local image transition induces its actual maximal-adic completion
map. These form a filtered ring diagram, with the original image diagram
mapping naturally into it. Its concrete ring colimit receives a flat map
from the original henselian ring. The native residue maps form an actual
cocone into the original residue field and preserve its original quotient.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.SubalgebraStages_nonempty_isLimit_cone

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

attribute [local instance] image_isNoetherianRing

/-- The actual image rings, using the existing exhaustive subalgebra diagram. -/
abbrev imageRingDiagram : FGSubalgebra R A ⥤ CommRingCat.{u} :=
  LimBC.ringDiagram (images R A)

/-- The original ring is the literal vertex of its image-ring cocone. -/
abbrev imageRingCocone : Cocone (imageRingDiagram R A) :=
  LimBC.ringCocone (images R A)

/-- Exhaustivity identifies the original henselian ring with this actual colimit. -/
def imageRingCoconeIsColimit : IsColimit (imageRingCocone R A) :=
  (LimBC.nonempty_isColimit_ringCocone (images R A) (exhaustive R A)).some

/-- The maximal-adic completion of an actual henselian Noetherian image. -/
abbrev completionStage (i : FGSubalgebra R A) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (image R A i)) (image R A i)

instance completionStage_isNoetherianRing (i : FGSubalgebra R A) :
    IsNoetherianRing (completionStage R A i) :=
  AdicCompletion.isNoetherianRing_of_isNoetherianRing _

instance completionStage_isLocalRing (i : FGSubalgebra R A) :
    IsLocalRing (completionStage R A i) :=
  inferInstanceAs (IsLocalRing
    (AdicCompletion (IsLocalRing.maximalIdeal (image R A i)) (image R A i)))

instance completionStage_isAdicComplete (i : FGSubalgebra R A) :
    IsAdicComplete (IsLocalRing.maximalIdeal (completionStage R A i))
      (completionStage R A i) :=
  inferInstanceAs (IsAdicComplete
    (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal (image R A i)) (image R A i)))
    (AdicCompletion (IsLocalRing.maximalIdeal (image R A i)) (image R A i)))

/-- The transition is the completed actual inclusion of image rings. -/
def completionTransition {i j : FGSubalgebra R A} (h : i ≤ j) :
    completionStage R A i →+* completionStage R A j := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  exact AdicCompletion.mapMaximal (Subalgebra.inclusion (image_mono R A h)).toRingHom

instance completionTransition_isLocalHom {i j : FGSubalgebra R A} (h : i ≤ j) :
    IsLocalHom (completionTransition R A h) := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  exact AdicCompletion.mapMaximal_isLocalHom
    (Subalgebra.inclusion (image_mono R A h)).toRingHom

omit [IsNoetherianRing R] in
theorem completionTransition_refl (i : FGSubalgebra R A) :
    completionTransition R A (le_refl i) = RingHom.id (completionStage R A i) := by
  have hi : (Subalgebra.inclusion (image_mono R A (le_refl i))).toRingHom =
      RingHom.id (image R A i) := by
    apply RingHom.ext
    intro x
    rfl
  dsimp only [completionTransition]
  simp only [hi, AdicCompletion.mapMaximal_id]

omit [IsNoetherianRing R] in
theorem completionTransition_comp {i j k : FGSubalgebra R A}
    (h : i ≤ j) (h' : j ≤ k) :
    (completionTransition R A h').comp (completionTransition R A h) =
      completionTransition R A (h.trans h') := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h')).toRingHom :=
    image_inclusion_isLocalHom R A h'
  dsimp only [completionTransition]
  rw [AdicCompletion.mapMaximal_comp]
  congr 1

/-- The actual filtered diagram of complete Noetherian local rings. -/
@[reducible] def completionDiagram : FGSubalgebra R A ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (completionStage R A i)
  map h := CommRingCat.ofHom (completionTransition R A h.le)
  map_id i := CommRingCat.hom_ext (completionTransition_refl R A i)
  map_comp h h' := CommRingCat.hom_ext (completionTransition_comp R A h.le h'.le).symm

/-- Every original stage maps naturally into its own completion. -/
def completionUnits : imageRingDiagram R A ⟶ completionDiagram R A where
  app i := CommRingCat.ofHom (algebraMap (image R A i) (completionStage R A i))
  naturality i j h := by
    have : IsLocalHom (Subalgebra.inclusion (image_mono R A h.le)).toRingHom :=
      image_inclusion_isLocalHom R A h.le
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (AdicCompletion.mapMaximal_algebraMap
      (Subalgebra.inclusion (image_mono R A h.le)).toRingHom x).symm

/-- The concrete filtered ring colimit cocone of the completed stages. -/
abbrev completionCocone : Cocone (completionDiagram R A) :=
  CommRingCat.FilteredColimits.colimitCocone (completionDiagram R A)

/-- The concrete filtered ring colimit satisfies its actual universal property. -/
def completionCoconeIsColimit : IsColimit (completionCocone R A) :=
  CommRingCat.FilteredColimits.colimitCoconeIsColimit (completionDiagram R A)

/-- The actual colimit ring, before any choice of a geometric generic lift. -/
abbrev completionColimit : CommRingCat.{u} := (completionCocone R A).pt

/-- The completion units form a cocone on the original image-ring diagram. -/
def completionBaseCocone : Cocone (imageRingDiagram R A) where
  pt := completionColimit R A
  ι := completionUnits R A ≫ (completionCocone R A).ι

/-- The original henselian ring maps to the actual colimit of completions. -/
def completionBaseMap : CommRingCat.of A ⟶ completionColimit R A :=
  (imageRingCoconeIsColimit R A).desc (completionBaseCocone R A)

omit [IsNoetherianRing R] in
@[reassoc]
theorem completionBaseMap_fac (i : FGSubalgebra R A) :
    (imageRingCocone R A).ι.app i ≫ completionBaseMap R A =
      (completionUnits R A).app i ≫ (completionCocone R A).ι.app i :=
  (imageRingCoconeIsColimit R A).fac (completionBaseCocone R A) i

/-- Flatness is supplied by the actual completion maps and the variable-base
filtered-colimit theorem, rather than assumed for the constructed ring. -/
theorem completionBaseMap_flat : (completionBaseMap R A).hom.Flat := by
  apply CommRingCat.flat_of_isColimits
    (imageRingDiagram R A) (completionDiagram R A) (completionUnits R A)
    (imageRingCocone R A) (completionCocone R A)
    (imageRingCoconeIsColimit R A) (completionCoconeIsColimit R A)
    (completionBaseMap R A) (completionBaseMap_fac R A)
  intro i
  change (algebraMap (image R A i) (completionStage R A i)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Reduction of a completed image stage to the original residue field. -/
def completionStageResidue (i : FGSubalgebra R A) :
    completionStage R A i →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.ResidueField.map (image R A i).val.toRingHom).comp
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (image R A i))).toRingHom

omit [IsNoetherianRing R] in
theorem completionStageResidue_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (completionStageResidue R A j).comp (completionTransition R A h) =
      completionStageResidue R A i := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  apply RingHom.ext
  intro x
  change IsLocalRing.ResidueField.map (image R A j).val.toRingHom
      (AdicCompletion.evalOneₐ _ (AdicCompletion.mapMaximal
        (Subalgebra.inclusion (image_mono R A h)).toRingHom x)) = _
  rw [AdicCompletion.evalOne_mapMaximal]
  have hr : (IsLocalRing.ResidueField.map (image R A j).val.toRingHom).comp
      (IsLocalRing.ResidueField.map
        (Subalgebra.inclusion (image_mono R A h)).toRingHom) =
        IsLocalRing.ResidueField.map (image R A i).val.toRingHom := by
    rw [← IsLocalRing.ResidueField.map_comp]
    rfl
  exact RingHom.congr_fun hr (AdicCompletion.evalOneₐ _ x)

/-- The original residue field is an actual cocone of the completed stages. -/
def completionResidueCocone : Cocone (completionDiagram R A) where
  pt := CommRingCat.of (IsLocalRing.ResidueField A)
  ι.app i := CommRingCat.ofHom (completionStageResidue R A i)
  ι.naturality i j h := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    change CommRingCat.ofHom ((completionStageResidue R A j).comp
      (completionTransition R A h.le)) = _
    exact CommRingCat.hom_ext (completionStageResidue_transition R A h.le)

/-- The induced actual residue map on the constructed colimit. -/
def completionResidueMap : completionColimit R A ⟶
    CommRingCat.of (IsLocalRing.ResidueField A) :=
  (completionCoconeIsColimit R A).desc (completionResidueCocone R A)

omit [IsNoetherianRing R] in
@[reassoc]
theorem completionResidueMap_fac (i : FGSubalgebra R A) :
    (completionCocone R A).ι.app i ≫ completionResidueMap R A =
      CommRingCat.ofHom (completionStageResidue R A i) :=
  (completionCoconeIsColimit R A).fac (completionResidueCocone R A) i

omit [IsNoetherianRing R] in
/-- The constructed colimit residue map preserves the original residue quotient. -/
theorem completionBaseMap_residue :
    completionBaseMap R A ≫ completionResidueMap R A =
      CommRingCat.ofHom (IsLocalRing.residue A) := by
  apply (imageRingCoconeIsColimit R A).hom_ext
  intro i
  change CommRingCat.ofHom (image R A i).val.toRingHom ≫
      (completionBaseMap R A ≫ completionResidueMap R A) =
    CommRingCat.ofHom (image R A i).val.toRingHom ≫
      CommRingCat.ofHom (IsLocalRing.residue A)
  have hb : CommRingCat.ofHom (image R A i).val.toRingHom ≫ completionBaseMap R A =
      CommRingCat.ofHom (algebraMap (image R A i) (completionStage R A i)) ≫
        (completionCocone R A).ι.app i := completionBaseMap_fac R A i
  rw [← Category.assoc, hb, Category.assoc, completionResidueMap_fac]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change IsLocalRing.ResidueField.map (image R A i).val.toRingHom
      (AdicCompletion.evalOneₐ _ (AdicCompletion.of _ _ x)) =
    IsLocalRing.residue A (x : A)
  rw [AdicCompletion.evalOneₐ_of]
  exact IsLocalRing.ResidueField.map_residue (image R A i).val.toRingHom x

end AlgebraicGeometry.HenselianNoetherianImageStages
