/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionImages
public import Nyll.SchemeTheory.RingTheory.Henselian.FilteredColimit
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Nyll.SchemeTheory.RingTheory.LocalRing.FilteredColimit

/-!
# Local, henselian and residue properties of the completion colimit

The actual colimit of completed image rings is henselian, and the
original ring maps to it faithfully flatly by a local homomorphism.
Its existing residue map is local and surjective. The native residue
lift is therefore a field isomorphism, with the original quotient map
as its literal composite and the native base residue map as its inverse.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

attribute [local instance] image_isNoetherianRing

/-- Every actual complete image stage is henselian at its native maximal ideal. -/
instance completionStage_henselianLocalRing (i : FGSubalgebra R A) :
    HenselianLocalRing (completionStage R A i) := by
  have : HenselianRing (completionStage R A i)
      (IsLocalRing.maximalIdeal (completionStage R A i)) := inferInstance
  refine { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (completionStage R A i))))

/-- Henselianity is supplied by the actual filtered diagram of completions. -/
instance completionColimit_henselianLocalRing :
    HenselianLocalRing (completionColimit R A) :=
  CommRingCat.henselianLocalRing_of_isColimit (completionDiagram R A)
    (completionCocone R A) (completionCoconeIsColimit R A)
    (fun {_ _} f => completionTransition_isLocalHom R A f.le)

/-- The actual map from the original henselian ring to the completion colimit is local. -/
instance completionBaseMap_isLocalHom : IsLocalHom (completionBaseMap R A).hom := by
  apply CommRingCat.isLocalHom_of_isColimits
    (imageRingDiagram R A) (completionDiagram R A) (completionUnits R A)
    (imageRingCocone R A) (completionCocone R A)
    (imageRingCoconeIsColimit R A) (completionCoconeIsColimit R A)
    (completionBaseMap R A) (completionBaseMap_fac R A)
    (fun {_ _} f => completionTransition_isLocalHom R A f.le)
  intro i
  change IsLocalHom (algebraMap (image R A i) (completionStage R A i))
  infer_instance

/-- Flatness and localness make the constructed base map faithfully flat. -/
theorem completionBaseMap_faithfullyFlat : (completionBaseMap R A).hom.FaithfullyFlat := by
  let _completionAlgebra : Algebra A (completionColimit R A) :=
    (completionBaseMap R A).hom.toAlgebra
  have : Module.Flat A (completionColimit R A) := completionBaseMap_flat R A
  have : IsLocalHom (algebraMap A (completionColimit R A)) := by
    change IsLocalHom (completionBaseMap R A).hom
    exact completionBaseMap_isLocalHom R A
  change Module.FaithfullyFlat A (completionColimit R A)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Each specified completed-stage residue map reflects units. -/
instance completionStageResidue_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (completionStageResidue R A i) := by
  have heval : IsLocalHom
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (image R A i))).toRingHom :=
    IsLocalHom.of_surjective _ (AdicCompletion.evalOneₐ_surjective _)
  have hfield : IsLocalHom (IsLocalRing.ResidueField.map (image R A i).val.toRingHom) := by
    constructor
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    rw [hzero, map_zero] at hx
    exact not_isUnit_zero hx
  change IsLocalHom
    ((IsLocalRing.ResidueField.map (image R A i).val.toRingHom).comp
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (image R A i))).toRingHom)
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _
    (IsLocalRing.ResidueField.map (image R A i).val.toRingHom)
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (image R A i))).toRingHom hfield heval

/-- The existing residue map of the actual colimit reflects units because
every element is represented at an actual completed image stage. -/
instance completionResidueMap_isLocalHom : IsLocalHom (completionResidueMap R A).hom := by
  constructor
  intro x hx
  have hrep : ∃ (i : FGSubalgebra R A) (b : completionStage R A i),
      (completionCocone R A).ι.app i b = x := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) (completionCoconeIsColimit R A)) x
  obtain ⟨i, b, rfl⟩ := hrep
  have hu : IsUnit (completionStageResidue R A i b) :=
    (ConcreteCategory.congr_hom (completionResidueMap_fac R A i) b) ▸ hx
  exact (isUnit_of_map_unit (completionStageResidue R A i) b hu).map
    ((completionCocone R A).ι.app i).hom

omit [IsNoetherianRing R] in
/-- The original residue quotient makes the specified colimit residue map surjective. -/
theorem completionResidueMap_surjective : Function.Surjective (completionResidueMap R A) := by
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨completionBaseMap R A a, ?_⟩
  exact ConcreteCategory.congr_hom (completionBaseMap_residue R A) a

/-- The actual colimit residue field is canonically the original residue field. -/
def completionResidueEquiv : IsLocalRing.ResidueField (completionColimit R A) ≃+*
    IsLocalRing.ResidueField A :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (completionResidueMap R A).hom)
    ⟨RingHom.injective _, fun x => by
      obtain ⟨a, ha⟩ := completionResidueMap_surjective R A x
      exact ⟨IsLocalRing.residue (completionColimit R A) a, ha⟩⟩

/-- The comparison has the already constructed residue map as its exact quotient composite. -/
theorem completionResidueEquiv_comp_residue :
    (completionResidueEquiv R A).toRingHom.comp
        (IsLocalRing.residue (completionColimit R A)) =
      (completionResidueMap R A).hom :=
  IsLocalRing.ResidueField.lift_comp_residue (completionResidueMap R A).hom

theorem completionResidueEquiv_residue (x : completionColimit R A) :
    completionResidueEquiv R A (IsLocalRing.residue (completionColimit R A) x) =
      completionResidueMap R A x :=
  RingHom.congr_fun (completionResidueEquiv_comp_residue R A) x

/-- The residue comparison preserves the original ring's specified quotient. -/
theorem completionResidueEquiv_base_residue (a : A) :
    completionResidueEquiv R A
        (IsLocalRing.residue (completionColimit R A) (completionBaseMap R A a)) =
      IsLocalRing.residue A a := by
  rw [completionResidueEquiv_residue]
  exact ConcreteCategory.congr_hom (completionBaseMap_residue R A) a

/-- Its inverse is the native residue map of the original actual base map. -/
theorem completionResidueEquiv_symm_toRingHom :
    (completionResidueEquiv R A).symm.toRingHom =
      IsLocalRing.ResidueField.map (completionBaseMap R A).hom := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  apply (completionResidueEquiv R A).injective
  change completionResidueEquiv R A
      ((completionResidueEquiv R A).symm (IsLocalRing.residue A a)) =
    completionResidueEquiv R A
      (IsLocalRing.ResidueField.map (completionBaseMap R A).hom (IsLocalRing.residue A a))
  rw [RingEquiv.apply_symm_apply, IsLocalRing.ResidueField.map_residue]
  exact (completionResidueEquiv_base_residue R A a).symm

end AlgebraicGeometry.HenselianNoetherianImageStages
