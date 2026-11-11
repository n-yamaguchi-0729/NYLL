/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionLocal
import Nyll.SchemeTheory.RingTheory.AdicCompletion.LocalHomExt
import Nyll.SchemeTheory.RingTheory.AdicCompletion.MapAlongIdeal

/-!
# Maps from the completion colimit to complete local rings

A local map from the original henselian ring to a complete Noetherian
local ring extends to the actual completion colimit. Each stage map is
the completed original map followed by the native completion equivalence.
These maps commute with the actual transitions, so the original colimit
constructs the extension and its exact base triangle.
Local maps into a separated target are unique from that triangle. Hence
extensions to complete targets commute with further local target maps.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]
  {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
  (f : A →+* B) [IsLocalHom f]

attribute [local instance] image_isNoetherianRing

/-- Complete the actual stage map and recover the supplied complete target. -/
def completionStageToComplete (i : FGSubalgebra R A) :
    completionStage R A i →+* B :=
  ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).symm.toRingHom).comp
    (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom))

omit [IsNoetherianRing R] [IsNoetherianRing B] in
/-- The stage extension retains the literal original map on the image ring. -/
theorem completionStageToComplete_algebraMap (i : FGSubalgebra R A) (a : image R A i) :
    completionStageToComplete R A f i
        (algebraMap (image R A i) (completionStage R A i) a) = f (a : A) := by
  change (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).symm
    (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom)
      (algebraMap (image R A i) (completionStage R A i) a)) = f (a : A)
  rw [AdicCompletion.mapMaximal_algebraMap]
  exact AdicCompletion.ofAlgEquiv_symm_of (IsLocalRing.maximalIdeal B) (f (a : A))

omit [IsNoetherianRing R] [IsNoetherianRing B] in
/-- Functoriality of actual completion maps supplies the required stage compatibility. -/
theorem completionStageToComplete_transition {i j : FGSubalgebra R A} (h : i ≤ j) :
    (completionStageToComplete R A f j).comp (completionTransition R A h) =
      completionStageToComplete R A f i := by
  have : IsLocalHom (Subalgebra.inclusion (image_mono R A h)).toRingHom :=
    image_inclusion_isLocalHom R A h
  change ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).symm.toRingHom).comp
      ((AdicCompletion.mapMaximal (f.comp (image R A j).val.toRingHom)).comp
        (AdicCompletion.mapMaximal (Subalgebra.inclusion (image_mono R A h)).toRingHom)) =
    ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).symm.toRingHom).comp
      (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom))
  rw [AdicCompletion.mapMaximal_comp]
  rfl

/-- The constructed completed-stage map is local. -/
instance completionStageToComplete_isLocalHom (i : FGSubalgebra R A) :
    IsLocalHom (completionStageToComplete R A f i) := by
  have hlocal : IsLocalHom
      (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom)) :=
    AdicCompletion.mapMaximal_isLocalHom _
  constructor
  intro x hx
  have hu := hx.map (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).toRingHom
  change IsUnit ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B))
    ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal B)).symm
      (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom) x))) at hu
  rw [AlgEquiv.apply_symm_apply] at hu
  exact isUnit_of_map_unit
    (AdicCompletion.mapMaximal (f.comp (image R A i).val.toRingHom)) x hu

/-- The supplied complete target is a cocone of the actual completed stages. -/
def completionToCompleteCocone : Cocone (completionDiagram R A) where
  pt := CommRingCat.of B
  ι.app i := CommRingCat.ofHom (completionStageToComplete R A f i)
  ι.naturality i j h := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    change CommRingCat.ofHom ((completionStageToComplete R A f j).comp
      (completionTransition R A h.le)) = _
    exact CommRingCat.hom_ext (completionStageToComplete_transition R A f h.le)

/-- The actual colimit supplies the extension of the given local map. -/
def completionToComplete : completionColimit R A →+* B :=
  ((completionCoconeIsColimit R A).desc (completionToCompleteCocone R A f)).hom

omit [IsNoetherianRing R] [IsNoetherianRing B] in
/-- Its restriction to every original completed stage is the map constructed above. -/
@[reassoc]
theorem completionToComplete_fac (i : FGSubalgebra R A) :
    (completionCocone R A).ι.app i ≫ CommRingCat.ofHom (completionToComplete R A f) =
      CommRingCat.ofHom (completionStageToComplete R A f i) :=
  (completionCoconeIsColimit R A).fac (completionToCompleteCocone R A f) i

omit [IsNoetherianRing R] [IsNoetherianRing B] in
/-- The extension factors the supplied original map exactly. -/
theorem completionToComplete_comp_baseMap :
    (completionToComplete R A f).comp (completionBaseMap R A).hom = f := by
  have hbase : completionBaseMap R A ≫ CommRingCat.ofHom (completionToComplete R A f) =
      CommRingCat.ofHom f := by
    apply (imageRingCoconeIsColimit R A).hom_ext
    intro i
    change CommRingCat.ofHom (image R A i).val.toRingHom ≫
        (completionBaseMap R A ≫ CommRingCat.ofHom (completionToComplete R A f)) =
      CommRingCat.ofHom (image R A i).val.toRingHom ≫ CommRingCat.ofHom f
    have hb : CommRingCat.ofHom (image R A i).val.toRingHom ≫ completionBaseMap R A =
        CommRingCat.ofHom (algebraMap (image R A i) (completionStage R A i)) ≫
          (completionCocone R A).ι.app i := completionBaseMap_fac R A i
    apply ((Category.assoc (CommRingCat.ofHom (image R A i).val.toRingHom)
      (completionBaseMap R A) (CommRingCat.ofHom (completionToComplete R A f))).symm.trans
        (congrArg (fun a => a ≫ CommRingCat.ofHom (completionToComplete R A f)) hb)).trans
    apply (Category.assoc
      (CommRingCat.ofHom (algebraMap (image R A i) (completionStage R A i)))
      ((completionCocone R A).ι.app i) (CommRingCat.ofHom (completionToComplete R A f))).trans
    apply (congrArg
      (fun a => CommRingCat.ofHom (algebraMap (image R A i) (completionStage R A i)) ≫ a)
      (completionToComplete_fac R A f i)).trans
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact completionStageToComplete_algebraMap R A f i a
  exact congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of B => g.hom) hbase

/-- Localness follows from actual stage representatives and the constructed local stage maps. -/
instance completionToComplete_isLocalHom : IsLocalHom (completionToComplete R A f) := by
  constructor
  intro x hx
  have hrep : ∃ (i : FGSubalgebra R A) (b : completionStage R A i),
      (completionCocone R A).ι.app i b = x := by
    exact Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat.{u}) (completionCoconeIsColimit R A)) x
  obtain ⟨i, b, rfl⟩ := hrep
  have hu : IsUnit (completionStageToComplete R A f i b) :=
    (ConcreteCategory.congr_hom (completionToComplete_fac R A f i) b) ▸ hx
  exact (isUnit_of_map_unit (completionStageToComplete R A f i) b hu).map
    ((completionCocone R A).ι.app i).hom

omit [IsNoetherianRing B] in
/-- Local maps from the constructed colimit into a complete local ring are
determined by their restriction to the original henselian ring. -/
theorem completionLocalHom_ext (g h : completionColimit R A →+* B)
    [IsLocalHom g] [IsLocalHom h]
    (heq : g.comp (completionBaseMap R A).hom =
      h.comp (completionBaseMap R A).hom) : g = h := by
  have hstage (i : FGSubalgebra R A) :
      g.comp ((completionCocone R A).ι.app i).hom =
        h.comp ((completionCocone R A).ι.app i).hom := by
    have hι : IsLocalHom ((completionCocone R A).ι.app i).hom :=
      completionCocone_isLocalHom R A i
    have hg : IsLocalHom (g.comp ((completionCocone R A).ι.app i).hom) :=
      ⟨fun x hx => isUnit_of_map_unit ((completionCocone R A).ι.app i).hom x
        (isUnit_of_map_unit g _ hx)⟩
    have hh : IsLocalHom (h.comp ((completionCocone R A).ι.app i).hom) :=
      ⟨fun x hx => isUnit_of_map_unit ((completionCocone R A).ι.app i).hom x
        (isUnit_of_map_unit h _ hx)⟩
    apply AdicCompletion.localHom_ext
    apply RingHom.ext
    intro a
    have ha := ConcreteCategory.congr_hom (completionBaseMap_fac R A i) a
    exact (congrArg g ha).symm.trans
      ((RingHom.congr_fun heq (a : A)).trans (congrArg h ha))
  apply RingHom.ext
  intro x
  obtain ⟨i, b, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) (completionCoconeIsColimit R A)) x
  exact RingHom.congr_fun (hstage i) b

/-- The constructed extension is the unique local extension of the given map. -/
theorem completionToComplete_unique (g : completionColimit R A →+* B)
    [IsLocalHom g] (hg : g.comp (completionBaseMap R A).hom = f) :
    g = completionToComplete R A f :=
  completionLocalHom_ext R A g (completionToComplete R A f)
    (hg.trans (completionToComplete_comp_baseMap R A f).symm)

/-- Further local maps of complete targets preserve the actual extension;
there is no new choice of maps on the completed stages. -/
theorem completionToComplete_comp
    {D : Type u} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (g : B →+* D) [IsLocalHom g] :
    g.comp (completionToComplete R A f) = completionToComplete R A (g.comp f) := by
  apply completionToComplete_unique
  rw [RingHom.comp_assoc, completionToComplete_comp_baseMap]

end AlgebraicGeometry.HenselianNoetherianImageStages
