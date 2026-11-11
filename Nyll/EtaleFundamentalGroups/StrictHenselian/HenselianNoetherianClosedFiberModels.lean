/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageApproximation
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity

/-!
# Native closed-fiber models over actual henselian image stages

The residue field used by the generic subalgebra limit is canonically the
native local-ring residue field of each actual image stage. This comparison
transports the constructed finite étale model while preserving its actual
closed-fiber inclusion and the projection from the original scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.HenselianNoetherianImageStages

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of R))
variable {Z : Scheme.{u}}
  (j : Z ⟶ (SubalgebraImageApproximation.ambientCone (images R A) f₀).pt)

/-- The native closed fiber of an actual henselian image stage. -/
abbrev stageClosedFiber (i : (FGSubalgebra R A)ᵒᵖ) : Scheme.{u} :=
  pullback (schemeBaseMap R A f₀ j i)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop))))

private theorem stageResidueSpecMap_base (i : (FGSubalgebra R A)ᵒᵖ) :
    Spec.map (imageResidueFieldEquiv R A i.unop).toCommRingCatIso.hom ≫
        SubalgebraStages.residueSpecBase (images R A) (IsLocalRing.maximalIdeal A) i =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop))) := by
  rw [SubalgebraStages.residueSpecBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact imageResidueFieldEquiv_algebraMap R A i.unop a

/-- The actual stage fiber comparison retains the original residue maps. -/
def stageClosedFiberResidueIso (i : (FGSubalgebra R A)ᵒᵖ) :
    stageClosedFiber R A f₀ j i ≅
      SubalgebraImageApproximation.residueFiberObj
        (images R A) f₀ j (IsLocalRing.maximalIdeal A) i :=
  asIso (pullback.map _ _ _ _ (𝟙 ((schemeDiagram R A f₀ j).obj i))
    (Spec.map (imageResidueFieldEquiv R A i.unop).toCommRingCatIso.hom)
    (𝟙 (Spec (CommRingCat.of (image R A i.unop))))
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, stageResidueSpecMap_base]))

@[reassoc]
lemma stageClosedFiberResidueIso_hom_fst (i : (FGSubalgebra R A)ᵒᵖ) :
    (stageClosedFiberResidueIso R A f₀ j i).hom ≫
        pullback.fst (schemeBaseMap R A f₀ j i)
          (SubalgebraStages.residueSpecBase (images R A) (IsLocalRing.maximalIdeal A) i) =
      pullback.fst (schemeBaseMap R A f₀ j i)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))) := by
  dsimp only [stageClosedFiberResidueIso, asIso_hom]
  rw [pullback.lift_fst, Category.comp_id]

@[reassoc]
lemma stageClosedFiberResidueIso_inv_fst (i : (FGSubalgebra R A)ᵒᵖ) :
    (stageClosedFiberResidueIso R A f₀ j i).inv ≫
        pullback.fst (schemeBaseMap R A f₀ j i)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))) =
      pullback.fst (schemeBaseMap R A f₀ j i)
        (SubalgebraStages.residueSpecBase (images R A) (IsLocalRing.maximalIdeal A) i) := by
  rw [← stageClosedFiberResidueIso_hom_fst R A f₀ j i, Iso.inv_hom_id_assoc]

/-- The actual original closed fiber maps to each native stage closed fiber. -/
def closedFiberStageMap (i : (FGSubalgebra R A)ᵒᵖ) :
    closedFiber R A f₀ j ⟶ stageClosedFiber R A f₀ j i :=
  (closedFiberCone R A f₀ j).π.app i ≫ (stageClosedFiberResidueIso R A f₀ j i).inv

/-- The native closed-fiber projections still lie over the original image projections. -/
@[reassoc]
theorem closedFiberStageMap_fst (i : (FGSubalgebra R A)ᵒᵖ) :
    closedFiberStageMap R A f₀ j i ≫
        pullback.fst (schemeBaseMap R A f₀ j i)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))) =
      pullback.fst (originalSchemeBaseMap R A f₀ j)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          (schemeCone R A f₀ j).π.app i := by
  let t : closedFiber R A f₀ j ⟶
      SubalgebraImageApproximation.residueFiberObj
        (images R A) f₀ j (IsLocalRing.maximalIdeal A) i :=
    (closedFiberCone R A f₀ j).π.app i
  let e := stageClosedFiberResidueIso R A f₀ j i
  let q := pullback.fst (schemeBaseMap R A f₀ j i)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop))))
  change (t ≫ e.inv) ≫ q = _
  exact (Category.assoc t e.inv q).trans
    ((congrArg (fun a : SubalgebraImageApproximation.residueFiberObj
        (images R A) f₀ j (IsLocalRing.maximalIdeal A) i ⟶
          (schemeDiagram R A f₀ j).obj i => t ≫ a)
      (stageClosedFiberResidueIso_inv_fst R A f₀ j i)).trans
        (closedFiberCone_projection_fst R A f₀ j i))

/-- The descended cover lives on the native closed fiber of an actual
proper henselian image stage and recovers the given original cover. -/
theorem exists_native_closedFiber_finiteEtale_model [IsProper f₀] [IsClosedImmersion j]
    (V : FiniteEtale (closedFiber R A f₀ j)) :
    ∃ (i : (FGSubalgebra R A)ᵒᵖ) (W : FiniteEtale (stageClosedFiber R A f₀ j i)),
      Nonempty ((FiniteEtale.pullback (closedFiberStageMap R A f₀ j i)).obj W ≅ V) := by
  obtain ⟨i, W, ⟨e⟩⟩ := exists_closedFiber_finiteEtale_model R A f₀ j V
  let h := closedFiberStageMap R A f₀ j i
  let g := (stageClosedFiberResidueIso R A f₀ j i).hom
  have hw : (closedFiberCone R A f₀ j).π.app i = h ≫ g := by
    let t : closedFiber R A f₀ j ⟶
        SubalgebraImageApproximation.residueFiberObj
          (images R A) f₀ j (IsLocalRing.maximalIdeal A) i :=
      (closedFiberCone R A f₀ j).π.app i
    let E := stageClosedFiberResidueIso R A f₀ j i
    change t = (t ≫ E.inv) ≫ E.hom
    exact ((Category.assoc t E.inv E.hom).trans
      ((congrArg (fun a : SubalgebraImageApproximation.residueFiberObj
          (images R A) f₀ j (IsLocalRing.maximalIdeal A) i ⟶
            SubalgebraImageApproximation.residueFiberObj
              (images R A) f₀ j (IsLocalRing.maximalIdeal A) i => t ≫ a)
        E.inv_hom_id).trans (Category.comp_id t))).symm
  let c : FiniteEtale.pullback ((closedFiberCone R A f₀ j).π.app i) ≅
      FiniteEtale.pullback g ⋙ FiniteEtale.pullback h :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      h g ((closedFiberCone R A f₀ j).π.app i) hw
  exact ⟨i, (FiniteEtale.pullback g).obj W, ⟨(c.app W).symm ≪≫ e⟩⟩

/-- An actual equality of original structure maps identifies the same native closed fiber. -/
def closedFiberSourceIso (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) :
    pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
      closedFiber R A f₀ j :=
  pullback.congrHom hf.symm rfl

@[reassoc]
lemma closedFiberSourceIso_hom_fst (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) :
    (closedFiberSourceIso R A f₀ j f hf).hom ≫
        pullback.fst (originalSchemeBaseMap R A f₀ j)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
  dsimp only [closedFiberSourceIso]
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

/-- The actual residue-fiber cone with the original structure map retained at its vertex. -/
def closedFiberConeOfBaseEq (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) : Cone
      (SubalgebraImageApproximation.residueFiberDiagram
        (images R A) f₀ j (IsLocalRing.maximalIdeal A)) :=
  (closedFiberCone R A f₀ j).extend (closedFiberSourceIso R A f₀ j f hf).hom

/-- The original closed fiber with its literal structure morphism is the actual limit. -/
def closedFiberConeOfBaseEqIsLimit [IsProper f₀] [IsClosedImmersion j]
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f) :
    IsLimit (closedFiberConeOfBaseEq R A f₀ j f hf) := by
  let e : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
      (closedFiberCone R A f₀ j).pt := closedFiberSourceIso R A f₀ j f hf
  exact IsLimit.extendIso (s := closedFiberCone R A f₀ j)
    e.hom (closedFiberConeIsLimit R A f₀ j)

/-- The stage projection with the original structure map retained as its source. -/
def closedFiberStageMapOfBaseEq (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) (i : (FGSubalgebra R A)ᵒᵖ) :
    pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ⟶
      stageClosedFiber R A f₀ j i :=
  (closedFiberSourceIso R A f₀ j f hf).hom ≫ closedFiberStageMap R A f₀ j i

/-- The native stage projection is compatible with the original closed-fiber inclusion. -/
@[reassoc]
theorem closedFiberStageMapOfBaseEq_fst (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) (i : (FGSubalgebra R A)ᵒᵖ) :
    closedFiberStageMapOfBaseEq R A f₀ j f hf i ≫
        pullback.fst (schemeBaseMap R A f₀ j i)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        (schemeCone R A f₀ j).π.app i := by
  rw [closedFiberStageMapOfBaseEq, Category.assoc, closedFiberStageMap_fst,
    closedFiberSourceIso_hom_fst_assoc]

/-- The actual descended cover recovers the given native closed-fiber cover
when the original structure map is retained through its proved base triangle. -/
theorem exists_native_closedFiber_finiteEtale_model_of_base_eq
    [IsProper f₀] [IsClosedImmersion j]
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (V : FiniteEtale (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) :
    ∃ (i : (FGSubalgebra R A)ᵒᵖ) (W : FiniteEtale (stageClosedFiber R A f₀ j i)),
      Nonempty ((FiniteEtale.pullback
        (closedFiberStageMapOfBaseEq R A f₀ j f hf i)).obj W ≅ V) := by
  let e := closedFiberSourceIso R A f₀ j f hf
  let V' := (FiniteEtale.pullback e.inv).obj V
  obtain ⟨i, W, ⟨hW⟩⟩ := exists_native_closedFiber_finiteEtale_model R A f₀ j V'
  let p := closedFiberStageMap R A f₀ j i
  let c : FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf i) ≅
      FiniteEtale.pullback p ⋙ FiniteEtale.pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom p (closedFiberStageMapOfBaseEq R A f₀ j f hf i) rfl
  let d : FiniteEtale.pullback (𝟙 _) ≅
      FiniteEtale.pullback e.inv ⋙ FiniteEtale.pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom e.inv (𝟙 _) e.hom_inv_id.symm
  exact ⟨i, W, ⟨c.app W ≪≫ (FiniteEtale.pullback e.hom).mapIso hW ≪≫
    (d.app V).symm ≪≫ (FiniteEtale.pullbackIdIso _).app V⟩⟩

end AlgebraicGeometry.HenselianNoetherianImageStages
