/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianClosedFiberModels
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.NatIso

/-!
# The native closed-fiber diagram over actual henselian image stages

The actual native residue fields identify the existing residue-fiber diagram
with a diagram of the native closed fibers of the proper image schemes.
Its affine transitions retain the actual closed-fiber inclusions, and its
limit cone has the original native closed fiber as vertex. The existing
finite-etale inverse-limit Hom, equality and isomorphism theorems therefore
apply directly to the native covers and the constructed stage maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of R))
variable {Z : Scheme.{u}}
  (j : Z ⟶ (SubalgebraImageApproximation.ambientCone (images R A) f₀).pt)

/-- The actual native closed fibers, with transitions transported through
their canonical residue-field comparisons. -/
@[reducible] def nativeClosedFiberDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} where
  obj i := stageClosedFiber R A f₀ j i
  map {i k} h := (stageClosedFiberResidueIso R A f₀ j i).hom ≫
    (SubalgebraImageApproximation.residueFiberDiagram
      (images R A) f₀ j (IsLocalRing.maximalIdeal A)).map h ≫
        (stageClosedFiberResidueIso R A f₀ j k).inv
  map_id i := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  map_comp h h' := by
    rw [(SubalgebraImageApproximation.residueFiberDiagram
      (images R A) f₀ j (IsLocalRing.maximalIdeal A)).map_comp h h']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The native diagram and the already constructed residue diagram agree
through the actual residue-field identifications at every stage. -/
def nativeClosedFiberDiagramIso :
    nativeClosedFiberDiagram R A f₀ j ≅
      SubalgebraImageApproximation.residueFiberDiagram
        (images R A) f₀ j (IsLocalRing.maximalIdeal A) :=
  NatIso.ofComponents (stageClosedFiberResidueIso R A f₀ j)
    (fun h => by
      dsimp only [nativeClosedFiberDiagram]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Each native transition lies over the actual transition of the image schemes. -/
@[reassoc]
theorem nativeClosedFiberDiagram_map_fst {i k : (FGSubalgebra R A)ᵒᵖ}
    (h : i ⟶ k) :
    (nativeClosedFiberDiagram R A f₀ j).map h ≫
        pullback.fst (schemeBaseMap R A f₀ j k)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A k.unop)))) =
      pullback.fst (schemeBaseMap R A f₀ j i)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))) ≫
          (schemeDiagram R A f₀ j).map h := by
  change ((stageClosedFiberResidueIso R A f₀ j i).hom ≫
    SubalgebraImageApproximation.residueFiberTrans
      (images R A) f₀ j (IsLocalRing.maximalIdeal A) h ≫
        (stageClosedFiberResidueIso R A f₀ j k).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, stageClosedFiberResidueIso_inv_fst,
    SubalgebraImageApproximation.residueFiberTrans_fst,
    stageClosedFiberResidueIso_hom_fst_assoc]

/-- The native closed-fiber inclusions form an actual morphism of the two diagrams. -/
def nativeClosedFiberFst :
    nativeClosedFiberDiagram R A f₀ j ⟶ schemeDiagram R A f₀ j where
  app i := pullback.fst (schemeBaseMap R A f₀ j i)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop))))
  naturality _ _ h := nativeClosedFiberDiagram_map_fst R A f₀ j h

instance {i k : (FGSubalgebra R A)ᵒᵖ} (h : i ⟶ k) :
    IsAffineHom ((nativeClosedFiberDiagram R A f₀ j).map h) :=
  inferInstanceAs (IsAffineHom ((stageClosedFiberResidueIso R A f₀ j i).hom ≫
    (SubalgebraImageApproximation.residueFiberDiagram
      (images R A) f₀ j (IsLocalRing.maximalIdeal A)).map h ≫
        (stageClosedFiberResidueIso R A f₀ j k).inv))

instance [IsProper f₀] (i : (FGSubalgebra R A)ᵒᵖ) :
    CompactSpace ((nativeClosedFiberDiagram R A f₀ j).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd (schemeBaseMap R A f₀ j i)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))))

instance [IsProper f₀] (i : (FGSubalgebra R A)ᵒᵖ) :
    QuasiSeparatedSpace ((nativeClosedFiberDiagram R A f₀ j).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd (schemeBaseMap R A f₀ j i)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A i.unop)))))

/-- The original native closed fiber and the previously constructed actual
stage maps form a cone over the native closed fibers. -/
def nativeClosedFiberCone : Cone (nativeClosedFiberDiagram R A f₀ j) :=
  (Cone.postcompose (nativeClosedFiberDiagramIso R A f₀ j).inv).obj
    (closedFiberCone R A f₀ j)

theorem nativeClosedFiberCone_projection (i : (FGSubalgebra R A)ᵒᵖ) :
    (nativeClosedFiberCone R A f₀ j).π.app i = closedFiberStageMap R A f₀ j i := rfl

/-- The morphism of cones is the original native closed-fiber inclusion. -/
theorem nativeClosedFiberCone_fst (i : (FGSubalgebra R A)ᵒᵖ) :
    (nativeClosedFiberCone R A f₀ j).π.app i ≫
        (nativeClosedFiberFst R A f₀ j).app i =
      pullback.fst (originalSchemeBaseMap R A f₀ j)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          (schemeCone R A f₀ j).π.app i :=
  closedFiberStageMap_fst R A f₀ j i

/-- The original native closed fiber is the limit of the native stage closed fibers. -/
def nativeClosedFiberConeIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (nativeClosedFiberCone R A f₀ j) :=
  (IsLimit.postcomposeInvEquiv (nativeClosedFiberDiagramIso R A f₀ j)
    (closedFiberCone R A f₀ j)).symm (closedFiberConeIsLimit R A f₀ j)

/-- The cone retaining a literal original structure map at its native closed-fiber vertex. -/
def nativeClosedFiberConeOfBaseEq (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) :
    Cone (nativeClosedFiberDiagram R A f₀ j) :=
  (nativeClosedFiberCone R A f₀ j).extend (closedFiberSourceIso R A f₀ j f hf).hom

theorem nativeClosedFiberConeOfBaseEq_projection (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) (i : (FGSubalgebra R A)ᵒᵖ) :
    (nativeClosedFiberConeOfBaseEq R A f₀ j f hf).π.app i =
      closedFiberStageMapOfBaseEq R A f₀ j f hf i := rfl

/-- The retained original structure map gives the literal native closed-fiber
inclusion as the map between the two actual cones. -/
theorem nativeClosedFiberConeOfBaseEq_fst (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) (i : (FGSubalgebra R A)ᵒᵖ) :
    (nativeClosedFiberConeOfBaseEq R A f₀ j f hf).π.app i ≫
        (nativeClosedFiberFst R A f₀ j).app i =
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        (schemeCone R A f₀ j).π.app i := by
  rw [nativeClosedFiberConeOfBaseEq_projection]
  exact closedFiberStageMapOfBaseEq_fst R A f₀ j f hf i

/-- The native closed-fiber cone with the retained original structure map is limiting. -/
def nativeClosedFiberConeOfBaseEqIsLimit [IsProper f₀] [IsClosedImmersion j]
    (f : Z ⟶ Spec (CommRingCat.of A))
    (hf : originalSchemeBaseMap R A f₀ j = f) :
    IsLimit (nativeClosedFiberConeOfBaseEq R A f₀ j f hf) := by
  let e : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
      (nativeClosedFiberCone R A f₀ j).pt := closedFiberSourceIso R A f₀ j f hf
  exact IsLimit.extendIso (s := nativeClosedFiberCone R A f₀ j)
    e.hom (nativeClosedFiberConeIsLimit R A f₀ j)

end AlgebraicGeometry.HenselianNoetherianImageStages
