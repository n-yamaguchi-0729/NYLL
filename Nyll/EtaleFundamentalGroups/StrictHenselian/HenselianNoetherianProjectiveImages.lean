/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianClosedFiberModels
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange

/-!
# Closed projective image stages over the actual henselian subalgebras

The original closed embedding over `A` is placed in the fixed projective
ambient model over `R` using the existing projective-space base-change
isomorphism. Every scheme-theoretic image stage is then embedded in the
projective space over its own actual henselian image ring. The original
structure maps and native closed-fiber cover are preserved.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.HenselianNoetherianImageStages

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

/-- The original embedding in the fixed projective model after the actual base change. -/
def projectiveAmbientEmbedding :
    Y ⟶ (SubalgebraImageApproximation.ambientCone (images R A) (ProjSpace.π R n)).pt :=
  j ≫ (ProjSpace.isPullback_map R A n).isoPullback.hom

instance [IsClosedImmersion j] :
    IsClosedImmersion (projectiveAmbientEmbedding R A n j) := by
  dsimp only [projectiveAmbientEmbedding]
  infer_instance

/-- The fixed ambient construction has the literal original projective structure map. -/
theorem projectiveAmbientEmbedding_base :
    originalSchemeBaseMap R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) =
      j ≫ ProjSpace.π A n := by
  change (j ≫ (ProjSpace.isPullback_map R A n).isoPullback.hom) ≫ _ = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]

/-- The actual image scheme diagram attached to the original closed projective family. -/
abbrev projectiveImageDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} :=
  schemeDiagram R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)

/-- The actual original family is the vertex of the image cone. -/
abbrev projectiveImageCone : Cone (projectiveImageDiagram R A n j) :=
  schemeCone R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)

/-- The images of the original closed projective family recover that original family. -/
def projectiveImageConeIsLimit [IsClosedImmersion j] :
    IsLimit (projectiveImageCone R A n j) :=
  schemeConeIsLimit R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)

/-- A stage image embeds into projective space over the actual stage ring. -/
def projectiveImageEmbedding (i : (FGSubalgebra R A)ᵒᵖ) :
    (projectiveImageDiagram R A n j).obj i ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (image R A i.unop)) :=
  AffineTransitionImage.inclusion
    (SubalgebraImageApproximation.ambientDiagram (images R A) (ProjSpace.π R n))
    (SubalgebraImageApproximation.ambientCone (images R A) (ProjSpace.π R n))
    (projectiveAmbientEmbedding R A n j) i ≫
      (ProjSpace.isPullback_map R (image R A i.unop) n).isoPullback.inv

instance (i : (FGSubalgebra R A)ᵒᵖ) :
    IsClosedImmersion (projectiveImageEmbedding R A n j i) := by
  dsimp only [projectiveImageEmbedding]
  infer_instance

/-- The stage closed embedding retains the actual image structure map. -/
theorem projectiveImageEmbedding_base (i : (FGSubalgebra R A)ᵒᵖ) :
    projectiveImageEmbedding R A n j i ≫ ProjSpace.π (image R A i.unop) n =
      schemeBaseMap R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i := by
  dsimp only [projectiveImageEmbedding]
  rw [Category.assoc, IsPullback.isoPullback_inv_snd]
  rfl

/-- The original projection to each image retains the original inclusion of the stage ring. -/
@[reassoc]
theorem projectiveImageCone_projection_base (i : (FGSubalgebra R A)ᵒᵖ) :
    (projectiveImageCone R A n j).π.app i ≫
        (projectiveImageEmbedding R A n j i ≫ ProjSpace.π (image R A i.unop) n) =
      (j ≫ ProjSpace.π A n) ≫ Spec.map (CommRingCat.ofHom (image R A i.unop).val.toRingHom) := by
  rw [projectiveImageEmbedding_base]
  have h := SubalgebraImageApproximation.cone_projection_baseMap
    (images R A) (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i
  change (projectiveImageCone R A n j).π.app i ≫
      schemeBaseMap R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i =
    (j ≫ ProjSpace.π A n) ≫ _
  calc
    (projectiveImageCone R A n j).π.app i ≫
        schemeBaseMap R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i =
      originalSchemeBaseMap R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) ≫
        Spec.map (CommRingCat.ofHom (image R A i.unop).val.toRingHom) := by
          simpa only [originalSchemeBaseMap, Category.assoc] using h
    _ = (j ≫ ProjSpace.π A n) ≫ _ := by rw [projectiveAmbientEmbedding_base]

/-- The actual image scheme is Noetherian over its actual henselian Noetherian image ring. -/
theorem projectiveImageStage_isNoetherian [IsNoetherianRing R]
    (i : (FGSubalgebra R A)ᵒᵖ) :
    IsNoetherian ((projectiveImageDiagram R A n j).obj i) :=
  schemeStage_isNoetherian R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i

/-- The original native closed fiber is identified with the same fiber
in the fixed ambient model. -/
def projectiveClosedFiberIso :
    pullback (j ≫ ProjSpace.π A n)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
      closedFiber R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) :=
  closedFiberSourceIso R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)
    (j ≫ ProjSpace.π A n) (projectiveAmbientEmbedding_base R A n j)

/-- The actual original projective closed fiber maps to the native image-stage fiber. -/
def projectiveClosedFiberStageMap (i : (FGSubalgebra R A)ᵒᵖ) :
    pullback (j ≫ ProjSpace.π A n)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ⟶
      stageClosedFiber R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i :=
  closedFiberStageMapOfBaseEq R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)
    (j ≫ ProjSpace.π A n) (projectiveAmbientEmbedding_base R A n j) i

/-- Every finite étale cover of the original closed fiber descends to an
actual native image-stage closed fiber of the constructed projective models. -/
theorem exists_projectiveImage_closedFiber_finiteEtale_model [IsClosedImmersion j]
    (V : FiniteEtale (pullback (j ≫ ProjSpace.π A n)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) :
    ∃ (i : (FGSubalgebra R A)ᵒᵖ)
      (W : FiniteEtale
        (stageClosedFiber R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j) i)),
      Nonempty ((FiniteEtale.pullback (projectiveClosedFiberStageMap R A n j i)).obj W ≅ V) :=
  exists_native_closedFiber_finiteEtale_model_of_base_eq
    R A (ProjSpace.π R n) (projectiveAmbientEmbedding R A n j)
    (j ≫ ProjSpace.π A n) (projectiveAmbientEmbedding_base R A n j) V

end AlgebraicGeometry.HenselianNoetherianImageStages
