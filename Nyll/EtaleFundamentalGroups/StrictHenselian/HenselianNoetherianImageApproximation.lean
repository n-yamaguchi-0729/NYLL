/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageResidue
public import Nyll.SchemeTheory.Descent.NoetherianImageResidueLimit
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual proper image models over the henselian Noetherian stages

A closed subscheme of the base change of a fixed proper model is recovered
from its images over the constructed henselian Noetherian subalgebras.
The generic image and residue-fiber limit proofs are reused. Transport of
the limit vertex retains the native residue quotient of the original ring.
Thus a finite étale cover of the actual original closed fiber descends to
an actual proper Noetherian henselian image stage.

No finite-presentation assumption is imposed on the original closed
subscheme. General proper families additionally require the projective
modification and effective descent steps; they are not asserted here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of R))
variable {Z : Scheme.{u}}
  (j : Z ⟶ (SubalgebraImageApproximation.ambientCone (images R A) f₀).pt)

/-- The actual image schemes over the actual henselian image rings. -/
abbrev schemeDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} :=
  SubalgebraImageApproximation.diagram (images R A) f₀ j

/-- The actual cone from the original closed subscheme. -/
abbrev schemeCone : Cone (schemeDiagram R A f₀ j) :=
  SubalgebraImageApproximation.cone (images R A) f₀ j

/-- The structure map to the actual henselian image ring of the same stage. -/
abbrev schemeBaseMap (i : (FGSubalgebra R A)ᵒᵖ) :
    (schemeDiagram R A f₀ j).obj i ⟶ Spec (CommRingCat.of (image R A i.unop)) :=
  SubalgebraImageApproximation.baseMap (images R A) f₀ j i

/-- The constructed image stages are proper over their original henselian rings. -/
instance [IsProper f₀] (i : (FGSubalgebra R A)ᵒᵖ) :
    IsProper (schemeBaseMap R A f₀ j i) :=
  inferInstanceAs (IsProper
    (SubalgebraImageApproximation.baseMap (images R A) f₀ j i))

/-- The actual image schemes are Noetherian, with no Noetherian assumption on `A`. -/
theorem schemeStage_isNoetherian [IsNoetherianRing R] [IsProper f₀]
    (i : (FGSubalgebra R A)ᵒᵖ) :
    IsNoetherian ((schemeDiagram R A f₀ j).obj i) := by
  have : IsNoetherianRing (image R A i.unop) := image_isNoetherianRing R A i.unop
  exact SubalgebraImageApproximation.stage_isNoetherian (images R A) f₀ j i

/-- The actual original closed subscheme is the limit of its constructed stages. -/
def schemeConeIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (schemeCone R A f₀ j) :=
  SubalgebraImageApproximation.coneIsLimit (images R A) f₀ j (exhaustive R A)

/-- The original structure map, before taking any image stage. -/
abbrev originalSchemeBaseMap : Z ⟶ Spec (CommRingCat.of A) :=
  j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := R) (A := A))

/-- The original closed fiber uses the native local-ring residue quotient. -/
abbrev closedFiber : Scheme.{u} :=
  pullback (originalSchemeBaseMap R A f₀ j)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))

theorem residueVertexSpecMap_base :
    Spec.map (imageResidueVertexIso R A).hom ≫
        SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
  rw [SubalgebraStages.residueSpecBaseTop, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  let e := maximalQuotientResidueEquiv (IsLocalRing.maximalIdeal A)
  change e.symm (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a
  apply e.injective
  rw [e.apply_symm_apply]
  exact (RingHom.congr_fun
    (maximalQuotientResidueEquiv_comp_quotient (IsLocalRing.maximalIdeal A)) a).symm

/-- The canonical residue-field identification on the actual original fiber. -/
def closedFiberResidueIso :
    closedFiber R A f₀ j ≅
      SubalgebraImageApproximation.originalResidueFiber
        (images R A) f₀ j (IsLocalRing.maximalIdeal A) :=
  asIso (pullback.map _ _ _ _ (𝟙 Z) (Spec.map (imageResidueVertexIso R A).hom)
    (𝟙 (Spec (CommRingCat.of A)))
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, residueVertexSpecMap_base]))

@[reassoc]
lemma closedFiberResidueIso_hom_fst :
    (closedFiberResidueIso R A f₀ j).hom ≫
        pullback.fst (originalSchemeBaseMap R A f₀ j)
          (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A)) =
      pullback.fst (originalSchemeBaseMap R A f₀ j)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
  dsimp only [closedFiberResidueIso, asIso_hom]
  rw [pullback.lift_fst, Category.comp_id]

/-- The actual original closed fiber maps to the actual residue fibers of the images. -/
def closedFiberCone : Cone
    (SubalgebraImageApproximation.residueFiberDiagram
      (images R A) f₀ j (IsLocalRing.maximalIdeal A)) :=
  (SubalgebraImageApproximation.residueFiberCone
    (images R A) f₀ j (IsLocalRing.maximalIdeal A)).extend
      (closedFiberResidueIso R A f₀ j).hom

/-- The original native closed fiber is the limit of the actual henselian image fibers. -/
def closedFiberConeIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (closedFiberCone R A f₀ j) :=
  IsLimit.extendIso
    (s := SubalgebraImageApproximation.residueFiberCone
      (images R A) f₀ j (IsLocalRing.maximalIdeal A))
    (closedFiberResidueIso R A f₀ j).hom
    (SubalgebraImageApproximation.residueFiberConeIsLimit
      (images R A) f₀ j (IsLocalRing.maximalIdeal A) (exhaustive R A))

/-- The limit comparison retains the original closed-fiber inclusion and image projections. -/
@[reassoc]
theorem closedFiberCone_projection_fst (i : (FGSubalgebra R A)ᵒᵖ) :
    (closedFiberCone R A f₀ j).π.app i ≫
        pullback.fst (schemeBaseMap R A f₀ j i)
          (SubalgebraStages.residueSpecBase (images R A) (IsLocalRing.maximalIdeal A) i) =
      pullback.fst (originalSchemeBaseMap R A f₀ j)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          (schemeCone R A f₀ j).π.app i := by
  change ((closedFiberResidueIso R A f₀ j).hom ≫
    SubalgebraImageApproximation.residueFiberLeg
      (images R A) f₀ j (IsLocalRing.maximalIdeal A) i) ≫ _ = _
  rw [Category.assoc, SubalgebraImageApproximation.residueFiberLeg_fst,
    closedFiberResidueIso_hom_fst_assoc]

/-- An actual finite étale closed-fiber cover descends to one constructed image fiber.
The recovery is along the literal native finite-étale pullback functor. -/
theorem exists_closedFiber_finiteEtale_model [IsProper f₀] [IsClosedImmersion j]
    (V : FiniteEtale (closedFiber R A f₀ j)) :
    ∃ (i : (FGSubalgebra R A)ᵒᵖ)
      (W : FiniteEtale
        (SubalgebraImageApproximation.residueFiberObj
          (images R A) f₀ j (IsLocalRing.maximalIdeal A) i)),
      Nonempty ((FiniteEtale.pullback ((closedFiberCone R A f₀ j).π.app i)).obj W ≅ V) :=
  FiniteEtale.exists_inverse_limit_model
    (SubalgebraImageApproximation.residueFiberDiagram
      (images R A) f₀ j (IsLocalRing.maximalIdeal A))
    (closedFiberCone R A f₀ j) (closedFiberConeIsLimit R A f₀ j) V

end AlgebraicGeometry.HenselianNoetherianImageStages
