/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The actual projective closed embedding after coefficient change

Pasting the original closed embedding with the projective structure
morphism identifies the literal coefficient pullback with the pullback
of the embedding. The canonical projective-space base-change
isomorphism then gives an actual closed embedding into projective space
over the new coefficient ring.

The two original structure maps, coordinate inverse-image cover, and
pulled back twisting line are retained by explicit comparisons. No
identification of either scheme or line bundle is additional data.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
  {Y : Scheme.{u}} (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))

/-- The actual map to projective space over the new coefficient ring,
constructed from the original pullback pasting isomorphism. -/
def closedImmersionBaseChangeMap :
    Limits.pullback (j ≫ π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) := by
  let σ : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let X : Scheme.{u} := Limits.pullback (j ≫ π R n) σ
  let Z : Scheme.{u} := Limits.pullback (π R n) σ
  let W : Scheme.{u} := Limits.pullback j (Limits.pullback.fst (π R n) σ)
  let e : W ≅ X := pullbackRightPullbackFstIso (π R n) σ j
  let b : W ⟶ Z := Limits.pullback.snd j (Limits.pullback.fst (π R n) σ)
  let a : P ≅ Z := (isPullback_map R A n).isoPullback
  exact e.inv ≫ b ≫ a.inv

/-- The map retains the original projection to the projective space
above the original coefficient ring. -/
theorem closedImmersionBaseChangeMap_comp_map :
    closedImmersionBaseChangeMap R A n j ≫ map R A n =
      Limits.pullback.fst (j ≫ π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ j := by
  let σ : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let Pₐ : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let X : Scheme.{u} := Limits.pullback (j ≫ π R n) σ
  let Z : Scheme.{u} := Limits.pullback (π R n) σ
  let a : X ⟶ Limits.pullback j (Limits.pullback.fst (π R n) σ) :=
    (pullbackRightPullbackFstIso (π R n) σ j).inv
  let b : Limits.pullback j (Limits.pullback.fst (π R n) σ) ⟶ Z :=
    Limits.pullback.snd j (Limits.pullback.fst (π R n) σ)
  let e : Pₐ ≅ Z := (isPullback_map R A n).isoPullback
  let p : X ⟶ Y := Limits.pullback.fst (j ≫ π R n) σ
  change (a ≫ b ≫ e.inv) ≫ map R A n = p ≫ j
  calc
    (a ≫ b ≫ e.inv) ≫ map R A n = a ≫ b ≫ (e.inv ≫ map R A n) := by
      simp only [Category.assoc]
    _ = a ≫ b ≫ Limits.pullback.fst (π R n) σ :=
      congrArg (fun t : Z ⟶ P => a ≫ b ≫ t) (isPullback_map R A n).isoPullback_inv_fst
    _ = p ≫ j := pullbackRightPullbackFstIso_inv_snd_fst (π R n) σ j

/-- The map retains the original structural second projection to
spectrum of the new coefficient ring. -/
theorem closedImmersionBaseChangeMap_comp_π :
    closedImmersionBaseChangeMap R A n j ≫ π A n =
      Limits.pullback.snd (j ≫ π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let σ : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let Pₐ : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let X : Scheme.{u} := Limits.pullback (j ≫ π R n) σ
  let Z : Scheme.{u} := Limits.pullback (π R n) σ
  let a : X ⟶ Limits.pullback j (Limits.pullback.fst (π R n) σ) :=
    (pullbackRightPullbackFstIso (π R n) σ j).inv
  let b : Limits.pullback j (Limits.pullback.fst (π R n) σ) ⟶ Z :=
    Limits.pullback.snd j (Limits.pullback.fst (π R n) σ)
  let e : Pₐ ≅ Z := (isPullback_map R A n).isoPullback
  let q : X ⟶ Spec (.of A) := Limits.pullback.snd (j ≫ π R n) σ
  change (a ≫ b ≫ e.inv) ≫ π A n = q
  calc
    (a ≫ b ≫ e.inv) ≫ π A n = a ≫ b ≫ (e.inv ≫ π A n) := by
      simp only [Category.assoc]
    _ = a ≫ b ≫ Limits.pullback.snd (π R n) σ :=
      congrArg (fun t : Z ⟶ Spec (.of A) => a ≫ b ≫ t)
        (isPullback_map R A n).isoPullback_inv_snd
    _ = q := pullbackRightPullbackFstIso_inv_snd_snd (π R n) σ j

/-- The coefficient pullback of the original closed embedding is
still an actual closed embedding into projective space. -/
instance isClosedImmersion_closedImmersionBaseChangeMap [IsClosedImmersion j] :
    IsClosedImmersion (closedImmersionBaseChangeMap R A n j) := by
  dsimp only [closedImmersionBaseChangeMap]
  infer_instance

/-- The original first projection is affine because the coefficient
change is a morphism between affine spectra. -/
theorem closedImmersionBaseChangeProjection_isAffineHom :
    IsAffineHom (Limits.pullback.fst (j ≫ π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{u})
    (self := isAffineHom_isStableUnderBaseChange)
    (IsPullback.of_hasPullback (j ≫ π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).flip
    (isAffineHom_of_isAffine (Spec.map (CommRingCat.ofHom (algebraMap R A))))

attribute [local instance] closedImmersionBaseChangeProjection_isAffineHom

/-- The actual coordinate cover after coefficient change is the
coordinate cover pulled back through the original first projection. -/
theorem closedImmersionBaseChangeMap_cover [IsClosedImmersion j] :
    stdCoverPullback (A := A) (n := n) (closedImmersionBaseChangeMap R A n j) =
      stdCoverPullback (A := R) (n := n)
        (Limits.pullback.fst (j ≫ π R n)
          (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ j) := by
  dsimp only [stdCoverPullback]
  congr 1
  funext i
  let σ : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  let Pₐ : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let X : Scheme.{u} := Limits.pullback (j ≫ π R n) σ
  let p : X ⟶ Y := Limits.pullback.fst (j ≫ π R n) σ
  let b : X ⟶ Pₐ := closedImmersionBaseChangeMap R A n j
  let U : P.Opens := (stdCover R n).U i
  change b ⁻¹ᵁ (stdCover A n).U i = (p ≫ j) ⁻¹ᵁ U
  calc
    b ⁻¹ᵁ (stdCover A n).U i = b ⁻¹ᵁ (map R A n ⁻¹ᵁ U) :=
      congrArg (fun V : Pₐ.Opens => b ⁻¹ᵁ V)
        (map_preimage_basicOpen_X R A n i.down).symm
    _ = (b ≫ map R A n) ⁻¹ᵁ U := (Scheme.Hom.comp_preimage b (map R A n) U).symm
    _ = (p ≫ j) ⁻¹ᵁ U :=
      congrArg (fun g : X ⟶ P => g ⁻¹ᵁ U) (closedImmersionBaseChangeMap_comp_map R A n j)

/-- The new twisting line pulls back to the original twisting line
pulled back through the original closed embedding and first projection. -/
def closedImmersionBaseChangeTwistingIso :
    (Scheme.Modules.pullback (closedImmersionBaseChangeMap R A n j)).obj
        (twistingSheaf A n) ≅
      (Scheme.Modules.pullback (Limits.pullback.fst (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj
          ((Scheme.Modules.pullback j).obj (twistingSheaf R n)) :=
  (Scheme.Modules.pullback (closedImmersionBaseChangeMap R A n j)).mapIso
      (twistingSheafBaseChangeIso R A n).symm ≪≫
    (pullbackComp (closedImmersionBaseChangeMap R A n j) (map R A n)).app
      (twistingSheaf R n) ≪≫
    (pullbackCongr (closedImmersionBaseChangeMap_comp_map R A n j)).app (twistingSheaf R n) ≪≫
    ((pullbackComp (Limits.pullback.fst (j ≫ π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) j).app (twistingSheaf R n)).symm

end AlgebraicGeometry.ProjSpace
