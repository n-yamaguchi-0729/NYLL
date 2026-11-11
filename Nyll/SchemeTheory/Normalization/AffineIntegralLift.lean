/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.AffineFiniteEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Extending actual lifts to the original affine normalization

The universal property of relative normalization extends an actual point
of any integral cover to the literal integral closure. Uniqueness retains
the original generic lift and proves naturality for every original source
automorphism. No connectedness of the integral cover is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The extension to the literal integral closure of an actual lift to an
integral scheme over the same affine base. -/
def affineNormalizationLift {T : Scheme.{u}}
    (c : T ⟶ Spec (.of R)) [IsIntegralHom c]
    (w : Spec (.of B) ⟶ T) (hw : w ≫ c = affineStructureMap R B) :
    Spec (.of (integralClosure R B)) ⟶ T :=
  (specNormalizationIso R B).inv ≫
    (affineStructureMap R B).normalizationDesc w c hw.symm

/-- Extension preserves the original generic lift. -/
@[reassoc]
theorem affineNormalizationLift_generic {T : Scheme.{u}}
    (c : T ⟶ Spec (.of R)) [IsIntegralHom c]
    (w : Spec (.of B) ⟶ T) (hw : w ≫ c = affineStructureMap R B) :
    Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫
      affineNormalizationLift R B c w hw = w := by
  dsimp only [affineNormalizationLift]
  rw [← toNormalization_specNormalizationIso_hom R B, Category.assoc,
    Iso.hom_inv_id_assoc, Scheme.Hom.toNormalization_normalizationDesc]

/-- Extension retains the original structural morphism. -/
@[reassoc]
theorem affineNormalizationLift_comp {T : Scheme.{u}}
    (c : T ⟶ Spec (.of R)) [IsIntegralHom c]
    (w : Spec (.of B) ⟶ T) (hw : w ≫ c = affineStructureMap R B) :
    affineNormalizationLift R B c w hw ≫ c =
      Spec.algebraMap R (integralClosure R B) := by
  dsimp only [affineNormalizationLift]
  rw [Category.assoc, Scheme.Hom.normalizationDesc_comp,
    ← specNormalizationIso_hom_fromNormalization R B, Iso.inv_hom_id_assoc]

/-- The inclusion in the original ambient algebra detects morphisms from
the literal integral closure to an affine scheme. -/
theorem affineNormalization_hom_ext {T : Scheme.{u}} [IsAffine T]
    {f g : Spec (.of (integralClosure R B)) ⟶ T}
    (h : Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫ g) :
    f = g := by
  apply (cancel_epi (specNormalizationIso R B).hom).mp
  apply spec_toNormalization_hom_ext R B
  simpa only [← Category.assoc, toNormalization_specNormalizationIso_hom] using h

/-- A reduced ambient algebra also detects morphisms to any separated
target over the same base. This allows a generic equality of proper group
coordinates to be specialized without choosing a new finite cover. -/
theorem affineNormalization_hom_ext_of_isSeparated [_root_.IsReduced B]
    {T S : Scheme.{u}} (s : T ⟶ S) [IsSeparated s]
    {f g : Spec (.of (integralClosure R B)) ⟶ T}
    (hbase : f ≫ s = g ≫ s)
    (h : Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫ g) :
    f = g := by
  have : _root_.IsReduced (integralClosure R B) :=
    isReduced_of_injective (integralClosure R B).val Subtype.val_injective
  have : IsDominant
      (Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom)) := by
    rw [← toNormalization_specNormalizationIso_hom R B]
    infer_instance
  exact ext_of_isDominant_of_isSeparated s hbase
    (Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom)) h

/-- The original source automorphism and its integral-closure restriction
commute with the literal generic inclusion. -/
@[reassoc]
theorem affineNormalization_source_square (σ : B ≃ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.mapIntegralClosure.toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (integralClosure R B).val.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- Every integral-cover extension is natural for the original source
automorphism; the two proofs of being over the affine base are immaterial. -/
theorem affineNormalizationLift_source {T : Scheme.{u}}
    (c : T ⟶ Spec (.of R)) [IsIntegralHom c]
    (w w' : Spec (.of B) ⟶ T)
    (hw : w ≫ c = affineStructureMap R B)
    (hw' : w' ≫ c = affineStructureMap R B)
    (σ : B ≃ₐ[R] B)
    (hσ : w' = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ w) :
    affineNormalizationLift R B c w' hw' =
      Spec.map (CommRingCat.ofHom σ.mapIntegralClosure.toRingHom) ≫
        affineNormalizationLift R B c w hw := by
  have : IsAffine T := isAffine_of_isAffineHom c
  apply affineNormalization_hom_ext R B
  rw [affineNormalizationLift_generic, ← Category.assoc,
    affineNormalization_source_square, Category.assoc,
    affineNormalizationLift_generic]
  exact hσ

end AlgebraicGeometry
