/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.PointSections
import Mathlib.Algebra.Algebra.Hom
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Changing the coefficient ring of a finite étale point

A base-linear map of coefficient rings acts on points by precomposition
with its spectrum morphism. This construction is natural in the cover,
respects composition of coefficient maps, and agrees with postcomposition
on the actual section-algebra homomorphisms.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H A B : Type u) [CommRing H] [CommRing A] [CommRing B]
  [Algebra H A] [Algebra H B]

/-- Change of coefficients on actual over-points, using the original
spectrum morphism of the supplied algebra homomorphism. -/
def pointHomBaseChange (σ : A →ₐ[H] B) (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H A) ⟶ X.toComma) :
    Over.mk (Spec.algebraMap H B) ⟶ X.toComma :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) (by
    have hb : CommRingCat.ofHom (algebraMap H A) ≫ CommRingCat.ofHom σ.toRingHom =
        CommRingCat.ofHom (algebraMap H B) :=
      CommRingCat.hom_ext σ.comp_algebraMap
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k : Spec (.of A) ⟶ Spec (.of H) =>
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ k) x.w).trans
          ((Spec.map_comp (CommRingCat.ofHom (algebraMap H A))
            (CommRingCat.ofHom σ.toRingHom)).symm.trans
              (congrArg (fun k : CommRingCat.of H ⟶ CommRingCat.of B => Spec.map k) hb))))

/-- Actual coefficient change commutes with morphisms of finite étale covers. -/
theorem pointHomBaseChange_naturality (σ : A →ₐ[H] B)
    {X Y : FiniteEtale (Spec (.of H))} (f : X ⟶ Y)
    (x : Over.mk (Spec.algebraMap H A) ⟶ X.toComma) :
    pointHomBaseChange H A B σ Y (x ≫ f.hom) =
      pointHomBaseChange H A B σ X x ≫ f.hom := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (x.left ≫ f.left) =
    (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) ≫ f.left
  exact (Category.assoc _ _ _).symm

/-- Successive coefficient changes equal the coefficient change for the
composite algebra map, as actual scheme-valued points. -/
theorem pointHomBaseChange_comp
    (C : Type u) [CommRing C] [Algebra H C]
    (σ : A →ₐ[H] B) (τ : B →ₐ[H] C)
    (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H A) ⟶ X.toComma) :
    pointHomBaseChange H B C τ X (pointHomBaseChange H A B σ X x) =
      pointHomBaseChange H A C (τ.comp σ) X x := by
  have hcomp : τ.toRingHom.comp σ.toRingHom = (τ.comp σ).toRingHom := by
    apply RingHom.ext
    intro a
    exact (AlgHom.comp_apply τ σ a).symm
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) =
    Spec.map (CommRingCat.ofHom (τ.comp σ).toRingHom) ≫ x.left
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

/-- Under the section-algebra correspondence, changing the coefficient
ring is postcomposition with the specified algebra map. -/
theorem pointHomAlgEquiv_pointHomBaseChange (σ : A →ₐ[H] B)
    (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H A) ⟶ X.toComma) :
    pointHomAlgEquiv H B X (pointHomBaseChange H A B σ X x) =
      σ.comp (pointHomAlgEquiv H A X x) := by
  apply AlgHom.coe_ringHom_injective
  refine congrArg (fun k : Γ(X.left, ⊤) ⟶ CommRingCat.of B => k.hom) ?_
  apply Spec.map_injective
  calc
    Spec.map (CommRingCat.ofHom
        (pointHomAlgEquiv H B X (pointHomBaseChange H A B σ X x)).toRingHom) =
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left) ≫ X.left.isoSpec.hom :=
      pointHomAlgEquiv_specMap H B X (pointHomBaseChange H A B σ X x)
    _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (x.left ≫ X.left.isoSpec.hom) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (pointHomAlgEquiv H A X x).toRingHom) :=
      congrArg (fun k : Spec (.of A) ⟶ Spec Γ(X.left, ⊤) =>
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ k)
        (pointHomAlgEquiv_specMap H A X x).symm
    _ = Spec.map (CommRingCat.ofHom
        (σ.comp (pointHomAlgEquiv H A X x)).toRingHom) :=
      (Spec.map_comp (CommRingCat.ofHom (pointHomAlgEquiv H A X x).toRingHom)
        (CommRingCat.ofHom σ.toRingHom)).symm

end AlgebraicGeometry.FiniteEtale
