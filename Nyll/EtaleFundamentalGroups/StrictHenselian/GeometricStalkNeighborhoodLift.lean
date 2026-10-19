/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.Etale.HenselianLocalGeometricLift
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The strict local spectrum maps to its actual étale neighborhoods

The spectrum of the existing geometric stalk has a unique pointed lift to
each étale neighborhood. Strict Henselianity constructs this lift, including
for non-affine neighborhoods. An affine pointed refinement proves that its
map on sections is exactly the original colimit germ map.

Consequently any field-valued point of this strict local spectrum supplies
compatible new points on the original neighborhoods. This is the geometric
input for the composition of specializations in Stacks Project, Lemma
58.16.2, https://stacks.math.columbia.edu/tag/0BUP.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

/-- Each actual pointed neighborhood has a unique compatible morphism
from the strict local spectrum. -/
theorem existsUnique_geometricStalkNeighborhoodLift
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    ∃! l : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ W.left,
      l ≫ W.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ∧
      Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫ l =
        w.left := by
  apply Etale.existsUnique_lift_of_closedFieldPoint
    (geometricStalk (Spec.map (CommRingCat.ofHom φ))) W.hom
    (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
    (Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))))
    ?_ w.left ?_
  · rw [Spec.map_apply]
    exact (congrArg (PrimeSpectrum.comap
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom)
        (Subsingleton.elim _ (closedPoint Ω))).trans (comap_closedPoint _)
  · have hw : w.left ≫ W.hom = Spec.map (CommRingCat.ofHom φ) := Over.w w
    have he : CommRingCat.ofHom (geometricStalkStructureMap φ) ≫
        geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)) = CommRingCat.ofHom φ :=
      congrArg CommRingCat.ofHom (geometricStalkStructureMap_evaluation φ)
    exact hw.trans ((congrArg Spec.map he.symm).trans (Spec.map_comp _ _))

/-- The actual map from the strict local spectrum to a pointed étale
neighborhood of the given geometric point. -/
def geometricStalkNeighborhoodLift
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ W.left :=
  (existsUnique_geometricStalkNeighborhoodLift φ W w).choose

/-- The neighborhood lift is a morphism over the original affine scheme. -/
theorem geometricStalkNeighborhoodLift_comp
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    geometricStalkNeighborhoodLift φ W w ≫ W.hom =
      Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) :=
  (existsUnique_geometricStalkNeighborhoodLift φ W w).choose_spec.1.1

/-- Evaluation at the original geometric point recovers its specified
point on the neighborhood. -/
theorem geometricStalkNeighborhoodLift_evaluation
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) ≫
      geometricStalkNeighborhoodLift φ W w = w.left :=
  (existsUnique_geometricStalkNeighborhoodLift φ W w).choose_spec.1.2

/-- The maps from the strict local spectrum commute with every morphism
of pointed étale neighborhoods. -/
theorem geometricStalkNeighborhoodLift_naturality
    {W V : (Spec (.of R)).Etale} (g : W ⟶ V)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    geometricStalkNeighborhoodLift φ W w ≫ g.left =
      geometricStalkNeighborhoodLift φ V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.map g w) := by
  apply (existsUnique_geometricStalkNeighborhoodLift φ V
    ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.map g w)).unique
  · constructor
    · have hg : g.left ≫ V.hom = W.hom := MorphismProperty.Over.w g
      calc
        (geometricStalkNeighborhoodLift φ W w ≫ g.left) ≫ V.hom =
            geometricStalkNeighborhoodLift φ W w ≫ (g.left ≫ V.hom) := Category.assoc _ _ _
        _ = geometricStalkNeighborhoodLift φ W w ≫ W.hom :=
          congrArg (fun a : W.left ⟶ Spec (.of R) =>
            geometricStalkNeighborhoodLift φ W w ≫ a) hg
        _ = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) :=
          geometricStalkNeighborhoodLift_comp φ W w
    · exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun a : Spec (.of Ω) ⟶ W.left => a ≫ g.left)
          (geometricStalkNeighborhoodLift_evaluation φ W w))
  · exact ⟨geometricStalkNeighborhoodLift_comp φ V _,
      geometricStalkNeighborhoodLift_evaluation φ V _⟩

private theorem geometricStalkNeighborhoodLift_appTop_of_isAffine
    (W : (Spec (.of R)).Etale) [IsAffine W.left]
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    (geometricStalkNeighborhoodLift φ W w).appTop ≫
        (Scheme.ΓSpecIso (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).hom =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W w := by
  let p : Spec (.of Ω) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  let H : CommRingCat.{u} := geometricStalk p
  let γ : Γ(W.left, ⊤) ⟶ H := geometricStalkGerm p W w
  let q : Spec H ⟶ W.left := Spec.map γ ≫ W.left.isoSpec.inv
  have he : W.left.isoSpec.inv.appTop ≫
      (Scheme.ΓSpecIso Γ(W.left, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]
  have hqγ : q.appTop ≫ (Scheme.ΓSpecIso H).hom = γ := by
    change (Spec.map γ ≫ W.left.isoSpec.inv).appTop ≫ _ = γ
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, he, Category.id_comp]
  have hbase : q ≫ W.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) := by
    apply ext_to_Spec
    apply (cancel_mono (Scheme.ΓSpecIso H).hom).mp
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (q ≫ W.hom).appTop) ≫
        (Scheme.ΓSpecIso H).hom =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))).appTop) ≫
          (Scheme.ΓSpecIso H).hom
    have hs := congrArg CommRingCat.ofHom (geometricStalkGerm_comp_structure φ W w)
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ W.hom.appTop) ≫ γ =
      CommRingCat.ofHom (geometricStalkStructureMap φ) at hs
    simpa only [Scheme.Hom.comp_appTop, Category.assoc, hqγ,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc] using hs
  have hpoint : Spec.map (geometricStalkEvaluation p) ≫ q = w.left := by
    let wHom : Spec (.of Ω) ⟶ W.left := w.left
    let ε : H ⟶ CommRingCat.of Ω := geometricStalkEvaluation p
    have hApps : (Spec.map ε ≫ q).appTop = wHom.appTop := by
      apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).mp
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        ← Category.assoc, hqγ]
      exact geometricStalkGerm_evaluation p W w
    apply (cancel_mono W.left.toSpecΓ).mp
    exact (Scheme.toSpecΓ_naturality (Spec.map ε ≫ q)).trans
      ((congrArg (fun a : Γ(W.left, ⊤) ⟶ Γ(Spec (.of Ω), ⊤) =>
        (Spec (.of Ω)).toSpecΓ ≫ Spec.map a) hApps).trans
          (Scheme.toSpecΓ_naturality wHom).symm)
  have hq : q = geometricStalkNeighborhoodLift φ W w :=
    (existsUnique_geometricStalkNeighborhoodLift φ W w).unique
      ⟨hbase, hpoint⟩ ⟨geometricStalkNeighborhoodLift_comp φ W w,
        geometricStalkNeighborhoodLift_evaluation φ W w⟩
  rw [← hq]
  exact hqγ

/-- The actual neighborhood lift induces exactly the original colimit
germ map on sections, including when the neighborhood is not affine. -/
theorem geometricStalkNeighborhoodLift_appTop
    (W : (Spec (.of R)).Etale)
    (w : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj W) :
    (geometricStalkNeighborhoodLift φ W w).appTop ≫
        (Scheme.ΓSpecIso (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).hom =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W w := by
  obtain ⟨V, v, g, hV, hv⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) W w
  let : IsAffine V.left := hV
  have hg := geometricStalkNeighborhoodLift_naturality φ g v
  rw [hv] at hg
  rw [← hg, Scheme.Hom.comp_appTop, Category.assoc,
    geometricStalkNeighborhoodLift_appTop_of_isAffine]
  have hγ := (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w g v (etaleSections (Spec (.of R)))
  rw [hv] at hγ
  exact hγ

end EtaleFundamentalGroups.StrictHenselian
