/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNeighborhoodLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.SchemeTheory.Etale.HenselianLocalSection
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Rigidity with a geometric stalk over a different base

Two maps from an affine geometric stalk to an arbitrary geometric stalk
are equal if they agree on the original base ring and have the same
evaluation in the target pointing field. Neither localness of the maps
nor separable closure of the target pointing field is assumed.

The proof compares their maps to every original pointed étale neighborhood.
These are two maps from the same local spectrum with the same base map
and closed field-valued point. Their open equalizer contains the closed
point and hence the whole local spectrum, proving equality on germs.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Structure and evaluation determine a map even when the target stalk
belongs to a different base scheme. -/
theorem geometricStalk_hom_ext_of_structure_evaluation
    {R Ω Ψ : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    [Field Ψ] {T : Scheme.{u}}
    (s : R →+* Ω) (t : Spec (.of Ψ) ⟶ T)
    (F G : geometricStalk (Spec.map (CommRingCat.ofHom s)) ⟶ geometricStalk t)
    (hbase : F.hom.comp (geometricStalkStructureMap s) =
      G.hom.comp (geometricStalkStructureMap s))
    (hevaluation : F ≫ geometricStalkEvaluation t = G ≫ geometricStalkEvaluation t) :
    F = G := by
  apply (Scheme.pointEtaleNeighborhoods
    (Spec.map (CommRingCat.ofHom s))).presheafFiber_hom_ext
  intro W w
  change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ F =
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ G
  let Hs : CommRingCat.{u} := geometricStalk (Spec.map (CommRingCat.ofHom s))
  let Ht : CommRingCat.{u} := geometricStalk t
  let l : Spec Hs ⟶ W.left := geometricStalkNeighborhoodLift s W w
  let b : Spec Ht ⟶ Spec (.of R) :=
    Spec.map F ≫ Spec.map (CommRingCat.ofHom (geometricStalkStructureMap s))
  let j : Spec (.of Ψ) ⟶ Spec Ht := Spec.map (geometricStalkEvaluation t)
  have hj : j default = closedPoint Ht := by
    change Spec.map (geometricStalkEvaluation t) default = closedPoint (geometricStalk t)
    rw [Spec.map_apply]
    exact (congrArg (PrimeSpectrum.comap (geometricStalkEvaluation t).hom)
      (Subsingleton.elim _ (closedPoint Ψ))).trans (comap_closedPoint _)
  have hF : (Spec.map F ≫ l) ≫ W.hom = b := by
    change (Spec.map F ≫ geometricStalkNeighborhoodLift s W w) ≫ W.hom = _
    rw [Category.assoc, geometricStalkNeighborhoodLift_comp]
    rfl
  have hG : (Spec.map G ≫ l) ≫ W.hom = b := by
    have hcat : CommRingCat.ofHom (geometricStalkStructureMap s) ≫ F =
        CommRingCat.ofHom (geometricStalkStructureMap s) ≫ G :=
      congrArg CommRingCat.ofHom hbase
    change (Spec.map G ≫ geometricStalkNeighborhoodLift s W w) ≫ W.hom =
      Spec.map F ≫ Spec.map (CommRingCat.ofHom (geometricStalkStructureMap s))
    rw [Category.assoc, geometricStalkNeighborhoodLift_comp]
    exact (Spec.map_comp (CommRingCat.ofHom (geometricStalkStructureMap s)) G).symm.trans
      ((congrArg Spec.map hcat.symm).trans
        (Spec.map_comp (CommRingCat.ofHom (geometricStalkStructureMap s)) F))
  have hpoint : j ≫ (Spec.map F ≫ l) = j ≫ (Spec.map G ≫ l) := by
    change Spec.map (geometricStalkEvaluation t) ≫ (Spec.map F ≫ l) =
      Spec.map (geometricStalkEvaluation t) ≫ (Spec.map G ≫ l)
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, hevaluation]
  have hl : Spec.map F ≫ l = Spec.map G ≫ l :=
    @Etale.localSource_hom_ext_of_closedPoint (geometricStalk t) inferInstance
      (geometricStalk_isLocalRing t) W.left (Spec (.of R)) W.hom inferInstance inferInstance
      (Spec.map F ≫ l) (Spec.map G ≫ l) (hF.trans hG.symm)
      (Spec (.of Ψ)) j default hj hpoint
  have hsections (K : Hs ⟶ Ht) :
      geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ K =
        (Spec.map K ≫ l).appTop ≫ (Scheme.ΓSpecIso Ht).hom := by
    change geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ K =
      (Spec.map K ≫ geometricStalkNeighborhoodLift s W w).appTop ≫
        (Scheme.ΓSpecIso Ht).hom
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, geometricStalkNeighborhoodLift_appTop]
  calc
    geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ F =
        (Spec.map F ≫ l).appTop ≫ (Scheme.ΓSpecIso Ht).hom := hsections F
    _ = (Spec.map G ≫ l).appTop ≫ (Scheme.ΓSpecIso Ht).hom :=
      congrArg (fun q : Spec Ht ⟶ W.left => q.appTop ≫ (Scheme.ΓSpecIso Ht).hom) hl
    _ = geometricStalkGerm (Spec.map (CommRingCat.ofHom s)) W w ≫ G :=
      (hsections G).symm

end EtaleFundamentalGroups.StrictHenselian
