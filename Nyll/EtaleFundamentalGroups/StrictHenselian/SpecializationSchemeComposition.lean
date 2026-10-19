/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFunctoriality
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Stalk

/-!
# The strict local diagram of a chosen geometric specialization

The map on geometric stalks induced by an affine scheme morphism preserves
the actual base-ring structure maps. Applying this to the ordinary stalk
map of a specialization and to the chosen field-valued lift constructs a
map between the two strict local models over the original scheme.

Its evaluation is the chosen lift, rather than a new choice of geometric
specialization. This is the strict-local-ring diagram in the proof of
Stacks Project, Lemma 58.16.2:
https://stacks.math.columbia.edu/tag/0BUP.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The map on geometric stalks of an affine scheme morphism extends the
original ring map. The proof compares the germ of the identity neighborhood
with its actual pullback and the ordinary structure germ there. -/
theorem geometricStalkMap_affine_comp_structure
    {R A Ω Ψ : Type u} [CommRing R] [CommRing A] [Field Ω] [Field Ψ]
    (f : R →+* A) (s : A →+* Ω) (t : R →+* Ψ) (ι : Ψ →+* Ω)
    (h : Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom t)) :
    (geometricStalkMap (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom s)) (Spec.map (CommRingCat.ofHom t)) ι h).hom.comp
        (geometricStalkStructureMap t) = (geometricStalkStructureMap s).comp f := by
  let F : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)
  let sPoint : Spec (.of Ω) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom s)
  let tPoint : Spec (.of Ψ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom t)
  let M : geometricStalk tPoint ⟶ geometricStalk sPoint :=
    geometricStalkMap F sPoint tPoint ι h
  let W : (Spec (.of R)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let w : (Scheme.pointEtaleNeighborhoods tPoint).fiber.obj W :=
    Over.homMk tPoint (Category.comp_id _)
  let P : (Spec (.of A)).Etale := Scheme.Etale.mk (pullback.snd (𝟙 (Spec (.of R))) F)
  let wp : (Scheme.pointEtaleNeighborhoods sPoint).fiber.obj P :=
    pointedEtalePullback F sPoint tPoint ι h W w
  let p : P.left ⟶ Spec (.of R) := pullback.fst (𝟙 (Spec (.of R))) F
  let q : P.left ⟶ Spec (.of A) := pullback.snd (𝟙 (Spec (.of R))) F
  let γR : Γ(Spec (.of R), ⊤) ⟶ geometricStalk tPoint := geometricStalkGerm tPoint W w
  let γP : Γ(P.left, ⊤) ⟶ geometricStalk sPoint := geometricStalkGerm sPoint P wp
  let aR : CommRingCat.of R ⟶ Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let aA : CommRingCat.of A ⟶ Γ(Spec (.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv
  have hGerm : γR ≫ M = p.appTop ≫ γP := geometricStalkGerm_map F sPoint tPoint ι h W w
  have hp : p = q ≫ F :=
    (Category.comp_id p).symm.trans (pullback.condition (f := 𝟙 (Spec (.of R))) (g := F))
  have hNat : aR ≫ F.appTop = CommRingCat.ofHom f ≫ aA :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm
  have hStructure : (aA ≫ q.appTop) ≫ γP = CommRingCat.ofHom (geometricStalkStructureMap s) :=
    congrArg CommRingCat.ofHom (geometricStalkGerm_comp_structure s P wp)
  have hcat : (aR ≫ γR) ≫ M =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (geometricStalkStructureMap s) := by
    rw [Category.assoc, hGerm, hp, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Category.assoc, hNat, Category.assoc, Category.assoc]
    exact congrArg (fun a : CommRingCat.of A ⟶ geometricStalk sPoint =>
      CommRingCat.ofHom f ≫ a) ((Category.assoc _ _ _).symm.trans hStructure)
  exact congrArg CommRingCat.Hom.hom hcat

/-- The originally chosen geometric lift extends to a map between the
actual strict local models at the two points. Its evaluation and its map
to the original scheme are both retained. -/
theorem exists_localGeometricStalk_map_of_specializationLift
    {S : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [IsSepClosed Ωs] [Field Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (h : t (closedPoint Ωt) ⤳ s (closedPoint Ωs))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* Ωt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint Ωs)) t h).hom) :
    ∃ a : geometricStalk
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)),
      a ≫ geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo t).hom)) = CommRingCat.ofHom ψ ∧
      a.hom.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
        (geometricStalkStructureMap (Scheme.stalkClosedPointTo t).hom).comp
          (S.presheaf.stalkSpecializes h).hom ∧
      Spec.map a ≫ localGeometricStalkToScheme s = localGeometricStalkToScheme t := by
  let R : CommRingCat.{u} := S.presheaf.stalk (s (closedPoint Ωs))
  let A : CommRingCat.{u} := S.presheaf.stalk (t (closedPoint Ωt))
  let f : R →+* A := (S.presheaf.stalkSpecializes h).hom
  let sr : R →+* Ωs := (Scheme.stalkClosedPointTo s).hom
  let ta : A →+* Ωt := (Scheme.stalkClosedPointTo t).hom
  let tr : R →+* Ωt := ta.comp f
  have hψ' : ψ.comp (geometricStalkStructureMap sr) = tr := hψ
  let δ : geometricStalk (Spec.map (CommRingCat.ofHom sr)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom tr)) :=
    geometricStalkSpecializationMap sr tr ψ hψ'
  have hSquare : Spec.map (CommRingCat.ofHom ta) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (RingHom.id Ωt)) ≫ Spec.map (CommRingCat.ofHom tr) := by
    change Spec.map (CommRingCat.ofHom ta) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (𝟙 (CommRingCat.of Ωt)) ≫ Spec.map (CommRingCat.ofHom tr)
    rw [Spec.map_id, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let β : geometricStalk (Spec.map (CommRingCat.ofHom tr)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom ta)) :=
    geometricStalkMap (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom ta)) (Spec.map (CommRingCat.ofHom tr)) (RingHom.id Ωt) hSquare
  let a : geometricStalk (Spec.map (CommRingCat.ofHom sr)) ⟶
      geometricStalk (Spec.map (CommRingCat.ofHom ta)) := δ ≫ β
  have hβEval : β ≫ geometricStalkEvaluation (Spec.map (CommRingCat.ofHom ta)) =
      geometricStalkEvaluation (Spec.map (CommRingCat.ofHom tr)) :=
    (geometricStalkMap_evaluation (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom ta)) (Spec.map (CommRingCat.ofHom tr))
      (RingHom.id Ωt) hSquare).trans (Category.comp_id _)
  have hEval : a ≫ geometricStalkEvaluation (Spec.map (CommRingCat.ofHom ta)) =
      CommRingCat.ofHom ψ := by
    change (δ ≫ β) ≫ geometricStalkEvaluation (Spec.map (CommRingCat.ofHom ta)) = _
    rw [Category.assoc, hβEval]
    exact geometricStalkSpecializationMap_evaluation sr tr ψ hψ'
  have hStructure : a.hom.comp (geometricStalkStructureMap sr) =
      (geometricStalkStructureMap ta).comp f := by
    change β.hom.comp (δ.hom.comp (geometricStalkStructureMap sr)) = _
    rw [geometricStalkSpecializationMap_comp_structure]
    exact geometricStalkMap_affine_comp_structure f ta tr (RingHom.id Ωt) hSquare
  refine ⟨a, hEval, hStructure, ?_⟩
  let cS : R ⟶ geometricStalk (Spec.map (CommRingCat.ofHom sr)) :=
    CommRingCat.ofHom (geometricStalkStructureMap sr)
  let cT : A ⟶ geometricStalk (Spec.map (CommRingCat.ofHom ta)) :=
    CommRingCat.ofHom (geometricStalkStructureMap ta)
  let fCat : R ⟶ A := CommRingCat.ofHom f
  let qS : Spec R ⟶ S := S.fromSpecStalk (s (closedPoint Ωs))
  let qT : Spec A ⟶ S := S.fromSpecStalk (t (closedPoint Ωt))
  have hcat : cS ≫ a = fCat ≫ cT :=
    congrArg CommRingCat.ofHom hStructure
  have hFrom : Spec.map fCat ≫ qS = qT :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  change Spec.map a ≫ (Spec.map cS ≫ qS) = Spec.map cT ≫ qT
  rw [← Category.assoc, ← Spec.map_comp, hcat, Spec.map_comp, Category.assoc, hFrom]

end EtaleFundamentalGroups.StrictHenselian
