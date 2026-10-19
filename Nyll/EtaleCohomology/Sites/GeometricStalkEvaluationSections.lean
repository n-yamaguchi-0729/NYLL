/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkNeighborhoodMaps
import Nyll.EtaleCohomology.Sites.ProperClosedFieldSections
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Evaluation of proper strict-local sections in the geometric field

The actual evaluation of the constructed geometric-stalk ring gives a native
Cartesian map from the geometric fibre to the strictly local base change.
Proper closed-field H⁰ makes pullback on global sections bijective. The
chosen inverse-image composition isomorphism and literal projection equality
identify its target with the original inverse-image sheaf on the geometric
fibre, without any additional comparison assumption.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual evaluation map on the source base changes. -/
def geometricStalkEvaluationBaseChangeMap :
    pullback (Spec.map (CommRingCat.ofHom φ)) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f :=
  pullback.lift
    (pullback.fst (Spec.map (CommRingCat.ofHom φ)) f ≫
      Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))))
    (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => pullback.fst (Spec.map (CommRingCat.ofHom φ)) f ≫ a)
        (geometricStalkEvaluation_structure φ)).trans pullback.condition))

theorem geometricStalkEvaluationBaseChangeMap_fst :
    geometricStalkEvaluationBaseChangeMap φ f ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f =
    pullback.fst (Spec.map (CommRingCat.ofHom φ)) f ≫
      Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))) :=
  pullback.lift_fst _ _ _

theorem geometricStalkEvaluationBaseChangeMap_snd :
    geometricStalkEvaluationBaseChangeMap φ f ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f =
    pullback.snd (Spec.map (CommRingCat.ofHom φ)) f :=
  pullback.lift_snd _ _ _

/-- The source evaluation map is the actual base change of the ring
evaluation, as a literal Cartesian square. -/
theorem geometricStalkEvaluationBaseChangeMap_isPullback :
    IsPullback (geometricStalkEvaluationBaseChangeMap φ f)
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) f)
      (pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
      (Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))) := by
  let t := Spec.map (CommRingCat.ofHom φ)
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let e := Spec.map (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ)))
  let m := geometricStalkEvaluationBaseChangeMap φ f
  have hm : m ≫ pullback.snd h f = pullback.snd t f :=
    geometricStalkEvaluationBaseChangeMap_snd φ f
  have he : e ≫ h = t := geometricStalkEvaluation_structure φ
  have houter : IsPullback (m ≫ pullback.snd h f) (pullback.fst t f) f (e ≫ h) := by
    rw [hm, he]
    exact (IsPullback.of_hasPullback t f).flip
  exact houter.of_right (geometricStalkEvaluationBaseChangeMap_fst φ f)
    (IsPullback.of_hasPullback h f).flip

variable (Λ : Type u) [CommRing Λ]

/-- The canonical comparison from iterated inverse image along evaluation
to the original inverse image on the geometric fibre. -/
def etaleGeometricStalkEvaluationPullbackIso :
    etalePullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ ⋙
      etalePullback (geometricStalkEvaluationBaseChangeMap φ f) Λ ≅
    etalePullback (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ :=
  (etalePullbackCompIso (geometricStalkEvaluationBaseChangeMap φ f)
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ).symm ≪≫
    eqToIso (congrArg (fun q => etalePullback q Λ)
      (geometricStalkEvaluationBaseChangeMap_snd φ f))

/-- Transport an actual section map through a natural isomorphism of
module-sheaf functors, evaluated at the specified étale object. -/
def etaleSectionMapThroughIso
    {S T : Scheme.{u}}
    {L M : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (e : L ≅ M) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) (U : S.Etale)
    {A : ModuleCat.{u} Λ} (a : A ⟶ (L.obj F).obj.obj (op U)) :
    A ⟶ (M.obj F).obj.obj (op U) :=
  a ≫ (e.hom.app F).hom.app (op U)

/-- Actual evaluation of sections after strictly local base change, with
target the original sheaf on the actual geometric fibre. -/
def etaleGeometricStalkEvaluationSections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etalePullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
        Λ).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 _))) ⟶
    ((etalePullback (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 _))) :=
  etaleSectionMapThroughIso Λ (etaleGeometricStalkEvaluationPullbackIso φ f Λ) F
    (Scheme.Etale.mk (𝟙 _))
    (etalePullbackGlobalSectionsMap (geometricStalkEvaluationBaseChangeMap φ f) Λ
      ((etalePullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ).obj F))

private theorem evaluationGlobalSections_bijective
    [IsSepClosed Ω] [IsProper f]
    (G : Sheaf
      (pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f).smallEtaleTopology
      (ModuleCat.{u} Λ)) :
    Function.Bijective
      (etalePullbackGlobalSectionsMap (geometricStalkEvaluationBaseChangeMap φ f) Λ G) := by
  let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let ε : H →+* Ω := (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
  have : HenselianLocalRing H :=
    geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ))
  have : IsSepClosed (IsLocalRing.ResidueField H) :=
    geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ))
  have : IsLocalHom ε := geometricStalkEvaluation_isLocalHom (Spec.map (CommRingCat.ofHom φ))
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let t := Spec.map (CommRingCat.ofHom φ)
  let fH : pullback h f ⟶ Spec (CommRingCat.of H) := pullback.fst h f
  have : IsProper fH := inferInstanceAs (IsProper (pullback.fst h f))
  exact etaleClosedField_globalSections_bijective_of_isPullback H ε fH
    (geometricStalkEvaluationBaseChangeMap φ f) (pullback.fst t f)
    (geometricStalkEvaluationBaseChangeMap_isPullback φ f) Λ G

private theorem sheafIso_app_bijective
    {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (e : F ≅ G) (U : S.Etale) : Function.Bijective (e.hom.hom.app (op U)) := by
  let E := ((sheafSections S.smallEtaleTopology (ModuleCat.{u} Λ)).obj (op U)).mapIso e
  exact ConcreteCategory.bijective_of_isIso E.hom

private theorem sectionsThroughNatIso_bijective
    {S T : Scheme.{u}}
    {L M : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (e : L ≅ M) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) (U : S.Etale)
    {A : ModuleCat.{u} Λ} (a : A ⟶ (L.obj F).obj.obj (op U))
    (ha : Function.Bijective a) :
    Function.Bijective (etaleSectionMapThroughIso Λ e F U a) :=
  (sheafIso_app_bijective Λ (e.app F) U).comp ha

/-- Properness makes the actual evaluation from strictly local sections
to geometric-fibre sections bijective for arbitrary coefficient sheaves. -/
theorem etaleGeometricStalkEvaluationSections_bijective
    [IsSepClosed Ω] [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etaleGeometricStalkEvaluationSections φ f Λ F) := by
  exact sectionsThroughNatIso_bijective Λ
    (etaleGeometricStalkEvaluationPullbackIso φ f Λ) F (Scheme.Etale.mk (𝟙 _))
    (etalePullbackGlobalSectionsMap (geometricStalkEvaluationBaseChangeMap φ f) Λ
      ((etalePullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ).obj F))
    (evaluationGlobalSections_bijective φ f Λ
      ((etalePullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) Λ).obj F))

end EtaleCohomology
