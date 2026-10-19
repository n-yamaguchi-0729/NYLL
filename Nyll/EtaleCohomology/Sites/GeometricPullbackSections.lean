/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.SeparablyClosedFieldStalks
import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Geometric stalks as sections of the actual inverse image

The actual inverse-image unit on stalks is invertible. At the identity
geometric point of the separably closed field, its target stalk is the
actual module of global sections. Their composite gives the canonical
isomorphism, and its value on each represented germ is the literal
pullback-section map through that neighborhood's geometric point.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem unit_stalkComponent_isIso_of_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) := by
  rcases s with ⟨s, rfl⟩
  exact etalePullbackUnit_stalkComponent_isIso q s Λ F

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ S) (Λ : Type u) [CommRing Λ]

/-- The canonical map from a geometric stalk to global sections of the
actual inverse image, built from the actual unit and identity geometric germ. -/
def etaleGeometricPullbackSections
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Scheme.pointSmallEtale t).sheafFiber.obj F ⟶
      ((etalePullback t Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _))) := by
  have : IsIso (etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of Ω))) Λ
      ((etalePullback t Λ).obj F)) :=
    etaleGlobalSectionsGerm_identity_isIso Ω Λ ((etalePullback t Λ).obj F)
  exact ((Scheme.pointSmallEtale t).sheafFiber.map
      ((etalePullbackPushforwardAdjunction t Λ).unit.app F) ≫
    etalePushforwardStalkComponent t t ⟨𝟙 _, Category.id_comp t⟩
      ((etalePullback t Λ).obj F)) ≫
    inv (etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of Ω))) Λ
      ((etalePullback t Λ).obj F))

/-- The canonical geometric-stalk section map is invertible for every
module sheaf, without any properness assumption. -/
theorem etaleGeometricPullbackSections_isIso
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (etaleGeometricPullbackSections t Λ F) := by
  have : IsIso (etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of Ω))) Λ
      ((etalePullback t Λ).obj F)) :=
    etaleGlobalSectionsGerm_identity_isIso Ω Λ ((etalePullback t Λ).obj F)
  have : IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
      ((etalePullbackPushforwardAdjunction t Λ).unit.app F) ≫
    etalePushforwardStalkComponent t t ⟨𝟙 _, Category.id_comp t⟩
      ((etalePullback t Λ).obj F)) :=
    unit_stalkComponent_isIso_of_lift t t ⟨𝟙 _, Category.id_comp t⟩ Λ F
  unfold etaleGeometricPullbackSections
  infer_instance

/-- On a represented germ, the canonical map is precisely the actual
pullback-section map through its geometric-point factor. -/
theorem toPresheafFiber_etaleGeometricPullbackSections
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : S.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale t).toPresheafFiber U v F.obj ≫
        etaleGeometricPullbackSections t Λ F =
      etalePullbackSectionMap t Λ F (U := Scheme.Etale.mk (𝟙 _)) (V := U) v.left
        (v.w.trans (Category.id_comp t).symm) := by
  let G := (etalePullback t Λ).obj F
  let H := (etalePushforward t Λ).obj G
  let Φ := Scheme.pointSmallEtale t
  let Ψ := Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))
  let T : (Spec (CommRingCat.of Ω)).Etale := Scheme.Etale.mk (𝟙 _)
  let B := (etaleBaseChange t).obj U
  let η : F ⟶ H := (etalePullbackPushforwardAdjunction t Λ).unit.app F
  let c : Φ.presheafFiber.obj H.obj ⟶ Ψ.presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent t t ⟨𝟙 _, Category.id_comp t⟩ G
  let γ : G.obj.obj (op T) ⟶ Ψ.presheafFiber.obj G.obj :=
    etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of Ω))) Λ G
  have : IsIso γ := etaleGlobalSectionsGerm_identity_isIso Ω Λ G
  let j : T ⟶ B := etaleBaseChangeLift t v.left
    (v.w.trans (Category.id_comp t).symm)
  let a₀ : Ψ.fiber.obj T := Over.homMk (𝟙 _) (Category.comp_id (𝟙 _))
  let b := etalePushforwardGeometricLift t t ⟨𝟙 _, Category.id_comp t⟩ U v
  have hj : Ψ.fiber.map j a₀ = b := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ j.left = j.left
    exact Category.id_comp _
  have hγ : G.obj.map j.op ≫ γ = Ψ.toPresheafFiber B b G.obj := by
    change G.obj.map j.op ≫ Ψ.toPresheafFiber T a₀ G.obj = _
    rw [Ψ.toPresheafFiber_w, hj]
  have hn : Φ.toPresheafFiber U v F.obj ≫ Φ.presheafFiber.map η.hom =
      η.hom.app (op U) ≫ Φ.toPresheafFiber U v H.obj :=
    Φ.toPresheafFiber_naturality η.hom U v
  have hc : Φ.toPresheafFiber U v H.obj ≫ c = Ψ.toPresheafFiber B b G.obj :=
    toPresheafFiber_etalePushforwardStalkComponent t t
      ⟨𝟙 _, Category.id_comp t⟩ G U v
  have h : Φ.toPresheafFiber U v F.obj ≫ (Φ.presheafFiber.map η.hom ≫ c) =
      (η.hom.app (op U) ≫ G.obj.map j.op) ≫ γ := by
    exact (Category.assoc (Φ.toPresheafFiber U v F.obj)
      (Φ.presheafFiber.map η.hom) c).symm.trans
      ((congrArg (fun a => a ≫ c) hn).trans
        ((Category.assoc (η.hom.app (op U)) (Φ.toPresheafFiber U v H.obj) c).trans
          ((congrArg (fun a => η.hom.app (op U) ≫ a) hc).trans
            ((congrArg (fun a => η.hom.app (op U) ≫ a) hγ.symm).trans
              (Category.assoc (η.hom.app (op U)) (G.obj.map j.op) γ).symm))))
  change Φ.toPresheafFiber U v F.obj ≫
      ((Φ.presheafFiber.map η.hom ≫ c) ≫ inv γ) = η.hom.app (op U) ≫ G.obj.map j.op
  exact (Category.assoc (Φ.toPresheafFiber U v F.obj)
    (Φ.presheafFiber.map η.hom ≫ c) (inv γ)).symm.trans
    ((congrArg (fun a => a ≫ inv γ) h).trans
      ((Category.assoc (η.hom.app (op U) ≫ G.obj.map j.op) γ (inv γ)).trans
        ((congrArg (fun a => (η.hom.app (op U) ≫ G.obj.map j.op) ≫ a)
          (IsIso.hom_inv_id γ)).trans (Category.comp_id _))))

end EtaleCohomology
