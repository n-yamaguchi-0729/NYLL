/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkCoverDescent
import Nyll.EtaleCohomology.Sites.GeometricStalkNeighborhoodMaps
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionComparison
import Nyll.EtaleCohomology.Sites.GeometricStalkSchemeLimit
import Nyll.SchemeTheory.Descent.AffineTransitionMatchedCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-!
# A pointed étale covering stage retaining its full overlap condition

The actual affine local-factor cover over the strict-local source descends
to a cover over a pointed affine étale neighborhood. Its map to the original
étale model and its entire overlap range are retained. Coefficient-stage
cover and overlap descent is purely geometric; no sheaf continuity is used.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

private theorem baseChangeFactor_w {X Y : Scheme.{u}} (q : Y ⟶ X)
    (U : X.Etale) (V : Y.Etale) (d : V ⟶ (etaleBaseChange q).obj U) :
    (d.left ≫ pullback.fst U.hom q) ≫ U.hom = V.hom ≫ q :=
  (Category.assoc d.left (pullback.fst U.hom q) U.hom).trans
    ((congrArg (fun k => d.left ≫ k) (pullback.condition (f := U.hom) (g := q))).trans
      ((Category.assoc d.left (pullback.snd U.hom q) q).symm.trans
        (congrArg (fun k => k ≫ q) d.w)))

/-- A genuine affine étale covering stage with exact recovery of the
original representative and containment of its whole self-overlap. -/
theorem geometricStalk_exists_affine_matched_cover_stage
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f]
    (U : X.Etale) [IsAffine U.left]
    (V : (pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f).Etale)
    [IsAffine V.left] [hVsurj : Surjective V.hom]
    (d : V ⟶ (etaleBaseChange
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)).obj U)
    [hd : IsOpenImmersion d.left]
    (W : (pullback U.hom U.hom).Opens)
    (hW : Set.range (pullback.map V.hom V.hom U.hom U.hom
      (d.left ≫ pullback.fst U.hom
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f))
      (d.left ≫ pullback.fst U.hom
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f))
      (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f)
      (baseChangeFactor_w _ U V d).symm (baseChangeFactor_w _ U V d).symm) ⊆ W.carrier) :
    ∃ (T : (Spec (CommRingCat.of R)).Etale)
      (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj T)
      (_ : IsAffine T.left) (C : X.Etale) (p : C ⟶ (etaleBaseChange f).obj T)
      (r : C ⟶ U) (e : V.left ⟶ C.left),
      IsAffine C.left ∧ Surjective p.left ∧
      e ≫ p.left = V.hom ≫ geometricStalkNeighborhoodBaseChangeMap φ f T t ∧
      e ≫ r.left = d.left ≫ pullback.fst U.hom
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ∧
      Set.range (pullback.map p.left p.left U.hom U.hom r.left r.left
        ((etaleBaseChange f).obj T).hom (p.w.trans r.w.symm) (p.w.trans r.w.symm)) ⊆
          W.carrier := by
  let D := geometricStalkSpecDiagram φ
  let c := geometricStalkSpecCone φ
  let F := geometricStalkSmallAlgebraDiagram φ
  have : ∀ {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (a : i ⟶ j),
      IsAffineHom (D.map a).left :=
    fun a => inferInstanceAs (IsAffineHom (Spec.map (F.map a.unop).right))
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ, CompactSpace (D.obj i).left :=
    fun i => inferInstanceAs (CompactSpace (Spec (F.obj i.unop).right))
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ,
      QuasiSeparatedSpace (D.obj i).left :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop).right))
  let h : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶
      Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let q : pullback h f ⟶ X := pullback.snd h f
  let d₀ : V.left ⟶ pullback U.hom q := d.left
  have hd₀ : IsOpenImmersion d₀ := hd
  let E : pullback h (U.hom ≫ f) ≅ pullback U.hom q :=
    (AffineTransitionHom.modelMap_isPullback h f U.hom).flip.isoPullback
  have hE : IsOpenImmersion E.inv := IsOpenImmersion.of_isIso E.inv
  let α : V.left ⟶ pullback c.pt.hom (U.hom ≫ f) := d₀ ≫ E.inv
  have hαOpen : IsOpenImmersion α := IsOpenImmersion.comp d₀ E.inv
  have hα : α ≫ AffineTransitionHom.modelMap h f U.hom = V.hom := by
    exact (Category.assoc d.left E.inv _).trans
      ((congrArg (fun k => d.left ≫ k)
        (AffineTransitionHom.modelMap_isPullback h f U.hom).flip.isoPullback_inv_snd).trans d.w)
  have hαr : α ≫ pullback.snd h (U.hom ≫ f) = d.left ≫ pullback.fst U.hom q :=
    (Category.assoc d.left E.inv _).trans
      (congrArg (fun k => d.left ≫ k)
        (AffineTransitionHom.modelMap_isPullback h f U.hom).flip.isoPullback_inv_fst)
  obtain ⟨i, O, hO, hrec, hsurj, hOverlap⟩ :=
    AffineTransitionHom.exists_affine_matched_cover_stage_of_maps
      (hα := hαOpen) (hSurj := hVsurj)
      (X := X) (U := U.left) (V := V.left) D c (geometricStalkSpecConeIsLimit φ) f U.hom α V.hom
      (d.left ≫ pullback.fst U.hom q) hα hαr (baseChangeFactor_w q U V d) W hW
  obtain ⟨T, t, hT, ρ, hρ, β₀, hρgerm, hβ, hρβ⟩ :=
    geometricStalk_exists_affine_coefficientFactor φ i
  have : IsAffine T.left := hT
  have : IsAffine (D.obj i).left :=
    inferInstanceAs (IsAffine (Spec (F.obj i.unop).right))
  let B : Over (Spec (CommRingCat.of R)) := Over.mk T.hom
  let β : B ⟶ D.obj i := Over.homMk β₀ hβ
  let τ : c.pt ⟶ B := Over.homMk ρ hρ
  have hτβ : τ ≫ β = c.π.app i := Over.OverMorphism.ext hρβ
  have : IsAffineHom β.left := inferInstanceAs (IsAffineHom β₀)
  have : IsAffineHom ((Over.pullback (U.hom ≫ f)).map β).left :=
    MorphismProperty.overPullbackMap
      (P := show MorphismProperty Scheme.{u} from @IsAffineHom)
      (U.hom ≫ f) β inferInstance
  let OT : (pullback T.hom (U.hom ≫ f)).Opens :=
    ((Over.pullback (U.hom ≫ f)).map β).left ⁻¹ᵁ O
  have hOT : IsAffineOpen OT := hO.preimage _
  have hCover : Surjective (OT.ι ≫ AffineTransitionHom.modelMap T.hom f U.hom) := by
    have : Surjective (O.ι ≫ AffineTransitionHom.modelMap (D.obj i).hom f U.hom) := hsurj
    exact AffineTransitionHom.modelOpenCover_surjective β f U.hom O
  have hRecover : ((Over.pullback (U.hom ≫ f)).map τ).left ⁻¹ᵁ OT = α.opensRange := by
    change ((Over.pullback (U.hom ≫ f)).map τ).left ⁻¹ᵁ
      (((Over.pullback (U.hom ≫ f)).map β).left ⁻¹ᵁ O) = α.opensRange
    rw [← Scheme.Hom.comp_preimage]
    have hcomp : ((Over.pullback (U.hom ≫ f)).map τ).left ≫
        ((Over.pullback (U.hom ≫ f)).map β).left =
          ((Over.pullback (U.hom ≫ f)).map (c.π.app i)).left :=
      (congrArg (fun k => k.left) ((Over.pullback (U.hom ≫ f)).map_comp τ β)).symm.trans
        (congrArg (fun k => ((Over.pullback (U.hom ≫ f)).map k).left) hτβ)
    rw [hcomp]
    exact hrec
  let a : O.toScheme ⟶ pullback (D.obj i).hom f :=
    O.ι ≫ AffineTransitionHom.modelMap (D.obj i).hom f U.hom
  let aT : OT.toScheme ⟶ pullback T.hom f := OT.ι ≫ AffineTransitionHom.modelMap T.hom f U.hom
  let dT : OT.toScheme ⟶ O.toScheme := ((Over.pullback (U.hom ≫ f)).map β).left ∣_ O
  have HT : IsPullback dT aT a ((Over.pullback f).map β).left :=
    AffineTransitionHom.openCover_transition_isPullback β f U.hom O
  let mT : pullback aT aT ⟶ pullback a a := pullback.map aT aT a a dT dT
    ((Over.pullback f).map β).left HT.w.symm HT.w.symm
  have hmT : mT ≫ AffineTransitionHom.modelCoverOverlapMap (D.obj i).hom f U.hom O.ι =
      AffineTransitionHom.modelCoverOverlapMap T.hom f U.hom OT.ι :=
    AffineTransitionHom.modelCoverOverlapMap_naturality β f U.hom OT.ι O.ι dT
      (morphismRestrict_ι _ _) HT.toCommSq
  have hRangeT : Set.range (AffineTransitionHom.modelCoverOverlapMap T.hom f U.hom OT.ι) ⊆
      W.carrier := by
    rintro z ⟨v, rfl⟩
    have hv := hOverlap ⟨mT v, rfl⟩
    have hp : AffineTransitionHom.modelCoverOverlapMap (D.obj i).hom f U.hom O.ι (mT v) =
        AffineTransitionHom.modelCoverOverlapMap T.hom f U.hom OT.ι v :=
      (Scheme.Hom.comp_apply mT _ v).symm.trans (congrArg (fun k => k v) hmT)
    exact hp ▸ hv
  let r₀ : OT.toScheme ⟶ U.left := OT.ι ≫ pullback.snd T.hom (U.hom ≫ f)
  let C : X.Etale := Scheme.Etale.mk (r₀ ≫ U.hom)
  let p : C ⟶ (etaleBaseChange f).obj T := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) aT
    (AffineTransitionHom.modelCoverMap_comp_snd T.hom f U.hom OT.ι)
  let r : C ⟶ U := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) r₀ rfl
  let e : V.left ⟶ C.left := AffineTransitionHom.modelOpenRecovery τ f U.hom α OT hRecover
  have He : IsPullback e (α ≫ AffineTransitionHom.modelMap h f U.hom) aT
      ((Over.pullback f).map τ).left :=
    AffineTransitionHom.modelOpenRecovery_isPullback τ f U.hom α OT hRecover
  have hρcanonical : ρ = geometricStalkNeighborhoodMap φ T t :=
    hρgerm.trans (geometricStalkNeighborhoodMap_eq_germ φ T t).symm
  have hcanonical : ((Over.pullback f).map τ).left =
      geometricStalkNeighborhoodBaseChangeMap φ f T t := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        ((congrArg (fun k => pullback.fst h f ≫ k) hρcanonical).trans
          (geometricStalkNeighborhoodBaseChangeMap_fst φ f T t).symm)
    · exact (Over.w ((Over.pullback f).map τ)).trans
        (geometricStalkNeighborhoodBaseChangeMap_snd φ f T t).symm
  have heP : e ≫ p.left = V.hom ≫ geometricStalkNeighborhoodBaseChangeMap φ f T t :=
    He.w.trans ((congrArg (fun k => k ≫ ((Over.pullback f).map τ).left) hα).trans
      (congrArg (fun k => V.hom ≫ k) hcanonical))
  have heR : e ≫ r.left = d.left ≫ pullback.fst U.hom q := by
    change e ≫ OT.ι ≫ pullback.snd T.hom (U.hom ≫ f) = _
    have hτsnd : ((Over.pullback (U.hom ≫ f)).map τ).left ≫
        pullback.snd T.hom (U.hom ≫ f) = pullback.snd h (U.hom ≫ f) :=
      Over.w ((Over.pullback (U.hom ≫ f)).map τ)
    have heι : e ≫ OT.ι = α ≫ ((Over.pullback (U.hom ≫ f)).map τ).left :=
      AffineTransitionHom.modelOpenRecovery_ι τ f U.hom α OT hRecover
    exact (Category.assoc e OT.ι (pullback.snd T.hom (U.hom ≫ f))).symm.trans
      ((congrArg (fun k => k ≫ pullback.snd T.hom (U.hom ≫ f)) heι).trans
        ((Category.assoc α ((Over.pullback (U.hom ≫ f)).map τ).left
          (pullback.snd T.hom (U.hom ≫ f))).trans
          ((congrArg (fun k => α ≫ k) hτsnd).trans hαr)))
  exact ⟨T, t, hT, C, p, r, e, hOT, hCover, heP, heR, hRangeT⟩

end EtaleCohomology
