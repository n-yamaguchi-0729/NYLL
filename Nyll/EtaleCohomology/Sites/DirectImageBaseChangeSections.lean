/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.DirectImageBaseChange
import Nyll.EtaleCohomology.Sites.PullbackSections
import Nyll.EtaleCohomology.Sites.PullbackSectionFactors
import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The actual base-change mate on pulled sections

The native pullback comparison of a commuting square takes local factors
to their literal base changes. Evaluating the actual adjunction-unit
identity of the base-change mate therefore gives a formula on every
pulled section. No properness, field-point detection or invertibility
of the base-change mate enters this identity.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem nativePullbackComp_inv_fst_fst
    {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X) (U : X.Etale) :
    ((MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).inv.app U).left ≫
        pullback.fst U.hom (p ≫ q) =
      pullback.fst (pullback.snd U.hom q) p ≫ pullback.fst U.hom q := by
  let e := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).app U
  let π := pullback.fst (pullback.snd U.hom q) p ≫ pullback.fst U.hom q
  let δ := pullback.fst U.hom (p ≫ q)
  have he : e.hom.left ≫ π = δ :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q U
  have hi : e.inv.left ≫ e.hom.left = 𝟙 _ :=
    congrArg (fun a => a.left) e.inv_hom_id
  change e.inv.left ≫ δ = π
  exact (congrArg (fun a => e.inv.left ≫ a) he.symm).trans
    ((Category.assoc e.inv.left e.hom.left π).symm.trans
      ((congrArg (fun a => a ≫ π) hi).trans (Category.id_comp π)))

private theorem nativePullbackCongr_fst
    {X Y : Scheme.{u}} {p q : Y ⟶ X} (h : p = q) (U : X.Etale) :
    ((eqToIso (congrArg etaleBaseChange h)).hom.app U).left ≫ pullback.fst U.hom q =
      pullback.fst U.hom p := by
  cases h
  change (𝟙 _) ≫ pullback.fst U.hom p = pullback.fst U.hom p
  exact Category.id_comp _

private theorem iteratedPullback_hom_ext
    {A B C D E : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) (p : D ⟶ B)
    {k₁ k₂ : E ⟶ pullback (pullback.snd f g) p}
    (hfst : k₁ ≫ pullback.fst (pullback.snd f g) p ≫ pullback.fst f g =
      k₂ ≫ pullback.fst (pullback.snd f g) p ≫ pullback.fst f g)
    (hsnd : k₁ ≫ pullback.snd (pullback.snd f g) p =
      k₂ ≫ pullback.snd (pullback.snd f g) p) : k₁ = k₂ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · calc
        (k₁ ≫ pullback.fst (pullback.snd f g) p) ≫ pullback.snd f g =
            k₁ ≫ pullback.snd (pullback.snd f g) p ≫ p := by
          rw [Category.assoc, pullback.condition]
        _ = k₂ ≫ pullback.snd (pullback.snd f g) p ≫ p := by
          rw [← Category.assoc, hsnd, Category.assoc]
        _ = (k₂ ≫ pullback.fst (pullback.snd f g) p) ≫ pullback.snd f g := by
          rw [Category.assoc, pullback.condition]
  · exact hsnd

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

private def baseChangeSquareIso :
    etaleBaseChange g ⋙ etaleBaseChange f' ≅
      etaleBaseChange f ⋙ etaleBaseChange g' :=
  (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f' g).symm ≪≫
    eqToIso (congrArg etaleBaseChange h) ≪≫
      MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) g' f

private theorem baseChangeSquareIso_fst_fst (U : Y.Etale) :
    ((baseChangeSquareIso f g f' g' h).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom f) g' ≫ pullback.fst U.hom f =
      pullback.fst (pullback.snd U.hom g) f' ≫ pullback.fst U.hom g := by
  let c₁ := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) g' f).hom.app U
  let c₂ := (MorphismProperty.Over.pullbackComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f' g).inv.app U
  let e := (eqToIso (congrArg etaleBaseChange h)).hom.app U
  have hc₁ : c₁.left ≫
      pullback.fst (pullback.snd U.hom f) g' ≫ pullback.fst U.hom f =
        pullback.fst U.hom (g' ≫ f) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) g' f U
  have he : e.left ≫ pullback.fst U.hom (g' ≫ f) =
      pullback.fst U.hom (f' ≫ g) := nativePullbackCongr_fst h U
  have hc₂ : c₂.left ≫ pullback.fst U.hom (f' ≫ g) =
      pullback.fst (pullback.snd U.hom g) f' ≫ pullback.fst U.hom g :=
    nativePullbackComp_inv_fst_fst f' g U
  let π := pullback.fst (pullback.snd U.hom f) g' ≫ pullback.fst U.hom f
  have hc : (e.left ≫ c₁.left) ≫ π = pullback.fst U.hom (f' ≫ g) :=
    (Category.assoc e.left c₁.left π).trans
      ((congrArg (fun a => e.left ≫ a) hc₁).trans he)
  change (c₂.left ≫ e.left ≫ c₁.left) ≫ π = _
  exact (Category.assoc c₂.left (e.left ≫ c₁.left) π).trans
    ((congrArg (fun a => c₂.left ≫ a) hc).trans hc₂)

private theorem baseChangeSquareIso_app_composition (U : Y.Etale) :
    (baseChangeSquareIso f g f' g' h).hom.app U =
      (MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f' g).inv.app U ≫
      (eqToIso (congrArg etaleBaseChange h)).hom.app U ≫
      (MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) g' f).hom.app U := rfl

/-- The literal base change of a local factor through a commuting square. -/
def etaleSquareLocalFactor
    {U : Y.Etale} {V : Y'.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ g) :
    ((etaleBaseChange f').obj V).left ⟶ ((etaleBaseChange f).obj U).left :=
  pullback.lift
    (pullback.fst V.hom f' ≫ l)
    (pullback.snd V.hom f' ≫ g')
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => pullback.fst V.hom f' ≫ a) hl).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ g) pullback.condition).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun a => pullback.snd V.hom f' ≫ a) h).trans
                (Category.assoc _ _ _).symm))))))

theorem etaleSquareLocalFactor_snd
    {U : Y.Etale} {V : Y'.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ g) :
    etaleSquareLocalFactor f g f' g' h l hl ≫ ((etaleBaseChange f).obj U).hom =
      ((etaleBaseChange f').obj V).hom ≫ g' := pullback.lift_snd _ _ _

private theorem baseChangeSquare_localFactor
    {U : Y.Etale} {V : Y'.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ g) :
    (etaleBaseChange f').map (etaleBaseChangeLift g l hl) ≫
        (baseChangeSquareIso f g f' g' h).hom.app U =
      etaleBaseChangeLift g' (etaleSquareLocalFactor f g f' g' h l hl)
        (etaleSquareLocalFactor_snd f g f' g' h l hl) := by
  let A := (etaleBaseChange f').obj V
  let B := (etaleBaseChange g).obj U
  let C := (etaleBaseChange f').obj B
  let W := (etaleBaseChange f).obj U
  let D := (etaleBaseChange g').obj W
  let a : V ⟶ B := etaleBaseChangeLift g l hl
  let b : A ⟶ C := (etaleBaseChange f').map a
  let e : C ⟶ D := (baseChangeSquareIso f g f' g' h).hom.app U
  let n := etaleSquareLocalFactor f g f' g' h l hl
  let c : A ⟶ D := etaleBaseChangeLift g' n
    (etaleSquareLocalFactor_snd f g f' g' h l hl)
  have hb : b.left ≫ pullback.fst B.hom f' = pullback.fst V.hom f' ≫ a.left :=
    pullback.lift_fst _ _ _
  have ha : a.left ≫ pullback.fst U.hom g = l := pullback.lift_fst _ _ _
  have he : e.left ≫ pullback.fst W.hom g' ≫ pullback.fst U.hom f =
      pullback.fst B.hom f' ≫ pullback.fst U.hom g :=
    baseChangeSquareIso_fst_fst f g f' g' h U
  have hc : c.left ≫ pullback.fst W.hom g' = n := pullback.lift_fst _ _ _
  have hn : n ≫ pullback.fst U.hom f = pullback.fst V.hom f' ≫ l :=
    pullback.lift_fst _ _ _
  have hleft : (b ≫ e).left ≫ pullback.fst W.hom g' ≫ pullback.fst U.hom f =
      pullback.fst V.hom f' ≫ l := by
    change (b.left ≫ e.left) ≫ _ ≫ _ = _
    exact (Category.assoc b.left e.left
      (pullback.fst W.hom g' ≫ pullback.fst U.hom f)).trans
      ((congrArg (fun a => b.left ≫ a) he).trans
        ((Category.assoc b.left (pullback.fst B.hom f') (pullback.fst U.hom g)).symm.trans
          ((congrArg (fun a => a ≫ pullback.fst U.hom g) hb).trans
            ((Category.assoc (pullback.fst V.hom f') a.left (pullback.fst U.hom g)).trans
              (congrArg (fun a => pullback.fst V.hom f' ≫ a) ha)))))
  have hright : c.left ≫ pullback.fst W.hom g' ≫ pullback.fst U.hom f =
      pullback.fst V.hom f' ≫ l :=
    (Category.assoc c.left (pullback.fst W.hom g') (pullback.fst U.hom f)).symm.trans
      ((congrArg (fun a => a ≫ pullback.fst U.hom f) hc).trans hn)
  change b ≫ e = c
  apply MorphismProperty.Over.Hom.ext
  apply iteratedPullback_hom_ext U.hom f g'
  · exact hleft.trans hright.symm
  · exact (b ≫ e).w.trans c.w.symm

variable (Λ : Type u) [CommRing Λ]

private theorem pushforwardCongr_app
    {S T : Scheme.{u}} {p q : T ⟶ S} (h : p = q)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)) (U : S.Etale) :
    ((eqToIso (congrArg (fun a => etalePushforward a Λ) h.symm)).hom.app G).hom.app
        (op U) =
      G.obj.map ((eqToIso (congrArg etaleBaseChange h)).hom.app U).op := by
  cases h
  change 𝟙 _ = G.obj.map (𝟙 _)
  exact (G.obj.map_id _).symm

private theorem pushforwardComp_hom_app
    {S T V : Scheme.{u}} (p : V ⟶ T) (q : T ⟶ S)
    (G : Sheaf V.smallEtaleTopology (ModuleCat.{u} Λ)) (U : S.Etale) :
    ((etalePushforwardCompIso p q Λ).hom.app G).hom.app (op U) =
      G.obj.map ((MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app U).op := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private theorem pushforwardComp_inv_app
    {S T V : Scheme.{u}} (p : V ⟶ T) (q : T ⟶ S)
    (G : Sheaf V.smallEtaleTopology (ModuleCat.{u} Λ)) (U : S.Etale) :
    ((etalePushforwardCompIso p q Λ).inv.app G).hom.app (op U) =
      G.obj.map ((MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).inv.app U).op := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem presheaf_map_triple
    {C D : Type*} [Category* C] [Category* D]
    (P : Cᵒᵖ ⥤ D) {A B E H : C} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ H) :
    P.map c.op ≫ P.map b.op ≫ P.map a.op = P.map (a ≫ b ≫ c).op :=
  (Category.assoc (P.map c.op) (P.map b.op) (P.map a.op)).symm.trans
    ((congrArg (fun k => k ≫ P.map a.op) (P.map_comp c.op b.op).symm).trans
      (P.map_comp (b ≫ c).op a.op).symm)

private theorem compose_three_of_eq
    {C : Type*} [Category* C] {A B D E : C}
    {a a' : A ⟶ B} {b b' : B ⟶ D} {c c' : D ⟶ E}
    (ha : a = a') (hb : b = b') (hc : c = c') :
    a ≫ b ≫ c = a' ≫ b' ≫ c' := by
  cases ha
  cases hb
  cases hc
  rfl

private theorem cancel_postcomp_sectionIso
    {C : Type*} [Category* C] {A B D : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) (bi : D ⟶ B)
    (ha : a ≫ b = c) (hb : b ≫ bi = 𝟙 B) : a = c ≫ bi :=
  (Category.comp_id a).symm.trans
    ((congrArg (fun k => a ≫ k) hb.symm).trans
      ((Category.assoc a b bi).symm.trans (congrArg (fun k => k ≫ bi) ha)))

private theorem natIso_component_hom_inv
    {C : Type*} [Category* C] {S : Scheme.{u}}
    {L M : C ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (e : L ≅ M) (G : C) (U : S.Etale) :
    (e.hom.app G).hom.app (op U) ≫ (e.inv.app G).hom.app (op U) = 𝟙 _ :=
  congrArg (fun η : L.obj G ⟶ L.obj G => η.hom.app (op U)) (e.app G).hom_inv_id

private theorem pushforwardSquareIso_app_decomposition
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y.Etale) :
    ((etalePushforwardSquareIso f g f' g' h Λ).hom.app G).hom.app (op U) =
      ((etalePushforwardCompIso g' f Λ).hom.app G).hom.app (op U) ≫
      ((eqToIso (congrArg (fun a => etalePushforward a Λ) h.symm)).hom.app G).hom.app
        (op U) ≫
      ((etalePushforwardCompIso f' g Λ).inv.app G).hom.app (op U) :=
  (cancel_postcomp_sectionIso _ _ _ _
    (congrArg (fun η => (η.app G).hom.app (op U))
      (etalePushforwardSquareIso_hom_comp f g f' g' h Λ))
    (natIso_component_hom_inv Λ (etalePushforwardCompIso f' g Λ) G U)).trans
    (Category.assoc
      (((etalePushforwardCompIso g' f Λ).hom.app G).hom.app (op U))
      (((eqToIso (congrArg (fun a => etalePushforward a Λ) h.symm)).hom.app G).hom.app
        (op U))
      (((etalePushforwardCompIso f' g Λ).inv.app G).hom.app (op U)))

private theorem pushforwardSquareIso_app
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y.Etale) :
    ((etalePushforwardSquareIso f g f' g' h Λ).hom.app G).hom.app (op U) =
      G.obj.map ((baseChangeSquareIso f g f' g' h).hom.app U).op :=
  (pushforwardSquareIso_app_decomposition f g f' g' h Λ G U).trans
    ((compose_three_of_eq
      (pushforwardComp_hom_app Λ g' f G U)
      (pushforwardCongr_app Λ h G U)
      (pushforwardComp_inv_app Λ f' g G U)).trans
      ((presheaf_map_triple G.obj
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f' g).inv.app U)
        ((eqToIso (congrArg etaleBaseChange h)).hom.app U)
        ((MorphismProperty.Over.pullbackComp
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) g' f).hom.app U)).trans
        (congrArg (fun a => G.obj.map a.op)
          (baseChangeSquareIso_app_composition f g f' g' h U).symm)))

private theorem presheaf_map_comp_of_eq
    {C D : Type*} [Category* C] [Category* D]
    (P : Cᵒᵖ ⥤ D) {A B E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ E)
    (h : a ≫ b = c) : P.map b.op ≫ P.map a.op = P.map c.op :=
  (P.map_comp b.op a.op).symm.trans (congrArg (fun k => P.map k.op) h)

private theorem pulledSection_diagram
    {C : Type*} [Category* C] {A B D E H I : C}
    (η : A ⟶ B) (η' : A ⟶ D) (r : B ⟶ E) (β : E ⟶ I)
    (β' : B ⟶ H) (e : D ⟶ H) (r' : H ⟶ I) (c : D ⟶ I)
    (hn : r ≫ β = β' ≫ r') (hu : η' ≫ e = η ≫ β') (hc : e ≫ r' = c) :
    (η ≫ r) ≫ β = η' ≫ c :=
  (Category.assoc η r β).trans
    ((congrArg (fun k => η ≫ k) hn).trans
      ((Category.assoc η β' r').symm.trans
        ((congrArg (fun k => k ≫ r') hu.symm).trans
          ((Category.assoc η' e r').trans (congrArg (fun k => η' ≫ k) hc)))))

private theorem baseChange_unit_component
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y.Etale) :
    ((etalePullbackPushforwardAdjunction g' Λ).unit.app F).hom.app
        (op ((etaleBaseChange f).obj U)) ≫
      ((etalePullback g' Λ).obj F).obj.map
        ((baseChangeSquareIso f g f' g' h).hom.app U).op =
    ((etalePullbackPushforwardAdjunction g Λ).unit.app
        ((etalePushforward f Λ).obj F)).hom.app (op U) ≫
      ((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app
        (op ((etaleBaseChange g).obj U)) := by
  have hu := congrArg (fun z => z.hom.app (op U))
    (etaleDirectImageBaseChange_unit f g f' g' h Λ F)
  exact (congrArg
    (fun z => ((etalePullbackPushforwardAdjunction g' Λ).unit.app F).hom.app
      (op ((etaleBaseChange f).obj U)) ≫ z)
    (pushforwardSquareIso_app f g f' g' h Λ ((etalePullback g' Λ).obj F) U).symm).trans hu

/-- The actual base-change mate applied to a pulled section is the section
pulled through the literal base change of its local factor. -/
theorem etaleDirectImageBaseChange_section
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V : Y'.Etale}
    (l : V.left ⟶ U.left) (hl : l ≫ U.hom = V.hom ≫ g) :
    etalePullbackSectionMap g Λ ((etalePushforward f Λ).obj F) l hl ≫
        ((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app (op V) =
      etalePullbackSectionMap g' Λ F (etaleSquareLocalFactor f g f' g' h l hl)
        (etaleSquareLocalFactor_snd f g f' g' h l hl) := by
  exact pulledSection_diagram
    (((etalePullbackPushforwardAdjunction g Λ).unit.app
      ((etalePushforward f Λ).obj F)).hom.app (op U))
    (((etalePullbackPushforwardAdjunction g' Λ).unit.app F).hom.app
      (op ((etaleBaseChange f).obj U)))
    (((etalePullback g Λ).obj ((etalePushforward f Λ).obj F)).obj.map
      (etaleBaseChangeLift g l hl).op)
    (((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app (op V))
    (((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app
      (op ((etaleBaseChange g).obj U)))
    (((etalePullback g' Λ).obj F).obj.map ((baseChangeSquareIso f g f' g' h).hom.app U).op)
    (((etalePullback g' Λ).obj F).obj.map
      ((etaleBaseChange f').map (etaleBaseChangeLift g l hl)).op)
    (((etalePullback g' Λ).obj F).obj.map
      (etaleBaseChangeLift g' (etaleSquareLocalFactor f g f' g' h l hl)
        (etaleSquareLocalFactor_snd f g f' g' h l hl)).op)
    (((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.naturality
      (etaleBaseChangeLift g l hl).op)
    (baseChange_unit_component f g f' g' h Λ F U)
    (presheaf_map_comp_of_eq ((etalePullback g' Λ).obj F).obj _ _ _
      (baseChangeSquare_localFactor f g f' g' h l hl))

/-- The native source factor induced by a global lift to an original
étale object in a commuting square. -/
def etaleSquareGlobalFactor
    {U : Y.Etale} (l : Y' ⟶ U.left) (hl : l ≫ U.hom = g) :
    X' ⟶ ((etaleBaseChange f).obj U).left :=
  pullback.lift (f' ≫ l) g'
    ((Category.assoc f' l U.hom).trans ((congrArg (fun a => f' ≫ a) hl).trans h))

theorem etaleSquareGlobalFactor_snd
    {U : Y.Etale} (l : Y' ⟶ U.left) (hl : l ≫ U.hom = g) :
    etaleSquareGlobalFactor f g f' g' h l hl ≫ ((etaleBaseChange f).obj U).hom = g' :=
  pullback.lift_snd _ _ _

private theorem squareLocalFactor_identity
    {U : Y.Etale} (l : Y' ⟶ U.left) (hl : l ≫ U.hom = g) :
    (baseChangeIdentityIso f').hom.left ≫
      etaleSquareLocalFactor f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm) =
      etaleSquareGlobalFactor f g f' g' h l hl := by
  let V : Y'.Etale := Scheme.Etale.mk (𝟙 _)
  let T : X'.Etale := Scheme.Etale.mk (𝟙 _)
  let A : X'.Etale := (etaleBaseChange f').obj V
  let W : X.Etale := (etaleBaseChange f).obj U
  let j : T ⟶ A := (baseChangeIdentityIso f').hom
  let N : A.left ⟶ W.left :=
    etaleSquareLocalFactor f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm)
  let n : X' ⟶ W.left := etaleSquareGlobalFactor f g f' g' h l hl
  have hN : N ≫ W.hom = A.hom ≫ g' :=
    etaleSquareLocalFactor_snd f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm)
  have hn : n ≫ W.hom = g' := etaleSquareGlobalFactor_snd f g f' g' h l hl
  have hj₁ : j.left ≫ pullback.fst V.hom f' = f' := pullback.lift_fst _ _ _
  have hj₂ : j.left ≫ pullback.snd V.hom f' = 𝟙 _ := pullback.lift_snd _ _ _
  have hN₁ : N ≫ pullback.fst U.hom f = pullback.fst V.hom f' ≫ l :=
    pullback.lift_fst _ _ _
  have hn₁ : n ≫ pullback.fst U.hom f = f' ≫ l := pullback.lift_fst _ _ _
  change j.left ≫ N = n
  apply pullback.hom_ext
  · exact (Category.assoc j.left N (pullback.fst U.hom f)).trans
      ((congrArg (fun a => j.left ≫ a) hN₁).trans
        ((Category.assoc j.left (pullback.fst V.hom f') l).symm.trans
          ((congrArg (fun a => a ≫ l) hj₁).trans hn₁.symm)))
  · exact (Category.assoc j.left N W.hom).trans
      ((congrArg (fun a => j.left ≫ a) hN).trans
        ((Category.assoc j.left A.hom g').symm.trans
          ((congrArg (fun a => a ≫ g') hj₂).trans
            ((Category.id_comp g').trans hn.symm))))

private theorem section_source_restriction_of_comp_eq
    {S T : Scheme.{u}} (q : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    {U V : T.Etale} {W : S.Etale} (a : U ⟶ V)
    (l : V.left ⟶ W.left) (hl : l ≫ W.hom = V.hom ≫ q)
    (n : U.left ⟶ W.left) (hn : n ≫ W.hom = U.hom ≫ q)
    (heq : a.left ≫ l = n) :
    etalePullbackSectionMap q Λ F l hl ≫ ((etalePullback q Λ).obj F).obj.map a.op =
      etalePullbackSectionMap q Λ F n hn := by
  subst n
  exact etalePullbackSectionMap_source_restriction q Λ F a l hl hn

private theorem squareGlobalSection_restriction
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} (l : Y' ⟶ U.left) (hl : l ≫ U.hom = g) :
    etalePullbackSectionMap g' Λ F
        (etaleSquareLocalFactor f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm))
        (etaleSquareLocalFactor_snd f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm)) ≫
      (etalePushforwardGlobalSectionsIso f' Λ ((etalePullback g' Λ).obj F)).hom =
    etalePullbackSectionMap g' Λ F (U := Scheme.Etale.mk (𝟙 _))
      (etaleSquareGlobalFactor f g f' g' h l hl)
      ((etaleSquareGlobalFactor_snd f g f' g' h l hl).trans (Category.id_comp g').symm) :=
  section_source_restriction_of_comp_eq Λ g' F (baseChangeIdentityIso f').hom
    (etaleSquareLocalFactor f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm))
    (etaleSquareLocalFactor_snd f g f' g' h (U := U)
        (V := Scheme.Etale.mk (𝟙 Y')) l (hl.trans (Category.id_comp g).symm))
    (etaleSquareGlobalFactor f g f' g' h l hl)
    ((etaleSquareGlobalFactor_snd f g f' g' h l hl).trans (Category.id_comp g').symm)
    (squareLocalFactor_identity f g f' g' h l hl)

/-- Evaluating the actual base-change mate on a global pulled section,
then using the actual direct-image global-section comparison, is the
original section pulled through the native source factor. -/
theorem etaleDirectImageBaseChange_global_section
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} (l : Y' ⟶ U.left) (hl : l ≫ U.hom = g) :
    etalePullbackSectionMap g Λ ((etalePushforward f Λ).obj F)
        (U := Scheme.Etale.mk (𝟙 _)) l (hl.trans (Category.id_comp g).symm) ≫
      ((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app
        (op (Scheme.Etale.mk (𝟙 _))) ≫
      (etalePushforwardGlobalSectionsIso f' Λ ((etalePullback g' Λ).obj F)).hom =
      etalePullbackSectionMap g' Λ F (U := Scheme.Etale.mk (𝟙 _))
        (etaleSquareGlobalFactor f g f' g' h l hl)
        ((etaleSquareGlobalFactor_snd f g f' g' h l hl).trans
          (Category.id_comp g').symm) :=
  (Category.assoc
    (etalePullbackSectionMap g Λ ((etalePushforward f Λ).obj F)
      (U := Scheme.Etale.mk (𝟙 _)) l (hl.trans (Category.id_comp g).symm))
    (((etaleDirectImageBaseChange f g f' g' h Λ).app F).hom.app
      (op (Scheme.Etale.mk (𝟙 _))))
    (etalePushforwardGlobalSectionsIso f' Λ ((etalePullback g' Λ).obj F)).hom).symm.trans
    ((congrArg
      (fun a => a ≫ (etalePushforwardGlobalSectionsIso f' Λ
        ((etalePullback g' Λ).obj F)).hom)
      (etaleDirectImageBaseChange_section f g f' g' h Λ F
        (V := Scheme.Etale.mk (𝟙 _)) l (hl.trans (Category.id_comp g).symm))).trans
      (squareGlobalSection_restriction f g f' g' h Λ F l hl))

end EtaleCohomology
