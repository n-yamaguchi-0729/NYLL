/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChangeStalkProducts
import Nyll.EtaleCohomology.Sites.DirectImageBaseChange
import Nyll.EtaleCohomology.Sites.PushforwardStalkComposition
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The canonical base-change map on geometric stalk components

The direct-image composition square preserves the actual restriction of
germs to successive geometric lifts. Its mate therefore commutes with the
inverse-image units on stalks. On a scheme pullback these component equations
give the canonical product diagram, without any finiteness assumption.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

private lemma compositionComponentDiagram
    {C : Type*} [Category C] {A B D E Z P Q : C}
    (σ : A ⟶ B) (δ : B ⟶ D) (α : A ⟶ E) (ε : E ⟶ D)
    (c₁ : E ⟶ Z) (c₂ : D ⟶ Z) (cf : A ⟶ P) (cg' : P ⟶ Z)
    (cg : B ⟶ Q) (cf' : Q ⟶ Z)
    (hσδ : σ ≫ δ = α ≫ ε) (hε : ε ≫ c₂ = c₁)
    (hα : α ≫ c₁ = cf ≫ cg') (hδ : δ ≫ c₂ = cg ≫ cf') :
    σ ≫ cg ≫ cf' = cf ≫ cg' := by
  rw [← hδ, ← Category.assoc, hσδ, Category.assoc, hε, hα]

private lemma mateComponentDiagram
    {C : Type*} [Category C] {A B D E H J L M Z : C}
    (ν : A ⟶ B) (a : B ⟶ D) (β : D ⟶ E) (d : E ⟶ Z)
    (b : B ⟶ H) (c : H ⟶ E) (f : A ⟶ J) (σ : J ⟶ H)
    (r : J ⟶ L) (l : L ⟶ Z) (k : A ⟶ M) (η : M ⟶ L)
    (hng : b ≫ c = a ≫ β) (hnf : f ≫ r = k ≫ η)
    (hu : ν ≫ b = f ≫ σ) (hs : σ ≫ c ≫ d = r ≫ l) :
    (ν ≫ a) ≫ β ≫ d = k ≫ η ≫ l := by
  calc
    (ν ≫ a) ≫ β ≫ d = ν ≫ (a ≫ β) ≫ d := by simp only [Category.assoc]
    _ = ν ≫ (b ≫ c) ≫ d := congrArg (fun e => ν ≫ e ≫ d) hng.symm
    _ = (ν ≫ b) ≫ c ≫ d := by simp only [Category.assoc]
    _ = (f ≫ σ) ≫ c ≫ d := congrArg (fun e => e ≫ c ≫ d) hu
    _ = f ≫ r ≫ l := (Category.assoc _ _ _).trans (congrArg (fun e => f ≫ e) hs)
    _ = (f ≫ r) ≫ l := (Category.assoc _ _ _).symm
    _ = (k ≫ η) ≫ l := congrArg (fun e => e ≫ l) hnf
    _ = k ≫ η ≫ l := Category.assoc _ _ _

private lemma productComponentDiagram
    {C : Type*} [Category C] {A B D P Q S T : C}
    (a : A ⟶ B) (β : B ⟶ D) (c' : D ⟶ P) (π' : P ⟶ T)
    (c : A ⟶ Q) (π : Q ⟶ S) (b : S ⟶ T) (m : Q ⟶ P)
    (cf' : D ⟶ T) (cf : A ⟶ S)
    (hc' : c' ≫ π' = cf') (hc : c ≫ π = cf)
    (hm : m ≫ π' = π ≫ b) (hscalar : a ≫ β ≫ cf' = cf ≫ b) :
    (a ≫ β ≫ c') ≫ π' = (c ≫ m) ≫ π' := by
  calc
    (a ≫ β ≫ c') ≫ π' = a ≫ β ≫ cf' := by rw [Category.assoc, Category.assoc, hc']
    _ = cf ≫ b := hscalar
    _ = (c ≫ π) ≫ b := congrArg (fun e => e ≫ b) hc.symm
    _ = c ≫ (π ≫ b) := Category.assoc _ _ _
    _ = c ≫ (m ≫ π') := congrArg (fun e => c ≫ e) hm.symm
    _ = (c ≫ m) ≫ π' := (Category.assoc _ _ _).symm

private lemma mapCompositionSquare
    {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {A B E Z : C} (a : A ⟶ B) (b : B ⟶ Z) (c : A ⟶ E) (d : E ⟶ Z)
    (h : a ≫ b = c ≫ d) : Φ.map a ≫ Φ.map b = Φ.map c ≫ Φ.map d :=
  (Φ.map_comp a b).symm.trans ((congrArg Φ.map h).trans (Φ.map_comp c d))

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
  (s : {s : Spec (.of Ω) ⟶ X' // s ≫ f' = t})
  (R : Type u) [CommRing R]

omit [IsSepClosed Ω] in
include h in
private theorem squareLift_w : (s.val ≫ g') ≫ f = t ≫ g := by
  rw [Category.assoc, ← h, ← Category.assoc, s.property]

private theorem square_stalkComposition
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardSquareIso f g f' g' h R).hom.app G) ≫
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardCompIso f' g R).hom.app G) =
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardCompIso g' f R).hom.app G) ≫
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((eqToIso (congrArg (fun q : X' ⟶ Y => etalePushforward q R) h.symm)).hom.app G) :=
  mapCompositionSquare (Scheme.pointSmallEtale (t ≫ g)).sheafFiber _ _ _ _
    (congrArg (fun k => k.app G) (etalePushforwardSquareIso_hom_comp f g f' g' h R))

private theorem square_stalkCongr
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((eqToIso (congrArg (fun q : X' ⟶ Y => etalePushforward q R) h.symm)).hom.app G) ≫
      etalePushforwardStalkComponent (f' ≫ g) (t ≫ g)
        ⟨s.val, by rw [← Category.assoc, s.property]⟩ G =
    etalePushforwardStalkComponent (g' ≫ f) (t ≫ g)
      ⟨s.val, (Category.assoc _ _ _).symm.trans (squareLift_w f g f' g' h t s)⟩ G :=
  etalePushforwardStalkComponent_congr (t ≫ g) R h.symm s.val _ _ G

private theorem square_leftComponents
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardCompIso g' f R).hom.app G) ≫
      etalePushforwardStalkComponent (g' ≫ f) (t ≫ g)
        ⟨s.val, (Category.assoc _ _ _).symm.trans (squareLift_w f g f' g' h t s)⟩ G =
    etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩ ((etalePushforward g' R).obj G) ≫
      etalePushforwardStalkComponent g' (s.val ≫ g') ⟨s.val, rfl⟩ G :=
  etalePushforwardStalkComponent_comp g' f (t ≫ g)
    ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩ ⟨s.val, rfl⟩ R G

private theorem square_rightComponents
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardCompIso f' g R).hom.app G) ≫
      etalePushforwardStalkComponent (f' ≫ g) (t ≫ g)
        ⟨s.val, by rw [← Category.assoc, s.property]⟩ G =
    etalePushforwardStalkComponent g (t ≫ g) ⟨t, rfl⟩ ((etalePushforward f' R).obj G) ≫
      etalePushforwardStalkComponent f' t s G :=
  etalePushforwardStalkComponent_comp f' g (t ≫ g) ⟨t, rfl⟩ s R G

private theorem pushforwardSquare_stalkComponents
    (G : Sheaf X'.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardSquareIso f g f' g' h R).hom.app G) ≫
      etalePushforwardStalkComponent g (t ≫ g) ⟨t, rfl⟩
        ((etalePushforward f' R).obj G) ≫
      etalePushforwardStalkComponent f' t s G =
    etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩
        ((etalePushforward g' R).obj G) ≫
      etalePushforwardStalkComponent g' (s.val ≫ g') ⟨s.val, rfl⟩ G :=
  compositionComponentDiagram _ _ _ _ _ _ _ _ _ _
    (square_stalkComposition f g f' g' h t R G)
    (square_stalkCongr f g f' g' h t s R G)
    (square_leftComponents f g f' g' h t s R G)
    (square_rightComponents g f' t s R G)

private theorem baseChange_stalkUnit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g R).unit.app ((etalePushforward f R).obj F)) ≫
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforward g R).map ((etaleDirectImageBaseChange f g f' g' h R).app F)) =
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforward f R).map ((etalePullbackPushforwardAdjunction g' R).unit.app F)) ≫
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforwardSquareIso f g f' g' h R).hom.app ((etalePullback g' R).obj F)) :=
  mapCompositionSquare (Scheme.pointSmallEtale (t ≫ g)).sheafFiber _ _ _ _
    (etaleDirectImageBaseChange_unit f g f' g' h R F).symm

private theorem baseChange_stalkNaturality_g
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforward g R).map ((etaleDirectImageBaseChange f g f' g' h R).app F)) ≫
      etalePushforwardStalkComponent g (t ≫ g) ⟨t, rfl⟩
        ((etalePushforward f' R).obj ((etalePullback g' R).obj F)) =
    etalePushforwardStalkComponent g (t ≫ g) ⟨t, rfl⟩
        ((etalePullback g R).obj ((etalePushforward f R).obj F)) ≫
      (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleDirectImageBaseChange f g f' g' h R).app F) :=
  etalePushforwardStalkComponent_naturality g (t ≫ g) ⟨t, rfl⟩
    ((etaleDirectImageBaseChange f g f' g' h R).app F)

private theorem baseChange_stalkNaturality_f
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePushforward f R).map ((etalePullbackPushforwardAdjunction g' R).unit.app F)) ≫
      etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩
        ((etalePushforward g' R).obj ((etalePullback g' R).obj F)) =
    etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩ F ≫
      (Scheme.pointSmallEtale (s.val ≫ g')).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g' R).unit.app F) :=
  etalePushforwardStalkComponent_naturality f (t ≫ g)
    ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩
    ((etalePullbackPushforwardAdjunction g' R).unit.app F)

private theorem baseChange_stalkComponent_raw
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((Scheme.pointSmallEtale (t ≫ g)).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g R).unit.app ((etalePushforward f R).obj F)) ≫
      etalePushforwardStalkComponent g (t ≫ g) ⟨t, rfl⟩
        ((etalePullback g R).obj ((etalePushforward f R).obj F))) ≫
      (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleDirectImageBaseChange f g f' g' h R).app F) ≫
      etalePushforwardStalkComponent f' t s ((etalePullback g' R).obj F) =
    etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', squareLift_w f g f' g' h t s⟩ F ≫
      (Scheme.pointSmallEtale (s.val ≫ g')).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g' R).unit.app F) ≫
      etalePushforwardStalkComponent g' (s.val ≫ g') ⟨s.val, rfl⟩
        ((etalePullback g' R).obj F) :=
  mateComponentDiagram _ _ _ _ _ _ _ _ _ _ _ _
    (baseChange_stalkNaturality_g f g f' g' h t R F)
    (baseChange_stalkNaturality_f f g f' g' h t s R F)
    (baseChange_stalkUnit f g f' g' h t R F)
    (pushforwardSquare_stalkComponents f g f' g' h t s R ((etalePullback g' R).obj F))

/-- The actual base-change mate sends each original germ to its inverse-image
germ at the corresponding geometric lift. No finiteness or Cartesian
assumption is needed for this component identity. -/
theorem etaleDirectImageBaseChange_stalkComponent
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (pullbackUnitGeometricStalkIso R g t ((etalePushforward f R).obj F)).hom ≫
      (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleDirectImageBaseChange f g f' g' h R).app F) ≫
      etalePushforwardStalkComponent f' t s ((etalePullback g' R).obj F) =
    etalePushforwardStalkComponent f (t ≫ g)
        ⟨s.val ≫ g', by rw [Category.assoc, ← h, ← Category.assoc, s.property]⟩ F ≫
      (pullbackUnitGeometricStalkIso R g' s.val F).hom := by
  rw [pullbackUnitGeometricStalkIso_hom, pullbackUnitGeometricStalkIso_hom]
  exact baseChange_stalkComponent_raw f g f' g' h t s R F

private theorem baseChangeProduct_inv_π
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (R : Type u) [CommRing R] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (s : {s : Spec (.of Ω) ⟶ pullback f g // s ≫ pullback.snd f g = t}) :
    (baseChangeStalkProductIso f g t R F).inv ≫
      Pi.π (fun z : {z : Spec (.of Ω) ⟶ pullback f g // z ≫ pullback.snd f g = t} =>
        (Scheme.pointSmallEtale z.val).sheafFiber.obj
          ((etalePullback (pullback.fst f g) R).obj F)) s =
    Pi.π (fun z : {z : Spec (.of Ω) ⟶ X // z ≫ f = t ≫ g} =>
        (Scheme.pointSmallEtale z.val).sheafFiber.obj F)
      (geometricLiftBaseChangeEquiv f g t s) ≫
        (pullbackUnitGeometricStalkIso R (pullback.fst f g) s.val F).hom :=
  Pi.map'_comp_π
    (f := fun z : {z : Spec (.of Ω) ⟶ X // z ≫ f = t ≫ g} =>
      (Scheme.pointSmallEtale z.val).sheafFiber.obj F)
    (g := fun z : {z : Spec (.of Ω) ⟶ pullback f g // z ≫ pullback.snd f g = t} =>
      (Scheme.pointSmallEtale z.val).sheafFiber.obj
        ((etalePullback (pullback.fst f g) R).obj F))
    (geometricLiftBaseChangeEquiv f g t)
    (fun z => (pullbackUnitGeometricStalkIso R (pullback.fst f g) z.val F).hom) s

private theorem baseChangeProduct_projectionDiagram
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (R : Type u) [CommRing R] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (s : {s : Spec (.of Ω) ⟶ pullback f g // s ≫ pullback.snd f g = t}) :
    ((pullbackUnitGeometricStalkIso R g t ((etalePushforward f R).obj F)).hom ≫
      (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
          pullback.condition.symm R).app F) ≫
      etalePushforwardStalkComparison (pullback.snd f g) t
        ((etalePullback (pullback.fst f g) R).obj F)) ≫
      Pi.π (fun z : {z : Spec (.of Ω) ⟶ pullback f g // z ≫ pullback.snd f g = t} =>
        (Scheme.pointSmallEtale z.val).sheafFiber.obj
          ((etalePullback (pullback.fst f g) R).obj F)) s =
    (etalePushforwardStalkComparison f (t ≫ g) F ≫
      (baseChangeStalkProductIso f g t R F).inv) ≫
      Pi.π (fun z : {z : Spec (.of Ω) ⟶ pullback f g // z ≫ pullback.snd f g = t} =>
        (Scheme.pointSmallEtale z.val).sheafFiber.obj
          ((etalePullback (pullback.fst f g) R).obj F)) s :=
  productComponentDiagram _ _ _ _ _ _ _ _ _ _
    (etalePushforwardStalkComparison_π (pullback.snd f g) t s
      ((etalePullback (pullback.fst f g) R).obj F))
    (etalePushforwardStalkComparison_π f (t ≫ g) (geometricLiftBaseChangeEquiv f g t s) F)
    (baseChangeProduct_inv_π f g t R F s)
    (etaleDirectImageBaseChange_stalkComponent f g (pullback.snd f g) (pullback.fst f g)
      pullback.condition.symm t s R F)

/-- On an actual scheme pullback, the canonical base-change map commutes
with the products of all geometric stalk components. -/
theorem etaleDirectImageBaseChange_stalk_product
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (R : Type u) [CommRing R] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (pullbackUnitGeometricStalkIso R g t ((etalePushforward f R).obj F)).hom ≫
      (Scheme.pointSmallEtale t).sheafFiber.map
        ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
          pullback.condition.symm R).app F) ≫
      etalePushforwardStalkComparison (pullback.snd f g) t
        ((etalePullback (pullback.fst f g) R).obj F) =
    etalePushforwardStalkComparison f (t ≫ g) F ≫
      (baseChangeStalkProductIso f g t R F).inv := by
  apply Pi.hom_ext
  exact baseChangeProduct_projectionDiagram f g t R F

end EtaleCohomology
