/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneIntrinsicTorsor
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The intrinsic tensor action on sheaf sections, with its actual group-action laws -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Actual rigidified tensor action on the pointwise product presheaf. -/
def modulusPicardOneTensorActionRaw :
    modulusPicardZeroPresheaf c i ⊗ modulusPicardOnePresheaf c i ⟶
      modulusPicardOnePresheaf c i where
  app T := TypeCat.ofHom (fun x => modulusPicardOneAction c i T.unop x.1 x.2)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    exact (modulusPicardOneAction_naturality c i f.unop x.1 x.2).symm

/-- Left exact sheafification transports the actual tensor action. -/
def modulusPicardOneTensorAction :
    modulusPicardZeroSheaf c i ⊗ modulusPicardOneSheaf c i ⟶ modulusPicardOneSheaf c i :=
  (prodComparisonIso
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))
      (modulusPicardZeroPresheaf c i) (modulusPicardOnePresheaf c i)).inv ≫
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).map
      (modulusPicardOneTensorActionRaw c i)

private theorem toSheafify_tensor_comparison
    (F G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1)) :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (F ⊗ G) ≫
      (prodComparisonIso
        (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))
        F G).hom.hom =
      toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) F ⊗ₘ
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) G := by
  ext T x
  apply Prod.ext
  · change (((presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Type (u + 1))).map (fst F G)).hom.app T)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (F ⊗ G)).app T x) = _
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (fst F G)) T) x).symm
  · change (((presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (Type (u + 1))).map (snd F G)).hom.app T)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (F ⊗ G)).app T x) = _
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (snd F G)) T) x).symm

omit [GeometricallyIntegral c] in
/-- The sheafified action is exactly tensor product on every actual pair of raw classes. -/
theorem modulusPicardOneTensorAction_actual :
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardZeroPresheaf c i) ⊗ₘ
      toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)) ≫ (modulusPicardOneTensorAction c i).hom =
      modulusPicardOneTensorActionRaw c i ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardOnePresheaf c i) := by
  rw [← toSheafify_tensor_comparison]
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  let e := prodComparisonIso S (modulusPicardZeroPresheaf c i) (modulusPicardOnePresheaf c i)
  change (_ ≫ e.hom.hom) ≫ (e.inv.hom ≫ (S.map (modulusPicardOneTensorActionRaw c i)).hom) = _
  have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
    congrArg (fun v : S.obj (modulusPicardZeroPresheaf c i ⊗
      modulusPicardOnePresheaf c i) ⟶ _ => v.hom) e.hom_inv_id
  rw [Category.assoc, ← Category.assoc e.hom.hom, he, Category.id_comp]
  exact (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusPicardOneTensorActionRaw c i)).symm

/-- Cartesian and categorical products describe the same actual sheaf tensor action. -/
theorem modulusPicardOneTensorAction_torsor :
    Limits.prod.lift
      (fst (modulusPicardZeroSheaf c i) (modulusPicardOneSheaf c i))
      (snd (modulusPicardZeroSheaf c i) (modulusPicardOneSheaf c i)) ≫
        (modulusPicardOneSheafTorsorIso c i).hom ≫ Limits.prod.fst =
      modulusPicardOneTensorAction c i := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  let F := modulusPicardZeroPresheaf c i
  let P := modulusPicardOnePresheaf c i
  let q : F ⊗ P ⟶ F ⨯ P := Limits.prod.lift (fst F P) (snd F P)
  let q' : S.obj F ⊗ S.obj P ⟶ S.obj F ⨯ S.obj P :=
    Limits.prod.lift (fst (S.obj F) (S.obj P)) (snd (S.obj F) (S.obj P))
  let e := prodComparisonIso S F P
  let e' := Limits.PreservesLimitPair.iso S F P
  have hq : S.map q ≫ e'.hom = e.hom ≫ q' := by
    change S.map q ≫ Limits.prodComparison S F P =
      CartesianMonoidalCategory.prodComparison S F P ≫ q'
    apply Limits.prod.hom_ext
    · simp only [Category.assoc,
        Limits.prodComparison_fst, ← S.map_comp, q, Limits.prod.lift_fst,
        q', CartesianMonoidalCategory.prodComparison_fst]
    · simp only [Category.assoc,
        Limits.prodComparison_snd, ← S.map_comp, q, Limits.prod.lift_snd,
        q', CartesianMonoidalCategory.prodComparison_snd]
  have hq' : q' ≫ e'.inv = e.inv ≫ S.map q := by
    apply (cancel_mono e'.hom).mp
    rw [Category.assoc, e'.inv_hom_id, Category.comp_id,
      Category.assoc, hq, ← Category.assoc, e.inv_hom_id]
    exact (Category.id_comp q').symm
  have ha : modulusPicardOneTensorActionRaw c i = q ≫ modulusPicardOneActionMap c i := by
    ext T x
    have hf := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Limits.prod.lift_fst (fst F P) (snd F P)) T) x
    have hs := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Limits.prod.lift_snd (fst F P) (snd F P)) T) x
    exact (congrArg₂ (modulusPicardOneAction c i T.unop) hf hs).symm
  rw [modulusPicardOneSheafTorsorIso_action]
  change q' ≫ e'.inv ≫ S.map (modulusPicardOneActionMap c i) = _
  rw [← Category.assoc, hq', Category.assoc, ← S.map_comp, ← ha]
  rfl

/-- The intrinsic action of the actual zero group sheaf, without a rational basepoint. -/
def modulusPicardOneIntrinsicActionMap :
    ((modulusPicardZeroGroupSheaf c i).obj ⋙ forget CommGrpCat.{u + 1}) ⊗
      (modulusPicardOneSheaf c i).obj ⟶ (modulusPicardOneSheaf c i).obj :=
  ((modulusPicardZeroGroupSheafForgetIso c i).hom ⊗ₘ 𝟙 _) ≫
    (modulusPicardOneTensorAction c i).hom

/-- Intrinsic tensor action on sections over any test scheme. -/
def modulusPicardOneIntrinsicAction (T : Over (Spec (CommRingCat.of R)))
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardOneSheaf c i).obj.obj (op T) :=
  (modulusPicardOneIntrinsicActionMap c i).app (op T) (g, x)

omit [GeometricallyIntegral c] in
/-- The intrinsic action is natural in the test scheme. -/
theorem modulusPicardOneIntrinsicAction_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardOneSheaf c i).obj.map f.op (modulusPicardOneIntrinsicAction c i T g x) =
      modulusPicardOneIntrinsicAction c i T'
        ((modulusPicardZeroGroupSheaf c i).obj.map f.op g)
        ((modulusPicardOneSheaf c i).obj.map f.op x) := by
  let a : (((modulusPicardZeroGroupSheaf c i).obj ⋙ forget CommGrpCat.{u + 1}) ⊗
    (modulusPicardOneSheaf c i).obj).obj (op T) := (g, x)
  exact ((modulusPicardOneIntrinsicActionMap c i).naturality_apply f.op a).symm

omit [GeometricallyIntegral c] in
/-- On original rigidified classes, the intrinsic action is their actual tensor product. -/
theorem modulusPicardOneIntrinsicAction_actual
    (T : Over (Spec (CommRingCat.of R)))
    (g : (modulusPicardZeroGroupPresheaf c i).obj (op T))
    (x : ModulusPicardOneClasses c i T) :
    modulusPicardOneIntrinsicAction c i T
      (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) x) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) (modulusPicardOneAction c i T g x) := by
  have hz := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toModulusPicardZeroGroupSheaf_forgetIso c i) (op T)) g
  let a : (modulusPicardZeroPresheaf c i ⊗ modulusPicardOnePresheaf c i).obj (op T) := (g, x)
  have h := congrArg (fun α : modulusPicardZeroPresheaf c i ⊗
    modulusPicardOnePresheaf c i ⟶ (modulusPicardOneSheaf c i).obj =>
      α.app (op T) a) (modulusPicardOneTensorAction_actual c i)
  change (modulusPicardOneTensorAction c i).hom.app (op T)
    ((modulusPicardZeroGroupSheafForgetIso c i).hom.app (op T)
      (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g),
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) x) = _
  exact (congrArg (fun z => (modulusPicardOneTensorAction c i).hom.app (op T)
    (z, (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardOnePresheaf c i)).app (op T) x)) hz).trans h

omit [GeometricallyIntegral c] in
/-- The unit of the canonical zero group acts identically on every intrinsic One section. -/
theorem modulusPicardOneIntrinsicAction_one
    (T : Over (Spec (CommRingCat.of R)))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    modulusPicardOneIntrinsicAction c i T 1 x = x := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let ηP := toSheafify J (modulusPicardOnePresheaf c i)
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (modulusPicardOneSheaf c i).2).isSeparated _ (Presheaf.imageSieve_mem J ηP x)).ext
  rintro Y f ⟨p, hp⟩
  change ηP.app (op Y) p = (modulusPicardOneSheaf c i).obj.map f.op x at hp
  rw [modulusPicardOneIntrinsicAction_naturality, map_one, ← hp]
  let η : (modulusPicardZeroGroupPresheaf c i).obj (op Y) →*
      (modulusPicardZeroGroupSheaf c i).obj.obj (op Y) :=
    ((toSheafify J (modulusPicardZeroGroupPresheaf c i)).app (op Y)).hom
  have h := modulusPicardOneIntrinsicAction_actual c i Y
    (1 : (modulusPicardZeroGroupPresheaf c i).obj (op Y)) p
  exact (congrArg (fun z => modulusPicardOneIntrinsicAction c i Y z
    (ηP.app (op Y) p)) η.map_one).symm.trans
      (h.trans (congrArg (ηP.app (op Y)) (modulusPicardOneAction_one c i Y p)))

omit [GeometricallyIntegral c] in
/-- Tensor associativity survives sheafification for the actual canonical zero group law. -/
theorem modulusPicardOneIntrinsicAction_mul
    (T : Over (Spec (CommRingCat.of R)))
    (g h : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    modulusPicardOneIntrinsicAction c i T (g * h) x =
      modulusPicardOneIntrinsicAction c i T g (modulusPicardOneIntrinsicAction c i T h x) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let ηG := toSheafify J (modulusPicardZeroGroupPresheaf c i)
  let ηP := toSheafify J (modulusPicardOnePresheaf c i)
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 (modulusPicardOneSheaf c i).2).isSeparated _
    (J.intersection_covering
      (J.intersection_covering (Presheaf.imageSieve_mem J ηG g)
        (Presheaf.imageSieve_mem J ηG h)) (Presheaf.imageSieve_mem J ηP x))).ext
  rintro Y f ⟨⟨⟨g₀, hg⟩, ⟨h₀, hh⟩⟩, ⟨x₀, hx⟩⟩
  change (ηG.app (op Y)).hom g₀ = (modulusPicardZeroGroupSheaf c i).obj.map f.op g at hg
  change (ηG.app (op Y)).hom h₀ = (modulusPicardZeroGroupSheaf c i).obj.map f.op h at hh
  change ηP.app (op Y) x₀ = (modulusPicardOneSheaf c i).obj.map f.op x at hx
  rw [modulusPicardOneIntrinsicAction_naturality,
    modulusPicardOneIntrinsicAction_naturality, modulusPicardOneIntrinsicAction_naturality,
    map_mul, ← hg, ← hh, ← hx]
  let η : (modulusPicardZeroGroupPresheaf c i).obj (op Y) →*
      (modulusPicardZeroGroupSheaf c i).obj.obj (op Y) := (ηG.app (op Y)).hom
  have ha := modulusPicardOneIntrinsicAction_actual c i Y (g₀ * h₀) x₀
  have hb := modulusPicardOneIntrinsicAction_actual c i Y h₀ x₀
  have hc := modulusPicardOneIntrinsicAction_actual c i Y g₀
    (modulusPicardOneAction c i Y h₀ x₀)
  have hraw := modulusPicardOneAction_mul c i Y g₀ h₀ x₀
  exact (congrArg (fun z => modulusPicardOneIntrinsicAction c i Y z
    (ηP.app (op Y) x₀)) (η.map_mul g₀ h₀).symm).trans
      (ha.trans ((congrArg (ηP.app (op Y)) hraw).trans
        (hc.symm.trans (congrArg (modulusPicardOneIntrinsicAction c i Y (η g₀)) hb.symm))))


end AlgebraicGeometry.GeneralizedJacobian
