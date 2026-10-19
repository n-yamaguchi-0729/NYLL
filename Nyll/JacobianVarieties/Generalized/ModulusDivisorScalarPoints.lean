/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelOneScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor
import Nyll.JacobianVarieties.Generalized.DivisorRestrictionScalarExtension
import Nyll.SchemeTheory.CategoryTheory.ScalarTowerMapComparison
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Actual points and basepoints for the scalar-extended full divisor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

private theorem mapTower_conjugation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U V : A} (q : U ⟶ V) {UL : B} {ULM UM : C}
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (qL : UL ⟶ F.obj V) (qM : UM ⟶ H.obj V) (qLM : ULM ⟶ G.obj (F.obj V))
    (hL : a.hom ≫ F.map q = qL) (hM : c.hom ≫ H.map q = qM)
    (hLM : b.hom ≫ G.map qL = qLM) :
    (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ c.symm).hom ≫ qM =
      qLM ≫ e.inv.app V := by
  rw [← hM, ← hLM, ← hL]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.app_inv]
  exact congrArg (fun f => b.hom ≫ G.map a.hom ≫ f) (e.inv.naturality q).symm

private theorem mapTower_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U P : A} {UL PL : B} {UM ULM PM PLM : C} (q : U ⟶ P)
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (pL : F.obj P ≅ PL) (pM : H.obj P ≅ PM) (pLM : G.obj PL ≅ PLM)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    (hL : a.hom ≫ F.map q ≫ pL.hom = qL)
    (hM : c.hom ≫ H.map q ≫ pM.hom = qM)
    (hLM : b.hom ≫ G.map qL ≫ pLM.hom = qLM) :
    (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ c.symm).hom ≫ qM =
      qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.app_inv]
  rw [← hM, ← hLM, ← hL]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (G.map pL.hom) (G.map pL.inv),
    ← G.map_comp, pL.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc, CategoryTheory.Functor.comp_map] using
    congrArg (fun f => b.hom ≫ G.map a.hom ≫ f ≫ pM.hom) (e.inv.naturality q).symm

private theorem mapTower_transport_postcomp
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U P : A} {UL PL : B} {UM ULM PM PLM : C} (q : U ⟶ P)
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (pL : F.obj P ≅ PL) (pM : H.obj P ≅ PM) (pLM : G.obj PL ≅ PLM)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    {R : C} (r : PM ⟶ R)
    (hL : a.hom ≫ F.map q ≫ pL.hom = qL)
    (hM : c.hom ≫ H.map q ≫ pM.hom = qM)
    (hLM : b.hom ≫ G.map qL ≫ pLM.hom = qLM) :
    qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom ≫ r =
      (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ c.symm).hom ≫ qM ≫ r := by
  simpa only [Category.assoc] using congrArg (fun z => z ≫ r)
    (mapTower_transport F G H e q a b c pL pM pLM qL qM qLM hL hM hLM).symm

private theorem mapTower_factorization
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : H ≅ F ⋙ G)
    {U P Q : A} {UL PL : B} {UM ULM PM PLM : C}
    (q : U ⟶ P) (t : U ⟶ Q)
    (a : UL ≅ F.obj U) (b : ULM ≅ G.obj UL) (c : UM ≅ H.obj U)
    (pL : F.obj P ≅ PL) (pM : H.obj P ≅ PM) (pLM : G.obj PL ≅ PLM)
    (qL : UL ⟶ PL) (qM : UM ⟶ PM) (qLM : ULM ⟶ PLM)
    (tL : UL ⟶ F.obj Q) (tM : UM ⟶ H.obj Q) (tLM : ULM ⟶ G.obj (F.obj Q))
    (fM : PM ⟶ H.obj Q)
    (hqL : a.hom ≫ F.map q ≫ pL.hom = qL)
    (hqM : c.hom ≫ H.map q ≫ pM.hom = qM)
    (hqLM : b.hom ≫ G.map qL ≫ pLM.hom = qLM)
    (htL : a.hom ≫ F.map t = tL) (htM : c.hom ≫ H.map t = tM)
    (htLM : b.hom ≫ G.map tL = tLM) (hf : qM ≫ fM = tM) :
    qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom ≫
      fM ≫ e.hom.app Q = tLM := by
  let i := b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ c.symm
  have h₁ := mapTower_transport_postcomp F G H e q a b c pL pM pLM qL qM qLM
    (fM ≫ e.hom.app Q) hqL hqM hqLM
  have h₂ := congrArg (fun z => i.hom ≫ z ≫ e.hom.app Q) hf
  have ht := mapTower_conjugation F G H e t a b c tL tM tLM htL htM htLM
  have h₃ := congrArg (fun z => z ≫ e.hom.app Q) ht
  have hj : e.inv.app Q ≫ e.hom.app Q = 𝟙 (G.obj (F.obj Q)) := e.inv_hom_id_app Q
  simp only [Category.assoc] at h₂
  simp only [Category.assoc, hj, Category.comp_id] at h₃
  exact h₁.trans (h₂.trans h₃)

private theorem complementRestriction_inverse
    {R : Type u} [CommRing R] {X Z Z' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) {i : Z ⟶ X} {i' : Z' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i'] (a : Z' ≅ Z)
    (w : i' = a.hom ≫ i) (w' : i = a.inv ≫ i') :
    modulusComplementRestriction f a.hom w ≫ modulusComplementRestriction f a.inv w' =
      𝟙 _ := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (modulusComplement i).ι).mp
  change (X.homOfLE (modulusComplement_le_of_restriction a.hom w) ≫
    X.homOfLE (modulusComplement_le_of_restriction a.inv w')) ≫
      (modulusComplement i).ι = (𝟙 _) ≫ (modulusComplement i).ι
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Category.id_comp]

/-- The actual inverse lift to the complement of the extended relative divisor. -/
def divisorScalarExtensionPointLift {T : Over (Spec (CommRingCat.of L))}
    (P : (Over.map (specMap K L)).obj T ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L) :=
  modulusScalarExtensionPointLift c (modulusCurveMap D) L P ≫
    modulusComplementRestriction (baseChange K c L) (divisorScalarExtensionModulusIso D L).hom
      (divisorScalarExtensionModulusIso_square D L)

/-- Projection of a lifted point recovers the original point with its original base map. -/
theorem divisorScalarExtensionPoint_lift {T : Over (Spec (CommRingCat.of L))}
    (P : (Over.map (specMap K L)).obj T ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    divisorScalarExtensionPoint c D L (divisorScalarExtensionPointLift c D L P) = P := by
  unfold divisorScalarExtensionPoint divisorScalarExtensionPointLift
  rw [Category.assoc, complementRestriction_inverse, Category.comp_id]
  exact modulusScalarExtensionPoint_lift c (modulusCurveMap D) L P

private theorem divisorScalarExtensionPointLift_inclusion
    {T : Over (Spec (CommRingCat.of L))}
    (P : (Over.map (specMap K L)).obj T ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (divisorScalarExtensionPointLift c D L P).left ≫
        (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι =
      modulusScalarExtensionCurvePoint c (modulusCurveMap D) L P := by
  change ((modulusScalarExtensionPointLift c (modulusCurveMap D) L P).left ≫
    (pullback c (specMap K L)).homOfLE
      (modulusComplement_le_of_restriction (divisorScalarExtensionModulusIso D L).hom
        (divisorScalarExtensionModulusIso_square D L))) ≫
      (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι = _
  rw [Category.assoc, Scheme.homOfLE_ι]
  exact modulusScalarExtensionPointLift_ι c (modulusCurveMap D) L P

/-- Projection of an extended complement point is the projection of the
same point on the full curve, before restricting to the original complement. -/
theorem divisorScalarExtensionPoint_inclusion
    {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (divisorScalarExtensionPoint c D L P).left ≫ (modulusComplement (modulusCurveMap D)).ι =
      (P.left ≫
        (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι) ≫
          pullback.fst c (specMap K L) := by
  change ((P.left ≫ (pullback c (specMap K L)).homOfLE
    (modulusComplement_le_of_restriction (divisorScalarExtensionModulusIso D L).inv
      (divisorScalarExtensionModulusIso_inv_square c D L))) ≫
    modulusComplementBaseChangeMap c (modulusCurveMap D) (specMap K L)) ≫
      (modulusComplement (modulusCurveMap D)).ι = _
  simp only [Category.assoc, modulusComplementBaseChangeMap_ι, Scheme.homOfLE_ι_assoc]

/-- Lifting the projection recovers the same point on the extended complement. -/
theorem divisorScalarExtensionPointLift_point {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    divisorScalarExtensionPointLift c D L (divisorScalarExtensionPoint c D L P) = P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono
    (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι).mp
  rw [divisorScalarExtensionPointLift_inclusion]
  apply pullback.hom_ext
  · change pullback.lift _ _ _ ≫ pullback.fst c (specMap K L) = _
    rw [pullback.lift_fst]
    exact divisorScalarExtensionPoint_inclusion c D L P
  · change pullback.lift _ _ _ ≫ pullback.snd c (specMap K L) = _
    rw [pullback.lift_snd, Category.assoc]
    exact (Over.w P).symm

private theorem scalarPoint_naturality
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Z ⟶ X) [IsClosedImmersion j]
    {T T' : Over (Spec (CommRingCat.of R'))} (g : T' ⟶ T)
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusBaseChange f j (specMap R R'))).ι ≫ baseChange R f R')) :
    modulusScalarExtensionPoint f j R' (g ≫ P) =
      (Over.map (specMap R R')).map g ≫ modulusScalarExtensionPoint f j R' P := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

/-- Projecting a scalar-extended point commutes with every change of its parameter scheme. -/
theorem divisorScalarExtensionPoint_naturality
    {T T' : Over (Spec (CommRingCat.of L))} (f : T' ⟶ T)
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    divisorScalarExtensionPoint c D L (f ≫ P) =
      (Over.map (specMap K L)).map f ≫ divisorScalarExtensionPoint c D L P := by
  unfold divisorScalarExtensionPoint
  rw [Category.assoc]
  exact scalarPoint_naturality c (modulusCurveMap D) f _

/-- The original complement basepoint, lifted to the actual scalar-extended complement. -/
def modulusBasepointScalarExtension
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L) :=
  divisorScalarExtensionPointLift c D L
    (Over.homMk ((𝟙 (Spec (CommRingCat.of L))) ≫ specMap K L)
      (Category.comp_id _) ≫ ε)

/-- The constant family of the extended basepoint projects to the original constant family. -/
theorem modulusBasepointScalarExtension_project
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (T : Over (Spec (CommRingCat.of L))) :
    divisorScalarExtensionPoint c D L
      (Over.homMk T.hom (Category.comp_id _) ≫ modulusBasepointScalarExtension c D L ε) =
        (Over.homMk (T.hom ≫ specMap K L) (Category.comp_id _) :
          (Over.map (specMap K L)).obj T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε := by
  rw [divisorScalarExtensionPoint_naturality, modulusBasepointScalarExtension,
    divisorScalarExtensionPoint_lift]
  apply Over.OverMorphism.ext
  change T.hom ≫ (((𝟙 (Spec (CommRingCat.of L))) ≫ specMap K L) ≫ ε.left) =
    (T.hom ≫ specMap K L) ≫ ε.left
  rw [Category.id_comp, Category.assoc]

/-- Pull a regular map to any target scheme back to the complement of the
whole extended modulus. Group-valued and torsor-valued maps use the same
adjunction and the same comparison of the divisor complements. -/
def modulusMapScalarExtension (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    Over.mk
        ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
          baseChange K c L) ⟶ (Over.pullback (specMap K L)).obj Q :=
  (Over.mapPullbackAdj (specMap K L)).homEquiv _ Q
    (divisorScalarExtensionPoint c D L (𝟙 _) ≫ q)

/-- Evaluation after scalar extension is the adjoint of the original map
on the projection of the same actual complement point. -/
theorem modulusMapScalarExtension_point
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    x ≫ modulusMapScalarExtension c D L Q q =
      (Over.mapPullbackAdj (specMap K L)).homEquiv T Q
        (divisorScalarExtensionPoint c D L x ≫ q) := by
  have hp : divisorScalarExtensionPoint c D L x =
      (Over.map (specMap K L)).map x ≫ divisorScalarExtensionPoint c D L (𝟙 _) := by
    simpa only [Category.comp_id] using
      divisorScalarExtensionPoint_naturality c D L x (𝟙 _)
  exact ((Over.mapPullbackAdj (specMap K L)).homEquiv_naturality_left x
    (divisorScalarExtensionPoint c D L (𝟙 _) ≫ q)).symm.trans
      (congrArg ((Over.mapPullbackAdj (specMap K L)).homEquiv T Q)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ q) hp.symm)))

/-- The actual scalar extension of a map commutes with every morphism of
target schemes, including changes of coordinates on a torsor. -/
theorem modulusMapScalarExtension_comp
    (Q Q' : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (g : Q ⟶ Q') :
    modulusMapScalarExtension c D L Q' (q ≫ g) =
      modulusMapScalarExtension c D L Q q ≫ (Over.pullback (specMap K L)).map g := by
  change (Over.mapPullbackAdj (specMap K L)).homEquiv _ Q'
      (divisorScalarExtensionPoint c D L (𝟙 _) ≫ q ≫ g) = _
  rw [← Category.assoc]
  exact (Over.mapPullbackAdj (specMap K L)).homEquiv_naturality_right _ _


/-- The complement of the whole extended divisor is the actual pullback
of the original complement. The inverse is the existing point lift, and the
two inverse identities use the same projection and pullback adjunction. -/
def divisorScalarExtensionComplementIso :
    Over.mk
        ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
          baseChange K c L) ≅
      (Over.pullback (specMap K L)).obj
        (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) := by
  let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
  let UL := Over.mk
    ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
      baseChange K c L)
  let F := Over.pullback (specMap K L)
  let A := Over.mapPullbackAdj (specMap K L)
  let h : UL ⟶ F.obj U := modulusMapScalarExtension c D L U (𝟙 U)
  let i : F.obj U ⟶ UL :=
    divisorScalarExtensionPointLift c D L ((A.homEquiv (F.obj U) U).symm (𝟙 _))
  refine ⟨h, i, ?_, ?_⟩
  · have hinj : Function.Injective (divisorScalarExtensionPoint c D L (T := UL)) :=
      Function.LeftInverse.injective (divisorScalarExtensionPointLift_point c D L)
    apply hinj
    rw [divisorScalarExtensionPoint_naturality]
    change (Over.map (specMap K L)).map h ≫
        divisorScalarExtensionPoint c D L
          (divisorScalarExtensionPointLift c D L
            ((A.homEquiv (F.obj U) U).symm (𝟙 _))) =
      divisorScalarExtensionPoint c D L (𝟙 UL)
    rw [divisorScalarExtensionPoint_lift,
      ← A.homEquiv_naturality_left_symm, Category.comp_id]
    change (A.homEquiv UL U).symm
        ((A.homEquiv UL U) (divisorScalarExtensionPoint c D L (𝟙 UL) ≫ 𝟙 U)) =
      divisorScalarExtensionPoint c D L (𝟙 UL)
    rw [Equiv.symm_apply_apply, Category.comp_id]
  · change i ≫ modulusMapScalarExtension c D L U (𝟙 U) = 𝟙 _
    rw [modulusMapScalarExtension_point, Category.comp_id]
    change (A.homEquiv (F.obj U) U)
        (divisorScalarExtensionPoint c D L
          (divisorScalarExtensionPointLift c D L
            ((A.homEquiv (F.obj U) U).symm (𝟙 _)))) = 𝟙 _
    rw [divisorScalarExtensionPoint_lift, Equiv.apply_symm_apply]

/-- Under the actual complement comparison, extending a regular map is
the ordinary pullback of that map. This retains the full divisor comparison. -/
theorem divisorScalarExtensionComplementIso_hom_map
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    (divisorScalarExtensionComplementIso c D L).hom ≫
        (Over.pullback (specMap K L)).map q =
      modulusMapScalarExtension c D L Q q := by
  change modulusMapScalarExtension c D L
      (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) (𝟙 _) ≫
        (Over.pullback (specMap K L)).map q =
      modulusMapScalarExtension c D L Q q
  exact (modulusMapScalarExtension_comp c D L _ Q (𝟙 _) q).symm.trans
    (congrArg (modulusMapScalarExtension c D L Q) (Category.id_comp q))

/-- The comparison from the complement after two scalar extensions to the direct
complement. The full Cartier divisor is retained in all three comparisons. -/
def divisorScalarExtensionComplementTowerIso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cLM := baseChange L (baseChange K c L) M
    let DLM := (D.changeBaseOfIdentity (specMap K L)).changeBaseOfIdentity
      (f := baseChange K c L) (specMap L M)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM) ≅
      Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM) :=
  scalarTowerComparisonIso (Over.pullback (specMap K M))
    (Over.pullback (specMap K L)) (Over.pullback (specMap L M)) e
    (divisorScalarExtensionComplementIso c D L)
    (divisorScalarExtensionComplementIso (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) M)
    (divisorScalarExtensionComplementIso c D M).symm

/-- Two successive field extensions of a regular map agree with the
direct extension under the actual complement isomorphisms and the native
composition isomorphism for pullbacks. No point of the curve is required. -/
theorem modulusMapScalarExtension_tower_of_iso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let eU := divisorScalarExtensionComplementIso cL DL M ≪≫
      FLM.mapIso (divisorScalarExtensionComplementIso c D L) ≪≫
        (e.app U).symm ≪≫ (divisorScalarExtensionComplementIso c D M).symm
    eU.hom ≫ modulusMapScalarExtension c D M Q q =
      modulusMapScalarExtension cL DL M (FKL.obj Q)
          (modulusMapScalarExtension c D L Q q) ≫ e.inv.app Q := by
  intro cL DL U FKL FLM eU
  exact mapTower_conjugation FKL FLM (Over.pullback (specMap K M)) e q
    (divisorScalarExtensionComplementIso c D L)
    (divisorScalarExtensionComplementIso cL DL M)
    (divisorScalarExtensionComplementIso c D M)
    (modulusMapScalarExtension c D L Q q)
    (modulusMapScalarExtension c D M Q q)
    (modulusMapScalarExtension cL DL M (FKL.obj Q) (modulusMapScalarExtension c D L Q q))
    (divisorScalarExtensionComplementIso_hom_map c D L Q q)
    (divisorScalarExtensionComplementIso_hom_map c D M Q q)
    (divisorScalarExtensionComplementIso_hom_map cL DL M (FKL.obj Q)
      (modulusMapScalarExtension c D L Q q))


/-- The native shared complement comparison intertwines the two actual scalar-extended
maps. Its proof uses the three original pullback squares. -/
theorem modulusMapScalarExtension_complementTowerIso
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let eU := scalarTowerComparisonIso (Over.pullback (specMap K M)) FKL FLM e
      (divisorScalarExtensionComplementIso c D L)
      (divisorScalarExtensionComplementIso cL DL M)
      (divisorScalarExtensionComplementIso c D M).symm
    eU.hom ≫ modulusMapScalarExtension c D M Q q =
      modulusMapScalarExtension cL DL M (FKL.obj Q)
          (modulusMapScalarExtension c D L Q q) ≫ e.inv.app Q := by
  intro cL DL FKL FLM eU
  exact scalarTowerComparisonIso_map FKL FLM (Over.pullback (specMap K M)) e q
    (divisorScalarExtensionComplementIso c D L)
    (divisorScalarExtensionComplementIso cL DL M)
    (divisorScalarExtensionComplementIso c D M)
    (modulusMapScalarExtension c D L Q q)
    (modulusMapScalarExtension c D M Q q)
    (modulusMapScalarExtension cL DL M (FKL.obj Q) (modulusMapScalarExtension c D L Q q))
    (divisorScalarExtensionComplementIso_hom_map c D L Q q)
    (divisorScalarExtensionComplementIso_hom_map c D M Q q)
    (divisorScalarExtensionComplementIso_hom_map cL DL M (FKL.obj Q)
      (modulusMapScalarExtension c D L Q q))


/-- The canonical scalar-tower specialization of the regular-map comparison. -/
theorem modulusMapScalarExtension_tower
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let w : specMap L M ≫ specMap K L = specMap K M := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
    let e : FKM ≅ FKL ⋙ FLM :=
      (eqToIso (congrArg
        (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
          Over.pullbackComp (specMap L M) (specMap K L)
    let eU := divisorScalarExtensionComplementIso cL DL M ≪≫
      FLM.mapIso (divisorScalarExtensionComplementIso c D L) ≪≫
        (e.app U).symm ≪≫ (divisorScalarExtensionComplementIso c D M).symm
    eU.hom ≫ modulusMapScalarExtension c D M Q q =
      modulusMapScalarExtension cL DL M (FKL.obj Q)
          (modulusMapScalarExtension c D L Q q) ≫ e.inv.app Q := by
  intro cL DL U FKL FLM FKM w e
  exact modulusMapScalarExtension_tower_of_iso c D L M Q q e


/-- The intrinsic Abel map commutes with the actual complement and Picard-one
comparisons for one field extension. -/
theorem abelOne_scalarExtension_square
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    (divisorScalarExtensionComplementIso c D L).hom ≫
        (Over.pullback (specMap K L)).map (abelOneMap c D) ≫
          (picardOneScalarExtensionIso c D L).hom =
      abelOneMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (picardOneScalarExtensionIso c D L).hom)
      (divisorScalarExtensionComplementIso_hom_map c D L (picardOne c D)
        (abelOneMap c D))).trans
      ((abelOneMap_scalarExtension c D L (𝟙 _)).trans (Category.id_comp _)))

/-- The intrinsic Abel map is compatible with two successive field
extensions. The comparison of the actual Picard-one schemes is built from
their existing scalar-extension isomorphisms and the native pullback
composition isomorphism; it requires no rational point on the curve. -/
theorem abelOneMap_scalarExtension_tower_of_iso
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let F := Over.pullback (specMap K L)
    let G := Over.pullback (specMap L M)
    let H := Over.pullback (specMap K M)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let P := picardOne c D
    let PL := picardOne cL DL
    let PM := picardOne cM DM
    let PLM := picardOne cLM DLM
    let a : UL ≅ F.obj U := divisorScalarExtensionComplementIso c D L
    let b : ULM ≅ G.obj UL := divisorScalarExtensionComplementIso cL DL M
    let h : UM ≅ H.obj U := divisorScalarExtensionComplementIso c D M
    let pL : F.obj P ≅ PL := picardOneScalarExtensionIso c D L
    let pM : H.obj P ≅ PM := picardOneScalarExtensionIso c D M
    let pLM : G.obj PL ≅ PLM := picardOneScalarExtensionIso cL DL M
    let qM : UM ⟶ PM := abelOneMap cM DM
    let qLM : ULM ⟶ PLM := abelOneMap cLM DLM
    (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ h.symm).hom ≫ qM =
      qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom := by
  intro cL DL cM DM cLM DLM F G H U UL UM ULM P PL PM PLM a b h pL pM pLM qM qLM
  let q : U ⟶ P := abelOneMap c D
  let qL : UL ⟶ PL := abelOneMap cL DL
  exact mapTower_transport F G H e q a b h pL pM pLM qL qM qLM
    (abelOne_scalarExtension_square c D L)
    (abelOne_scalarExtension_square c D M)
    (abelOne_scalarExtension_square cL DL M)


/-- The actual Abel map commutes with the shared complement and Picard-one tower
comparisons. This is calculated from the three scalar-extension Abel squares. -/
theorem abelOneMap_scalarExtensionTowerIso
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let F := Over.pullback (specMap K L)
    let G := Over.pullback (specMap L M)
    let H := Over.pullback (specMap K M)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let P := picardOne c D
    let PL := picardOne cL DL
    let PM := picardOne cM DM
    let PLM := picardOne cLM DLM
    let a : UL ≅ F.obj U := divisorScalarExtensionComplementIso c D L
    let b : ULM ≅ G.obj UL := divisorScalarExtensionComplementIso cL DL M
    let h : UM ≅ H.obj U := divisorScalarExtensionComplementIso c D M
    let pL : F.obj P ≅ PL := picardOneScalarExtensionIso c D L
    let pM : H.obj P ≅ PM := picardOneScalarExtensionIso c D M
    let pLM : G.obj PL ≅ PLM := picardOneScalarExtensionIso cL DL M
    let qM : UM ⟶ PM := abelOneMap cM DM
    let qLM : ULM ⟶ PLM := abelOneMap cLM DLM
    (scalarTowerComparisonIso H F G e a b h.symm).hom ≫ qM =
      qLM ≫ (scalarTowerComparisonIso H F G e pL.symm pLM.symm pM).hom := by
  intro cL DL cM DM cLM DLM F G H U UL UM ULM P PL PM PLM a b h pL pM pLM qM qLM
  let q : U ⟶ P := abelOneMap c D
  let qL : UL ⟶ PL := abelOneMap cL DL
  exact scalarTowerComparisonIso_transport F G H e q a b h pL pM pLM qL qM qLM
    (abelOne_scalarExtension_square c D L)
    (abelOne_scalarExtension_square c D M)
    (abelOne_scalarExtension_square cL DL M)


/-- Postcomposing the intrinsic Abel comparison along a field-extension tower agrees
with first transporting the complement and then postcomposing the Abel map. The comparison
uses the existing scalar-extension squares and accepts an arbitrary final target. -/
theorem abelOneMap_scalarExtension_tower_postcomp_of_iso
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M))
    (T : Over (Spec (CommRingCat.of M)))
    (r : picardOne (baseChange K c M) (D.changeBaseOfIdentity (specMap K M)) ⟶ T) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let F := Over.pullback (specMap K L)
    let G := Over.pullback (specMap L M)
    let H := Over.pullback (specMap K M)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let P := picardOne c D
    let PL := picardOne cL DL
    let PM := picardOne cM DM
    let PLM := picardOne cLM DLM
    let a : UL ≅ F.obj U := divisorScalarExtensionComplementIso c D L
    let b : ULM ≅ G.obj UL := divisorScalarExtensionComplementIso cL DL M
    let h : UM ≅ H.obj U := divisorScalarExtensionComplementIso c D M
    let pL : F.obj P ≅ PL := picardOneScalarExtensionIso c D L
    let pM : H.obj P ≅ PM := picardOneScalarExtensionIso c D M
    let pLM : G.obj PL ≅ PLM := picardOneScalarExtensionIso cL DL M
    let qM : UM ⟶ PM := abelOneMap cM DM
    let qLM : ULM ⟶ PLM := abelOneMap cLM DLM
    qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom ≫ r =
      (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ h.symm).hom ≫ qM ≫ r := by
  intro cL DL cM DM cLM DLM F G H U UL UM ULM P PL PM PLM a b h pL pM pLM qM qLM
  let q : U ⟶ P := abelOneMap c D
  let qL : UL ⟶ PL := abelOneMap cL DL
  exact mapTower_transport_postcomp F G H e q a b h pL pM pLM qL qM qLM r
    (abelOne_scalarExtension_square c D L)
    (abelOne_scalarExtension_square c D M)
    (abelOne_scalarExtension_square cL DL M)


/-- A factorization of the Abel map over the final field transports along any pullback
comparison to the iterated scalar extension of the original map. -/
theorem abelOneMap_scalarExtension_tower_factorization
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M]
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let aL : FKL.obj (picardOne c D) ≅ picardOne cL DL :=
      picardOneScalarExtensionIso c D L
    let aM : FKM.obj (picardOne c D) ≅ picardOne cM DM :=
      picardOneScalarExtensionIso c D M
    let aLM : FLM.obj (picardOne cL DL) ≅ picardOne cLM DLM :=
      picardOneScalarExtensionIso cL DL M
    let eP : picardOne cLM DLM ≅ picardOne cM DM :=
      aLM.symm ≪≫ FLM.mapIso aL.symm ≪≫ (e.app (picardOne c D)).symm ≪≫ aM
    let p : FKM.obj Q ⟶ FLM.obj (FKL.obj Q) := e.hom.app Q
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let abelM : UM ⟶ picardOne cM DM := abelOneMap cM DM
    let abelLM : ULM ⟶ picardOne cLM DLM := abelOneMap cLM DLM
    let qM : UM ⟶ FKM.obj Q := modulusMapScalarExtension c D M Q q
    let qLM : ULM ⟶ FLM.obj (FKL.obj Q) :=
      modulusMapScalarExtension cL DL M (FKL.obj Q)
        (modulusMapScalarExtension c D L Q q)
    ∀ (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelM ≫ fM = qM →
      abelLM ≫ (eP.hom ≫ fM ≫ p) = qLM := by
  intro FKL FLM FKM cL DL cM DM cLM DLM aL aM aLM eP p
    UM ULM abelM abelLM qM qLM fM hAbelM
  let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
  let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
  let a : UL ≅ FKL.obj U := divisorScalarExtensionComplementIso c D L
  let b : ULM ≅ FLM.obj UL := divisorScalarExtensionComplementIso cL DL M
  let h : UM ≅ FKM.obj U := divisorScalarExtensionComplementIso c D M
  let abel : U ⟶ picardOne c D := abelOneMap c D
  let abelL : UL ⟶ picardOne cL DL := abelOneMap cL DL
  let qL : UL ⟶ FKL.obj Q := modulusMapScalarExtension c D L Q q
  exact mapTower_factorization FKL FLM FKM e abel q a b h aL aM aLM
    abelL abelM abelLM qL qM qLM fM
    (abelOne_scalarExtension_square c D L)
    (abelOne_scalarExtension_square c D M)
    (abelOne_scalarExtension_square cL DL M)
    (divisorScalarExtensionComplementIso_hom_map c D L Q q)
    (divisorScalarExtensionComplementIso_hom_map c D M Q q)
    (divisorScalarExtensionComplementIso_hom_map cL DL M (FKL.obj Q)
      (modulusMapScalarExtension c D L Q q)) hAbelM


/-- The canonical scalar-tower specialization of the Abel-map comparison. -/
theorem abelOneMap_scalarExtension_tower
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let F := Over.pullback (specMap K L)
    let G := Over.pullback (specMap L M)
    let H := Over.pullback (specMap K M)
    let w : specMap L M ≫ specMap K L = specMap K M := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
    let e : H ≅ F ⋙ G :=
      (eqToIso (congrArg
        (fun f : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback f) w)).symm ≪≫
          Over.pullbackComp (specMap L M) (specMap K L)
    let U := Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)
    let UL := Over.mk ((modulusComplement (modulusCurveMap (c := cL) DL)).ι ≫ cL)
    let UM := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM)
    let ULM := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM)
    let P := picardOne c D
    let PL := picardOne cL DL
    let PM := picardOne cM DM
    let PLM := picardOne cLM DLM
    let a : UL ≅ F.obj U := divisorScalarExtensionComplementIso c D L
    let b : ULM ≅ G.obj UL := divisorScalarExtensionComplementIso cL DL M
    let h : UM ≅ H.obj U := divisorScalarExtensionComplementIso c D M
    let pL : F.obj P ≅ PL := picardOneScalarExtensionIso c D L
    let pM : H.obj P ≅ PM := picardOneScalarExtensionIso c D M
    let pLM : G.obj PL ≅ PLM := picardOneScalarExtensionIso cL DL M
    let qM : UM ⟶ PM := abelOneMap cM DM
    let qLM : ULM ⟶ PLM := abelOneMap cLM DLM
    (b ≪≫ G.mapIso a ≪≫ (e.app U).symm ≪≫ h.symm).hom ≫ qM =
      qLM ≫ (pLM.symm ≪≫ G.mapIso pL.symm ≪≫ (e.app P).symm ≪≫ pM).hom := by
  intro cL DL cM DM cLM DLM F G H w e
  exact abelOneMap_scalarExtension_tower_of_iso c D L M e

/-- Projection of an extended complement point commutes with restriction
along the same morphism of full modulus subschemes. -/
theorem divisorScalarExtensionPoint_restriction
    {e : ℕ} (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
    (j : E.I.subscheme ⟶ D.I.subscheme)
    (w : modulusCurveMap E = j ≫ modulusCurveMap D)
    {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    let r := modulusComplementRestriction c j w
    let rL := modulusComplementRestriction (baseChange K c L)
      (divisorRestrictionScalarMap D E j w L) (divisorRestrictionScalarMap_square D E j w L)
    divisorScalarExtensionPoint c E L (P ≫ rL) =
      divisorScalarExtensionPoint c D L P ≫ r := by
  intro r rL
  have hr : r.left ≫ (modulusComplement (modulusCurveMap E)).ι =
      (modulusComplement (modulusCurveMap D)).ι :=
    Scheme.homOfLE_ι C (modulusComplement_le_of_restriction j w)
  have hrL : rL.left ≫
      (modulusComplement (modulusCurveMap (E.changeBaseOfIdentity (specMap K L)))).ι =
      (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι :=
    Scheme.homOfLE_ι (pullback c (specMap K L))
      (modulusComplement_le_of_restriction (divisorRestrictionScalarMap D E j w L)
        (divisorRestrictionScalarMap_square D E j w L))
  apply Over.OverMorphism.ext
  apply (cancel_mono (modulusComplement (modulusCurveMap E)).ι).mp
  calc
    _ = ((P ≫ rL).left ≫
        (modulusComplement (modulusCurveMap (E.changeBaseOfIdentity (specMap K L)))).ι) ≫
          pullback.fst c (specMap K L) :=
      divisorScalarExtensionPoint_inclusion c E L (P ≫ rL)
    _ = (P.left ≫
        (modulusComplement (modulusCurveMap (c := baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)))).ι) ≫
          pullback.fst c (specMap K L) := by
      change ((P.left ≫ rL.left) ≫ _) ≫ _ = _
      rw [Category.assoc P.left rL.left, hrL]
    _ = (divisorScalarExtensionPoint c D L P).left ≫
        (modulusComplement (modulusCurveMap D)).ι :=
      (divisorScalarExtensionPoint_inclusion c D L P).symm
    _ = _ := by
      change _ = ((divisorScalarExtensionPoint c D L P).left ≫ r.left) ≫
        (modulusComplement (modulusCurveMap E)).ι
      rw [Category.assoc, hr]

/-- Restricting a regular map to a smaller open commutes with its actual
scalar extension, retaining the entire divisor rather than only its support. -/
theorem modulusMapScalarExtension_restriction
    {e : ℕ} (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
    (j : E.I.subscheme ⟶ D.I.subscheme)
    (w : modulusCurveMap E = j ≫ modulusCurveMap D)
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ c) ⟶ Q) :
    let r := modulusComplementRestriction c j w
    let rL := modulusComplementRestriction (baseChange K c L)
      (divisorRestrictionScalarMap D E j w L) (divisorRestrictionScalarMap_square D E j w L)
    modulusMapScalarExtension c D L Q (r ≫ q) =
      rL ≫ modulusMapScalarExtension c E L Q q := by
  intro r rL
  have hδ : divisorScalarExtensionPoint c D L (𝟙 _) ≫ r =
      (Over.map (specMap K L)).map rL ≫ divisorScalarExtensionPoint c E L (𝟙 _) := by
    have h : divisorScalarExtensionPoint c E L ((𝟙 _) ≫ rL) =
        divisorScalarExtensionPoint c D L (𝟙 _) ≫ r :=
      divisorScalarExtensionPoint_restriction c D L E j w (𝟙 _)
    have hn := divisorScalarExtensionPoint_naturality c E L rL (𝟙 _)
    rw [Category.id_comp] at h
    rw [Category.comp_id] at hn
    exact h.symm.trans hn
  exact (congrArg ((Over.mapPullbackAdj (specMap K L)).homEquiv _ Q)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun p => p ≫ q) hδ).trans (Category.assoc _ _ _)))).trans
    ((Over.mapPullbackAdj (specMap K L)).homEquiv_naturality_left rL
      (divisorScalarExtensionPoint c E L (𝟙 _) ≫ q))

end AlgebraicGeometry.GeneralizedJacobian
