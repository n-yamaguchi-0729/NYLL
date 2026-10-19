/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusTorsorRegularMap
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneScalarExtension
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Descent of the equivariant Abel factor

The actual group homomorphism and torsor morphism obtained by finite
separable descent retain equivariance and the original Abel factorization.
For positive modulus this constructs the unique pair over the original
field, without a rational point on the curve or on the target torsor.
-/

noncomputable section

universe u v u' v'

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- Faithful monoidal transport reflects equivariance after the actual
comparison maps have identified the transported group and torsor maps. -/
private theorem equivariant_of_faithful_comparison
    {A : Type u} [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    {B : Type u'} [Category.{v'} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    (F : A ⥤ B) [F.Braided] [F.Faithful]
    (G H : CommGrp A) (P Q : A) [ModObj G.X P] [ModObj H.X Q]
    (G' : CommGrp B) (P' : B) [ModObj G'.X P']
    (b : F.mapCommGrp.obj G ⟶ G') (p : F.obj P ⟶ P')
    (φ : G ⟶ H) (f : P ⟶ Q)
    (ψ : G' ⟶ F.mapCommGrp.obj H) (f' : P' ⟶ F.obj Q)
    (hφ : F.mapCommGrp.map φ = b ≫ ψ) (hf : F.map f = p ≫ f') :
    let _ : ModObj (F.mapCommGrp.obj G).X (F.obj P) := F.modObjObj G.X P
    let _ : ModObj (F.mapCommGrp.obj H).X (F.obj Q) := F.modObjObj H.X Q
    (∀ (T : B) (g : T ⟶ (F.mapCommGrp.obj G).X) (x : T ⟶ F.obj P),
      (g • x) ≫ p = (g ≫ b.hom.hom.hom) • (x ≫ p)) →
    (∀ (T : B) (g : T ⟶ G'.X) (x : T ⟶ P'),
      (g • x) ≫ f' = (g ≫ ψ.hom.hom.hom) • (x ≫ f')) →
    ∀ (T : A) (g : T ⟶ G.X) (x : T ⟶ P),
      (g • x) ≫ f = (g ≫ φ.hom.hom.hom) • (x ≫ f) := by
  intro sourceAction targetAction hp hf' T g x
  let b₀ : F.obj G.X ⟶ G'.X := b.hom.hom.hom
  let ψ₀ : G'.X ⟶ F.obj H.X := ψ.hom.hom.hom
  let sourceNative : ModObj (F.obj G.X) (F.obj P) := sourceAction
  let targetNative : ModObj (F.obj H.X) (F.obj Q) := targetAction
  have hp₀ (V : B) (a : V ⟶ F.obj G.X) (y : V ⟶ F.obj P) :
      (a • y) ≫ p = (a ≫ b₀) • (y ≫ p) := hp V a y
  have hf₀ (V : B) (a : V ⟶ G'.X) (y : V ⟶ P') :
      (a • y) ≫ f' = (a ≫ ψ₀) • (y ≫ f') := hf' V a y
  have hφ' : F.map φ.hom.hom.hom = b₀ ≫ ψ₀ :=
    congrArg (fun t => t.hom.hom.hom) hφ
  apply F.map_injective
  calc
    F.map ((g • x) ≫ f) = ((F.map g • F.map x) ≫ p) ≫ f' := by
      rw [F.map_comp, F.map_modObj_smul G.X P, hf, Category.assoc]
    _ = ((F.map g ≫ b₀) • (F.map x ≫ p)) ≫ f' :=
      congrArg (fun t => t ≫ f') (hp₀ (F.obj T) (F.map g) (F.map x))
    _ = ((F.map g ≫ b₀) ≫ ψ₀) •
        ((F.map x ≫ p) ≫ f') :=
      hf₀ (F.obj T) (F.map g ≫ b₀) (F.map x ≫ p)
    _ = F.map (g ≫ φ.hom.hom.hom) • F.map (x ≫ f) := by
      rw [F.map_comp, F.map_comp, hφ', hf, Category.assoc, Category.assoc]
    _ = F.map ((g ≫ φ.hom.hom.hom) • (x ≫ f)) :=
      (F.map_modObj_smul H.X Q (g ≫ φ.hom.hom.hom) (x ≫ f)).symm

/-- A comparison of source objects and a faithful functor reflect an
actual factorization square. -/
private theorem factorization_of_faithful_comparison
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (F : A ⥤ B) [F.Faithful] {U P Q : A} {U' P' : B}
    (a : U ⟶ P) (q : U ⟶ Q) (f : P ⟶ Q)
    (e : U' ≅ F.obj U) (p : F.obj P ⟶ P')
    (a' : U' ⟶ P') (q' : U' ⟶ F.obj Q) (f' : P' ⟶ F.obj Q)
    (ha : e.hom ≫ F.map a ≫ p = a') (hq : e.hom ≫ F.map q = q')
    (hf : F.map f = p ≫ f') (hfac : a' ≫ f' = q') : a ≫ f = q := by
  apply F.map_injective
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ F.map (a ≫ f) = (e.hom ≫ F.map a ≫ p) ≫ f' := by
      rw [F.map_comp, hf]
      simp only [Category.assoc]
    _ = a' ≫ f' := congrArg (fun t => t ≫ f') ha
    _ = q' := hfac
    _ = e.hom ≫ F.map q := hq.symm

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (H : CommGrp (Over (Spec (CommRingCat.of K))))
  (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)

/-- A pair whose actual scalar extension is an equivariant Abel factor is
itself an equivariant Abel factor. This reflects both identities through
faithful field extension and uses the existing comparison morphisms. -/
theorem abelOneMap_equivariantPair_of_scalarExtension
    (L : Type u) [Field L] [Algebra K L] :
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
    ∀ (φ : groupScheme c D ⟶ H) (f : picardOne c D ⟶ Q)
      (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ F.obj Q),
      (GroupSchemes.baseChange (specMap K L)).map φ =
        (groupActualScalarExtensionIso c D L).hom ≫ φL →
      F.map f = (picardOneScalarExtensionIso c D L).hom ≫ fL →
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (g : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
        (g • x) ≫ fL = (g ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      abelOneMap c D ≫ f = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ f = (g ≫ φ.hom.hom.hom) • (x ≫ f) := by
  intro F cL DL HL actionL φ f φL fL hφ hf hAbelL hfL
  have : Flat (specMap K L) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (specMap K L) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstanceAs (Module.FaithfullyFlat K L)))).2
  have ha : (divisorScalarExtensionComplementIso c D L).hom ≫
      F.map (abelOneMap c D) ≫ (picardOneScalarExtensionIso c D L).hom =
        abelOneMap cL DL :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ (picardOneScalarExtensionIso c D L).hom)
        (divisorScalarExtensionComplementIso_hom_map c D L (picardOne c D)
          (abelOneMap c D))).trans
        ((abelOneMap_scalarExtension c D L (𝟙 _)).trans (Category.id_comp _)))
  refine ⟨?_, ?_⟩
  · exact factorization_of_faithful_comparison F (abelOneMap c D) q f
      (divisorScalarExtensionComplementIso c D L) (picardOneScalarExtensionIso c D L).hom
      (abelOneMap cL DL) (modulusMapScalarExtension c D L Q q) fL ha
      (divisorScalarExtensionComplementIso_hom_map c D L Q q) hf hAbelL
  · exact equivariant_of_faithful_comparison F (groupScheme c D) H (picardOne c D) Q
      (groupScheme cL DL) (picardOne cL DL)
      (groupActualScalarExtensionIso c D L).hom (picardOneScalarExtensionIso c D L).hom
      φ f φL fL hφ hf
      (fun _ g x => picardOneScalarExtensionIso_smul c D L g x) hfL

variable [IsSeparated H.X.hom] [IsIso (ModObj.leftSMul H.X Q)]

/-- The two actual finite-separable descents form one unique equivariant
Abel factor over the original field. Both scalar-extension recovery
identities are retained together with the original factorization. -/
theorem existsUnique_equivariantPair_descends_finiteSeparable
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] (hmod : geometricTorsorMapHasModulus c D H Q q) :
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ F.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (g : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
        (g • x) ≫ fL = (g ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
        (GroupSchemes.baseChange (specMap K L)).map fg.1 =
            (groupActualScalarExtensionIso c D L).hom ≫ φL ∧
          F.map fg.2 = (picardOneScalarExtensionIso c D L).hom ≫ fL ∧
          abelOneMap c D ≫ fg.2 = q ∧
          ∀ (T : Over (Spec (CommRingCat.of K)))
            (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
            (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  intro F cL DL HL actionL φL fL hAbelL hfL
  obtain ⟨f, hf, hfUnique⟩ := existsUnique_picardOneMap_descends_finiteSeparable
    c D H Q q L hmod φL fL hAbelL hfL
  obtain ⟨φ, hφ, hφUnique⟩ := existsUnique_groupHom_descends_finiteSeparable
    c D H Q q L hmod φL fL hAbelL hfL
  refine ⟨(φ, f), ⟨hφ, hf,
    abelOneMap_equivariantPair_of_scalarExtension c D H Q q L
      φ f φL fL hφ hf hAbelL hfL⟩, ?_⟩
  intro fg hfg
  exact Prod.ext (hφUnique fg.1 hfg.1) (hfUnique fg.2 hfg.2.1)

/-- Positive full geometric modulus gives a unique equivariant Abel factor
over any field. The finite separable complement point, both descended
morphisms, and their compatibilities are constructed internally. -/
theorem existsUnique_picardOneMapFromGeometricModulus_positive_unpointed
    (hd : 0 < d) (hmod : geometricTorsorMapHasModulus c D H Q q) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  obtain ⟨E, hfinite, hseparable, hE⟩ :=
    exists_finiteSeparableExtension_picardOneMap c D H Q q hd hmod (AlgebraicClosure K)
  have : Module.Finite K E := hfinite
  have : Algebra.IsSeparable K E := hseparable
  let F := Over.pullback (specMap K E)
  let HE := (GroupSchemes.baseChange (specMap K E)).obj H
  let _ : ModObj HE.X (F.obj Q) := F.modObjObj H.X Q
  obtain ⟨fgE, hfgE, _⟩ := hE
  obtain ⟨fg, hfg, _⟩ := existsUnique_equivariantPair_descends_finiteSeparable
    c D H Q q E hmod fgE.1 fgE.2 hfgE.1 hfgE.2
  refine ⟨fg, hfg.2.2, ?_⟩
  intro fg' hfg'
  obtain ⟨hφ, hf⟩ := abelOneMap_equivariantPair_ext_unpointed c D
    fg'.1 fg.1 fg'.2 fg.2 hfg'.2 hfg.2.2.2 (hfg'.1.trans hfg.2.2.1.symm)
  exact Prod.ext hφ hf

end AlgebraicGeometry.GeneralizedJacobian
