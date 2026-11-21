/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Tactic.Choose
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.Pullback
public import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
public import Nyll.JacobianVarieties.Picard.Representability.UniqueHom
public import Nyll.JacobianVarieties.Picard.GroupLaw.PicardRepresentabilityPostCompMul
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.SchemeTheory.Modules.Invertible.Field
public import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso
public import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.ChangeRigidification

/-!
# Multiplication for a classified Picard transformation

Tensor compatibility of the rigidified pullback transformation yields multiplication compatibility.
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ClassifiedMultiplication

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

noncomputable section

namespace Sub2c

section Rep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L))
      :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

end Rep

end Sub2c

namespace I2

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c')
  (f : C' ⟶ C) (g : C ⟶ C') (hf : f ≫ c = c') (hg : g ≫ c' = c) (hgf : g ≫ f = 𝟙 C)

/-- Transport the original rigidifying section along the inverse curve map. -/
def epsT : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' :=
  ⟨ε.1 ≫ g, by rw [Category.assoc, hg]; exact ε.2⟩

include hgf in
theorem epsT_comp : (epsT ε g hg).1 ≫ f = ε.1 := by
  change (ε.1 ≫ g) ≫ f = ε.1
  rw [Category.assoc, hgf, Category.comp_id]

/-- Pull a rigidified bundle along the curve map and rigidify at the target section. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist (epsT ε g hg) ε' (M.pullbackCurve
    f hf (epsT_comp ε f g hg hgf))

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi ε ε' f g hf hg hgf t M).L =
      (Scheme.Modules.pullback (curveChange f hf t)).obj M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c' t)).obj
          (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv (epsT ε g hg) ε'
            (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))) := rfl

theorem Phi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t)
    (i : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi ε ε' f g hf hg hgf t M).L ≅ (Phi ε ε' f g hf hg hgf t M').L) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_congr _ _ t _ _
    (RigidifiedLineBundle.pullbackCurve_congr f hf (epsT_comp ε f g hg
    hgf) i)

theorem Phi_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi ε ε' f g hf hg hgf t M).pullbackAlong ψ).L ≅
      (Phi ε ε' f g hf hg hgf t' (M.pullbackAlong ψ)).L) := by
  obtain ⟨i1⟩ := _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_natural (epsT ε g
    hg) ε' ψ (M.pullbackCurve f hf (epsT_comp ε f g hg
    hgf))
  obtain ⟨i2⟩ := _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_congr (epsT ε g hg)
    ε' t' _ _
    ⟨M.pullbackCurvePullbackAlongIso f hf (epsT_comp ε f g hg hgf) ψ⟩
  exact ⟨i1 ≪≫ i2⟩

theorem Phi_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi ε ε' f g hf hg hgf t M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut _ _ t _
    (FibrewiseAlgEquivZero.pullbackCurve f hf (epsT_comp ε f g hg hgf) hM)

theorem exists_theta {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ θ : SchemeHomOver D.toBase D'.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h.classify t M hM) =
          h'.classify t (Phi ε ε' f g hf hg hgf t M) (Phi_cut ε ε' f g hf hg hgf t M hM) := by
  obtain ⟨θ, hθ, -⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform h' h
    (fun t M => Phi ε ε' f g hf hg hgf t M)
    (fun t M M' i => Phi_congr ε ε' f g hf hg hgf t M M' i)
    (fun ψ M => Phi_natural ε ε' f g hf hg hgf ψ M)
    (fun t M hM => Phi_cut ε ε' f g hf hg hgf t M hM)
  exact ⟨θ, fun t M hM => hθ t M hM⟩

end Transform

end I2

/-- Reorder the middle factors in a tensor product of two pairs. -/
def tensorTensorIso {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
    (A B C D : 𝒞) :
    (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  (α_ A B (C ⊗ D)) ≪≫ whiskerLeftIso A ((α_ B C D).symm ≪≫ whiskerRightIso (β_ B C) D ≪≫ α_ C B D)
    ≪≫ (α_ A C (B ⊗ D)).symm

end

end JacobianVarieties.Picard.Proofs.ClassifiedMultiplication

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian

universe u

open _root_.JacobianVarieties.Picard.Proofs.ClassifiedMultiplication in
theorem schemeHomOverComp_mul_eq_mul_of_forall_postComp_classify_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (w : C ≅ C) (hw : w.hom ≫ c = c) (hw' : w.inv ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (P₁ : RigidifiedLineBundle c ε t) (hP₁ : FibrewiseAlgEquivZero P₁)
        (P₂ : RigidifiedLineBundle c ε t) (hP₂ : FibrewiseAlgEquivZero P₂)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (P₂.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) w.inv hw' t)).obj
          P₁.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t P₁ hP₁) = h.classify t P₂ hP₂) :
    ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P :=
        algEquivZeroGroupCut _ _) h).mul s x y) θ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul s
          (NeronModelInfra.schemeHomOverComp x θ) (NeronModelInfra.schemeHomOverComp y θ) := by
  intro T s x y
  have hww : w.hom ≫ w.inv = 𝟙 C := w.hom_inv_id
  let Rel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c ε t → RigidifiedLineBundle c ε t → Prop := fun {T} t M N =>
    ∃ Q : T.Modules, Scheme.Modules.IsInvertible Q ∧
      Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) w.inv hw' t)).obj
        M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c t)).obj Q)
  have key := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classify_rel
    (P := algEquivZeroGroupCut c ε) (P' := algEquivZeroGroupCut c ε) h h θ Rel
    (fun t M hM N hN hrel => by
      obtain ⟨Q, hQ, hiso⟩ := hrel
      exact hθ t M hM N hN Q hQ hiso)
    (fun t M hM => by
      refine ⟨I2.Phi ε ε w.inv w.hom hw' hw hww t M, I2.Phi_cut ε ε w.inv w.hom hw' hw hww t M hM,
        _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv _ ε (M.pullbackCurve w.inv
          hw' (I2.epsT_comp ε w.inv w.hom hw hww)),
          _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv_isInvertible _ _ _,
            ⟨Iso.refl _⟩⟩)
    (fun t M₁ M₂ N₁ N₂ h₁ h₂ => by
      obtain ⟨Q₁, hQ₁, ⟨e₁⟩⟩ := h₁
      obtain ⟨Q₂, hQ₂, ⟨e₂⟩⟩ := h₂
      refine ⟨Q₁ ⊗ Q₂, hQ₁.tensor hQ₂, ⟨?_⟩⟩
      exact (e₁ ⊗ᵢ e₂) ≪≫ tensorTensorIso _ _ _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso _
          _ _).symm))
    s x y
  exact key

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
