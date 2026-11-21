/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
import Nyll.JacobianVarieties.Picard.Representability.UniqueHom

import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
import Nyll.SchemeTheory.Modules.Invertible.Field
import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.ChangeRigidification

/-!
# Comparing Picard representations at different rigidifying sections

Twisting by the inverse of the restriction at a section constructs mutually inverse
comparison morphisms between the corresponding represented Picard schemes.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.InversePairSections


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
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  {D₁ D₂ : RelativePic0Designation R c}
  (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
  (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)

theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M')
    (i : Nonempty (M.L ≅ M'.L)) :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

theorem exists_theta :
    ∃ θ : SchemeHomOver D₁.toBase D₂.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₁ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h₁.classify t M hM) =
          h₂.classify t (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M)
            (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ t M hM) := by
  obtain ⟨θ, hθ, -⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform h₂ h₁
    (fun t M => _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M)
    (fun t M M' e => _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_congr ε₁ ε₂ t M
      M' e)
    (fun ψ M => _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_natural ε₁ ε₂ ψ M)
    (fun t M hM => _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ t M hM)
  exact ⟨θ, fun t M hM => hθ t M hM⟩

end Rep

section Comp

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem twist_twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty ((_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₂ ε₁
      (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M)).L ≅ M.L) := by
  let q₁ := _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv ε₁ ε₂ M
  let q₂ := _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv ε₂ ε₁
    (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M)
  have hX : (Scheme.Modules.pullback (rigSection c t ε₁)).obj
    (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M).L ≅ q₁ :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (M.rigidified.some ⊗ᵢ
        _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.sectionPullbackIso t ε₁ q₁) ≪≫ λ_ q₁
  have h12 : q₁ ⊗ q₂ ≅ 𝟙_ _ := _root_.CategoryTheory.MonoidalCategory.tensorInverseOfIso hX
    (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinvIso ε₂ ε₁
    (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M))
  exact ⟨α_ _ _ _ ≪≫
    whiskerLeftIso M.L ((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso h12 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
    ρ_ M.L⟩

end Comp

section Assembly

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem comp_eq_id (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D₁ D₂ : RelativePic0Designation R c}
    (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
    (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)
    (θ : SchemeHomOver D₁.toBase D₂.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₁ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h₁.classify t M hM) = h₂.classify t
          (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M)
          (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ t M hM))
    (θ' : SchemeHomOver D₂.toBase D₁.toBase)
    (hθ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₂ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ' (h₂.classify t M hM) = h₁.classify t
          (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₂ ε₁ M)
          (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₂ ε₁ t M hM)) :
    θ.1 ≫ θ'.1 = 𝟙 D₁.P := by
  have hid : h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h₁.classify_unique D₁.toBase _ _ _
      ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D₁.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have key : postComp (postComp θ' θ) (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)
      = h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem := by
    have step : postComp (postComp θ' θ) (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)
        = postComp θ' (postComp θ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [step]
    refine (congrArg (postComp θ') (hθ D₁.toBase h₁.poincare h₁.poincare_mem)).trans ?_
    refine (hθ' D₁.toBase (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂
      h₁.poincare)
      (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ D₁.toBase
        h₁.poincare h₁.poincare_mem)).trans ?_
    exact classify_congr h₁ _ _ _ _ _ (twist_twist ε₁ ε₂ h₁.poincare)
  rw [hid] at key
  have := congrArg Subtype.val key
  simpa only [postComp, Category.id_comp] using this

end Assembly

end Sub2c

end

theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D D' : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c ε' (algEquivZeroCut c ε') D') :
    ∃ (θ : SchemeHomOver D.toBase D'.toBase) (θ' : SchemeHomOver D'.toBase D.toBase),
      θ.1 ≫ θ'.1 = 𝟙 D.P ∧ θ'.1 ≫ θ.1 = 𝟙 D'.P ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN := by
  obtain ⟨θ, hθ⟩ := Sub2c.exists_theta ε ε' h h'
  obtain ⟨θ', hθ'⟩ := Sub2c.exists_theta ε' ε h' h
  refine ⟨θ, θ', Sub2c.comp_eq_id ε ε' h h' θ hθ θ' hθ', Sub2c.comp_eq_id ε' ε h' h θ' hθ' θ hθ, ?_⟩
  intro T t M hM N hN Q hQ hNM
  rw [hθ t M hM]
  apply Sub2c.classify_congr
  have hQinv : (Scheme.Modules.pullback (rigSection c t ε')).obj M.L ⊗ Q ≅ 𝟙_ _ :=
    (whiskerLeftIso _ (_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.sectionPullbackIso
      t ε' Q)).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hNM.some.symm ≪≫ N.rigidified.some
  exact ⟨_root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twistIsoOfInverse ε ε' M Q hQinv
    ≪≫ hNM.some.symm⟩
end JacobianVarieties.Picard.Proofs.InversePairSections
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe NeronModelInfra.schemeHomOverComp_coe
