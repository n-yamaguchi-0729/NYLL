/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq.lean
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
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensorInverse

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.SchemeTheory.Modules.Invertible.Field
public import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso
public import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.ChangeRigidification

/-!
# Transport of Picard pullback morphisms

Pullback morphisms commute with the classified transport of rigidified line bundles.
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackHomTransport

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

section Monoidal

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]

/-- Tensor inverses of isomorphic objects are isomorphic via the given inverse evaluations. -/
def inverseIso {X X' Q Q' : 𝒞} (eX : X ≅ X') (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) (hQ' : X' ⊗ Q' ≅ 𝟙_ 𝒞) : Q ≅ Q' :=
  _root_.CategoryTheory.MonoidalCategory.tensorInverseIso eX hQ hQ'

/-- Transport the given tensor-inverse evaluation along an isomorphism of its first factor. -/
def inverseOfIso {X Y Q : 𝒞} (eX : X ≅ Y) (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) : Y ⊗ Q ≅ 𝟙_ 𝒞 :=
  _root_.CategoryTheory.MonoidalCategory.tensorInverseOfIso eX hQ

end Monoidal

section Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem rigSection_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.rigSection_snd t ε

/-- Pulling a base module to the curve and then back along the section recovers that module. -/
def sectionPullbackIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (Q : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅ Q :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.sectionPullbackIso t ε Q

theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.baseChangeSnd_snd (c := c) ψ

/-- Pullback from the base commutes with a change of the parameter scheme. -/
def baseChangePullbackIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (Q : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback ψ.1).obj Q) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.baseChangePullbackIso (c := c) ψ Q

end Modules

theorem nonempty_iso_unit_of_field {k : Type u} [Field k] (Q : (Spec (CommRingCat.of k)).Modules)
    (hQ : Scheme.Modules.IsInvertible Q) : Nonempty (Q ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) :=
  _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k Q hQ

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- A chosen tensor inverse of the line bundle restricted to the second rigidifying section. -/
noncomputable def qinv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) : T.Modules :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv ε₁ ε₂ M

theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv_isInvertible ε₁ ε₂ M

/-- The chosen inverse evaluates the restriction at the second section to the unit module. -/
noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinvIso ε₁ ε₂ M

/-- Change the rigidifying section by tensoring with the inverse of its restriction. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M

theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_L ε₁ ε₂ M

/-- Identify the rigidification twist using any specified tensor-inverse evaluation. -/
def twistIsoOfInverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t)
    (Q : T.Modules) (hQ : (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ Q ≅ 𝟙_ _) :
    (twist ε₁ ε₂ M).L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twistIsoOfInverse ε₁ ε₂ M Q hQ

theorem twist_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε₁ t)
    (e : Nonempty (M.L ≅ M'.L)) : Nonempty ((twist ε₁ ε₂ M).L ≅ (twist ε₁ ε₂ M').L) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_congr ε₁ ε₂ t M M' e

theorem twist_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty (((twist ε₁ ε₂ M).pullbackAlong ψ).L ≅ (twist ε₁ ε₂ (M.pullbackAlong ψ)).L) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_natural ε₁ ε₂ ψ M

theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ t M hM

end Twist

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

/-- Transport the section along the specified morphism of curves. -/
def epsT : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' :=
  ⟨ε.1 ≫ g, by rw [Category.assoc, hg]; exact ε.2⟩

include hgf in
theorem epsT_comp : (epsT ε g hg).1 ≫ f = ε.1 := by
  change (ε.1 ≫ g) ≫ f = ε.1
  rw [Category.assoc, hgf, Category.comp_id]

/-- Pull back a rigidified line bundle and adjust its rigidifying section. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  Sub2c.twist (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi ε ε' f g hf hg hgf t M).L =
      (Scheme.Modules.pullback (curveChange f hf t)).obj M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c' t)).obj
          (Sub2c.qinv (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))) := rfl

theorem Phi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t)
    (i : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi ε ε' f g hf hg hgf t M).L ≅ (Phi ε ε' f g hf hg hgf t M').L) :=
  Sub2c.twist_congr _ _ t _ _ (RigidifiedLineBundle.pullbackCurve_congr f hf (epsT_comp ε f g hg
    hgf) i)

theorem Phi_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi ε ε' f g hf hg hgf t M).pullbackAlong ψ).L ≅
      (Phi ε ε' f g hf hg hgf t' (M.pullbackAlong ψ)).L) := by
  obtain ⟨i1⟩ := Sub2c.twist_natural (epsT ε g hg) ε' ψ (M.pullbackCurve f hf (epsT_comp ε f g hg
    hgf))
  obtain ⟨i2⟩ := Sub2c.twist_congr (epsT ε g hg) ε' t' _ _
    ⟨M.pullbackCurvePullbackAlongIso f hf (epsT_comp ε f g hg hgf) ψ⟩
  exact ⟨i1 ≪≫ i2⟩

theorem Phi_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi ε ε' f g hf hg hgf t M) :=
  Sub2c.twist_cut _ _ t _ (FibrewiseAlgEquivZero.pullbackCurve f hf (epsT_comp ε f g hg hgf) hM)

end Transform

end I2

end
end JacobianVarieties.Picard.Proofs.PullbackHomTransport

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.PullbackHomTransport
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
universe u

/-- Pullback morphisms commute with the classified transport of rigidified line bundles. -/
theorem schemeHomOverComp_pullbackHom_eq_of_transport_of_hom_comp_eq
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (W : C ≅ C) (hW : W.hom ≫ c = c) (hW' : W.inv ≫ c = c)
    (α : C' ≅ C') (hα' : α.inv ≫ c' = c')
    (hcomm : α.hom ≫ f = f ≫ W.hom)
    (θW : SchemeHomOver D.toBase D.toBase)
    (hθW : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) W.inv hW' t)).obj
          M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θW (h.classify t M hM) = h.classify t N hN))
    (θα : SchemeHomOver D'.toBase D'.toBase)
    (hθα : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c' ε' t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c') (c' := c') α.inv hα'
          t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θα (h'.classify t M hM) = h'.classify t N hN)) :
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') θW =
      postComp θα (RepresentsRelSubPic.pullbackHom f hf hε h h') := by
  classical
  have hcomm' : α.inv ≫ f = f ≫ W.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, W.hom_inv_id, Category.comp_id]
  let NW : RigidifiedLineBundle c ε D.toBase := I2.Phi ε ε W.inv W.hom hW' hW W.hom_inv_id D.toBase
    h.poincare
  have hNW : FibrewiseAlgEquivZero NW :=
    I2.Phi_cut ε ε W.inv W.hom hW' hW W.hom_inv_id D.toBase h.poincare h.poincare_mem
  let Q : D.P.Modules := Sub2c.qinv (I2.epsT ε W.hom hW) ε
    (h.poincare.pullbackCurve W.inv hW' (I2.epsT_comp ε W.inv W.hom hW W.hom_inv_id))
  have hQ : Scheme.Modules.IsInvertible Q := Sub2c.qinv_isInvertible _ _ _
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c
      D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have hθW' : θW = h.classify D.toBase NW hNW := by
    have key := hθW D.toBase h.poincare h.poincare_mem NW hNW Q hQ ⟨Iso.refl _⟩
    rw [hid] at key
    rw [← key]
    apply Subtype.ext
    exact (Category.id_comp _).symm
  have hL : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') θW =
      h'.classify D.toBase (NW.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε
        hNW) := by
    rw [hθW']
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' D.toBase NW hNW
  have hcc : curveChange f hf D.toBase ≫ curveChange (c := c) (c' := c) W.inv hW' D.toBase =
      curveChange (c := c') (c' := c') α.inv hα' D.toBase ≫ curveChange f hf D.toBase := by
    apply pullback.hom_ext <;>
      simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd,
        Category.comp_id, hcomm']
  have hR : postComp θα (RepresentsRelSubPic.pullbackHom f hf hε h h') =
      h'.classify D.toBase (NW.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε
        hNW) := by
    refine hθα D.toBase (h.poincare.pullbackCurve f hf hε)
      (FibrewiseAlgEquivZero.pullbackCurve f hf hε h.poincare_mem) _ _ Q hQ ⟨?_⟩
    exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hcc).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (curveChange_snd
          f hf D.toBase)).app _))
  exact hL.trans hR.symm
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
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
