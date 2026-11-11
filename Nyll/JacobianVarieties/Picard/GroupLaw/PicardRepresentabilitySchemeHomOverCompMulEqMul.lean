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
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensorInverse
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

/-- Base change commutes with pulling a module back from the base scheme. -/
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

/-- Rigidify at the second section using the chosen inverse on the base. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M

theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_L ε₁ ε₂ M

/-- Compare the chosen twist with any tensor inverse of the same section restriction. -/
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
        Sub2c.qinv _ ε (M.pullbackCurve w.inv hw' (I2.epsT_comp ε w.inv w.hom hw hww)),
          Sub2c.qinv_isInvertible _ _ _, ⟨Iso.refl _⟩⟩)
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
