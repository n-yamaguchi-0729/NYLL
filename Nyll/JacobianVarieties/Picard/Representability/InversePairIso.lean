/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections.lean
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
import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensorInverse
import Nyll.JacobianVarieties.Picard.Representability.UniqueHom

import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
import Nyll.SchemeTheory.Modules.Invertible.Field
import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.ChangeRigidification
/-!
# Picard isomorphisms from changes of curve and rigidifying section
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.InversePairIsoSections

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

/-- The rigidifying section lies over the identity of the test scheme. -/
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

/-- Base change commutes with the second pullback projection. -/
theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.baseChangeSnd_snd (c := c) ψ

/-- Pulling back a module from the base commutes with base change. -/
def baseChangePullbackIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (Q : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback ψ.1).obj Q) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.baseChangePullbackIso (c := c) ψ Q

end Modules

/-- An invertible module over the spectrum of a field is trivial. -/
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

/-- The chosen tensor inverse is invertible. -/
theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinv_isInvertible ε₁ ε₂ M

/-- The chosen inverse evaluates the restriction at the second section to the unit module. -/
noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.qinvIso ε₁ ε₂ M

/-- Rigidify at the second section by tensoring with its chosen inverse. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist ε₁ ε₂ M

/-- The underlying module of the change of rigidification. -/
theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_L ε₁ ε₂ M

/-- Compare the chosen twist with any specified tensor inverse. -/
def twistIsoOfInverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t)
    (Q : T.Modules) (hQ : (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ Q ≅ 𝟙_ _) :
    (twist ε₁ ε₂ M).L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twistIsoOfInverse ε₁ ε₂ M Q hQ

/-- An isomorphism of line bundles induces an isomorphism of their twists. -/
theorem twist_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε₁ t)
    (e : Nonempty (M.L ≅ M'.L)) : Nonempty ((twist ε₁ ε₂ M).L ≅ (twist ε₁ ε₂ M').L) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_congr ε₁ ε₂ t M M' e

/-- Changing rigidification commutes with pullback along the test scheme. -/
theorem twist_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty (((twist ε₁ ε₂ M).pullbackAlong ψ).L ≅ (twist ε₁ ε₂ (M.pullbackAlong ψ)).L) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_natural ε₁ ε₂ ψ M

/-- Changing rigidification preserves the algebraic equivalence zero condition. -/
theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) :=
  _root_.AlgebraicGeometry.RelPicard.ChangeRigidification.twist_cut ε₁ ε₂ t M hM

end Twist

section Rep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- Isomorphic underlying line bundles have the same classifying morphism. -/
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

/-- Transport the rigidifying section along the inverse curve morphism. -/
def epsT : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' :=
  ⟨ε.1 ≫ g, by rw [Category.assoc, hg]; exact ε.2⟩

include hgf in
/-- The transported section maps back to the original section. -/
theorem epsT_comp : (epsT ε g hg).1 ≫ f = ε.1 := by
  change (ε.1 ≫ g) ≫ f = ε.1
  rw [Category.assoc, hgf, Category.comp_id]

/-- Transport a rigidified line bundle along a curve morphism and change its section. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  Sub2c.twist (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))

/-- The module underlying the transported and newly rigidified line bundle. -/
theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi ε ε' f g hf hg hgf t M).L =
      (Scheme.Modules.pullback (curveChange f hf t)).obj M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c' t)).obj
          (Sub2c.qinv (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))) := rfl

/-- Transport preserves isomorphisms of underlying line bundles. -/
theorem Phi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t)
    (i : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi ε ε' f g hf hg hgf t M).L ≅ (Phi ε ε' f g hf hg hgf t M').L) :=
  Sub2c.twist_congr _ _ t _ _ (RigidifiedLineBundle.pullbackCurve_congr f hf (epsT_comp ε f g hg
    hgf) i)

/-- Transport and change of rigidification commute with test scheme pullback. -/
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

/-- Transport preserves the algebraic equivalence zero condition. -/
theorem Phi_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi ε ε' f g hf hg hgf t M) :=
  Sub2c.twist_cut _ _ t _ (FibrewiseAlgEquivZero.pullbackCurve f hf (epsT_comp ε f g hg hgf) hM)

/-- Representability supplies the morphism induced by transport of line bundles. -/
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

section Comp

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c')
  (f : C' ⟶ C) (g : C ⟶ C') (hf : f ≫ c = c') (hg : g ≫ c' = c) (hgf : g ≫ f = 𝟙 C) (hfg : f ≫ g =
    𝟙 C')

include hgf in
/-- Inverse curve maps induce inverse maps on each pullback. -/
theorem curveChange_comp_eq_id {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c') (c' := c) g hg t ≫ curveChange (c := c) (c' := c') f hf t = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.id_comp, hgf,
      Category.comp_id]
  · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

/-- Transport along inverse curve maps recovers the original underlying line bundle. -/
theorem Phi_Phi {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    :
    Nonempty ((Phi ε' ε g f hg hf hfg t (Phi ε ε' f g hf hg hgf t M)).L ≅ M.L) := by
  let N := Phi ε ε' f g hf hg hgf t M
  let q₁ := Sub2c.qinv (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))
  let Nf := N.pullbackCurve g hg (epsT_comp ε' g f hf hfg)
  let q₂ := Sub2c.qinv (epsT ε' f hf) ε Nf
  have hcc : (Scheme.Modules.pullback (curveChange (c := c') (c' := c) g hg t)).obj
      ((Scheme.Modules.pullback (curveChange (c := c) (c' := c') f hf t)).obj M.L) ≅ M.L :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_comp_eq_id f g hf hg hgf t)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _
  have hpq : (Scheme.Modules.pullback (curveChange (c := c') (c' := c) g hg t)).obj
      ((Scheme.Modules.pullback (pullback.snd c' t)).obj q₁) ≅ (Scheme.Modules.pullback
        (pullback.snd c t)).obj q₁ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_snd g hg t)).app _
  have X : Nf.L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj q₁ :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (hcc ⊗ᵢ hpq)
  have hX : (Scheme.Modules.pullback (rigSection c t ε)).obj Nf.L ≅ q₁ :=
    (Scheme.Modules.pullback _).mapIso X ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (M.rigidified.some ⊗ᵢ Sub2c.sectionPullbackIso t ε q₁) ≪≫ λ_ q₁
  have h12 : q₁ ⊗ q₂ ≅ 𝟙_ _ := Sub2c.inverseOfIso hX (Sub2c.qinvIso (epsT ε' f hf) ε Nf)
  exact ⟨(X ⊗ᵢ Iso.refl _) ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso M.L ((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso h12 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
    ρ_ M.L⟩

/-- The representing morphisms induced by inverse transports compose to the identity. -/
theorem comp_eq_id {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (θ : SchemeHomOver D.toBase D'.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h.classify t M hM) =
          h'.classify t (Phi ε ε' f g hf hg hgf t M) (Phi_cut ε ε' f g hf hg hgf t M hM))
    (θ' : SchemeHomOver D'.toBase D.toBase)
    (hθ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ' (h'.classify t M hM) =
          h.classify t (Phi ε' ε g f hg hf hfg t M) (Phi_cut ε' ε g f hg hf hfg t M hM)) :
    θ.1 ≫ θ'.1 = 𝟙 D.P := by
  have hid : h.classify D.toBase h.poincare h.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h.classify_unique D.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c
      D.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have key : postComp (postComp θ' θ) (h.classify D.toBase h.poincare h.poincare_mem)
      = h.classify D.toBase h.poincare h.poincare_mem := by
    have step : postComp (postComp θ' θ) (h.classify D.toBase h.poincare h.poincare_mem)
        = postComp θ' (postComp θ (h.classify D.toBase h.poincare h.poincare_mem)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [step]
    refine (congrArg (postComp θ') (hθ D.toBase h.poincare h.poincare_mem)).trans ?_
    refine (hθ' D.toBase (Phi ε ε' f g hf hg hgf D.toBase h.poincare)
      (Phi_cut ε ε' f g hf hg hgf D.toBase h.poincare h.poincare_mem)).trans ?_
    exact Sub2c.classify_congr h _ _ _ _ _ (Phi_Phi ε ε' f g hf hg hgf hfg h.poincare)
  rw [hid] at key
  have := congrArg Subtype.val key
  simpa only [postComp, Category.id_comp] using this

end Comp

end I2

end

end JacobianVarieties.Picard.Proofs.InversePairIsoSections

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.InversePairIsoSections
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
universe u

/-- A curve isomorphism with compatible sections induces inverse Picard morphisms. -/
theorem exists_inverse_pair_of_iso_of_sections
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c')
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ (θ : SchemeHomOver D.toBase D'.toBase) (θ' : SchemeHomOver D'.toBase D.toBase),
      θ.1 ≫ θ'.1 = 𝟙 D.P ∧ θ'.1 ≫ θ.1 = 𝟙 D'.P ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj
          M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN := by
  obtain ⟨θ, hθ⟩ := I2.exists_theta ε ε' e.inv e.hom he' he e.hom_inv_id h h'
  obtain ⟨θ', hθ'⟩ := I2.exists_theta ε' ε e.hom e.inv he he' e.inv_hom_id h' h
  refine ⟨θ, θ', I2.comp_eq_id ε ε' e.inv e.hom he' he e.hom_inv_id e.inv_hom_id h h' θ hθ θ' hθ',
    I2.comp_eq_id ε' ε e.hom e.inv he he' e.inv_hom_id e.hom_inv_id h' h θ' hθ' θ hθ, ?_⟩
  intro T t M hM N hN Q hQ hNM
  rw [hθ t M hM]
  apply Sub2c.classify_congr
  have hQinv : (Scheme.Modules.pullback (rigSection c' t ε')).obj
      (M.pullbackCurve e.inv he' (I2.epsT_comp ε e.inv e.hom he e.hom_inv_id)).L ⊗ Q ≅ 𝟙_ _ :=
    (whiskerLeftIso _ (Sub2c.sectionPullbackIso t ε' Q)).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hNM.some.symm ≪≫ N.rigidified.some
  exact ⟨Sub2c.twistIsoOfInverse _ ε' _ Q hQinv ≪≫ hNM.some.symm⟩
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
  NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe NeronModelInfra.schemeHomOverComp_coe
