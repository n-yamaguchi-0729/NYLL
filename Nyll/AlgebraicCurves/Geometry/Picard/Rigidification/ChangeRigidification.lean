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

module

public import Nyll.SchemeTheory.CategoryTheory.TensorInverseIso
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Modules.Invertible.Field
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensorInverse

/-! # Change of the actual rigidifying section

The inverse bundle is chosen from the original restriction at the second section.
The same choice, evaluation isomorphism and base pullback define the new
rigidification, its naturality and preservation of algebraic equivalence to zero.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra

namespace AlgebraicGeometry.RelPicard.ChangeRigidification

section Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- The given rigidifying section lies over the identity of the test scheme. -/
theorem rigSection_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
  simp only [rigSection, pullback.lift_snd]

/-- Restrict the actual base pullback back along the specified section. -/
def sectionPullbackIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (Q : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅ Q :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_snd t ε)).app Q ≪≫
    (Scheme.Modules.pullbackId _).app Q

/-- The actual base-change map commutes with the second projection. -/
theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
  simp only [baseChangeSnd, pullback.lift_snd]

/-- Compare the two pullbacks of the original base module. -/
def baseChangePullbackIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (Q : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback ψ.1).obj Q) :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm

end Modules

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- The original chosen tensor inverse of the restriction at the second section. -/
noncomputable def qinv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) : T.Modules :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose

/-- The same chosen inverse bundle is invertible. -/
theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.1

/-- The evaluation from the same chosen inverse witness. -/
noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.2.some

/-- Change rigidification using the original inverse choice and evaluation. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t where
  L := M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)
  isInvertible := M.isInvertible.tensor ((qinv_isInvertible ε₁ ε₂ M).pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (sectionPullbackIso t ε₂ _) ≪≫ qinvIso ε₁ ε₂ M⟩

/-- The underlying module is the original bundle tensored with the chosen base inverse. -/
theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) := rfl

/-- Compare the chosen twist with a specified inverse evaluation. -/
def twistIsoOfInverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t)
    (Q : T.Modules) (hQ : (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ Q ≅ 𝟙_ _) :
    (twist ε₁ ε₂ M).L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q :=
  whiskerLeftIso M.L ((Scheme.Modules.pullback _).mapIso (tensorInverseIso
    (Iso.refl _) (qinvIso ε₁ ε₂ M)
    hQ))

/-- Isomorphic input line bundles have isomorphic twists. -/
theorem twist_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε₁ t)
    (e : Nonempty (M.L ≅ M'.L)) : Nonempty ((twist ε₁ ε₂ M).L ≅ (twist ε₁ ε₂ M').L) :=
  ⟨e.some ⊗ᵢ (Scheme.Modules.pullback _).mapIso
    (tensorInverseIso ((Scheme.Modules.pullback _).mapIso e.some) (qinvIso ε₁ ε₂ M)
      (qinvIso ε₁ ε₂ M'))⟩

/-- Changing rigidification commutes with the actual test-scheme pullback. -/
theorem twist_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty (((twist ε₁ ε₂ M).pullbackAlong ψ).L ≅ (twist ε₁ ε₂ (M.pullbackAlong ψ)).L) := by
  have hX : (Scheme.Modules.pullback (rigSection c t' ε₂)).obj (M.pullbackAlong ψ).L ≅
      (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε₂ ψ)).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  have hQ : (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj
    M.L) ⊗
      (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback ψ.1).mapIso (qinvIso ε₁ ε₂ M) ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
  have hq : (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ qinv ε₁ ε₂ (M.pullbackAlong ψ) :=
    tensorInverseIso hX.symm hQ (qinvIso ε₁ ε₂ (M.pullbackAlong ψ))
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (baseChangePullbackIso ψ _ ≪≫ (Scheme.Modules.pullback _).mapIso hq)⟩

/-- Changing rigidification preserves fibrewise algebraic equivalence to zero. -/
theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) := by
  intro k _ _ s
  let φ := pullback.fst (pullback.snd c t) s
  have hφ : φ ≫ pullback.snd c t = fibreAt c t s ≫ s := pullback.condition
  obtain ⟨e0⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _
    ((qinv_isInvertible ε₁ ε₂ M).pullback s)
  have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj (qinv
    ε₁ ε₂ M)) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (fibreAt c t s)).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have e2 : (Scheme.Modules.pullback φ).obj (twist ε₁ ε₂ M).L ≅ (Scheme.Modules.pullback φ).obj M.L
    :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ e1 ≪≫ ρ_ _
  exact (hM k s).of_iso e2.symm

end Twist

end AlgebraicGeometry.RelPicard.ChangeRigidification
