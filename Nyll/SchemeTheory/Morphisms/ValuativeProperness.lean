/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.FunctionFields.Functoriality
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.Transcendence
public import Nyll.ValuedFieldTheory.Valuation.ResidueTranscendence
public import Nyll.SchemeTheory.Morphisms.AffineCompactification
public import Nyll.SchemeTheory.LocalGeometry.Dimension
public import Nyll.SchemeTheory.Morphisms.OpenImmersionCriteria

/-!
# Valuation models and codimension-one boundaries

Proper birational maps preserve normal codimension-one stalks. Valuation rings of
function fields produce proper models with codimension-one centers and detect the
boundary of a nonproper variety. Function-field maps and section algebras use their
existing canonical owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open AlgebraicCurve

universe u

open AbelianVarieties.NOSProofs.VarietyNormalization.AlgebraicGeometry.NormalizationOfVariety
  (chart_finiteType)

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

theorem
    exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {P' P : Scheme.{u}} (p : P ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral P] [IsIntegral P'] (π : P' ⟶ P) [IsProper π]
    (W : P.Opens) (hW : (W : Set P).Nonempty) [IsIso (π ∣_ W)]
    (w : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1)
    (hwn : IsIntegrallyClosed (P.presheaf.stalk w)) :
    ∃ w' : P', π.base w' = w ∧ IsIso (π.stalkMap w') := by
  classical
  have hLN : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have hDom : IsDomain (P.presheaf.stalk w) := inferInstance
  have hFR : IsFractionRing (P.presheaf.stalk w) P.functionField := inferInstance
  have hK1 : Ring.KrullDimLE 1 (P.presheaf.stalk w) :=
    Ring.krullDimLE_iff.mpr (by rw [hw₁]; exact le_rfl)
  have h4 : IsIntegrallyClosed (P.presheaf.stalk w) ∧ ∀ Q : Ideal (P.presheaf.stalk w), Q ≠ ⊥ →
      Q.IsPrime → Q = IsLocalRing.maximalIdeal (P.presheaf.stalk w) :=
    ⟨hwn, fun Q hQ hQ' => IsLocalRing.eq_maximalIdeal
      ((Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hK1) Q hQ hQ')⟩
  have hVal : ValuationRing (P.presheaf.stalk w) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (P.presheaf.stalk w)).out 4 2).mp h4
  obtain ⟨x, hx⟩ := hW
  have hVne : Nonempty (π ⁻¹ᵁ W) := ⟨(inv (π ∣_ W)).base ⟨x, hx⟩⟩
  let η : ↥(π ⁻¹ᵁ W) := genericPoint (π ⁻¹ᵁ W)
  have hη : (π ⁻¹ᵁ W).ι.base η = genericPoint P' := genericPoint_eq_of_isOpenImmersion _
  have hg : (π ⁻¹ᵁ W).ι ≫ π = (π ∣_ W) ≫ W.ι := (morphismRestrict_ι π W).symm
  have hgen : π.base (genericPoint P') = genericPoint P := by
    rw [← hη, ← Scheme.Hom.comp_apply, hg]
    exact genericPoint_eq_of_isOpenImmersion _
  have hiso₁ : IsIso (((π ⁻¹ᵁ W).ι ≫ π).stalkMap η) := by
    rw [hg]; infer_instance
  have hiso₂ : IsIso (π.stalkMap ((π ⁻¹ᵁ W).ι.base η)) := by
    rw [Scheme.Hom.stalkMap_comp] at hiso₁
    have : π.stalkMap ((π ⁻¹ᵁ W).ι.base η) =
        (π.stalkMap ((π ⁻¹ᵁ W).ι.base η) ≫ (π ⁻¹ᵁ W).ι.stalkMap η) ≫
          inv ((π ⁻¹ᵁ W).ι.stalkMap η) := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    exact IsIso.comp_isIso' hiso₁ inferInstance
  have hiso : IsIso (π.stalkMap (genericPoint P')) := by rwa [hη] at hiso₂
  set e' : P'.presheaf.stalk (genericPoint P') ⟶ P.functionField :=
    inv (π.stalkMap (genericPoint P')) ≫ (P.presheaf.stalkCongr (.of_eq hgen)).hom with he'def
  have he' : IsIso e' := by rw [he'def]; infer_instance
  set i₁ : Spec P.functionField ⟶ P' := Spec.map e' ≫ P'.fromSpecStalk (genericPoint P') with hi₁def
  have hcomp : π.stalkMap (genericPoint P') ≫ e' = (P.presheaf.stalkCongr (.of_eq hgen)).hom := by
    rw [he'def, IsIso.hom_inv_id_assoc]
  have hL : i₁ ≫ π = P.fromSpecStalk (genericPoint P) := by
    rw [hi₁def, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, hcomp,
      TopCat.Presheaf.stalkCongr_hom]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (X := P) (x := genericPoint P) (y := π.base (genericPoint P'))
      (Inseparable.of_eq hgen).symm.specializes
  have hRt : Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)) ≫
      P.fromSpecStalk w =
      P.fromSpecStalk (genericPoint P) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes w)
  have hsq : CommSq i₁
      (Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)))
      π (P.fromSpecStalk w) :=
    ⟨hL.trans hRt.symm⟩
  have hUC : UniversallyClosed π := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨hEx, -⟩ := hUC
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ :=
    (hEx { R := (P.presheaf.stalk w : Type u), commRing := inferInstance, domain := hDom,
            valuationRing := hVal, K := (P.functionField : Type u), field := inferInstance,
            algebra := inferInstance, isFractionRing := hFR,
            i₁ := i₁, i₂ := P.fromSpecStalk w, commSq := hsq }).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)) ≫
    l = i₁ at hl₁
  change l ≫ π = P.fromSpecStalk w at hl₂
  let xw : Spec (P.presheaf.stalk w) := IsLocalRing.closedPoint (P.presheaf.stalk w)
  refine ⟨l.base (xw), ?_, ?_⟩
  · have h := Scheme.Hom.comp_apply l π (xw)
    rw [hl₂] at h
    rw [← h]
    exact Scheme.fromSpecStalk_closedPoint
  · have hθ' : ∀ g : Spec (P.presheaf.stalk w) ⟶ P, g = P.fromSpecStalk w →
        IsIso (Scheme.stalkClosedPointTo g) := by
      rintro g rfl
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    have hθ := hθ' (l ≫ π) hl₂
    rw [Scheme.stalkClosedPointTo_comp] at hθ
    set φ := Scheme.stalkClosedPointTo l with hφ
    have hθ₂ : IsIso (π.stalkMap (l.base (xw)) ≫ φ) := hθ
    have hlF : Spec.map φ ≫ P'.fromSpecStalk _ = l := by
      rw [hφ]; exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have hξw : genericPoint P' ⤳ l.base (xw) :=
      genericPoint_specializes _
    have key : φ ≫ CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField) =
        P'.presheaf.stalkSpecializes hξw ≫ e' := by
      apply Spec.map_injective
      rw [← cancel_mono (P'.fromSpecStalk (l.base (xw)))]
      rw [Spec.map_comp_assoc, hlF, hl₁, Spec.map_comp_assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hi₁def]
    have hinj : Function.Injective φ.hom := by
      have h2 : Function.Injective
          (φ ≫ CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)).hom := by
        rw [key, CommRingCat.hom_comp, RingHom.coe_comp]
        exact (asIso e').commRingCatIsoToRingEquiv.injective.comp
          (IsFractionRing.injective (P'.presheaf.stalk _) P'.functionField)
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at h2
      exact h2.of_comp
    have hsurj : Function.Surjective φ.hom := by
      have hb' : Function.Surjective
          (π.stalkMap (l.base (xw)) ≫ φ).hom :=
        (@asIso _ _ _ _ _ hθ₂).commRingCatIsoToRingEquiv.surjective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hb'
      exact hb'.of_comp
    have hφiso : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hinj, hsurj⟩
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (π.stalkMap _) φ hφiso hθ₂

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.ValuativeProperness

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

namespace NormalCompactification

theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    [IsIso (g ∣_ U)] (x : X) (hx : g.base x ∈ U) : IsIso (g.stalkMap x) := by
  have : IsOpenImmersion ((g ⁻¹ᵁ U).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  obtain ⟨x', rfl⟩ : ∃ x' : ↥((g ⁻¹ᵁ U : X.Opens) : Scheme.{u}), (g ⁻¹ᵁ U).ι x' = x :=
    ⟨⟨x, hx⟩, rfl⟩
  have h := Scheme.Hom.stalkMap_comp (g ⁻¹ᵁ U).ι g x'
  have i1 : IsIso (((g ⁻¹ᵁ U).ι ≫ g).stalkMap x') := inferInstance
  have i2 : IsIso ((g ⁻¹ᵁ U).ι.stalkMap x') := inferInstance
  rw [h] at i1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ i2 i1

end NormalCompactification

end SchemeTheory.ValuativeProperness

namespace AlgebraicGeometry

open SchemeTheory.ValuativeProperness.NormalCompactification

theorem
    exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (D : P.Opens)
      (τ : (D : Scheme.{u}) ⟶ X) (V : X.Opens) (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u})),
      IsProper p ∧ IsIntegral P ∧ (∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) ∧
      IsProper τ ∧ τ ≫ f = D.ι ≫ p ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧ ι ≫ τ = V.ι := by
  obtain ⟨X', Pt, π, j, q, hπ, -, hj, hq, hjq, hX', hPt, U, hU, hiso⟩ :=
    exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral f
  have : IsProper π := hπ
  have : IsOpenImmersion j := hj
  have : IsProper q := hq
  have : IsIntegral X' := hX'
  have : IsIntegral Pt := hPt
  have : IsIso (π ∣_ U) := hiso
  obtain ⟨P, ν, hPint, hPn, hνfin, -, -, hνiso⟩ :=
    exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral k q
  have : IsIntegral P := hPint
  have : IsFinite ν := hνfin
  let U₀ : Pt.Opens := j.opensRange
  let D : P.Opens := ν ⁻¹ᵁ U₀
  let τ : (D : Scheme.{u}) ⟶ X := (ν ∣_ U₀) ≫ j.isoOpensRange.inv ≫ π
  let U₁ : Pt.Opens := j ''ᵁ (π ⁻¹ᵁ U)
  have hU₁ : ∀ z ∈ U₁, IsIntegrallyClosed (Pt.presheaf.stalk z) := by
    rintro _ ⟨y, hy, rfl⟩
    have : IsIso (π.stalkMap y) := isIso_stalkMap_of_isIso_morphismRestrict π U y hy
    have : IsIntegrallyClosed (X'.presheaf.stalk y) := by
      have : IsIntegrallyClosed (X.presheaf.stalk (π.base y)) := hX (π.base y)
      exact IsIntegrallyClosed.of_equiv (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv
    exact IsIntegrallyClosed.of_equiv (asIso (j.stalkMap y)).symm.commRingCatIsoToRingEquiv
  have hνU₁ : IsIso (ν ∣_ U₁) := hνiso U₁ hU₁
  have hle : ν ⁻¹ᵁ U₁ ≤ D := by
    intro z hz
    change ν.base z ∈ U₀
    obtain ⟨y, -, hy⟩ := hz
    exact ⟨y, hy⟩
  let ι : (U : Scheme.{u}) ⟶ (D : Scheme.{u}) :=
    inv (π ∣_ U) ≫ (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle
  refine ⟨P, ν ≫ q, D, τ, U, ι, inferInstance, hPint, hPn, inferInstance, ?_, ?_, inferInstance, ?_⟩
  · simp only [τ, Category.assoc]
    rw [← hjq, j.isoOpensRange_inv_comp_assoc, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  · have : (U : Set X).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hU (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_bot.symm))
    obtain ⟨x, hx⟩ := this
    exact ⟨⟨x, hx⟩⟩
  · rw [← cancel_epi (π ∣_ U)]
    have hm : (j.isoImage (π ⁻¹ᵁ U)).hom ≫ inv (ν ∣_ U₁) ≫ P.homOfLE hle ≫ (ν ∣_ U₀) =
        (π ⁻¹ᵁ U).ι ≫ j.isoOpensRange.hom := by
      rw [← cancel_mono U₀.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      rw [Scheme.homOfLE_ι_assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
        Scheme.Hom.isoImage_hom_ι]
      simp only [U₀, Scheme.Hom.isoOpensRange_hom_ι]
    simp only [ι, τ, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc (j.isoImage _).hom, ← Category.assoc ((j.isoImage _).hom ≫ _),
      ← Category.assoc (((j.isoImage _).hom ≫ _) ≫ _)]
    simp only [Category.assoc] at hm ⊢
    rw [reassoc_of% hm, Iso.hom_inv_id_assoc, morphismRestrict_ι]

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.ValuativeProperness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace StalkValuations

variable {k : Type u} [Field k]

/-- The valuation subring given by the image of a valuation stalk in its function field. -/
noncomputable def stalkValuationSubring (V : Scheme.{u}) [IsIntegral V] (z : V)
    [ValuationRing (V.presheaf.stalk z)] :
    ValuationSubring V.functionField where
  toSubring := (algebraMap (V.presheaf.stalk z) V.functionField).range
  mem_or_inv_mem' x := by
    rcases ValuationRing.isInteger_or_isInteger (V.presheaf.stalk z) x with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem valuationRing_of_ringKrullDim_eq_one {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (h1 : ringKrullDim R = 1) (hn : IsIntegrallyClosed R) :
    ValuationRing R := by
  have hnf : ¬ IsField R := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [h1] at this; exact one_ne_zero this
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [h1]; exact le_rfl)
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
    ⟨hn, IsLocalRing.maximalIdeal R, ⟨hm, inferInstance⟩,
      fun P hP => IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)⟩
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 4 2).mp h4

end StalkValuations

namespace Transcendence

variable {k : Type u} [Field k]

theorem c_eq_algebraMap_germ {Y : Scheme.{u}} [IsIntegral Y]
    (fY : Y ⟶ Spec (.of k)) (y : Y) (x : k) :
    baseToFunctionField fY x = algebraMap (Y.presheaf.stalk y) Y.functionField
      ((Y.presheaf.germ ⊤ y trivial).hom
        (fY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))) := by
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
  exact (Y.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := y) trivial
    (fY.appTop ((Scheme.ΓSpecIso (.of k)).inv x))).symm

end Transcendence

namespace Transcendence

variable {k : Type u} [Field k]

/- The chart-tower argument is from the codimension-one boundary source unit attributed below. -/
theorem isScalarTower_chart_ff {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) [Nonempty U] :
    let : Algebra k Γ(X, U) := f.sectionsAlgebra U
    let : Algebra k X.functionField := (baseToFunctionField f).toAlgebra
    IsScalarTower k Γ(X, U) X.functionField := by
  intro algA algK
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) =
    (X.germToFunctionField U).hom.comp
      ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  have hgerm : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.germToFunctionField U =
      X.presheaf.germ ⊤ (genericPoint X) trivial :=
    X.presheaf.germ_res _ _ _
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← RingHom.comp_assoc]
  congr 1
  rw [← hgerm]
  rfl

theorem trdeg_eq_of_isFractionRing (k A K : Type u) [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] :
    Algebra.trdeg k K = Algebra.trdeg k A := by
  have : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  have : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := K)
  rw [trdeg_eq_zero (R := A) (A := K), add_zero] at h
  exact h.symm

theorem exists_nat_trdeg_functionField {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    let : Algebra k X.functionField := (baseToFunctionField f).toAlgebra
    ∃ n : ℕ, Algebra.trdeg k X.functionField = n ∧ topologicalKrullDim X = (n : WithBot ℕ∞) := by
  intro algK
  obtain ⟨_, ⟨U, hU, rfl⟩, hζU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hζU⟩⟩
  let algA : Algebra k Γ(X, U) := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := chart_finiteType f hU
  have : IsScalarTower k Γ(X, U) X.functionField := isScalarTower_chart_ff f U
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k Γ(X, U) :=
    trdeg_eq_of_isFractionRing k Γ(X, U) X.functionField
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := k) (S := Γ(X, U)))
  refine ⟨n, htr.trans hn, ?_⟩
  rw [topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral f hU ⟨_, hζU⟩,
    Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k Γ(X, U), hn, Cardinal.toENat_nat]
  rfl

theorem trdeg_residueField_stalk_eq {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (z : X) (hz : ringKrullDim (X.presheaf.stalk z) = 1)
    (n : ℕ) (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    let : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk z)) :=
      ((IsLocalRing.residue _).comp ((X.presheaf.germ ⊤ z trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))).toAlgebra
    Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z)) = (n - 1 : ℕ) := by
  intro alg
  have hL1 :
      (Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) :
        WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({z} : Set X)) :=
    AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure f z
  have hcd := ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral f z
  rw [hz, hX, ← hL1] at hcd
  have h1 : (1 : WithBot ℕ∞) +
      Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) =
      ((n : ℕ∞) : WithBot ℕ∞) := hcd
  have h2 : (1 : ℕ∞) +
      Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) = n := by
    exact_mod_cast h1
  have h3 : Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) =
      (n - 1 : ℕ) := by
    have hfin :
        Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) ≠ ⊤ := by
      intro ht
      rw [ht, add_top] at h2
      exact ENat.top_ne_natCast n h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm] at h2 ⊢
    have : 1 + m = n := by exact_mod_cast h2
    congr 1
    omega
  exact Cardinal.toENat_eq_natCast.mp h3

end Transcendence

namespace StalkValuations

theorem core {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (α : V ⟶ Y) (hdom : DenseRange α.base)
    (z : V) [ValuationRing (V.presheaf.stalk z)]
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base z)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ =
        Y.fromSpecStalk (genericPoint Y))
      (φ : CommRingCat.of O ⟶ V.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = V.fromSpecStalk z ≫ α ∧
      O = (stalkValuationSubring V z).comap (α.functionFieldMap hdom) := by
  classical
  set y := α.base z with hy
  let K := Y.functionField
  let L := V.functionField
  let R := V.presheaf.stalk z
  let S := Y.presheaf.stalk y
  let ψ : K →+* L := α.functionFieldMap hdom
  let A : ValuationSubring L := stalkValuationSubring V z
  let O : ValuationSubring K := A.comap ψ
  have hSO : ∀ s : S, algebraMap S K s ∈ O := fun s => by
    rw [ValuationSubring.mem_comap]
    rw [show ψ (algebraMap S K s) = algebraMap R L ((α.stalkMap z).hom s) from
      α.functionFieldMap_algebraMap_stalk hdom z s]
    exact ⟨_, rfl⟩
  let σ : S →+* O := (algebraMap S K).codRestrict O.toSubring hSO
  have hinjRL : Function.Injective (algebraMap R L) := IsFractionRing.injective R L
  let eA : R ≃+* A := RingEquiv.ofBijective (algebraMap R L).rangeRestrict
    ⟨fun a b h => hinjRL (congrArg Subtype.val h), (algebraMap R L).rangeRestrict_surjective⟩
  let ρ : O →+* A :=
    ψ.restrict O.toSubring A.toSubring (fun a ha => ValuationSubring.mem_comap.mp ha)
  let φ : O →+* R := eA.symm.toRingHom.comp ρ
  have hφval : ∀ a : O, algebraMap R L (φ a) = ψ (a : K) := fun a => by
    change ((eA (eA.symm (ρ a))) : L) = ψ a
    rw [RingEquiv.apply_symm_apply]; rfl
  have hφσ : ∀ s : S, φ (σ s) = (α.stalkMap z).hom s := fun s =>
    hinjRL (by rw [hφval]; exact α.functionFieldMap_algebraMap_stalk hdom z s)
  have hφloc : IsLocalHom φ := by
    constructor
    intro a ha
    have hAunit : IsUnit (ρ a) := by
      have h := ha.map eA.toRingHom
      change IsUnit (eA (eA.symm (ρ a))) at h
      rwa [eA.apply_symm_apply] at h
    have ha0 : (a : K) ≠ 0 := by
      rintro h0
      apply hAunit.ne_zero
      ext; change ψ a = 0; rw [h0, map_zero]
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hAunit
    have hbv : (b : L) = (ψ a)⁻¹ := by
      have : ψ a * (b : L) = 1 := congrArg Subtype.val hb
      exact (eq_inv_of_mul_eq_one_right this)
    have hinvA : (ψ a)⁻¹ ∈ A := hbv ▸ b.2
    have hinvO : (a : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀]; exact hinvA
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  have hO : O ≠ ⊤ := by
    have hSnf : ¬ IsField S := fun hF => hnd (ringKrullDim_eq_zero_of_isField hF)
    have hmS : IsLocalRing.maximalIdeal S ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hSnf
    obtain ⟨s, hsm, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmS
    have hsu : ¬ IsUnit (σ s) := by
      intro hu
      have h1 : IsUnit (φ (σ s)) := hu.map φ
      rw [hφσ] at h1
      have h2 : IsUnit s := (isUnit_map_iff (α.stalkMap z).hom s).mp h1
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal s).mp hsm)) h2
    have hs0' : ((σ s : O) : K) ≠ 0 := by
      change algebraMap S K s ≠ 0
      exact fun h => hs0 (IsFractionRing.injective S K (by rw [h, map_zero]))
    intro htop
    apply hsu
    have hinv : ((σ s : O) : K)⁻¹ ∈ O := by
      have : ∀ x : K, x ∈ O := fun x => by rw [htop]; trivial
      exact this _
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0')⟩
  let ℓ₀ : Spec (CommRingCat.of O) ⟶ Y := Spec.map (CommRingCat.ofHom σ) ≫ Y.fromSpecStalk y
  have hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ ℓ₀ =
      Y.fromSpecStalk (genericPoint Y) := by
    simp only [ℓ₀, ← Spec.map_comp_assoc]
    have : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap O K) =
        Y.presheaf.stalkSpecializes (genericPoint_specializes y) := by
      ext s; rfl
    rw [this, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫ ℓ₀ = V.fromSpecStalk z ≫ α := by
    simp only [ℓ₀, ← Spec.map_comp_assoc]
    have : CommRingCat.ofHom σ ≫ CommRingCat.ofHom φ = α.stalkMap z := by
      ext s; exact hφσ s
    rw [this, Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact ⟨O, hO, ℓ₀, hℓ₀, CommRingCat.ofHom φ, hφloc, hφ, rfl⟩

end StalkValuations

end SchemeTheory.ValuativeProperness

namespace AlgebraicGeometry

open SchemeTheory.ValuativeProperness.Transcendence
open SchemeTheory.ValuativeProperness.StalkValuations

theorem
    exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ =
        Y.fromSpecStalk (genericPoint Y))
      (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O)
      (_ : ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0)
      (φ : CommRingCat.of O ⟶ X.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α := by
  classical
  let uz : (U : Scheme.{u}) := ⟨z, hzU⟩
  have : Nonempty ↥(U : Scheme.{u}) := ⟨⟨z, hzU⟩⟩
  have : IsIntegral (U : Scheme.{u}) := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  have hiso : IsIso (U.ι.stalkMap uz) := inferInstance
  let e : X.presheaf.stalk z ≅ (U : Scheme.{u}).presheaf.stalk uz :=
    @asIso _ _ _ _ (U.ι.stalkMap uz) hiso
  have : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  have : IsNoetherianRing ((U : Scheme.{u}).presheaf.stalk uz) := inferInstance
  have : ValuationRing ((U : Scheme.{u}).presheaf.stalk uz) := by
    apply valuationRing_of_ringKrullDim_eq_one
    · rw [← hz₁]; exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm
    · have : IsIntegrallyClosed (X.presheaf.stalk z) := hzn
      exact IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv
  have hnd' : ringKrullDim (Y.presheaf.stalk (α.base uz)) ≠ 0 := hnd
  obtain ⟨O, hO, ℓ₀, hℓ₀, φ, hφloc, hφ, hOeq⟩ := core α hdom uz hnd'
  obtain ⟨d, hd, g, hg, hind⟩ : ∃ (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O),
      ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0 := by
    let cK : k →+* Y.functionField := baseToFunctionField fY
    let cL : k →+* (U : Scheme.{u}).functionField := baseToFunctionField (U.ι ≫ fX)
    let algK : Algebra k Y.functionField := cK.toAlgebra
    let algL : Algebra k (U : Scheme.{u}).functionField := cL.toAlgebra
    let algKL : Algebra Y.functionField (U : Scheme.{u}).functionField :=
      α.functionFieldAlgebraOfDenseRange hdom
    have hscalar (x : k) : α.functionFieldMap hdom (cK x) = cL x :=
      (Scheme.Hom.functionFieldMap_baseToFunctionField fY α hdom x).trans
        (congrArg (fun q : (U : Scheme.{u}) ⟶ Spec (.of k) => baseToFunctionField q x) hα)
    have : IsScalarTower k Y.functionField (U : Scheme.{u}).functionField :=
      IsScalarTower.of_algebraMap_eq (fun x => (hscalar x).symm)
    obtain ⟨nY, hnY, hdimY⟩ := exists_nat_trdeg_functionField (k := k) fY
    obtain ⟨nV, hnV, hdimV⟩ := exists_nat_trdeg_functionField (k := k) (U.ι ≫ fX)
    let A : ValuationSubring (U : Scheme.{u}).functionField :=
      stalkValuationSubring (U : Scheme.{u}) uz
    have hkA : ∀ x : k, algebraMap k (U : Scheme.{u}).functionField x ∈ A := fun x => by
      change cL x ∈ A
      rw [show cL x = _ from c_eq_algebraMap_germ (U.ι ≫ fX) uz x]
      exact ⟨_, rfl⟩
    have hz1' : ringKrullDim ((U : Scheme.{u}).presheaf.stalk uz) = 1 := by
      rw [← hz₁]; exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm
    have hA : let : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp
          ((algebraMap k (U : Scheme.{u}).functionField).codRestrict A.toSubring hkA)).toAlgebra
        ((nV - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A) := by
      intro algA'
      let R := (U : Scheme.{u}).presheaf.stalk uz
      have hinjRL : Function.Injective (algebraMap R (U : Scheme.{u}).functionField) :=
        IsFractionRing.injective R _
      let eA : R ≃+* A :=
        RingEquiv.ofBijective (algebraMap R (U : Scheme.{u}).functionField).rangeRestrict
          ⟨fun a b h => hinjRL (congrArg Subtype.val h),
            (algebraMap R (U : Scheme.{u}).functionField).rangeRestrict_surjective⟩
      let gR : k →+* R := (((U : Scheme.{u}).presheaf.germ ⊤ uz trivial).hom.comp
        ((U.ι ≫ fX).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))
      let algR : Algebra k (IsLocalRing.ResidueField R) :=
        ((IsLocalRing.residue R).comp gR).toAlgebra
      have hA2 : Algebra.trdeg k (IsLocalRing.ResidueField R) = (nV - 1 : ℕ) :=
        trdeg_residueField_stalk_eq (k := k) (U.ι ≫ fX) uz hz1' nV hdimV
      let eκ : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField A :=
        IsLocalRing.ResidueField.mapEquiv eA
      have hcomm : ∀ x : k, eκ (algebraMap k (IsLocalRing.ResidueField R) x) =
          algebraMap k (IsLocalRing.ResidueField A) x := by
        intro x
        change IsLocalRing.ResidueField.mapEquiv eA (IsLocalRing.residue R (gR x)) =
          IsLocalRing.residue A
            ((algebraMap k (U : Scheme.{u}).functionField).codRestrict A.toSubring hkA x)
        have h1 : IsLocalRing.ResidueField.mapEquiv eA (IsLocalRing.residue R (gR x)) =
            IsLocalRing.residue A (eA (gR x)) := rfl
        rw [h1]
        congr 1
        apply Subtype.ext
        change algebraMap R (U : Scheme.{u}).functionField (gR x) = cL x
        exact (c_eq_algebraMap_germ (U.ι ≫ fX) uz x).symm
      let eκa : IsLocalRing.ResidueField R ≃ₐ[k] IsLocalRing.ResidueField A :=
        AlgEquiv.ofRingEquiv (f := eκ) hcomm
      rw [← eκa.trdeg_eq, hA2]
    have hTR :=
      ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField A hkA nY nV hnY hnV hA
    have hnY1 : 1 ≤ nY := by
      by_contra hlt
      have h0 : nY = 0 := by omega
      have hcd := ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral fY
        (α.base uz)
      rw [hdimY, h0] at hcd
      have ha : (0 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk (α.base uz)) :=
        ringKrullDim_nonneg_of_nontrivial
      have hb : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(closure ({α.base uz} : Set Y)) := by
        have : Nonempty (TopologicalSpace.IrreducibleCloseds ↥(closure ({α.base uz} : Set Y))) :=
          ⟨⟨closure {⟨_, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
        exact Order.krullDim_nonneg
      apply hnd
      apply le_antisymm _ ha
      calc ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩))
          ≤ ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) +
              topologicalKrullDim ↥(closure ({α.base uz} : Set Y)) :=
            le_add_of_nonneg_right hb
        _ = ((0 : ℕ) : WithBot ℕ∞) := hcd
        _ = 0 := rfl
    subst hOeq
    have hc : ∀ x : k, cK x ∈ A.comap (α.functionFieldMap hdom) := fun x => by
      rw [ValuationSubring.mem_comap]
      rw [hscalar]
      exact hkA x
    obtain ⟨g, hg, hgi⟩ := ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg cK
      (A.comap (α.functionFieldMap hdom)) hc (d := nY - 1) (by exact hTR)
    refine ⟨nY - 1, ?_, g, hg,
      fun Q hQ => ValuationSubring.eq_zero_of_valuation_eval2_lt_one cK _ hc g hg hgi Q hQ⟩
    rw [hdimY]; congr 1; exact_mod_cast Nat.sub_add_cancel hnY1
  refine ⟨O, hO, ℓ₀, hℓ₀, d, hd, g, hg, hind, φ ≫ e.inv, ?_, ?_⟩
  · have : IsLocalHom φ.hom := hφloc
    change IsLocalHom (e.inv.hom.comp φ.hom)
    exact RingHom.isLocalHom_comp _ _
  · rw [Spec.map_comp, Category.assoc, hφ,
      Scheme.Opens.fromSpecStalkOfMem, Category.assoc]
    exact congrArg
      (fun q : (U : Scheme.{u}).presheaf.stalk uz ⟶ X.presheaf.stalk z =>
        Spec.map q ≫ (U : Scheme.{u}).fromSpecStalk uz ≫ α)
      (asIso_inv (U.ι.stalkMap uz))

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.ValuativeProperness

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace Boundary
open AlgebraicGeometry

theorem exists_notMem {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ¬ IsProper f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ X) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : X.Opens) [hV : Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    (hτι : ι ≫ τ = V.ι) :
    ∃ x : P, x ∉ D := by
  by_contra hall
  have hDtop : D = ⊤ := top_unique fun x _ => by
    by_contra hx
    exact hall ⟨x, hx⟩
  have : IsIso D.ι := by
    rw [hDtop]
    exact inferInstanceAs (IsIso (Scheme.topIso P).hom)
  have : IsProper (D.ι ≫ p) := inferInstance
  have : IsProper (τ ≫ f) := hτ ▸ inferInstance
  have : Surjective τ := by
    refine ⟨fun y => ?_⟩
    have hcl : IsClosed (Set.range τ.base) :=
      τ.isClosedMap.isClosed_range
    have hdense : Dense (Set.range τ.base) := by
      have hVsub : (V : Set X) ⊆ Set.range τ.base := by
        intro z hz
        refine ⟨ι.base ⟨z, hz⟩, ?_⟩
        change (ι ≫ τ).base ⟨z, hz⟩ = z
        rw [hτι]
        rfl
      have hVne : (V : Set X).Nonempty := by
        obtain ⟨v⟩ := hV
        exact ⟨v.1, v.2⟩
      have hVdense : Dense (V : Set X) := V.2.dense hVne
      exact hVdense.mono hVsub
    have : Set.range τ.base = Set.univ := by
      rw [← hcl.closure_eq, hdense.closure_eq]
    obtain ⟨z, hz⟩ := (Set.eq_univ_iff_forall.mp this) y
    exact ⟨z, hz⟩
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective τ f
  exact hX ⟨⟩

end Boundary

end SchemeTheory.ValuativeProperness

namespace AlgebraicGeometry

open SchemeTheory.ValuativeProperness.Boundary

open SchemeTheory.ValuativeProperness.Transcendence

theorem
    exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ¬ IsProper f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ X) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : X.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : X.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ (π ⁻¹ᵁ D : Scheme.{u})),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧ ι' ≫ (π ∣_ D) ≫ τ = V'.ι ∧
      ∃ w : P', w ∉ (π ⁻¹ᵁ D : Set P') ∧ ringKrullDim (P'.presheaf.stalk w) = 1 := by
  classical
  obtain ⟨x, hxD⟩ := exists_notMem f hX p D τ hτ V ι hτι
  obtain ⟨Ua, hUa, hxUa, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := P) (x := x) (U := ⊤) trivial
  have hUane : Nonempty Ua := ⟨⟨x, hxUa⟩⟩
  have hηD : genericPoint P ∈ D := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
    have hmem : (ι.base v).1 ∈ (D : Set P) := (ι.base v).2
    exact ((genericPoint_spec P).mem_open_set_iff D.2).mpr ⟨_, Set.mem_univ _, hmem⟩
  have hxη : x ≠ genericPoint P := fun h => hxD (h ▸ hηD)
  set A := Γ(P, Ua) with hA
  let 𝔭 : PrimeSpectrum A := hUa.primeIdealOf ⟨x, hxUa⟩
  have h𝔭 : 𝔭.asIdeal ≠ ⊥ := by
    intro hbot
    apply hxη
    have h1 : hUa.primeIdealOf ⟨x, hxUa⟩ =
        hUa.primeIdealOf ⟨genericPoint P,
          ((genericPoint_spec P).mem_open_set_iff Ua.2).mpr ⟨x, Set.mem_univ _, hxUa⟩⟩ := by
      rw [hUa.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hbot
    have h2 := congrArg hUa.fromSpec h1
    rw [hUa.fromSpec_primeIdealOf, hUa.fromSpec_primeIdealOf] at h2
    exact h2
  let algA : Algebra k A := p.sectionsAlgebra Ua
  have : Algebra.FiniteType k A := chart_finiteType p hUa
  let algK : Algebra k P.functionField := (baseToFunctionField p).toAlgebra
  have : IsScalarTower k A P.functionField := isScalarTower_chart_ff p Ua
  have : IsFractionRing A P.functionField :=
    functionField_isFractionRing_of_isAffineOpen P Ua hUa
  have : 𝔭.asIdeal.IsPrime := 𝔭.2
  obtain ⟨O, d, g, hOtop, hAO, hcen, hd, hgO, hind⟩ :=
    Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType k P.functionField
      𝔭.asIdeal h𝔭
  let φ : A →+* O := (algebraMap A P.functionField).codRestrict O hAO
  have hφ : (algebraMap O P.functionField).comp φ = algebraMap A P.functionField := by
    ext a; rfl
  let ℓ₀ : Spec (CommRingCat.of O) ⟶ P := Spec.map (CommRingCat.ofHom φ) ≫ hUa.fromSpec
  have hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
      P.fromSpecStalk (genericPoint P) := by
    have hη : genericPoint P ∈ Ua :=
      ((genericPoint_spec P).mem_open_set_iff Ua.2).mpr ⟨x, Set.mem_univ _, hxUa⟩
    rw [← hUa.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk]
    change Spec.map _ ≫ Spec.map _ ≫ hUa.fromSpec = _
    rw [← Spec.map_comp_assoc]
    congr 2
  let xO : Spec (.of O) := IsLocalRing.closedPoint O
  have hℓ₀x : ℓ₀.base (xO) = x := by
    change hUa.fromSpec ((Spec.map (CommRingCat.ofHom φ)).base (xO)) = x
    have hpt : (Spec.map (CommRingCat.ofHom φ)).base (xO) = 𝔭 := by
      rw [Spec.map_apply]
      refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
      change φ a ∈ IsLocalRing.maximalIdeal O ↔ a ∈ 𝔭.asIdeal
      rw [ValuationSubring.valuation_lt_one_iff]
      exact hcen a
    rw [hpt]
    exact hUa.fromSpec_primeIdealOf ⟨x, hxUa⟩
  have hd' : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P := by
    rw [hd]
    exact (AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p
      hUa ⟨x, hxUa⟩).symm
  have hind' : ∀ Q : MvPolynomial (Fin d) k,
      O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0 := by
    intro Q hQ
    apply hind Q
    rwa [MvPolynomial.aeval_def]
  obtain ⟨P₁, β, U, s, ℓ, y', hP₁, hβ, hUne, hs, hsβ, hsrange, hℓβ, hℓy', hdim⟩ :=
    AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
      k p O hOtop ℓ₀ hℓ₀ d hd' g hgO hind'
  have : IsIntegral P₁ := hP₁
  have : IsProper β := hβ
  have : IsOpenImmersion s := hs
  change ℓ.base xO = y' at hℓy'
  have hβy' : β.base y' = x := by
    rw [← hℓy']
    exact (congrArg (fun q : Spec (.of O) ⟶ P => q xO) hℓβ).trans hℓ₀x
  obtain ⟨P', ν, hP', hnorm, hfin, hsurj, hdimeq, hiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
      k (β ≫ p)
  have : IsIntegral P' := hP'
  have : IsFinite ν := hfin
  let π : P' ⟶ P := ν ≫ β
  have hπ : IsProper π := inferInstance
  obtain ⟨w, hw⟩ := hsurj y'
  have hwdim : ringKrullDim (P'.presheaf.stalk w) = 1 := by rw [hdimeq w, hw, hdim]
  have hwD : w ∉ (π ⁻¹ᵁ D : Set P') := by
    intro hmem
    apply hxD
    have : π.base w ∈ (D : Set P) := hmem
    rwa [show π.base w = x by
      change (ν ≫ β).base w = x
      rw [Scheme.Hom.comp_apply, hw, hβy']] at this
  let U₁ : P₁.Opens := s.opensRange
  have hU₁norm : ∀ z ∈ U₁, IsIntegrallyClosed (P₁.presheaf.stalk z) := by
    rintro z ⟨u, rfl⟩
    have : IsIntegrallyClosed (P.presheaf.stalk (U.ι u)) := hn _
    have h1 : IsIntegrallyClosed ((U : Scheme.{u}).presheaf.stalk u) :=
      IsIntegrallyClosed.of_equiv (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
    have e : (U : Scheme.{u}).presheaf.stalk u ≅ P₁.presheaf.stalk (s.base u) :=
      (asIso (s.stalkMap u)).symm
    exact IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv
  have hisoU₁ : IsIso (ν ∣_ U₁) := hiso U₁ hU₁norm
  let t : (U : Scheme.{u}) ⟶ P' := s.isoOpensRange.hom ≫ inv (ν ∣_ U₁) ≫ (ν ⁻¹ᵁ U₁).ι
  have ht : IsOpenImmersion t := inferInstance
  have htπ : t ≫ π = U.ι := by
    change (s.isoOpensRange.hom ≫ inv (ν ∣_ U₁) ≫ (ν ⁻¹ᵁ U₁).ι) ≫ ν ≫ β = U.ι
    simp only [Category.assoc]
    rw [← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, hsβ]
  let jP : (V : Scheme.{u}) ⟶ P := ι ≫ D.ι
  have : IsOpenImmersion jP := inferInstance
  let W : (V : Scheme.{u}).Opens := jP ⁻¹ᵁ U
  let V' : X.Opens := V.ι ''ᵁ W
  have hV'ne : Nonempty (V' : Scheme.{u}) := by
    have hr : IsOpen (Set.range jP.base) := jP.isOpenEmbedding.isOpen_range
    have hrne : (Set.range jP.base).Nonempty := by
      obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
      exact ⟨_, v, rfl⟩
    obtain ⟨z, hzU, ⟨v, rfl⟩⟩ := nonempty_preirreducible_inter U.2 hr hUne hrne
    have hvW : v ∈ W := hzU
    exact ⟨⟨V.ι.base v, ⟨v, hvW, rfl⟩⟩⟩
  let e : (V' : Scheme.{u}) ⟶ (W : Scheme.{u}) := (V.ι.isoImage W).inv
  have he : e ≫ W.ι ≫ V.ι = V'.ι := Scheme.Hom.isoImage_inv_ι V.ι W
  let ι'₀ : (V' : Scheme.{u}) ⟶ P' := e ≫ (jP ∣_ U) ≫ t
  have hι'₀ : IsOpenImmersion ι'₀ := inferInstance
  have hι'₀π : ι'₀ ≫ π = e ≫ W.ι ≫ jP := by
    change (e ≫ (jP ∣_ U) ≫ t) ≫ π = e ≫ W.ι ≫ jP
    simp only [Category.assoc]
    rw [htπ, morphismRestrict_ι]
  have hrange : Set.range ι'₀.base ⊆ Set.range (π ⁻¹ᵁ D).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π.base (ι'₀.base y) ∈ D
    rw [← Scheme.Hom.comp_apply, hι'₀π]
    change (D.ι.base (ι.base (W.ι.base (e.base y)))) ∈ D
    exact (ι.base (W.ι.base (e.base y))).2
  let ι' : (V' : Scheme.{u}) ⟶ (π ⁻¹ᵁ D : Scheme.{u}) := IsOpenImmersion.lift (π ⁻¹ᵁ D).ι ι'₀ hrange
  have hι'fac : ι' ≫ (π ⁻¹ᵁ D).ι = ι'₀ := IsOpenImmersion.lift_fac _ _ _
  have hι' : IsOpenImmersion ι' := by
    have : IsOpenImmersion (ι' ≫ (π ⁻¹ᵁ D).ι) := hι'fac ▸ hι'₀
    exact IsOpenImmersion.of_comp ι' (π ⁻¹ᵁ D).ι
  have hsec : ι' ≫ (π ∣_ D) ≫ τ = V'.ι := by
    have h1 : ι' ≫ (π ∣_ D) = e ≫ W.ι ≫ ι := by
      rw [← cancel_mono D.ι]
      simp only [Category.assoc]
      rw [morphismRestrict_ι, ← Category.assoc ι', hι'fac, hι'₀π]
    rw [← Category.assoc, h1]
    simp only [Category.assoc]
    rw [hτι]
    exact he
  exact ⟨P', π, V', ι', hP', hnorm, hπ, hV'ne, hι', hsec, w, hwD, hwdim⟩

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

theorem
    exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (Y' : Scheme.{u}) (fY' : Y' ⟶ Spec (.of k)) (_ : IsIntegral Y') (_ : IsProper fY')
      (β : Y' ⟶ Y) (_ : β ≫ fY = fY') (W : Y.Opens) (_ : Dense (W : Set ↥Y)) (_ : IsIso (β ∣_ W))
      (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U')
      (α' : (U' : Scheme.{u}) ⟶ Y') (_ : α' ≫ β = X.homOfLE hU' ≫ α),
      ringKrullDim (Y'.presheaf.stalk (α'.base ⟨z, hzU'⟩)) = 1 := by
  obtain ⟨O, hO, ℓ₀, hℓ₀, d, hd, g, hgO, hind, φ, hφloc, hφ⟩ :=
    exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
      fX fY U α hα hdom z hzU hz₁ hzn hnd
  have : LocallyOfFiniteType fY := inferInstance
  obtain ⟨Y', β, W, s, ℓ, y', hY'i, hβ, hWne, hs, hsβ, hsr, hℓβ, hℓy', hdim⟩ :=
    exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
      k fY O hO ℓ₀ hℓ₀ d hd
      g hgO hind
  have : IsIntegral Y' := hY'i
  have : IsProper β := hβ
  have : IsOpenImmersion s := hs
  have hβW : IsIso (β ∣_ W) :=
    isIso_morphismRestrict_of_isOpenImmersion_of_range_eq β W s hsβ hsr
  have : LocallyOfFiniteType β := inferInstance
  have : X.IsGermInjectiveAt z := inferInstance
  have : IsLocalHom φ.hom := hφloc
  obtain ⟨U', hU', hzU', α', hα'β, hα'z⟩ :=
    AlgebraicGeometry.exists_opens_comp_eq_base_eq_of_isLocalHom U α z hzU β ℓ₀ ℓ hℓβ φ hφ
  refine ⟨Y', β ≫ fY, hY'i, inferInstance, β, rfl, W, ?_, hβW, U', hU', hzU', α', hα'β, ?_⟩
  · exact W.2.dense hWne
  · rw [hα'z, hℓy']; exact hdim

end AlgebraicGeometry
end
