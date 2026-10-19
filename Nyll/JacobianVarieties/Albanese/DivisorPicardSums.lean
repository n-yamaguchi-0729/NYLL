/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.LineBundleSumInvariance
import Nyll.JacobianVarieties.Albanese.DivisorPicardChart
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.OpenChartPicardZeroPresheaf
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.TwistModulePullbackIsoPullback
import Nyll.SchemeTheory.Modules.Invertible.Rigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoTensorUnitLocalRing
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleInvModule
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ExtCompEq
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!+# Sums on divisor Picard charts

Over a field, equal-degree divisor twists are isomorphic exactly when their
divisor line bundles are isomorphic: rigidification contributes only a trivial
line from the base and the common base-point twist cancels. Over an algebraically
closed field this implies equality of the sum morphisms on reduced families.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne

namespace JacobianVarieties.Albanese

private theorem nonempty_rigidify_iso_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (σ : Spec (CommRingCat.of K) ⟶ X) (q : X ⟶ Spec (CommRingCat.of K))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (Scheme.Modules.rigidify σ q M ≅ M) := by
  obtain ⟨e⟩ := (hM.pullback σ).dual.1.nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨(Iso.refl M ⊗ᵢ ((Scheme.Modules.pullback q).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso q)) ≪≫ ρ_ M⟩

/-- Rigidification over a field loses no line-bundle class. The common
base-point twist of two degree-`r` divisors can then be cancelled. -/
theorem nonempty_lineBundle_iso_of_twistModule_iso
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) {r : ℕ}
    (D₀ D₁ : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K))))
    (e : D₀.twistModule c ε ≅ D₁.twistModule c ε) :
    Nonempty (D₀.lineBundle ≅ D₁.lineBundle) := by
  let F := ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of K)))) ^ r).module
  have hF : Scheme.Modules.IsInvertible F :=
    ((isInvertible_sectionIdeal K c ε (𝟙 _)).pow r).isInvertible_module
  have h₀ := D₀.isInvertible_I.isInvertible_invModule.tensor hF
  have h₁ := D₁.isInvertible_I.isInvertible_invModule.tensor hF
  obtain ⟨e₀⟩ := nonempty_rigidify_iso_over_field (rigSection c (𝟙 _) ε)
    (pullback.snd c (𝟙 _)) (D₀.lineBundle ⊗ F) h₀
  obtain ⟨e₁⟩ := nonempty_rigidify_iso_over_field (rigSection c (𝟙 _) ε)
    (pullback.snd c (𝟙 _)) (D₁.lineBundle ⊗ F) h₁
  let eL : D₀.lineBundle ⊗ F ≅ D₁.lineBundle ⊗ F := e₀.symm ≪≫ e ≪≫ e₁
  obtain ⟨eF⟩ := hF.dual.2
  exact ⟨(ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ eF.symm) ≪≫ (α_ _ _ _).symm ≪≫
    (eL ⊗ᵢ Iso.refl _) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eF) ≪≫ ρ_ _⟩

private theorem lift_pullbackAlong
    {C S Y T T' : Scheme.{u}} {c : C ⟶ S} {r : ℕ}
    {y : Y ⟶ S} {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {g : T ⟶ S} (D : RelEffCartierDiv c r g)
    {g' : T' ⟶ S} (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    hU.lift (D.pullbackAlong φ hφ) = φ ≫ hU.lift D := by
  symm
  apply hU.eq_lift (by rw [Category.assoc, hU.lift_comp, hφ])
  have h : U.pullbackAlong (φ ≫ hU.lift D)
      (by rw [Category.assoc, hU.lift_comp, hφ]) = D.pullbackAlong φ hφ := by
    rw [← U.pullbackAlong_comp (hU.lift D) (hU.lift_comp D) φ hφ,
      hU.pullbackAlong_lift]
  exact congrArg RelEffCartierDiv.I h

/-- On a reduced family over an algebraically closed field, two equal-degree
divisors with isomorphic actual twists have the same sum morphism. -/
theorem lift_comp_eq_of_twistModule_iso
    {K : Type u} [Field K] [IsAlgClosed K] {C B Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)}
    {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (sum : SchemeHomOver y b)
    (t : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t] [IsReduced T]
    (D₀ D₁ : RelEffCartierDiv c r t)
    (e : D₀.twistModule c ε ≅ D₁.twistModule c ε) :
    hU.lift D₀ ≫ sum.1 = hU.lift D₁ ≫ sum.1 := by
  apply ext_of_forall_comp_eq_of_isAlgClosed t b
    (by rw [Category.assoc, sum.2, hU.lift_comp])
    (by rw [Category.assoc, sum.2, hU.lift_comp])
  intro x hx
  let ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) t := ⟨x, hx⟩
  obtain ⟨e₀⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ D₀
  obtain ⟨e₁⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ D₁
  have e' : (D₀.pullbackAlong x hx).twistModule c ε ≅
      (D₁.pullbackAlong x hx).twistModule c ε :=
    e₀ ≪≫ (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso e ≪≫ e₁.symm
  obtain ⟨eL⟩ := nonempty_lineBundle_iso_of_twistModule_iso c ε _ _ e'
  have h := lift_comp_eq_of_lineBundle_iso c hU G sum
    (D₀.pullbackAlong x hx) (D₁.pullbackAlong x hx) eL
  rw [lift_pullbackAlong, lift_pullbackAlong, Category.assoc, Category.assoc] at h
  exact h

end JacobianVarieties.Albanese
