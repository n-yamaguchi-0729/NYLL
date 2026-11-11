/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLawGrpObj
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Generic fibres and commutativity

Generic-fibre restriction is injective for flat test schemes and separated targets.
This injectivity also descends commutativity of a relative group law.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ProperCommutativity

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem
    _root_.GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f]
    [GeometricallyIntegral f] (G : RelativeGroupLaw K f) : G.IsCommutative :=
  fun {_} t x y => G.mul_comm_of_isProper_of_geometricallyIntegral t x y

end AbelianVarieties.NOSProofs.ProperCommutativity
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GenericFibreRestriction


universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra

namespace NeronModelInfra
open _root_.NeronModelInfra
namespace GenericFibreRestrictInjective
open _root_.NeronModelInfra

theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W T X S : Scheme.{u}}
    {a b : T ⟶ X} (f : X ⟶ S) [IsSeparated f] (t : T ⟶ S) (ha : a ≫ f = t) (hb : b ≫ f = t)
    (p : W ⟶ T) [IsSchemeTheoreticallyDominant p] (h : p ≫ a = p ≫ b) : a = b := by
  let X' : Over S := Over.mk f
  let T' : Over S := Over.mk t
  let a' : T' ⟶ X' := Over.homMk a ha
  let b' : T' ⟶ X' := Over.homMk b hb
  let p' : Over.mk (p ≫ t) ⟶ T' := Over.homMk p rfl
  have hp' : p' ≫ a' = p' ≫ b' := Over.OverMorphism.ext h
  let l : Over.mk (p ≫ t) ⟶ equalizer a' b' := equalizer.lift p' hp'
  have hl : l ≫ equalizer.ι a' b' = p' := equalizer.lift_ι _ _
  have : IsSeparated X'.hom := ‹IsSeparated f›
  have : IsClosedImmersion (equalizer.ι a' b').left := isClosedImmersion_equalizer_ι_left a' b'
  have hcomp : l.left ≫ (equalizer.ι a' b').left = p := by
    rw [← Over.comp_left, hl]; rfl
  have hker : Scheme.Hom.ker (equalizer.ι a' b').left = ⊥ := by
    have h1 := Scheme.Hom.le_ker_comp l.left (equalizer.ι a' b').left
    rw [hcomp] at h1
    exact le_bot_iff.mp (h1.trans (le_of_eq (Scheme.Hom.ker_eq_bot p)))
  have hiso : IsIso (equalizer.ι a' b').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hcond : (equalizer.ι a' b').left ≫ a = (equalizer.ι a' b').left ≫ b := by
    exact congrArg CommaMorphism.left (equalizer.condition a' b')
  have : Epi (equalizer.ι a' b').left := @IsIso.epi_of_iso _ _ _ _ _ hiso
  exact (cancel_epi (equalizer.ι a' b').left).mp hcond

end NeronModelInfra.GenericFibreRestrictInjective

open NeronModelInfra.GenericFibreRestrictInjective in
theorem _root_.NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [Flat t] :
    Function.Injective (genericFibreRestrict R K f t) := by
  intro φ ψ h
  have h1 : pullback.fst t (specGenericFibreInclusion R K) ≫ φ.1 =
      pullback.fst t (specGenericFibreInclusion R K) ≫ ψ.1 := by
    have := congrArg
      (fun χ : SchemeHomOver _ _ => χ.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) h
    rwa [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst] at this
  have : IsDominant (specGenericFibreInclusion R K) := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  have : IsSchemeTheoreticallyDominant (specGenericFibreInclusion R K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant (pullback.fst t (specGenericFibreInclusion R K)) :=
    IsSchemeTheoreticallyDominant.pullbackFst t _
  exact Subtype.ext (ext_of_isSchemeTheoreticallyDominant_of_isSeparated f t φ.2 ψ.2 _ h1)

end AbelianVarieties.NOSProofs.GenericFibreRestriction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GenericFibreCommutativity


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Commutativity

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem mul_comm_over_genericFibre (LB : RelativeGroupLaw R g)
    (h : (LB.genericFibre K).IsCommutative)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
    (y₁ y₂ : SchemeHomOver (s ≫ specGenericFibreInclusion R K) g) :
    LB.mul _ y₁ y₂ = LB.mul _ y₂ y₁ := by
  have e₁ : y₁ = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y₁) :=
    (RelativeGroupLaw.baseChangePointToBase_ofBase _ y₁).symm
  have e₂ : y₂ = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y₂) :=
    (RelativeGroupLaw.baseChangePointToBase_ofBase _ y₂).symm
  rw [e₁, e₂, ← RelativeGroupLaw.baseChangePointToBase_mul,
    ← RelativeGroupLaw.baseChangePointToBase_mul]
  exact congrArg _ (h s _ _)

variable [IsDomain R] [IsFractionRing R K] [IsSeparated g] [Flat g]

theorem mul_fst_snd_eq (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) :
    LB.mul (pullback.fst g g ≫ g)
        ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩ =
      LB.mul (pullback.fst g g ≫ g)
        ⟨pullback.snd g g, pullback.condition.symm⟩ ⟨pullback.fst g g, rfl⟩ := by
  set t₀ : pullback g g ⟶ Spec (CommRingCat.of R) := pullback.fst g g ≫ g
  set p₁ : SchemeHomOver t₀ g := ⟨pullback.fst g g, rfl⟩
  set p₂ : SchemeHomOver t₀ g := ⟨pullback.snd g g, pullback.condition.symm⟩
  set ι := specGenericFibreInclusion R K
  set ψ : pullback t₀ ι ⟶ pullback g g := pullback.fst t₀ ι
  have hψt : ψ ≫ t₀ = pullback.snd t₀ ι ≫ ι := pullback.condition
  have hgen : GoodReductionJacobian.schemeHomOverComp ψ hψt (LB.mul t₀ p₁ p₂) =
      GoodReductionJacobian.schemeHomOverComp ψ hψt (LB.mul t₀ p₂ p₁) := by
    rw [LB.mul_natural t₀ _ ψ hψt, LB.mul_natural t₀ _ ψ hψt]
    exact mul_comm_over_genericFibre K LB h _ _ _
  have hgen1 : ψ ≫ (LB.mul t₀ p₁ p₂).1 = ψ ≫ (LB.mul t₀ p₂ p₁).1 := by
    have := congrArg Subtype.val hgen
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using this
  have hres : genericFibreRestrict R K g t₀ (LB.mul t₀ p₁ p₂) =
      genericFibreRestrict R K g t₀ (LB.mul t₀ p₂ p₁) := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
      exact hgen1
    · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
  have : Flat t₀ := inferInstance
  exact NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K g t₀ hres

theorem main (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) :
    LB.IsCommutative := by
  intro T t x y
  set q : T ⟶ pullback g g := pullback.lift x.1 y.1 (x.2.trans y.2.symm) with hq
  have hqt : q ≫ (pullback.fst g g ≫ g) = t := by
    rw [← Category.assoc, hq, pullback.lift_fst, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp q hqt
      (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = x :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hq, pullback.lift_fst])
  have hy : GoodReductionJacobian.schemeHomOverComp q hqt
      (⟨pullback.snd g g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = y :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hq, pullback.lift_snd])
  have h1 := congrArg (GoodReductionJacobian.schemeHomOverComp q hqt) (mul_fst_snd_eq K LB h)
  rw [LB.mul_natural _ _ q hqt, LB.mul_natural _ _ q hqt, hx, hy] at h1
  exact h1

end Commutativity

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isCommutative_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [IsSeparated g] [Flat g]
    (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) :
    LB.IsCommutative :=
  Commutativity.main K LB h

end AbelianVarieties.NOSProofs.GenericFibreCommutativity
end
