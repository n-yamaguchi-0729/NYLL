/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.Differentials.ComponentData
public import Nyll.AbelianVarieties.NeronModels.Differentials.Order
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.Affine.OpenNeighborhoods
public import Nyll.SchemeTheory.Modules.Differentials.Bases
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.Modules.Differentials.TopFormMaps
public import Nyll.SchemeTheory.Modules.Differentials.Pullback
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.Morphisms.OpenImmersionCriteria
public import Nyll.SchemeTheory.Morphisms.SmoothnessCriteria
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.Affine.PullbackSectionsPushout
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraFormallyEtaleFormallySmooth
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # Component valuations and comparison of top differential forms -/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentStalkMaps


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

namespace GenericPoints

theorem bot_mem_range_specGenericFibreInclusion (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (specGenericFibreInclusion R K).base
      := by
  rw [specGenericFibreInclusion_eq]
  change (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap
    R K))
  rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
  change Disjoint ((nonZeroDivisors R : Submonoid R) : Set R) ((⊥ : Ideal R) : Set R)
  rw [Set.disjoint_iff]
  rintro x ⟨hx, hx0⟩
  exact nonZeroDivisors.ne_zero hx hx0

end GenericPoints

end AbelianVarieties.NOSProofs.ComponentStalkMaps

namespace NeronModelInfra.ComponentReading

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AbelianVarieties.NOSProofs.ComponentStalkMaps

universe u

theorem isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)}
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    let : Algebra R (T.Y.presheaf.stalk T.y) := T.algebra
    let φ : T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩) ⟶ T.Y.presheaf.stalk T.y :=
      u.1.stalkMap ⟨T.y, hyW⟩ ≫ (W.stalkIso ⟨T.y, hyW⟩).hom
    let : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) :=
      φ.hom.toAlgebra
    let : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk
      T.y)) :=
      ((algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))).comp
        φ.hom).toAlgebra
    let : Algebra R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) := stalkAlgebra T'.f (u.1.base
      ⟨T.y, hyW⟩)
    IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) ∧
      Function.Injective φ.hom ∧
      IsScalarTower R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) ∧
      IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing
        (T.Y.presheaf.stalk T.y)) := by
  intro instRO φ instO'O instO'F instRO'
  classical
  have : Smooth T'.f := T'.smooth
  have hDom : IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      T'.f _).1
  have hDomO : IsDomain (T.Y.presheaf.stalk T.y) := T.isDomain
  have hDomW : IsDomain ((W : Scheme.{u}).presheaf.stalk (⟨T.y, hyW⟩ : (W : Scheme.{u}))) :=
    MulEquiv.isDomain (T.Y.presheaf.stalk T.y) (W.stalkIso ⟨T.y,
      hyW⟩).commRingCatIsoToRingEquiv.toMulEquiv
  have hι : IsOpenImmersion (specGenericFibreInclusion R K) :=
    NeronModelInfra.isOpenImmersion_specGenericFibreInclusion R K
  have hfst : IsOpenImmersion (pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R K)) :=
    inferInstance
  let U' : (W : Scheme.{u}).Opens := (pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R
    K)).opensRange
  have : IsOpenImmersion T.e.1 := T.isOpenImmersion
  have : IsOpenImmersion T'.e.1 := T'.isOpenImmersion
  have hr : IsOpenImmersion (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 := by
    have : IsOpenImmersion ((genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫
        pullback.fst T.f (specGenericFibreInclusion R K)) := by
      rw [genericFibreRestrict_coe_comp_fst]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst T.f (specGenericFibreInclusion R K))
  have huK : IsOpenImmersion (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 := by
    have : IsOpenImmersion ((genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1) := by
      rw [hu]; infer_instance
    exact IsOpenImmersion.of_comp _ T'.e.1
  have hU'u : IsOpenImmersion (U'.ι ≫ u.1) := by
    have heq : U'.ι ≫ u.1 =
        (pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R K)).isoOpensRange.inv ≫
          ((genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫
            pullback.fst T'.f (specGenericFibreInclusion R K)) := by
      rw [genericFibreRestrict_coe_comp_fst, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    rw [heq]; infer_instance
  have hinjRO : Function.Injective (algebraMap R (T.Y.presheaf.stalk T.y)) := by
    let : Algebra K (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraK
    have : IsScalarTower R K (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTower
    have h1 : Function.Injective (algebraMap R (FractionRing (T.Y.presheaf.stalk T.y))) := by
      rw [IsScalarTower.algebraMap_eq R K (FractionRing (T.Y.presheaf.stalk T.y))]
      exact (algebraMap K _).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk
      T.y)),
      RingHom.coe_comp] at h1
    exact h1.of_comp
  have hU' : ∃ x : (W : Scheme.{u}), x ∈ U' ∧ x ⤳ (⟨T.y, hyW⟩ : (W : Scheme.{u})) := by
    let p0 : PrimeSpectrum (T.Y.presheaf.stalk T.y) := ⟨⊥, Ideal.isPrime_bot⟩
    let η : T.Y := (T.Y.fromSpecStalk T.y).base p0
    have hηy : η ⤳ T.y := by
      have : η ∈ Set.range (T.Y.fromSpecStalk T.y).base := ⟨p0, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hηW : η ∈ W := hηy.mem_open W.2 hyW
    refine ⟨⟨η, hηW⟩, ?_, (subtype_specializes_iff _ _).2 hηy⟩
    have hrange : (⟨η, hηW⟩ : (W : Scheme.{u})) ∈
        Set.range (pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R K)).base := by
      rw [Scheme.Pullback.range_fst]
      change (W.ι ≫ T.f).base ⟨η, hηW⟩ ∈ Set.range (specGenericFibreInclusion R K).base
      have hfη : (W.ι ≫ T.f).base ⟨η, hηW⟩ = T.f.base η := rfl
      rw [hfη]
      have hη' : T.f.base η = (T.Y.fromSpecStalk T.y ≫ T.f).base p0 := rfl
      rw [hη', T.halg]
      have hcomap : (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk T.y)))).base
        p0 =
          ⟨⊥, Ideal.isPrime_bot⟩ := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap R (T.Y.presheaf.stalk T.y)) ⊥ = ⊥
        rw [Ideal.comap_bot_of_injective _ hinjRO]
      rw [hcomap]
      exact GenericPoints.bot_mem_range_specGenericFibreInclusion R K
    exact hrange
  have hfracW :=
    AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
    u.1 (⟨T.y, hyW⟩ : (W : Scheme.{u})) U' hU'
  have hfrac : IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing
    (T.Y.presheaf.stalk T.y)) := by
    let instW : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩))
        (FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩)) :=
      ((algebraMap ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩)
        (FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩))).comp (u.1.stalkMap ⟨T.y,
          hyW⟩).hom).toAlgebra
    have hW : IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩))
        (FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩)) := hfracW
    let θ : ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩) ≃+* (T.Y.presheaf.stalk T.y) :=
      (W.stalkIso ⟨T.y, hyW⟩).commRingCatIsoToRingEquiv
    let Θ : FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩) ≃+* FractionRing
      (T.Y.presheaf.stalk T.y) :=
      IsFractionRing.ringEquivOfRingEquiv θ
    let e : FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩) ≃ₐ[T'.Y.presheaf.stalk
      (u.1.base ⟨T.y, hyW⟩)]
        FractionRing (T.Y.presheaf.stalk T.y) :=
      AlgEquiv.ofRingEquiv (f := Θ) (fun x => by
        change Θ (algebraMap _ (FractionRing ((W : Scheme.{u}).presheaf.stalk ⟨T.y, hyW⟩))
          ((u.1.stalkMap ⟨T.y, hyW⟩).hom x)) =
          algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) (φ.hom x)
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
        rfl)
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors _) e
  refine ⟨hDom, ?_, ?_, hfrac⟩
  · have h := IsFractionRing.injective (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing
      (T.Y.presheaf.stalk T.y))
    intro a b hab
    apply h
    change algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) (φ.hom a) =
      algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) (φ.hom b)
    exact congrArg _ hab
  · have hspec : Spec.map (CommRingCat.ofHom (φ.hom.comp (stalkAlgebraMap T'.f (u.1.base ⟨T.y,
      hyW⟩)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk T.y))) := by
      rw [← T.halg]
      have h1 : CommRingCat.ofHom (φ.hom.comp (stalkAlgebraMap T'.f (u.1.base ⟨T.y, hyW⟩))) =
          CommRingCat.ofHom (stalkAlgebraMap T'.f (u.1.base ⟨T.y, hyW⟩)) ≫ φ := rfl
      rw [h1, Spec.map_comp]
      have h2 : Spec.map (CommRingCat.ofHom (stalkAlgebraMap T'.f (u.1.base ⟨T.y, hyW⟩))) =
          T'.Y.fromSpecStalk (u.1.base ⟨T.y, hyW⟩) ≫ T'.f :=
        (NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T'.f (u.1.base
          ⟨T.y, hyW⟩)).symm
      rw [h2, Spec.map_comp, Category.assoc]
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc u.1
        (x := (⟨T.y, hyW⟩ : ↥(W : Scheme.{u}))) T'.f]
      rw [u.2]
      let yw : (W : Scheme.{u}) := ⟨T.y, hyW⟩
      let sw := W.stalkIso ⟨T.y, hyW⟩
      have hstalk : W.ι.stalkMap yw = sw.inv :=
        (W.stalkIso_inv ⟨T.y, hyW⟩).symm
      have hcancel : Spec.map sw.hom ≫ Spec.map (W.ι.stalkMap yw) = 𝟙 _ := calc
        _ = Spec.map sw.hom ≫ Spec.map sw.inv :=
          congrArg (fun m => Spec.map sw.hom ≫ Spec.map m) hstalk
        _ = Spec.map (sw.inv ≫ sw.hom) := (Spec.map_comp _ _).symm
        _ = 𝟙 _ := by rw [Iso.inv_hom_id, Spec.map_id]
      calc
        _ = Spec.map sw.hom ≫
            (Spec.map (W.ι.stalkMap yw) ≫ T.Y.fromSpecStalk T.y ≫ T.f) :=
          congrArg (Spec.map sw.hom ≫ ·)
            (Scheme.SpecMap_stalkMap_fromSpecStalk_assoc W.ι (x := yw) T.f).symm
        _ = (Spec.map sw.hom ≫ Spec.map (W.ι.stalkMap yw)) ≫
            T.Y.fromSpecStalk T.y ≫ T.f := (Category.assoc _ _ _).symm
        _ = _ := (congrArg (· ≫ T.Y.fromSpecStalk T.y ≫ T.f) hcancel).trans
          (Category.id_comp (T.Y.fromSpecStalk T.y ≫ T.f))
    have heq : φ.hom.comp (stalkAlgebraMap T'.f (u.1.base ⟨T.y, hyW⟩)) = algebraMap R
      (T.Y.presheaf.stalk T.y) := by
      have := Spec.map_injective hspec
      exact congrArg CommRingCat.Hom.hom this
    exact IsScalarTower.of_algebraMap_eq fun r => ((congrArg (fun g => g r) heq).symm :)

end NeronModelInfra.ComponentReading

namespace AbelianVarieties.NOSProofs.ComponentStalkMaps

end AbelianVarieties.NOSProofs.ComponentStalkMaps
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentSpecializations


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

end AbelianVarieties.NOSProofs.ComponentSpecializations

namespace NeronModelInfra.MinimalComponentData

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AbelianVarieties.NOSProofs.ComponentSpecializations

universe u

theorem exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (_ : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (ξ : ↥X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : ↥X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ)
    [Algebra R (X.presheaf.stalk ξ)]
    (halgX : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk
      ξ))))
    (F : Type u) [Field F] [Algebra (X.presheaf.stalk ξ) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (X.presheaf.stalk ξ) F] [IsScalarTower R K F]
    (hinj : Function.Injective (algebraMap (X.presheaf.stalk ξ) F)) :
    ∃ (c : D.ι) (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ξ))
      (_ : (j c).1.base ⟨(D.C c).y, hyV c⟩ = ξ)
      (_ : Function.Bijective φ) (_ : IsLocalHom φ)
      (_ : let : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
        φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) =
          algebraMap R (X.presheaf.stalk ξ))
      (_ : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : let : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F := ((algebraMap
        (X.presheaf.stalk ξ) F).comp φ).toAlgebra
           IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
             c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : let : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK;
        IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F),
      let : Algebra K Γ(XK, (D.C c).U) := gK.sectionsAlgebra (D.C c).U
      let : Algebra Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C
        c).algebraU
      let : Algebra Γ(XK, (D.C c).U) F :=
        ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap
          Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
      Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) F)) ≫ (D.C c).hU.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ξ, halgX⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap
              R (X.presheaf.stalk ξ)))) f))
          e).1 := by
  classical
  obtain ⟨c, v, hv⟩ := hcover ξ
  have h2 : (j c).1 ≫ f = (V c).ι ≫ (D.C c).f := (j c).2
  have hjf : ∀ w : ↥(V c : Scheme.{u}),
      f.base ((j c).1.base w) = (D.C c).f.base ((V c).ι.base w) := by
    intro w
    have := congrArg (fun φ => φ.base w) h2
    exact this
  have hvspec : (D.C c).f.base ((V c).ι.base v) = IsLocalRing.closedPoint R := by
    exact (hjf v).symm.trans ((congrArg f hv).trans hξ)
  have hgen : (D.C c).y ⤳ (V c).ι.base v := D.hgen c _ hvspec
  set y0 : ↥(V c : Scheme.{u}) := ⟨(D.C c).y, hyV c⟩ with hy0
  have hgenV : y0 ⤳ v := by
    exact (V c).ι.isOpenEmbedding.isInducing.specializes_iff.mp hgen
  have hjy : (j c).1.base y0 ⤳ ξ := by
    rw [← hv]; exact hgenV.map (j c).1.base.hom.continuous
  have hjy0 : f.base ((j c).1.base y0) = IsLocalRing.closedPoint R := by
    rw [hjf]; exact (D.C c).hy
  have hξeq : (j c).1.base y0 = ξ := hξmax _ hjy hjy0
  subst hξeq
  have hιopen : IsOpenImmersion (V c).ι := inferInstance
  have hιI : IsIso ((V c).ι.stalkMap y0) := (IsOpenImmersion.iff_isIso_stalkMap.mp hιopen).2 y0
  have hjI : IsIso ((j c).1.stalkMap y0) := (IsOpenImmersion.iff_isIso_stalkMap.mp (hjopen c)).2 y0
  let eφm := ((V c).ι.stalkMap y0) ≫ inv ((j c).1.stalkMap y0)
  have : IsIso eφm := IsIso.comp_isIso' hιI inferInstance
  let φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ((j c).1.base y0)) := eφm.hom
  have heφ : CommRingCat.ofHom φ = ((V c).ι.stalkMap y0) ≫ inv ((j c).1.stalkMap y0) :=
    CommRingCat.ofHom_hom _
  have hφbij : Function.Bijective φ := (asIso eφm).commRingCatIsoToRingEquiv.bijective
  have hφloc : IsLocalHom φ := IsLocalHom.of_surjective φ hφbij.2
  have hA : Spec.map ((j c).1.stalkMap y0) ≫ X.fromSpecStalk ((j c).1.base y0) = (V c :
    Scheme.{u}).fromSpecStalk y0 ≫ (j c).1 :=
    Scheme.SpecMap_stalkMap_fromSpecStalk _
  have hB : Spec.map ((V c).ι.stalkMap y0) ≫ (D.C c).Y.fromSpecStalk (D.C c).y = (V c :
    Scheme.{u}).fromSpecStalk y0 ≫ (V c).ι :=
    Scheme.SpecMap_stalkMap_fromSpecStalk _
  have hSpecφ : Spec.map (CommRingCat.ofHom φ) ≫ (D.C c).Y.fromSpecStalk (D.C c).y ≫ (D.C c).f =
      X.fromSpecStalk ((j c).1.base y0) ≫ f := by
    have hA' : X.fromSpecStalk ((j c).1.base y0) = Spec.map (inv ((j c).1.stalkMap y0)) ≫ (V c :
      Scheme.{u}).fromSpecStalk y0 ≫ (j c).1 := by
      rw [← hA, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    change Spec.map (((V c).ι.stalkMap y0) ≫ inv ((j c).1.stalkMap y0)) ≫ (D.C
      c).Y.fromSpecStalk (D.C c).y ≫ (D.C c).f =
      X.fromSpecStalk ((j c).1.base y0) ≫ f
    rw [hA', Category.assoc, Category.assoc, h2, Spec.map_comp, Category.assoc]
    have hB' := congrArg (· ≫ (D.C c).f) hB
    exact congrArg (Spec.map (inv ((j c).1.stalkMap y0)) ≫ ·)
      ((Category.assoc _ _ _).symm.trans (hB'.trans (Category.assoc _ _ _)))
  have hφR : (let : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra;
    φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) =
      algebraMap R (X.presheaf.stalk ((j c).1.base y0))) := by
    let : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
    have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C
      c).y)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((j c).1.base y0)))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← halgX, ← (D.C c).halg, ← hSpecφ]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  let algRY : Algebra R ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).algebra
  let algKF : Algebra K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C c).algebraK
  have : IsScalarTower R K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C
    c).isScalarTower
  have : IsDomain ((D.C c).Y.presheaf.stalk (D.C c).y) := (D.C c).isDomain
  let algYF : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F := ((algebraMap (X.presheaf.stalk
    ((j c).1.base y0)) F).comp φ).toAlgebra
  have hinjY : Function.Injective (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) F) :=
    hinj.comp hφbij.1
  let ψ : (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) →+* F := IsFractionRing.lift hinjY
  let algF : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F := ψ.toAlgebra
  have tower1 : IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
    c).Y.presheaf.stalk (D.C c).y)) F :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinjY x).symm
  have hY : algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) F = (algebraMap (X.presheaf.stalk
    ((j c).1.base y0)) F).comp φ := RingHom.algebraMap_toAlgebra _
  have hψalg : algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F = ψ :=
    RingHom.algebraMap_toAlgebra ψ
  have hψY0 : ψ.comp (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
    c).Y.presheaf.stalk (D.C c).y))) = algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) F := by
    rw [← hψalg]
    exact (IsScalarTower.algebraMap_eq ((D.C c).Y.presheaf.stalk (D.C c).y)
      (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).symm
  have hψY : ψ.comp (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C
    c).Y.presheaf.stalk (D.C c).y))) = (algebraMap (X.presheaf.stalk ((j c).1.base y0)) F).comp
    φ := hψY0.trans hY
  have hψK : ψ.comp (algebraMap K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y))) =
    algebraMap K F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R K (FractionRing ((D.C
      c).Y.presheaf.stalk (D.C c).y)), IsScalarTower.algebraMap_eq R ((D.C c).Y.presheaf.stalk
      (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)),
      ← RingHom.comp_assoc, hψY, RingHom.comp_assoc, hφR, ← IsScalarTower.algebraMap_eq R
        (X.presheaf.stalk ((j c).1.base y0)) F,
      ← IsScalarTower.algebraMap_eq R K F]
  have towerK : IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F :=
    IsScalarTower.of_algebraMap_eq fun k => (RingHom.congr_fun hψK k).symm
  refine ⟨c, φ, rfl, hφbij, hφloc, hφR, algF, tower1, towerK, ?_⟩
  let : Algebra K Γ(XK, (D.C c).U) := gK.sectionsAlgebra (D.C c).U
  let : Algebra Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) := (D.C
    c).algebraU
  let g0 : (X.presheaf.stalk ((j c).1.base y0)) →+* F := algebraMap (X.presheaf.stalk ((j
    c).1.base y0)) F
  let a : Spec (CommRingCat.of F) ⟶ (V c : Scheme.{u}) :=
    Spec.map (CommRingCat.ofHom g0) ≫ Spec.map (inv ((j c).1.stalkMap y0)) ≫ (V c :
      Scheme.{u}).fromSpecStalk y0
  have hA' : X.fromSpecStalk ((j c).1.base y0) = Spec.map (inv ((j c).1.stalkMap y0)) ≫ (V c :
    Scheme.{u}).fromSpecStalk y0 ≫ (j c).1 := by
    rw [← hA, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have haj : a ≫ (j c).1 = Spec.map (CommRingCat.ofHom g0) ≫ X.fromSpecStalk ((j c).1.base y0)
    := by
    simp only [a, Category.assoc, hA']
  have haι : a ≫ (V c).ι = Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing
        ((D.C c).Y.presheaf.stalk (D.C c).y)))) ≫ (D.C c).Y.fromSpecStalk (D.C c).y := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψY, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
    change _ = Spec.map (CommRingCat.ofHom g0) ≫ Spec.map (((V c).ι.stalkMap y0) ≫ inv ((j
      c).1.stalkMap y0)) ≫ (D.C c).Y.fromSpecStalk (D.C c).y
    rw [Spec.map_comp]
    simp only [Category.assoc]
    have hB' := congrArg
      (fun k => Spec.map (CommRingCat.ofHom g0) ≫
        Spec.map (inv ((j c).1.stalkMap y0)) ≫ k) hB.symm
    calc
      a ≫ (V c).ι = Spec.map (CommRingCat.ofHom g0) ≫
          Spec.map (inv ((j c).1.stalkMap y0)) ≫
            (V c : Scheme.{u}).fromSpecStalk y0 ≫ (V c).ι :=
        (Category.assoc _ _ _).trans
          (congrArg (Spec.map (CommRingCat.ofHom g0) ≫ ·) (Category.assoc _ _ _))
      _ = Spec.map (CommRingCat.ofHom g0) ≫ Spec.map (inv ((j c).1.stalkMap y0)) ≫
          Spec.map ((V c).ι.stalkMap y0) ≫ (D.C c).Y.fromSpecStalk (D.C c).y := hB'
      _ = _ := congrArg (Spec.map (CommRingCat.ofHom g0) ≫ ·) (Category.assoc _ _ _).symm
  have hRF : Spec.map (CommRingCat.ofHom g0) ≫ Spec.map (CommRingCat.ofHom (algebraMap R
    (X.presheaf.stalk ((j c).1.base y0)))) =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ specGenericFibreInclusion R K := by
    rw [specGenericFibreInclusion_eq, ← Spec.map_comp, ← Spec.map_comp, ←
      CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R (X.presheaf.stalk ((j c).1.base y0)) F, ←
        IsScalarTower.algebraMap_eq R K F]
  let pV : Spec (CommRingCat.of F) ⟶ pullback ((V c).ι ≫ (D.C c).f) (specGenericFibreInclusion R
    K) :=
    pullback.lift a (Spec.map (CommRingCat.ofHom (algebraMap K F))) (by
      have hw1 : a ≫ (V c).ι ≫ (D.C c).f = a ≫ (j c).1 ≫ f := by rw [h2]
      rw [hw1, ← Category.assoc a, haj, Category.assoc, halgX, hRF])
  have h5a : pV ≫ (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫
        (pointGenericFibre (K := K) (K' := (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))
          (⟨(D.C c).Y.fromSpecStalk (D.C c).y, (D.C c).halg⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R ((D.C c).Y.presheaf.stalk
              (D.C c).y)))) (D.C c).f)).1 := by
    apply pullback.hom_ext
    · have l1 : (pV ≫ (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι,
      rfl⟩).1) ≫
          pullback.fst (D.C c).f (specGenericFibreInclusion R K) = a ≫ (V c).ι := by
        rw [Category.assoc, genericFibreRestrict_coe_comp_fst, pullback.lift_fst_assoc]
      rw [l1]
      conv_rhs => rw [Category.assoc, pointGenericFibre_coe_comp_fst]
      exact haι
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd, Category.assoc,
        pointGenericFibre_coe_comp_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψK]
  have h5b : pV ≫ (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 =
      (pointGenericFibre (K := K) (K' := F)
          (⟨X.fromSpecStalk ((j c).1.base y0), halgX⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((j
              c).1.base y0))))) f)).1 := by
    apply pullback.hom_ext
    · have l2 : (pV ≫ (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1) ≫
          pullback.fst f (specGenericFibreInclusion R K) = a ≫ (j c).1 := by
        rw [Category.assoc, genericFibreRestrict_coe_comp_fst, pullback.lift_fst_assoc]
      rw [l2, pointGenericFibre_coe_comp_fst]
      exact haj
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd,
      pointGenericFibre_coe_comp_snd]
  rw [NeronModelInfra.schemeHomOverComp_coe, ← h5b, Category.assoc, hjchart, ← Category.assoc,
    h5a, Category.assoc]
  change Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C
    c).Y.presheaf.stalk (D.C c).y))))) ≫ (D.C c).hU.fromSpec = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, (D.C c).hx,
    NeronModelInfra.schemeHomOverComp_coe]

end NeronModelInfra.MinimalComponentData

namespace AbelianVarieties.NOSProofs.ComponentSpecializations

end AbelianVarieties.NOSProofs.ComponentSpecializations
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentOrders


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

namespace SpecializationMaps

theorem comp_algebraMap_eq_of_specializes {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) {y y₁ : Y} (h : y ⤳ y₁)
    [Algebra R (Y.presheaf.stalk y₁)] [Algebra R (Y.presheaf.stalk y)]
    (halg₁ : Y.fromSpecStalk y₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R
      (Y.presheaf.stalk y₁))))
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
      y)))) :
    (Y.presheaf.stalkSpecializes h).hom.comp (algebraMap R (Y.presheaf.stalk y₁)) =
      algebraMap R (Y.presheaf.stalk y) := by
  have key : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y₁)) ≫
    Y.presheaf.stalkSpecializes h =
      CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← halg, ← halg₁, ← Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have := congrArg CommRingCat.Hom.hom key
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this

end SpecializationMaps

theorem _root_.NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (_hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (_hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R
      (T.Y.presheaf.stalk y₁))))
    (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
    (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ)
    (h : ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
        [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
        (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
        (_hKU : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
        (_hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
          (schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
                SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk
                  y₁)))) T.f))
            T.e).1)
        (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
        (_hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE
          le_top).op ω),
        let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
        TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
          (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
              algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ m) •
            TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b')) :
    m = T.n := by
  classical
  have : Smooth T.f := T.smooth
  let algRO : Algebra R (T.Y.presheaf.stalk T.y) := T.algebra
  let algKF : Algebra K (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraK
  have towRKF : IsScalarTower R K (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTower
  let algO₁O : Algebra (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) :=
    (T.Y.presheaf.stalkSpecializes hgen).hom.toAlgebra
  have hcomp := SpecializationMaps.comp_algebraMap_eq_of_specializes T.f hgen halg₁ T.halg
  have towRO₁O : IsScalarTower R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have towO₁OF : IsScalarTower (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
      (FractionRing (T.Y.presheaf.stalk T.y)) := inferInstance
  have towRO₁F : IsScalarTower R (T.Y.presheaf.stalk y₁) (FractionRing (T.Y.presheaf.stalk T.y))
    := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
        (FractionRing (T.Y.presheaf.stalk T.y)),
      IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk T.y) (FractionRing
        (T.Y.presheaf.stalk T.y)),
      ← IsScalarTower.algebraMap_apply R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)]
  have hdom₁ : IsDomain (T.Y.presheaf.stalk y₁) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      T.f y₁).1
  have hlocO := AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes (X := T.Y)
    hgen
  let P : Ideal (T.Y.presheaf.stalk y₁) :=
    Ideal.comap (T.Y.presheaf.stalkSpecializes hgen).hom (IsLocalRing.maximalIdeal
      (T.Y.presheaf.stalk T.y))
  have hfrac₁ : IsFractionRing (T.Y.presheaf.stalk y₁) (FractionRing (T.Y.presheaf.stalk T.y))
    := by
    have h1 := IsLocalization.localization_localization_isLocalization_of_has_all_units
      (R := T.Y.presheaf.stalk y₁) P.primeCompl (S := T.Y.presheaf.stalk T.y)
      (nonZeroDivisors (T.Y.presheaf.stalk T.y)) (FractionRing (T.Y.presheaf.stalk T.y))
      (fun x hx => hx.mem_nonZeroDivisors)
    have hinj : Function.Injective (algebraMap (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) :=
      IsLocalization.injective (T.Y.presheaf.stalk T.y) (M := P.primeCompl)
        (le_nonZeroDivisors_of_noZeroDivisors fun h0 => h0 P.zero_mem)
    have heq : (nonZeroDivisors (T.Y.presheaf.stalk T.y)).comap
        (algebraMap (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) = nonZeroDivisors
          (T.Y.presheaf.stalk y₁) :=
      le_antisymm (comap_nonZeroDivisors_le_of_injective hinj)
        (IsLocalization.nonZeroDivisors_le_comap (M := P.primeCompl) (S := T.Y.presheaf.stalk T.y))
    change IsLocalization (nonZeroDivisors (T.Y.presheaf.stalk y₁)) (FractionRing
      (T.Y.presheaf.stalk T.y))
    rw [← heq]; exact h1
  have hpt : (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk
    T.y))
        (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
            T.f)).1 =
      (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk T.y))
        (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk T.y))))
            T.f)).1 := by
    apply pullback.hom_ext
    · rw [NeronModelInfra.pointGenericFibre_coe_comp_fst,
      NeronModelInfra.pointGenericFibre_coe_comp_fst]
      change Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) (FractionRing
        (T.Y.presheaf.stalk T.y)))) ≫
          T.Y.fromSpecStalk y₁ =
        Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk T.y) (FractionRing
          (T.Y.presheaf.stalk T.y)))) ≫
          T.Y.fromSpecStalk T.y
      rw [IsScalarTower.algebraMap_eq (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)
          (FractionRing (T.Y.presheaf.stalk T.y)), CommRingCat.ofHom_comp, Spec.map_comp,
            Category.assoc]
      congr 1
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen
    · rw [NeronModelInfra.pointGenericFibre_coe_comp_snd,
      NeronModelInfra.pointGenericFibre_coe_comp_snd]
  let algUF : Algebra Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraU
  let algKU : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U
  have towKUF : IsScalarTower K Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) :=
    T.isScalarTowerU
  have hx₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, T.U) (FractionRing
    (T.Y.presheaf.stalk T.y)))) ≫
      T.hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (T.Y.presheaf.stalk T.y))
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
              T.f))
        T.e).1 := by
    rw [T.hx]
    change (NeronModelInfra.pointGenericFibre _).1 ≫ T.e.1 = (NeronModelInfra.pointGenericFibre
      _).1 ≫ T.e.1
    rw [hpt]
  have hσ := h (FractionRing (T.Y.presheaf.stalk T.y)) T.U T.hU T.isScalarTowerU hx₁ T.ωU T.hωU
  obtain ⟨_, _, hlh, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    T.f T.y T.hy T.hmax T.halg
  obtain ⟨hle, hiff⟩ :=
    (open NeronModelInfra.TopFormOrder in
      le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R K (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))
      ϖ hϖ hidx.map_maximalIdeal d b' T.b m w _ hσ)
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁)
    (T.Y.presheaf.stalk T.y)) := by
    have : IsLocalizedModule P.primeCompl
        (KaehlerDifferential.map R R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y)) :=
      KaehlerDifferential.isLocalizedModule_map R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk
        T.y) P.primeCompl
    have hbc := IsLocalizedModule.isBaseChange P.primeCompl (T.Y.presheaf.stalk T.y)
      (KaehlerDifferential.map R R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk T.y))
    have heqv : ∀ x, KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁)
      (T.Y.presheaf.stalk T.y) x =
        hbc.equiv x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul s y => rw [KaehlerDifferential.mapBaseChange_tmul, IsBaseChange.equiv_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have : ⇑(KaehlerDifferential.mapBaseChange R (T.Y.presheaf.stalk y₁) (T.Y.presheaf.stalk
      T.y)) = ⇑hbc.equiv :=
      funext heqv
    rw [this]; exact hbc.equiv.bijective
  have hord := hiff.mpr hbij
  obtain ⟨hρ0, -⟩ :=
    NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
    R K (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) d T.b
  obtain ⟨-, hordsmul⟩ :=
    NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
    R K (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) d T.b
  have hTa := hordsmul T.a T.ha0 hρ0
  rw [← T.ha] at hTa
  rw [hTa] at hord
  change m = TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk
    T.y)) T.a
  exact hord.symm

end AbelianVarieties.NOSProofs.ComponentOrders
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentConstruction


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

noncomputable section

namespace ChartConstruction

theorem smoothOfRelativeDimension_genericFibre_of_chart
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1] :
    SmoothOfRelativeDimension d (pullback.snd f (specGenericFibreInclusion R K)) := by
  rw [← e.2]
  have : SmoothOfRelativeDimension (0 + d) (e.1 ≫ gK) := inferInstance
  simpa only [zero_add] using this

theorem injective_algebraMap_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O] [IsLocalHom
      (algebraMap R O)]
    (h : IsIndexOneExtension R O) : Function.Injective (algebraMap R O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hprime : (RingHom.ker (algebraMap R O)).IsPrime := RingHom.ker_isPrime _
  have hmax : RingHom.ker (algebraMap R O) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (hprime.isMaximal hne)
  have hmap : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = ⊥ := by
    rw [← hmax, Ideal.map_eq_bot_iff_le_ker]
  apply IsDiscreteValuationRing.not_a_field O
  rw [← h.map_maximalIdeal, hmap]

theorem exists_omegaU {K : Type u} [Field K] {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of
  K)) (d : ℕ)
    (ω : Γ(gK.topDifferentials d, ⊤)) (U : XK.Opens) (hU : IsAffineOpen U) :
    ∃ ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)),
      gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω :=
  (Scheme.Hom.topToSections_bijective_of_isAffineOpen gK d hU).2 _

section A

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
  (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
  (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y)
  [algR : Algebra R (Y.presheaf.stalk y)]
  (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))

include f y hy hmax algR halg

omit [LocallyOfFiniteType f] in
theorem stalk_facts : ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing
  (Y.presheaf.stalk y)),
    Function.Injective (algebraMap R (Y.presheaf.stalk y)) := by
  obtain ⟨hdom, hdvr, hloc, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes f y hy hmax halg
  exact ⟨hdom, hdvr, injective_algebraMap_of_isIndexOneExtension (Y.presheaf.stalk y) hidx⟩

omit [LocallyOfFiniteType f] in
theorem injective_toFrac : Function.Injective (algebraMap R (FractionRing (Y.presheaf.stalk y)))
  := by
  obtain ⟨hdom, hdvr, hinj⟩ := stalk_facts f y hy hmax halg
  rw [IsScalarTower.algebraMap_eq R (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))]
  exact (IsFractionRing.injective (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))).comp
    hinj

variable [hdomI : IsDomain (Y.presheaf.stalk y)]

include K hdomI

/-- The fraction-field algebra induced by the generic component point. -/
@[reducible] def algK : Algebra K (FractionRing (Y.presheaf.stalk y)) :=
  (IsFractionRing.lift (K := K) (g := algebraMap R (FractionRing (Y.presheaf.stalk y)))
    (injective_toFrac f y hy hmax halg)).toAlgebra

omit [LocallyOfFiniteType f] in
theorem tower_RKF : let := algK K f y hy hmax halg
    IsScalarTower R K (FractionRing (Y.presheaf.stalk y)) :=
  let := algK K f y hy hmax halg
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (K := K) (injective_toFrac f y hy hmax halg) x).symm

include gK e

/-- The generic-fibre point attached to a component stalk. -/
@[reducible] def xF : let := algK K f y hy hmax halg; let := tower_RKF K f y hy hmax halg
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (FractionRing (Y.presheaf.stalk
      y))))) gK :=
  let := algK K f y hy hmax halg; let := tower_RKF K f y hy hmax halg
  NeronModelInfra.schemeHomOverComp
    (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
      (⟨Y.fromSpecStalk y, halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f)) e

/-- The underlying generic-fibre point of a component reading. -/
@[reducible] def xpt : XK := (xF K gK f e y hy hmax halg).1.base (IsLocalRing.closedPoint
  (FractionRing (Y.presheaf.stalk y)))

omit [IsOpenImmersion e.1] [LocallyOfFiniteType f] in
theorem exists_chart (U₀ : XK.Opens) (hxU₀ : xpt K gK f e y hy hmax halg ∈ U₀) :
    let := algK K f y hy hmax halg
    ∃ (U : XK.Opens) (hU : IsAffineOpen U) (_algU : Algebra Γ(XK, U) (FractionRing
      (Y.presheaf.stalk y)))
      (_ : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U;
        IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk
        y)))) ≫ hU.fromSpec =
        (xF K gK f e y hy hmax halg).1),
      xpt K gK f e y hy hmax halg ∈ U ∧ U ≤ U₀ := by
  intro algK'
  have : IsScalarTower R K (FractionRing (Y.presheaf.stalk y)) :=
    tower_RKF K f y hy hmax halg
  obtain ⟨U'', hUmem, hxU, hUU₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    XK.isBasis_affineOpens) hxU₀
  let U : XK.Opens := U''
  have hUaff : IsAffineOpen U := hUmem
  change xpt K gK f e y hy hmax halg ∈ U at hxU
  change U ≤ U₀ at hUU₀
  have hrange : Set.range (xF K gK f e y hy hmax halg).1.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p = IsLocalRing.closedPoint (FractionRing (Y.presheaf.stalk y)) := Subsingleton.elim _ _
    rw [this]; exact hxU
  let xU : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ (U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι (xF K gK f e y hy hmax halg).1 hrange
  have hxU_fac : xU ≫ U.ι = (xF K gK f e y hy hmax halg).1 := IsOpenImmersion.lift_fac U.ι _ hrange
  let φ : Γ(XK, U) ⟶ CommRingCat.of (FractionRing (Y.presheaf.stalk y)) := Spec.homEquiv (xU ≫
    hUaff.isoSpec.hom)
  have hφ : Spec.map φ = xU ≫ hUaff.isoSpec.hom := Spec.homEquiv.symm_apply_apply (xU ≫
    hUaff.isoSpec.hom)
  let algU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))) = φ := rfl
  have hxfac : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk
    y)))) ≫
      hUaff.fromSpec = (xF K gK f e y hy hmax halg).1 := by
    rw [hφ', hφ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hxU_fac]
  let algKU : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
  have halgKU : algebraMap K Γ(XK, U) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U
    le_top).hom :=
    rfl
  have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U le_top ≫ φ =
      CommRingCat.ofHom (algebraMap K (FractionRing (Y.presheaf.stalk y))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← (xF K gK f e y hy hmax halg).2, ← hxfac, hφ']
    simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hUaff le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have ecomp : (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))).comp (algebraMap K
    Γ(XK, U)) =
      algebraMap K (FractionRing (Y.presheaf.stalk y)) := by
    have h := congrArg CommRingCat.Hom.hom key
    rw [halgKU]
    exact h
  have towKUF := IsScalarTower.of_algebraMap_eq' (R := K) (S := Γ(XK, U))
    (A := FractionRing (Y.presheaf.stalk y)) ecomp.symm
  exact ⟨U, hUaff, algU, towKUF, hxfac, hxU, hUU₀⟩

end A

theorem topToSections_smul {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec
  (CommRingCat.of A))
    (d : ℕ) (U : X.Opens) (g : Γ(X, U)) (s : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))) :
    f.topToSections d U (g • s) = g • f.topToSections d U s := by
  rw [AbelianVarieties.NOSProofs.AffineExteriorSections.ExteriorSections.topToSections_eq,
    map_smul, AbelianVarieties.NOSProofs.AffineExteriorSections.ExteriorSections.unitD_smul]
  rfl

/-- Transport a basis of differential sections to the affine presheaf. -/
noncomputable def basisKaehlerPresheaf {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(X, U) Γ(f.kaehler, U)) :
    Module.Basis (Fin d) Γ(X, U) (f.kaehlerPresheaf.obj (op U)) :=
  bU.map (LinearEquiv.ofBijective (f.kaehlerToSectionsₗ U)
    (Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hU)).symm

theorem bijective_smul_of_isFrameOn {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : Γ(f.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (ωU : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)))
    (hωU : f.topToSections d U ωU = (f.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    Function.Bijective fun g : Γ(X, U) => g • ωU := by
  have hbij := Scheme.Hom.topToSections_bijective_of_isAffineOpen f d hU
  have hfr := hω.bijective (W := U) le_top le_top
  have hcomp : (f.topToSections d U) ∘ (fun g : Γ(X, U) => g • ωU) =
      fun g : Γ(X, U) => g • ((f.topDifferentials d).presheaf.map (homOfLE le_top).op ω :
        Γ(f.topDifferentials d, U)) := by
    funext g
    simp only [Function.comp_apply, topToSections_smul, hωU]
  have h2 : Function.Bijective ((f.topToSections d U) ∘ (fun g : Γ(X, U) => g • ωU)) := by
    rw [hcomp]
    exact hfr
  exact ⟨fun a b hab => h2.1 (by simp only [Function.comp_apply, hab]),
    fun s => by obtain ⟨g, hg⟩ := h2.2 (f.topToSections d U s); exact ⟨g, hbij.1 hg⟩⟩

end ChartConstruction

private theorem maximal_fraction_stalk_point
    {Y : Scheme.{u}} (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (pt : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y)))) :
    let sp := Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))
    ∀ w : Y, w ⤳ (Y.fromSpecStalk y) (sp pt) → w = (Y.fromSpecStalk y) (sp pt) := by
  intro sp w hw
  have hηy : (Y.fromSpecStalk y) (sp pt) ⤳ y :=
    (Scheme.range_fromSpecStalk (x := y)).le ⟨_, rfl⟩
  let p : PrimeSpectrum (FractionRing (Y.presheaf.stalk y)) := pt
  have : p.asIdeal.IsPrime := p.isPrime
  have hpt : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have hp : (sp pt).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap (Y.presheaf.stalk y)
      (FractionRing (Y.presheaf.stalk y))) p.asIdeal = ⊥
    rw [hpt]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (Y.presheaf.stalk y)
      (FractionRing (Y.presheaf.stalk y)))
  obtain ⟨q, hq⟩ : w ∈ Set.range (Y.fromSpecStalk y).base := by
    rw [Scheme.range_fromSpecStalk]
    exact hw.trans hηy
  by_cases hqbot : q.asIdeal = ⊥
  · rw [← hq]
    congr 1
    apply PrimeSpectrum.ext
    exact hqbot.trans hp.symm
  · have hqmax : q = IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := q.2) hqbot)
    have hwy : w = y := by
      rw [← hq, hqmax]
      exact Scheme.fromSpecStalk_closedPoint
    rw [hwy] at hw ⊢
    exact (hw.antisymm hηy).eq

/-- A localized generic stalk point remains maximal in an open pullback chart. -/
private theorem generic_point_in_open_pullback
    {Y P X : Scheme.{u}} (y : Y) [IsDomain (Y.presheaf.stalk y)]
    [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    (b : P ⟶ Y) [IsPreimmersion b] (e : P ⟶ X) [IsOpenImmersion e]
    (p : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ P)
    (hp : p ≫ b = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)))) ≫
        Y.fromSpecStalk y) :
    IsPreimmersion (p ≫ e) ∧
      ∀ pt : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))),
        ∀ x : X, x ⤳ (p ≫ e) pt → x = (p ≫ e) pt := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (Y.presheaf.stalk y))
  have : IsPreimmersion (p ≫ b) := by rw [hp]; infer_instance
  have : IsPreimmersion p := IsPreimmersion.of_comp p b
  refine ⟨inferInstance, ?_⟩
  intro pt x hx
  have hxr : x ∈ Set.range e.base :=
    hx.mem_open e.isOpenEmbedding.isOpen_range ⟨p pt, rfl⟩
  obtain ⟨z, rfl⟩ := hxr
  change e z ⤳ e (p pt) at hx
  change e z = e (p pt)
  have hz : z ⤳ p pt := e.isEmbedding.isInducing.specializes_iff.mp hx
  have hbpt : b (p pt) = (Y.fromSpecStalk y)
      ((Spec.map (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y))))).base pt) :=
    congrArg (fun m : Spec (CommRingCat.of (FractionRing (Y.presheaf.stalk y))) ⟶ Y => m pt) hp
  have hmax : ∀ w : Y, w ⤳ b (p pt) → w = b (p pt) := by
    rw [hbpt]
    exact maximal_fraction_stalk_point y pt
  exact congrArg e (b.isEmbedding.injective (hmax _ (hz.map b.continuous)))

/-- An affine frame stays nonzero after localization of its ring of sections to a field. -/
private theorem ChartConstruction.topFormMap_ne_zero_of_frame_localization
    (K : Type u) [fieldK : Field K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) (ω : Γ(g.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (U : X.Opens) (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(X, U) Γ(g.kaehler, U))
    (F : Type u) [fieldF : Field F] [algKF : Algebra K F] [algAF : Algebra Γ(X, U) F]
    (hT : let : Algebra K Γ(X, U) := g.sectionsAlgebra U; IsScalarTower K Γ(X, U) F)
    (M : Submonoid Γ(X, U)) [hLoc : IsLocalization M F]
    (ωU : ⋀[Γ(X, U)]^d (g.kaehlerPresheaf.obj (op U)))
    (hωU : g.topToSections d U ωU = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    let : Algebra K Γ(X, U) := g.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(X, U) F d ωU ≠ 0 := by
  intro algKU
  have : IsScalarTower K Γ(X, U) F := hT
  let b : Module.Basis (Fin d) Γ(X, U) (Ω[Γ(X, U)⁄K]) :=
    basisKaehlerPresheaf g d hU bU
  have hbij : Function.Bijective (fun a : Γ(X, U) => a • ωU) :=
    bijective_smul_of_isFrameOn g d hU ω hω ωU hωU
  exact @NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
    K Γ(X, U) F fieldK (CommRingCat.commRing Γ(X, U)) algKU fieldF algAF algKF hT
    M hLoc d b ωU hbij

/-- An affine frame stays nonzero at a maximal point represented by a field preimmersion. -/
private theorem ChartConstruction.topFormMap_ne_zero_at_maximal_point
    (K : Type u) [Field K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d g]
    (ω : Γ(g.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (F : Type u) [Field F] [Algebra K F]
    (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
    (hmax : ∀ x : X, x ⤳ φ (IsLocalRing.closedPoint F) → x = φ (IsLocalRing.closedPoint F))
    (U : X.Opens) (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(X, U) Γ(g.kaehler, U))
    [Algebra Γ(X, U) F]
    (hT : let : Algebra K Γ(X, U) := g.sectionsAlgebra U; IsScalarTower K Γ(X, U) F)
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) F)) ≫ hU.fromSpec = φ)
    (ωU : ⋀[Γ(X, U)]^d (g.kaehlerPresheaf.obj (op U)))
    (hωU : g.topToSections d U ωU = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    let : Algebra K Γ(X, U) := g.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(X, U) F d ωU ≠ 0 := by
  intro algKU
  have : IsScalarTower K Γ(X, U) F := hT
  have : Smooth g := SmoothOfRelativeDimension.smooth (n := d) (f := g)
  have : IsReduced X := Smooth.isReduced_of_isReduced_of_isLocallyNoetherian g
  let pt : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  let x : X := φ pt
  have hxU : x ∈ U := by
    have hpoint : hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) F))) pt) = x :=
      congrArg (fun m : Spec (CommRingCat.of F) ⟶ X => m pt) hφ
    exact hU.range_fromSpec.le ⟨_, hpoint⟩
  have hloc : IsLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl F :=
    hU.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
      x hxU hmax F φ rfl hφ
  exact ChartConstruction.topFormMap_ne_zero_of_frame_localization K g d ω hω U hU bU
    F hT (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ωU hωU

theorem ChartConstruction.topFormMap_ne_zero_of_isFrameOn
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (_ : f.base y = IsLocalRing.closedPoint R)
    (_ : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
      y))))
    [IsDomain (Y.presheaf.stalk y)] [IsDiscreteValuationRing (Y.presheaf.stalk y)]
    [Algebra K (FractionRing (Y.presheaf.stalk y))] [IsScalarTower R K (FractionRing
      (Y.presheaf.stalk y))]
    (U : XK.Opens) (hU : IsAffineOpen U)
    (bU : Module.Basis (Fin d) Γ(XK, U) Γ(gK.kaehler, U))
    [Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))]
    (hT : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U;
      IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y))))
      ≫ hU.fromSpec =
      (NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
          (⟨Y.fromSpecStalk y, halg⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
        e).1)
    (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
    (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU ≠ 0 := by
  intro algKU
  let y₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f :=
    ⟨Y.fromSpecStalk y, halg⟩
  let pG := NeronModelInfra.pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y)) y₀
  have : IsPreimmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hpG : pG.1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
        (FractionRing (Y.presheaf.stalk y)))) ≫ Y.fromSpecStalk y :=
    NeronModelInfra.pointGenericFibre_coe_comp_fst y₀
  obtain ⟨hpre, hmax⟩ := generic_point_in_open_pullback y
    (pullback.fst f (specGenericFibreInclusion R K)) e.1 pG.1 hpG
  exact ChartConstruction.topFormMap_ne_zero_at_maximal_point K gK d ω hω
    (FractionRing (Y.presheaf.stalk y)) (pG.1 ≫ e.1) (hmax _) U hU bU hT hx ωU hωU

open ChartConstruction in
theorem _root_.NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing (Y.presheaf.stalk y))
      (_algebra : Algebra R (Y.presheaf.stalk y))
      (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R
        (Y.presheaf.stalk y))))
      (_algebraK : Algebra K (FractionRing (Y.presheaf.stalk y)))
      (_ : IsScalarTower R K (FractionRing (Y.presheaf.stalk y)))
      (b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R]))
      (U : XK.Opens) (hU : IsAffineOpen U)
      (_algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U;
        IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk
        y)))) ≫ hU.fromSpec =
        (schemeHomOverComp
          (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
            (⟨Y.fromSpecStalk y, halg⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
          e).1)
      (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
      (_ : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
      (a : FractionRing (Y.presheaf.stalk y)),
      (let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U;
        TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
          a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk
            y)) d
            (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)) ∧
      a ≠ 0 := by
  classical
  let algR : Algebra R (Y.presheaf.stalk y) := stalkAlgebra f y
  have halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R
    (Y.presheaf.stalk y))) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f y
  obtain ⟨hdom, hdvr, hinj⟩ := stalk_facts f y hy hmax halg
  have := smoothOfRelativeDimension_genericFibre_of_chart K gK d f e
  have : SmoothOfRelativeDimension d f :=
    AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_genericFibre K f d
  obtain ⟨b⟩ :=
    (open AlgebraicGeometry.SmoothOfRelativeDimension in
      nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq)
    f d y halg
  let algK' := algK K f y hy hmax halg
  have towRKF := tower_RKF K f y hy hmax halg
  obtain ⟨U₀, hxU₀, eΩ, hbasis⟩ :=
    (open AlgebraicGeometry.Scheme.Hom in
      exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension) gK d
      (xpt K gK f e y hy hmax halg)
  obtain ⟨U, hU, algU, towKUF, hx, hxU, hUU₀⟩ := exists_chart K gK f e y hy hmax halg U₀ hxU₀
  let := algU
  have hω' := exists_omegaU gK d ω U hU
  cases hω' with
  | intro ωU hωU =>
  have hline :=
    (NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
    R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d b).2
    (let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U;
      TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU)
  cases hline with
  | intro a ha =>
  have hbU := hbasis U hUU₀ hU
  cases hbU with
  | intro bU _ =>
  have hne := topFormMap_ne_zero_of_isFrameOn K gK d ω hω f e y hy hmax halg U hU bU towKUF hx
    ωU hωU
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hne
    rw [ha, zero_smul]
  exact ⟨hdom, hdvr, algR, halg, algK', towRKF, b, U, hU, algU, towKUF, hx, ωU, hωU, a, ha, ha0⟩

end

end AbelianVarieties.NOSProofs.ComponentConstruction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentFrames


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

noncomputable section

open AbelianVarieties.NOSProofs.ComponentConstruction.ChartConstruction
  (topToSections_smul basisKaehlerPresheaf bijective_smul_of_isFrameOn
    smoothOfRelativeDimension_genericFibre_of_chart exists_omegaU)

namespace FrameComparison

theorem isDomain_stalk_of_smooth {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (y : Y) : IsDomain
      (Y.presheaf.stalk y) := by
  let e : Γ(Spec (CommRingCat.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of
    R)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Spec (CommRingCat.of R), ⊤) := MulEquiv.isDomain R e.toMulEquiv
  have : IsIntegrallyClosed Γ(Spec (CommRingCat.of R), ⊤) := IsIntegrallyClosed.of_equiv e.symm
  exact (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f y).1

theorem ringHom_ext_of_specMap_comp_fromSpec_eq {X : Scheme.{u}} {U : X.Opens} (hU :
  IsAffineOpen U)
    {F : Type u} [CommRing F] (a b : Γ(X, U) →+* F)
    (h : Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom b) ≫
      hU.fromSpec) : a = b := by
  have h1 : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := by
    rw [← cancel_mono hU.fromSpec]; exact h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

theorem specMap_germ_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
  (hx : x ∈ U) :
    Spec.map (X.presheaf.germ U x hx) ≫ hU.fromSpec = X.fromSpecStalk x := by
  change hU.fromSpecStalk hx = _
  exact IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hx

end FrameComparison

end

end AbelianVarieties.NOSProofs.ComponentFrames

namespace NeronModelInfra.ComponentReading

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AbelianVarieties.NOSProofs.ComponentFrames
open AbelianVarieties.NOSProofs.ComponentConstruction.ChartConstruction
  (topToSections_smul basisKaehlerPresheaf bijective_smul_of_isFrameOn
    smoothOfRelativeDimension_genericFibre_of_chart exists_omegaU)

universe u

open FrameComparison in
theorem exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (_ : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R
      (T.Y.presheaf.stalk y₁)))) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ),
      ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
        [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
        (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
        (_ : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
        (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
          (schemeHomOverComp
            (pointGenericFibre (K := K) (K' := F)
              (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
                SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk
                  y₁)))) T.f))
            T.e).1)
        (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
        (_ : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE
          le_top).op ω),
        let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
        TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
          (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
              algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ m) •
            TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by
  classical
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have : IsLocalization.Away ϖ K := NeronModelInfra.isLocalizationAway_of_irreducible K hirr
  have : IsOpenImmersion T.e.1 := T.isOpenImmersion
  have : Smooth T.f := T.smooth
  have : LocallyOfFiniteType T.f := T.locallyOfFiniteType
  have := smoothOfRelativeDimension_genericFibre_of_chart K gK d T.f T.e
  have : SmoothOfRelativeDimension d T.f :=
    AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_genericFibre K T.f d
  have : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.f
  have : IsDomain (T.Y.presheaf.stalk y₁) := isDomain_stalk_of_smooth T.f y₁
  obtain ⟨hϖ0, hϖp⟩ :=
    AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
    ϖ hϖ T.f y₁ hy₁ halg₁
  obtain ⟨U₀, hyU₀, eΩ, hbasis⟩ :=
    (open AlgebraicGeometry.Scheme.Hom in
      exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension) T.f d y₁
  obtain ⟨W', hWaff, hyW, hWU₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T.Y.isBasis_affineOpens) hyU₀
  let W : T.Y.Opens := W'
  have hW : IsAffineOpen W := hWaff
  change y₁ ∈ W at hyW
  change W ≤ U₀ at hWU₀
  have hβ₀ := hbasis W hWU₀ hW
  cases hβ₀ with
  | intro β₀ _ =>
  let algRW : Algebra R Γ(T.Y, W) := T.f.sectionsAlgebra W
  let β : Module.Basis (Fin d) Γ(T.Y, W) (T.f.kaehlerPresheaf.obj (op W)) :=
    basisKaehlerPresheaf T.f d hW β₀
  let fstT := pullback.fst T.f (specGenericFibreInclusion R K)
  let sndT := pullback.snd T.f (specGenericFibreInclusion R K)
  let WK : (pullback T.f (specGenericFibreInclusion R K)).Opens := fstT ⁻¹ᵁ W
  have hPB : IsPullback fstT sndT T.f (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨hWK, hpush⟩ :=
    AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback T.f sndT fstT
      hPB W hW
  let U₂ : XK.Opens := T.e.1 ''ᵁ WK
  have hU₂ : IsAffineOpen U₂ := hWK.image_of_isOpenImmersion T.e.1
  let algKB' : Algebra K Γ(XK, U₂) := gK.sectionsAlgebra U₂
  let eApp : Γ(XK, U₂) ≅ Γ(pullback T.f (specGenericFibreInclusion R K), WK) := T.e.1.appIso WK
  let algBB' : Algebra Γ(T.Y, W) Γ(XK, U₂) := ((fstT.appLE W WK le_rfl) ≫ eApp.inv).hom.toAlgebra
  let algRB' : Algebra R Γ(XK, U₂) := ((algebraMap K Γ(XK, U₂)).comp (algebraMap R K)).toAlgebra
  have towRKB' : IsScalarTower R K Γ(XK, U₂) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let algKWK : Algebra K Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    sndT.sectionsAlgebra WK
  let algBWK : Algebra Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    (fstT.appLE W WK le_rfl).hom.toAlgebra
  let algRWK : Algebra R Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    ((algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp (algebraMap R
      K)).toAlgebra
  have towRKWK : IsScalarTower R K Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKWK : algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ sndT.appLE ⊤ WK le_top).hom := rfl
  have hcompWK : (algebraMap Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp
      (algebraMap R Γ(T.Y, W)) =
      (algebraMap K Γ(pullback T.f (specGenericFibreInclusion R K), WK)).comp (algebraMap R K)
        := by
    apply RingHom.ext
    intro r
    change (fstT.appLE W WK le_rfl).hom ((T.f.constToPresheaf.app (op W)).hom r) =
      (sndT.constToPresheaf.app (op WK)).hom (algebraMap R K r)
    have heq := SchemeTheory.DifferentialPullback.Construction.fac_apply T.f sndT fstT
      (pullback.condition) W r
    rw [Scheme.Hom.app_eq_appLE] at heq
    exact heq
  have towRBWK : IsScalarTower R Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    IsScalarTower.of_algebraMap_eq' hcompWK.symm
  have hKU₂ : algebraMap K Γ(XK, U₂) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U₂
    le_top).hom := rfl
  have hgKapp : gK.appLE ⊤ U₂ le_top = sndT.appLE ⊤ WK le_top ≫ eApp.inv := by
    rw [Iso.eq_comp_inv]
    change gK.appLE ⊤ U₂ le_top ≫ (T.e.1.appIso WK).hom = sndT.appLE ⊤ WK le_top
    exact (congrArg (gK.appLE ⊤ U₂ (fun _ _ => trivial) ≫ ·)
      (T.e.1.appIso_hom' WK)).trans
      ((Scheme.Hom.appLE_comp_appLE T.e.1 gK ⊤ U₂ WK (fun _ _ => trivial) _).trans
        (congrArg (fun g : pullback T.f (specGenericFibreInclusion R K) ⟶
          Spec (CommRingCat.of K) => g.appLE ⊤ WK (fun _ _ => trivial)) T.e.2))
  have towRBB' : IsScalarTower R Γ(T.Y, W) Γ(XK, U₂) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change (algebraMap K Γ(XK, U₂)).comp (algebraMap R K) =
      (eApp.inv.hom.comp (algebraMap Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K),
        WK))).comp
        (algebraMap R Γ(T.Y, W))
    rw [RingHom.comp_assoc, hcompWK, ← RingHom.comp_assoc]
    congr 1
    rw [hKU₂, hKWK, hgKapp]; rfl
  have hpo : Algebra.IsPushout R K Γ(T.Y, W) Γ(pullback T.f (specGenericFibreInclusion R K), WK)
    := hpush
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ))
      Γ(pullback T.f (specGenericFibreInclusion R K), WK) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers ϖ) K).mpr hpo.symm
  let eAlg : Γ(pullback T.f (specGenericFibreInclusion R K), WK) ≃ₐ[Γ(T.Y, W)] Γ(XK, U₂) :=
    AlgEquiv.ofRingEquiv (f := eApp.symm.commRingCatIsoToRingEquiv) (fun x => rfl)
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ)) Γ(XK, U₂) :=
    IsLocalization.isLocalization_of_algEquiv _ eAlg
  have hAway : IsLocalization.Away (algebraMap R Γ(T.Y, W) ϖ) Γ(XK, U₂) := by
    have hsub : Algebra.algebraMapSubmonoid Γ(T.Y, W) (Submonoid.powers ϖ) =
        Submonoid.powers (algebraMap R Γ(T.Y, W) ϖ) := Submonoid.map_powers _ _
    unfold IsLocalization.Away
    rw [← hsub]; infer_instance
  have hωU₂' := exists_omegaU gK d ω U₂ hU₂
  cases hωU₂' with
  | intro ωU₂ hωU₂ =>
  have hbij := bijective_smul_of_isFrameOn gK d hU₂ ω hω ωU₂ hωU₂
  have hspan : Submodule.span Γ(XK, U₂) {ωU₂} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro s
    obtain ⟨g, hg⟩ := hbij.2 s
    rw [Submodule.mem_span_singleton]
    exact ⟨g, hg⟩
  let algWO : Algebra Γ(T.Y, W) (T.Y.presheaf.stalk y₁) := (T.Y.presheaf.germ W y₁
    hyW).hom.toAlgebra
  have hlocO : IsLocalization.AtPrime (T.Y.presheaf.stalk y₁) (hW.primeIdealOf ⟨y₁,
    hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y₁, hyW⟩
  have htowO : (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁)).comp (algebraMap R Γ(T.Y, W)) =
      algebraMap R (T.Y.presheaf.stalk y₁) := by
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁)).comp
        (algebraMap R Γ(T.Y, W)))) = Spec.map (CommRingCat.ofHom (algebraMap R
          (T.Y.presheaf.stalk y₁))) := by
      rw [← halg₁]
      change Spec.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.f.appLE ⊤ W le_top) ≫
        T.Y.presheaf.germ W y₁ hyW) = _
      rw [Spec.map_comp, Spec.map_comp]
      have h2 : Spec.map (T.f.appLE ⊤ W le_top) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of
        R)).inv =
          hW.fromSpec ≫ T.f := by
        rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
        exact IsAffineOpen.SpecMap_appLE_fromSpec T.f (isAffineOpen_top _) hW le_top
      rw [h2, ← Category.assoc, specMap_germ_comp_fromSpec hW y₁ hyW]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have towerRWO : IsScalarTower R Γ(T.Y, W) (T.Y.presheaf.stalk y₁) :=
    IsScalarTower.of_algebraMap_eq' htowO.symm
  have hcore :=
    (open NeronModelInfra.TopFormOrder in
      @exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
      R K Γ(T.Y, W) Γ(XK, U₂) (T.Y.presheaf.stalk y₁)
      inferInstance inferInstance inferInstance ϖ inferInstance
      inferInstance algRW inferInstance algBB' algKB' algRB' towRBB' towRKB' hAway
      d β ωU₂ hspan inferInstance inferInstance inferInstance algWO inferInstance towerRWO
      (hW.primeIdealOf ⟨y₁, hyW⟩).asIdeal.primeCompl hlocO hϖ0 hϖp)
  rcases hcore with ⟨b', w, m, -, hF⟩
  refine ⟨b', w, m, ?_⟩
  intro F _ _ _ _ _ _ U hU _ hKU hx ωU hωU
  let pG := NeronModelInfra.pointGenericFibre (K := K) (K' := F)
    (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f)
  have hpG_fst : pG.1 ≫ fstT = Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁)
    F)) ≫
      T.Y.fromSpecStalk y₁ := NeronModelInfra.pointGenericFibre_coe_comp_fst _
  have hrangeW : ∀ z, fstT.base (pG.1.base z) ∈ W := by
    intro z
    rw [← Scheme.Hom.comp_apply, hpG_fst, Scheme.Hom.comp_apply]
    have hz : (T.Y.fromSpecStalk y₁).base
        ((Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) F))).base z) ∈
        Set.range (T.Y.fromSpecStalk y₁).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open W.2 hyW
  have hrange : Set.range (pG.1 ≫ T.e.1).base ⊆ Set.range U₂.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨pG.1.base z, hrangeW z, rfl⟩
  let xU := IsOpenImmersion.lift U₂.ι (pG.1 ≫ T.e.1) hrange
  have hxU_fac : xU ≫ U₂.ι = pG.1 ≫ T.e.1 := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(XK, U₂) ⟶ CommRingCat.of F := Spec.homEquiv (xU ≫ hU₂.isoSpec.hom)
  have hφ : Spec.map φ = xU ≫ hU₂.isoSpec.hom := Spec.homEquiv.symm_apply_apply (xU ≫
    hU₂.isoSpec.hom)
  let algB'F : Algebra Γ(XK, U₂) F := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap Γ(XK, U₂) F) = φ := rfl
  have hx₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U₂) F)) ≫ hU₂.fromSpec = pG.1 ≫ T.e.1
    := by
    rw [hφ', hφ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hxU_fac]
  have hxF2 : (pG.1 ≫ T.e.1) ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K F)) :=
    (NeronModelInfra.schemeHomOverComp pG T.e).2
  have keyK : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ gK.appLE ⊤ U₂ le_top ≫ φ =
      CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← hxF2, ← hx₂, hφ']
    simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec gK (isAffineOpen_top _) hU₂ le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have ecompK : (algebraMap Γ(XK, U₂) F).comp (algebraMap K Γ(XK, U₂)) = algebraMap K F := by
    have h := congrArg CommRingCat.Hom.hom keyK
    rw [hKU₂]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
    exact h
  have towKB'F : IsScalarTower K Γ(XK, U₂) F := IsScalarTower.of_algebraMap_eq' ecompK.symm
  let algWF : Algebra Γ(T.Y, W) F :=
    ((algebraMap (T.Y.presheaf.stalk y₁) F).comp (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk
      y₁))).toAlgebra
  have towerWOF : IsScalarTower Γ(T.Y, W) (T.Y.presheaf.stalk y₁) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  have towerRWF : IsScalarTower R Γ(T.Y, W) F := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change algebraMap R F = ((algebraMap (T.Y.presheaf.stalk y₁) F).comp
      (algebraMap Γ(T.Y, W) (T.Y.presheaf.stalk y₁))).comp (algebraMap R Γ(T.Y, W))
    rw [RingHom.comp_assoc, htowO, ← IsScalarTower.algebraMap_eq]
  have hSpecApp : Spec.map eApp.inv ≫ hWK.fromSpec ≫ T.e.1 = hU₂.fromSpec := by
    have h1 : Spec.map eApp.hom ≫ hU₂.fromSpec = hWK.fromSpec ≫ T.e.1 := by
      change Spec.map (T.e.1.appIso WK).hom ≫ hU₂.fromSpec = _
      rw [Scheme.Hom.appIso_hom']
      exact IsAffineOpen.SpecMap_appLE_fromSpec T.e.1 hU₂ hWK _
    rw [← h1, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have keyW : (algebraMap Γ(XK, U₂) F).comp (algebraMap Γ(T.Y, W) Γ(XK, U₂)) = algebraMap Γ(T.Y,
    W) F := by
    apply ringHom_ext_of_specMap_comp_fromSpec_eq hW
    let sF : T.Y.presheaf.stalk y₁ ⟶ CommRingCat.of F :=
      CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk y₁) F)
    have hpG_sF : pG.1 ≫ fstT = Spec.map sF ≫ T.Y.fromSpecStalk y₁ := hpG_fst
    change Spec.map ((fstT.appLE W WK le_rfl ≫ eApp.inv) ≫ φ) ≫ hW.fromSpec =
      Spec.map (T.Y.presheaf.germ W y₁ hyW ≫ sF) ≫ hW.fromSpec
    rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec fstT hW hWK le_rfl, specMap_germ_comp_fromSpec hW y₁
        hyW, ← hpG_sF]
    have h3 : Spec.map φ ≫ Spec.map eApp.inv ≫ hWK.fromSpec = pG.1 := by
      rw [← cancel_mono T.e.1]
      simp only [Category.assoc]
      rw [hSpecApp, ← hφ', hx₂]
    rw [← h3]
    simp only [Category.assoc]
  have towerWB'F : IsScalarTower Γ(T.Y, W) Γ(XK, U₂) F :=
    IsScalarTower.of_algebraMap_eq' keyW.symm
  have hmain := @hF F inferInstance inferInstance inferInstance inferInstance algWF algB'F
    inferInstance inferInstance towerWOF towerRWF towerWB'F towKB'F
  rw [← hmain]
  exact AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq gK d ω
    F U hU hKU U₂ hU₂
    towKB'F (hx.trans hx₂.symm) ωU hωU ωU₂ hωU₂

end NeronModelInfra.ComponentReading

namespace AbelianVarieties.NOSProofs.ComponentFrames

noncomputable section

end
end AbelianVarieties.NOSProofs.ComponentFrames
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentFrameComparison


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

end AbelianVarieties.NOSProofs.ComponentFrameComparison

namespace NeronModelInfra.ComponentReading

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AbelianVarieties.NOSProofs.ComponentFrameComparison

universe u

theorem exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R
      (T.Y.presheaf.stalk y₁))))
    (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
    (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
    (hKU : let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
              T.f))
        T.e).1)
    (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
    (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ),
      let : Algebra K Γ(XK, U) := gK.sectionsAlgebra U
      TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
        (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
            algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by
  obtain ⟨b', w, m, h⟩ :=
    (open _root_.NeronModelInfra.ComponentReading in
      exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
        ϖ hϖ K hω T y₁ hy₁ hgen halg₁)
  have hm : m = T.n :=
    NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul ϖ hϖ K hω T y₁
      hy₁ hgen halg₁ b' w m h
  exact ⟨b', w, hm ▸ h F U hU hKU hx ωU hωU⟩

end NeronModelInfra.ComponentReading

namespace AbelianVarieties.NOSProofs.ComponentFrameComparison

end AbelianVarieties.NOSProofs.ComponentFrameComparison
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ComponentOrderComparison


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

universe u

namespace SmoothStalks

theorem formallySmooth_stalk_of_smooth
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
      y)))) :
    Algebra.FormallySmooth R (Y.presheaf.stalk y) := by
  have hmap : algebraMap R (Y.presheaf.stalk y) = stalkAlgebraMap f y := by
    have heq := Spec.map_injective
      (halg.symm.trans (fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra f y))
    exact congrArg CommRingCat.Hom.hom heq
  have heq : ‹Algebra R (Y.presheaf.stalk y)› = stalkAlgebra f y :=
    Algebra.algebra_ext _ _ fun r => congrArg (fun h : R →+* Y.presheaf.stalk y => h r) hmap
  cases heq
  apply (SchemeTheory.LocalGeometry.SmoothnessDefect.mem_smoothLocus_iff f y).mp
  rw [f.smoothLocus_eq_top]
  trivial

end SmoothStalks

namespace Transport

theorem isDomain_and_isDiscreteValuationRing_stalk_opens
    {X : Scheme.{u}} (W : X.Opens) (x : ↥W)
    [IsDomain (X.presheaf.stalk x.1)] [IsDiscreteValuationRing (X.presheaf.stalk x.1)] :
    ∃ (_ : IsDomain ((W : Scheme.{u}).presheaf.stalk x)), IsDiscreteValuationRing ((W :
      Scheme.{u}).presheaf.stalk x) := by
  let r : ((W : Scheme.{u}).presheaf.stalk x) ≃+* X.presheaf.stalk x.1 := (W.stalkIso
    x).commRingCatIsoToRingEquiv
  have hD : IsDomain ((W : Scheme.{u}).presheaf.stalk x) := MulEquiv.isDomain (X.presheaf.stalk
    x.1) r.toMulEquiv
  exact ⟨hD, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing r.symm⟩

theorem isFractionRing_and_formallySmooth_stalk_opens
    {X Y' : Scheme.{u}} (W : X.Opens) (v : (W : Scheme.{u}) ⟶ Y') (x : ↥W)
    [IsDomain (X.presheaf.stalk x.1)] [IsDomain ((W : Scheme.{u}).presheaf.stalk x)]
    (hfrac : let φ := v.stalkMap x ≫ (W.stalkIso x).hom
      let : Algebra (Y'.presheaf.stalk (v.base x)) (FractionRing (X.presheaf.stalk x.1)) :=
        ((algebraMap (X.presheaf.stalk x.1) (FractionRing (X.presheaf.stalk x.1))).comp
          φ.hom).toAlgebra
      IsFractionRing (Y'.presheaf.stalk (v.base x)) (FractionRing (X.presheaf.stalk x.1)))
    (hfs : let φ := v.stalkMap x ≫ (W.stalkIso x).hom
      let : Algebra (Y'.presheaf.stalk (v.base x)) (X.presheaf.stalk x.1) := φ.hom.toAlgebra
      Algebra.FormallySmooth (Y'.presheaf.stalk (v.base x)) (X.presheaf.stalk x.1)) :
    (let _i1 : Algebra (Y'.presheaf.stalk (v.base x)) (FractionRing ((W :
      Scheme.{u}).presheaf.stalk x)) :=
        ((algebraMap ((W : Scheme.{u}).presheaf.stalk x)
          (FractionRing ((W : Scheme.{u}).presheaf.stalk x))).comp
            (v.stalkMap x).hom).toAlgebra;
      IsFractionRing (Y'.presheaf.stalk (v.base x)) (FractionRing ((W :
        Scheme.{u}).presheaf.stalk x))) ∧
    (let _i2 : Algebra (Y'.presheaf.stalk (v.base x)) ((W : Scheme.{u}).presheaf.stalk x) :=
      (v.stalkMap x).hom.toAlgebra;
      Algebra.FormallySmooth (Y'.presheaf.stalk (v.base x)) ((W : Scheme.{u}).presheaf.stalk x))
        := by
  let O' := Y'.presheaf.stalk (v.base x)
  let SW := (W : Scheme.{u}).presheaf.stalk x
  let SX := X.presheaf.stalk x.1
  let r : SW ≃+* SX := (W.stalkIso x).commRingCatIsoToRingEquiv
  let ψ : O' →+* SW := (v.stalkMap x).hom
  let φ : O' →+* SX := (v.stalkMap x ≫ (W.stalkIso x).hom).hom
  have hφψ : ∀ a, φ a = r (ψ a) := fun a => rfl
  let aX : Algebra O' SX := φ.toAlgebra
  let aW : Algebra O' SW := ψ.toAlgebra
  let aKX : Algebra O' (FractionRing SX) := ((algebraMap SX (FractionRing SX)).comp φ).toAlgebra
  let aKW : Algebra O' (FractionRing SW) := ((algebraMap SW (FractionRing SW)).comp ψ).toAlgebra
  let eS : SX ≃ₐ[O'] SW := AlgEquiv.ofRingEquiv (f := r.symm) (fun a => by
    change r.symm (φ a) = ψ a
    rw [hφψ, r.symm_apply_apply])
  let eK : FractionRing SX ≃ₐ[O'] FractionRing SW :=
    AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv r.symm) (fun a => by
      change IsFractionRing.ringEquivOfRingEquiv r.symm (algebraMap SX (FractionRing SX) (φ a)) =
        algebraMap SW (FractionRing SW) (ψ a)
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, hφψ, r.symm_apply_apply])
  constructor
  · have : IsFractionRing O' (FractionRing SX) := hfrac
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors O') eK
  · have : Algebra.FormallySmooth O' SX := hfs
    exact Algebra.FormallySmooth.of_equiv eS

end Transport

namespace OrderComparison

open _root_.NeronModelInfra.TopFormOrder

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  {d : ℕ} [SmoothOfRelativeDimension d gK]
  {ω : Γ(gK.topDifferentials d, ⊤)}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem lift_comp_genericFibreRestrict
    {Y Y' : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of R)) (fY' : Y' ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (v : SchemeHomOver (W.ι ≫ fY) fY')
    {S : Scheme.{u}} (a : S ⟶ (W : Scheme.{u})) (b : S ⟶ Spec (CommRingCat.of K))
    (hab : (a ≫ v.1) ≫ fY' = b ≫ specGenericFibreInclusion R K) :
    pullback.lift (a ≫ v.1) b hab =
      pullback.lift a b (by rw [← hab, Category.assoc, v.2]) ≫ (genericFibreRestrict R K fY'
        (W.ι ≫ fY) v).1 := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ← Category.assoc,
    pullback.lift_fst]
  · rw [pullback.lift_snd, Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.lift_snd]

theorem main (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : T'.y ⤳ u.1.base ⟨T.y, hyW⟩) :
    T'.n ≤ T.n ∧
    (T.n = T'.n → u.1.base ⟨T.y, hyW⟩ = T'.y ∧
      ∃ (W' : T.Y.Opens) (hW' : W' ≤ W), T.y ∈ W' ∧ IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1)) := by
  classical
  have : Smooth T.f := T.smooth
  have : Smooth T'.f := T'.smooth
  let : Algebra R (T.Y.presheaf.stalk T.y) := T.algebra
  let : Algebra K (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraK
  have : IsScalarTower R K (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTower
  let : Algebra Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) := T.algebraU
  let : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U
  have : IsScalarTower K Γ(XK, T.U) (FractionRing (T.Y.presheaf.stalk T.y)) := T.isScalarTowerU
  let O := T.Y.presheaf.stalk T.y
  let F := FractionRing O
  let x : (W : Scheme.{u}) := ⟨T.y, hyW⟩
  let y₁ : ↥T'.Y := u.1.base x
  let O' := T'.Y.presheaf.stalk y₁
  let φ : O' ⟶ O := u.1.stalkMap x ≫ (W.stalkIso x).hom
  let algO'O : Algebra O' O := φ.hom.toAlgebra
  let algO'F : Algebra O' F := ((algebraMap O F).comp φ.hom).toAlgebra
  let algRO' : Algebra R O' := stalkAlgebra T'.f y₁
  have halg₁ : T'.Y.fromSpecStalk y₁ ≫ T'.f = Spec.map (CommRingCat.ofHom (algebraMap R O')) :=
    fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra T'.f y₁
  have hy₁ : T'.f.base y₁ = IsLocalRing.closedPoint R := by
    change (u.1 ≫ T'.f).base x = _
    rw [u.2]
    exact T.hy
  obtain ⟨hdomO', hφinj, htowRO'O, hfracO'⟩ :=
    (open _root_.NeronModelInfra.ComponentReading in
      isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq)
      K T T' W hyW u hu
  have : IsDomain O' := hdomO'
  have : IsScalarTower R O' O := htowRO'O
  have : IsFractionRing O' F := hfracO'
  have : @IsScalarTower O' O F algO'O.toSMul Algebra.toSMul algO'F.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instROF : @IsScalarTower R O' F Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap R F r = algebraMap O F (φ.hom (algebraMap R O' r))
    rw [show φ.hom (algebraMap R O' r) = algebraMap R O r from (IsScalarTower.algebraMap_apply R
      O' O r).symm]
    exact IsScalarTower.algebraMap_apply R O F r
  obtain ⟨_, _, hlocRO, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes T.f T.y T.hy
      T.hmax T.halg
  have : IsLocalHom (algebraMap R O) := hlocRO
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hx' : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, T.U) F)) ≫ T.hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f))
        T'.e).1 := by
    rw [T.hx]
    let q₀ : Spec O ⟶ (W : Scheme.{u}) := Spec.map (W.stalkIso x).hom ≫ (W :
      Scheme.{u}).fromSpecStalk x
    have hq₀ι : q₀ ≫ W.ι = T.Y.fromSpecStalk T.y := by
      change (Spec.map (W.stalkIso x).hom ≫ (W : Scheme.{u}).fromSpecStalk x) ≫ W.ι =
        T.Y.fromSpecStalk x.1
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk W.ι (x := x), ←
        Category.assoc, ← Spec.map_comp,
        ← Scheme.Opens.stalkIso_inv]
      erw [(W.stalkIso x).inv_hom_id, Spec.map_id, Category.id_comp]
      rfl
    have hq₀u : q₀ ≫ u.1 = Spec.map φ ≫ T'.Y.fromSpecStalk y₁ := by
      change (Spec.map (W.stalkIso x).hom ≫ (W : Scheme.{u}).fromSpecStalk x) ≫ u.1 =
        Spec.map (u.1.stalkMap x ≫ (W.stalkIso x).hom) ≫ T'.Y.fromSpecStalk (u.1.base x)
      rw [Spec.map_comp, Category.assoc, Category.assoc]
      exact congrArg (Spec.map (W.stalkIso x).hom ≫ ·)
        (Scheme.SpecMap_stalkMap_fromSpecStalk u.1 (x := x)).symm
    have hspecO'F : Spec.map (CommRingCat.ofHom (algebraMap O' F)) =
        Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ Spec.map φ := by
      rw [← Spec.map_comp]; rfl
    change ((pointGenericFibre (K := K) (K' := F) (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O))) T.f)).1 ≫ T.e.1) =
      (pointGenericFibre (K := K) (K' := F) (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f)).1 ≫ T'.e.1
    have hcompat : (Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ q₀) ≫ W.ι ≫ T.f =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ specGenericFibreInclusion R K := by
      rw [Category.assoc, ← Category.assoc q₀, hq₀ι, T.halg, ← Spec.map_comp,
        specGenericFibreInclusion_eq, ← Spec.map_comp]
      congr 1
      change CommRingCat.ofHom ((algebraMap O F).comp (algebraMap R O)) = CommRingCat.ofHom
        ((algebraMap K F).comp (algebraMap R K))
      rw [← IsScalarTower.algebraMap_eq R O F, ← IsScalarTower.algebraMap_eq R K F]
    let pt : Spec (CommRingCat.of F) ⟶ pullback (W.ι ≫ T.f) (specGenericFibreInclusion R K) :=
      pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap O F)) ≫ q₀) (Spec.map
        (CommRingCat.ofHom (algebraMap K F)))
        (by rw [Category.assoc]; exact hcompat)
    have hT : (pointGenericFibre (K := K) (K' := F) (⟨T.Y.fromSpecStalk T.y, T.halg⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O))) T.f)).1 =
        pt ≫ (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 := by
      apply pullback.hom_ext
      · rw [pointGenericFibre_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ←
        Category.assoc,
          pullback.lift_fst, Category.assoc, hq₀ι]
      · rw [pointGenericFibre_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd,
        pullback.lift_snd]
    have hT' : (pointGenericFibre (K := K) (K' := F) (⟨T'.Y.fromSpecStalk y₁, halg₁⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R O'))) T'.f)).1 =
        pt ≫ (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 := by
      apply pullback.hom_ext
      · rw [pointGenericFibre_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst, ←
        Category.assoc,
          pullback.lift_fst, Category.assoc, hq₀u, hspecO'F, Category.assoc]
      · rw [pointGenericFibre_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd,
        pullback.lift_snd]
    rw [hT, hT', Category.assoc, Category.assoc, hu]
  obtain ⟨b', w, hread⟩ :=
    NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
      ϖ hϖ K hω T' y₁ hy₁ hgen halg₁ F T.U T.hU T.isScalarTowerU hx' T.ωU T.hωU
  have hO : Ideal.map (algebraMap R O) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O
    := hidx.map_maximalIdeal
  have hσ : (let : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U;
    topFormMap K K Γ(XK, T.U) F d T.ωU) =
      (algebraMap O' F (w : O') * algebraMap O' F (algebraMap R O' ϖ) ^ T'.n) •
        topFormMap R K O' F d (exteriorPower.ιMulti O' d b') := hread
  obtain ⟨hle, hiff⟩ :=
    (open NeronModelInfra.TopFormOrder in
      le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R K O' O F ϖ hϖ hO d b' T.b T'.n w (let : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U;
        topFormMap K K Γ(XK, T.U) F d T.ωU) hσ)
  have hordT : ord R K O d F (let : Algebra K Γ(XK, T.U) := gK.sectionsAlgebra T.U;
    topFormMap K K Γ(XK, T.U) F d T.ωU) = T.n := by
    obtain ⟨hρne, -⟩ :=
      NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R K O
      F d T.b
    obtain ⟨-, hordsmul⟩ :=
      NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis R K O F d T.b
    have := hordsmul T.a T.ha0 hρne
    rw [T.ha]
    exact this
  rw [hordT] at hle hiff
  refine ⟨hle, fun heq => ?_⟩
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R O' O) := hiff.mp heq
  have : Algebra.FormallySmooth R O := SmoothStalks.formallySmooth_stalk_of_smooth T.f T.y T.halg
  have : Algebra.FormallyEtale O' O :=
    Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hbij
  have hfsO : Algebra.FormallySmooth O' O := inferInstance
  obtain ⟨hdomS, hdvrS⟩ := Transport.isDomain_and_isDiscreteValuationRing_stalk_opens W x
  have := hdomS
  have := hdvrS
  obtain ⟨hfracS, hfsS⟩ := Transport.isFractionRing_and_formallySmooth_stalk_opens W u.1 x
    hfracO' hfsO
  obtain ⟨hϖO'0, hϖO'prime⟩ :=
    AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint ϖ
      hϖ T'.f y₁ hy₁ halg₁
  have : LocallyOfFiniteType u.1 := by
    have : LocallyOfFiniteType (u.1 ≫ T'.f) := by rw [u.2]; infer_instance
    exact HasRingHomProperty.of_comp (P := @LocallyOfFiniteType) (fun _ _ h =>
      RingHom.FiniteType.of_comp_finiteType h) this
  have : IsLocallyNoetherian T'.Y := LocallyOfFiniteType.isLocallyNoetherian T'.f
  obtain ⟨V, hxV, hVopen⟩ :=
    (open AlgebraicGeometry in
      exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing)
      u.1 x (algebraMap R O' ϖ) hϖO'0 hϖO'prime hfracS hfsS
  let W' : T.Y.Opens := W.ι ''ᵁ V
  have hW' : W' ≤ W := by
    rintro z ⟨z', -, rfl⟩; exact z'.2
  have hyW' : T.y ∈ W' := ⟨x, hxV, rfl⟩
  have hfac : T.Y.homOfLE hW' = (W.ι.isoImage V).inv ≫ V.ι := by
    rw [← cancel_mono W.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  have : IsOpenImmersion (V.ι ≫ u.1) := hVopen
  have hopen : IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1) := by
    rw [hfac, Category.assoc]; infer_instance
  let ψ := V.ι ≫ u.1
  let pt : (V : Scheme.{u}) := ⟨x, hxV⟩
  have hψpt : ψ.base pt = y₁ := rfl
  have hmemr : T'.y ∈ Set.range ψ.base :=
    hgen.mem_open ψ.isOpenEmbedding.isOpen_range ⟨pt, hψpt⟩
  obtain ⟨z, hz⟩ := hmemr
  have hzpt : z ⤳ pt := by
    rw [← ψ.isOpenEmbedding.isEmbedding.isInducing.specializes_iff, hz, hψpt]; exact hgen
  have hzT : (V.ι ≫ W.ι).base z ⤳ T.y := hzpt.map (V.ι ≫ W.ι).base.hom.continuous
  have hzsp : T.f.base ((V.ι ≫ W.ι).base z) = IsLocalRing.closedPoint R := by
    change ((V.ι ≫ W.ι) ≫ T.f).base z = _
    rw [Category.assoc, ← u.2, ← Category.assoc]
    change T'.f.base (ψ.base z) = _
    rw [hz]; exact T'.hy
  have hzeq : (V.ι ≫ W.ι).base z = (V.ι ≫ W.ι).base pt := (T.hmax _ hzT hzsp).trans rfl
  have hz' : z = pt := (V.ι ≫ W.ι).isOpenEmbedding.injective hzeq
  refine ⟨?_, W', hW', hyW', hopen⟩
  change y₁ = T'.y
  rw [← hψpt, ← hz', hz]

end OrderComparison

theorem _root_.NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : T'.y ⤳ u.1.base ⟨T.y, hyW⟩) :
    T'.n ≤ T.n ∧
    (T.n = T'.n → u.1.base ⟨T.y, hyW⟩ = T'.y ∧
      ∃ (W' : T.Y.Opens) (hW' : W' ≤ W), T.y ∈ W' ∧ IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1)) :=
  OrderComparison.main K hω T T' W hyW u hu hgen

end AbelianVarieties.NOSProofs.ComponentOrderComparison
end
