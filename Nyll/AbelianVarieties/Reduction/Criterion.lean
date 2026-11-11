/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.Ring
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeSchemeHomOverCompMulEqMul
public import Nyll.AbelianVarieties.Geometry.ProperSubgroups
public import Nyll.AbelianVarieties.Geometry.Subgroups
public import Nyll.AbelianVarieties.Geometry.Torsion.Bounds
public import Nyll.AbelianVarieties.NeronModels.MappingProperty
public import Nyll.AbelianVarieties.Reduction.Inertia
public import Nyll.AbelianVarieties.Reduction.TorsionSpecialization
public import Nyll.SchemeTheory.Morphisms.PropernessCriteria
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AbelianVarieties.NeronModels.Basic

/-! # Good reduction from unramified prime-power torsion -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.ReductionCriterion.Properness


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace ProperTransfer

theorem geometricallyConnected_of_iso_comp {X Y S : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (f : Y ⟶ S)
    [GeometricallyConnected f] : GeometricallyConnected (e ≫ f) := by
  have : MorphismProperty.RespectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyConnected : MorphismProperty Scheme.{u}) e f).mpr ‹_›

theorem geometricallyConnected_of_comp_iso {X Y S : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (f : Y ⟶ S)
    {h : X ⟶ S} (hh : e ≫ f = h) [GeometricallyConnected h] : GeometricallyConnected f := by
  have : f = inv e ≫ h := by rw [← hh, IsIso.inv_hom_id_assoc]
  rw [this]
  exact geometricallyConnected_of_iso_comp _ _

theorem connectedSpace_pullback_comp {X S : Scheme.{u}} (f : X ⟶ S) {k K' : Type u} [Field k]
  [Field K']
    (ι : Spec (CommRingCat.of k) ⟶ S) (y' : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of k))
    [GeometricallyConnected (pullback.snd f ι)] : ConnectedSpace ↥(pullback f (y' ≫ ι)) := by
  have h : ConnectedSpace ↥(pullback (pullback.snd f ι) y') :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f :=
      pullback.snd f ι))
      K' y'
  exact ((pullbackLeftPullbackSndIso f ι y').hom.homeomorph.connectedSpace_iff).mp h

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_eq_comp_or (K' : Type u) [Field K'] (φ : R →+* K') :
    (∃ ψ : K →+* K', φ = ψ.comp (algebraMap R K)) ∨
      ∃ ψ : IsLocalRing.ResidueField R →+* K', φ = ψ.comp (IsLocalRing.residue R) := by
  by_cases hinj : Function.Injective φ
  · left
    refine ⟨IsFractionRing.lift hinj, ?_⟩
    ext x
    exact (IsFractionRing.lift_algebraMap hinj x).symm
  · right
    have : IsLocalHom φ := by
      constructor
      intro a ha
      by_contra hna
      have hker : RingHom.ker φ ≠ ⊥ := by
        intro h
        exact hinj ((RingHom.injective_iff_ker_eq_bot φ).mpr h)
      have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
      have hmax : (RingHom.ker φ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hker
      have hle : IsLocalRing.maximalIdeal R = RingHom.ker φ :=
        (IsLocalRing.eq_maximalIdeal hmax).symm
      have ha' : a ∈ RingHom.ker φ := hle ▸ (IsLocalRing.mem_maximalIdeal a).mpr hna
      rw [RingHom.mem_ker] at ha'
      exact ha.ne_zero ha'
    refine ⟨IsLocalRing.ResidueField.lift φ, ?_⟩
    exact (IsLocalRing.ResidueField.lift_comp_residue φ).symm

theorem geometricallyConnected_of_fibres {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [GeometricallyConnected (pullback.snd f (specGenericFibreInclusion R K))]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      R))))] :
    GeometricallyConnected f := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K' _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  rcases exists_eq_comp_or K K' φ.hom with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · have hy : Spec.map φ = Spec.map (CommRingCat.ofHom ψ) ≫ specGenericFibreInclusion R K := by
      rw [specGenericFibreInclusion_eq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
      rfl
    rw [hy]
    exact connectedSpace_pullback_comp f _ _
  · have hy : Spec.map φ =
        Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
      rfl
    rw [hy]
    exact connectedSpace_pullback_comp f _ _

theorem specGeneric_ne_specClosed (x : Spec (CommRingCat.of K))
    (y : Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :
    (specGenericFibreInclusion R K) x ≠
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) y := by
  intro h
  let x' : PrimeSpectrum K := x
  let y' : PrimeSpectrum (IsLocalRing.ResidueField R) := y
  have he : PrimeSpectrum.comap (algebraMap R K) x' =
      PrimeSpectrum.comap (IsLocalRing.residue R) y' := h
  have hx : x'.asIdeal = ⊥ := by
    have : x'.asIdeal.IsPrime := x'.isPrime
    exact Ideal.eq_bot_of_prime x'.asIdeal
  have hy : y'.asIdeal = ⊥ := by
    have : y'.asIdeal.IsPrime := y'.isPrime
    exact Ideal.eq_bot_of_prime y'.asIdeal
  have h' := congrArg PrimeSpectrum.asIdeal he
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, hx, hy,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K),
    ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue] at h'
  exact IsDiscreteValuationRing.not_isField R
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h'.symm)

end DVR

theorem geometricallyConnected_of_connectedSpace {k : Type u} [Field k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) : GeometricallyConnected f := by
  exact (open AbelianVarieties.NOSProofs.ChevalleyAssembly in
    Assembly.geometricallyConnected_of_connectedSpace L)

end ProperTransfer

end NeronModelInfra.ReductionCriterion.Properness

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one in
open H2bHomExt (connectedSpace_of_bundle) in
open NeronModelInfra.ReductionCriterion.Properness.ProperTransfer in
theorem abelianScheme_of_neronModel_of_proper_fibres
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (hproper : ∀ (G₀ : Scheme.{u})
        (i : G₀ ⟶ pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
        [IsOpenImmersion i],
        Set.range i =
          connectedComponent
            (((LB.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).one
                (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).1
              (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) →
        IsProper (i ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :
    AbelianSchemePropertyBundle R g := by
  classical
  have : Smooth g := hN.smooth
  have : IsSeparated g := hN.separated
  have : LocallyOfFiniteType g := hN.locallyOfFiniteType
  have : QuasiCompact g := hN.quasiCompact
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian g
  set k : Type u := IsLocalRing.ResidueField R with hk
  set ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) with hι
  have : IsClosedImmersion ι :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  set ιK := specGenericFibreInclusion R K with hιK
  obtain ⟨U, iU, LU, hopenU, hrangeU, hpreU, hcomplU, -, -⟩ :=
    exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
      LB ι
  have : IsOpenImmersion iU := hopenU
  let j : pullback (iU ≫ g) ι ⟶ pullback g ι :=
    pullback.map (iU ≫ g) ι g ι iU (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hj_snd : j ≫ pullback.snd g ι = pullback.snd (iU ≫ g) ι := by
    simp only [j, pullback.map, pullback.lift_snd, Category.comp_id]
  have hrange_j : Set.range j =
      connectedComponent (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of k)))).1
        (IsLocalRing.closedPoint k)) := by
    rw [Scheme.Pullback.range_map, ← hpreU]
    simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id, Set.preimage_univ,
      Set.inter_univ]
  have : IsProper (pullback.snd (iU ≫ g) ι) := by
    rw [← hj_snd]; exact hproper _ j hrange_j
  have : GeometricallyConnected (pullback.snd (iU ≫ g) ι) := by
    obtain ⟨G₀, i₀, L₀, hopen₀, -, -, -, hgc₀, hrange₀, -⟩ :=
      exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
        k (LB.baseChange ι)
    have : IsOpenImmersion i₀ := hopen₀
    have : GeometricallyConnected (i₀ ≫ pullback.snd g ι) := hgc₀
    let e := IsOpenImmersion.isoOfRangeEq j i₀ (hrange_j.trans hrange₀.symm)
    have he : e.hom ≫ (i₀ ≫ pullback.snd g ι) = pullback.snd (iU ≫ g) ι := by
      rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, hj_snd]
    rw [← he]
    exact geometricallyConnected_of_iso_comp _ _
  have : ConnectedSpace ↥(pullback g ιK) := connectedSpace_of_bundle hBK
  have : GeometricallyConnected (pullback.snd g ιK) :=
    geometricallyConnected_of_connectedSpace _ (LB.baseChange ιK)
  let jK : pullback (iU ≫ g) ιK ⟶ pullback g ιK :=
    pullback.map (iU ≫ g) ιK g ιK iU (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hjK_snd : jK ≫ pullback.snd g ιK = pullback.snd (iU ≫ g) ιK := by
    simp only [jK, pullback.map, pullback.lift_snd, Category.comp_id]
  have hjK_surj : Function.Surjective jK := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_map, Set.eq_univ_iff_forall]
    intro z
    refine ⟨?_, ⟨_, rfl⟩⟩
    change pullback.fst g ιK z ∈ Set.range iU
    apply hcomplU
    rintro ⟨w, hw⟩
    have h1 : g (pullback.fst g ι w) = ι (pullback.snd g ι w) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h2 : g (pullback.fst g ιK z) = ιK (pullback.snd g ιK z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [hw, h2] at h1
    exact specGeneric_ne_specClosed K _ _ h1
  have : GeometricallyConnected (pullback.snd (iU ≫ g) ιK) := by
    have : Epi jK.base := (TopCat.epi_iff_surjective _).mpr hjK_surj
    have : IsIso jK := IsOpenImmersion.isIso jK
    rw [← hjK_snd]
    exact geometricallyConnected_of_iso_comp _ _
  have : GeometricallyConnected (iU ≫ g) := geometricallyConnected_of_fibres K (iU ≫ g)
  have : IsProper (iU ≫ g) :=
    AlgebraicGeometry.isProper_of_isProper_pullback_snd_of_geometricallyConnected_of_isLocalRing
      (iU ≫ g)
      (LU.one (𝟙 _)).1 (LU.one (𝟙 _)).2 ι
  have hU : AbelianSchemePropertyBundle R (iU ≫ g) :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => (iU ≫ g).isConnected_preimage_singleton s
      hasGroupLaw := ⟨LU⟩ }
  have : PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K)) := inferInstance
  exact (open NeronModelInfra.NeronModelPropertyBundle in
    (isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion K hN iU rfl hU).2)

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.ReductionCriterion.Torsion


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TorsionBounds

open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection
  (torsionEquivBaseChange torsionEquivOfEq)

theorem key_ineq {ℓ d c : ℕ} (hℓ : 2 ≤ ℓ) (hd : 0 < d) :
    c * ℓ ^ (c * (2 * d - 1)) < ℓ ^ (2 * d * c) := by
  have h1 : c < ℓ ^ c := Nat.lt_pow_self (by omega)
  have h2 : 2 * d * c = c * (2 * d - 1) + c := by
    have : 2 * d = (2 * d - 1) + 1 := by omega
    calc 2 * d * c = ((2 * d - 1) + 1) * c := by rw [← this]
      _ = c * (2 * d - 1) + c := by ring
  rw [h2, pow_add]
  have hpos : 0 < ℓ ^ (c * (2 * d - 1)) := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  calc c * ℓ ^ (c * (2 * d - 1)) = ℓ ^ (c * (2 * d - 1)) * c := by ring
    _ < ℓ ^ (c * (2 * d - 1)) * ℓ ^ c := Nat.mul_lt_mul_of_pos_left h1 hpos

end TorsionBounds

end NeronModelInfra.ReductionCriterion.Torsion

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection
  (torsionEquivBaseChange torsionEquivOfEq) in
open NeronModelInfra.ReductionCriterion.Torsion.TorsionBounds in
theorem abelianScheme_of_neronModel_of_fixed_torsion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓu : IsUnit (ℓ : R))
    (hunr : ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1) :
    AbelianSchemePropertyBundle R g := by
  classical
  have : Smooth g := hN.smooth
  have : IsSeparated g := hN.separated
  have : LocallyOfFiniteType g := hN.locallyOfFiniteType
  have : QuasiCompact g := hN.quasiCompact
  obtain ⟨d, hd⟩ :=
    exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing LB
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension d f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  have : SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K)) :=
    hbc.of_isPullback (IsPullback.of_hasPullback g (specGenericFibreInclusion R K)) hd
  set k : Type u := IsLocalRing.ResidueField R with hk
  set ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) with hι
  have : SmoothOfRelativeDimension d (pullback.snd g ι) :=
    hbc.of_isPullback (IsPullback.of_hasPullback g ι) hd
  have hc : (LB.baseChange ι).IsCommutative :=
    RelativeGroupLaw.IsCommutative.baseChange ι (fun t x y => hcomm t x y)
  set k' : Type u := AlgebraicClosure k with hk'
  rcases forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
      k (pullback.snd g ι) (LB.baseChange ι) hc d k' with hprop | ⟨hdpos, c, hbound⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.abelianScheme_of_neronModel_of_proper_fibres
      K LB hN hBK hprop
  · exfalso
    have hk'zero : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0 := by
      intro r hr
      rw [IsScalarTower.algebraMap_apply R k k', IsLocalRing.ResidueField.algebraMap_eq,
        (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
    obtain ⟨r, hr⟩ :=
      exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
        K LB hcomm hN hBK d ℓ hℓu hunr k' hk'zero c
    have hm : ((ℓ ^ c : ℕ) : k) ≠ 0 := by
      have hu : IsUnit ((ℓ : k) ^ c) := by
        have := (hℓu.map (algebraMap R k)).pow c
        rwa [map_natCast] at this
      rw [Nat.cast_pow]
      exact hu.ne_zero
    obtain ⟨hfin, hcard⟩ := hbound (ℓ ^ c) hm
    set t' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k k')) with ht'
    have hcomp : t' ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap R k')) := by
      rw [ht', hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq R k k',
        IsLocalRing.ResidueField.algebraMap_eq]
    let e := (torsionEquivBaseChange ι LB t' (ℓ ^ c)).trans (torsionEquivOfEq LB hcomp (ℓ ^ c))
    have : Finite {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) (ℓ ^ c) y} :=
      Finite.of_equiv _ e
    have h1 : ℓ ^ (2 * d * c) ≤
        Nat.card {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) (ℓ ^ c) y} := by
      simpa only [Nat.card_fin] using Nat.card_le_card_of_injective r hr
    have h2 : Nat.card {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) (ℓ ^ c) y} ≤
        c * (ℓ ^ c) ^ (2 * d - 1) := by
      rw [← Nat.card_congr e]; exact hcard
    have h3 := key_ineq (c := c) hℓ.two_le hdpos
    rw [← pow_mul] at h2
    omega

end GoodReductionJacobian.RelativeGroupLaw
end
