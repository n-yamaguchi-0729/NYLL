/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.Transcendence
public import Nyll.ValuedFieldTheory.Valuation.ResidueTranscendence
public import Nyll.SchemeTheory.Morphisms.AffineCompactification
public import Nyll.SchemeTheory.ProjectiveSpace.AwayRatio
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataReducedSubschemeVanishingIdealLeKer
public import Nyll.SchemeTheory.Morphisms.AppLECongr

/-!
# Local dimension of schemes of finite type

Affine chart dimensions, the dimension formula at a point, generic fibres and a
valuation-theoretic proper model. Chart algebra structures and stalk heights use the
existing sections and normalization APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology AlgebraicGeometry
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula
  (height_eq_ringKrullDim_of_isMaximal)
open AlgebraicCurves.Geometry.Schemes.Proofs
open SmoothOfRelativeDimension_topologicalKrullDim_le.P2mSmoothOfRelativeDimensionKrullDim
  (topologicalKrullDim_le_of_forall_exists_isOpenEmbedding)
open AbelianVarieties.NOSProofs.VarietyNormalization.AlgebraicGeometry.NormalizationOfVariety
  (chart_finiteType primeIdealOf_fromSpec ringKrullDim_stalk_eq_height)

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

open _root_.AlgebraicGeometry

namespace FibreDimension

section Algebra

theorem exists_ringKrullDim_eq_natCast (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have hfin : m.height ≠ ⊤ := by
    have : m.FiniteHeight := inferInstance
    exact Ideal.height_ne_top hm.ne_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨n, ?_⟩
  rw [← height_eq_ringKrullDim_of_isMaximal k m, ← hn]
  rfl

theorem ringKrullDim_le_ringKrullDim_localization (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {g : A} (hg : g ≠ 0)
    (L : Type v) [CommRing L] [Algebra A L] [IsLocalization.Away g L] :
    ringKrullDim A ≤ ringKrullDim L := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced]
  have hg' : g ∉ (⊥ : Ideal A).jacobson := by rw [hjac]; exact hg
  rw [Ideal.jacobson, Ideal.mem_sInf] at hg'
  simp only [Set.mem_ofPred_eq, not_forall, exists_prop] at hg'
  obtain ⟨M, ⟨-, hM⟩, hgM⟩ := hg'
  have : M.IsMaximal := hM
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid A) : Set A) (M : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgM (hM.isPrime.mem_of_pow_mem n hn)
  have hMap : (M.map (algebraMap A L)).height = M.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers g) M hdisj
  have : (M.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L M hM.isPrime hdisj
  calc ringKrullDim A = M.height := (height_eq_ringKrullDim_of_isMaximal k M).symm
    _ = (M.map (algebraMap A L)).height := by rw [hMap]
    _ ≤ ringKrullDim L := Ideal.height_le_ringKrullDim_of_isPrime

theorem exists_minimalPrime_ringKrullDim_le (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {B : Type v} [CommRing B]
    [IsNoetherianRing B] (φ : B →+* A) (P : Ideal A) [P.IsPrime] (m : Ideal B) [hm : m.IsMaximal]
    (hmP : m = P.comap φ) :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q ≤ P ∧ m.map φ ≤ Q ∧
      ringKrullDim A ≤ ringKrullDim (A ⧸ Q) +
        ((m.map (Ideal.Quotient.mk (RingHom.ker φ))).height : WithBot ℕ∞) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set J : Ideal A := m.map φ with hJ
  have hJP : J ≤ P := by rw [hJ, Ideal.map_le_iff_le_comap, hmP]
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
  have hQ : Q.IsPrime := hQmin.1.1
  have hJQ : J ≤ Q := hQmin.1.2
  refine ⟨Q, hQ, hQP, hJQ, ?_⟩
  set I : Ideal B := RingHom.ker φ with hI
  let ψ : B ⧸ I →+* A := RingHom.kerLift φ
  have hψmk : ψ.comp (Ideal.Quotient.mk I) = φ := RingHom.ext fun b => RingHom.kerLift_mk φ b
  let : Algebra (B ⧸ I) A := ψ.toAlgebra
  set m' : Ideal (B ⧸ I) := m.map (Ideal.Quotient.mk I) with hm'
  have hIm : I ≤ m := by
    rw [hmP, hI, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hm'c : m'.comap (Ideal.Quotient.mk I) = m := by
    rw [hm', Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIm]
  have hm'max : m'.IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        hm).resolve_left ?_
    intro htop
    apply hm.ne_top
    rw [← hm'c]
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) m) = ⊤
    rw [htop, Ideal.comap_top]
  have hm'J : m'.map (algebraMap (B ⧸ I) A) = J := by
    change (m.map (Ideal.Quotient.mk I)).map ψ = m.map φ
    rw [Ideal.map_map, hψmk]
  have : Q.LiesOver m' := by
    refine ⟨(hm'max.eq_of_le ?_ ?_)⟩
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap, hm'J]
      exact hJQ
  have hkrull := Ideal.height_le_height_add_of_liesOver m' Q
  rw [hm'J] at hkrull
  have hQJ : (Q.map (Ideal.Quotient.mk J)).height = 0 := by
    obtain ⟨q, hq, hqQ⟩ : ∃ q ∈ minimalPrimes (A ⧸ J), Ideal.comap (Ideal.Quotient.mk J) q = Q := by
      have : Q ∈ Ideal.comap (Ideal.Quotient.mk J) '' minimalPrimes (A ⧸ J) := by
        rw [← Ideal.minimalPrimes_eq_comap]; exact hQmin
      exact this
    have hqeq : Q.map (Ideal.Quotient.mk J) = q := by
      rw [← hqQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have : q.IsPrime := hq.1.1
    rw [hqeq]
    exact Ideal.height_eq_zero_iff.mpr hq
  rw [hQJ, add_zero] at hkrull
  have hdimf := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  rw [← hdimf, add_comm]
  have hk' : ((Q.height : ℕ∞) : WithBot ℕ∞) ≤ ((m'.height : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast hkrull
  exact add_le_add_right hk' _

end Algebra

section TopologyB2

theorem topologicalKrullDim_affineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim ↥U = ringKrullDim Γ(X, U) := by
  have h : topologicalKrullDim (Spec Γ(X, U)) = ringKrullDim Γ(X, U) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph] at h
  exact h

theorem topologicalKrullDim_zeroLocus {A : Type u} [CommRing A] (I : Ideal A) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) = ringKrullDim (A ⧸ I) := by
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [range_comap_of_surjective (A ⧸ I) _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let e : PrimeSpectrum (A ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set A) :=
    hce.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (A ⧸ I)]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

theorem topologicalKrullDim_le_of_isEmbedding_image {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) (s : Set X) (t : Set Y)
    (hst : f '' s ⊆ t) : topologicalKrullDim s ≤ topologicalKrullDim t := by
  let φ : s → t := fun z => ⟨f z.1, hst ⟨z.1, z.2, rfl⟩⟩
  have hφ : IsInducing φ := (hf.isInducing.comp IsInducing.subtypeVal).codRestrict _
  exact Topology.IsInducing.topologicalKrullDim_le hφ

end TopologyB2

section Integral

variable {k : Type u} [Field k]

theorem topologicalKrullDim_le_ringKrullDim {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fX] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := by
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding (X := X) _ fun ξ => ?_
  obtain ⟨U', hU', hξU', -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := ξ) (U := ⊤) trivial
  refine ⟨↥U', inferInstance, Subtype.val, U'.2.isOpenEmbedding_subtypeVal, ⟨⟨ξ, hξU'⟩, rfl⟩, ?_⟩
  rw [topologicalKrullDim_affineOpen hU']
  obtain ⟨z, hzU, hzU'⟩ := nonempty_preirreducible_inter U.2 U'.2 hUne ⟨ξ, hξU'⟩
  obtain ⟨g, hgU, hzg⟩ := hU'.exists_basicOpen_le ⟨z, hzU⟩ hzU'
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hzg
    exact hzg
  have : Nonempty U' := ⟨⟨ξ, hξU'⟩⟩
  let algKU : Algebra k Γ(X, U') := fX.sectionsAlgebra U'
  have : Algebra.FiniteType k Γ(X, U') := chart_finiteType fX hU'
  have := hU'.isLocalization_basicOpen g
  have h1 : ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, X.basicOpen g) :=
    ringKrullDim_le_ringKrullDim_localization k hg _
  have h2 : ringKrullDim Γ(X, X.basicOpen g) = topologicalKrullDim ↥(X.basicOpen g) :=
    (topologicalKrullDim_affineOpen (hU'.basicOpen g)).symm
  have h3 : topologicalKrullDim ↥(X.basicOpen g) ≤ topologicalKrullDim ↥U :=
    Topology.IsInducing.topologicalKrullDim_le (IsEmbedding.inclusion hgU).isInducing
  rw [← topologicalKrullDim_affineOpen hU]
  exact h1.trans (h2.le.trans h3)

theorem main_integral {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IsIntegral X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (_ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have hxV : x ∈ o ⁻¹ᵁ V := by change o x ∈ V; rw [hx]; exact hyV
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ o ⁻¹ᵁ V := hUV
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let algA : Algebra k Γ(X, U) := fX.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := chart_finiteType fX hU
  have : IsNoetherianRing Γ(Y, V) := by
    let algKV : Algebra k Γ(Y, V) := fY.sectionsAlgebra V
    have : Algebra.FiniteType k Γ(Y, V) := chart_finiteType fY hV
    exact Algebra.FiniteType.isNoetherianRing k Γ(Y, V)
  let φ : Γ(Y, V) →+* Γ(X, U) := (o.appLE V U hUV').hom
  let px : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  let py : PrimeSpectrum Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  have hmax : py.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hy
  have hcomap : px.comap φ = py := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := o) V hV U hU hUV' hxU
    have : (⟨o x, hUV' hxU⟩ : V) = ⟨y, hyV⟩ := Subtype.ext hx
    rw [this] at h
    exact h
  have hmP : py.asIdeal = px.asIdeal.comap φ := by
    rw [← hcomap]; rfl
  obtain ⟨Q, hQ, hQP, hmQ, hdim⟩ :=
    exists_minimalPrime_ringKrullDim_le k φ px.asIdeal py.asIdeal hmP
  let Z₀ : Set (PrimeSpectrum Γ(X, U)) := PrimeSpectrum.zeroLocus (Q : Set Γ(X, U))
  let ι : PrimeSpectrum Γ(X, U) → X := fun p => hU.fromSpec p
  have hιemb : IsOpenEmbedding ι := hU.fromSpec.isOpenEmbedding
  let Z : Set X := closure (ι '' Z₀)
  have hxZ₀ : px ∈ Z₀ := by
    change px ∈ PrimeSpectrum.zeroLocus (Q : Set Γ(X, U))
    rw [PrimeSpectrum.mem_zeroLocus]
    exact hQP
  have hιpx : ι px = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  refine ⟨Z, ?_, ?_, ?_, isClosed_closure, ?_⟩
  · exact subset_closure ⟨px, hxZ₀, hιpx⟩
  · refine closure_minimal ?_ (hy.preimage o.continuous)
    rintro _ ⟨p, hp, rfl⟩
    change o (hU.fromSpec p) = y
    have hsq : hV.fromSpec (PrimeSpectrum.comap φ p) = o (hU.fromSpec p) :=
      congrArg (fun g : Spec Γ(X, U) ⟶ Y => g (p : Spec Γ(X, U)))
        (IsAffineOpen.SpecMap_appLE_fromSpec o hV hU hUV')
    have hcp : PrimeSpectrum.comap φ p = py := by
      apply PrimeSpectrum.ext
      refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
      rw [PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
      exact hmQ.trans ((PrimeSpectrum.mem_zeroLocus _ _).mp hp)
    exact hsq.symm.trans
      ((congrArg (fun q : PrimeSpectrum Γ(Y, V) => hV.fromSpec q) hcp).trans
        (hV.fromSpec_primeIdealOf ⟨y, hyV⟩))
  · refine IsIrreducible.closure (IsIrreducible.image ?_ ι hιemb.continuous.continuousOn)
    rw [PrimeSpectrum.isIrreducible_zeroLocus_iff, Ideal.IsPrime.radical hQ]
    exact hQ
  · have hX : topologicalKrullDim X ≤ ringKrullDim Γ(X, U) :=
      topologicalKrullDim_le_ringKrullDim fX hU ⟨x, hxU⟩
    have hZ : ringKrullDim (Γ(X, U) ⧸ Q) ≤ topologicalKrullDim Z := by
      rw [← topologicalKrullDim_zeroLocus Q]
      exact topologicalKrullDim_le_of_isEmbedding_image hιemb.isEmbedding Z₀ Z subset_closure
    have hI : ((Ideal.map (Ideal.Quotient.mk (RingHom.ker φ)) py.asIdeal).height : WithBot ℕ∞) ≤
        topologicalKrullDim (closure (Set.range o)) := by
      refine (Ideal.height_le_ringKrullDim_of_ne_top ?_).trans ?_
      · intro htop
        apply hmax.ne_top
        have hIm : RingHom.ker φ ≤ py.asIdeal := by
          rw [hmP, RingHom.ker_eq_comap_bot]; exact Ideal.comap_mono bot_le
        have := congrArg (Ideal.comap (Ideal.Quotient.mk (RingHom.ker φ))) htop
        rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ←
            RingHom.ker_eq_comap_bot,
          Ideal.mk_ker, sup_eq_left.mpr hIm, Ideal.comap_top] at this
      · rw [← topologicalKrullDim_zeroLocus (RingHom.ker φ), ← PrimeSpectrum.closure_range_comap]
        let ιV : PrimeSpectrum Γ(Y, V) → Y := fun p => hV.fromSpec p
        have hιV : IsOpenEmbedding ιV := hV.fromSpec.isOpenEmbedding
        refine topologicalKrullDim_le_of_isEmbedding_image hιV.isEmbedding _ _ ?_
        refine (image_closure_subset_closure_image hιV.continuous).trans (closure_mono ?_)
        rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
        refine ⟨ι p, ?_⟩
        exact (congrArg (fun g : Spec Γ(X, U) ⟶ Y => g (p : Spec Γ(X, U)))
          (IsAffineOpen.SpecMap_appLE_fromSpec o hV hU hUV')).symm
    calc topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := hX
      _ ≤ ringKrullDim (Γ(X, U) ⧸ Q) +
          ((Ideal.map (Ideal.Quotient.mk (RingHom.ker φ)) py.asIdeal).height : WithBot ℕ∞) := hdim
      _ ≤ topologicalKrullDim Z + topologicalKrullDim (closure (Set.range o)) := add_le_add hZ hI

end Integral

section Reduction

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k]

theorem main {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by
  let Xr : Scheme.{u} := (vanishingIdeal (⊤ : Closeds X)).subscheme
  let ι : Xr ⟶ X := (vanishingIdeal (⊤ : Closeds X)).subschemeι
  have : IsReduced Xr :=
    (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (⊤ : Closeds X)).1
  have hrange : Set.range ι = Set.univ := by
    change Set.range (vanishingIdeal (⊤ : Closeds X)).subschemeι = Set.univ
    rw [range_subschemeι]
    apply Set.eq_univ_of_univ_subset
    have : (⊤ : Closeds X) ≤ (vanishingIdeal (⊤ : Closeds X)).support :=
      le_support_iff_le_vanishingIdeal.mpr le_rfl
    exact this
  have hsurj : Function.Surjective ι := Set.range_eq_univ.mp hrange
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  let e : Xr ≃ₜ X := hemb.toHomeomorphOfSurjective hsurj
  have he : ∀ z, e z = ι z := fun z => rfl
  have : IrreducibleSpace Xr := e.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral Xr := isIntegral_of_irreducibleSpace_of_isReduced Xr
  obtain ⟨x', hx'⟩ := hsurj x
  have hx'' : (ι ≫ o) x' = y := by rw [Scheme.Hom.comp_apply, hx', hx]
  obtain ⟨Z', hxZ', hZ'fib, hZ'irr, hZ'cl, hdim⟩ :=
    main_integral (ι ≫ fX) fY (ι ≫ o) (by rw [Category.assoc, ho]) hy hx''
  refine ⟨ι '' Z', ⟨x', hxZ', hx'⟩, ?_, hZ'irr.image _ ι.continuous.continuousOn,
    ι.isClosedEmbedding.isClosedMap _ hZ'cl, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := hZ'fib hz
    rwa [Set.mem_preimage, Scheme.Hom.comp_apply] at this
  · have h1 : topologicalKrullDim X = topologicalKrullDim Xr :=
      (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm
    have h2 : topologicalKrullDim Z' ≤ topologicalKrullDim (ι '' Z') :=
      topologicalKrullDim_le_of_isEmbedding_image hemb Z' _ le_rfl
    have h3 : closure (Set.range (ι ≫ o)) = closure (Set.range o) := by
      congr 1
      ext z
      simp only [Set.mem_range, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨w, rfl⟩
        obtain ⟨w', rfl⟩ := hsurj w
        exact ⟨w', rfl⟩
    rw [h1, ← h3]
    exact hdim.trans (add_le_add h2 le_rfl)

end Reduction

end FibreDimension

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) :=
  FibreDimension.main fX fY o ho hy hx

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

open _root_.AlgebraicGeometry
namespace AffineDimension
open _root_.AlgebraicGeometry

open SchemeTheory.LocalDimension.FibreDimension

variable {k : Type u} [Field k]

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  refine le_antisymm (topologicalKrullDim_le_ringKrullDim f hU hUne) ?_
  rw [← topologicalKrullDim_affineOpen hU]
  exact topologicalKrullDim_subspace_le X (U : Set X)

end AffineDimension

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) :=
  AffineDimension.main f hU hUne

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

open _root_.AlgebraicGeometry
namespace GenericFibre
open _root_.AlgebraicGeometry

variable {k : Type u} [Field k]

theorem chart_isNoetherianRing {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X, U) := by
  let algKU : Algebra k Γ(X, U) := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := chart_finiteType f hU
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U)

section Generic

variable {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))

theorem exists_isGenericPoint [UniversallyOpen f] [GeometricallyIrreducible f] [Flat f] (w : P) :
    ∃ ζ : ↥(pullback f p),
      IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)) ∧
      (pullback.snd f p).base ζ = w := by
  set g := pullback.snd f p with hg
  have hT : IsIrreducible ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    g.isIrreducible_preimage g.isOpenMap isIrreducible_singleton.closure
  have hTc : IsClosed ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    isClosed_closure.preimage g.continuous
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hT hTc
  refine ⟨ζ, hζ, ?_⟩
  have hζT : ζ ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hζ.mem
  have hwy : w ⤳ g.base ζ := specializes_iff_mem_closure.mpr hζT
  have hgen : GeneralizingMap g := Flat.generalizingMap g
  obtain ⟨ζ', hζ'ζ, hζ'w⟩ := hgen hwy
  have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := by
    change g.base ζ' ∈ closure ({w} : Set P)
    rw [hζ'w]; exact subset_closure rfl
  have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
  have : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq
  rw [← this]; exact hζ'w

end Generic

section Heights

variable {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))

theorem height_eq [Flat f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P)
    (ζ : ↥(pullback f p))
    (hζ : IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)))
    (hζw : (pullback.snd f p).base ζ = w)
    {V : P.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V)
    {U : (pullback f p).Opens} (hU : IsAffineOpen U) (hζU : ζ ∈ U)
    (hUV : U ≤ (pullback.snd f p) ⁻¹ᵁ V) :
    (hU.primeIdealOf ⟨ζ, hζU⟩).asIdeal.height = (hV.primeIdealOf ⟨w, hwV⟩).asIdeal.height := by
  set g : pullback f p ⟶ P := pullback.snd f p with hg
  let φ : Γ(P, V) →+* Γ(pullback f p, U) := (g.appLE V U hUV).hom
  have hφ : φ.Flat :=
    HasRingHomProperty.appLE @Flat g (inferInstance : Flat g) ⟨V, hV⟩ ⟨U, hU⟩ hUV
  let : Algebra Γ(P, V) Γ(pullback f p, U) := φ.toAlgebra
  have : Module.Flat Γ(P, V) Γ(pullback f p, U) := hφ
  have : Algebra.HasGoingDown Γ(P, V) Γ(pullback f p, U) := inferInstance
  have : IsNoetherianRing Γ(P, V) := chart_isNoetherianRing p hV
  have : IsNoetherianRing Γ(pullback f p, U) := chart_isNoetherianRing (pullback.fst f p ≫ f) hU
  set Q : PrimeSpectrum Γ(pullback f p, U) := hU.primeIdealOf ⟨ζ, hζU⟩ with hQ
  set pw : PrimeSpectrum Γ(P, V) := hV.primeIdealOf ⟨w, hwV⟩ with hpw
  have hcomap : ∀ q : PrimeSpectrum Γ(pullback f p, U),
      hV.fromSpec (PrimeSpectrum.comap φ q) = g.base (hU.fromSpec q) := by
    intro q
    exact congrArg
      (fun h : Spec Γ(pullback f p, U) ⟶ P => h (q : Spec Γ(pullback f p, U)))
      (IsAffineOpen.SpecMap_appLE_fromSpec g hV hU hUV)
  have hmemU : ∀ q : PrimeSpectrum Γ(pullback f p, U), hU.fromSpec q ∈ U := fun q => by
    have := hU.range_fromSpec ▸ Set.mem_range_self (f := hU.fromSpec) q
    exact this
  have hmemV : ∀ q : PrimeSpectrum Γ(P, V), hV.fromSpec q ∈ V := fun q => by
    have := hV.range_fromSpec ▸ Set.mem_range_self (f := hV.fromSpec) q
    exact this
  have hζQ : hU.fromSpec Q = ζ := hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩
  have hwpw : hV.fromSpec pw = w := hV.fromSpec_primeIdealOf ⟨w, hwV⟩
  have hunder : PrimeSpectrum.comap φ Q = pw := by
    have h1 : hV.fromSpec (PrimeSpectrum.comap φ Q) = w := by rw [hcomap, hζQ, hζw]
    have h2 := primeIdealOf_fromSpec hV (PrimeSpectrum.comap φ Q) (hmemV _)
    rw [← h2]
    have : (⟨hV.fromSpec (PrimeSpectrum.comap φ Q), hmemV _⟩ : V) = ⟨w, hwV⟩ := Subtype.ext h1
    rw [this]
  have hlies : Q.asIdeal.LiesOver pw.asIdeal := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    have := congrArg PrimeSpectrum.asIdeal hunder
    have h__af := this.symm
    change pw.asIdeal = Q.asIdeal.comap φ at h__af
    exact h__af
  have hmin : ∀ Q' : PrimeSpectrum Γ(pullback f p, U), pw.asIdeal.map φ ≤ Q'.asIdeal → Q' ≤ Q → Q' =
      Q := by
    intro Q' hJ hle
    set ζ' : ↥(pullback f p) := hU.fromSpec Q' with hζ'
    have hζ'ζ : ζ' ⤳ ζ := by
      have := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
      rwa [hζQ] at this
    have hpw' : pw ≤ PrimeSpectrum.comap φ Q' := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal, ←
          Ideal.map_le_iff_le_comap]
      exact hJ
    have hgζ' : g.base ζ' ∈ closure ({w} : Set P) := by
      have := ((PrimeSpectrum.le_iff_specializes _ _).mp hpw').map hV.fromSpec.continuous
      rw [hwpw, hcomap] at this
      exact specializes_iff_mem_closure.mp this
    have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hgζ'
    have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
    have heq : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq
    have h1 := primeIdealOf_fromSpec hU Q' (hmemU _)
    rw [← h1]
    have : (⟨hU.fromSpec Q', hmemU _⟩ : U) = ⟨ζ, hζU⟩ := Subtype.ext heq
    rw [this]
  set J : Ideal Γ(pullback f p, U) := pw.asIdeal.map (algebraMap Γ(P, V) Γ(pullback f p, U)) with
      hJdef
  have hJφ : J = pw.asIdeal.map φ := rfl
  have hJQ : J ≤ Q.asIdeal := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    exact le_of_eq (hlies.over.symm ▸ rfl)
  have hfib : (Q.asIdeal.map (Ideal.Quotient.mk J)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    have hQm : (Q.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨hQm, bot_le⟩, ?_⟩
    rintro q' ⟨hq', -⟩ hq'le
    have : q'.IsPrime := hq'
    let Q' : PrimeSpectrum Γ(pullback f p, U) := ⟨q'.comap (Ideal.Quotient.mk J), inferInstance⟩
    have hJQ' : pw.asIdeal.map φ ≤ Q'.asIdeal := by
      change J ≤ q'.comap (Ideal.Quotient.mk J)
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q'.zero_mem
    have hQ'Q : Q' ≤ Q := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal]
      change q'.comap (Ideal.Quotient.mk J) ≤ Q.asIdeal
      intro x hx
      rw [Ideal.mem_comap] at hx
      have hx' : Ideal.Quotient.mk J x ∈ Q.asIdeal.map (Ideal.Quotient.mk J) := hq'le hx
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rw [Ideal.Quotient.eq, ← neg_sub] at hyx
      have hxy : x - y ∈ Q.asIdeal := hJQ ((neg_mem_iff).mp hyx)
      have := Q.asIdeal.add_mem hxy hy
      simpa only [sub_add_cancel] using this
    have hEq : Q' = Q := hmin Q' hJQ' hQ'Q
    have hq'eq : q' = Q.asIdeal.map (Ideal.Quotient.mk J) := by
      have h1 : q' = (q'.comap (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk J) :=
        (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q').symm
      rw [h1]
      change Q'.asIdeal.map _ = _
      rw [hEq]
    exact le_of_eq hq'eq.symm
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown pw.asIdeal Q.asIdeal
  rw [hfib, add_zero] at hgd
  exact hgd

end Heights

theorem main {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) := by
  have : Flat f := inferInstance
  have : UniversallyOpen f := inferInstance
  obtain ⟨ζ, hζ, hζw⟩ := exists_isGenericPoint f p w
  refine ⟨ζ, hζ, hζw, ?_⟩
  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := w) (U := ⊤) trivial
  have hζV : ζ ∈ (pullback.snd f p) ⁻¹ᵁ V := by
    change (pullback.snd f p).base ζ ∈ V
    rw [hζw]; exact hwV
  obtain ⟨U, hU, hζU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := pullback f p) (x := ζ) (U := (pullback.snd f p) ⁻¹ᵁ V)
        hζV
  rw [ringKrullDim_stalk_eq_height hU ζ hζU, ringKrullDim_stalk_eq_height hV w hwV,
    height_eq f p w ζ hζ hζw hV hwV hU hζU hUV]

end GenericFibre

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) :=
  GenericFibre.main f p w

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

open _root_.AlgebraicGeometry
namespace CodimFormula

open SchemeTheory.LocalDimension.FibreDimension
open _root_.AlgebraicGeometry

theorem eq_sub_of_natCast_add_eq (h n : ℕ) (d : WithBot ℕ∞)
    (hd : (h : WithBot ℕ∞) + d = n) : d = ((n - h : ℕ) : WithBot ℕ∞) ∧ h ≤ n := by
  induction d using WithBot.recBotCoe with
  | bot =>
    have hfalse : (⊥ : WithBot ℕ∞) = (n : ℕ∞) := (WithBot.add_bot _).symm.trans hd
    exact False.elim (WithBot.bot_ne_coe hfalse)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((h : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hd
      rw [← WithBot.coe_add, WithBot.coe_inj] at h1
      rw [add_top] at h1
      exact ENat.top_ne_natCast n h1
    | coe m =>
      have h1 : ((h : ℕ∞) : WithBot ℕ∞) + ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hd
      rw [← WithBot.coe_add, WithBot.coe_inj] at h1
      have h2 : h + m = n := by exact_mod_cast h1
      refine ⟨?_, by omega⟩
      have : m = n - h := by omega
      subst this
      rfl

section Charts

variable {k : Type u} [Field k]

theorem
 chart_numbers {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ∃ n h : ℕ, h ≤ n ∧ topologicalKrullDim X = n ∧
      ringKrullDim (X.presheaf.stalk x) = h ∧
      topologicalKrullDim (PrimeSpectrum.zeroLocus
        (((hU.primeIdealOf ⟨x, hx⟩).asIdeal : Ideal Γ(X, U)) : Set Γ(X, U))) = ((n - h : ℕ) :
            WithBot ℕ∞) := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  let algKU : Algebra k Γ(X, U) := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := chart_finiteType f hU
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  set p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hx⟩ with hp
  have hX : topologicalKrullDim X = ringKrullDim Γ(X, U) :=
    AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral f hU ⟨x, hx⟩
  have hdf := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k p.asIdeal
  have hfin : p.asIdeal.height ≠ ⊤ := by
    have : p.asIdeal.FiniteHeight := inferInstance
    exact Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k (A := Γ(X, U))
  rw [hn, ← hh] at hdf
  obtain ⟨hquot, hle⟩ := eq_sub_of_natCast_add_eq h n _ hdf
  refine ⟨n, h, hle, hX.trans hn, ?_, ?_⟩
  · rw [ringKrullDim_stalk_eq_height hU x hx, ← hh]
    rfl
  · rw [topologicalKrullDim_zeroLocus, hquot]

theorem
 fromSpec_mem_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : PrimeSpectrum Γ(X, U)) (hq : hU.primeIdealOf ⟨x, hx⟩ ≤ q) :
    hU.fromSpec q ∈ closure ({x} : Set X) := by
  have hs : hU.primeIdealOf ⟨x, hx⟩ ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hq
  have hs' := hs.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at hs'
  exact specializes_iff_mem_closure.mp hs'

theorem
 primeIdealOf_le_of_mem_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x
    ∈ U)
    (c : X) (hcU : c ∈ U) (hc : c ∈ closure ({x} : Set X)) :
    hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨c, hcU⟩ := by
  rw [PrimeSpectrum.le_iff_specializes]
  refine (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp ?_
  have e1 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨c, hcU⟩
  have hs : x ⤳ c := specializes_iff_mem_closure.mpr hc
  convert hs using 1

theorem
 zeroLocus_le_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus
        (((hU.primeIdealOf ⟨x, hx⟩).asIdeal : Ideal Γ(X, U)) : Set Γ(X, U))) ≤
      topologicalKrullDim (closure ({x} : Set X)) := by
  refine topologicalKrullDim_le_of_isEmbedding_image hU.fromSpec.isOpenEmbedding.isEmbedding _ _ ?_
  rintro _ ⟨q, hq, rfl⟩
  refine fromSpec_mem_closure hU x hx q ?_
  exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hq

theorem
 closure_le {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType
    f]
    (x : X) (n h : ℕ) (hXn : topologicalKrullDim X = n)
    (hxh : ringKrullDim (X.presheaf.stalk x) = h) :
    topologicalKrullDim (closure ({x} : Set X)) ≤ ((n - h : ℕ) : WithBot ℕ∞) := by
  have hclosed : IsClosedEmbedding (Subtype.val : closure ({x} : Set X) → X) :=
    isClosed_closure.isClosedEmbedding_subtypeVal
  have : QuasiSober (closure ({x} : Set X)) := hclosed.quasiSober
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding _ fun c => ?_
  obtain ⟨U', hU', hcU', -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := c.1) (U := ⊤) trivial
  have hxU' : x ∈ U' := by
    obtain ⟨y, hyU', hyx⟩ := mem_closure_iff.mp c.2 U' U'.isOpen hcU'
    rw [Set.mem_singleton_iff] at hyx
    rwa [hyx] at hyU'
  set p' : PrimeSpectrum Γ(X, U') := hU'.primeIdealOf ⟨x, hxU'⟩ with hp'
  let Z : Set (PrimeSpectrum Γ(X, U')) := PrimeSpectrum.zeroLocus ((p'.asIdeal : Ideal Γ(X, U')) :
      Set Γ(X, U'))
  let g : Z → closure ({x} : Set X) := fun q =>
    ⟨hU'.fromSpec q.1, fromSpec_mem_closure hU' x hxU' q.1
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp q.2)⟩
  have hgemb : IsEmbedding g :=
    ((hU'.fromSpec.isOpenEmbedding.isEmbedding).comp IsEmbedding.subtypeVal).codRestrict _ _
  have hrange : Set.range g = Subtype.val ⁻¹' (U' : Set X) := by
    ext c'
    constructor
    · rintro ⟨q, rfl⟩
      change hU'.fromSpec q.1 ∈ (U' : Set X)
      have := hU'.range_fromSpec ▸ Set.mem_range_self (f := hU'.fromSpec) q.1
      exact this
    · intro hc'
      refine ⟨⟨hU'.primeIdealOf ⟨c'.1, hc'⟩, ?_⟩, ?_⟩
      · change hU'.primeIdealOf ⟨c'.1, hc'⟩ ∈ PrimeSpectrum.zeroLocus _
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
        exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
          (primeIdealOf_le_of_mem_closure hU' x hxU' c'.1 hc' c'.2)
      · apply Subtype.ext
        exact hU'.fromSpec_primeIdealOf ⟨c'.1, hc'⟩
  have hopen : IsOpen (Set.range g) := by
    rw [hrange]
    exact U'.isOpen.preimage continuous_subtype_val
  have hg : IsOpenEmbedding g := ⟨hgemb, hopen⟩
  have hcg : c ∈ Set.range g := by rw [hrange]; exact hcU'
  refine ⟨Z, inferInstance, g, hg, hcg, ?_⟩
  obtain ⟨n', h', -, hXn', hxh', hZ⟩ := chart_numbers f hU' x hxU'
  have hn : n' = n := by
    have := hXn'.symm.trans hXn
    exact_mod_cast this
  have hh : h' = h := by
    have := hxh'.symm.trans hxh
    exact_mod_cast this
  subst hn hh
  exact hZ.le

theorem
 main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType f]
    (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨n, h, hle, hXn, hxh, hZ⟩ := chart_numbers f hU x hxU
  have hC : topologicalKrullDim (closure ({x} : Set X)) = ((n - h : ℕ) : WithBot ℕ∞) :=
    le_antisymm (closure_le f x n h hXn hxh) (hZ ▸ zeroLocus_le_closure hU x hxU)
  rw [hxh, hC, hXn]
  have : h + (n - h) = n := by omega
  exact_mod_cast this

end Charts

end CodimFormula

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X :=
  CodimFormula.main f x

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem topologicalKrullDim_eq_of_iso_opens
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) (U' : Y.Opens) (hU : (U : Set X).Nonempty) (e : (U : Scheme.{u}) ≅ (U' :
        Scheme.{u})) :
    topologicalKrullDim ↥X = topologicalKrullDim ↥Y := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (U : Scheme.{u}).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (⟨x, hx⟩ : ↥U))
      isOpen_univ
  have hVX : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hVU' : IsAffineOpen (e.hom ''ᵁ V) := hV.image_of_isOpenImmersion e.hom
  have hVY : IsAffineOpen (U'.ι ''ᵁ (e.hom ''ᵁ V)) := hVU'.image_of_isOpenImmersion U'.ι
  have hneX : ((U.ι ''ᵁ V : X.Opens) : Set X).Nonempty := ⟨_, ⟨_, hxV, rfl⟩⟩
  have hneY : ((U'.ι ''ᵁ (e.hom ''ᵁ V) : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨e.hom ⟨x, hx⟩, ⟨_, hxV, rfl⟩, rfl⟩⟩
  let ε : Γ(X, U.ι ''ᵁ V) ≅ Γ(Y, U'.ι ''ᵁ (e.hom ''ᵁ V)) :=
    U.ι.appIso V ≪≫ (e.hom.appIso V).symm ≪≫ (U'.ι.appIso _).symm
  rw [AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fX hVX
      hneX,
    AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fY hVY hneY]
  exact ringKrullDim_eq_of_ringEquiv ε.commRingCatIsoToRingEquiv

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ResidueDimension

open Topology

theorem chart_top {X : Scheme.{u}} {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) :
    ∃ g : PrimeSpectrum (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) → ↥(closure ({x} : Set X)),
      IsOpenEmbedding g ∧ ∀ z : ↥(closure ({x} : Set X)), z.1 ∈ (U : Set X) → z ∈ Set.range g := by
  have hmk : Function.Surjective (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :=
    Ideal.Quotient.mk_surjective
  have hc : IsClosedEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hmk
  have hcr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal))
      =
      closure {hU.primeIdealOf ⟨x, hxU⟩} := by
    rw [range_comap_of_surjective _ _ hmk, Ideal.mk_ker,
      ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  have hF : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have hFq : hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hg₀ : IsEmbedding (hU.fromSpec.base ∘
      PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) :=
    hF.isEmbedding.comp hc.isEmbedding
  have hfwd : ∀ p, (hU.fromSpec.base ∘
      PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈
        closure ({x} : Set X) ∧
      (hU.fromSpec.base ∘
        PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈ (U : Set X)
            := by
    intro p
    refine ⟨?_, ?_⟩
    · have hle : hU.primeIdealOf ⟨x, hxU⟩ ≤
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p := by
        intro a ha
        change Ideal.Quotient.mk _ a ∈ p.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact p.asIdeal.zero_mem
      have hsp : hU.primeIdealOf ⟨x, hxU⟩ ⤳
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p :=
        (PrimeSpectrum.le_iff_specializes _ _).mp hle
      have hsp' : hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) ⤳ hU.fromSpec.base
          (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p) :=
        hsp.map hU.fromSpec.continuous
      rw [hFq] at hsp'
      exact specializes_iff_mem_closure.mp hsp'
    · have : (hU.fromSpec.base ∘
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈
          Set.range hU.fromSpec.base := ⟨_, rfl⟩
      rwa [hU.range_fromSpec] at this
  have hbwd : ∀ y : X, y ∈ closure ({x} : Set X) → y ∈ (U : Set X) →
      y ∈ Set.range (hU.fromSpec.base ∘
        PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) := by
    intro y hy hyU
    rw [← hU.range_fromSpec] at hyU
    obtain ⟨p, rfl⟩ := hyU
    have hsp : x ⤳ hU.fromSpec.base p := specializes_iff_mem_closure.mpr hy
    rw [← hFq] at hsp
    have hsp' : hU.primeIdealOf ⟨x, hxU⟩ ⤳ p := hF.isEmbedding.isInducing.specializes_iff.mp hsp
    have hp : p ∈ Set.range
        (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) := by
      rw [hcr]; exact specializes_iff_mem_closure.mp hsp'
    obtain ⟨p', rfl⟩ := hp
    exact ⟨p', rfl⟩
  refine ⟨fun p => ⟨_, (hfwd p).1⟩, ⟨(IsEmbedding.subtypeVal.of_comp_iff).mp hg₀, ?_⟩, ?_⟩
  · have hrange : Set.range (fun p => (⟨_, (hfwd p).1⟩ : ↥(closure ({x} : Set X)))) =
        Subtype.val ⁻¹' (U : Set X) := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact (hfwd p).2
      · intro hz
        obtain ⟨p, hp⟩ := hbwd z.1 z.2 hz
        exact ⟨p, Subtype.ext hp⟩
    rw [hrange]
    exact U.isOpen.preimage continuous_subtype_val
  · intro z hz
    obtain ⟨p, hp⟩ := hbwd z.1 z.2 hz
    exact ⟨p, Subtype.ext hp⟩

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The residue-field algebra induced by the structure morphism. -/
noncomputable abbrev resAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue
      x).hom.toAlgebra

theorem chart_alg [LocallyOfFiniteType f] {x : X} {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    letI := resAlgebra f x
    ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) := by
  let : Algebra k (X.residueField x) := resAlgebra f x
  let : Algebra k Γ(X, U) := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := chart_finiteType f hU
  let algSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hev : ∀ a : k, (X.evaluation U x hxU).hom (algebraMap k Γ(X, U) a) = algebraMap k
      (X.residueField x) a := by
    intro a
    exact congrArg (fun z : X.presheaf.stalk x => X.residue x z)
      (X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hxU
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))
  have hker : RingHom.ker (X.evaluation U x hxU).hom = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    ext a
    rw [RingHom.mem_ker]
    change (X.residue x).hom ((X.presheaf.germ U x hxU).hom a) = 0 ↔ _
    exact (IsLocalRing.residue_eq_zero_iff _).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal a)
  rw [← hker]
  have hprime : (RingHom.ker (X.evaluation U x hxU).hom).IsPrime := RingHom.ker_isPrime _
  let algQ : Algebra (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) :=
    (RingHom.kerLift (X.evaluation U x hxU).hom).toAlgebra
  have : IsScalarTower k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [← Ideal.Quotient.mk_algebraMap,
      RingHom.algebraMap_toAlgebra (RingHom.kerLift (X.evaluation U x hxU).hom), RingHom.kerLift_mk]
    exact (hev a).symm
  have : FaithfulSMul (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective _)
  have : FaithfulSMul k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k _).injective
  have : Algebra.IsAlgebraic (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x)
      := by
    refine ⟨fun z => ?_⟩
    obtain ⟨s, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl s
    have ht : (X.evaluation U x hxU).hom t ≠ 0 := by
      intro h0
      have : (t : Γ(X, U)) ∈ RingHom.ker (X.evaluation U x hxU).hom := h0
      rw [hker] at this
      exact t.2 this
    have hz : (X.residue x).hom s * (X.evaluation U x hxU).hom t = (X.evaluation U x hxU).hom a
        := by
      change (X.residue x).hom s * (X.residue x).hom ((X.presheaf.germ U x hxU).hom t) =
        (X.residue x).hom ((X.presheaf.germ U x hxU).hom a)
      rw [← map_mul]
      exact congrArg _ hat
    have hz' : (X.residue x).hom s =
        algebraMap (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x)
            (Ideal.Quotient.mk _ a) *
          (algebraMap (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x)
              (Ideal.Quotient.mk _ t))⁻¹ := by
      rw [RingHom.algebraMap_toAlgebra, RingHom.kerLift_mk, RingHom.kerLift_mk,
        eq_mul_inv_iff_mul_eq₀ ht, hz]
    rw [hz']
    exact (isAlgebraic_algebraMap _).mul (isAlgebraic_algebraMap _).inv
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom)
  have hs' := hs.algebraMap_comp (A := X.residueField x)
  rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x
      hxU).hom),
    ← hs.cardinalMk_eq_trdeg, ← hs'.cardinalMk_eq_trdeg]

theorem main [LocallyOfFiniteType f] (x : X) :
    letI := resAlgebra f x
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) := by
  let : Algebra k (X.residueField x) := resAlgebra f x
  have : QuasiSober ↥(closure ({x} : Set X)) :=
    (isClosed_closure.isClosedEmbedding_subtypeVal).quasiSober
  apply le_antisymm
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    obtain ⟨g, hg, -⟩ := chart_top hU hxU
    rw [← chart_alg f hU hxU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact Topology.IsInducing.topologicalKrullDim_le hg.isEmbedding.isInducing
  · refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding _ fun z => ?_
    obtain ⟨U, hU, hzU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := z.1) (U := ⊤) trivial
    have hxU : x ∈ U := by
      obtain ⟨y, hyU, hyx⟩ := mem_closure_iff.mp z.2 U U.isOpen hzU
      rw [Set.mem_singleton_iff] at hyx
      exact hyx ▸ hyU
    obtain ⟨g, hg, hrg⟩ := chart_top hU hxU
    refine ⟨_, inferInstance, g, hg, hrg z hzU, ?_⟩
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, chart_alg f hU hxU]

end Chart

end ResidueDimension

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem toENat_trdeg_residueField_eq_topologicalKrullDim_closure
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue
          x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) :=
  ResidueDimension.main f x

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalDimension

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Topology
open _root_.IsLocalRing
open _root_.HomogeneousLocalization

universe u

noncomputable section

open _root_.AlgebraicGeometry
namespace ValuationModel

attribute [local instance] MvPolynomial.gradedAlgebra
open _root_.AlgebraicGeometry

section Eval

variable {R : CommRingCat.{u}} {Z : Scheme.{u}}

/-- Evaluation on a chart through a morphism from an affine scheme. -/
def ev (u : Spec R ⟶ Z) (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) : Γ(Z, V) →+* R :=
  (Scheme.ΓSpecIso R).hom.hom.comp (u.appLE V ⊤ h).hom

lemma ev_apply (u : Spec R ⟶ Z) (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) (x : Γ(Z, V)) :
    ev u V h x = (Scheme.ΓSpecIso R).hom (u.appLE V ⊤ h x) := rfl

lemma ev_map (u : Spec R ⟶ Z) {V V' : Z.Opens} (i : V ≤ V') (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V)
    (h' : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V') (x : Γ(Z, V')) :
    ev u V h (Z.presheaf.map (homOfLE i).op x) = ev u V' h' x := by
  simp only [ev_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

lemma appLE_congr_hom {X Y : Scheme.{u}} {u u' : X ⟶ Y} (e : u = u') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ u ⁻¹ᵁ V) : u.appLE V W h = u'.appLE V W (e ▸ h) :=
  _root_.AlgebraicGeometry.Scheme.Hom.appLE_congr_hom e V W h (e ▸ h)

lemma ev_comp {Z' : Scheme.{u}} (v : Spec R ⟶ Z') (w : Z' ⟶ Z) (V : Z.Opens)
    (h : (⊤ : (Spec R).Opens) ≤ (v ≫ w) ⁻¹ᵁ V) (x : Γ(Z, V)) :
    ev (v ≫ w) V h x = ev v (w ⁻¹ᵁ V) h (w.app V x) := by
  exact congrArg
    (fun q : Γ(Z, V) ⟶ Γ(Spec R, ⊤) => (Scheme.ΓSpecIso R).hom (q x))
    (Scheme.Hom.comp_appLE v w V ⊤ h)

lemma ev_specMap_top {A : CommRingCat.{u}} (φ : A ⟶ R) (a : A) :
    ev (Spec.map φ) ⊤ le_top ((Scheme.ΓSpecIso A).inv a) = φ a := by
  have hmap : (Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop ≫
      (Scheme.ΓSpecIso R).hom = φ := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact (congrArg
    (fun q : Γ(Spec A, ⊤) ⟶ Γ(Spec R, ⊤) =>
      (Scheme.ΓSpecIso R).hom (q ((Scheme.ΓSpecIso A).inv a)))
    (appLE_top_top (Spec.map φ) le_top)).trans (congrArg (fun q : A ⟶ R => q a) hmap)

lemma primeIdealOf_eq_comap_ev [IsLocalRing R] (u : Spec R ⟶ Z) {V : Z.Opens} (hV : IsAffineOpen V)
    (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V) :
    (hV.primeIdealOf ⟨u (closedPoint R), h (Opens.mem_top _)⟩).asIdeal =
      Ideal.comap (ev u V h) (maximalIdeal R) := by
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := u) (x := closedPoint R) V hV ⊤
    (isAffineOpen_top (Spec R)) h (Opens.mem_top _)
  rw [← h1]
  let x : Spec R := closedPoint R
  have : IsLocalRing ((Spec R).presheaf.stalk x) := inferInstance
  have h2 : ((isAffineOpen_top (Spec R)).primeIdealOf ⟨closedPoint R, Opens.mem_top _⟩) =
      PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom (closedPoint R) := by
    rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
    change Spec.map ((Spec R).presheaf.germ ⊤ (closedPoint R) trivial) _ = _
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv R, Spec.map_comp]
    change PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom
      (Spec.map (stalkClosedPointIso R).inv
        (closedPoint ((Spec R).presheaf.stalk x))) = _
    apply congrArg (PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom)
    exact (congrArg
      (fun q : Spec ((Spec R).presheaf.stalk x) ⟶ Spec R =>
        q (closedPoint ((Spec R).presheaf.stalk x)))
      (Spec_stalkClosedPointIso R)).trans Scheme.fromSpecStalk_closedPoint
  rw [h2]
  simp only [PrimeSpectrum.comap_asIdeal, ev, Ideal.comap_comap]
  rfl

lemma top_le_of_closedPoint_mem [IsLocalRing R] (u : Spec R ⟶ Z) (V : Z.Opens)
    (h : u (closedPoint R) ∈ V) : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V := by
  have : closedPoint R ∈ u ⁻¹ᵁ V := h
  rw [(IsLocalRing.closedPoint_mem_iff _).mp this]
  exact le_top

end Eval

section Sections

variable {P : Scheme.{u}} [IsIntegral P]

lemma exists_affine_sections {d : ℕ} (f : Fin d → P.functionField) :
    ∃ (U : P.Opens) (_hU : IsAffineOpen U) (hη : genericPoint P ∈ U) (g : Fin d → Γ(P, U)),
      ∀ i, P.presheaf.germ U (genericPoint P) hη (g i) = f i := by
  classical
  have hrep : ∀ i, ∃ (W : P.Opens) (hW : genericPoint P ∈ W) (t : Γ(P, W)),
      P.presheaf.germ W (genericPoint P) hW t = f i := fun i =>
    let ⟨W, hW, t, ht⟩ := P.presheaf.exists_germ_eq (x := genericPoint P) (f i)
    ⟨W, hW, t, ht⟩
  choose W hW t ht using hrep
  let W₀ : P.Opens := Finset.univ.inf W
  have hW₀ : genericPoint P ∈ W₀ := by
    change genericPoint P ∈ (Finset.univ.inf W : P.Opens)
    rw [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    exact Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun _ => hW i
  have hle : ∀ i, W₀ ≤ W i := fun i => Finset.inf_le (Finset.mem_univ i)
  obtain ⟨U, hU, hηU, hUW⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint P) (U := W₀) hW₀
  refine ⟨U, hU, hηU, fun i => P.presheaf.map (homOfLE ((hUW.trans (hle i)) : U ≤ W i)).op (t i),
      fun i => ?_⟩
  change P.presheaf.germ U (genericPoint P) hηU (P.presheaf.map (homOfLE _).op (t i)) = f i
  rw [TopCat.Presheaf.germ_res_apply P.presheaf]
  exact ht i

end Sections

section Chart

variable (k : Type u) [Field k] (d : ℕ)

/-- The standard grading defining the projective space used for compactification. -/
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k

/-- The projective space of the prescribed dimension. -/
abbrev PP : Scheme.{u} := Proj (grading k d)

/-- The distinguished standard affine chart of projective space. -/
abbrev Ad : Type u := Away (grading k d) (MvPolynomial.X (0 : Fin (d + 1)))

/-- The inclusion of the distinguished projective chart. -/
abbrev awayι₀ : Spec (.of (Ad k d)) ⟶ PP k d :=
  Proj.awayι (grading k d) (MvPolynomial.X 0) (ProjSpace.X_mem_one k d 0) one_pos

/-- The structure morphism of the chosen projective space. -/
abbrev πP : PP k d ⟶ Spec (.of k) := ProjSpace.π k d

variable {k d}
variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))

/-- The canonical map of constants into local sections. -/
def φk (U : P.Opens) : CommRingCat.of k ⟶ Γ(P, U) :=
  p.constToPresheaf.app (Opposite.op U)

lemma ι_comp_eq (U : P.Opens) (hU : IsAffineOpen U) :
    U.ι ≫ p = hU.isoSpec.hom ≫ Spec.map (φk p U) := by
  rw [φk, Scheme.Hom.constToPresheaf, ← IsAffineOpen.toSpecΓ_fromSpec hU, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]
  rfl

/-- The projective morphism defined by an algebra map on the affine chart. -/
def chartMor (U : P.Opens) (hU : IsAffineOpen U)
    (φ : letI := p.sectionsAlgebra U; Ad k d →ₐ[k] Γ(P, U)) : (U : Scheme.{u}) ⟶ PP k d :=
  letI := p.sectionsAlgebra U
  hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ awayι₀ k d

lemma chartMor_comp_π (U : P.Opens) (hU : IsAffineOpen U)
    (φ : letI := p.sectionsAlgebra U; Ad k d →ₐ[k] Γ(P, U)) :
    chartMor p U hU φ ≫ πP k d = U.ι ≫ p := by
  let : Algebra k Γ(P, U) := p.sectionsAlgebra U
  rw [chartMor, Category.assoc, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp, ι_comp_eq p
      U hU]
  congr 2
  ext x
  change φ.toRingHom (algebraMap k (Ad k d) x) = (φk p U) x
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end Chart

section KPoint

variable {P : Scheme.{u}} [IsIntegral P]

/-- The generic point factored through a nonempty affine chart. -/
def κ (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    Spec P.functionField ⟶ (U : Scheme.{u}) :=
  Spec.map (P.presheaf.germ U (genericPoint P) hη) ≫ hU.isoSpec.inv

@[reassoc]
lemma κ_ι (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    κ U hU hη ≫ U.ι = P.fromSpecStalk (genericPoint P) := by
  rw [κ, Category.assoc, IsAffineOpen.isoSpec_inv_ι, ← hU.fromSpecStalk_eq_fromSpecStalk hη]
  rfl

@[reassoc]
lemma κ_isoSpec_hom (U : P.Opens) (hU : IsAffineOpen U) (hη : genericPoint P ∈ U) :
    κ U hU hη ≫ hU.isoSpec.hom = Spec.map (P.presheaf.germ U (genericPoint P) hη) := by
  rw [κ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (O : ValuationSubring P.functionField)
  (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
  (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
    P.fromSpecStalk (genericPoint P))

include hℓ₀ in
lemma algebraMap_ev_ℓ₀ (V : P.Opens) (h : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ₀ ⁻¹ᵁ V)
    (hηV : genericPoint P ∈ V) (x : Γ(P, V)) :
    algebraMap O P.functionField (ev ℓ₀ V h x) = P.presheaf.germ V (genericPoint P) hηV x := by
  set ι : CommRingCat.of (O : Type u) ⟶ P.functionField := CommRingCat.ofHom (algebraMap O
      P.functionField)
  have hℓ₀' : Spec.map ι ≫ ℓ₀ = P.fromSpecStalk (genericPoint P) := hℓ₀
  have hK : (⊤ : (Spec P.functionField).Opens) ≤ (Spec.map ι ≫ ℓ₀) ⁻¹ᵁ V := by
    intro y _
    change ℓ₀ (Spec.map ι y) ∈ V
    exact h (Opens.mem_top _)
  have h1 : (Scheme.ΓSpecIso P.functionField).hom ((Spec.map ι ≫ ℓ₀).appLE V ⊤ hK x) =
      (Scheme.ΓSpecIso P.functionField).hom
        ((P.fromSpecStalk (genericPoint P)).appLE V ⊤ (hℓ₀' ▸ hK) x) := by
    rw [appLE_congr_hom hℓ₀']
  have h2 : (Spec.map ι ≫ ℓ₀).appLE V ⊤ hK x = (Spec.map ι).appTop (ℓ₀.appLE V ⊤ h x) := by
    have he := Scheme.Hom.appLE_comp_appLE (Spec.map ι) ℓ₀ V ⊤ ⊤ h le_top
    have ht := appLE_top_top (Spec.map ι) le_top
    exact (congrArg (fun q : Γ(P, V) ⟶ Γ(Spec P.functionField, ⊤) => q x) he).symm.trans
      (congrArg (fun q : Γ(Spec (.of O), ⊤) ⟶ Γ(Spec P.functionField, ⊤) =>
        q (ℓ₀.appLE V ⊤ h x)) ht)
  have h3 : (Scheme.ΓSpecIso P.functionField).hom ((Spec.map ι).appTop (ℓ₀.appLE V ⊤ h x)) =
      ι ((Scheme.ΓSpecIso (CommRingCat.of (O : Type u))).hom (ℓ₀.appLE V ⊤ h x)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
    rfl
  have h4 : (P.fromSpecStalk (genericPoint P)).appLE V ⊤ (hℓ₀' ▸ hK) x =
      (Scheme.ΓSpecIso P.functionField).inv (P.presheaf.germ V (genericPoint P) hηV x) := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hηV]
    simp only [Category.assoc, ← Functor.map_comp]
    have : (homOfLE (le_top : (P.fromSpecStalk (genericPoint P)) ⁻¹ᵁ V ≤ ⊤)).op ≫
        (homOfLE ((hℓ₀' ▸ hK) : (⊤ : (Spec P.functionField).Opens) ≤ (P.fromSpecStalk (genericPoint
            P)) ⁻¹ᵁ V)).op =
        𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [h2, h3, h4] at h1
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h1
  exact h1

end KPoint

section Constants

variable {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsIntegral P]

/-- The base field embedded into the function field. -/
def θ : k →+* P.functionField :=
  (P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

variable (O : ValuationSubring P.functionField) {d : ℕ} (f : Fin d → P.functionField)
  (hind : ∀ Q : MvPolynomial (Fin d) k,
    O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0)

include hind in
lemma θ_mem (c : k) : θ p c ∈ O := by
  by_contra hc
  have h1 : ¬ O.valuation (θ p c) ≤ 1 := fun h => hc ((O.valuation_le_one_iff _).mp h)
  have h2 : 1 < O.valuation (θ p c) := lt_of_not_ge h1
  have hc0 : θ p c ≠ 0 := by
    intro h0; rw [h0, map_zero] at h2; exact not_lt_of_ge zero_le_one h2
  have h3 : O.valuation (θ p c⁻¹) < 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_lt_one_of_one_lt₀ h2
  have h4 : (MvPolynomial.C c⁻¹ : MvPolynomial (Fin d) k) = 0 := by
    apply hind
    rw [MvPolynomial.eval₂_C]
    exact h3
  rw [MvPolynomial.C_eq_zero, inv_eq_zero] at h4
  exact hc0 (by rw [h4, map_zero])

/-- The constants regarded as elements of the chosen valuation subring. -/
def θO : k →+* O := (θ p).codRestrict O.toSubring (θ_mem p O f hind)

lemma algebraMap_θO (c : k) : algebraMap O P.functionField (θO p O f hind c) = θ p c := rfl

end Constants

section Aux

variable {R : CommRingCat.{u}} {Z : Scheme.{u}}

lemma ev_congr {u u' : Spec R ⟶ Z} (e : u = u') (V : Z.Opens) (h : (⊤ : (Spec R).Opens) ≤ u ⁻¹ᵁ V)
    (x : Γ(Z, V)) : ev u V h x = ev u' V (e ▸ h) x := by
  subst e; rfl

end Aux

section Main

variable {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  [IsIntegral P] [LocallyOfFiniteType p]
  (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
  (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
  (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
    P.fromSpecStalk (genericPoint P))
  (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
  (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
  (hind : ∀ Q : MvPolynomial (Fin d) k,
    O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0)

omit [LocallyOfFiniteType p] in
include hℓ₀ in
lemma ev_ℓ₀_p (h : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ (ℓ₀ ≫ p) ⁻¹ᵁ ⊤) (c : k) :
    ev (ℓ₀ ≫ p) ⊤ h ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = θO p O f hind c := by
  apply Subtype.ext
  change algebraMap O P.functionField _ = θ p c
  rw [ev_comp, algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ (p ⁻¹ᵁ ⊤) h trivial]
  rfl

include hO hℓ₀ hd hf hind in
theorem main :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 := by
  classical
  obtain ⟨U, hU, hη, g, hg⟩ := exists_affine_sections f
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have hUne : (U : Set P).Nonempty := ⟨_, hη⟩
  let algKU : Algebra k Γ(P, U) := p.sectionsAlgebra U
  let bU : Fin (d + 1) → Γ(P, U) := Fin.cons 1 g
  obtain ⟨φU, hφU⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq k d 0 bU (by rfl)
  let gU : (U : Scheme.{u}) ⟶ PP k d := chartMor p U hU φU
  have hgU : gU ≫ πP k d = U.ι ≫ p := chartMor_comp_π p U hU φU
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨P', β, s, g', hP'int, hβ, hs, hsβ, hrange, hsg', hg'π⟩ :=
    AlgebraicGeometry.exists_isProper_isOpenImmersion_range_eq_preimage_comp_eq_of_isProper
      p (πP k d) U hUne gU hgU
  let ιOK : CommRingCat.of (O : Type u) ⟶ P.functionField :=
    CommRingCat.ofHom (algebraMap O P.functionField)
  have hℓ₀' : Spec.map ιOK ≫ ℓ₀ = P.fromSpecStalk (genericPoint P) := hℓ₀
  have hprop : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) β := by
    rw [← IsProper.eq_valuativeCriterion]; exact hβ
  let sq : ValuativeCommSq β :=
    { R := O, K := P.functionField, i₁ := κ U hU hη ≫ s, i₂ := ℓ₀,
      commSq := ⟨by rw [Category.assoc, hsβ, κ_ι]; exact hℓ₀'.symm⟩ }
  obtain ⟨⟨⟨lift⟩, -⟩⟩ := hprop.1.1.1 sq
  let ℓ : Spec (CommRingCat.of O) ⟶ P' := lift.l
  have hℓK : Spec.map ιOK ≫ ℓ = κ U hU hη ≫ s := lift.fac_left
  have hℓβ : ℓ ≫ β = ℓ₀ := lift.fac_right
  let algKO : Algebra k O := (θO p O f hind).toAlgebra
  let bO : Fin (d + 1) → O := Fin.cons 1 (fun i => ⟨f i, hf i⟩)
  obtain ⟨φO, hφO⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq k d 0 bO (by rfl)
  let mO : Spec (CommRingCat.of O) ⟶ PP k d :=
    Spec.map (CommRingCat.ofHom φO.toRingHom) ≫ awayι₀ k d
  have hring : (algebraMap O P.functionField).comp φO.toRingHom =
      (P.presheaf.germ U (genericPoint P) hη).hom.comp φU.toRingHom := by
    let algKK : Algebra k P.functionField := (θ p).toAlgebra
    let F1 : Ad k d →ₐ[k] P.functionField :=
      { toRingHom := (algebraMap O P.functionField).comp φO.toRingHom
        commutes' := fun c => by
          change algebraMap O P.functionField (φO (algebraMap k (Ad k d) c)) = θ p c
          rw [AlgHom.commutes]
          rfl }
    let F2 : Ad k d →ₐ[k] P.functionField :=
      { toRingHom := (P.presheaf.germ U (genericPoint P) hη).hom.comp φU.toRingHom
        commutes' := fun c => by
          change P.presheaf.germ U (genericPoint P) hη (φU (algebraMap k (Ad k d) c)) = θ p c
          rw [AlgHom.commutes]
          change P.presheaf.germ U (genericPoint P) hη
            (P.presheaf.map (homOfLE le_top).op (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
                c))) = _
          rw [TopCat.Presheaf.germ_res_apply P.presheaf]
          rfl }
    have hF : F1 = F2 := by
      refine AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio k d 0) ?_
      rintro _ ⟨j, rfl⟩
      change algebraMap O P.functionField (φO (ProjSpace.ratio k d 0 j)) =
        P.presheaf.germ U (genericPoint P) hη (φU (ProjSpace.ratio k d 0 j))
      rw [hφO, hφU]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [bO, bU, Fin.cons_zero, map_one]
      · simp only [bO, bU, Fin.cons_succ]
        exact (hg i).symm
    exact congrArg AlgHom.toRingHom hF
  have hsqP : CommSq (κ U hU hη ≫ gU) (Spec.map ιOK) (πP k d) (ℓ₀ ≫ p) :=
    ⟨by rw [Category.assoc, hgU, ← Category.assoc, κ_ι, ← hℓ₀', Category.assoc]⟩
  have hmO_left : Spec.map ιOK ≫ mO = κ U hU hη ≫ gU := by
    change Spec.map ιOK ≫ Spec.map _ ≫ awayι₀ k d =
      κ U hU hη ≫ (hU.isoSpec.hom ≫ Spec.map _ ≫ awayι₀ k d)
    rw [κ_isoSpec_hom_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext1
    exact hring
  have hmO_right : mO ≫ πP k d = ℓ₀ ≫ p := by
    change (Spec.map _ ≫ awayι₀ k d) ≫ πP k d = ℓ₀ ≫ p
    rw [Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
    refine ext_of_isAffine ?_
    have key : ∀ c : k, (Scheme.ΓSpecIso (CommRingCat.of O)).hom
        ((ℓ₀ ≫ p).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = θO p O f hind c := by
      intro c
      rw [← appLE_top_top (ℓ₀ ≫ p) le_top]
      exact ev_ℓ₀_p p O ℓ₀ hℓ₀ d f hind le_top c
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of O)).hom, Category.assoc, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
    apply CommRingCat.hom_ext
    refine RingHom.ext fun c => ?_
    change φO.toRingHom (algebraMap k (Ad k d) c) =
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom ((ℓ₀ ≫ p).appTop ((Scheme.ΓSpecIso (CommRingCat.of
          k)).inv c))
    rw [key c, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hℓg' : ℓ ≫ g' = mO := by
    let sqP : ValuativeCommSq (πP k d) :=
      { R := O, K := P.functionField, i₁ := κ U hU hη ≫ gU, i₂ := ℓ₀ ≫ p, commSq := hsqP }
    have hsub : Subsingleton sqP.commSq.LiftStruct := IsSeparated.valuativeCriterion (πP k d) sqP
    let L1 : sqP.commSq.LiftStruct :=
      ⟨ℓ ≫ g', by
        change Spec.map ιOK ≫ ℓ ≫ g' = κ U hU hη ≫ gU
        rw [← Category.assoc, hℓK, Category.assoc, hsg'], by
        change (ℓ ≫ g') ≫ πP k d = ℓ₀ ≫ p
        rw [Category.assoc, hg'π, ← Category.assoc, hℓβ]⟩
    let L2 : sqP.commSq.LiftStruct := ⟨mO, hmO_left, hmO_right⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim L1 L2)
  let W0 : (PP k d).Opens := (awayι₀ k d) ''ᵁ ⊤
  let r : Fin (d + 1) → Γ(PP k d, W0) := fun j =>
    ((awayι₀ k d).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (Ad k d))).inv (ProjSpace.ratio k
        d 0 j))
  let V0 : P'.Opens := g' ⁻¹ᵁ W0
  let t : Fin (d + 1) → Γ(P', V0) := fun j => g'.app W0 (r j)
  let xO : Spec (CommRingCat.of O) := closedPoint O
  let y' : P' := ℓ xO
  have hy'V0 : y' ∈ V0 := by
    change g' (ℓ xO) ∈ W0
    rw [← Scheme.Hom.comp_apply, hℓg']
    change awayι₀ k d (Spec.map (CommRingCat.ofHom φO.toRingHom) xO) ∈ (awayι₀ k d) ''ᵁ
        ⊤
    exact ⟨_, trivial, rfl⟩
  have hV0top : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ ⁻¹ᵁ V0 := top_le_of_closedPoint_mem ℓ V0
      hy'V0
  have ht : ∀ j, ev ℓ V0 hV0top (t j) = bO j := by
    intro j
    have e1 : ev ℓ V0 hV0top (t j) = ev (ℓ ≫ g') W0 hV0top (r j) := (ev_comp ℓ g' W0 hV0top (r
        j)).symm
    have hmap : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤
        (Spec.map (CommRingCat.ofHom φO.toRingHom)) ⁻¹ᵁ ((awayι₀ k d) ⁻¹ᵁ W0) :=
      Eq.mp (congrArg
        (fun q : Spec (.of O) ⟶ PP k d => (⊤ : (Spec (.of O)).Opens) ≤ q ⁻¹ᵁ W0)
        hℓg') hV0top
    refine e1.trans ((ev_congr hℓg' W0 hV0top (r j)).trans
      ((ev_comp (Spec.map (CommRingCat.ofHom φO.toRingHom)) (awayι₀ k d)
        W0 hmap (r j)).trans ?_))
    change ev (Spec.map (CommRingCat.ofHom φO.toRingHom)) ((awayι₀ k d) ⁻¹ᵁ W0) hmap
      ((awayι₀ k d).app ((awayι₀ k d) ''ᵁ ⊤) (((awayι₀ k d).appIso ⊤).inv _)) = _
    rw [Scheme.Hom.appIso_inv_app_apply]
    have hop : (eqToHom ((awayι₀ k d).preimage_image_eq ⊤)).op =
        (homOfLE ((awayι₀ k d).preimage_image_eq ⊤).le).op := Subsingleton.elim _ _
    rw [hop, ev_map (Spec.map (CommRingCat.ofHom φO.toRingHom)) ((awayι₀ k d).preimage_image_eq
        ⊤).le _ le_top,
      ev_specMap_top]
    exact hφO j
  obtain ⟨V, hV, hy'V, hVV0s⟩ := exists_isAffineOpen_mem_and_subset (x := y') (U := V0) hy'V0
  have hVV0 : V ≤ V0 := hVV0s
  have hVtop : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ ⁻¹ᵁ V := top_le_of_closedPoint_mem ℓ V hy'V
  let tV : Fin (d + 1) → Γ(P', V) := fun j => P'.presheaf.map (homOfLE hVV0).op (t j)
  let χ : Γ(P', V) →+* O := ev ℓ V hVtop
  have hχt : ∀ j, χ (tV j) = bO j := fun j => by
    change ev ℓ V hVtop (P'.presheaf.map (homOfLE hVV0).op (t j)) = bO j
    rw [ev_map ℓ hVV0 hVtop hV0top]
    exact ht j
  let 𝔮 : PrimeSpectrum Γ(P', V) := hV.primeIdealOf ⟨y', hy'V⟩
  have h𝔮 : 𝔮.asIdeal = Ideal.comap χ (maximalIdeal O) := primeIdealOf_eq_comap_ev ℓ hV hVtop
  let p' : P' ⟶ Spec (CommRingCat.of k) := β ≫ p
  let algB : Algebra k Γ(P', V) := p'.sectionsAlgebra V
  have : Algebra.FiniteType k Γ(P', V) := chart_finiteType p' hV
  have : Nonempty V := ⟨⟨y', hy'V⟩⟩
  have hχalg : ∀ c : k, χ (algebraMap k Γ(P', V) c) = θO p O f hind c := by
    intro c
    have e0 : χ (algebraMap k Γ(P', V) c) =
        ev (ℓ ≫ p') ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
      exact congrArg
        (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(Spec (.of O), ⊤) =>
          (Scheme.ΓSpecIso (.of O)).hom (q ((Scheme.ΓSpecIso (.of k)).inv c)))
        (Scheme.Hom.appLE_comp_appLE ℓ p' ⊤ V ⊤ le_top hVtop)
    have e : ℓ ≫ p' = ℓ₀ ≫ p := by
      change ℓ ≫ β ≫ p = ℓ₀ ≫ p
      rw [← Category.assoc, hℓβ]
    exact e0.trans ((ev_congr e ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv c)).trans
      (ev_ℓ₀_p p O ℓ₀ hℓ₀ d f hind _ c))
  have hind' : ∀ Q : MvPolynomial (Fin d) k,
      MvPolynomial.aeval (fun i => tV i.succ) Q ∈ 𝔮.asIdeal → Q = 0 := by
    intro Q hQ
    rw [h𝔮, Ideal.mem_comap] at hQ
    apply hind Q
    have e1 : χ (MvPolynomial.aeval (fun i => tV i.succ) Q) =
        MvPolynomial.eval₂ (χ.comp (algebraMap k _)) (χ ∘ fun i => tV i.succ) Q := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    have e2 : (χ ∘ fun i => tV i.succ) = fun i => (⟨f i, hf i⟩ : O) := by
      funext i
      change χ (tV i.succ) = _
      rw [hχt]
      exact Fin.cons_succ _ _ _
    have e3 : χ.comp (algebraMap k Γ(P', V)) = θO p O f hind := RingHom.ext hχalg
    have e4 : ((χ (MvPolynomial.aeval (fun i => tV i.succ) Q) : O) : P.functionField) =
        Q.eval₂ (θ p) f := by
      rw [e1, e3, e2]
      change algebraMap O P.functionField (MvPolynomial.eval₂ _ _ Q) = _
      rw [MvPolynomial.eval₂_comp_left (algebraMap O P.functionField)]
      rfl
    have e5 : O.valuation (Q.eval₂ (θ p) f) < 1 := by
      rw [← e4]
      exact (O.valuation_lt_one_iff _).mp hQ
    exact e5
  have h𝔮ne : 𝔮.asIdeal ≠ ⊥ := by
    intro hbot
    have hy'gen : y' = genericPoint P' := by
      have e1 : hV.fromSpec 𝔮 = y' := hV.fromSpec_primeIdealOf ⟨y', hy'V⟩
      have e2 : 𝔮 = genericPoint (Spec Γ(P', V)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext hbot
      rw [← e1, e2]
      exact genericPoint_eq_of_isOpenImmersion hV.fromSpec
    have hβgen : β y' = genericPoint P := by
      rw [hy'gen, ← genericPoint_eq_of_isOpenImmersion s, ← Scheme.Hom.comp_apply, hsβ]
      exact genericPoint_eq_of_isOpenImmersion U.ι
    have hx₀ : ℓ₀ xO = genericPoint P := by
      exact (congrArg (fun q : Spec (.of O) ⟶ P => q xO) hℓβ).symm.trans hβgen
    have hUtop : (⊤ : (Spec (CommRingCat.of O)).Opens) ≤ ℓ₀ ⁻¹ᵁ U :=
      top_le_of_closedPoint_mem ℓ₀ U (by rw [hx₀]; exact hη)
    have hχ₀ : Ideal.comap (ev ℓ₀ U hUtop) (maximalIdeal O) = ⊥ := by
      rw [← primeIdealOf_eq_comap_ev ℓ₀ hU hUtop]
      have e1 : hU.primeIdealOf ⟨ℓ₀ xO, hUtop (Opens.mem_top _)⟩ =
          hU.primeIdealOf ⟨genericPoint P, hη⟩ := by
        congr 2
      rw [e1]
      have e2 := hU.primeIdealOf_genericPoint (X := P)
      rw [genericPoint_eq_bot_of_affine] at e2
      exact congrArg PrimeSpectrum.asIdeal e2
    apply hO
    have : IsFractionRing Γ(P, U) P.functionField :=
      functionField_isFractionRing_of_isAffineOpen P U hU
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, b, hbnz, rfl⟩ := IsFractionRing.div_surjective (A := Γ(P, U)) z
    have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbnz
    have hbunit : IsUnit (ev ℓ₀ U hUtop b) := by
      by_contra hnu
      have : b ∈ Ideal.comap (ev ℓ₀ U hUtop) (maximalIdeal O) :=
        Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hnu)
      rw [hχ₀] at this
      exact hb this
    have ha' : algebraMap Γ(P, U) P.functionField a = algebraMap O P.functionField (ev ℓ₀ U hUtop a)
        :=
      (algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ U hUtop hη a).symm
    have hb' : algebraMap Γ(P, U) P.functionField b = algebraMap O P.functionField (ev ℓ₀ U hUtop b)
        :=
      (algebraMap_ev_ℓ₀ O ℓ₀ hℓ₀ U hUtop hη b).symm
    obtain ⟨u, hu⟩ := hbunit
    rw [ha', hb', ← hu]
    have : algebraMap O P.functionField (ev ℓ₀ U hUtop a) / algebraMap O P.functionField (u : O) =
        algebraMap O P.functionField (ev ℓ₀ U hUtop a * ((u⁻¹ : Oˣ) : O)) := by
      rw [map_mul, div_eq_mul_inv]
      congr 1
      exact (map_units_inv (algebraMap O P.functionField) u).symm
    rw [this]
    exact (ev ℓ₀ U hUtop a * ((u⁻¹ : Oˣ) : O)).2
  have hdimU : topologicalKrullDim P = ringKrullDim Γ(P, U) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p hU hUne
  have : IsAffine (U : Scheme.{u}) := hU
  have hsU : IsAffineOpen (s ''ᵁ ⊤) := (isAffineOpen_top (U : Scheme.{u})).image_of_isOpenImmersion
      s
  have hsUne : ((s ''ᵁ ⊤ : P'.Opens) : Set P').Nonempty :=
    ⟨s ⟨genericPoint P, hη⟩, ⟨⟨genericPoint P, hη⟩, trivial, rfl⟩⟩
  have : LocallyOfFiniteType p' := inferInstance
  have hdimP'1 : topologicalKrullDim P' = ringKrullDim Γ(P', s ''ᵁ ⊤) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p' hsU hsUne
  have hdimP'2 : topologicalKrullDim P' = ringKrullDim Γ(P', V) :=
    topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral p' hV ⟨y', hy'V⟩
  have hiso : ringKrullDim Γ(P', s ''ᵁ ⊤) = ringKrullDim Γ(P, U) :=
    ringKrullDim_eq_of_ringEquiv ((s.appIso ⊤) ≪≫ U.topIso).commRingCatIsoToRingEquiv
  have hdimB : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim Γ(P', V) := by
    rw [← hdimP'2, hdimP'1, hiso, ← hdimU]
    exact hd
  have hht : 𝔮.asIdeal.height = 1 :=
    Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq k 𝔮.asIdeal
        h𝔮ne d
      hdimB (fun i => tV i.succ) hind'
  have hdim : ringKrullDim (P'.presheaf.stalk y') = 1 := by
    rw [ringKrullDim_stalk_eq_height hV y' hy'V]
    change ((𝔮.asIdeal.height : ℕ∞) : WithBot ℕ∞) = 1
    rw [hht]
    rfl
  exact ⟨P', β, U, s, ℓ, y', hP'int, hβ, hUne, hs, hsβ, hrange, hℓβ, rfl, hdim⟩

end Main

end ValuationModel

end

end SchemeTheory.LocalDimension

namespace AlgebraicGeometry

universe u v

open SchemeTheory.LocalDimension

theorem exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
    (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p]
    (O : ValuationSubring P.functionField) (hO : O ≠ ⊤)
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ P)
    (hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O P.functionField)) ≫ ℓ₀ =
      P.fromSpecStalk (genericPoint P))
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P)
    (f : Fin d → P.functionField) (hf : ∀ i, f i ∈ O)
    (hind : ∀ Q : MvPolynomial (Fin d) k,
      O.valuation (Q.eval₂ ((P.presheaf.germ ⊤ (genericPoint P) trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) f) < 1 → Q = 0) :
    ∃ (P' : Scheme.{u}) (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P')
      (ℓ : Spec (CommRingCat.of O) ⟶ P') (y' : P'),
      IsIntegral P' ∧ IsProper β ∧ (U : Set P).Nonempty ∧ IsOpenImmersion s ∧ s ≫ β = U.ι ∧
      Set.range s.base = β.base ⁻¹' (U : Set P) ∧
      ℓ ≫ β = ℓ₀ ∧ ℓ.base (IsLocalRing.closedPoint O) = y' ∧
      ringKrullDim (P'.presheaf.stalk y') = 1 :=
  ValuationModel.main p O hO ℓ₀ hℓ₀ d hd f hf hind

end AlgebraicGeometry
end
