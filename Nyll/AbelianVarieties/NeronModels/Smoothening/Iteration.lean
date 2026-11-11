/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Tactic.Push
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Morphisms.OpenImmersionLocalization
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.AbelianVarieties.NeronModels.Smoothening.Charts
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.Smoothening.Dilatations
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.RingTheory.Dilatation.Basic
public import Nyll.SchemeTheory.RingTheory.Dilatation.UniversalProperty
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.HomSmoothLocusLePreimage

/-!
# Finite smoothening by dilatations

Glue dilatations along a finite descending stratification of the special fibre.
Each step decreases the smoothness defect while preserving the generic fibre and
lifting points over index-one extensions. Iterating the decrease and restricting to
the smooth locus produces the smooth model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NeronModelInfra
open TensorProduct IsLocalRing TopologicalSpace Topology
open NeronModelInfra.SmootheningBounds.NeronSmootheningBound (smoothnessDefect_comp_eq)
open NeronModelInfra.Dilatations.Construction.AffineCharts
  (primeIdealOf_fromSpec fromSpec_mem mem_basicOpen_iff_notMem)
open SchemeTheory.LocalGeometry.SmoothnessDefect (finiteType_sectionsAlgebra)

universe u v w

private theorem sourceLocalOfRingHom (P : MorphismProperty Scheme.{u})
    (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
    [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra.SmootheningIteration

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NeronModelInfra

noncomputable section

namespace StrataGlue

section SeparatedCriterion

variable {X₁ X : Scheme.{u}} (v : X₁ ⟶ X) (𝒲 : X₁.OpenCover)

/-- The product chart used to test whether the diagonal is closed. -/
abbrev sqMap (i : 𝒲.I₀) : pullback (𝒲.f i ≫ v) (𝒲.f i ≫ v) ⟶ pullback v v :=
  pullback.map _ _ _ _ (𝒲.f i) (𝒲.f i) (𝟙 X) (Category.comp_id _) (Category.comp_id _)

scoped instance (i : 𝒲.I₀) : IsOpenImmersion (sqMap v 𝒲 i) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

theorem isSeparated_of_openCover [∀ i, IsSeparated (𝒲.f i ≫ v)]
    (h : ∀ z₁ z₂ : X₁, v z₁ = v z₂ → ∃ i, z₁ ∈ Set.range (𝒲.f i) ∧ z₂ ∈ Set.range (𝒲.f i)) :
    IsSeparated v := by
  have hcov : ⨆ i, (sqMap v 𝒲 i).opensRange = ⊤ := by
    rw [← top_le_iff]
    rintro z -
    obtain ⟨i, h₁, h₂⟩ := h (pullback.fst v v z) (pullback.snd v v z)
      (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    change z ∈ ((sqMap v 𝒲 i).opensRange : Set _)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map]
    exact ⟨h₁, h₂⟩
  have key : ∀ i, IsClosedImmersion (pullback.diagonal v ∣_ (sqMap v 𝒲 i).opensRange) := by
    intro i
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictOpensRange _
      _)]
    have H := pullback_map_diagonal_isPullback (𝒲.f i) (𝒲.f i) v
    have e : pullback.snd (pullback.diagonal v) (sqMap v 𝒲 i) = H.isoPullback.inv ≫
        pullback.map _ _ _ _ (𝟙 _) (𝟙 _) v (Category.id_comp _).symm (Category.id_comp _).symm := by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
    rw [e, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
    have : IsIso (pullback.diagonal (𝒲.f i)) := (pullback.isIso_diagonal_iff _).mpr inferInstance
    have e2 : pullback.map _ _ _ _ (𝟙 _) (𝟙 _) v (Category.id_comp (𝒲.f i ≫ v)).symm
        (Category.id_comp (𝒲.f i ≫ v)).symm =
        inv (pullback.diagonal (𝒲.f i)) ≫ pullback.diagonal (𝒲.f i ≫ v) := by
      rw [IsIso.eq_inv_comp]
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
          pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    rw [e2, MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]
    exact IsSeparated.isClosedImmersion_diagonal
  exact ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov key⟩

end SeparatedCriterion

section Restrict

variable {X₁ X : Scheme.{u}} (v : X₁ ⟶ X)

theorem isIso_morphismRestrict_of_le {U W : X.Opens} (hW : IsIso (v ∣_ W)) (h : U ≤ W) : IsIso (v
    ∣_ U) := by
  have hUeq : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  have h1 : (MorphismProperty.isomorphisms Scheme.{u}) ((v ∣_ W) ∣_ (W.ι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme.{u}) hW _
  rwa [(MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ hUeq)] at h1

theorem isIso_pullback_snd_of_range_subset {T : Scheme.{u}} (k : T ⟶ X) (W : X.Opens) (hW : IsIso
    (v ∣_ W))
    (hk : ∀ t : T, k t ∈ W) : IsIso (pullback.snd v k) := by
  have hr : Set.range k ⊆ Set.range W.ι := by
    rintro _ ⟨t, rfl⟩; rw [Scheme.Opens.range_ι]; exact hk t
  let g := IsOpenImmersion.lift W.ι k hr
  have hg : g ≫ W.ι = k := IsOpenImmersion.lift_fac _ _ _
  have : IsIso (pullback.snd v W.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]; infer_instance
  have : ∀ (k' : T ⟶ X), k' = g ≫ W.ι → IsIso (pullback.snd v k') := by
    rintro k' rfl
    have e : pullback.snd v (g ≫ W.ι) =
        (pullbackLeftPullbackSndIso v W.ι g).inv ≫ pullback.snd (pullback.snd v W.ι) g := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [e]
    infer_instance
  exact this k hg.symm

theorem isIso_pullback_map {S T : Scheme.{u}} (f : X ⟶ S) (ι : T ⟶ S) (W : X.Opens) (hW : IsIso (v
    ∣_ W))
    (hι : ∀ t : ↥(pullback f ι), pullback.fst f ι t ∈ W) :
    IsIso (pullback.map (v ≫ f) ι f ι v (𝟙 T) (𝟙 S) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  have : IsIso (pullback.snd v (pullback.fst f ι)) :=
    isIso_pullback_snd_of_range_subset v (pullback.fst f ι) W hW hι
  have e : pullback.map (v ≫ f) ι f ι v (𝟙 T) (𝟙 S) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (pullbackRightPullbackFstIso f ι v).inv ≫ pullback.snd v (pullback.fst f ι) := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_fst]
    · simp only [pullback.lift_snd, Category.comp_id, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_snd]
  rw [e]
  infer_instance

theorem isIso_ι_morphismRestrict (U W : X.Opens) (h : W ≤ U) : IsIso (U.ι ∣_ W) := by
  apply U.ι.isIso_morphismRestrict_of_le_opensRange
  rwa [Scheme.Opens.opensRange_ι]

theorem isIso_morphismRestrict_of_comp {Q : Scheme.{u}} (j : Q ⟶ X₁) [IsOpenImmersion j] (w : Q ⟶ X)
    (hw : j ≫ v = w) (W : X.Opens) (hW : IsIso (w ∣_ W)) (hcov : ∀ z : X₁, v z ∈ W → z ∈ Set.range
      j) :
    IsIso (v ∣_ W) := by
  subst hw
  let e := IsOpenImmersion.isoOfRangeEq (v ⁻¹ᵁ W).ι (((j ≫ v) ⁻¹ᵁ W).ι ≫ j) (by
    rw [Scheme.Opens.range_ι]
    ext z
    constructor
    · intro hz
      obtain ⟨q, rfl⟩ := hcov z hz
      have hq : (j ≫ v) q ∈ W := hz
      exact ⟨(⟨q, hq⟩ : (((j ≫ v) ⁻¹ᵁ W) : Scheme.{u})), rfl⟩
    · rintro ⟨q, rfl⟩
      exact q.2)
  have he : e.hom ≫ ((j ≫ v) ⁻¹ᵁ W).ι ≫ j = (v ⁻¹ᵁ W).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _
    _ _
  have : v ∣_ W = e.hom ≫ ((j ≫ v) ∣_ W) := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, ←
      Category.assoc _ j v,
      ← Category.assoc e.hom, ← Category.assoc e.hom, Category.assoc e.hom, he]
  rw [this]
  infer_instance

end Restrict

section Points

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem algebraMap_injective {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (h : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal R') :
    Function.Injective (algebraMap R R') := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  have hprime : (RingHom.ker (algebraMap R R')).IsPrime := RingHom.ker_isPrime _
  have hne' : RingHom.ker (algebraMap R R') ≠ ⊥ := fun h0 => hne (by
    have : r ∈ RingHom.ker (algebraMap R R') := hr
    rw [h0] at this; exact this)
  have hmax := hprime.isMaximal hne'
  have heq : RingHom.ker (algebraMap R R') = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hmax
  have : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = ⊥ := by
    rw [← heq, Ideal.map_eq_bot_iff_le_ker]
  rw [this] at h
  exact IsDiscreteValuationRing.not_a_field R' h.symm

theorem specMap_apply_ne_closedPoint {R' : Type u} [CommRing R'] (g : R →+* R')
    (hinj : Function.Injective g) (q : PrimeSpectrum R') (hq : q.asIdeal = ⊥) :
    (Spec.map (CommRingCat.ofHom g)) q ≠ IsLocalRing.closedPoint R := by
  intro h
  have h' := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap g q.asIdeal = IsLocalRing.maximalIdeal R at h'
  rw [hq, Ideal.comap_bot_of_injective _ hinj] at h'
  exact IsDiscreteValuationRing.not_a_field R h'.symm

theorem range_subset_of_apply_closedPoint_mem {X : Scheme.{u}} {R' : Type u} [CommRing R']
    [IsLocalRing R']
    {W : X.Opens} (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x (IsLocalRing.closedPoint R') ∈ W) : Set.range x ⊆ Set.range W.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact ((IsLocalRing.specializes_closedPoint t).map x.continuous).mem_open W.isOpen hx

end Points

section Dictionary

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem mem_iff_vanishingIdeal_le (Z : Set X) (hZ : IsClosed Z) (y : X) (hy : y ∈ U) :
    y ∈ Z ↔ PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈
      Z}) ≤
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [NeronModelInfra.Dilatations.Construction.AffineCharts.vanishingIdeal_image_eq hU Z hZ]
  exact NeronModelInfra.Dilatations.Construction.AffineCharts.mem_iff_ideal_le hU Z hZ y hy

end Dictionary

section Setup

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The open complement of the special fibre. -/
def XK : X.Opens :=
  f ⁻¹ᵁ ⟨{IsLocalRing.closedPoint R}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩

theorem mem_XK {x : X} : x ∈ XK f ↔ f x ≠ IsLocalRing.closedPoint R := Iff.rfl

variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i))

/-- The open complement of a closed stratum. -/
def C (m : ℕ) : X.Opens := ⟨(Y m)ᶜ, (hY m).isOpen_compl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_C {m : ℕ} {x : X} : x ∈ C Y hY m ↔ x ∉ Y m := Iff.rfl

theorem XK_le_C (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R) (m : ℕ) : XK f ≤ C Y hY m :=
  fun x hx hxY => hx (hYs m x hxY)

/-- The ideal cutting out a closed center in an affine chart. -/
abbrev idealOf (U : X.Opens) (hU : IsAffineOpen U) (Z : Set X) : Ideal Γ(X, U) :=
  PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Z})

/-- The restriction of a base-ring element to an affine chart. -/
abbrev secOf (U : X.Opens) (π : R) : Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
    R)).inv.hom π))

/-- An actual dilatation with its affine charts and generic-fibre comparison. -/
structure Dil (Z : Set X) where
  /-- The dilatation scheme. -/
  D : Scheme.{u}
  /-- The dilatation morphism. -/
  p : D ⟶ X
  /-- The dilatation morphism is affine. -/
  affine : IsAffineHom p
  /-- The structural morphism is locally of finite type. -/
  loft : LocallyOfFiniteType p
  /-- The dilatation is an isomorphism away from the special fibre. -/
  isIso_restrict : ∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)
  /-- Special-fibre points map into the chosen center. -/
  apply_mem : ∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Z
  /-- Affine dilatation charts and their compatibility with the structure morphism. -/
  chart : ∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R), IsLocalRing.maximalIdeal R = Ideal.span
    {π} →
    ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
        Spec (CommRingCat.of (AffineDilatation.Ring (idealOf U hU Z) (secOf f U π))),
      (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
          (AffineDilatation.Ring (idealOf U hU Z) (secOf f U π)))) ≫ hU.fromSpec

/-- A dilatation chart together with the point-lifting locus it covers. -/
def ChartConcl {X₁ : Scheme.{u}} (v : X₁ ⟶ X) (i : ℕ) (U : X.Opens) (hU : IsAffineOpen U) (π : R)
    : Prop :=
  ∃ (W : X₁.Opens)
    (e : (W : Scheme.{u}) ≅ Spec (CommRingCat.of (AffineDilatation.Ring (idealOf U hU (Y i))
      (secOf f U π)))),
    W.ι ≫ v = e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (AffineDilatation.Ring (idealOf U hU (Y i)) (secOf f U π)))) ≫ hU.fromSpec ∧
    ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
        (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
        (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
        x₁.1 (IsLocalRing.closedPoint R') ∈ W

/-- The model and lifting properties after finitely many gluing steps. -/
structure Prev (n : ℕ) where
  /-- The model at this stage. -/
  Q : Scheme.{u}
  /-- The morphism to the initial scheme. -/
  w : Q ⟶ X
  /-- The structural morphism is separated. -/
  sep : IsSeparated w
  /-- The structural morphism is locally of finite type. -/
  loft : LocallyOfFiniteType w
  /-- The structural morphism is quasi-compact. -/
  qc : QuasiCompact w
  /-- The generic open is unchanged. -/
  isoK : IsIso (w ∣_ XK f)
  /-- The complement of the initial stratum is unchanged. -/
  isoC : IsIso (w ∣_ C Y hY 0)
  /-- The model avoids the next stratum. -/
  notMem : ∀ q : Q, w q ∉ Y n
  /-- Points outside the next stratum lift to this model. -/
  lift : ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
    Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
    ∀ x : Spec (CommRingCat.of R') ⟶ X, x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      x (IsLocalRing.closedPoint R') ∉ Y n → ∃ x₁ : Spec (CommRingCat.of R') ⟶ Q, x₁ ≫ w = x
  /-- Affine dilatation charts and their compatibility with the structure morphism. -/
  chart : ∀ i, i < n → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ U, y ∉ Y (i + 1)) →
    ∀ π : R, IsLocalRing.maximalIdeal R = Ideal.span {π} → ChartConcl f Y w i U hU π

attribute [scoped instance] Dil.affine Dil.loft Prev.sep Prev.loft Prev.qc Prev.isoK Prev.isoC

end Setup

section Base

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y =
    IsLocalRing.closedPoint R)

/-- The initial model obtained by removing the first closed stratum. -/
def prevZero : Prev f Y hY 0 where
  Q := ↑(C Y hY 0)
  w := (C Y hY 0).ι
  sep := inferInstance
  loft := inferInstance
  qc := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    infer_instance
  isoK := isIso_ι_morphismRestrict _ _ (XK_le_C f Y hY hYs 0)
  isoC := isIso_ι_morphismRestrict _ _ le_rfl
  notMem := fun q => q.2
  lift := by
    intro R' _ _ _ _ _ x _ hx₀
    exact ⟨IsOpenImmersion.lift (C Y hY 0).ι x (range_subset_of_apply_closedPoint_mem (W := C Y hY
      0) x hx₀),
      IsOpenImmersion.lift_fac _ _ _⟩
  chart := fun i hi => absurd hi (Nat.not_lt_zero i)

end Base

section Step

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable {Y : ℕ → Set X} (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y =
    IsLocalRing.closedPoint R)
variable {n : ℕ} (𝔓 : Prev f Y hY n) (𝔇 : Dil f (Y n))

/-- The dilatation locus outside the next stratum. -/
def E : 𝔇.D.Opens := 𝔇.p ⁻¹ᵁ C Y hY (n + 1)

/-- The generic-fibre open of the new dilatation. -/
abbrev U₀ : 𝔇.D.Opens := 𝔇.p ⁻¹ᵁ XK f

include hYs in
theorem U₀_le_E : U₀ 𝔇 ≤ E hY 𝔇 := fun _ hd => XK_le_C f Y hY hYs (n + 1) hd

scoped instance : IsIso (𝔇.p ∣_ XK f) := 𝔇.isIso_restrict _ fun _ hx => hx

/-- The generic open included in the new chart. -/
def iE : (↑(U₀ 𝔇) : Scheme.{u}) ⟶ ↑(E hY 𝔇) := 𝔇.D.homOfLE (U₀_le_E hY hYs 𝔇)

scoped instance : IsOpenImmersion (iE hY hYs 𝔇) := by
  delta iE; infer_instance

/-- The generic open identified with the preceding model. -/
def iQ : (↑(U₀ 𝔇) : Scheme.{u}) ⟶ 𝔓.Q := (𝔇.p ∣_ XK f) ≫ inv (𝔓.w ∣_ XK f) ≫ (𝔓.w ⁻¹ᵁ XK f).ι

scoped instance : IsOpenImmersion (iQ hY 𝔓 𝔇) := by
  delta iQ; infer_instance

theorem iQ_w : iQ hY 𝔓 𝔇 ≫ 𝔓.w = (U₀ 𝔇).ι ≫ 𝔇.p := by
  rw [iQ, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    morphismRestrict_ι]

theorem iE_p : iE hY hYs 𝔇 ≫ (E hY 𝔇).ι ≫ 𝔇.p = (U₀ 𝔇).ι ≫ 𝔇.p := by
  rw [iE, ← Category.assoc, Scheme.homOfLE_ι]

/-- The model obtained by gluing the preceding stage to the new chart. -/
def X₁ : Scheme.{u} := pushout (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)

/-- The new chart included in the glued model. -/
def jE : (↑(E hY 𝔇) : Scheme.{u}) ⟶ X₁ hY hYs 𝔓 𝔇 := pushout.inl _ _

/-- The preceding model included in the glued model. -/
def jQ : 𝔓.Q ⟶ X₁ hY hYs 𝔓 𝔇 := pushout.inr _ _

scoped instance : IsOpenImmersion (jE hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.left))

scoped instance : IsOpenImmersion (jQ hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.right))

/-- The structural morphism from the glued model to the initial scheme. -/
def v : X₁ hY hYs 𝔓 𝔇 ⟶ X :=
  pushout.desc ((E hY 𝔇).ι ≫ 𝔇.p) 𝔓.w (by rw [iE_p, iQ_w])

@[scoped simp] theorem jE_v : jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇 = (E hY 𝔇).ι ≫ 𝔇.p := pushout.inl_desc
    _ _ _
@[scoped simp] theorem jQ_v : jQ hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇 = 𝔓.w := pushout.inr_desc _ _ _

theorem jE_iE : iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇 = iQ hY 𝔓 𝔇 ≫ jQ hY hYs 𝔓 𝔇 := pushout.condition

theorem v_jE_apply (e : (E hY 𝔇 : Scheme.{u})) : v hY hYs 𝔓 𝔇 (jE hY hYs 𝔓 𝔇 e) = 𝔇.p e.1 := by
  exact congrArg (fun m : (E hY 𝔇 : Scheme.{u}) ⟶ X => m e) (jE_v hY hYs 𝔓 𝔇)

theorem v_jQ_apply (q : 𝔓.Q) : v hY hYs 𝔓 𝔇 (jQ hY hYs 𝔓 𝔇 q) = 𝔓.w q := by
  rw [← Scheme.Hom.comp_apply, jQ_v]

theorem cover (z : X₁ hY hYs 𝔓 𝔇) : (∃ e, jE hY hYs 𝔓 𝔇 e = z) ∨ ∃ q, jQ hY hYs 𝔓 𝔇 q = z := by
  obtain ⟨i, xi, rfl⟩ :=
    Scheme.IsLocallyDirected.ι_jointly_surjective (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) z
  rcases i with (_ | _ | _)
  · left
    refine ⟨iE hY hYs 𝔇 xi, ?_⟩
    change (iE hY hYs 𝔇 ≫ pushout.inl (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) xi = _
    rw [← colimit.w (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.Hom.fst]
    rfl
  · exact Or.inl ⟨xi, rfl⟩
  · exact Or.inr ⟨xi, rfl⟩

theorem mem_U₀ (e : (E hY 𝔇 : Scheme.{u})) (he : 𝔇.p e.1 ∉ Y n) : e.1 ∈ U₀ 𝔇 :=
  fun h => he (𝔇.apply_mem _ h)

theorem jE_mem_range_jQ (e : (E hY 𝔇 : Scheme.{u})) (he : 𝔇.p e.1 ∉ Y n) :
    jE hY hYs 𝔓 𝔇 e ∈ Set.range (jQ hY hYs 𝔓 𝔇) := by
  let e₀ : (U₀ 𝔇 : Scheme.{u}) := ⟨e.1, mem_U₀ hY 𝔇 e he⟩
  refine ⟨iQ hY 𝔓 𝔇 e₀, ?_⟩
  calc
    _ = jE hY hYs 𝔓 𝔇 (iE hY hYs 𝔇 e₀) :=
      (congrArg (fun m : (U₀ 𝔇 : Scheme.{u}) ⟶ X₁ hY hYs 𝔓 𝔇 => m e₀)
        (jE_iE hY hYs 𝔓 𝔇)).symm
    _ = jE hY hYs 𝔓 𝔇 e :=
      congrArg (jE hY hYs 𝔓 𝔇) (𝔇.D.homOfLE_apply' _ e.1 _)

theorem mem_range_jE (z : X₁ hY hYs 𝔓 𝔇) (hz : v hY hYs 𝔓 𝔇 z ∈ Y n) :
    z ∈ Set.range (jE hY hYs 𝔓 𝔇) := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · exact ⟨e, rfl⟩
  · rw [v_jQ_apply] at hz; exact absurd hz (𝔓.notMem q)

theorem mem_range_jQ (z : X₁ hY hYs 𝔓 𝔇) (hz : v hY hYs 𝔓 𝔇 z ∉ Y n) :
    z ∈ Set.range (jQ hY hYs 𝔓 𝔇) := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · rw [v_jE_apply] at hz
    exact jE_mem_range_jQ hY hYs 𝔓 𝔇 e hz
  · exact ⟨q, rfl⟩

theorem v_notMem (hanti : ∀ i, Y (i + 1) ⊆ Y i) (z : X₁ hY hYs 𝔓 𝔇) : v hY hYs 𝔓 𝔇 z ∉ Y (n + 1)
    := by
  rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
  · rw [v_jE_apply]; exact e.2
  · rw [v_jQ_apply]; exact fun h => 𝔓.notMem q (hanti n h)

/-- The open cover supplied by the gluing pushout. -/
def cov : (X₁ hY hYs 𝔓 𝔇).OpenCover :=
  Scheme.IsLocallyDirected.openCover (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇))

theorem cov_f_zero : (cov hY hYs 𝔓 𝔇).f WalkingSpan.zero = iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇 :=
  (colimit.w (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.Hom.fst).symm

theorem cov_f_left : (cov hY hYs 𝔓 𝔇).f WalkingSpan.left = jE hY hYs 𝔓 𝔇 := rfl

theorem cov_f_right : (cov hY hYs 𝔓 𝔇).f WalkingSpan.right = jQ hY hYs 𝔓 𝔇 := rfl

scoped instance isSeparated_v : IsSeparated (v hY hYs 𝔓 𝔇) := by
  have : ∀ i, IsSeparated ((cov hY hYs 𝔓 𝔇).f i ≫ v hY hYs 𝔓 𝔇) := by
    rintro (_ | _ | _)
    · rw [cov_f_zero]
      change IsSeparated ((iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇) ≫ v hY hYs 𝔓 𝔇)
      rw [Category.assoc, jE_v]
      infer_instance
    · change IsSeparated (jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇)
      rw [jE_v]
      infer_instance
    · change IsSeparated (jQ hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇)
      rw [jQ_v]
      infer_instance
  refine isSeparated_of_openCover (v hY hYs 𝔓 𝔇) (cov hY hYs 𝔓 𝔇) ?_
  intro z₁ z₂ h
  by_cases h₁ : v hY hYs 𝔓 𝔇 z₁ ∈ Y n
  · refine ⟨WalkingSpan.left, ?_, ?_⟩ <;> rw [cov_f_left]
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)
  · refine ⟨WalkingSpan.right, ?_, ?_⟩ <;> rw [cov_f_right]
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)

scoped instance locallyOfFiniteType_v : LocallyOfFiniteType (v hY hYs 𝔓 𝔇) := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    sourceLocalOfRingHom _ RingHom.FiniteType
  refine IsZariskiLocalAtSource.of_openCover (cov hY hYs 𝔓 𝔇) ?_
  rintro (_ | _ | _)
  · rw [cov_f_zero]
    change LocallyOfFiniteType ((iE hY hYs 𝔇 ≫ jE hY hYs 𝔓 𝔇) ≫ v hY hYs 𝔓 𝔇)
    rw [Category.assoc, jE_v]
    infer_instance
  · change LocallyOfFiniteType (jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇)
    rw [jE_v]
    infer_instance
  · change LocallyOfFiniteType (jQ hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇)
    rw [jQ_v]
    infer_instance

scoped instance quasiCompact_v [LocallyOfFiniteType f] : QuasiCompact (v hY hYs 𝔓 𝔇) := by
  have : IsLocallyNoetherian 𝔇.D := LocallyOfFiniteType.isLocallyNoetherian (𝔇.p ≫ f)
  have : QuasiCompact ((E hY 𝔇).ι ≫ 𝔇.p) := inferInstance
  constructor
  intro U hUo hUc
  have hset : v hY hYs 𝔓 𝔇 ⁻¹' U =
      jE hY hYs 𝔓 𝔇 '' (((E hY 𝔇).ι ≫ 𝔇.p) ⁻¹' U) ∪ jQ hY hYs 𝔓 𝔇 '' (𝔓.w ⁻¹' U) := by
    ext z
    constructor
    · intro hz
      rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
      · left; refine ⟨e, ?_, rfl⟩
        rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, jE_v] at hz; exact hz
      · right; refine ⟨q, ?_, rfl⟩
        rw [Set.mem_preimage, ← v_jQ_apply hY hYs 𝔓 𝔇 q]; exact hz
    · rintro (⟨e, he, rfl⟩ | ⟨q, hq, rfl⟩)
      · change (jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇) e ∈ U
        rw [jE_v]; exact he
      · change v hY hYs 𝔓 𝔇 (jQ hY hYs 𝔓 𝔇 q) ∈ U
        rw [v_jQ_apply]; exact hq
  rw [hset]
  exact ((QuasiCompact.isCompact_preimage (f := (E hY 𝔇).ι ≫ 𝔇.p) U hUo hUc).image
    (jE hY hYs 𝔓 𝔇).continuous).union
    ((QuasiCompact.isCompact_preimage (f := 𝔓.w) U hUo hUc).image (jQ hY hYs 𝔓 𝔇).continuous)

theorem isIso_restrict_XK : IsIso (v hY hYs 𝔓 𝔇 ∣_ XK f) :=
  isIso_morphismRestrict_of_comp (v hY hYs 𝔓 𝔇) (jQ hY hYs 𝔓 𝔇) 𝔓.w (jQ_v hY hYs 𝔓 𝔇) (XK f) 𝔓.isoK
    fun z hz => mem_range_jQ hY hYs 𝔓 𝔇 z fun h => hz (hYs n _ h)

theorem isIso_restrict_C (hanti : ∀ i, Y (i + 1) ⊆ Y i) : IsIso (v hY hYs 𝔓 𝔇 ∣_ C Y hY 0) :=
  isIso_morphismRestrict_of_comp (v hY hYs 𝔓 𝔇) (jQ hY hYs 𝔓 𝔇) 𝔓.w (jQ_v hY hYs 𝔓 𝔇) (C Y hY 0)
    𝔓.isoC
    fun z hz => mem_range_jQ hY hYs 𝔓 𝔇 z fun h => hz ((antitone_nat_of_succ_le hanti)
      (Nat.zero_le n) h)

section Lift

variable (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
variable (hR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
    IsLocalRing.maximalIdeal R')

include hR' in
theorem algebraMap_ne_zero {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    algebraMap R R' π ≠ 0 := by
  intro h0
  rw [hπ, Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_zero] at hR'
  exact IsDiscreteValuationRing.not_a_field R' hR'.symm

include hY hR' in
theorem exists_lift_D (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hx₀ : x (IsLocalRing.closedPoint R') ∈ Y n) :
    ∃ x₁ : Spec (CommRingCat.of R') ⟶ 𝔇.D, x₁ ≫ 𝔇.p = x := by
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπirr.maximalIdeal_eq
  obtain ⟨_, ⟨U, hU, rfl⟩, hx₀U, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint R'))) isOpen_univ
  change IsAffineOpen U at hU
  obtain ⟨e, he⟩ := 𝔇.chart U hU π hπ
  have hle : (⊤ : (Spec (CommRingCat.of R')).Opens) ≤ x ⁻¹ᵁ U := by
    rintro t -
    have := range_subset_of_apply_closedPoint_mem (W := U) x hx₀U ⟨t, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  let φ' : Γ(X, U) ⟶ CommRingCat.of R' := x.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of
    R')).hom
  have hφ'x : Spec.map φ' ≫ hU.fromSpec = x := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top
      _) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  let I : Ideal Γ(X, U) := idealOf U hU (Y n)
  let a : Γ(X, U) := secOf f U π
  have hφ'a : φ'.hom a = algebraMap R R' π := by
    simp only [φ', a, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply (X.presheaf.map _) (x.appLE U ⊤ hle), Scheme.Hom.map_appLE]
    have h1 : x.appLE ⊤ ⊤ (hle.trans (x.preimage_mono le_top)) = x.appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [h1, ← CommRingCat.comp_apply f.appTop x.appTop, ← Scheme.Hom.comp_appTop, hx,
      ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R')).hom,
        Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R)).hom,
      Iso.inv_hom_id]
    rfl
  let alg : Algebra Γ(X, U) R' := φ'.hom.toAlgebra
  have hreg : IsSMulRegular R' a := by
    intro r s hrs
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hφ'a] at hrs
    exact mul_left_cancel₀ (algebraMap_ne_zero R' hR' hπ) hrs
  have hIle : I.map (algebraMap Γ(X, U) R') ≤ Ideal.span {algebraMap Γ(X, U) R' a} := by
    rw [RingHom.algebraMap_toAlgebra, hφ'a, ← Set.image_singleton, ← Ideal.map_span, ← hπ, hR',
      Ideal.map_le_iff_le_comap]
    let pt : Spec (CommRingCat.of R') := IsLocalRing.closedPoint R'
    let q : PrimeSpectrum Γ(X, U) := Spec.map φ' pt
    have hq0 : hU.fromSpec q = x (IsLocalRing.closedPoint R') :=
      congrArg (fun m : Spec (CommRingCat.of R') ⟶ X => m pt) hφ'x
    have hqY : hU.fromSpec q ∈ Y n := hq0 ▸ hx₀
    have h := (mem_iff_vanishingIdeal_le hU (Y n) (hY n) (hU.fromSpec q) (fromSpec_mem hU q)).mp hqY
    rw [primeIdealOf_fromSpec] at h
    have hq' : q.asIdeal = Ideal.comap φ'.hom (IsLocalRing.maximalIdeal R') := rfl
    rw [← hq']
    exact h
  obtain ⟨⟨ψ⟩, -⟩ := AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular I a hreg
    hIle
  have hψ : CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring I a)) ≫
      CommRingCat.ofHom ψ.toRingHom = φ' := by
    ext g
    change ψ (algebraMap Γ(X, U) (AffineDilatation.Ring I a) g) = φ'.hom g
    rw [ψ.commutes]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ e.inv ≫ (𝔇.p ⁻¹ᵁ U).ι, ?_⟩
  rw [Category.assoc, Category.assoc, he, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, hψ, hφ'x]

include hR' in
theorem exists_lift (x : Spec (CommRingCat.of R') ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hxn : x (IsLocalRing.closedPoint R') ∉ Y (n + 1)) :
    ∃ x₁ : Spec (CommRingCat.of R') ⟶ X₁ hY hYs 𝔓 𝔇, x₁ ≫ v hY hYs 𝔓 𝔇 = x := by
  by_cases hx₀ : x (IsLocalRing.closedPoint R') ∈ Y n
  swap
  · obtain ⟨x₁, hx₁⟩ := 𝔓.lift R' hR' x hx hx₀
    exact ⟨x₁ ≫ jQ hY hYs 𝔓 𝔇, by rw [Category.assoc, jQ_v, hx₁]⟩
  obtain ⟨xD, hxD⟩ := exists_lift_D hY 𝔇 R' hR' x hx hx₀
  have hmem : xD (IsLocalRing.closedPoint R') ∈ E hY 𝔇 := by
    change 𝔇.p (xD (IsLocalRing.closedPoint R')) ∉ Y (n + 1)
    exact (congrArg (fun m : Spec (CommRingCat.of R') ⟶ X =>
      m (IsLocalRing.closedPoint R')) hxD).symm ▸ hxn
  have hr := range_subset_of_apply_closedPoint_mem (W := E hY 𝔇) xD hmem
  refine ⟨IsOpenImmersion.lift (E hY 𝔇).ι xD hr ≫ jE hY hYs 𝔓 𝔇, ?_⟩
  rw [Category.assoc, jE_v, ← Category.assoc, IsOpenImmersion.lift_fac, hxD]

end Lift

theorem chart_new (U : X.Opens) (hU : IsAffineOpen U) (hUY : ∀ y ∈ U, y ∉ Y (n + 1)) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) : ChartConcl f Y (v hY hYs 𝔓 𝔇) n U hU
      π := by
  obtain ⟨e, he⟩ := 𝔇.chart U hU π hπ
  have hle : 𝔇.p ⁻¹ᵁ U ≤ E hY 𝔇 := fun d hd => hUY _ hd
  let g := 𝔇.D.homOfLE hle ≫ jE hY hYs 𝔓 𝔇
  let e₀ := IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by rw [Scheme.Opens.range_ι]; rfl)
  have he₀ : e₀.hom ≫ g = g.opensRange.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine ⟨g.opensRange, e₀ ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, ← he, ← he₀, Category.assoc, Category.assoc, jE_v, ←
    Category.assoc _ _ 𝔇.p,
      Scheme.homOfLE_ι]
  · intro R' _ _ _ _ _ x₁ hYmem hUmem
    obtain ⟨d, hd⟩ := mem_range_jE hY hYs 𝔓 𝔇 (x₁.1 (IsLocalRing.closedPoint R')) hYmem
    have hdU : d.1 ∈ 𝔇.p ⁻¹ᵁ U := by
      change 𝔇.p d.1 ∈ U
      rwa [← v_jE_apply hY hYs 𝔓 𝔇 d, hd]
    change x₁.1 (IsLocalRing.closedPoint R') ∈ Set.range g
    refine ⟨⟨d.1, hdU⟩, ?_⟩
    change jE hY hYs 𝔓 𝔇 (𝔇.D.homOfLE hle ⟨d.1, hdU⟩) = _
    rw [Scheme.homOfLE_apply']
    exact hd

theorem chart_old (hanti : ∀ i, Y (i + 1) ⊆ Y i) (i : ℕ) (hi : i < n) (U : X.Opens) (hU :
    IsAffineOpen U)
    (hUY : ∀ y ∈ U, y ∉ Y (i + 1)) (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    ChartConcl f Y (v hY hYs 𝔓 𝔇) i U hU π := by
  obtain ⟨W', e', he', hcatch⟩ := 𝔓.chart i hi U hU hUY π hπ
  let j := jQ hY hYs 𝔓 𝔇
  refine ⟨j ''ᵁ W', (j.isoImage W').symm ≪≫ e', ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he', ← Scheme.Hom.isoImage_inv_ι j W',
      Category.assoc, Category.assoc, jQ_v]
  · intro R' _ _ _ _ hR' x₁ hYmem hUmem
    have hnot : (x₁.1 ≫ v hY hYs 𝔓 𝔇) (IsLocalRing.closedPoint R') ∉ Y n := fun h =>
      hUY _ hUmem ((antitone_nat_of_succ_le hanti) (Nat.succ_le_of_lt hi) h)
    have hrange : Set.range x₁.1 ⊆ Set.range j := by
      have h1 : x₁.1 (IsLocalRing.closedPoint R') ∈ j.opensRange :=
        mem_range_jQ hY hYs 𝔓 𝔇 _ hnot
      have h2 := range_subset_of_apply_closedPoint_mem (W := j.opensRange) x₁.1 h1
      rwa [Scheme.Opens.range_ι] at h2
    let y := IsOpenImmersion.lift j x₁.1 hrange
    have hy : y ≫ j = x₁.1 := IsOpenImmersion.lift_fac _ _ _
    have hyover : y ≫ 𝔓.w ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [← jQ_v hY hYs 𝔓 𝔇, ← Category.assoc, ← Category.assoc, hy, Category.assoc]; exact x₁.2
    have h1 : (y ≫ 𝔓.w) (IsLocalRing.closedPoint R') = (x₁.1 ≫ v hY hYs 𝔓 𝔇)
      (IsLocalRing.closedPoint R') := by
      rw [← jQ_v hY hYs 𝔓 𝔇, ← Category.assoc, hy]
    have hW' := hcatch R' hR' ⟨y, hyover⟩ (by rw [h1]; exact hYmem) (by rw [h1]; exact hUmem)
    change x₁.1 (IsLocalRing.closedPoint R') ∈ j ''ᵁ W'
    rw [← hy]
    change j (y (IsLocalRing.closedPoint R')) ∈ j ''ᵁ W'
    exact ⟨_, hW', rfl⟩

/-- The next gluing stage, with the previous and new affine charts. -/
def prevSucc [LocallyOfFiniteType f] (hanti : ∀ i, Y (i + 1) ⊆ Y i) : Prev f Y hY (n + 1) where
  Q := X₁ hY hYs 𝔓 𝔇
  w := v hY hYs 𝔓 𝔇
  sep := inferInstance
  loft := inferInstance
  qc := inferInstance
  isoK := isIso_restrict_XK hY hYs 𝔓 𝔇
  isoC := isIso_restrict_C hY hYs 𝔓 𝔇 hanti
  notMem := v_notMem hY hYs 𝔓 𝔇 hanti
  lift := fun R' _ _ _ _ hR' x hx hxn => exists_lift hY hYs 𝔓 𝔇 R' hR' x hx hxn
  chart := by
    intro i hi U hU hUY π hπ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact chart_old hY hYs 𝔓 𝔇 hanti i hi U hU hUY π hπ
    · exact chart_new hY hYs 𝔓 𝔇 U hU hUY π hπ

end Step

section Consequences

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable {Y : ℕ → Set X} (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y =
    IsLocalRing.closedPoint R)
variable {X₁ : Scheme.{u}} (v : X₁ ⟶ X) (hC : IsIso (v ∣_ C Y hY 0))

include hYs hC in
theorem isIso_genericFibre (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
      v (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))
        := by
  refine isIso_pullback_map v f _ (C Y hY 0) hC fun t => ?_
  intro hmem
  have h1 : f (pullback.fst f (specGenericFibreInclusion R K) t) =
      (specGenericFibreInclusion R K) (pullback.snd f (specGenericFibreInclusion R K) t) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have h2 := hYs 0 _ hmem
  rw [h1] at h2
  exact specMap_apply_ne_closedPoint (algebraMap R K) (IsFractionRing.injective R K) _
    (Ideal.eq_bot_of_prime _) h2

variable [IsSeparated v]
variable (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
variable (hR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
    IsLocalRing.maximalIdeal R')

include hYs hC hR' in
theorem lift_unique (x₁ x₂ : Spec (CommRingCat.of R') ⟶ X₁) (h : x₁ ≫ v = x₂ ≫ v)
    (hx : x₁ ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) : x₁ = x₂ := by
  have : IsIso (v ∣_ C Y hY 0) := hC
  let K' := FractionRing R'
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  have happ : ι.appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (algebraMap R' K') ≫
      (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsDominant ι := isDominant_of_of_appTop_injective (by
    rw [happ]
    exact (Scheme.ΓSpecIso (CommRingCat.of K')).commRingCatIsoToRingEquiv.symm.injective.comp
      ((IsFractionRing.injective R' K').comp
        (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.injective))
  refine ext_of_isDominant_of_isSeparated v h ι ?_
  have hinj : Function.Injective ((algebraMap R' K').comp (algebraMap R R')) :=
    (IsFractionRing.injective R' K').comp (algebraMap_injective hR')
  have hmem : ∀ y : Spec (CommRingCat.of R') ⟶ X₁,
      y ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      Set.range (ι ≫ y) ⊆ Set.range (v ⁻¹ᵁ C Y hY 0).ι := by
    rintro y hy _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change v ((ι ≫ y) t) ∉ Y 0
    intro hmemY
    have h1 := hYs 0 _ hmemY
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hy, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp] at h1
    let p : PrimeSpectrum K' := t
    have : p.asIdeal.IsPrime := p.isPrime
    exact specMap_apply_ne_closedPoint _ hinj p (Ideal.eq_bot_of_prime _) h1
  have hx₂ : x₂ ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [← Category.assoc, ← h, Category.assoc, hx]
  let a := IsOpenImmersion.lift (v ⁻¹ᵁ C Y hY 0).ι (ι ≫ x₁) (hmem x₁ hx)
  let b := IsOpenImmersion.lift (v ⁻¹ᵁ C Y hY 0).ι (ι ≫ x₂) (hmem x₂ hx₂)
  have ha : a ≫ (v ⁻¹ᵁ C Y hY 0).ι = ι ≫ x₁ := IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ (v ⁻¹ᵁ C Y hY 0).ι = ι ≫ x₂ := IsOpenImmersion.lift_fac _ _ _
  have hab : a = b := by
    rw [← cancel_mono (v ∣_ C Y hY 0), ← cancel_mono (C Y hY 0).ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, reassoc_of% ha, reassoc_of% hb, h]
  rw [← ha, ← hb, hab]

end Consequences

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i)
  (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)

include hanti hYs in
theorem nonempty_prev : ∀ n, Nonempty (Prev f Y hY n)
  | 0 => ⟨prevZero f Y hY hYs⟩
  | n + 1 => by
    obtain ⟨𝔓⟩ := nonempty_prev n
    obtain ⟨D, p, h1, h2, h3, h4, h5⟩ :=
      NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed f
        (Y n) (hY n)
        (hYs n)
    let 𝔇 : Dil f (Y n) := ⟨D, p, h1, h2, h3, h4, h5⟩
    exact ⟨prevSucc hY hYs 𝔓 𝔇 hanti⟩

end Main

end StrataGlue

end

end NeronModelInfra.SmootheningIteration

namespace NeronModelInfra

open NeronModelInfra.SmootheningIteration
open scoped NeronModelInfra.SmootheningIteration.StrataGlue

theorem
    exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (t : ℕ) (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i) (hYt : Y t =
      ∅)
    (hYs : ∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType v ∧ QuasiCompact v ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R
        K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ ⟨(Y 0)ᶜ, (hY 0).isOpen_compl⟩) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
        Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃! x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f), x₁.1 ≫ v
            = x.1) ∧
      (∀ (i : ℕ), i < t → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ (U : Set X), y ∉ Y (i +
        1)) →
        ∀ (π : R), IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ (W : X₁.Opens)
          (e : (W : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X)
                ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))),
          W.ι ≫ v = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X)
                ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec ∧
          ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
            Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
            ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
              x₁.1 (IsLocalRing.closedPoint R') ∈ W) := by
  have hYs' : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R :=
    fun m y hy => hYs y ((antitone_nat_of_succ_le hanti) (Nat.zero_le m) hy)
  obtain ⟨𝔓⟩ := StrataGlue.nonempty_prev f Y hY hanti hYs' t
  refine ⟨𝔓.Q, 𝔓.w, 𝔓.sep, 𝔓.loft, 𝔓.qc, StrataGlue.isIso_genericFibre hY hYs' 𝔓.w 𝔓.isoC K,
    𝔓.isoC, ?_,
    fun i hi U hU hUY π hπ => 𝔓.chart i hi U hU hUY π hπ⟩
  intro R' _ _ _ _ hR' x
  obtain ⟨x₁, hx₁⟩ := 𝔓.lift R' hR' x.1 x.2 (by rw [hYt]; exact Set.notMem_empty _)
  refine ⟨⟨x₁, by rw [← Category.assoc, hx₁]; exact x.2⟩, hx₁, ?_⟩
  rintro ⟨x₂, hx₂'⟩ hx₂
  exact Subtype.ext (StrataGlue.lift_unique hY hYs' 𝔓.w 𝔓.isoC R' hR' x₂ x₁ (hx₂.trans hx₁.symm)
    hx₂')

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra.SmootheningIteration

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

namespace Stratification

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}} (f :
    X ⟶ Spec (CommRingCat.of R))

/-- A special point realized over an index-one extension of valuation rings. -/
def IsIdxSpec (y : X) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
    Algebra R R')
    (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1
      (IsLocalRing.closedPoint R') = y

/-- Smoothness and differential freeness at a point of an affine stratum. -/
def GoodClause (C : Set X) (U : X.Opens) (hU : IsAffineOpen U) (y : X) (hyU : y ∈ U) : Prop :=
  let : Algebra R Γ(X, U) := f.sectionsAlgebra U
  let J : Ideal Γ(X, U) :=
    PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
  ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
    𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
    (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
      [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
      Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
    (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
      Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])

/-- The points admitting a smooth and differentially free chart on the stratum. -/
def Good (C : Set X) : Set X := {y | ∃ (U : X.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U),
    GoodClause f C U hU y hyU}

/-- The remaining locus after removing the good points of its closure. -/
def step (S : Set X) : Set X := S \ Good f (closure S)

theorem step_subset (S : Set X) : step f S ⊆ S := Set.sdiff_subset

theorem iterate_step_subset (S : Set X) (n : ℕ) : (step f)^[n] S ⊆ S := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (step_subset f _).trans ih

theorem iterate_step_succ_subset (S : Set X) (n : ℕ) : (step f)^[n + 1] S ⊆ (step f)^[n] S := by
  rw [Function.iterate_succ_apply']; exact step_subset f _

end Stratification

end NeronModelInfra.SmootheningIteration

namespace NeronModelInfra

open NeronModelInfra.SmootheningIteration
open NeronModelInfra.SmootheningIteration.Stratification

theorem
    exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (_hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (t : ℕ) (Y : ℕ → Set X), (∀ i, IsClosed (Y i)) ∧ (∀ i, Y (i + 1) ⊆ Y i) ∧ Y t = ∅ ∧
      (∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) ∧ (∀ y ∈ Y 0, y ∉ (f.smoothLocus : Set X)) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∉ (f.smoothLocus : Set X) →
          x.1 (IsLocalRing.closedPoint R') ∈ Y 0) ∧
      (∀ (i : ℕ), i < t → ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
        [Algebra R R'] [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∈ Y i → x.1 (IsLocalRing.closedPoint R') ∉ Y (i + 1) →
          ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U),
            (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) ∧
            let : Algebra R Γ(X, U) :=
              ((X.presheaf.map (homOfLE le_top).op).hom.comp
                (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
            let J : Ideal Γ(X, U) :=
              PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈
                Y i})
            (∀ g : Γ(X, U),
              (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R'']
                [Algebra R R'']
                [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
                ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
                  g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J) ∧
            (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
              𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'),
                hxU⟩).asIdeal →
              (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
                [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
                Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
              (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
                Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]))) := by
  classical
  let S₀ : Set X := {y | IsIdxSpec f y ∧ y ∉ (f.smoothLocus : Set X)}
  let Sq : ℕ → Set X := fun n => (step f)^[n] S₀
  have hSq_succ : ∀ n, Sq (n + 1) = step f (Sq n) := fun n => Function.iterate_succ_apply' (step
    f) n S₀
  have hidx_k : ∀ y : X, IsIdxSpec f y → f y = IsLocalRing.closedPoint R := by
    rintro y ⟨R', _, _, _, _, _, _, x, rfl⟩
    change (x.1 ≫ f).base (IsLocalRing.closedPoint R') = _
    rw [x.2]
    exact IsLocalRing.comap_closedPoint (algebraMap R R')
  have hSqidx : ∀ n, ∀ y ∈ Sq n, IsIdxSpec f y := fun n y hy => (iterate_step_subset f S₀ n hy).1
  have hSqk : ∀ n, ∀ y ∈ Sq n, f y = IsLocalRing.closedPoint R := fun n y hy => hidx_k y (hSqidx n
    y hy)
  have hSq_shape : ∀ n, ∀ s ∈ Sq n, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ :
    IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1
        (IsLocalRing.closedPoint R') = s :=
    fun n s hs => hSqidx n s hs
  have hfib : IsClosed {y : X | f y = IsLocalRing.closedPoint R} := by
    have h1 : IsClosed ({IsLocalRing.closedPoint R} : Set (Spec (CommRingCat.of R))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal R)
    exact h1.preimage f.base.hom.continuous
  have hYk : ∀ n, ∀ y ∈ closure (Sq n), f y = IsLocalRing.closedPoint R := fun n =>
    (hfib.closure_subset_iff.mpr (fun y hy => hSqk n y hy))
  have hY0sm : ∀ y ∈ closure (Sq 0), y ∉ (f.smoothLocus : Set X) := by
    have : closure (Sq 0) ⊆ (f.smoothLocus : Set X)ᶜ :=
      (f.smoothLocus.2.isClosed_compl).closure_subset_iff.mpr (fun y hy => hy.2)
    exact fun y hy => this hy
  have hstrict : ∀ S : Set X, S ⊆ S₀ → S.Nonempty → ¬ closure S ⊆ closure (step f S) := by
    intro S hS ⟨s, hs⟩ hle
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ s) isOpen_univ
    obtain ⟨W, hWU, hWne, hWgood⟩ :=
      NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus f S
        (fun s hs => (hS hs).1) (fun s hs => hidx_k s (hS hs).1) U hU
    obtain ⟨w, hwS, hwW⟩ := hWne ⟨s, subset_closure hs, hsU⟩
    have hmiss : closure (step f S) ⊆ (W : Set X)ᶜ := by
      refine (W.2.isClosed_compl).closure_subset_iff.mpr ?_
      rintro y ⟨hyS, hyngood⟩ hyW
      exact hyngood ⟨U, hU, hWU hyW, (hWgood y (hWU hyW) (subset_closure hyS)).mp hyW⟩
    exact hmiss (hle hwS) hwW
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hterm : ∃ t : ℕ, Sq t = ∅ := by
    by_contra hne
    push Not at hne
    have hchain : ∀ n, (⟨closure (Sq (n + 1)), isClosed_closure⟩ : TopologicalSpace.Closeds X) <
        ⟨closure (Sq n), isClosed_closure⟩ := by
      intro n
      refine lt_of_le_of_ne ?_ ?_
      · exact closure_mono (by rw [hSq_succ]; exact step_subset f _)
      · intro h
        have h' : closure (Sq n) ⊆ closure (Sq (n + 1)) := by
          have := congrArg (fun C : TopologicalSpace.Closeds X => (C : Set X)) h
          exact this.symm.subset
        rw [hSq_succ] at h'
        exact hstrict (Sq n) (iterate_step_subset f S₀ n) (hne n) h'
    exact (RelEmbedding.natGT (fun n => (⟨closure (Sq n), isClosed_closure⟩ :
      TopologicalSpace.Closeds X)) hchain).not_wellFounded
      wellFounded_lt
  obtain ⟨t, ht⟩ := hterm
  have hmemSq : ∀ (i : ℕ) (y : X), y ∈ S₀ → y ∈ closure (Sq i) → y ∈ Sq i := by
    intro i
    induction i with
    | zero => exact fun y hy _ => hy
    | succ j ih =>
      intro y hy0 hyY
      have hyj : y ∈ Sq j := ih y hy0 (closure_mono (by rw [hSq_succ]; exact step_subset f _) hyY)
      rw [hSq_succ]
      refine ⟨hyj, ?_⟩
      rintro ⟨U, hU, hyU, hgood⟩
      obtain ⟨W, hWU, -, hWgood⟩ :=
        NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus f (Sq j)
          (hSq_shape j) (hSqk j) U hU
      have hyW : y ∈ W := (hWgood y hyU (subset_closure hyj)).mpr hgood
      have hmiss : closure (step f (Sq j)) ⊆ (W : Set X)ᶜ := by
        refine (W.2.isClosed_compl).closure_subset_iff.mpr ?_
        rintro y' ⟨hy'S, hy'ngood⟩ hy'W
        exact hy'ngood ⟨U, hU, hWU hy'W, (hWgood y' (hWU hy'W) (subset_closure hy'S)).mp hy'W⟩
      rw [hSq_succ] at hyY
      exact hmiss hyY hyW
  have hYempty : closure (Sq t) = ∅ := by rw [ht, closure_empty]
  refine ⟨t, fun n => closure (Sq n), fun n => isClosed_closure,
    fun n => closure_mono (by rw [hSq_succ]; exact step_subset f _), hYempty,
    hYk 0, hY0sm, ?_, ?_⟩
  · intro R' _ _ _ _ _ hR' x hx
    exact subset_closure ⟨⟨R', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hR', x, rfl⟩, hx⟩
  · intro i hi R' _ _ _ _ _ hR' x hyi hyi1
    set y := x.1 (IsLocalRing.closedPoint R') with hy
    have hy0 : y ∈ S₀ := ⟨⟨R', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hR', x, rfl⟩,
      hY0sm y (closure_mono (iterate_step_subset f S₀ i) hyi)⟩
    have hySi : y ∈ Sq i := hmemSq i y hy0 hyi
    have hgood : y ∈ Good f (closure (Sq i)) := by
      by_contra h
      exact hyi1 (subset_closure (by rw [hSq_succ]; exact ⟨hySi, h⟩))
    obtain ⟨U, hU, hyU, hgoodU⟩ := hgood
    let algU : Algebra R Γ(X, U) := f.sectionsAlgebra U
    obtain ⟨h, hhvan, hhy⟩ : ∃ h : Γ(X, U), (∀ z : U, (z : X) ∈ closure (Sq (i + 1)) → h ∈
      (hU.primeIdealOf z).asIdeal) ∧
        h ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      let T : Set (PrimeSpectrum Γ(X, U)) := (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X)
        ∈ closure (Sq (i + 1))}
      have hT : IsClosed T := by
        have hcl : IsClosed {z : U | (z : X) ∈ closure (Sq (i + 1))} := isClosed_closure.preimage
          continuous_subtype_val
        have : T = Scheme.homeoOfIso hU.isoSpec '' {z : U | (z : X) ∈ closure (Sq (i + 1))} := by
          ext q
          simp only [T, Set.mem_image, Scheme.homeoOfIso_apply]
          rfl
        rw [this]
        exact (Scheme.homeoOfIso hU.isoSpec).isClosed_image.mpr hcl
      have hyT : hU.primeIdealOf ⟨y, hyU⟩ ∉ T := by
        rintro ⟨z, hz, hzy⟩
        apply hyi1
        have : (z : X) = y := by
          have := congrArg (fun q => hU.fromSpec.base q) hzy
          simpa only [IsAffineOpen.fromSpec_primeIdealOf] using this
        rw [← this]; exact hz
      have hnot : ¬ ((PrimeSpectrum.vanishingIdeal T : Ideal Γ(X, U)) ≤ (hU.primeIdealOf ⟨y,
        hyU⟩).asIdeal) := by
        intro hle
        apply hyT
        have : hU.primeIdealOf ⟨y, hyU⟩ ∈ PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal T
          : Set Γ(X, U)) := hle
        rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hT.closure_eq] at this
      obtain ⟨h, hhI, hhy⟩ := Set.not_subset.mp hnot
      refine ⟨h, fun z hz => ?_, hhy⟩
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hhI _ ⟨z, hz, rfl⟩
    have hyh : y ∈ X.basicOpen h := (mem_basicOpen_iff_notMem hU h y hyU).mpr hhy
    refine ⟨X.basicOpen h, hU.basicOpen h, hyh, ?_, ?_, ?_⟩
    · intro z hz hz'
      have hzU : z ∈ U := X.basicOpen_le h hz
      exact (mem_basicOpen_iff_notMem hU h z hzU).mp hz (hhvan ⟨z, hzU⟩ hz')
    · exact NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom
        f (Sq i) (hSq_shape i) (X.basicOpen h) (hU.basicOpen h)
    · exact NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
        f (closure (Sq i)) (hYk i) U hU h y hyU hyh hgoodU

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra.SmootheningIteration

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

open TensorProduct IsLocalRing

noncomputable section

namespace DefectDrop

theorem exists_lift_of_apply_closedPoint_mem {U X : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g]
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ Set.range g) :
    ∃ a' : Spec (CommRingCat.of R') ⟶ U, a' ≫ g = a := by
  have hrange : Set.range a ⊆ Set.range g := by
    rintro _ ⟨z, rfl⟩
    have hz : a z ⤳ a (IsLocalRing.closedPoint R') :=
      (IsLocalRing.specializes_closedPoint z).map a.continuous
    exact g.isOpenEmbedding.isOpen_range.stableUnderGeneralization hz h
  exact ⟨IsOpenImmersion.lift g a hrange, IsOpenImmersion.lift_fac _ _ _⟩

section Chart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (U : X.Opens) (hU : IsAffineOpen U)

theorem fromSpec_comp_eq :
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U) (self := f.sectionsAlgebra
      U))) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (V := U) (U := ⊤) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  congr 1

end Chart

section GenericPoint

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

theorem mem_smoothLocus_of_apply_eq_bot {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K)))
    (y : X) (hy : f y = (⊥ : PrimeSpectrum R)) : y ∈ f.smoothLocus := by
  have : IsNoetherianRing (CommRingCat.of R) := inferInstanceAs (IsNoetherianRing R)
  have : Flat (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq, HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap R K).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  have hpt : f y = (specGenericFibreInclusion R K) (⊥ : PrimeSpectrum K) := by
    rw [hy, specGenericFibreInclusion_eq]
    change (⊥ : PrimeSpectrum R) = PrimeSpectrum.comap (algebraMap R K) ⊥
    ext1
    change (⊥ : Ideal R) = Ideal.comap (algebraMap R K) ⊥
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := specGenericFibreInclusion R K) y (⊥ : PrimeSpectrum K) hpt
  have hle := AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback
    (IsPullback.of_hasPullback f (specGenericFibreInclusion R K))
  have : Smooth (pullback.snd f (specGenericFibreInclusion R K)) := hK
  have hz' : z ∈ (pullback.snd f (specGenericFibreInclusion R K)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have := hle hz'
  rwa [Scheme.Hom.mem_preimage, hz] at this

theorem apply_bot_mem_smoothLocus (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K)))
    {R' : Type u} [CommRing R'] [IsDomain R'] [Algebra R R'] (hinj : Function.Injective
      (algebraMap R R'))
    (a : Spec (CommRingCat.of R') ⟶ X) (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R
      R'))) :
    a (⊥ : PrimeSpectrum R') ∈ f.smoothLocus := by
  apply mem_smoothLocus_of_apply_eq_bot K f hK
  refine (congrArg (fun m : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) =>
    m (⊥ : PrimeSpectrum R')) ha).trans ?_
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R R') ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hinj

end GenericPoint

section SmoothLocusChart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [LocallyOfFinitePresentation f] (U : X.Opens) (hU : IsAffineOpen U)

theorem mem_smoothLocus_iff_mem_algebra_smoothLocus (x : X) (hx : x ∈ U) :
    let : Algebra R Γ(X, U) := f.sectionsAlgebra U
    x ∈ f.smoothLocus ↔
      hU.primeIdealOf ⟨x, hx⟩ ∈ Algebra.smoothLocus R Γ(X, U) := by
  intro iR
  let iΓ : Algebra Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U) := (f.appLE ⊤ U le_top).hom.toAlgebra
  let iRΓ : Algebra R Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of
    R)).inv.hom.toAlgebra
  have : IsScalarTower R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [Scheme.Hom.mem_smoothLocus,
    AlgebraicGeometry.formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) U hU le_top hx]
  change Algebra.IsSmoothAt Γ(Spec (CommRingCat.of R), ⊤) (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
    Algebra.IsSmoothAt R (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : IsLocalization.Away (1 : R) Γ(Spec (CommRingCat.of R), ⊤) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  have : Algebra.FormallyEtale R Γ(Spec (CommRingCat.of R), ⊤) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : R))
  exact (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Γ(Spec (CommRingCat.of R),
    ⊤))).symm

end SmoothLocusChart

end DefectDrop

end

end NeronModelInfra.SmootheningIteration

namespace NeronModelInfra

open NeronModelInfra.SmootheningIteration
open NeronModelInfra.SmootheningIteration.DefectDrop

theorem
    exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType (v ≫ f) ∧ QuasiCompact (v ≫ f) ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R
        K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ f.smoothLocus) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
            x₁.1 ≫ v = x.1) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
          smoothnessDefect (v ≫ f) x₁.1 + 1 ≤ max 1 (smoothnessDefect f (x₁.1 ≫ v)))  := by
  classical
  obtain ⟨t, Y, hYc, hanti, hYt, hYs, hYsm, hY0, hchart⟩ :=
    NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd K f hK
  obtain ⟨X₁, v, hsep, hlft, hqc, hiso, hisoY, hlift, hW⟩ :=
    exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
      K f t Y hYc hanti hYt hYs
  have : IsSeparated v := hsep
  have : LocallyOfFiniteType v := hlft
  have : QuasiCompact v := hqc
  refine ⟨X₁, v, hsep, inferInstance, inferInstance, hiso, ?_, ?_, ?_⟩
  · exact StrataGlue.isIso_morphismRestrict_of_le v hisoY
      (fun y hy hy0 => hYsm y hy0 hy)
  · intro R' _ _ _ _ _ hR' x
    obtain ⟨x₁, hx₁, -⟩ := hlift R' hR'.map_maximalIdeal x
    exact ⟨x₁, hx₁⟩
  · intro R' _ _ _ _ _ hR' x₁
    let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f :=
      ⟨x₁.1 ≫ v, by rw [Category.assoc]; exact x₁.2⟩
    have hinj : Function.Injective (algebraMap R R') :=
      StrataGlue.algebraMap_injective hR'.map_maximalIdeal
    have hgen : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') ∈ f.smoothLocus :=
      apply_bot_mem_smoothLocus K f hK hinj (x₁.1 ≫ v) x.2
    obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπ : maximalIdeal R = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr
    set s : X := (x₁.1 ≫ v) (IsLocalRing.closedPoint R') with hs_def
    by_cases hs : s ∈ Y 0
    swap
    · have hsm : s ∈ (f.smoothLocus : Set X) := by
        by_contra h; exact hs (hY0 R' hR' x h)
      have h0 : smoothnessDefect f (x₁.1 ≫ v) = 0 :=
        (NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus f (x₁.1 ≫
          v) hgen).mpr
          hsm
      let V : X.Opens := ⟨(Y 0)ᶜ, (hYc 0).isOpen_compl⟩
      have : IsIso (v ∣_ V) := hisoY
      have hx₁V : x₁.1 (IsLocalRing.closedPoint R') ∈ Set.range (v ⁻¹ᵁ V).ι := by
        rw [Scheme.Opens.range_ι]; exact hs
      obtain ⟨y, hy⟩ := exists_lift_of_apply_closedPoint_mem (v ⁻¹ᵁ V).ι x₁.1 hx₁V
      have e1 : smoothnessDefect (v ≫ f) x₁.1 = smoothnessDefect f (x₁.1 ≫ v) := by
        rw [← hy, ← smoothnessDefect_comp_eq ((v ⁻¹ᵁ V).ι) (v ≫ f) y]
        have hfac : (v ⁻¹ᵁ V).ι ≫ v ≫ f = (v ∣_ V) ≫ (V.ι ≫ f) := by
          rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
        rw [hfac, smoothnessDefect_comp_eq (v ∣_ V) (V.ι ≫ f) y, smoothnessDefect_comp_eq V.ι f (y
          ≫ v ∣_ V),
          Category.assoc, Category.assoc, morphismRestrict_ι]
      rw [e1, h0]
      simp only [zero_add, max_eq_left (show (0 : ℕ∞) ≤ 1 from zero_le), le_refl]
    · have hex : ∃ j, s ∉ Y j := ⟨t, by rw [hYt]; exact Set.notMem_empty s⟩
      have hj : s ∉ Y (Nat.find hex) := Nat.find_spec hex
      have hj0 : Nat.find hex ≠ 0 := fun h => by rw [h] at hj; exact hj hs
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hsi : s ∈ Y i := by
        by_contra h; exact Nat.find_min hex (show i < Nat.find hex by omega) h
      have hsi1 : s ∉ Y (i + 1) := by have h' := hj; rwa [hi] at h'
      have hit : i < t := by
        have := Nat.find_le (h := hex) (n := t) (by rw [hYt]; exact Set.notMem_empty s)
        omega
      obtain ⟨U, hU, hxU, hUY, hN, hgood⟩ := hchart i hit R' hR' x hsi hsi1
      obtain ⟨W, e, hWv, hWpt⟩ := hW i hit U hU hUY π hπ
      have hx₁W : x₁.1 (IsLocalRing.closedPoint R') ∈ W := hWpt R' hR'.map_maximalIdeal x₁ hsi hxU
      let iRA : Algebra R Γ(X, U) := f.sectionsAlgebra U
      let J : Ideal Γ(X, U) :=
        PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i})
      let A' : Type u := AffineDilatation.Ring J (algebraMap R Γ(X, U) π)
      let eA : (W : Scheme.{u}) ≅ Spec (CommRingCat.of A') := e
      let bA : Spec (CommRingCat.of A') ⟶ Spec Γ(X, U) :=
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) A'))
      have hWvA : W.ι ≫ v = eA.hom ≫ bA ≫ hU.fromSpec := hWv
      obtain ⟨a, ha⟩ := exists_lift_of_apply_closedPoint_mem hU.fromSpec (x₁.1 ≫ v)
        (by rw [IsAffineOpen.range_fromSpec]; exact hxU)
      have hfS := fromSpec_comp_eq f U hU
      obtain ⟨y₁, hy₁⟩ := exists_lift_of_apply_closedPoint_mem W.ι x₁.1 (by
        rw [Scheme.Opens.range_ι]
        exact hx₁W)
      set z : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of A') := y₁ ≫ eA.hom with hz
      have hza : z ≫ bA = a := by
        apply (cancel_mono hU.fromSpec).mp
        calc
          (z ≫ bA) ≫ hU.fromSpec = y₁ ≫ (eA.hom ≫ bA ≫ hU.fromSpec) := by
            rw [hz]; simp only [Category.assoc]
          _ = y₁ ≫ (W.ι ≫ v) := congrArg (y₁ ≫ ·) hWvA.symm
          _ = a ≫ hU.fromSpec := by rw [← Category.assoc, hy₁, ha]
      set φr := Spec.preimage a with hφr
      set φ'r := Spec.preimage z with hφ'r
      have haφ : Spec.map φr = a := Spec.map_preimage a
      have hzφ : Spec.map φ'r = z := Spec.map_preimage z
      have hcompat : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫ φr = CommRingCat.ofHom (algebraMap
        R R') := by
        apply Spec.map_injective
        rw [Spec.map_comp, haφ, ← hfS, ← Category.assoc, ha, Category.assoc]
        exact x₁.2
      have hcompat' : CommRingCat.ofHom (algebraMap Γ(X, U) A') ≫ φ'r = φr := by
        apply Spec.map_injective
        rw [Spec.map_comp, hzφ, hza, haφ]
      let φ : Γ(X, U) →ₐ[R] R' := AlgHom.mk φr.hom fun r => by
        exact congrArg (fun ψ : CommRingCat.of R ⟶ CommRingCat.of R' => ψ.hom r) hcompat
      let φ' : A' →ₐ[R] R' := AlgHom.mk φ'r.hom fun r => by
        have h1 := congrArg (fun ψ => ψ.hom (algebraMap R Γ(X, U) r)) hcompat'
        have h2 := congrArg (fun ψ => ψ.hom r) hcompat
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply] at h1 h2
        change φ'r.hom (algebraMap R A' r) = algebraMap R R' r
        rw [IsScalarTower.algebraMap_apply R Γ(X, U) A' r]
        exact h1.trans h2
      have hφ' : ∀ b : Γ(X, U), φ' (algebraMap Γ(X, U) A' b) = φ b := fun b =>
        congrArg (fun ψ : Γ(X, U) ⟶ CommRingCat.of R' => ψ.hom b) hcompat'
      have hsU : hU.fromSpec (a (IsLocalRing.closedPoint R')) = s :=
        congrArg (fun m : Spec (CommRingCat.of R') ⟶ X => m (IsLocalRing.closedPoint R')) ha
      have h𝔭 : hU.primeIdealOf ⟨s, hxU⟩ = a (IsLocalRing.closedPoint R') := by
        apply hU.fromSpec.isOpenEmbedding.injective
        exact (hU.fromSpec_primeIdealOf ⟨s, hxU⟩).trans hsU.symm
      have h𝔭' : (hU.primeIdealOf ⟨s, hxU⟩).asIdeal = (maximalIdeal R').comap φ := by
        rw [h𝔭, ← haφ]; rfl
      have hJ𝔭 : J ≤ (hU.primeIdealOf ⟨s, hxU⟩).asIdeal := fun g hg =>
        (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg _ ⟨⟨s, hxU⟩, hsi, rfl⟩
      let 𝔮 : Ideal (Γ(X, U) ⧸ J) := (hU.primeIdealOf ⟨s, hxU⟩).asIdeal.map (Ideal.Quotient.mk J)
      have h𝔮p : 𝔮.IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h𝔮c : 𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨s, hxU⟩).asIdeal := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ←
          RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr hJ𝔭]
      have hπJ : algebraMap R Γ(X, U) π ∈ J := by
        rw [PrimeSpectrum.mem_vanishingIdeal]
        rintro _ ⟨y, hy, rfl⟩
        have hy0 : (y : X) ∈ Y 0 := (antitone_nat_of_succ_le hanti (Nat.zero_le i)) hy
        let pt : Spec Γ(X, U) := hU.primeIdealOf y
        have h1 : (hU.fromSpec ≫ f) pt = IsLocalRing.closedPoint R :=
          (Scheme.Hom.comp_apply hU.fromSpec f pt).trans
            ((congrArg f (hU.fromSpec_primeIdealOf y)).trans (hYs _ hy0))
        rw [hfS] at h1
        have h2 : π ∈ ((Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (hU.primeIdealOf
          y)).asIdeal := by
          rw [h1]
          change π ∈ maximalIdeal R
          rw [hπ]; exact Ideal.mem_span_singleton_self π
        exact h2
      have hle : maximalIdeal R ≤ J.comap (algebraMap R Γ(X, U)) := by
        rw [hπ, Ideal.span_singleton_le_iff_mem]; exact hπJ
      let ik : Algebra (ResidueField R) (Γ(X, U) ⧸ J) := (Ideal.quotientMap J (algebraMap R Γ(X,
        U)) hle).toAlgebra
      have hresTower : IsScalarTower R (ResidueField R) (Γ(X, U) ⧸ J) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => rfl)
      obtain ⟨hsmooth, hfree⟩ := hgood 𝔮 h𝔮c
      have hbotU : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') ∈ U := by
        have hb0 : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') = hU.fromSpec (a (⊥ : PrimeSpectrum R')) :=
          (congrArg (fun m : Spec (CommRingCat.of R') ⟶ X => m (⊥ : PrimeSpectrum R')) ha).symm
        have hr := hU.range_fromSpec
        rw [Set.ext_iff] at hr
        rw [hb0]
        exact (hr _).mp ⟨_, rfl⟩
      have hgen' : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈ Algebra.smoothLocus R
        Γ(X, U) := by
        have key := (mem_smoothLocus_iff_mem_algebra_smoothLocus f U hU _ hbotU).mp hgen
        have hpt : hU.primeIdealOf ⟨(x₁.1 ≫ v) (⊥ : PrimeSpectrum R'), hbotU⟩ = a (⊥ :
          PrimeSpectrum R') := by
          let pt : Spec (CommRingCat.of R') := (⊥ : PrimeSpectrum R')
          have hb : hU.fromSpec (a pt) = (x₁.1 ≫ v) pt :=
            (Scheme.Hom.comp_apply a hU.fromSpec pt).symm.trans
              (congrArg (fun m : Spec (CommRingCat.of R') ⟶ X => m pt) ha)
          apply hU.fromSpec.isOpenEmbedding.injective
          exact (hU.fromSpec_primeIdealOf _).trans hb.symm
        rw [hpt, ← haφ] at key
        exact key
      have : Algebra.FiniteType R Γ(X, U) := finiteType_sectionsAlgebra f U hU
      have key :=
        @NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
          R _ _ _ π hπ Γ(X, U) _ iRA inferInstance J hπJ ik hresTower
          hN R' _ _ _ _ _ hR' φ hgen' 𝔮 h𝔮p (by rw [h𝔮c, h𝔭'])
          (@hsmooth ik hresTower) hfree φ' hφ'
      have e_right : smoothnessDefect f (x₁.1 ≫ v) =
          smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))))
            (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
        rw [← ha, ← smoothnessDefect_comp_eq hU.fromSpec f a, hfS, ← haφ]
        rfl
      have hsc : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫ CommRingCat.ofHom (algebraMap Γ(X, U)
        A') =
          CommRingCat.ofHom (algebraMap R A') := by
        rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R Γ(X, U) A']
      have e_left : smoothnessDefect (v ≫ f) x₁.1 =
          smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A')))
            (Spec.map (CommRingCat.ofHom φ'.toRingHom)) := by
        have hbAf : bA ≫ hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A')) :=
          calc
            bA ≫ hU.fromSpec ≫ f = bA ≫ Spec.map (CommRingCat.ofHom
                (algebraMap R Γ(X, U))) := congrArg (bA ≫ ·) hfS
            _ = Spec.map (CommRingCat.ofHom (algebraMap R A')) :=
              (Spec.map_comp _ _).symm.trans (congrArg Spec.map hsc)
        calc
          smoothnessDefect (v ≫ f) x₁.1 =
              smoothnessDefect (W.ι ≫ v ≫ f) y₁ := by
                rw [smoothnessDefect_comp_eq W.ι (v ≫ f) y₁, hy₁]
          _ = smoothnessDefect (eA.hom ≫ (bA ≫ hU.fromSpec ≫ f)) y₁ := by
            rw [← Category.assoc, hWvA]; simp only [Category.assoc]
          _ = smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A'))) z := by
            rw [smoothnessDefect_comp_eq eA.hom _ y₁, hbAf, ← hz]
          _ = _ := by rw [← hzφ]; rfl
      rw [e_left, e_right]
      exact key

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra.SmootheningIteration

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TopologicalSpace

namespace Smoothening

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual morphism on generic fibres induced by a morphism of models. -/
noncomputable def gfm {X' X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    pullback (u ≫ f) (specGenericFibreInclusion R K) ⟶ pullback f (specGenericFibreInclusion R K) :=
  pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
    (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := scoped simp)]
theorem gfm_fst {X' X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfm K f u ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst (u ≫ f) (specGenericFibreInclusion R K) ≫ u :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := scoped simp)]
theorem gfm_snd {X' X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfm K f u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd (u ≫ f) (specGenericFibreInclusion R K) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem isIso_gfm_comp {X'' X' X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X)
    (w : X'' ⟶ X') [IsIso (gfm K f u)] [IsIso (gfm K (u ≫ f) w)] : IsIso (gfm K f (w ≫ u)) := by
  have h : gfm K f (w ≫ u) =
      (pullback.congrHom (Category.assoc w u f) rfl).hom ≫ gfm K (u ≫ f) w ≫ gfm K f u := by
    apply pullback.hom_ext
    · simp only [gfm, pullback.congrHom_hom, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc,
        Category.comp_id]
    · simp only [gfm, pullback.congrHom_hom, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [h]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem smooth_snd_of_isIso_gfm {X' X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X)
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) [IsIso (gfm K f u)] :
    Smooth (pullback.snd (u ≫ f) (specGenericFibreInclusion R K)) := by
  have : Smooth (pullback.snd f (specGenericFibreInclusion R K)) := hK
  rw [← gfm_snd K f u]
  infer_instance

theorem smoothen_of_le (n : ℕ) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f],
      Smooth (pullback.snd f (specGenericFibreInclusion R K)) →
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          smoothnessDefect f x.1 ≤ n) →
      ∃ (X' : Scheme.{u}) (u : X' ⟶ X),
        IsSeparated u ∧ LocallyOfFiniteType (u ≫ f) ∧ QuasiCompact (u ≫ f) ∧
        IsIso (gfm K f u) ∧
        (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
          [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
          ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
            ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f),
              x'.1 ≫ u = x.1) ∧
        (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
          [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
          ∀ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f),
            smoothnessDefect (u ≫ f) x'.1 = 0) := by
  induction n with
  | zero =>
    intro X f _ _ hK hδ
    refine ⟨X, 𝟙 X, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.id_comp]; infer_instance
    · rw [Category.id_comp]; infer_instance
    · unfold gfm
      infer_instance
    · intro R' _ _ _ _ _ h1 x
      exact ⟨⟨x.1, by rw [Category.id_comp]; exact x.2⟩, Category.comp_id _⟩
    · intro R' _ _ _ _ _ h1 x'
      obtain ⟨a, ha⟩ := x'
      have hx : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
        rwa [Category.id_comp] at ha
      have h := hδ R' h1 ⟨a, hx⟩
      simp only [Nat.cast_zero, nonpos_iff_eq_zero] at h
      simpa only [Category.id_comp] using h
  | succ n ih =>
    intro X f _ _ hK hδ
    obtain ⟨X₁, v, hsep, hloft, hqc, hiso, -, hlift, hdrop⟩ :=
      NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd K f hK
    have : IsSeparated v := hsep
    have : LocallyOfFiniteType (v ≫ f) := hloft
    have : QuasiCompact (v ≫ f) := hqc
    have : IsIso (gfm K f v) := hiso
    have hK₁ : Smooth (pullback.snd (v ≫ f) (specGenericFibreInclusion R K)) :=
      smooth_snd_of_isIso_gfm K f v hK
    have hδ₁ : ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R
      R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
          smoothnessDefect (v ≫ f) x.1 ≤ n := by
      intro R' _ _ _ _ _ h1 x₁
      have h := hdrop R' h1 x₁
      have hb : smoothnessDefect f (x₁.1 ≫ v) ≤ (n : ℕ∞) + 1 := by
        have := hδ R' h1 ⟨x₁.1 ≫ v, by rw [Category.assoc, x₁.2]⟩
        simpa only [Nat.cast_succ] using this
      have h' : smoothnessDefect (v ≫ f) x₁.1 + 1 ≤ (n : ℕ∞) + 1 :=
        h.trans (max_le le_add_self hb)
      exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h'
    obtain ⟨X', u', hsep', hloft', hqc', hiso', hlift', hzero'⟩ := ih (v ≫ f) hK₁ hδ₁
    have : IsSeparated u' := hsep'
    have : LocallyOfFiniteType (u' ≫ v ≫ f) := hloft'
    have : QuasiCompact (u' ≫ v ≫ f) := hqc'
    have : IsIso (gfm K (v ≫ f) u') := hiso'
    refine ⟨X', u' ≫ v, inferInstance, ?_, ?_, isIso_gfm_comp K f v u', ?_, ?_⟩
    · rw [Category.assoc]; exact hloft'
    · rw [Category.assoc]; exact hqc'
    · intro R' _ _ _ _ _ h1 x
      obtain ⟨x₁, hx₁⟩ := hlift R' h1 x
      obtain ⟨x', hx'⟩ := hlift' R' h1 x₁
      refine ⟨⟨x'.1, by rw [Category.assoc, x'.2]⟩, ?_⟩
      change x'.1 ≫ u' ≫ v = x.1
      rw [← Category.assoc, hx', hx₁]
    · intro R' _ _ _ _ _ h1 x'
      obtain ⟨a, ha⟩ := x'
      have h2 : a ≫ u' ≫ v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
        simpa only [Category.assoc] using ha
      have h := hzero' R' h1 ⟨a, h2⟩
      simpa only [Category.assoc] using h

theorem isIso_gfm_smoothLocus_ι {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType g]
    (hK : Smooth (pullback.snd g (specGenericFibreInclusion R K))) :
    IsIso (gfm K g g.smoothLocus.ι) := by
  set W : X.Opens := g.smoothLocus with hW
  have hrange : Set.range (pullback.fst g (specGenericFibreInclusion R K)) ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply DefectDrop.mem_smoothLocus_of_apply_eq_bot K g hK
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    let q : PrimeSpectrum K := (pullback.snd g (specGenericFibreInclusion R K)) z
    change PrimeSpectrum.comap (algebraMap R K) q = ⊥
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    have : q.asIdeal.IsPrime := q.isPrime
    rw [Ideal.eq_bot_of_prime q.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact StrataGlue.isIso_pullback_map W.ι g _ W
    (StrataGlue.isIso_ι_morphismRestrict W W le_rfl) (fun z => by
      have h := hrange ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at h)

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X' : Scheme.{u}) (u : X' ⟶ X),
      Smooth (u ≫ f) ∧ QuasiCompact (u ≫ f) ∧ IsSeparated u ∧
      IsIso (gfm K f u) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f), x'.1 ≫ u
            = x.1 := by
  have : IsNoetherianRing (CommRingCat.of R) := inferInstanceAs (IsNoetherianRing R)
  obtain ⟨c, hc⟩ := NeronModelInfra.exists_forall_smoothnessDefect_le_of_smooth_pullback_snd K f hK
  have hδ : ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
      [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
      ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
        smoothnessDefect f x.1 ≤ c :=
    fun R' _ _ _ _ _ h1 x => hc R' h1.map_maximalIdeal x
  obtain ⟨X₁, u₁, hsep, hloft, hqc, hiso, hlift, hzero⟩ := smoothen_of_le K c f hK hδ
  have : IsSeparated u₁ := hsep
  have : LocallyOfFiniteType (u₁ ≫ f) := hloft
  have : QuasiCompact (u₁ ≫ f) := hqc
  have : IsIso (gfm K f u₁) := hiso
  set g : X₁ ⟶ Spec (CommRingCat.of R) := u₁ ≫ f with hg
  have hK₁ : Smooth (pullback.snd g (specGenericFibreInclusion R K)) := smooth_snd_of_isIso_gfm K
    f u₁ hK
  set W : X₁.Opens := g.smoothLocus with hW
  refine ⟨W, W.ι ≫ u₁, ?_, ?_, inferInstance, ?_, ?_⟩
  · change Smooth (W.ι ≫ u₁ ≫ f)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self W
  · change QuasiCompact (W.ι ≫ u₁ ≫ f)
    have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian g
    have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace g
    have : IsNoetherian X₁ := ⟨⟩
    have : NoetherianSpace X₁ := inferInstance
    have : CompactSpace (W : Scheme.{u}) := NoetherianSpace.compactSpace (W : Set X₁)
    exact (quasiCompact_iff_compactSpace (W.ι ≫ u₁ ≫ f)).mpr inferInstance
  · have : IsIso (gfm K (u₁ ≫ f) W.ι) := isIso_gfm_smoothLocus_ι K g hK₁
    exact isIso_gfm_comp K f u₁ W.ι
  · intro R' _ _ _ _ _ h1 x
    obtain ⟨x₁, hx₁⟩ := hlift R' h1 x
    have h0 : smoothnessDefect g x₁.1 = 0 := hzero R' h1 x₁
    have hgen : x₁.1 (⊥ : PrimeSpectrum R') ∈ g.smoothLocus :=
      DefectDrop.apply_bot_mem_smoothLocus K g hK₁
        (StrataGlue.algebraMap_injective h1.map_maximalIdeal) x₁.1 x₁.2
    have hcl : x₁.1 (IsLocalRing.closedPoint R') ∈ W :=
      (NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus g x₁.1
        hgen).mp h0
    have hrange : Set.range x₁.1 ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      have htop := Scheme.preimage_eq_top_of_closedPoint_mem x₁.1 hcl
      have : p ∈ x₁.1 ⁻¹ᵁ W := by rw [htop]; trivial
      exact this
    refine ⟨⟨IsOpenImmersion.lift W.ι x₁.1 hrange, ?_⟩, ?_⟩
    · rw [Category.assoc, ← Category.assoc (IsOpenImmersion.lift W.ι x₁.1 hrange),
        IsOpenImmersion.lift_fac,
        ← hg, x₁.2]
    · change IsOpenImmersion.lift W.ι x₁.1 hrange ≫ W.ι ≫ u₁ = x.1
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hx₁]

end Smoothening

end NeronModelInfra.SmootheningIteration

namespace NeronModelInfra

open NeronModelInfra.SmootheningIteration
theorem
    exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X' : Scheme.{u}) (u : X' ⟶ X),
      Smooth (u ≫ f) ∧ QuasiCompact (u ≫ f) ∧ IsSeparated u ∧
      IsIso (pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R
        K) u
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f), x'.1 ≫ u
            = x.1 :=
  Smoothening.main K f hK

end NeronModelInfra
end
