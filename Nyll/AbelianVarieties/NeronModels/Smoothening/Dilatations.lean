/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Tauto
public import Nyll.AbelianVarieties.NeronModels.Smoothening.Charts
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.RingTheory.Differentials.Basic
public import Nyll.SchemeTheory.RingTheory.Dilatation.BaseChange
public import Nyll.SchemeTheory.RingTheory.Dilatation.Basic
public import Nyll.SchemeTheory.RingTheory.Dilatation.UniversalProperty
public import Nyll.SchemeTheory.RingTheory.Ramification.DVRLength
public import Nyll.SchemeTheory.RingTheory.Smooth.Charts

/-! # Global dilatations and decrease of the smoothness defect -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.Dilatations.Construction


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace AffineCharts

section RingLevel

variable {A : Type u} [CommRing A]

open AffineDilatation

open AbelianVarieties.NOSProofs.AffineDilatationRegularity.AffineDilatation.BasicProps
  (isSMulRegular)

theorem mul_left_cancel_algebraMap (I : Ideal A) (a : A) {x y : Ring I a}
    (h : algebraMap A (Ring I a) a * x = algebraMap A (Ring I a) a * y) : x = y := by
  refine isSMulRegular I a (?_ : a • x = a • y)
  rwa [Algebra.smul_def, Algebra.smul_def]

theorem ringHom_ext {C : Type*} [CommRing C] (I : Ideal A) (a : A) (φ ψ : Ring I a →+* C)
    (hA : ∀ r : A, φ (algebraMap A (Ring I a) r) = ψ (algebraMap A (Ring I a) r))
    (hreg : ∀ c c' : C, φ (algebraMap A (Ring I a) a) * c = φ (algebraMap A (Ring I a) a) * c' →
      c = c') :
    φ = ψ := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change φ (divElem I a g hg) = ψ (divElem I a g hg)
      have h := congrArg φ (algebraMap_mul_divElem I a g hg)
      have h' := congrArg ψ (algebraMap_mul_divElem I a g hg)
      rw [map_mul] at h h'
      apply hreg
      rw [h, hA g, ← h', hA a]
  | algebraMap r => exact hA r
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

theorem exists_ringHom {C : Type u} [CommRing C] (I : Ideal A) (a : A) (v : A →+* C)
    (hreg : ∀ c c' : C, v a * c = v a * c' → c = c')
    (hI : ∀ g ∈ I, ∃ c : C, v g = v a * c) :
    ∃ φ : Ring I a →+* C, φ.comp (algebraMap A (Ring I a)) = v := by
  let : Algebra A C := v.toAlgebra
  have hreg' : IsSMulRegular C a := by
    intro c c' h
    exact hreg c c' (by simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h)
  have hI' : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a} := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    obtain ⟨c, hc⟩ := hI g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨c, by rw [mul_comm, RingHom.algebraMap_toAlgebra]; exact hc.symm⟩
  obtain ⟨⟨φ⟩, -⟩ := AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular I a
    hreg' hI'
  exact ⟨φ.toRingHom, RingHom.ext fun r => φ.commutes r⟩

theorem algebraMap_bijective_of_isUnit (I : Ideal A) {a : A} (ha : IsUnit a) :
    Function.Bijective (algebraMap A (Ring I a)) := by
  have hle : Submonoid.powers a ≤ IsUnit.submonoid A := by
    rw [Submonoid.powers_le]; exact ha
  let e : A ≃ₐ[A] Localization.Away a := IsLocalization.atUnits A (Submonoid.powers a) hle
  have he : ∀ r : A, e r = algebraMap A (Localization.Away a) r := fun r => e.commutes r
  constructor
  · intro r s h
    have h' : (algebraMap A (Localization.Away a) r) = algebraMap A (Localization.Away a) s :=
      congrArg Subtype.val h
    rw [← he, ← he] at h'
    exact e.injective h'
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, Subtype.ext ?_⟩
    change algebraMap A (Localization.Away a) (e.symm x) = x
    rw [← he, AlgEquiv.apply_symm_apply]

theorem exists_ringEquiv_of_eq_unit_mul (I : Ideal A) (a b : A) (u : Aˣ) (hb : b = u * a)
    (ha : a ∈ I) :
    ∃ e : Ring I a ≃+* Ring I b,
      e.toRingHom.comp (algebraMap A (Ring I a)) = algebraMap A (Ring I b) := by
  have hb' : a = (u⁻¹ : Aˣ) * b := by rw [hb, ← mul_assoc, Units.inv_mul, one_mul]
  have hbI : b ∈ I := by rw [hb]; exact I.mul_mem_left _ ha
  have reg : ∀ (c d : A) (w : Aˣ), d = w * c → ∀ x y : Ring I c,
      algebraMap A (Ring I c) d * x = algebraMap A (Ring I c) d * y → x = y := by
    intro c d w hd x y h
    rw [hd, map_mul, mul_assoc, mul_assoc] at h
    have h2 := (((Units.map (algebraMap A (Ring I c)).toMonoidHom w).isUnit).mul_left_cancel h)
    exact mul_left_cancel_algebraMap I c h2
  have dvd : ∀ (c d : A) (w : Aˣ), d = w * c → ∀ g ∈ I, ∃ z : Ring I c,
      algebraMap A (Ring I c) g = algebraMap A (Ring I c) d * z := by
    intro c d w hd g hg
    refine ⟨algebraMap A (Ring I c) ((w⁻¹ : Aˣ) : A) * divElem I c g hg, ?_⟩
    rw [hd, map_mul, mul_assoc, ← mul_assoc (algebraMap A _ c), mul_comm (algebraMap A _ c),
      mul_assoc, algebraMap_mul_divElem, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  obtain ⟨φ, hφ⟩ := exists_ringHom I a (algebraMap A (Ring I b)) (reg b a u⁻¹ hb') (dvd b a u⁻¹
    hb')
  obtain ⟨ψ, hψ⟩ := exists_ringHom I b (algebraMap A (Ring I a)) (reg a b u hb) (dvd a b u hb)
  have hφr : ∀ r, φ (algebraMap A _ r) = algebraMap A _ r := fun r => RingHom.congr_fun hφ r
  have hψr : ∀ r, ψ (algebraMap A _ r) = algebraMap A _ r := fun r => RingHom.congr_fun hψ r
  have h1 : ψ.comp φ = RingHom.id _ := by
    apply ringHom_ext I a
    · intro r; simp only [RingHom.comp_apply, hφr, hψr, RingHom.id_apply]
    · intro c c' h
      simp only [RingHom.comp_apply, hφr, hψr] at h
      exact mul_left_cancel_algebraMap I a h
  have h2 : φ.comp ψ = RingHom.id _ := by
    apply ringHom_ext I b
    · intro r; simp only [RingHom.comp_apply, hφr, hψr, RingHom.id_apply]
    · intro c c' h
      simp only [RingHom.comp_apply, hφr, hψr] at h
      exact mul_left_cancel_algebraMap I b h
  refine ⟨RingEquiv.ofRingHom φ ψ h2 h1, ?_⟩
  exact hφ

theorem nonempty_algEquiv_of_eq {I I' : Ideal A} {a a' : A} (hI : I = I') (ha : a = a') :
    Nonempty (Ring I a ≃ₐ[A] Ring I' a') := by
  subst hI ha
  exact ⟨AlgEquiv.refl⟩

theorem exists_ringEquiv_of_eq {I I' : Ideal A} {a a' : A} (hI : I = I') (ha : a = a') :
    ∃ e : Ring I a ≃+* Ring I' a', e.toRingHom.comp (algebraMap A (Ring I a)) = algebraMap A
      (Ring I' a') := by
  subst hI ha
  exact ⟨RingEquiv.refl _, rfl⟩

end RingLevel

section Dictionary

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The global section induced by a base-ring element. -/
noncomputable def secTop (π : R) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)

/-- The restriction of the base section to an open set. -/
noncomputable def sec (π : R) (U : X.Opens) : Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom (secTop f π)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem sec_def (π : R) (U : X.Opens) : sec f π U =
    (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
      R)).inv.hom π)) :=
  rfl

/-- The base-ring map to sections of an open set. -/
noncomputable def toSec (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem toSec_apply (π : R) (U : X.Opens) : toSec f U π = sec f π U := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem map_sec (π : R) {U V : X.Opens} (i : op U ⟶ op V) :
    (X.presheaf.map i).hom (sec f π U) = sec f π V := by
  simp only [sec, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_basicOpen_secTop_iff (π : R) (x : X) :
    x ∈ X.basicOpen (secTop f π) ↔ π ∉ (f x).asIdeal := by
  have h : f ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of
    R)).inv.hom π) =
      X.basicOpen (secTop f π) := Scheme.preimage_basicOpen f _
  rw [← h, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen π (f x)

theorem eq_closedPoint_iff {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (q : PrimeSpectrum R) : q = IsLocalRing.closedPoint R ↔ π ∈ q.asIdeal := by
  constructor
  · rintro rfl
    change π ∈ IsLocalRing.maximalIdeal R
    rw [hπ]; exact Ideal.mem_span_singleton_self π
  · intro h
    apply PrimeSpectrum.ext
    change q.asIdeal = IsLocalRing.maximalIdeal R
    have hle : IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
      rw [hπ, Ideal.span_singleton_le_iff_mem]; exact h
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top hle).symm

theorem mem_basicOpen_secTop_iff' {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (x
  : X) :
    x ∈ X.basicOpen (secTop f π) ↔ f x ≠ IsLocalRing.closedPoint R :=
  (mem_basicOpen_secTop_iff f π x).trans (eq_closedPoint_iff hπ (f x)).symm.not

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem basicOpen_sec (π : R) (U : X.Opens) :
    X.basicOpen (sec f π U) = U ⊓ X.basicOpen (secTop f π) :=
  Scheme.basicOpen_res X _ _

variable {U : X.Opens} (hU : IsAffineOpen U)

theorem primeIdealOf_fromSpec (q : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec q ∈ U) : hU.primeIdealOf ⟨hU.fromSpec q, hq⟩ = q := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem fromSpec_mem (q : PrimeSpectrum Γ(X, U)) : hU.fromSpec q ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩

theorem mem_basicOpen_iff_notMem (s : Γ(X, U)) (y : X) (hy : y ∈ U) :
    y ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen s]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen s
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem sec_mem_asIdeal_iff {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (y : X)
  (hy : y ∈ U) :
    sec f π U ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ↔ f y = IsLocalRing.closedPoint R := by
  have h := mem_basicOpen_iff_notMem hU (sec f π U) y hy
  rw [basicOpen_sec, TopologicalSpace.Opens.mem_inf, mem_basicOpen_secTop_iff' f hπ] at h
  tauto

variable (Y : Set X) (hY : IsClosed Y)

/-- The reduced ideal sheaf cutting out the closed center. -/
noncomputable def idealY : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩

theorem idealY_ideal (V : X.affineOpens) :
    (idealY Y hY).ideal V = PrimeSpectrum.vanishingIdeal (V.2.fromSpec ⁻¹' Y) :=
  Scheme.IdealSheafData.vanishingIdeal_ideal _ _

theorem idealY_ideal' : (idealY Y hY).ideal ⟨U, hU⟩ = PrimeSpectrum.vanishingIdeal (hU.fromSpec
  ⁻¹' Y) :=
  Scheme.IdealSheafData.vanishingIdeal_ideal _ _

theorem mem_iff_ideal_le (y : X) (hy : y ∈ U) :
    y ∈ Y ↔ (idealY Y hY).ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [idealY_ideal', ← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hc : IsClosed (hU.fromSpec ⁻¹' Y) := hY.preimage hU.fromSpec.continuous
  erw [hc.closure_eq, Set.mem_preimage]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ Y
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem vanishingIdeal_image_eq :
    PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}) =
      (idealY Y hY).ideal ⟨U, hU⟩ := by
  rw [idealY_ideal']
  congr 1
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    change hU.fromSpec (hU.primeIdealOf y) ∈ Y
    rw [IsAffineOpen.fromSpec_primeIdealOf]; exact hy
  · intro hq
    exact ⟨⟨hU.fromSpec q, fromSpec_mem hU q⟩, hq, primeIdealOf_fromSpec hU q _⟩

variable (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R)
include hYs

theorem sec_mem_ideal {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    sec f π U ∈ (idealY Y hY).ideal ⟨U, hU⟩ := by
  rw [idealY_ideal', PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have := (sec_mem_asIdeal_iff f hU hπ (hU.fromSpec q) (fromSpec_mem hU q)).mpr (hYs _ hq)
  rwa [primeIdealOf_fromSpec] at this

end Dictionary

section Global

open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite
open _root_.AffineDilatation

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (Y : Set X) (hY : IsClosed Y) (π : R)

/-- The ideal of the center on an affine chart. -/
abbrev idl (U : X.AffineZariskiSite) : Ideal Γ(X, U.1) := (idealY Y hY).ideal ⟨U.1, U.2⟩

/-- The dilatation ring on an affine chart. -/
abbrev objRing (U : X.AffineZariskiSite) : Type u := AffineDilatation.Ring (idl Y hY U) (sec f π
  U.1)

/-- Restriction of affine sections. -/
abbrev res {V U : X.AffineZariskiSite} (h : V ≤ U) : Γ(X, U.1) →+* Γ(X, V.1) :=
  (X.presheaf.map (homOfLE (toOpens_mono h)).op).hom

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem res_sec {V U : X.AffineZariskiSite} (h : V ≤ U) : res h (sec f π U.1) = sec f π V.1 :=
  map_sec f π _

theorem idl_map {V U : X.AffineZariskiSite} (h : V ≤ U) : (idl Y hY U).map (res h) = idl Y hY V :=
  (idealY Y hY).map_ideal (U := ⟨V.1, V.2⟩) (V := ⟨U.1, U.2⟩)
    (Scheme.AffineZariskiSite.toOpens_mono h)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem exists_transition {V U : X.AffineZariskiSite} (h : V ≤ U) :
    ∃ φ : objRing f Y hY π U →+* objRing f Y hY π V,
      φ.comp (algebraMap _ _) = (algebraMap _ (objRing f Y hY π V)).comp (res h) := by
  apply exists_ringHom
  · intro c c' hc
    rw [RingHom.comp_apply, res_sec] at hc
    exact mul_left_cancel_algebraMap _ _ hc
  · intro g hg
    have hg' : res h g ∈ idl Y hY V := by rw [← idl_map Y hY h]; exact Ideal.mem_map_of_mem _ hg
    exact ⟨divElem _ _ (res h g) hg', by
      rw [RingHom.comp_apply, RingHom.comp_apply, res_sec, algebraMap_mul_divElem]⟩

/-- The unique transition map between dilatation rings. -/
def transition {V U : X.AffineZariskiSite} (h : V ≤ U) : objRing f Y hY π U →+* objRing f Y hY π
  V :=
  (exists_transition f Y hY π h).choose

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_algebraMap {V U : X.AffineZariskiSite} (h : V ≤ U) (g : Γ(X, U.1)) :
    transition f Y hY π h (algebraMap _ _ g) = algebraMap _ _ (res h g) :=
  RingHom.congr_fun (exists_transition f Y hY π h).choose_spec g

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_unique {V U : X.AffineZariskiSite} (h : V ≤ U)
    (φ : objRing f Y hY π U →+* objRing f Y hY π V)
    (hφ : ∀ g, φ (algebraMap _ _ g) = algebraMap _ _ (res h g)) : φ = transition f Y hY π h := by
  apply ringHom_ext
  · intro g; rw [hφ, transition_algebraMap]
  · intro c c' hc
    rw [hφ, res_sec] at hc
    exact mul_left_cancel_algebraMap _ _ hc

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_refl (U : X.AffineZariskiSite) : transition f Y hY π (le_refl U) = RingHom.id
  _ := by
  symm; apply transition_unique
  intro g
  have : res (le_refl U) g = g := by
    change (X.presheaf.map (𝟙 (op U.1))).hom g = g
    rw [X.presheaf.map_id]; rfl
  rw [this]; rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_trans {W V U : X.AffineZariskiSite} (h : W ≤ V) (h' : V ≤ U) :
    (transition f Y hY π h).comp (transition f Y hY π h') = transition f Y hY π (h.trans h') := by
  apply transition_unique
  intro g
  rw [RingHom.comp_apply, transition_algebraMap, transition_algebraMap]
  congr 1
  change ((X.presheaf.map (homOfLE _).op) ≫ X.presheaf.map (homOfLE _).op).hom g = _
  rw [← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The diagram of dilatation rings on the affine site. -/
def diagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (objRing f Y hY π (unop U))
  map {U V} i := CommRingCat.ofHom (transition f Y hY π i.unop.le)
  map_id U := by
    ext1
    exact transition_refl f Y hY π (unop U)
  map_comp {U V W} i j := by
    ext1
    exact (transition_trans f Y hY π j.unop.le i.unop.le).symm

/-- The structural natural transformation to dilatation rings. -/
def toDiagram : (toOpensFunctor X).op ⋙ X.presheaf ⟶ diagram f Y hY π where
  app U := CommRingCat.ofHom (algebraMap Γ(X, (unop U).1) (objRing f Y hY π (unop U)))
  naturality {U V} i := by
    ext g
    exact (transition_algebraMap f Y hY π i.unop.le g).symm

variable {π}
variable (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
variable (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R)
include hπ hYs

theorem sec_mem_idl (U : X.AffineZariskiSite) : sec f π U.1 ∈ idl Y hY U :=
  sec_mem_ideal f U.2 Y hY hYs hπ

theorem coequifibered : (toDiagram f Y hY π).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  change @IsLocalization.Away (objRing f Y hY π U) _ (algebraMap Γ(X, U.1) (objRing f Y hY π U) r)
    (objRing f Y hY π (U.basicOpen r)) _ (transition f Y hY π (U.basicOpen_le r)).toAlgebra
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  obtain ⟨φ, hφ⟩ := AffineDilatation.exists_algHom_isLocalization_map (idl Y hY U) (sec f π U.1)
    (sec_mem_idl f Y hY hπ hYs U) (Submonoid.powers r) Γ(X, X.basicOpen r)
  have hI : (idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)) = idl Y hY (U.basicOpen
    r) :=
    (idealY Y hY).map_ideal_basicOpen ⟨U.1, U.2⟩ r
  have ha : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1) = sec f π (U.basicOpen r).1 :=
    map_sec f π _
  obtain ⟨e⟩ := nonempty_algEquiv_of_eq (A := Γ(X, X.basicOpen r)) hI ha
  have key : transition f Y hY π (U.basicOpen_le r) = e.toRingEquiv.toRingHom.comp φ.toRingHom
    := by
    symm
    apply transition_unique
    intro g
    change e (φ (algebraMap _ _ g)) = _
    rw [φ.commutes g, IsScalarTower.algebraMap_apply Γ(X, U.1) Γ(X, X.basicOpen r) _ g, e.commutes]
    rfl
  rw [key]
  let : Algebra (objRing f Y hY π U)
      (AffineDilatation.Ring ((idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)))
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1))) := φ.toRingHom.toAlgebra
  let : Algebra (objRing f Y hY π U) (objRing f Y hY π (U.basicOpen r)) :=
    (e.toRingEquiv.toRingHom.comp φ.toRingHom).toAlgebra
  have hM : Algebra.algebraMapSubmonoid (objRing f Y hY π U) (Submonoid.powers r) =
      Submonoid.powers (algebraMap Γ(X, U.1) (objRing f Y hY π U) r) := Submonoid.map_powers _ _
  have : IsLocalization (Submonoid.powers (algebraMap Γ(X, U.1) (objRing f Y hY π U) r))
      (AffineDilatation.Ring ((idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)))
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1))) := hM ▸ hφ
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers _)
    { e.toRingEquiv with commutes' := fun x => rfl }

/-- Gluing data for the affine dilatation charts. -/
def glueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (coequifibered f Y hY hπ hYs)

scoped instance : ((glueData f Y hY hπ hYs).functor ⋙ Scheme.forget).IsLocallyDirected := by
  have directed (𝒰 : X.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]
      [Quiver.IsThin 𝒰.I₀] (d : 𝒰.RelativeGluingData) :
      (d.functor ⋙ Scheme.forget).IsLocallyDirected := inferInstance
  exact directed (directedCover X) (glueData f Y hY hπ hYs)

/-- The global dilatation obtained by gluing affine charts. -/
def D : Scheme.{u} := (glueData f Y hY hπ hYs).glued

/-- The structural morphism of the global dilatation. -/
def p : D f Y hY hπ hYs ⟶ X := (glueData f Y hY hπ hYs).toBase

/-- The chart map into the global dilatation. -/
def chart (U : X.AffineZariskiSite) : Spec (CommRingCat.of (objRing f Y hY π U)) ⟶ D f Y hY hπ
  hYs :=
  (glueData f Y hY hπ hYs).cover.f U

scoped instance (U : X.AffineZariskiSite) : IsOpenImmersion (chart f Y hY hπ hYs U) :=
  (glueData f Y hY hπ hYs).cover.map_prop U

theorem chart_def (U : X.AffineZariskiSite) :
    chart f Y hY hπ hYs U = colimit.ι (glueData f Y hY hπ hYs).functor U := rfl

theorem chart_p (U : X.AffineZariskiSite) :
    chart f Y hY hπ hYs U ≫ p f Y hY hπ hYs =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫ U.2.fromSpec := by
  exact colimit.ι_desc _ _

theorem preimage_p (U : X.AffineZariskiSite) :
    p f Y hY hπ hYs ⁻¹ᵁ U.1 = (chart f Y hY hπ hYs U).opensRange := by
  ext1
  rw [Scheme.Hom.coe_opensRange]
  have h := (glueData f Y hY hπ hYs).preimage_toBase_eq_range_ι U
  change (p f Y hY hπ hYs) ⁻¹' Set.range (U.1.ι) = Set.range (chart f Y hY hπ hYs U) at h
  rw [Scheme.Opens.range_ι] at h
  exact h

theorem isPullback_chart (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫
      U.2.isoSpec.inv)
      (chart f Y hY hπ hYs U) U.1.ι (p f Y hY hπ hYs) :=
  (glueData f Y hY hπ hYs).isPullback_natTrans_ι_toBase U

theorem restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (U : X.AffineZariskiSite) :
    P (p f Y hY hπ hYs ∣_ U.1) ↔
      P (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U)))) := by
  have h₁ := isPullback_chart f Y hY hπ hYs U
  have h₂ := isPullback_morphismRestrict (p f Y hY hπ hYs) U.1
  let e := h₂.isoIsPullback _ _ h₁
  have he : e.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫
      U.2.isoSpec.inv) = p f Y hY hπ hYs ∣_ U.1 := h₂.isoIsPullback_hom_fst _ _ h₁
  rw [← he, ← Category.assoc, P.cancel_right_of_respectsIso, P.cancel_left_of_respectsIso]

scoped instance isAffineHom_p : IsAffineHom (p f Y hY hπ hYs) := by
  refine ⟨fun U hU => ?_⟩
  rw [preimage_p f Y hY hπ hYs ⟨U, hU⟩]
  have : IsOpenImmersion (chart f Y hY hπ hYs ⟨U, hU⟩) :=
    (glueData f Y hY hπ hYs).cover.map_prop (⟨U, hU⟩ : X.AffineZariskiSite)
  exact isAffineOpen_opensRange _

theorem locallyOfFiniteType_p [LocallyOfFiniteType f] : LocallyOfFiniteType (p f Y hY hπ hYs) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have targetLocal (P : MorphismProperty Scheme.{u})
      (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
      [HasRingHomProperty P Q] : IsZariskiLocalAtTarget P := inferInstance
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    targetLocal _ RingHom.FiniteType
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @LocallyOfFiniteType)]
    exact affineLocally_respectsIso _ RingHom.finiteType_isLocal.respectsIso
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) (fun U :
    X.affineOpens => U.1)
    (iSup_affineOpens_eq_top X) fun U => (restrict_iff f Y hY hπ hYs _ ⟨U.1, U.2⟩).mpr ?_
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap Γ(X, U.1) (objRing f Y hY π ⟨U.1, U.2⟩)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact AffineDilatation.finiteType_of_fg _ _ (IsNoetherian.noetherian _)

omit hYs in
theorem isUnit_sec {U : X.Opens} (hU : ∀ x ∈ U, f x ≠ IsLocalRing.closedPoint R) : IsUnit (sec f
  π U) := by
  have hle : U ≤ X.basicOpen (secTop f π) := fun x hx => (mem_basicOpen_secTop_iff' f hπ x).mpr
    (hU x hx)
  have h1 : IsUnit (sec f π (X.basicOpen (secTop f π))) := RingedSpace.isUnit_res_basicOpen _ _
  have h2 := h1.map (X.presheaf.map (homOfLE hle).op).hom
  rwa [map_sec] at h2

theorem isIso_restrict_affine (U : X.AffineZariskiSite) (hU : ∀ x ∈ U.1, f x ≠
  IsLocalRing.closedPoint R) :
    IsIso (p f Y hY hπ hYs ∣_ U.1) := by
  refine (restrict_iff f Y hY hπ hYs (MorphismProperty.isomorphisms Scheme.{u}) U).mpr ?_
  have hb := algebraMap_bijective_of_isUnit (idl Y hY U) (isUnit_sec f hπ hU)
  change IsIso (Spec.map (RingEquiv.ofBijective _ hb).toCommRingCatIso.hom)
  infer_instance

theorem isIso_restrict (W : X.Opens) (hW : ∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) :
    IsIso (p f Y hY hπ hYs ∣_ W) := by
  have hcov : ⨆ U : {U : X.affineOpens // U.1 ≤ W}, W.ι ⁻¹ᵁ U.1.1 = ⊤ := by
    rw [← top_le_iff]
    rintro w -
    obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open w.2
      W.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hwU⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{u}) _
    hcov ?_
  intro U
  have hUeq : W.ι ''ᵁ (W.ι ⁻¹ᵁ U.1.1) = U.1.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr
      U.2]
  rw [(MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ hUeq)]
  exact isIso_restrict_affine f Y hY hπ hYs ⟨U.1.1, U.1.2⟩ (fun x hx => hW x (U.2 hx))

theorem apply_mem (d : D f Y hY hπ hYs) (hd : f (p f Y hY hπ hYs d) = IsLocalRing.closedPoint R) :
    p f Y hY hπ hYs d ∈ Y := by
  obtain ⟨U₀, z₀, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (glueData f Y hY hπ hYs).functor d
  let U : { V : X.Opens // IsAffineOpen V } := U₀
  let z : Spec (CommRingCat.of (objRing f Y hY π U)) := z₀
  change f (p f Y hY hπ hYs (chart f Y hY hπ hYs U z)) = _ at hd
  change p f Y hY hπ hYs (chart f Y hY hπ hYs U z) ∈ Y
  have h1 : p f Y hY hπ hYs (chart f Y hY hπ hYs U z) =
      U.2.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) z)
        := by
    rw [← Scheme.Hom.comp_apply, chart_p, Scheme.Hom.comp_apply]
  rw [h1] at hd ⊢
  set q := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) z with hq
  have hyU := fromSpec_mem U.2 q
  have hprime : U.2.primeIdealOf ⟨U.2.fromSpec q, hyU⟩ =
      (q : PrimeSpectrum Γ(X, U.1)) := primeIdealOf_fromSpec U.2 q hyU
  rw [← sec_mem_asIdeal_iff f U.2 hπ _ hyU] at hd
  rw [hprime] at hd
  rw [mem_iff_ideal_le U.2 Y hY _ hyU, hprime]
  intro g hg
  have hq' : q.asIdeal = Ideal.comap (algebraMap Γ(X, U.1) (objRing f Y hY π U)) z.asIdeal := by
    rw [hq, Spec.map_apply]; rfl
  rw [hq'] at hd ⊢
  change (algebraMap Γ(X, U.1) (objRing f Y hY π U)) (sec f π U.1) ∈ z.asIdeal at hd
  change (algebraMap Γ(X, U.1) (objRing f Y hY π U)) g ∈ z.asIdeal
  have hmul : (algebraMap Γ(X, U.1) (objRing f Y hY π U)) g =
      (algebraMap Γ(X, U.1) (objRing f Y hY π U)) (sec f π U.1) * divElem (idl Y hY U) (sec f π
        U.1) g hg :=
    (algebraMap_mul_divElem _ _ g hg).symm
  rw [hmul]
  exact z.asIdeal.mul_mem_right _ hd

omit hπ hYs in
theorem exists_specIso {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B]
    [Algebra A B'] (E : B ≃+* B') (hE : E.toRingHom.comp (algebraMap A B) = algebraMap A B') :
    ∃ e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of B'),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B')) = Spec.map (CommRingCat.ofHom
        (algebraMap A B)) := by
  refine ⟨Scheme.Spec.mapIso E.symm.toCommRingCatIso.op, ?_⟩
  change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  rw [← hE]
  ext x
  exact E.symm_apply_apply (algebraMap A B x)

theorem exists_chartIso (U : X.Opens) (hU : IsAffineOpen U) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    ∃ e : (↑(p f Y hY hπ hYs ⁻¹ᵁ U) : Scheme.{u}) ≅
        Spec (CommRingCat.of (AffineDilatation.Ring
          (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈
            Y}))
          ((X.presheaf.map (homOfLE le_top).op).hom
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))))),
      (p f Y hY hπ hYs ⁻¹ᵁ U).ι ≫ p f Y hY hπ hYs = e.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
          (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈
            Y}))
          ((X.presheaf.map (homOfLE le_top).op).hom
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))))) ≫ hU.fromSpec := by
  let U' : X.AffineZariskiSite := ⟨U, hU⟩
  let e₁ : (↑(p f Y hY hπ hYs ⁻¹ᵁ U) : Scheme.{u}) ≅ Spec (CommRingCat.of (objRing f Y hY π U')) :=
    IsOpenImmersion.isoOfRangeEq (p f Y hY hπ hYs ⁻¹ᵁ U).ι (chart f Y hY hπ hYs U') (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
      exact congrArg SetLike.coe (preimage_p f Y hY hπ hYs U'))
  have he₁ : e₁.hom ≫ chart f Y hY hπ hYs U' = (p f Y hY hπ hYs ⁻¹ᵁ U).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hassoc : Associated π ϖ := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hπ, ← hϖ]
  obtain ⟨u, hu⟩ := hassoc
  have hb : sec f ϖ U = (Units.map (toSec f U).toMonoidHom u : Γ(X, U)ˣ) * sec f π U := by
    rw [← toSec_apply, ← toSec_apply, ← hu, map_mul, mul_comm]; rfl
  obtain ⟨e', he'⟩ := exists_ringEquiv_of_eq_unit_mul (idl Y hY U') (sec f π U) (sec f ϖ U) _ hb
    (sec_mem_idl f Y hY hπ hYs U')
  obtain ⟨e'', he''⟩ := exists_ringEquiv_of_eq (A := Γ(X, U)) (a := sec f ϖ U) (a' := sec f ϖ U)
    (vanishingIdeal_image_eq hU Y hY).symm rfl
  let E : objRing f Y hY π U' ≃+* AffineDilatation.Ring
      (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
      (sec f ϖ U) := e'.trans e''
  have hE : E.toRingHom.comp (algebraMap Γ(X, U) (objRing f Y hY π U')) = algebraMap _ _ := by
    have hEt : E.toRingHom = e''.toRingHom.comp e'.toRingHom := RingHom.ext fun x => rfl
    rw [hEt, RingHom.comp_assoc, he', he'']
  obtain ⟨e₂, he₂⟩ := exists_specIso (A := Γ(X, U)) E hE
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  change (p f Y hY hπ hYs ⁻¹ᵁ U).ι ≫ p f Y hY hπ hYs =
    (e₁.hom ≫ e₂.hom) ≫ _ ≫ hU.fromSpec
  rw [← he₁, Category.assoc]
  have hp : chart f Y hY hπ hYs U' ≫ p f Y hY hπ hYs =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (objRing f Y hY π U'))) ≫
        hU.fromSpec := chart_p f Y hY hπ hYs U'
  rw [hp, Category.assoc]
  exact congrArg (e₁.hom ≫ ·)
    ((congrArg (· ≫ hU.fromSpec) he₂).symm.trans (Category.assoc _ _ _))

end Global

end AffineCharts

end

end NeronModelInfra.Dilatations.Construction

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Dilatations.Construction

universe u

theorem exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (Y : Set X) (hY : IsClosed Y) (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R) :
    ∃ (D : Scheme.{u}) (p : D ⟶ X),
      IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)) ∧
      (∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Y) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R),
        IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y :
                X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))))),
          (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y :
                X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫
                  hU.fromSpec) := by
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπirr.maximalIdeal_eq
  exact ⟨_, AffineCharts.p f Y hY hπ hYs, AffineCharts.isAffineHom_p f Y hY hπ hYs,
    AffineCharts.locallyOfFiniteType_p f Y hY hπ hYs, AffineCharts.isIso_restrict f Y hY hπ hYs,
    AffineCharts.apply_mem f Y hY hπ hYs, AffineCharts.exists_chartIso f Y hY hπ hYs⟩

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.Dilatations.DefectDecrease


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

open KaehlerDifferential IsLocalRing

noncomputable section

namespace JacobiLength

open NeronModelInfra.SmootheningBounds.NeronSmootheningBound
  (globalAlgebra globalPointAlgebra smoothnessDefect_eq_length_torsion_global
    algebraMap_globalPointAlgebra_globalAlgebra length_torsion_eq_of_equiv)

theorem smoothnessDefect_Spec_eq {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (φ : A →+* R') :
    let : Algebra A R' := φ.toAlgebra
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map
      (CommRingCat.ofHom φ)) =
      Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])) := by
  intro iAR'
  rw [smoothnessDefect_eq_length_torsion_global]
  set Γ' : Type u := Γ(Spec (CommRingCat.of A), ⊤) with hΓ
  let iRΓ : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    globalAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let iΓR' : Algebra Γ(Spec (CommRingCat.of A), ⊤) R' := globalPointAlgebra (Spec.map
    (CommRingCat.ofHom φ))
  let iΓA : Algebra Γ(Spec (CommRingCat.of A), ⊤) A := (Scheme.ΓSpecIso (CommRingCat.of
    A)).hom.hom.toAlgebra
  have : IsScalarTower R Γ(Spec (CommRingCat.of A), ⊤) A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext; intro r
    change algebraMap R A r = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id]
    rfl)
  have : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A R' := IsScalarTower.of_algebraMap_eq' (by
    change ((Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.germ ⊤ _ trivial).hom) =
      φ.comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    rw [← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo_Spec]
    rfl)
  have : IsLocalization.Away (1 : Γ(Spec (CommRingCat.of A), ⊤)) A :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
  have : Algebra.FormallyEtale Γ(Spec (CommRingCat.of A), ⊤) A :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : Γ(Spec (CommRingCat.of A), ⊤)))
  let e₁ : A ⊗[Γ(Spec (CommRingCat.of A), ⊤)] Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R] ≃ₗ[A] Ω[A⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(Spec (CommRingCat.of A), ⊤) A
  let e₂ := (e₁.symm.baseChange A R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(Spec (CommRingCat.of A), ⊤) A
    R' R'
    Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R]
  exact (NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv
    (e₂.trans e₃)).symm

theorem length_torsion_baseChange_kaehler_eq_of_formallyEtale
    (R : Type u) [CommRing R] (A S R' : Type u) [CommRing A] [CommRing S] [CommRing R']
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra A R'] [Algebra S R'] [IsScalarTower A S R'] [Algebra.FormallyEtale A S] :
    Module.length R' (Submodule.torsion R' (R' ⊗[S] Ω[S⁄R])) =
      Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])) := by
  let e₁ : S ⊗[A] Ω[A⁄R] ≃ₗ[S] Ω[S⁄R] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R
    A S
  let e₂ := (e₁.symm.baseChange S R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange A S R' R' Ω[A⁄R]
  exact NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv
    (e₂.trans e₃)

theorem length_torsion_quotient_mono_of_forall_exists_smul_mem
    {S : Type u} [CommRing S] [IsDomain S] {M : Type u} [AddCommGroup M] [Module S M]
    (N₁ N₂ : Submodule S M) (hle : N₁ ≤ N₂) (htor : ∀ x ∈ N₂, ∃ s : S, s ≠ 0 ∧ s • x ∈ N₁) :
    Module.length S (Submodule.torsion S (M ⧸ N₂)) ≤ Module.length S (Submodule.torsion S (M ⧸
      N₁)) := by
  let q : (M ⧸ N₁) →ₗ[S] (M ⧸ N₂) := Submodule.factor hle
  have hq : ∀ y : M ⧸ N₂, y ∈ Submodule.torsion S (M ⧸ N₂) →
      ∃ x ∈ Submodule.torsion S (M ⧸ N₁), q x = y := by
    intro y hy
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N₂ y
    obtain ⟨⟨a, ha⟩, hay⟩ := (Submodule.mem_torsion_iff _).mp hy
    change (a : S) • (Submodule.Quotient.mk m : M ⧸ N₂) = 0 at hay
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hay
    obtain ⟨s, hs, hsm⟩ := htor _ hay
    refine ⟨Submodule.Quotient.mk m, ?_, rfl⟩
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s * a, mul_ne_zero hs (nonZeroDivisors.ne_zero
      ha) |>
      mem_nonZeroDivisors_of_ne_zero⟩, ?_⟩
    change (s * (a : S)) • (Submodule.Quotient.mk m : M ⧸ N₁) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul]
    exact hsm
  let q' : Submodule.torsion S (M ⧸ N₁) →ₗ[S] Submodule.torsion S (M ⧸ N₂) :=
    (q.restrict fun x hx => by
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hx
      exact (Submodule.mem_torsion_iff _).mpr ⟨a, by
        change (a : S) • q x = 0
        rw [← map_smul]
        rw [show (a : S) • (x : M ⧸ N₁) = 0 from ha, map_zero]⟩)
  have hq' : Function.Surjective q' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hq y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Module.length_le_of_surjective q' hq'

theorem one_tmul_smul_eq {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] {M : Type u}
  [AddCommGroup M]
    [Module S M] (c : S) (m : M) :
    ((1 : T) ⊗ₜ[S] (c • m) : T ⊗[S] M) = algebraMap S T c • ((1 : T) ⊗ₜ[S] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]

theorem length_torsion_add_one_le_of_diagonal_map
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (π' : R') (hπ'irr : Irreducible π') (r n : ℕ)
    {M M' : Type u} [AddCommGroup M] [Module R' M] [AddCommGroup M'] [Module R' M']
    (N : Submodule R' M) (N'' : Submodule R' M')
    (κ : M ≃ₗ[R'] ((Fin r → R') × (Fin n → R')))
    (κ' : M' ≃ₗ[R'] ((Fin r → R') × (Fin n → R')))
    (hNcDm : (N.map κ.toLinearMap).map
        ((LinearMap.id : (Fin r → R') →ₗ[R'] (Fin r → R')).prodMap
          (π' • (LinearMap.id : (Fin n → R') →ₗ[R'] (Fin n → R')))) =
        (Ideal.span {π' ^ 2} : Ideal R') • N''.map κ'.toLinearMap) :
    Module.length R' (Submodule.torsion R' (M' ⧸ N'')) + 1 ≤
      max 1 (Module.length R' (Submodule.torsion R' (M ⧸ N))) := by
  classical
  let Dm : ((Fin r → R') × (Fin n → R')) →ₗ[R'] ((Fin r → R') × (Fin n → R')) :=
    (LinearMap.id : (Fin r → R') →ₗ[R'] (Fin r → R')).prodMap
      (π' • (LinearMap.id : (Fin n → R') →ₗ[R'] (Fin n → R')))
  let I2 : Ideal R' := Ideal.span {π' ^ 2}
  have hπ'ne : π' ≠ 0 := hπ'irr.ne_zero
  let Fsub : Submodule R' ((Fin r → R') × (Fin n → R')) := (⊤ : Submodule R' (Fin r → R')).prod
    ((Ideal.span {π'} : Ideal R') • ⊤)
  have hDm_mem : ∀ v : ((Fin r → R') × (Fin n → R')), Dm v ∈ Fsub := by
    rintro ⟨u, w⟩
    refine ⟨trivial, ?_⟩
    change π' • w ∈ (Ideal.span {π'} : Ideal R') • (⊤ : Submodule R' (Fin n → R'))
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hDm_inj : Function.Injective Dm := by
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    simp only [Dm, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : w = w' := smul_right_injective (Fin n → R') hπ'ne h2
    rw [this]
  have hDm_surj : ∀ y ∈ Fsub, ∃ v, Dm v = y := by
    rintro ⟨u, w'⟩ ⟨-, hw'⟩
    change w' ∈ (Ideal.span {π'} : Ideal R') • (⊤ : Submodule R' (Fin n → R')) at hw'
    rw [Submodule.ideal_span_singleton_smul] at hw'
    obtain ⟨w, -, rfl⟩ := hw'
    exact ⟨(u, w), rfl⟩
  let Dm' : ((Fin r → R') × (Fin n → R')) ≃ₗ[R'] Fsub := LinearEquiv.ofBijective (Dm.codRestrict
    Fsub hDm_mem)
    ⟨fun a b h => hDm_inj (congrArg Subtype.val h), fun y => by
      obtain ⟨v, hv⟩ := hDm_surj y.1 y.2; exact ⟨v, Subtype.ext hv⟩⟩
  have hJ1hyp : I2 • N''.map κ'.toLinearMap ≤ Fsub := by
    rw [← hNcDm]; rintro _ ⟨v, -, rfl⟩; exact hDm_mem v
  have hJ1 := IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
    π' hπ'irr r n
    (N''.map κ'.toLinearMap) hJ1hyp
  have eq1 : Module.length R' (Submodule.torsion R' (M' ⧸ N'')) =
      Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N''.map
        κ'.toLinearMap)) :=
    NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv
      (Submodule.Quotient.equiv _ _ κ' rfl)
  have hmapDm' : (N.map (κ.trans Dm').toLinearMap) = (I2 • N''.map κ'.toLinearMap).comap
    Fsub.subtype := by
    rw [← hNcDm]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨κ x, Submodule.mem_map_of_mem hx, rfl⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, hv⟩
      refine ⟨x, hx, Subtype.ext ?_⟩
      change Dm (κ x) = Fsub.subtype y
      exact hv
  have eq2 : Module.length R' (Submodule.torsion R' (M ⧸ N)) =
      Module.length R' (Submodule.torsion R' (Fsub ⧸ (I2 • N''.map κ'.toLinearMap).comap
        Fsub.subtype)) :=
    NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv
      (Submodule.Quotient.equiv _ _ (κ.trans Dm') hmapDm')
  have key : Module.length R' (Submodule.torsion R' (M' ⧸ N'')) +
      Module.finrank R' (N''.map κ'.toLinearMap) ≤
      Module.length R' (Submodule.torsion R' (M ⧸ N)) := by
    rw [eq1, eq2]; exact hJ1
  by_cases hρ : Module.finrank R' (N''.map κ'.toLinearMap) = 0
  · have hbot : N''.map κ'.toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.mp hρ) ⟨x, hx⟩
      have h' : a • x = 0 := congrArg Subtype.val hax
      exact (smul_eq_zero.mp h').resolve_left ha
    have h0 : Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N''.map
      κ'.toLinearMap)) = 0 := by
      rw [hbot]
      have e := (Submodule.quotEquivOfEqBot (⊥ : Submodule R' ((Fin r → R') × (Fin n → R'))) rfl)
      rw [NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv e,
        Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance]
      exact Module.length_bot
    rw [eq1, h0, zero_add]
    exact le_max_left _ _
  · have h1 : (1 : ℕ∞) ≤ Module.finrank R' (N''.map κ'.toLinearMap) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ
    calc Module.length R' (Submodule.torsion R' (M' ⧸ N'')) + 1
        ≤ Module.length R' (Submodule.torsion R' (M' ⧸ N'')) +
            Module.finrank R' (N''.map κ'.toLinearMap) := add_le_add_right h1 _
      _ ≤ Module.length R' (Submodule.torsion R' (M ⧸ N)) := key
      _ ≤ _ := le_max_right _ _


theorem center_comap_saturated
    {R A C Ag : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [CommRing C] [CommRing Ag] [Algebra R A] [Algebra R C]
    [Algebra R Ag] [Algebra A Ag] [Algebra C Ag]
    [IsScalarTower R A Ag] [IsScalarTower R C Ag]
    (g : A) [IsLocalization.Away g Ag] (J : Ideal A) (JC : Ideal C)
    (hJC : Ideal.comap (algebraMap C Ag) (J.map (algebraMap A Ag)) = JC)
    (hN : ∀ g₀ : A,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R'']
        [Algebra R R''] [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : A →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g₀ ∈ (IsLocalRing.maximalIdeal R'').comap c) → g₀ ∈ J) :
    ∀ g₀ : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C Ag) ≤ RingHom.ker c.toRingHom →
          JC ≤ (IsLocalRing.maximalIdeal R'').comap c → g₀ ∈ (IsLocalRing.maximalIdeal
            R'').comap c) →
      g₀ ∈ JC := by
  intro g₀ hg₀
  rw [← hJC, Ideal.mem_comap]
  obtain ⟨⟨a₀, ⟨_, ⟨m, rfl⟩⟩⟩, ha₀⟩ := IsLocalization.mk'_surjective (Submonoid.powers g)
    (algebraMap C Ag g₀)
  have hclaim : a₀ * g ∈ J := by
    apply hN
    intro R'' _ _ _ _ _ hR'' c hJc
    by_cases hcg : c g ∈ IsLocalRing.maximalIdeal R''
    · exact Ideal.mem_comap.mpr (by rw [map_mul]; exact Ideal.mul_mem_left _ _ hcg)
    · have hu : IsUnit (c.toRingHom g) := IsLocalRing.notMem_maximalIdeal.mp hcg
      let cg : Ag →+* R'' := IsLocalization.Away.lift g (g := c.toRingHom) hu
      have hcg_eq : ∀ a, cg (algebraMap A Ag a) = c a := IsLocalization.Away.lift_eq g hu
      let ct : C →ₐ[R] R'' := AlgHom.mk (cg.comp (algebraMap C Ag)) (fun r' => by
        change cg (algebraMap C Ag (algebraMap R C r')) = algebraMap R R'' r'
        rw [← IsScalarTower.algebraMap_apply R C Ag, IsScalarTower.algebraMap_apply R A Ag,
          hcg_eq,
          AlgHom.commutes])
      have hker : RingHom.ker (algebraMap C Ag) ≤ RingHom.ker ct.toRingHom := by
        intro f hf
        simp only [RingHom.mem_ker] at hf ⊢
        change cg (algebraMap C Ag f) = 0
        rw [hf, map_zero]
      have hJle : JC ≤ (IsLocalRing.maximalIdeal R'').comap ct := by
        rw [← hJC]
        intro j hj
        rw [Ideal.mem_comap] at hj ⊢
        change cg (algebraMap C Ag j) ∈ IsLocalRing.maximalIdeal R''
        have : J.map (algebraMap A Ag) ≤ (IsLocalRing.maximalIdeal R'').comap cg := by
          rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
          intro a ha
          rw [Ideal.mem_comap, RingHom.comp_apply, hcg_eq]
          exact hJc ha
        exact this hj
      have h1 := hg₀ R'' hR'' ct hker hJle
      rw [Ideal.mem_comap] at h1
      change cg (algebraMap C Ag g₀) ∈ IsLocalRing.maximalIdeal R'' at h1
      rw [← ha₀] at h1
      have h2 : cg (IsLocalization.mk' Ag a₀ (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) *
          cg (algebraMap A Ag (g ^ m)) = c a₀ := by
        rw [← map_mul, IsLocalization.mk'_spec, hcg_eq]
      rw [Ideal.mem_comap, map_mul, ← h2, mul_assoc]
      exact Ideal.mul_mem_right _ _ h1
  have h3 : algebraMap C Ag g₀ =
      algebraMap A Ag (a₀ * g) * IsLocalization.mk' Ag 1 (⟨g ^ (m + 1), m + 1, rfl⟩ :
        Submonoid.powers g) := by
    rw [← ha₀, ← IsLocalization.mk'_one (M := Submonoid.powers g) Ag, ← IsLocalization.mk'_mul]
    rw [IsLocalization.mk'_eq_iff_eq]
    simp only [one_mul, mul_one]
    congr 1
    ring
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hclaim)

/-- Saturating divided relations can only decrease the torsion length of differentials. -/
private theorem length_torsion_kaehler_quotient_le
    {R C C' B S : Type u} [CommRing R] [CommRing C] [CommRing C'] [CommRing B]
    [CommRing S] [IsDomain S] [Algebra R C'] [Algebra C C'] [Algebra C' S]
    (I : Ideal C) (π : R) (θ : C' →+* B) (fp : I → C')
    (hfp : ∀ f : I, (algebraMap R C' π) ^ 2 * fp f = algebraMap C C' (f : C))
    (hθι : ∀ f : I, θ (algebraMap C C' (f : C)) = 0)
    (hθfp : ∀ f : I, θ (fp f) = 0)
    (hθk : ∀ x, θ x = 0 → ∃ ν : ℕ,
      (algebraMap R C' π) ^ ν * x ∈ I.map (algebraMap C C'))
    (hπne : algebraMap C' S (algebraMap R C' π) ≠ 0)
    (hzero : ∀ x, θ x = 0 → algebraMap C' S x = 0) :
    Module.length S (Submodule.torsion S
      ((S ⊗[C'] Ω[C'⁄R]) ⧸ Submodule.span S
        (Set.range fun x : RingHom.ker θ => (1 : S) ⊗ₜ[C'] D R C' (x : C')))) ≤
    Module.length S (Submodule.torsion S
      ((S ⊗[C'] Ω[C'⁄R]) ⧸ Submodule.span S
        (Set.range fun f : I => (1 : S) ⊗ₜ[C'] D R C' (fp f)))) := by
  let N'full : Submodule S (S ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span S (Set.range fun x : RingHom.ker θ => (1 : S) ⊗ₜ[C'] D R C' (x : C'))
  let N'' : Submodule S (S ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span S (Set.range fun f : I => (1 : S) ⊗ₜ[C'] D R C' (fp f))
  let πS : S := algebraMap C' S (algebraMap R C' π)
  have hπS : algebraMap C' S (algebraMap R C' π) = πS := rfl
  have hN''le : N'' ≤ N'full := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨⟨fp f, RingHom.mem_ker.mpr (hθfp f)⟩, rfl⟩
  have htmul : ∀ (c : C') (m : Ω[C'⁄R]),
      ((1 : S) ⊗ₜ[C'] (c • m) : S ⊗[C'] Ω[C'⁄R]) = algebraMap C' S c • ((1 : S) ⊗ₜ[C'] m) :=
    fun c m => one_tmul_smul_eq c m
  have hπsq : (algebraMap R C' π) ^ 2 = algebraMap R C' (π ^ 2) := (map_pow _ _ _).symm
  have hIC' : ∀ x ∈ I.map (algebraMap C C'),
      θ x = 0 ∧ ((1 : S) ⊗ₜ[C'] D R C' x) ∈ N'' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => θ x = 0 ∧ ((1 : S) ⊗ₜ[C'] D R C' x) ∈
      N'') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨hθι ⟨f, hf⟩, ?_⟩
      rw [← hfp ⟨f, hf⟩, Derivation.leibniz, hπsq, Derivation.map_algebraMap, smul_zero,
        add_zero, htmul]
      exact N''.smul_mem _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)
    · exact ⟨map_zero _, by rw [map_zero, TensorProduct.tmul_zero]; exact Submodule.zero_mem _⟩
    · rintro x y - - ⟨hx0, hx⟩ ⟨hy0, hy⟩
      refine ⟨by rw [map_add, hx0, hy0, add_zero], ?_⟩
      rw [map_add, TensorProduct.tmul_add]
      exact N''.add_mem hx hy
    · rintro c x - ⟨hx0, hx⟩
      refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], ?_⟩
      rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, htmul, htmul]
      have hψx : algebraMap C' S x = 0 := hzero x hx0
      rw [hψx, zero_smul, add_zero]
      exact N''.smul_mem _ hx
  have htors : ∀ x ∈ N'full, ∃ s : S, s ≠ 0 ∧ s • x ∈ N'' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ s : S, s ≠ 0 ∧ s • x ∈ N'') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨f', hf'⟩, rfl⟩
      have h0 : θ f' = 0 := RingHom.mem_ker.mp hf'
      obtain ⟨ν, hν⟩ := hθk f' h0
      refine ⟨πS ^ ν, pow_ne_zero ν hπne, ?_⟩
      have h1 := (hIC' _ hν).2
      rw [Derivation.leibniz, TensorProduct.tmul_add, htmul, htmul, map_pow, hπS] at h1
      have h2 : (D R C') ((algebraMap R _ π) ^ ν) = 0 := by
        rw [← map_pow]; exact Derivation.map_algebraMap _ _
      rw [h2, TensorProduct.tmul_zero, smul_zero, add_zero] at h1
      simpa only using h1
    · exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro x y - - ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
      refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
      rw [smul_add]
      exact N''.add_mem (by rw [mul_comm, mul_smul]; exact N''.smul_mem t hsx)
        (by rw [mul_smul]; exact N''.smul_mem s hty)
    · rintro a x - ⟨s, hs, hsx⟩
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact N''.smul_mem _ hsx
  exact length_torsion_quotient_mono_of_forall_exists_smul_mem N'' N'full hN''le htors

/-- Dividing the normal coordinates by a uniformizer strictly lowers the torsion defect. -/
private theorem length_torsion_kaehler_quotients_add_one_le
    {R C C' S : Type u} [CommRing R] [CommRing C] [CommRing C']
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R C] [Algebra R C'] [Algebra C C'] [IsScalarTower R C C']
    [Algebra C S] [Algebra C' S] [IsScalarTower C C' S]
    (π : R) (πS : S) (hπirr : Irreducible πS)
    (hπS : algebraMap C' S (algebraMap R C' π) = πS) (r n : ℕ)
    (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (b' : Module.Basis (Fin r ⊕ Fin n) C' Ω[C'⁄R])
    (hmap_y : ∀ i, KaehlerDifferential.map R R C C' (b (Sum.inl i)) = b' (Sum.inl i))
    (hmap_z : ∀ j, KaehlerDifferential.map R R C C' (b (Sum.inr j)) =
      algebraMap R C' π • b' (Sum.inr j))
    (I : Ideal C) (fp : I → C')
    (hfp : ∀ f : I, (algebraMap R C' π) ^ 2 * fp f = algebraMap C C' (f : C)) :
    Module.length S (Submodule.torsion S
      ((S ⊗[C'] Ω[C'⁄R]) ⧸ Submodule.span S
        (Set.range fun f : I => (1 : S) ⊗ₜ[C'] D R C' (fp f)))) + 1 ≤
    max 1 (Module.length S (Submodule.torsion S
      ((S ⊗[C] Ω[C⁄R]) ⧸ Submodule.span S
        (Set.range fun f : I => (1 : S) ⊗ₜ[C] D R C (f : C))))) := by
  classical
  let N : Submodule S (S ⊗[C] Ω[C⁄R]) :=
    Submodule.span S (Set.range fun f : I => (1 : S) ⊗ₜ[C] D R C (f : C))
  let N'' : Submodule S (S ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span S (Set.range fun f : I => (1 : S) ⊗ₜ[C'] D R C' (fp f))
  have htmul : ∀ (c : C') (m : Ω[C'⁄R]),
      ((1 : S) ⊗ₜ[C'] (c • m) : S ⊗[C'] Ω[C'⁄R]) =
        algebraMap C' S c • ((1 : S) ⊗ₜ[C'] m) := fun c m => one_tmul_smul_eq c m
  have hπsq : (algebraMap R C' π) ^ 2 = algebraMap R C' (π ^ 2) := (map_pow _ _ _).symm
  let bF := Algebra.TensorProduct.basis S b
  let bF' := Algebra.TensorProduct.basis S b'
  let e0 : (Fin r ⊕ Fin n → S) ≃ₗ[S] ((Fin r → S) × (Fin n → S)) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin n) S S
  let κ : (S ⊗[C] Ω[C⁄R]) ≃ₗ[S] ((Fin r → S) × (Fin n → S)) := bF.equivFun.trans e0
  let κ' : (S ⊗[C'] Ω[C'⁄R]) ≃ₗ[S] ((Fin r → S) × (Fin n → S)) := bF'.equivFun.trans e0
  let Dm : ((Fin r → S) × (Fin n → S)) →ₗ[S] ((Fin r → S) × (Fin n → S)) := (LinearMap.id :
    (Fin r → S) →ₗ[S] (Fin r → S)).prodMap
    (πS • (LinearMap.id : (Fin n → S) →ₗ[S] (Fin n → S)))
  have he0 : ∀ f : Fin r ⊕ Fin n → S, e0 f = (fun i => f (Sum.inl i), fun j => f (Sum.inr j)) :=
    fun f => rfl
  have hDmap : ∀ (u : Fin r → S) (w : Fin n → S), Dm (u, w) = (u, πS • w) := fun u w => rfl
  let Φ : (S ⊗[C] Ω[C⁄R]) →ₗ[S] (S ⊗[C'] Ω[C'⁄R]) :=
    ((KaehlerDifferential.mapBaseChange R C C').baseChange S).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C C' S S Ω[C⁄R]).symm.toLinearMap
  have hΦ : ∀ m : Ω[C⁄R], Φ ((1 : S) ⊗ₜ[C] m) = (1 : S) ⊗ₜ[C'] KaehlerDifferential.map R R C
    C' m := by
    intro m
    change ((KaehlerDifferential.mapBaseChange R C C').baseChange S)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C C' S S Ω[C⁄R]).symm ((1 : S)
        ⊗ₜ[C] m)) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      KaehlerDifferential.mapBaseChange_tmul]
    exact congrArg ((1 : S) ⊗ₜ[C'] ·) (one_smul C' ((KaehlerDifferential.map R R C C') m))
  have hKC : (κ'.toLinearMap.comp Φ) = Dm.comp κ.toLinearMap := by
    refine bF.ext fun k => ?_
    rcases k with i | j
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have h1 : Φ (bF (Sum.inl i)) = bF' (Sum.inl i) := by
        rw [Algebra.TensorProduct.basis_apply, hΦ, hmap_y, (Algebra.TensorProduct.basis_apply b'
          _).symm]
      change κ' (Φ (bF (Sum.inl i))) = Dm (κ (bF (Sum.inl i)))
      rw [h1]
      change e0 (bF'.equivFun (bF' (Sum.inl i))) = Dm (e0 (bF.equivFun (bF (Sum.inl i))))
      refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        simp only [Finsupp.single_apply, Sum.inl_ne_inr, ite_false, Pi.smul_apply, smul_zero]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have h1 : Φ (bF (Sum.inr j)) = πS • bF' (Sum.inr j) := by
        rw [Algebra.TensorProduct.basis_apply, hΦ, hmap_z, htmul, hπS,
          (Algebra.TensorProduct.basis_apply b' _).symm]
      change κ' (Φ (bF (Sum.inr j))) = Dm (κ (bF (Sum.inr j)))
      rw [h1, map_smul]
      change πS • e0 (bF'.equivFun (bF' (Sum.inr j))) = Dm (e0 (bF.equivFun (bF (Sum.inr j))))
      refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        simp only [Finsupp.single_apply, Sum.inr_ne_inl, ite_false, Prod.smul_fst,
          Pi.smul_apply, smul_zero]
      · simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDmap]
        rfl
  let I2 : Ideal S := Ideal.span {πS ^ 2}
  have hΦgen : ∀ f : I,
      Φ ((1 : S) ⊗ₜ[C] D R C (f : C)) = (πS ^ 2) • ((1 : S) ⊗ₜ[C'] D R C' (fp f)) := by
    intro f
    rw [hΦ, KaehlerDifferential.map_D, ← hfp f, Derivation.leibniz, hπsq,
      Derivation.map_algebraMap, smul_zero,
      add_zero, ← hπsq, htmul, map_pow, hπS]
  have hNΦ : N.map Φ = I2 • N'' := by
    apply le_antisymm
    · rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
      rw [hΦgen]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (Submodule.subset_span ⟨f,
        rfl⟩)
    · rw [Submodule.smul_le]
      rintro a ha x hx
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [mul_smul]
      refine Submodule.smul_mem _ t ?_
      have hle : N'' ≤ (N.map Φ).comap ((πS ^ 2) • LinearMap.id) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨f, rfl⟩
        change ((1 : S) ⊗ₜ[C'] D R C' (fp f)) ∈ Submodule.comap ((πS ^ 2) • LinearMap.id)
          (N.map Φ)
        rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, ← hΦgen]
        exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨f, rfl⟩)
      simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using hle hx
  have hNcDm : (N.map κ.toLinearMap).map Dm = I2 • N''.map κ'.toLinearMap := by
    rw [← Submodule.map_comp, ← hKC, Submodule.map_comp, hNΦ, Submodule.map_smul'']
  exact length_torsion_add_one_le_of_diagonal_map πS hπirr r n N N'' κ κ' hNcDm

/-- Compatible points lift to the localized dilatation and agree on the localized base. -/
private theorem exists_compatible_localization_point
    {A Ag A' B S : Type u} [CommRing A] [CommRing Ag] [CommRing A'] [CommRing B]
    [CommRing S] [Algebra A Ag] [Algebra A A'] [Algebra A B] [Algebra A' B]
    [Algebra Ag B] [IsScalarTower A Ag B] (g : A) [IsLocalization.Away g Ag]
    [IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) B]
    (φ : A →+* S) (φg : Ag →+* S) (φ' : A' →+* S) (hg : IsUnit (φ g))
    (hφg : ∀ a, φg (algebraMap A Ag a) = φ a)
    (hφ' : ∀ a, φ' (algebraMap A A' a) = φ a)
    (hA : (algebraMap A' B).comp (algebraMap A A') = algebraMap A B) :
    ∃ φB : B →+* S, (∀ a', φB (algebraMap A' B a') = φ' a') ∧
      φB.comp (algebraMap Ag B) = φg := by
  have hunits : ∀ s : Algebra.algebraMapSubmonoid A' (Submonoid.powers g), IsUnit (φ' s) := by
    rintro ⟨_, ⟨a, ⟨k, rfl⟩, rfl⟩⟩
    change IsUnit (φ' (algebraMap A A' (g ^ k)))
    rw [hφ', map_pow]
    exact hg.pow k
  let φB : B →+* S := IsLocalization.lift
    (M := Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) hunits
  have hφB : ∀ a' : A', φB (algebraMap A' B a') = φ' a' :=
    fun a' => IsLocalization.lift_eq hunits a'
  refine ⟨φB, hφB, ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  ext a
  change φB (algebraMap Ag B (algebraMap A Ag a)) = φg (algebraMap A Ag a)
  calc
    φB (algebraMap Ag B (algebraMap A Ag a)) = φB (algebraMap A B a) :=
      congrArg φB (IsScalarTower.algebraMap_apply A Ag B a).symm
    _ = φB (algebraMap A' B (algebraMap A A' a)) :=
      congrArg φB (RingHom.congr_fun hA a).symm
    _ = φ' (algebraMap A A' a) := hφB _
    _ = φ a := hφ' a
    _ = φg (algebraMap A Ag a) := (hφg a).symm

/-- A smooth presentation with quadratic relations decreases the differential torsion length. -/
private theorem length_torsion_decrease_of_smooth_presentation
    {R C A C' B S : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing C']
    [CommRing B] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    [Algebra R C'] [Algebra C C'] [IsScalarTower R C C']
    [Algebra R B] [Algebra C' B] [IsScalarTower R C' B]
    [Algebra C S] [Algebra A S] [IsScalarTower C A S]
    [Algebra C' S] [Algebra B S] [IsScalarTower C' B S] [IsScalarTower C C' S]
    (π : R) (πS : S) (hπirr : Irreducible πS)
    (hπS : algebraMap C' S (algebraMap R C' π) = πS)
    (J : Ideal C) (hIJ2 : RingHom.ker (algebraMap C A) ≤ J ^ 2)
    (hJmap : J.map (algebraMap C C') = Ideal.span {algebraMap R C' π})
    (hreg : ∀ x : B, algebraMap C' B (algebraMap R C' π) ^ 2 * x = 0 → x = 0)
    (hkill : ∀ f : RingHom.ker (algebraMap C A), algebraMap C' B (algebraMap C C' (f : C)) = 0)
    (hker : ∀ x, algebraMap C' B x = 0 ↔ ∃ ν : ℕ, (algebraMap R C' π) ^ ν * x ∈
      (RingHom.ker (algebraMap C A)).map (algebraMap C C'))
    (hsurj : Function.Surjective (algebraMap C A))
    (hsurj' : Function.Surjective (algebraMap C' B))
    (r n : ℕ) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (b' : Module.Basis (Fin r ⊕ Fin n) C' Ω[C'⁄R])
    (hmap_y : ∀ i, KaehlerDifferential.map R R C C' (b (Sum.inl i)) = b' (Sum.inl i))
    (hmap_z : ∀ j, KaehlerDifferential.map R R C C' (b (Sum.inr j)) =
      algebraMap R C' π • b' (Sum.inr j)) :
    Module.length S (Submodule.torsion S (S ⊗[B] Ω[B⁄R])) + 1 ≤
      max 1 (Module.length S (Submodule.torsion S (S ⊗[A] Ω[A⁄R]))) := by
  classical
  obtain ⟨eF⟩ :=
    KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
      (R := R) (C := C) (A := A) (R' := S) hsurj
  obtain ⟨eF'⟩ :=
    KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
      (R := R) (C := C') (A := B) (R' := S) hsurj'
  rw [NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv eF,
    NeronModelInfra.SmootheningBounds.NeronSmootheningBound.length_torsion_eq_of_equiv eF']
  have hex : ∀ f : RingHom.ker (algebraMap C A), ∃ f' : C',
      algebraMap R C' π ^ 2 * f' = algebraMap C C' (f : C) := by
    rintro ⟨f, hf⟩
    have h1 : algebraMap C C' f ∈ (J.map (algebraMap C C')) ^ 2 := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (hIJ2 hf)
    rw [hJmap, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', by rw [mul_comm]; exact hf'⟩
  choose fp hfp using hex
  have hfpker : ∀ f : RingHom.ker (algebraMap C A), algebraMap C' B (fp f) = 0 := by
    intro f
    apply hreg
    rw [← map_pow, ← map_mul, hfp, hkill]
  let N'full : Submodule S (S ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span S (Set.range fun f : RingHom.ker (algebraMap C' B) =>
      (1 : S) ⊗ₜ[C'] D R C' (f : C'))
  let N'' : Submodule S (S ⊗[C'] Ω[C'⁄R]) :=
    Submodule.span S (Set.range fun f : RingHom.ker (algebraMap C A) =>
      (1 : S) ⊗ₜ[C'] D R C' (fp f))
  have hmono : Module.length S (Submodule.torsion S ((S ⊗[C'] Ω[C'⁄R]) ⧸ N'full)) ≤
      Module.length S (Submodule.torsion S ((S ⊗[C'] Ω[C'⁄R]) ⧸ N'')) :=
    length_torsion_kaehler_quotient_le (R := R) (RingHom.ker (algebraMap C A)) π
      (algebraMap C' B) fp hfp hkill hfpker (fun x hx => (hker x).mp hx)
      (by rw [hπS]; exact hπirr.ne_zero) (fun x hx => by
        rw [IsScalarTower.algebraMap_apply C' B S, hx, map_zero])
  exact (add_le_add hmono (le_refl 1)).trans
    (length_torsion_kaehler_quotients_add_one_le π πS hπirr hπS r n b b' hmap_y hmap_z
      (RingHom.ker (algebraMap C A)) fp hfp)

end JacobiLength

end

open JacobiLength in
theorem
  _root_.NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R)
      (A ⧸ J)]
    (hN : ∀ g : A,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : A →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (hR' : IsIndexOneExtension R R')
    (φ : A →ₐ[R] R') (_ : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈
      Algebra.smoothLocus R A)
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) =
      (IsLocalRing.maximalIdeal R').comap φ)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈
      Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (φ' : AffineDilatation.Ring J (algebraMap R A π) →ₐ[R] R')
    (hφ' : ∀ a : A, φ' (algebraMap A (AffineDilatation.Ring J (algebraMap R A π)) a) = φ a) :
    smoothnessDefect
        (Spec.map (CommRingCat.ofHom (algebraMap R (AffineDilatation.Ring J (algebraMap R A π)))))
        (Spec.map (CommRingCat.ofHom φ'.toRingHom)) + 1 ≤
      max 1 (smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom)))  := by
  classical
  let 𝔭 : Ideal A := (IsLocalRing.maximalIdeal R').comap φ.toRingHom
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have h𝔮' : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭 := h𝔮
  obtain ⟨g, hg, r, n, C, iC, iRC, iCAg, iT, hCsm, hθ, y, z, b, hby, hbz, hJC, hlin⟩ :=
    Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
      π hπ J hπJ 𝔭 𝔮 h𝔮' hsmooth hfree
  let : CommRing C := iC
  let : Algebra R C := iRC
  let : Algebra C (Localization.Away g) := iCAg
  have : IsScalarTower R C (Localization.Away g) := iT
  set Ag : Type u := Localization.Away g with hAg
  have hgunit : IsUnit (φ g) := IsLocalRing.notMem_maximalIdeal.mp hg
  let φg : Ag →+* R' := IsLocalization.Away.lift g (g := φ.toRingHom) hgunit
  have hφg : ∀ a : A, φg (algebraMap A Ag a) = φ a := fun a => IsLocalization.Away.lift_eq g
    hgunit a
  set JC : Ideal C := Ideal.span (insert (algebraMap R C π) (Set.range z)) with hJCdef
  have hπJC : algebraMap R C π ∈ JC := Ideal.subset_span (Set.mem_insert _ _)
  have hNC := center_comap_saturated g J JC hJC hN
  have hIJ : RingHom.ker (algebraMap C Ag) ≤ JC := by
    rw [← hJC]; exact fun f hf => by
      simp only [Ideal.mem_comap, RingHom.mem_ker] at hf ⊢; rw [hf]; exact Ideal.zero_mem _
  have hIJ2 : RingHom.ker (algebraMap C Ag) ≤ JC ^ 2 :=
    NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne π hπ hθ z hIJ hlin hNC
  obtain ⟨b', hb'y, hb'z⟩ :=
    AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis π hπ y z b hby hbz
  have hImap : JC.map (algebraMap C Ag) = J.map (algebraMap A Ag) := by
    rw [← hJC, Ideal.map_comap_of_surjective _ hθ]
  have hπeq : algebraMap R Ag π = algebraMap A Ag (algebraMap R A π) :=
    IsScalarTower.algebraMap_apply R A Ag π
  have h5 : ∃ θ' : AffineDilatation.Ring JC (algebraMap R C π) →ₐ[C]
      AffineDilatation.Ring (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap R A π)),
      Function.Surjective θ' ∧ ∀ x, θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
        (RingHom.ker (algebraMap C Ag)).map (algebraMap C (AffineDilatation.Ring JC (algebraMap
          R C π))) := by
    have h := AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective (R := R) π (C :=
      C) (A := Ag) hθ JC
    rw [hImap, hπeq] at h
    exact h
  obtain ⟨θ', hθ's, hθ'k⟩ := h5
  obtain ⟨lam, hlam⟩ := AffineDilatation.exists_algHom_isLocalization_map J (algebraMap R A π) hπJ
    (Submonoid.powers g) Ag
  let A' : Type u := AffineDilatation.Ring J (algebraMap R A π)
  let B : Type u := AffineDilatation.Ring (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap
    R A π))
  let C' : Type u := AffineDilatation.Ring JC (algebraMap R C π)
  let iA'B : Algebra A' B := lam.toRingHom.toAlgebra
  have hlam' : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) B := hlam
  have : Algebra.FormallyEtale A' B := Algebra.FormallyEtale.of_isLocalization
    (Algebra.algebraMapSubmonoid A' (Submonoid.powers g))
  obtain ⟨φB, hφB, hφBAg⟩ := exists_compatible_localization_point
    (B := B) g φ.toRingHom φg φ'.toRingHom hgunit hφg hφ' lam.comp_algebraMap
  let iAgR' : Algebra Ag R' := φg.toAlgebra
  let iAR' : Algebra A R' := φ.toRingHom.toAlgebra
  have : IsScalarTower A Ag R' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hφg
    a).symm)
  let iCR' : Algebra C R' := (φg.comp (algebraMap C Ag)).toAlgebra
  have : IsScalarTower C Ag R' := IsScalarTower.of_algebraMap_eq' rfl
  have hδφ : smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      Module.length R' (Submodule.torsion R' (R' ⊗[Ag] Ω[Ag⁄R])) := by
    rw [smoothnessDefect_Spec_eq]
    have : Algebra.FormallyEtale A Ag := Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers g)
    exact (length_torsion_baseChange_kaehler_eq_of_formallyEtale R A Ag R').symm
  let iC'B : Algebra C' B := θ'.toRingHom.toAlgebra
  have : IsScalarTower C C' B := IsScalarTower.of_algebraMap_eq' (θ'.comp_algebraMap).symm
  have : IsScalarTower R C' B := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R C C', ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq
      C C' B,
      IsScalarTower.algebraMap_eq R C B])
  have : IsScalarTower R A' B := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R A A', ← RingHom.comp_assoc]
    have hl : (algebraMap A' B).comp (algebraMap A A') = algebraMap A B := lam.comp_algebraMap
    rw [hl, ← IsScalarTower.algebraMap_eq R A B])
  let iBR' : Algebra B R' := φB.toAlgebra
  let iA'R' : Algebra A' R' := φ'.toRingHom.toAlgebra
  have : IsScalarTower A' B R' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a' => (hφB
    a').symm)
  let iC'R' : Algebra C' R' := (φB.comp θ'.toRingHom).toAlgebra
  have : IsScalarTower C' B R' := IsScalarTower.of_algebraMap_eq' rfl
  have hδφ' : smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      (Spec.map (CommRingCat.ofHom φ'.toRingHom)) =
      Module.length R' (Submodule.torsion R' (R' ⊗[B] Ω[B⁄R])) := by
    rw [smoothnessDefect_Spec_eq]
    exact (length_torsion_baseChange_kaehler_eq_of_formallyEtale R A' B R').symm
  have hψ : ∀ c : C, algebraMap C' R' (algebraMap C C' c) = algebraMap C R' c := by
    intro c
    change φB (θ' (algebraMap C C' c)) = φg (algebraMap C Ag c)
    rw [θ'.commutes, IsScalarTower.algebraMap_apply C Ag B, ← RingHom.comp_apply, hφBAg]
  obtain ⟨-, hJC'⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton JC
    (algebraMap R C π) hπJC
  have hπJ' : algebraMap A Ag (algebraMap R A π) ∈ J.map (algebraMap A Ag) :=
    Ideal.mem_map_of_mem _ hπJ
  obtain ⟨hregB, -⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton
    (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap R A π)) hπJ'
  have hπB : algebraMap C' B (algebraMap R C' π) =
      algebraMap Ag B (algebraMap A Ag (algebraMap R A π)) := by
    change θ' (algebraMap R C' π) = _
    rw [IsScalarTower.algebraMap_apply R C C' π, θ'.commutes,
      ← IsScalarTower.algebraMap_apply R C B, IsScalarTower.algebraMap_apply R Ag B,
      IsScalarTower.algebraMap_apply R A Ag]
  have hreg : ∀ x : B, algebraMap C' B (algebraMap R C' π) ^ 2 * x = 0 → x = 0 := by
    intro x hx
    apply hregB.pow 2
    change (algebraMap A Ag (algebraMap R A π)) ^ 2 • x =
      (algebraMap A Ag (algebraMap R A π)) ^ 2 • (0 : B)
    rw [smul_zero, Algebra.smul_def, map_pow, ← hπB]
    exact hx
  have hkill : ∀ f : RingHom.ker (algebraMap C Ag),
      algebraMap C' B (algebraMap C C' (f : C)) = 0 := by
    rintro ⟨f, hf⟩
    change θ' (algebraMap C C' f) = 0
    rw [θ'.commutes, IsScalarTower.algebraMap_apply C Ag B, RingHom.mem_ker.mp hf, map_zero]
  have hRC' : ∀ r : R, algebraMap C' R' (algebraMap R C' r) = algebraMap R R' r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R C C' r, hψ]
    change φg (algebraMap C Ag (algebraMap R C r)) = algebraMap R R' r
    rw [← IsScalarTower.algebraMap_apply R C Ag, IsScalarTower.algebraMap_apply R A Ag, hφg,
      AlgHom.commutes]
  have hπ'irr : Irreducible (algebraMap R R' π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hR'.map_maximalIdeal, hπ,
      Ideal.map_span, Set.image_singleton]
  have : IsScalarTower C C' R' :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun c => (hψ c).symm)
  have hmap_y : ∀ i, KaehlerDifferential.map R R C C' (b (Sum.inl i)) = b' (Sum.inl i) := by
    intro i
    rw [hby, KaehlerDifferential.map_D, hb'y]
  have hmap_z : ∀ j, KaehlerDifferential.map R R C C' (b (Sum.inr j)) =
      algebraMap R C' π • b' (Sum.inr j) := by
    intro j
    rw [hbz, KaehlerDifferential.map_D, hb'z]
  rw [hδφ, hδφ']
  exact length_torsion_decrease_of_smooth_presentation π (algebraMap R R' π) hπ'irr (hRC' π)
    JC hIJ2 (by rwa [← IsScalarTower.algebraMap_apply R C C'] at hJC') hreg hkill hθ'k hθ hθ's
    r n b b' hmap_y hmap_z

end NeronModelInfra.Dilatations.DefectDecrease
end
