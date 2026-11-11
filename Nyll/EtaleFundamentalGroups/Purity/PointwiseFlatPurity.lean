/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The affine comparison for formal unramifiedness adapts the argument of
`formallySmooth_stalkMap_iff` in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:
Copyright (c) 2024 Christian Merten; Authors: Christian Merten; Apache 2.0.
-/

module

public import Nyll.SchemeTheory.RingTheory.Ramification.Trace.PointwiseFlatPurity
public import Nyll.SchemeTheory.Affine.StalkLocalization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sober

/-!
# Pointwise purity for flat quasi-finite morphisms

The original height-one unramified stalk maps are compared with those of an
affine chart. The affine purity criterion supplies an etale principal open,
which is mapped back to an actual open neighborhood in the original scheme.
Only finite type on a neighborhood of the chosen point is required.

Stacks Project, Tag 0BJH: https://stacks.math.columbia.edu/tag/0BJH.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The original stalk map is unramified exactly when its affine prime is unramified. -/
theorem formallyUnramified_stalkMap_iff_isUnramifiedAt
    {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  intro sharedOwner1
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let : q.LiesOver p :=
    ⟨congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx) |>.symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  change (f.stalkMap x).hom.FormallyUnramified ↔ Algebra.IsUnramifiedAt Γ(Y, U) q
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyUnramified_algebraMap]
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · constructor
    · intro h
      let : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := h
      exact Algebra.FormallyUnramified.comp Γ(Y, U) (Localization.AtPrime p)
        (Localization.AtPrime q)
    · intro h
      let : Algebra.IsUnramifiedAt Γ(Y, U) q := h
      exact Algebra.FormallyUnramified.of_restrictScalars Γ(Y, U)
        (Localization.AtPrime p) (Localization.AtPrime q)

/-- Etaleness at an affine prime gives an actual etale open in the original scheme. -/
theorem exists_etale_open_of_isEtaleAt_appLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (hfp : (f.appLE U V hVU).hom.FinitePresentation)
    (hetale :
      let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
      Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let : Algebra R S := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.FinitePresentation R S := hfp
  let q := hV.primeIdealOf ⟨x, hx⟩
  let : Algebra.IsEtaleAt R q.asIdeal := hetale
  obtain ⟨a, haq, ha⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q.asIdeal
  let L := Localization.Away a
  let : Algebra.Etale R L := ha
  let i : Spec (CommRingCat.of L) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S L))
  let j : Spec (CommRingCat.of L) ⟶ X := i ≫ hV.fromSpec
  let g : Spec (CommRingCat.of L) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R L))
  let : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr ha)
  have hmap : f.appLE U V hVU ≫ CommRingCat.ofHom (algebraMap S L) =
      CommRingCat.ofHom (algebraMap R L) := by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq R S L).symm
  have hj : j ≫ f = g ≫ hU.fromSpec := by
    dsimp only [j, g, i]
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU,
      ← Category.assoc, ← Spec.map_comp, hmap]
  let : Etale (j ≫ f) := by rw [hj]; infer_instance
  have hxj : x ∈ j.opensRange := by
    have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S L)) := by
      rw [PrimeSpectrum.localization_away_comap_range L a]
      exact haq
    obtain ⟨z, hz⟩ := hq
    refine ⟨z, ?_⟩
    change hV.fromSpec (i z) = x
    rw [show i z = q from hz]
    exact hV.fromSpec_primeIdealOf ⟨x, hx⟩
  refine ⟨j.opensRange, hxj, ?_⟩
  have h : Etale (j.isoOpensRange.inv ≫ (j ≫ f)) := inferInstance
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] at h
  exact h

/-- Codimension-one unramified stalk maps at the generalizations of a
point give the original height-one prime condition in every affine chart. -/
theorem isUnramifiedAt_height_one_appLE_of_specializations
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V)
    (hunramified : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (q' : Ideal Γ(X, V)) [q'.IsPrime],
      q' ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal → q'.height = 1 →
        Algebra.IsUnramifiedAt Γ(Y, U) q' := by
  intro alg
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let q := hV.primeIdealOf ⟨x, hxV⟩
  intro q' _ hq'q hq'height
  let y : V := hV.isoSpec.inv (⟨q', inferInstance⟩ : PrimeSpectrum S)
  have hy : hV.primeIdealOf y = (⟨q', inferInstance⟩ : PrimeSpectrum S) :=
    Scheme.inv_hom_apply hV.isoSpec _
  have hyx : (y : X) ⤳ x := by
    have hspecial : (⟨q', inferInstance⟩ : PrimeSpectrum S) ⤳ q :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hq'q
    have hmap := hspecial.map hV.fromSpec.continuous
    rw [← hy, hV.fromSpec_primeIdealOf y,
      hV.fromSpec_primeIdealOf ⟨x, hxV⟩] at hmap
    exact hmap
  have hydim : ringKrullDim (X.presheaf.stalk (y : X)) = 1 := by
    let : Algebra S (X.presheaf.stalk (y : X)) := X.presheaf.algebra_section_stalk y
    let : IsLocalization.AtPrime (X.presheaf.stalk (y : X))
        (hV.primeIdealOf y).asIdeal := hV.isLocalization_stalk y
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf y).asIdeal
      (X.presheaf.stalk (y : X)), hy, hq'height]
    rfl
  have hlocal := (formallyUnramified_stalkMap_iff_isUnramifiedAt U hU V hV hVU y.2).mp
    (hunramified y hyx hydim)
  change Algebra.IsUnramifiedAt R (hV.primeIdealOf y).asIdeal at hlocal
  rw [hy] at hlocal
  exact hlocal

/-- Positive local dimension suffices for the pointwise flat purity criterion. -/
theorem exists_etale_open_of_flat_of_quasiFiniteAt_of_positive_dimension
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (x : X)
    (hquasi : f.QuasiFiniteAt x)
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hunramified : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  change V ≤ f ⁻¹ᵁ U at hVU
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let : Algebra R S := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra.FiniteType R S := f.finiteType_appLE hU hV hVU
  let : Module.Flat R S := f.flat_appLE hU hV hVU
  let q := hV.primeIdealOf ⟨x, hxV⟩
  let : Algebra.QuasiFiniteAt R q.asIdeal := hquasi.quasiFiniteAt hV hU hVU hxV
  have hqheight : 1 ≤ q.asIdeal.height := by
    let : Algebra S (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
      hV.isLocalization_stalk ⟨x, hxV⟩
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
      (X.presheaf.stalk x)] at hdim
    exact_mod_cast hdim
  apply exists_etale_open_of_isEtaleAt_appLE f U hU V hV hVU hxV
    (f.finitePresentation_appLE hU hV hVU)
  apply SchemeTheory.isEtaleAt_of_flat_of_quasiFiniteAt_of_isUnramifiedAt_height_one
    q.asIdeal hqheight
  exact isUnramifiedAt_height_one_appLE_of_specializations f x U hU V hV hVU hxV
    hunramified

/-- Stacks Project, Tag 0BJH. A flat map between locally Noetherian schemes
is etale on a neighborhood of a quasi-finite point which is not generic,
provided the original stalk maps are unramified at all codimension-one
generalizations. The finite-type assumption is imposed only near that point,
as in the usual definition of being quasi-finite at a point. -/
theorem exists_etale_open_of_flat_of_quasiFiniteAt_of_unramified_codimensionOne
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (x : X)
    (hfiniteType : ∃ T : X.Opens, x ∈ T ∧ LocallyOfFiniteType (T.ι ≫ f))
    (hquasi : f.QuasiFiniteAt x) (hnotgeneric : x ∉ genericPoints X)
    (hunramified : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
    let C : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let η : genericPoints X := genericPoints.ofComponent C
    have hηx : η.1 ⤳ x :=
      (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
    have hxη : x < η.1 := by
      refine ⟨hηx, ?_⟩
      intro hxη
      apply hnotgeneric
      have heq : x = η.1 := (hxη.antisymm hηx).eq
      rw [heq]
      exact η.2
    rw [ringKrullDim_stalk_eq_coheight]
    apply WithBot.coe_le_coe.mpr
    exact (show (1 : ℕ∞) ≤ Order.coheight η.1 + 1 from
      le_add_self).trans (Order.coheight_add_one_le hxη)
  obtain ⟨T, hxT, hTfinite⟩ := hfiniteType
  let : LocallyOfFiniteType (T.ι ≫ f) := hTfinite
  let t : T := ⟨x, hxT⟩
  have htquasi : (T.ι ≫ f).QuasiFiniteAt t :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr hquasi
  have htdim : (1 : WithBot ℕ∞) ≤ ringKrullDim (T.toScheme.presheaf.stalk t) := by
    rw [IsOpenImmersion.ringKrullDim_stalk_eq T.ι t]
    exact hdim
  obtain ⟨V, htV, hVetale⟩ :=
    exists_etale_open_of_flat_of_quasiFiniteAt_of_positive_dimension
      (T.ι ≫ f) t htquasi htdim (by
        intro t' htt' hdim'
        have hspecial : T.ι t' ⤳ x := htt'.map T.ι.continuous
        have hdimX : ringKrullDim (X.presheaf.stalk (T.ι t')) = 1 := by
          rw [← IsOpenImmersion.ringKrullDim_stalk_eq T.ι t']
          exact hdim'
        have heq : ((T.ι ≫ f).stalkMap t').hom =
            (T.ι.stalkMap t').hom.comp (f.stalkMap (T.ι t')).hom :=
          congrArg (fun a : Y.presheaf.stalk (f (T.ι t')) ⟶
            T.toScheme.presheaf.stalk t' => a.hom) (Scheme.Hom.stalkMap_comp T.ι f t')
        exact heq.symm ▸ (hunramified (T.ι t') hspecial hdimX).comp
          (FormallyUnramified.stalkMap T.ι t'))
  let j : V.toScheme ⟶ X := V.ι ≫ T.ι
  let : Etale (j ≫ f) := by
    dsimp only [j]
    rw [Category.assoc]
    exact hVetale
  refine ⟨j.opensRange, ⟨⟨t, htV⟩, rfl⟩, ?_⟩
  have h : Etale (j.isoOpensRange.inv ≫ (j ≫ f)) := inferInstance
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] at h
  exact h

end AlgebraicGeometry
