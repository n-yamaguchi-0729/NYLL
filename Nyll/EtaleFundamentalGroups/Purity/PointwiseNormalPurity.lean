/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.PointwiseFlatPurity
public import Nyll.EtaleFundamentalGroups.Purity.PointwiseNormalBranchCriterion
public import Nyll.SchemeTheory.Affine.StalkLocalization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Purity of the branch locus at a point

For a quasi-finite map, normality of the source local ring, regularity of
the target local ring, equality of their positive dimensions, and
unramifiedness at the original codimension-one generalizations construct
an etale open neighborhood. Finite type is required only near the point.
The equality of dimensions is used by the affine criterion to construct
injectivity of the finite local factor; dominance and flatness are not
additional hypotheses.

Stacks Project, Tag 0BMB: https://stacks.math.columbia.edu/tag/0BMB.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace EtaleFundamentalGroups

namespace AlgebraicGeometry

universe u

private theorem exists_etale_open_of_normal_of_regular_of_locallyOfFiniteType
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hquasi : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpositive : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
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
  let q := hV.primeIdealOf ⟨x, hxV⟩
  let p := hU.primeIdealOf ⟨f x, hVU hxV⟩
  let : Algebra.QuasiFiniteAt R q.asIdeal := hquasi.quasiFiniteAt hV hU hVU hxV
  have hqp : q.asIdeal.under R = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
  let : Algebra S (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let eS : X.presheaf.stalk x ≃ₐ[S] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv q.asIdeal.primeCompl _ _
  let : IsDomain (Localization.AtPrime q.asIdeal) :=
    MulEquiv.isDomain (X.presheaf.stalk x) eS.symm.toRingEquiv.toMulEquiv
  let : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    IsIntegrallyClosed.of_equiv eS.toRingEquiv
  let : Algebra R (Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p.asIdeal :=
    hU.isLocalization_stalk ⟨f x, hVU hxV⟩
  let eR : Y.presheaf.stalk (f x) ≃ₐ[R] Localization.AtPrime p.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularLocalRing.of_ringEquiv eR.toRingEquiv
  have hqpspec : (⟨q.asIdeal.under R, inferInstance⟩ : PrimeSpectrum R) = p :=
    PrimeSpectrum.ext hqp
  let : IsRegularLocalRing (Localization.AtPrime (q.asIdeal.under R)) :=
    (congrArg (fun r : PrimeSpectrum R => IsRegularLocalRing (Localization.AtPrime r.asIdeal))
      hqpspec).mpr inferInstance
  have hheight : q.asIdeal.height = (q.asIdeal.under R).height := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk x),
      IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Y.presheaf.stalk (f x))] at hdim
    rw [hqp]
    exact WithBot.coe_injective hdim
  have hqpositive : 1 ≤ q.asIdeal.height := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk x)] at hpositive
    exact_mod_cast hpositive
  apply exists_etale_open_of_isEtaleAt_appLE f U hU V hV hVU hxV
    (f.finitePresentation_appLE hU hV hVU)
  apply isEtaleAt_of_normal_of_regular_of_quasiFiniteAt_of_isUnramifiedAt_height_one
      q.asIdeal hheight hqpositive
  exact isUnramifiedAt_height_one_appLE_of_specializations f x U hU V hV hVU hxV hunramified

/-- Stacks Project, Tag 0BMB: purity of the branch locus at the original
point. Normality and regularity are only required at the two specified
stalks; their equal positive dimensions and the original codimension-one
unramifiedness construct an actual etale open neighborhood. -/
theorem exists_etale_open_of_normal_of_regular_of_quasiFiniteAt_of_unramified_codimensionOne
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hfiniteType : ∃ T : X.Opens, x ∈ T ∧ LocallyOfFiniteType (T.ι ≫ f))
    (hquasi : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpositive : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hunramified : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f) := by
  obtain ⟨T, hxT, hTfinite⟩ := hfiniteType
  let : LocallyOfFiniteType (T.ι ≫ f) := hTfinite
  let t : T := ⟨x, hxT⟩
  have : IsIso (T.ι.stalkMap t) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion T.ι)).2 t
  let : IsRegularLocalRing (Y.presheaf.stalk ((T.ι ≫ f) t)) := by
    change IsRegularLocalRing (Y.presheaf.stalk (f x))
    infer_instance
  let e : X.presheaf.stalk x ≃+* T.toScheme.presheaf.stalk t :=
    (asIso (T.ι.stalkMap t)).commRingCatIsoToRingEquiv
  let : IsDomain (T.toScheme.presheaf.stalk t) :=
    MulEquiv.isDomain (X.presheaf.stalk x) e.symm.toMulEquiv
  let : IsIntegrallyClosed (T.toScheme.presheaf.stalk t) := IsIntegrallyClosed.of_equiv e
  have htquasi : (T.ι ≫ f).QuasiFiniteAt t :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr hquasi
  have htdim : ringKrullDim (T.toScheme.presheaf.stalk t) =
      ringKrullDim (Y.presheaf.stalk ((T.ι ≫ f) t)) := by
    rw [IsOpenImmersion.ringKrullDim_stalk_eq T.ι t]
    exact hdim
  have htpositive : (1 : WithBot ℕ∞) ≤ ringKrullDim (T.toScheme.presheaf.stalk t) := by
    rw [IsOpenImmersion.ringKrullDim_stalk_eq T.ι t]
    exact hpositive
  obtain ⟨V, htV, hVetale⟩ :=
    exists_etale_open_of_normal_of_regular_of_locallyOfFiniteType
      (T.ι ≫ f) t htquasi htdim htpositive (by
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
