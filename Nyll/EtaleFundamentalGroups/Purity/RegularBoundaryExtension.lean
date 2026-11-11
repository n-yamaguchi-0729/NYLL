/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.DVRBoundaryEnlargement
public import Nyll.EtaleFundamentalGroups.Purity.GenericComplementCoverExtension
public import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalCompletionDescent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.CompatibleStalkCoverSpreading
public import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.FiniteEtale.MaximalOpenExtension
public import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
public import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDimensionOne
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Extending unramified covers across a regular boundary

Over a Noetherian scheme, a finite etale cover of a dense open extends when
all missing stalks are regular and its actual generic field factors are
unramified at the dimension-one boundary points. A maximal extension can
be enlarged at every generic missing point: the DVR construction handles
dimension one and regular-local punctured purity handles larger dimension.

This is the Noetherian global step in Stacks Project, Lemma 58.31.2
(https://stacks.math.columbia.edu/tag/0H2W). The locally Noetherian theorem
also needs descent of these extensions from Noetherian open subschemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A point outside a dense open of a Noetherian scheme has a
positive-dimensional stalk. A generic point of an irreducible component
through it gives the required strict chain of generizations. -/
theorem one_le_ringKrullDim_stalk_of_not_mem_dense_open
    {X : Scheme.{u}} [NoetherianSpace X]
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let η : genericPoints X := genericPoints.ofComponent C
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure {η.1}) η.2
  obtain ⟨z, hzO, hzU⟩ := hU.inter_open_nonempty O hO hOne
  have hηU : η.1 ∈ U :=
    ((genericPoints.isGenericPoint η).mem_open_set_iff U.isOpen).mpr
      ⟨z, hOC hzO, hzU⟩
  have hηx : η.1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  have hxη : x < η.1 := by
    refine ⟨hηx, ?_⟩
    intro hxη
    exact hx ((show x ⤳ η.1 from hxη).mem_open U.isOpen hηU)
  have hheight : (1 : ℕ∞) ≤ Order.coheight x := by
    calc
      (1 : ℕ∞) = 0 + 1 := (zero_add 1).symm
      _ ≤ Order.coheight η.1 + 1 :=
        add_le_add_left (show (0 : ℕ∞) ≤ Order.coheight η.1 from zero_le) 1
      _ ≤ Order.coheight x := Order.coheight_add_one_le hxη
  rw [ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr hheight

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] Ideal.Quotient.field
  finiteEtaleOverCategoryCoherence finiteEtaleHasPullbacksAlongCoherence
  finiteEtaleStableUnderBaseChangeAlongCoherence

/-- A cover of a dense open of a Noetherian scheme extends across a regular
boundary if its actual generic field factors are unramified at every
codimension-one boundary point. The stalk models and their comparisons are
constructed; they are not hypotheses of the theorem. -/
theorem exists_extension_of_regular_boundary_of_unramified_codimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (Y : FiniteEtale U.toScheme)
    (hunramified : ∀ (x : X) (hx : x ∉ U)
      (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)),
      let R : CommRingCat.{u} := X.presheaf.stalk x
      let : IsRegularLocalRing R := hregular x hx
      let : IsDomain R := IsRegularLocalRing.isDomain R
      let : IsDiscreteValuationRing R :=
        SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
      let K : Type u := FractionRing R
      let r : Spec (.of K) ⟶ U.toScheme :=
        Scheme.denseOpenDVRFractionFieldMap U hU x hx hdim
      let A : CommAlgCat.FiniteEtale.{u} K :=
        (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback r).obj Y))
      let : Algebra R A := Algebra.compHom A (algebraMap R K)
      ∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) :
    ∃ Z : FiniteEtale X, Nonempty ((pullback U.ι).obj Z ≅ Y) := by
  obtain ⟨N, hUN, W, ⟨eW⟩, hmax⟩ := exists_maximal_open_extension U Y
  have hN : N = ⊤ := by
    apply top_unique
    intro z _
    by_contra hzN
    let zC : {z : X // z ∉ N} := ⟨z, hzN⟩
    have hclosed : IsClosed {z : X | z ∉ N} := N.isOpen.isClosed_compl
    have : QuasiSober {z : X // z ∉ N} :=
      hclosed.isClosedEmbedding_subtypeVal.quasiSober
    let C : irreducibleComponents {z : X // z ∉ N} :=
      ⟨irreducibleComponent zC, irreducibleComponent_mem_irreducibleComponents zC⟩
    let x : genericPoints {z : X // z ∉ N} := genericPoints.ofComponent C
    have hxU : x.1.1 ∉ U := fun hx ↦ x.1.2 (hUN hx)
    let : IsRegularLocalRing (X.presheaf.stalk x.1.1) := hregular x.1.1 hxU
    by_cases hdim : ringKrullDim (X.presheaf.stalk x.1.1) = (1 : WithBot ℕ∞)
    · obtain ⟨M, hNM, hxM, Z, hZN⟩ :=
        exists_open_enlargement_at_regular_dimension_one_boundary
          U N hU hUN x.1.1 x.1.2 hdim Y W eW (hunramified x.1.1 hxU hdim)
      exact x.1.2 (hmax M hNM Z hZN hxM)
    · have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x.1.1) :=
        Scheme.one_le_ringKrullDim_stalk_of_not_mem_dense_open U hU x.1.1 hxU
      have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x.1.1) := by
        rw [ringKrullDim_stalk_eq_coheight] at hpos hdim ⊢
        apply WithBot.coe_le_coe.mpr
        by_contra hlt
        have hle : Order.coheight x.1.1 ≤ 1 :=
          ENat.lt_two_iff.mp (lt_of_not_ge hlt)
        have hge : (1 : ℕ∞) ≤ Order.coheight x.1.1 := WithBot.coe_le_coe.mp hpos
        exact hdim (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) (hle.antisymm hge))
      have hpurity : HasPuncturedPurity (X.presheaf.stalk x.1.1) :=
        EtaleFundamentalGroups.hasPuncturedPurity_of_isRegularLocalRing
          (X.presheaf.stalk x.1.1) htwo
      obtain ⟨L, ⟨a⟩⟩ := exists_stalk_cover_extension_of_generic_complement N x hpurity W
      let : NoetherianSpace N.toScheme :=
        N.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
      obtain ⟨M, hxM, B, ⟨b⟩⟩ :=
        exists_compatible_open_cover_fromSpecStalk X N x.1.1 W L a
      obtain ⟨Z, hZN, _⟩ := exists_glued_over_sup X N M W B b.symm
      have hNM : N ⊔ M ≤ N := hmax (N ⊔ M) le_sup_left Z hZN
      exact x.1.2 (hNM ((show M ≤ N ⊔ M from le_sup_right) hxM))
  let eN : N.toScheme ≅ X := X.isoOfEq hN ≪≫ X.topIso
  have heN : eN.hom = N.ι := X.isoOfEq_hom_ι hN
  have hUi : X.homOfLE hUN = U.ι ≫ eN.inv := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, eN.inv_hom_id, Category.comp_id, heN, Scheme.homOfLE_ι]
  let c : pullback (X.homOfLE hUN) ≅ pullback eN.inv ⋙ pullback U.ι :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      U.ι eN.inv (X.homOfLE hUN) hUi
  exact ⟨(pullback eN.inv).obj W, ⟨(c.app W).symm ≪≫ eW⟩⟩

end AlgebraicGeometry.FiniteEtale

namespace AlgebraicGeometry.Scheme

universe u

/-- Positive stalk dimension outside a dense open is local on a locally
Noetherian ambient scheme. -/
theorem one_le_ringKrullDim_stalk_of_not_mem_dense_open_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : NoetherianSpace V.toScheme := noetherianSpace_of_isAffineOpen V hV
  let xV : V.toScheme := ⟨x, hxV⟩
  let UV : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have hUV : Dense (UV : Set V.toScheme) := hU.preimage V.ι.isOpenEmbedding.isOpenMap
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim (V.toScheme.presheaf.stalk xV) :=
    one_le_ringKrullDim_stalk_of_not_mem_dense_open UV hUV xV hx
  have heq : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (V.toScheme.presheaf.stalk xV) :=
    ringKrullDim_eq_of_ringEquiv (asIso (V.ι.stalkMap xV)).commRingCatIsoToRingEquiv
  rw [heq]
  exact hpos

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] Ideal.Quotient.field
  finiteEtaleOverCategoryCoherence finiteEtaleHasPullbacksAlongCoherence
  finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The ascending chain condition is needed only on one observation open:
a cover has an extension whose domain cannot be enlarged inside that open.
The resulting cover still extends the entire original domain. -/
theorem exists_open_extension_maximal_on_noetherian_open
    {X : Scheme.{u}} (U V : X.Opens) [NoetherianSpace V.toScheme]
    (Y : FiniteEtale U.toScheme) :
    ∃ (N : X.Opens) (hUN : U ≤ N) (W : FiniteEtale N.toScheme),
      Nonempty ((pullback (X.homOfLE hUN)).obj W ≅ Y) ∧
      ∀ (M : X.Opens) (hNM : N ≤ M) (Z : FiniteEtale M.toScheme),
        Nonempty ((pullback (X.homOfLE hNM)).obj Z ≅ W) →
          V.ι ⁻¹ᵁ M ≤ V.ι ⁻¹ᵁ N := by
  let P (A : V.toScheme.Opens) : Prop :=
    ∃ (N : X.Opens) (hUN : U ≤ N) (W : FiniteEtale N.toScheme),
      V.ι ⁻¹ᵁ N = A ∧ Nonempty ((pullback (X.homOfLE hUN)).obj W ≅ Y)
  have hU : P (V.ι ⁻¹ᵁ U) := by
    refine ⟨U, le_rfl, Y, rfl, ⟨?_⟩⟩
    rw [Scheme.homOfLE_rfl]
    exact (pullbackIdIso U.toScheme).app Y
  obtain ⟨A, hmax⟩ := exists_maximal_of_wellFoundedGT P ⟨V.ι ⁻¹ᵁ U, hU⟩
  obtain ⟨N, hUN, W, hNA, ⟨eW⟩⟩ := hmax.1
  refine ⟨N, hUN, W, ⟨eW⟩, ?_⟩
  intro M hNM Z ⟨a⟩
  rw [hNA]
  apply hmax.2
  · refine ⟨M, hUN.trans hNM, Z, rfl, ⟨?_⟩⟩
    let c : pullback (X.homOfLE (hUN.trans hNM)) ≅
        pullback (X.homOfLE hNM) ⋙ pullback (X.homOfLE hUN) :=
      MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
        (X.homOfLE hUN) (X.homOfLE hNM) (X.homOfLE (hUN.trans hNM))
        (X.homOfLE_homOfLE hUN hNM).symm
    exact c.app Z ≪≫ (pullback (X.homOfLE hUN)).mapIso a ≪≫ eW
  · rw [← hNA]
    exact V.ι.preimage_mono hNM

/-- Every point admits an extension neighborhood containing the entire
original dense open, under regular-boundary purity and the original
unramified codimension-one field-factor condition. -/
theorem exists_open_extension_containing_point_of_regular_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (Y : FiniteEtale U.toScheme)
    (hunramified : ∀ (x : X) (hx : x ∉ U)
      (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞)),
      let R : CommRingCat.{u} := X.presheaf.stalk x
      let : IsRegularLocalRing R := hregular x hx
      let : IsDomain R := IsRegularLocalRing.isDomain R
      let : IsDiscreteValuationRing R :=
        SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
      let K : Type u := FractionRing R
      let r : Spec (.of K) ⟶ U.toScheme :=
        Scheme.denseOpenDVRFractionFieldMap U hU x hx hdim
      let A : CommAlgCat.FiniteEtale.{u} K :=
        (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback r).obj Y))
      let : Algebra R A := Algebra.compHom A (algebraMap R K)
      ∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal))
    (z : X) :
    ∃ (N : X.Opens) (hUN : U ≤ N), z ∈ N ∧
      ∃ Z : FiniteEtale N.toScheme,
        Nonempty ((pullback (X.homOfLE hUN)).obj Z ≅ Y) := by
  obtain ⟨V, hV, hzV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : NoetherianSpace V.toScheme := noetherianSpace_of_isAffineOpen V hV
  obtain ⟨N, hUN, W, ⟨eW⟩, hmax⟩ := exists_open_extension_maximal_on_noetherian_open U V Y
  refine ⟨N, hUN, ?_, W, ⟨eW⟩⟩
  by_contra hzN
  let zC : {z : X // z ∉ N} := ⟨z, hzN⟩
  have hclosed : IsClosed {z : X | z ∉ N} := N.isOpen.isClosed_compl
  have : QuasiSober {z : X // z ∉ N} :=
    hclosed.isClosedEmbedding_subtypeVal.quasiSober
  let C : irreducibleComponents {z : X // z ∉ N} :=
    ⟨irreducibleComponent zC, irreducibleComponent_mem_irreducibleComponents zC⟩
  let x : genericPoints {z : X // z ∉ N} := genericPoints.ofComponent C
  have hxz : x.1.1 ⤳ z :=
    (subtype_specializes_iff x.1 zC).mp
      ((genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent)
  have hxV : x.1.1 ∈ V := hxz.mem_open V.isOpen hzV
  let xV : V.toScheme := ⟨x.1.1, hxV⟩
  have hxU : x.1.1 ∉ U := fun hx ↦ x.1.2 (hUN hx)
  let : IsRegularLocalRing (X.presheaf.stalk x.1.1) := hregular x.1.1 hxU
  by_cases hdim : ringKrullDim (X.presheaf.stalk x.1.1) = (1 : WithBot ℕ∞)
  · obtain ⟨M, hNM, hxM, Z, hZN⟩ :=
      exists_open_enlargement_at_regular_dimension_one_boundary
        U N hU hUN x.1.1 x.1.2 hdim Y W eW (hunramified x.1.1 hxU hdim)
    exact x.1.2 (hmax M hNM Z hZN (show xV ∈ V.ι ⁻¹ᵁ M from hxM))
  · have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x.1.1) :=
      Scheme.one_le_ringKrullDim_stalk_of_not_mem_dense_open_of_isLocallyNoetherian
        U hU x.1.1 hxU
    have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x.1.1) := by
      rw [ringKrullDim_stalk_eq_coheight] at hpos hdim ⊢
      apply WithBot.coe_le_coe.mpr
      by_contra hlt
      have hle : Order.coheight x.1.1 ≤ 1 := ENat.lt_two_iff.mp (lt_of_not_ge hlt)
      have hge : (1 : ℕ∞) ≤ Order.coheight x.1.1 := WithBot.coe_le_coe.mp hpos
      exact hdim (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) (hle.antisymm hge))
    have hpurity : HasPuncturedPurity (X.presheaf.stalk x.1.1) :=
      EtaleFundamentalGroups.hasPuncturedPurity_of_isRegularLocalRing
        (X.presheaf.stalk x.1.1) htwo
    obtain ⟨L, ⟨a⟩⟩ := exists_stalk_cover_extension_of_generic_complement N x hpurity W
    obtain ⟨M, hxM, B, ⟨b⟩⟩ :=
      exists_compatible_open_cover_fromSpecStalk X N x.1.1 W L a
    obtain ⟨Z, hZN, _⟩ := exists_glued_over_sup X N M W B b.symm
    have hxNM : xV ∈ V.ι ⁻¹ᵁ (N ⊔ M) :=
      (show M ≤ N ⊔ M from le_sup_right) hxM
    exact x.1.2 (hmax (N ⊔ M) le_sup_left Z hZN hxNM)

end AlgebraicGeometry.FiniteEtale
