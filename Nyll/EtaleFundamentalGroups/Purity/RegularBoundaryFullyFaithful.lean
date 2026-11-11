/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
public import Nyll.SchemeTheory.Divisors.ConnectedComplement
public import Nyll.SchemeTheory.Divisors.EtaleRegularity
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict

public import Nyll.SchemeTheory.Etale.MaximalSectionExtension
public import Nyll.SchemeTheory.FiniteEtale.DensePullback
public import Nyll.SchemeTheory.FiniteEtale.FullOfSectionDescent
public import Nyll.SchemeTheory.FiniteEtale.ClopenFull
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full faithfulness across an arbitrary regular boundary

The connectedness argument used for Cartier complements in
`GeometricFiber.RegularBoundarySurjective` works for every dense open:
regularity at missing points supplies irreducible neighborhoods, and the
same remains true after finite etale pullback. Restriction therefore
preserves connected finite etale covers and is fully faithful.

This supplies uniqueness of local finite etale extensions in regular-boundary
purity, without assuming that the closed complement is a Cartier divisor.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A dense open of a connected locally Noetherian scheme stays connected
when the missing stalks are domains. -/
theorem connectedSpace_denseOpen_of_domain_boundary
    {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hboundary : ∀ (x : X), x ∉ U → IsDomain (X.presheaf.stalk x)) :
    ConnectedSpace U.toScheme := by
  apply SchemeTheory.connectedSpace_open_of_dense_of_irreducible_boundary_neighborhoods
    (U : Set X) U.isOpen hU
  intro x hx
  let : IsDomain (X.presheaf.stalk x) := hboundary x hx
  exact Scheme.exists_isIrreducible_open_of_isDomain_stalk x

/-- A connected finite etale cover remains connected on a dense open if
the ambient scheme is regular along the missing points. -/
theorem pullback_isConnected_of_denseOpen_regular_boundary
    {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    [ConnectedSpace U.toScheme]
    (W : FiniteEtale X) [IsConnected W] :
    IsConnected ((pullback U.ι).obj W) := by
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let f : W.left ⟶ X := W.hom
  let : IsFiniteEtale f := W.prop
  let : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian f
  let V : W.left.Opens := f ⁻¹ᵁ U
  have hV : Dense (V : Set W.left) := hU.preimage f.isOpenMap
  have hboundary : ∀ (w : W.left), w ∉ V → IsDomain (W.left.presheaf.stalk w) := by
    intro w hw
    have hfw : f w ∉ U := hw
    let : IsRegularLocalRing (W.left.presheaf.stalk w) :=
      Scheme.IsRegularAt.of_etale f w (hregular (f w) hfw)
    exact IsRegularLocalRing.isDomain (W.left.presheaf.stalk w)
  let : ConnectedSpace V.toScheme :=
    connectedSpace_denseOpen_of_domain_boundary V hV hboundary
  let e : ((pullback U.ι).obj W).left ≅ V.toScheme :=
    pullbackRestrictIsoRestrict f U
  let : ConnectedSpace ((pullback U.ι).obj W).left :=
    e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  exact isConnected_of_connectedSpace_left ((pullback U.ι).obj W)

/-- Finite etale covers and their morphisms restrict fully faithfully to a
dense open of a connected locally Noetherian scheme whose boundary is regular.
No divisor, ambient normality, or global Noetherianity is required. -/
theorem pullback_fullyFaithful_of_denseOpen_regular_boundary
    {X : Scheme.{u}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    Nonempty (pullback U.ι).FullyFaithful := by
  have hdomain : ∀ (x : X), x ∉ U → IsDomain (X.presheaf.stalk x) := by
    intro x hx
    let : IsRegularLocalRing (X.presheaf.stalk x) := hregular x hx
    exact IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  let : ConnectedSpace U.toScheme := connectedSpace_denseOpen_of_domain_boundary U hU hdomain
  apply pullback_fullyFaithful_of_preserves_connected U.ι
  intro W hW
  let : IsConnected W := hW
  exact pullback_isConnected_of_denseOpen_regular_boundary U hU hregular W

/-- A section of a finite etale cover on a dense open extends uniquely in
existence form across an arbitrary regular boundary of a locally Noetherian
scheme. -/
theorem exists_section_of_denseOpen_regular_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (B : FiniteEtale X) (s : U.toScheme ⟶ B.left) (hs : s ≫ B.hom = U.ι) :
    ∃ t : X ⟶ B.left, t ≫ B.hom = 𝟙 X ∧ U.ι ≫ t = s := by
  obtain ⟨N, hUN, b, hbf, hbu, hmax⟩ :=
    Etale.exists_maximal_open_section_extension (X := X) (Y := B.left)
      (show B.left ⟶ X from B.hom) U hU s hs
  have hN : N = ⊤ := by
    apply top_unique
    intro x _
    by_contra hxN
    have hxU : x ∉ U := fun hx ↦ hxN (hUN hx)
    let : IsRegularLocalRing (X.presheaf.stalk x) := hregular x hxU
    let : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    obtain ⟨O, hO, hxO, hirred⟩ := Scheme.exists_isIrreducible_open_of_isDomain_stalk x
    let V : X.Opens := ⟨O, hO⟩
    let : IrreducibleSpace V.toScheme := isIrreducible_iff_irreducibleSpace.mp hirred
    let VU : V.toScheme.Opens := V.ι ⁻¹ᵁ U
    have hVU : Dense (VU : Set V.toScheme) := hU.preimage V.ι.isOpenEmbedding.isOpenMap
    have hregV : ∀ (v : V.toScheme), v ∉ VU →
        IsRegularLocalRing (V.toScheme.presheaf.stalk v) := by
      intro v hv
      exact Scheme.IsRegularAt.of_etale V.ι v (hregular (V.ι v) hv)
    obtain ⟨hFF⟩ := pullback_fullyFaithful_of_denseOpen_regular_boundary VU hVU hregV
    let : (pullback VU.ι).Full := hFF.full
    let C : FiniteEtale V.toScheme := (pullback V.ι).obj B
    let l : VU.toScheme ⟶ U.toScheme := V.ι ∣_ U
    have hl : l ≫ U.ι = VU.ι ≫ V.ι := morphismRestrict_ι V.ι U
    let a : VU.toScheme ⟶ C.left :=
      Limits.pullback.lift (l ≫ s) VU.ι (by rw [Category.assoc, hs, hl])
    have haf : a ≫ C.hom = VU.ι := Limits.pullback.lift_snd _ _ _
    have haB : a ≫ Limits.pullback.fst B.hom V.ι = l ≫ s :=
      Limits.pullback.lift_fst _ _ _
    obtain ⟨d, hd, hdU⟩ := section_descent_of_pullback_full VU.ι C a haf
    let d₀ : V.toScheme ⟶ Limits.pullback B.hom V.ι := d
    let a₀ : VU.toScheme ⟶ Limits.pullback B.hom V.ι := a
    have hd₀ : d₀ ≫ Limits.pullback.snd B.hom V.ι = 𝟙 V.toScheme := hd
    have hdU₀ : VU.ι ≫ d₀ = a₀ := hdU
    have haB₀ : a₀ ≫ Limits.pullback.fst B.hom V.ι = l ≫ s := haB
    let c : V.toScheme ⟶ B.left := d₀ ≫ Limits.pullback.fst B.hom V.ι
    have hcf : c ≫ B.hom = V.ι := by
      change (d₀ ≫ Limits.pullback.fst B.hom V.ι) ≫ B.hom = V.ι
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hd₀,
        Category.id_comp]
    have hcu' : VU.ι ≫ c = l ≫ s := by
      change VU.ι ≫ (d₀ ≫ Limits.pullback.fst B.hom V.ι) = l ≫ s
      rw [← Category.assoc, hdU₀, haB₀]
    let e : (U ⊓ V).toScheme ≅ VU.toScheme :=
      (isPullback_opens_inf U V).isoIsPullback _ _ (isPullback_morphismRestrict V.ι U)
    have heU : e.hom ≫ l = X.homOfLE (show U ⊓ V ≤ U from inf_le_left) :=
      IsPullback.isoIsPullback_hom_fst U.toScheme V.toScheme
        (isPullback_opens_inf U V) (isPullback_morphismRestrict V.ι U)
    have heV : e.hom ≫ VU.ι = X.homOfLE (show U ⊓ V ≤ V from inf_le_right) :=
      IsPullback.isoIsPullback_hom_snd U.toScheme V.toScheme
        (isPullback_opens_inf U V) (isPullback_morphismRestrict V.ι U)
    have hcu : X.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ c := by
      rw [← heU, ← heV, Category.assoc, Category.assoc, hcu']
    exact hxN (hmax V c hcf hcu hxO)
  let e : N.toScheme ≅ X := X.isoOfEq hN ≪≫ X.topIso
  have he : e.hom = N.ι := X.isoOfEq_hom_ι hN
  let t : X ⟶ B.left := e.inv ≫ b
  have htf : t ≫ B.hom = 𝟙 X := by
    change (e.inv ≫ b) ≫ B.hom = 𝟙 X
    rw [Category.assoc, hbf, ← he, e.inv_hom_id]
  have hUi : U.ι ≫ e.inv = X.homOfLE hUN := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, he, Scheme.homOfLE_ι]
  refine ⟨t, htf, ?_⟩
  change U.ι ≫ (e.inv ≫ b) = s
  rw [← Category.assoc, hUi, hbu]

/-- Full faithfulness across any regular boundary of a locally Noetherian
scheme, with no connectedness or global Noetherianity assumption. -/
def denseOpenPullbackFullyFaithful_of_regular_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    (pullback U.ι).FullyFaithful := by
  let : (pullback U.ι).Full :=
    pullback_full_of_section_descent U.ι
      (exists_section_of_denseOpen_regular_boundary U hU hregular)
  let : IsDominant U.ι := Opens.isDominant_ι hU
  let : (pullback U.ι).Faithful := pullback_faithful_of_isDominant U.ι
  exact Functor.FullyFaithful.ofFullyFaithful (pullback U.ι)

/-- Restriction from any larger open to the original dense open is fully
faithful when the original boundary has regular local rings. -/
def denseOpenHomOfLEPullbackFullyFaithful_of_regular_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : Dense (U : Set X))
    (hregular : ∀ (x : X), x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (N : X.Opens) (hUN : U ≤ N) :
    (pullback (X.homOfLE hUN)).FullyFaithful := by
  let j : U.toScheme ⟶ N.toScheme := X.homOfLE hUN
  let : IsDominant j := Opens.isDominant_homOfLE hU hUN
  let O : N.toScheme.Opens := j.opensRange
  have hO : Dense (O : Set N.toScheme) := j.denseRange
  have hregularO : ∀ (n : N.toScheme), n ∉ O →
      IsRegularLocalRing (N.toScheme.presheaf.stalk n) := by
    intro n hn
    have hnU : N.ι n ∉ U := by
      change n ∉ j.opensRange at hn
      rw [Scheme.opensRange_homOfLE] at hn
      exact hn
    exact Scheme.IsRegularAt.of_etale N.ι n (hregular (N.ι n) hnU)
  have hsections : ∀ (B : FiniteEtale N.toScheme) (s : U.toScheme ⟶ B.left),
      s ≫ B.hom = j → ∃ t : N.toScheme ⟶ B.left,
        t ≫ B.hom = 𝟙 N.toScheme ∧ j ≫ t = s := by
    intro B s hs
    have hsO : (j.isoOpensRange.inv ≫ s) ≫ B.hom = O.ι := by
      rw [Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]
    obtain ⟨t, ht, hst⟩ := exists_section_of_denseOpen_regular_boundary
      O hO hregularO B (j.isoOpensRange.inv ≫ s) hsO
    refine ⟨t, ht, ?_⟩
    rw [← j.isoOpensRange_hom_ι, Category.assoc, hst, Iso.hom_inv_id_assoc]
  let : (pullback j).Full := pullback_full_of_section_descent j hsections
  let : (pullback j).Faithful := pullback_faithful_of_isDominant j
  exact Functor.FullyFaithful.ofFullyFaithful (pullback j)

end AlgebraicGeometry.FiniteEtale
