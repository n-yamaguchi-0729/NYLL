/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationCover
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecializationFunctor
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.StrictHenselianProperFiberSurjective
public import Nyll.EtaleFundamentalGroups.GaloisCategories.ExactSequence
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.NeronModels.AbelianExtensions

/-!
# Multiplication covers under actual proper specialization

At every index invertible in the original local base, the multiplication
cover on either fibre is the pullback of the same multiplication cover on
the total space. The proper-complete specialization functor therefore
recovers the original generic multiplication cover. Its fundamental-group
kernel fixes every generic connected cover of degree invertible in the base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Base change retains the actual multiplication morphism as a finite étale cover. -/
def unitMultiplicationCoverBaseChangeIso
    {R R' : Type u} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {A : Scheme.{u}} {f : A ⟶ Spec (.of R)} [IsProper f] [Smooth f]
    (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    (ι : Spec (.of R') ⟶ Spec (.of R))
    (n : ℕ) (hn : IsUnit (n : R)) (hn' : IsUnit (n : R')) :
    (G.baseChange ι).unitMultiplicationCover (IsCommutative.baseChange ι hc) n hn' ≅
      (FiniteEtale.pullback (Limits.pullback.fst f ι)).obj
        (G.unitMultiplicationCover hc n hn) := by
  let h := (G.isPullback_baseChange_schemeNsmul ι n).flip
  exact MorphismProperty.Over.isoMk h.isoPullback h.isoPullback_hom_snd

section CompleteLocal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of R)} [hProper : IsProper f] [hSmooth : Smooth f]
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
  {k : Type u} [Field k] [IsSepClosed k]
  (aₛ : R →+* k) (ι : IsLocalRing.ResidueField R →+* k)
  (hs : Spec.map (CommRingCat.ofHom aₛ) = Spec.map (CommRingCat.ofHom ι) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  {K : Type u} [Field K] (aη : R →+* K)

/-- Lifting the actual closed-fibre multiplication cover through the proper
closed-fibre equivalence recovers the original generic multiplication cover. -/
def unitMultiplicationCoverSpecializationIso (n : ℕ) (hn : IsUnit (n : R)) :
    let s := Spec.map (CommRingCat.ofHom aₛ)
    let η := Spec.map (CommRingCat.ofHom aη)
    let hnₛ : IsUnit (n : k) := by simpa only [map_natCast] using hn.map aₛ
    let hnη : IsUnit (n : K) := by simpa only [map_natCast] using hn.map aη
    (properCompleteGeometricSpecializationFunctor R f s ι hs η).obj
        ((G.baseChange s).unitMultiplicationCover (IsCommutative.baseChange s hc) n hnₛ) ≅
      (G.baseChange η).unitMultiplicationCover (IsCommutative.baseChange η hc) n hnη := by
  intro s η hnₛ hnη
  exact (properCompleteGeometricSpecializationFunctor R f s ι hs η).mapIso
      (G.unitMultiplicationCoverBaseChangeIso hc s n hn hnₛ) ≪≫
    (properCompleteGeometricSpecializationFunctor_recovery R f s ι hs η).app
      (G.unitMultiplicationCover hc n hn) ≪≫
    (G.unitMultiplicationCoverBaseChangeIso hc η n hn hnη).symm

/-- The kernel of the original specialization homomorphism acts trivially on
an original generic multiplication fibre at every invertible base index. -/
theorem specialization_kernel_fixes_unitMultiplicationCover
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (.of Ωη) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom aη)))
    (xs : Spec (.of Ωs) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom aₛ)))
    (t : fiber (xη ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom aη))) ≅
      fiber (xs ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom aₛ))))
    (γ : π₁ᵉᵗ(xη))
    (hγ : properCompleteGeometricSpecializationHom R f
      (Spec.map (CommRingCat.ofHom aₛ)) ι hs (Spec.map (CommRingCat.ofHom aη))
      xη xs t γ = 1)
    (n : ℕ) (hn : IsUnit (n : R)) :
    let η := Spec.map (CommRingCat.ofHom aη)
    let hnη : IsUnit (n : K) := by simpa only [map_natCast] using hn.map aη
    ∀ z : (fiber xη).obj
        ((G.baseChange η).unitMultiplicationCover (IsCommutative.baseChange η hc) n hnη),
      γ • z = z := by
  intro η hnη z
  let s := Spec.map (CommRingCat.ofHom aₛ)
  have htotal : fundamentalGroupHom (Limits.pullback.fst f η) xη γ = 1 := by
    apply (continuousConjAut t).injective
    calc
      continuousConjAut t (fundamentalGroupHom (Limits.pullback.fst f η) xη γ) =
          fundamentalGroupHom (Limits.pullback.fst f s) xs
            (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t γ) :=
        (properCompleteGeometricSpecializationHom_triangle R f s ι hs η xη xs t γ).symm
      _ = 1 := by rw [hγ, map_one]
      _ = continuousConjAut t 1 := (map_one (continuousConjAut t)).symm
  let W := G.unitMultiplicationCover hc n hn
  let e := G.unitMultiplicationCoverBaseChangeIso hc η n hn hnη
  let v := (fiber xη).map e.hom z
  have hv : γ • v = v := by
    apply (ConcreteCategory.bijective_of_isIso
      ((pullbackFiberIso (Limits.pullback.fst f η) xη).hom.app W)).injective
    change (pullbackFiberIso (Limits.pullback.fst f η) xη).hom.app W
        (γ.asIso.hom.app ((FiniteEtale.pullback (Limits.pullback.fst f η)).obj W) v) = _
    rw [pullbackFiberIso_hom_fundamentalGroupHom_apply, htotal]
    rfl
  apply (ConcreteCategory.bijective_of_isIso ((fiber xη).map e.hom)).injective
  exact (mulAction_naturality (fiber xη) γ e.hom z).symm.trans hv

include hc hSmooth in
/-- Multiplication-cover domination shows that the actual specialization
kernel fixes every connected generic cover whose degree is invertible in the
original base ring. -/
theorem specialization_kernel_fixes_cover_of_degree_isUnit
    [IsSepClosed K] [GeometricallyConnected f]
    {Ωη Ωs : Type u} [Field Ωη] [IsSepClosed Ωη] [Field Ωs]
    (xη : Spec (.of Ωη) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom aη)))
    (xs : Spec (.of Ωs) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom aₛ)))
    (t : fiber (xη ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom aη))) ≅
      fiber (xs ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom aₛ))))
    (γ : π₁ᵉᵗ(xη))
    (hγ : properCompleteGeometricSpecializationHom R f
      (Spec.map (CommRingCat.ofHom aₛ)) ι hs (Spec.map (CommRingCat.ofHom aη))
      xη xs t γ = 1) :
    let η := Spec.map (CommRingCat.ofHom aη)
    let Gη := G.baseChange η
    ∀ (W : FiniteEtale (Limits.pullback f η)) [IsConnected W],
      IsUnit ((Nat.card ((fiber (Gη.one (𝟙 (Spec (.of K)))).1).obj W)) : R) →
      ∀ z : (fiber xη).obj W, γ • z = z := by
  intro η Gη W hW hn z
  let hGη : Gη.IsCommutative := IsCommutative.baseChange η hc
  have : ConnectedSpace ↑(Limits.pullback f η) :=
    GeometricallyConnected.connectedSpace (baseChangeStr η f)
      (baseChangeStr η f).isOpenMap
  let n := Nat.card ((fiber (Gη.one (𝟙 (Spec (.of K)))).1).obj W)
  have hnη : IsUnit (n : K) := by simpa only [map_natCast] using hn.map aη
  obtain ⟨q⟩ := Gη.nonempty_unitMultiplicationCover_hom hGη W hnη
  have : IsConnected (Gη.unitMultiplicationCover hGη n hnη) :=
    Gη.isConnected_unitMultiplicationCover hGη n hnη
  obtain ⟨y, rfl⟩ := surjective_of_nonempty_fiber_of_isConnected (fiber xη) q z
  exact (mulAction_naturality (fiber xη) γ q y).trans
    (congrArg ((fiber xη).map q)
      (G.specialization_kernel_fixes_unitMultiplicationCover hc aₛ ι hs aη
        xη xs t γ hγ n hn y))

omit [IsNoetherianRing R] in
include hc hProper hSmooth in
/-- A connected finite étale cover of the generic abelian variety whose
degree is a unit in the original base extends to an actual finite étale
cover of the given abelian scheme. The generic identification is constructed
from multiplication-cover domination and the proper homotopy sequence. -/
theorem exists_unitDegree_cover_model
    [IsSepClosed K] [GeometricallyConnected f] :
    let η := Spec.map (CommRingCat.ofHom aη)
    let Gη := G.baseChange η
    ∀ (W : FiniteEtale (Limits.pullback f η)) [IsConnected W],
      IsUnit ((Nat.card ((fiber (Gη.one (𝟙 (Spec (.of K)))).1).obj W)) : R) →
      ∃ Z : FiniteEtale A,
        Nonempty ((FiniteEtale.pullback (Limits.pullback.fst f η)).obj Z ≅ W) := by
  intro η Gη W hW hn
  let hGη : Gη.IsCommutative := IsCommutative.baseChange η hc
  have : HenselianLocalRing R :=
    { toIsLocalRing := inferInstance
      is_henselian := fun q hq a ha hder =>
        HenselianRing.is_henselian q hq a ha
          (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) }
  have : PreconnectedSpace (Spec (.of R)) := by
    refine ⟨?_⟩
    intro U V hU hV hcover hneU hneV
    rcases hcover (Set.mem_univ (IsLocalRing.closedPoint R)) with h | h
    · obtain ⟨v, _, hv⟩ := hneV
      exact ⟨v, trivial, (IsLocalRing.specializes_closedPoint v).mem_open hU h, hv⟩
    · obtain ⟨v, _, hv⟩ := hneU
      exact ⟨v, trivial, hv, (IsLocalRing.specializes_closedPoint v).mem_open hV h⟩
  have : ConnectedSpace (Spec (.of R)) := ⟨⟨IsLocalRing.closedPoint R⟩⟩
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace ↑(Limits.pullback f η) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.snd f η)
  let xi := (Gη.one (𝟙 (Spec (.of K)))).1
  let n := Nat.card ((fiber xi).obj W)
  have hnη : IsUnit (n : K) := by simpa only [map_natCast] using hn.map aη
  obtain ⟨q⟩ := Gη.nonempty_unitMultiplicationCover_hom hGη W hnη
  have : IsConnected (Gη.unitMultiplicationCover hGη n hnη) :=
    Gη.isConnected_unitMultiplicationCover hGη n hnη
  have : Epi q := epi_of_nonempty_of_isConnected (fiber xi) q
  let e := G.unitMultiplicationCoverBaseChangeIso hc η n hn hnη
  let p := e.inv ≫ q
  have : Epi p := inferInstance
  have hsurj := fundamentalGroupHom_smoothProper_fiberFst_surjective_of_strictHenselian
    R f η xi
  exact essImage_of_epi_of_autHom_surjective
    (FiniteEtale.pullback (Limits.pullback.fst f η))
    (pullbackFiberIso (Limits.pullback.fst f η) xi) hsurj
    (G.unitMultiplicationCover hc n hn) W p

include hc hSmooth in
/-- The preceding actual extension gives a closed-fibre cover whose proper
specialization is the specified generic cover, with the original generic
cover retained in the conclusion. -/
theorem exists_unitDegree_specialization_cover
    [IsSepClosed K] [GeometricallyConnected f] :
    let s := Spec.map (CommRingCat.ofHom aₛ)
    let η := Spec.map (CommRingCat.ofHom aη)
    let Gη := G.baseChange η
    ∀ (W : FiniteEtale (Limits.pullback f η)) [IsConnected W],
      IsUnit ((Nat.card ((fiber (Gη.one (𝟙 (Spec (.of K)))).1).obj W)) : R) →
      ∃ V : FiniteEtale (Limits.pullback f s),
        Nonempty ((properCompleteGeometricSpecializationFunctor R f s ι hs η).obj V ≅ W) := by
  intro s η Gη W hW hn
  obtain ⟨Z, ⟨e⟩⟩ := G.exists_unitDegree_cover_model hc aη W hn
  exact ⟨(FiniteEtale.pullback (Limits.pullback.fst f s)).obj Z,
    ⟨(properCompleteGeometricSpecializationFunctor_recovery R f s ι hs η).app Z ≪≫ e⟩⟩

end CompleteLocal

section CompleteDVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of R)} [hProper : IsProper f] [hSmooth : Smooth f]
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)

include hc hProper hSmooth in
/-- The Néron extension property constructs the actual relative map from a
smooth quasi-compact source to the given abelian scheme over a complete
strict local DVR. Every unit-degree geometric generic cover of the target
then pulls back to a cover extending on that original source. The fraction
field used by the Néron property and the separably closed geometric field
are kept distinct. -/
theorem exists_genericMap_unitDegree_cover_extension
    [GeometricallyConnected f]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [Smooth t] [QuasiCompact t]
    (uF : SchemeHomOver (Limits.pullback.snd t (specGenericFibreInclusion R F))
      (Limits.pullback.snd f (specGenericFibreInclusion R F))) :
    ∃ u : SchemeHomOver t f,
      genericFibreRestrict R F f t u = uF ∧
      properFamilyFiberMap t f u.val u.property (specGenericFibreInclusion R F) = uF.val ∧
      ∀ (K' : Type u) [Field K'] [IsSepClosed K'] (a : R →+* K'),
        let η := Spec.map (CommRingCat.ofHom a)
        let Gη := G.baseChange η
        ∀ (V : FiniteEtale (Limits.pullback f η)) [IsConnected V],
          IsUnit ((Nat.card ((fiber (Gη.one (𝟙 (Spec (.of K')))).1).obj V)) : R) →
          ∃ Z : FiniteEtale T,
            Nonempty ((FiniteEtale.pullback (Limits.pullback.fst t η)).obj Z ≅
              (FiniteEtale.pullback (properFamilyFiberMap t f u.val u.property η)).obj V) := by
  have hA : AbelianSchemePropertyBundle R f :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => f.isConnected_preimage_singleton s
      hasGroupLaw := ⟨G⟩ }
  obtain ⟨u, hu⟩ := hA.genericFibreRestrict_surjective_of_quasiCompact R F t uF
  have hmap : properFamilyFiberMap t f u.val u.property (specGenericFibreInclusion R F) =
      (genericFibreRestrict R F f t u).val := by
    apply Limits.pullback.hom_ext
    · exact (properFamilyFiberMap_fst t f u.val u.property
        (specGenericFibreInclusion R F)).trans
          (genericFibreRestrict_coe_comp_fst R F f t u).symm
    · exact (properFamilyFiberMap_snd t f u.val u.property
        (specGenericFibreInclusion R F)).trans
          (genericFibreRestrict_coe_comp_snd R F f t u).symm
  refine ⟨u, hu, hmap.trans (congrArg Subtype.val hu), ?_⟩
  intro K' hK' hsep' a η Gη V hV hn
  obtain ⟨Z, ⟨e⟩⟩ := G.exists_unitDegree_cover_model hc a V hn
  exact ⟨(FiniteEtale.pullback u.val).obj Z,
    ⟨(properFamilyFiberPullbackIso t f u.val u.property η).app Z ≪≫
      (FiniteEtale.pullback (properFamilyFiberMap t f u.val u.property η)).mapIso e⟩⟩

end CompleteDVR

end GoodReductionJacobian.RelativeGroupLaw
