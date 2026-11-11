/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteQuotientRealization
public import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.ChartFunctionFieldCompatibility
public import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.ComponentMappedFiniteQuotientInertia
public import Nyll.EtaleFundamentalGroups.Kummer.Normalization.EssentiallyEtaleBaseChangeInertiaContraction
public import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteQuotientNormalizationInertiaCoprimality
public import Nyll.SchemeTheory.LocalGeometry.EtaleStalkPrimeLocalization
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.EtaleFundamentalGroups.Kummer.Normalization.EtaleBaseChangeInertiaCardinality
public import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealImage
public import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction

/-!
# Finite-quotient inertia along a normal-crossings component

This file transports the local normal-crossings calculation at a selected
horizontal component to the inertia image in an explicitly prescribed finite
quotient of the global complement's etale fundamental group.
-/

@[expose] public section

noncomputable section


open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups TopologicalSpace
open AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups renaming
  normalizationInertia_natCard_eq_at_essentiallyEtale_contraction_of_functionFieldProduct_surjective
    → normalizationInertiaCardComparison
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u v

variable {X S : Scheme.{u}}

private noncomputable def transportStalkIdeal
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (q : Ideal (T.presheaf.stalk x)) :
    Ideal (T.presheaf.stalk x') :=
  h ▸ q

private theorem transportStalkIdeal_isPrime
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (q : Ideal (T.presheaf.stalk x)) (hq : q.IsPrime) :
    (transportStalkIdeal h q).IsPrime := by
  subst x'
  exact hq

private theorem transportStalkIdeal_height
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (q : Ideal (T.presheaf.stalk x)) :
    (transportStalkIdeal h q).height = q.height := by
  subst x'
  rfl

private theorem transportStalkIdeal_charZero
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (q : Ideal (T.presheaf.stalk x))
    [CharZero (T.presheaf.stalk x ⧸ q)] :
    CharZero (T.presheaf.stalk x' ⧸ transportStalkIdeal h q) := by
  subst x'
  change CharZero (T.presheaf.stalk x ⧸ q)
  infer_instance

private theorem integralClosure_galAction_eq
    {V KC M : Type u}
    [CommRing V] [IsDomain V]
    [Field KC] [Field M]
    [Algebra V KC] [IsFractionRing V KC]
    [Algebra KC M] [Algebra V M] [IsScalarTower V KC M]
    [FiniteDimensional KC M] [_root_.IsGalois KC M] :
    let B := integralClosure V M
    let actionIC : MulSemiringAction Gal(M/KC) B :=
      IsIntegralClosure.MulSemiringAction V KC M B
    let actionSub : MulSemiringAction Gal(M/KC) B :=
      instMulSemiringActionSubtypeMemSubalgebraIntegralClosure
    ∀ (g : Gal(M/KC)) (x : B),
      @SMul.smul Gal(M/KC) B actionIC.toSMul g x =
        @SMul.smul Gal(M/KC) B actionSub.toSMul g x := by
  dsimp only
  intro g x
  apply Subtype.ext
  change algebraMap (integralClosure V M) M
      (@SMul.smul Gal(M/KC) (integralClosure V M)
        (IsIntegralClosure.MulSemiringAction V KC M
          (integralClosure V M)).toSMul g x) =
    algebraMap (integralClosure V M) M
      (@SMul.smul Gal(M/KC) (integralClosure V M)
        instMulSemiringActionSubtypeMemSubalgebraIntegralClosure.toSMul g x)
  calc
    _ = g (x : M) := algebraMap_galRestrictHom_apply
      V KC M (integralClosure V M) g x
    _ = _ := (integralClosure.coe_smul g x).symm

private theorem integralClosure_galInertia_natCard_eq
    {V KC M : Type u}
    [CommRing V] [IsDomain V]
    [Field KC] [Field M]
    [Algebra V KC] [IsFractionRing V KC]
    [Algebra KC M] [Algebra V M] [IsScalarTower V KC M]
    [FiniteDimensional KC M] [_root_.IsGalois KC M]
    (Q : Ideal (integralClosure V M)) :
    let B := integralClosure V M
    let actionIC : MulSemiringAction Gal(M/KC) B :=
      IsIntegralClosure.MulSemiringAction V KC M B
    let actionSub : MulSemiringAction Gal(M/KC) B :=
      instMulSemiringActionSubtypeMemSubalgebraIntegralClosure
    Nat.card
        (@AddSubgroup.inertia B _ Q.toAddSubgroup Gal(M/KC) _
          actionIC.toMulAction) =
      Nat.card
        (@AddSubgroup.inertia B _ Q.toAddSubgroup Gal(M/KC) _
          actionSub.toMulAction) := by
  dsimp only
  have hsub :
      @AddSubgroup.inertia (integralClosure V M) _ Q.toAddSubgroup
          Gal(M/KC) _
          (IsIntegralClosure.MulSemiringAction V KC M
            (integralClosure V M)).toMulAction =
        @AddSubgroup.inertia (integralClosure V M) _ Q.toAddSubgroup
          Gal(M/KC) _
          instMulSemiringActionSubtypeMemSubalgebraIntegralClosure.toMulAction := by
    ext g
    change
      (∀ x : integralClosure V M,
        @SMul.smul Gal(M/KC) (integralClosure V M)
            (IsIntegralClosure.MulSemiringAction V KC M
              (integralClosure V M)).toSMul g x - x ∈ Q) ↔
      (∀ x : integralClosure V M,
        @SMul.smul Gal(M/KC) (integralClosure V M)
            instMulSemiringActionSubtypeMemSubalgebraIntegralClosure.toSMul g x - x ∈ Q)
    constructor
    · intro h x
      rw [← integralClosure_galAction_eq
        (V := V) (KC := KC) (M := M) g x]
      exact h x
    · intro h x
      rw [integralClosure_galAction_eq
        (V := V) (KC := KC) (M := M) g x]
      exact h x
  exact congrArg (fun H : Subgroup Gal(M/KC) => Nat.card H) hsub

private theorem exists_integralClosurePrime_liesOver
    {V KC M : Type u}
    [CommRing V] [IsDomain V]
    [Field KC] [Field M]
    [Algebra V KC] [IsFractionRing V KC]
    [Algebra KC M] [Algebra V M] [IsScalarTower V KC M]
    [FiniteDimensional KC M]
    (qV : Ideal V) [qV.IsPrime] :
    ∃ Q : Ideal (integralClosure V M), Q.IsPrime ∧ Q.LiesOver qV := by
  let B := integralClosure V M
  let : IsFractionRing B M :=
    IsIntegralClosure.isFractionRing_of_finite_extension V KC M B
  have hVB : Function.Injective (algebraMap V B) := by
    intro a b hab
    have hab' := congrArg (fun x : B ↦ (x : M)) hab
    change algebraMap V M a = algebraMap V M b at hab'
    have habKC : algebraMap V KC a = algebraMap V KC b := by
      apply FaithfulSMul.algebraMap_injective KC M
      simpa only [IsScalarTower.algebraMap_apply V KC M] using hab'
    exact IsFractionRing.injective V KC habKC
  obtain ⟨Q, -, hQPrime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral qV
      (⊥ : Ideal B) (by
        change Ideal.comap (algebraMap V B) ⊥ ≤ qV
        rw [← RingHom.ker_eq_comap_bot,
          (RingHom.injective_iff_ker_eq_bot _).mp hVB]
        exact bot_le)
  exact ⟨Q, hQPrime, (Ideal.liesOver_iff Q qV).mpr hQcomap.symm⟩

private theorem finiteEtaleGaloisCoverIdealInertia_coprime_iff_image_coprime
    {T : Scheme.{u}} [IsIntegral T] [IsNormalIntegral T]
    [IsLocallyNoetherian T]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ T)
    (Y : FiniteEtale T) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let K := T.functionField
    let L := Y.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Y
    ∀ (V B : Type u) [CommRing V] [CommRing B]
      [Algebra V K] [IsFractionRing V K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra V B] [Algebra V L]
      [IsScalarTower V K L] [IsScalarTower V B L]
      [IsIntegrallyClosed V] [IsIntegralClosure B V L]
      (Q : Ideal B) (p : ℕ),
      let : FiniteDimensional K L :=
        EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction V K L B
      let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY V B
      let qY :=
        EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi Y hY y
      let H := Subgroup.map qY
        (Subgroup.comap qY (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ))
      Nat.Coprime (Nat.card H) p ↔
        Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro sharedOwner1 sharedOwner2 K L sharedOwner5 V B _ _ _ _ _ _ _ _ _ _ _ _ Q p
    finiteKL fieldAction coverAction qY H
  rw [EtaleFundamentalGroups.Kummer.natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
    xi Y hY y V B Q]

private theorem pullbackComponent_integralClosureInertia_coprime
    {T R : Scheme.{u}} [IsIntegral T] [IsNormalIntegral T]
    [IsLocallyNoetherian T]
    [ConnectedSpace R]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (c : T ⟶ R) (xi : Spec (.of Omega) ⟶ T)
    (W : FiniteEtale R)
    (hW : CategoryTheory.PreGaloisCategory.IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ c)).obj W)
    (Y : FiniteEtale T) (i : Y ⟶ (FiniteEtale.pullback c).obj W)
    (y : (FiniteEtale.fiber xi).obj Y)
    (hiy : (FiniteEtale.fiber xi).map i y =
      transportedPointOfCompIso
        (FiniteEtale.pullback c) (FiniteEtale.pullbackFiberIso c xi) W w)
    (hY : CategoryTheory.PreGaloisCategory.IsGalois Y) (hi : Mono i) :
    let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    let : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    let K := T.functionField
    let L := Y.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Y
    ∀ (V B : Type u) [CommRing V] [CommRing B]
      [Algebra V K] [IsFractionRing V K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra V B] [Algebra V L]
      [IsScalarTower V K L] [IsScalarTower V B L]
      [IsIntegrallyClosed V] [IsIntegralClosure B V L]
      (Q : Ideal B) (p : ℕ),
      let : FiniteDimensional K L :=
        EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction V K L B
      let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY V B
      let qY :=
        EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi Y hY y
      let H := Subgroup.map qY
        (Subgroup.comap qY (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ))
      Nat.Coprime
          (Nat.card (H.map
            (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
              c xi W hW w Y i y hiy hY hi))) p →
        Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro sharedOwner1 sharedOwner2 K L sharedOwner5 V B _ _ _ _ _ _ _ _ _ _ _ _ Q p
    finiteKL fieldAction coverAction qY H hMapped
  have hH : Nat.Coprime (Nat.card H) p :=
    (FiniteEtale.galoisPullbackComponentQuotientMonoidHom_map_coprime_iff
      c xi W hW w Y i y hiy hY hi H p).mp hMapped
  exact (finiteEtaleGaloisCoverIdealInertia_coprime_iff_image_coprime
    xi Y hY y V B Q p).mp hH

private theorem transportedComponentBranchData
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    {U : Scheme.{u}} (f : U ⟶ X) (u : U)
    (hfu : f u = D.1.subschemeι z) :
    let A := X.presheaf.stalk (f u)
    let p0 := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
    let pA : Ideal A := transportStalkIdeal hfu.symm p0
    pA.IsPrime ∧ pA.height = 1 ∧ CharZero (A ⧸ pA) := by
  intro A p0 pA
  let x := D.1.subschemeι z
  let : p0.IsPrime :=
    (D.1.componentBranchPrimeAt Z hZ z hz).isPrime
  have hp0height : p0.height = 1 :=
    D.2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  have hIp0 : D.1.stalkIdeal x ≤ p0 :=
    D.1.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz
  let : CharZero (X.presheaf.stalk x ⧸ p0) :=
    (hD.hasCharacteristicZeroBranchesAt D structural)
      p0 inferInstance hp0height hIp0
  exact ⟨transportStalkIdeal_isPrime hfu.symm p0 inferInstance,
    (transportStalkIdeal_height hfu.symm p0).trans hp0height,
    transportStalkIdeal_charZero hfu.symm p0⟩

private theorem exists_contractedNormalizationPrime_coprime
    {A C F KC L M : Type u}
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [IsIntegrallyClosed C] [Algebra A C]
    [Algebra.EssFiniteType A C] [Algebra.FormallyEtale A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [FiniteDimensional F L] [_root_.IsGalois F L]
    [Field M] [Algebra KC M] [Algebra C M]
    [FiniteDimensional KC M] [_root_.IsGalois KC M]
    [Algebra L M] [Algebra F M] [Algebra A M]
    [IsScalarTower C KC M] [IsScalarTower F KC M]
    [IsScalarTower F L M] [IsScalarTower A C M]
    [IsScalarTower A L M]
    (p : ℕ)
    (hgeneric : Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom F KC M)
        (IsScalarTower.toAlgHom F L M)))
    (pA : Ideal A) [pA.IsPrime] (hpAheight : pA.height = 1)
    (qV : Ideal C) [qV.IsPrime] (hqVheight : qV.height = 1)
    [qV.LiesOver pA]
    (Q : Ideal (integralClosure C M)) [Q.IsPrime] [Q.LiesOver qV]
    [CharZero (A ⧸ pA)] [CharZero (C ⧸ qV)]
    (hQcoprimeIntegralClosure :
      let actionIC : MulSemiringAction Gal(M/KC) (integralClosure C M) :=
        IsIntegralClosure.MulSemiringAction C KC M (integralClosure C M)
      Nat.Coprime
        (Nat.card
          (letI := actionIC
           Q.toAddSubgroup.inertia Gal(M/KC))) p) :
    let q := Q.comap
      (EtaleFundamentalGroups.integralClosureEtaleBaseChangeHom
        (A := A) (C := C) (L := L) (M := M))
    q.IsPrime ∧ q.LiesOver pA ∧
      Nat.Coprime (Nat.card (q.toAddSubgroup.inertia Gal(L/F))) p := by
  dsimp only at hQcoprimeIntegralClosure ⊢
  obtain ⟨hqPrime, hqOver, hcard⟩ :=
    normalizationInertiaCardComparison
      (A := A) (C := C) (F := F) (KC := KC) (L := L) (M := M)
      hgeneric pA hpAheight qV hqVheight Q
  have hQcoprimeGeneric :=
    Eq.mp (congrArg (fun n => Nat.Coprime n p)
      (integralClosure_galInertia_natCard_eq
        (V := C) (KC := KC) (M := M) Q))
      hQcoprimeIntegralClosure
  exact ⟨hqPrime, hqOver,
    Eq.mp (congrArg (fun n => Nat.Coprime n p) hcard)
      hQcoprimeGeneric⟩

private def ComponentNormalizationInertiaCoprimeResult
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (p : ℕ) [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    {U : Scheme.{u}} (f : U ⟶ X) (u : U)
    (hfu : f u = D.1.subschemeι z) : Prop :=
  let K := (D.1.supportComplement : Scheme).functionField
  let : IsIntegral D.1.supportComplement :=
    isIntegral_of_isOpenImmersion D.1.supportComplement.ι
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
  let A := X.presheaf.stalk (f u)
  let : Algebra A K := D.1.supportComplementFunctionFieldAlgebra (f u)
  let : IsFractionRing A K :=
    D.1.supportComplementFunctionField_isFractionRing (f u)
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
    hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
  ∃ q : Ideal B, q.IsPrime ∧ q.LiesOver branchPrime ∧
    Nat.Coprime (Nat.card (q.toAddSubgroup.inertia Gal(L/K))) p

private theorem exists_componentNormalizationInertia_coprime_of_mappedChart
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (U : Scheme.{u}) (f : U ⟶ X) (u : U)
    (hfu : f u = D.1.subschemeι z) (hf : Etale f)
    (qU : Ideal (U.presheaf.stalk u))
    (hqUPrime : qU.IsPrime) (hqUheight : qU.height = 1)
    (hqUcomap : qU.comap (f.stalkMap u).hom =
      hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal)
    (hlocal :
      letI : IsIntegral D.1.supportComplement :=
        isIntegral_of_isOpenImmersion D.1.supportComplement.ι
      D.1.HasMappedQuotientIdealInertiaCoprime f u qU p) :
    ComponentNormalizationInertiaCoprimeResult
      D Z hZ z hz p W hW f u hfu := by
  delta ComponentNormalizationInertiaCoprimeResult
  intro F integralComplement integralW L algebraFL finiteFL galoisFL A algebraAF fractionAF
    algebraAL towerAFL B fractionBL branchPrime
  let : IsNormalIntegral D.1.supportComplement := inferInstance
  let : IsLocallyNoetherian D.1.supportComplement := inferInstance
  let : IsGalois W := hW
  let : Etale f := hf
  let : qU.IsPrime := hqUPrime
  delta Scheme.IdealSheafData.HasMappedQuotientIdealInertiaCoprime at hlocal
  extract_lets -descend -merge AU at hlocal
  obtain ⟨P, hqUP, hPheight, hchart⟩ := hlocal
  extract_lets -descend -merge V qV at hchart
  obtain ⟨r, t, branch, hVdomain, hVregular, hVnormal, hboundary, hLocalNC,
    hbranch, hqVeq, hlocalizedCharZero, hpV, hcovers⟩ := hchart
  extract_lets -descend -merge domainV regularV normalV boundary hboundary_ne Away
    domainAway normalAway c at hcovers
  let : IsIntegrallyClosed A :=
    IsNormalIntegral.stalk_isIntegrallyClosed (f u)
  let : qV.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P.asIdeal hqUP.le
  have hc : DenseRange c :=
    Scheme.IdealSheafData.boundaryAwayToSupportComplement_denseRange
      D.1 f u P t hboundary_ne hboundary hVdomain
  have hcomponent := hcovers W hW
  extract_lets -descend -merge s Omega xiLocal wLocal at hcomponent
  obtain ⟨Y, i, y, hiy, hY, hi, hQmapped⟩ := hcomponent
  extract_lets -descend -merge galoisY integralY KC M algebraKCM algebraVKC algebraVM
    towerVKCM fractionVKC finiteKCM galoisKCM BLocal fractionBLocalM
    integralClosureAction normalizationAction at hQmapped
  let : Mono i := hi
  let g := FiniteEtale.pullbackComponentToOriginal c W Y i
  let hg := FiniteEtale.pullbackComponentToOriginal_denseRange c hc W Y i
  let : Algebra F KC := c.functionFieldAlgebraOfDenseRange hc
  let : Algebra L M := g.functionFieldAlgebraOfDenseRange hg
  let : Algebra F M :=
    ((algebraMap KC M).comp (algebraMap F KC)).toAlgebra
  let : IsScalarTower F KC M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq'
    (FiniteEtale.pullbackComponent_functionFieldMap_compatibility
      c hc W Y i).symm
  let : Algebra A AU := (f.stalkMap u).hom.toAlgebra
  let : Algebra A V := f.stalkPrimeLocalizationAlgebra u P.asIdeal
  let : SMul A V := (inferInstance : Algebra A V).toSMul
  let : IsScalarTower A AU V := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A KC :=
    ((algebraMap V KC).comp (algebraMap A V)).toAlgebra
  let : IsScalarTower A V KC := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A F KC := IsScalarTower.of_algebraMap_eq'
    (Scheme.IdealSheafData.boundaryAway_functionFieldMap_comp_ambientStalk
      D.1 f u P t hboundary_ne hboundary).symm
  let : Algebra A M :=
    ((algebraMap V M).comp (algebraMap A V)).toAlgebra
  let : IsScalarTower A V M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A KC M := IsScalarTower.to₁₃₄ A V KC M
  let : IsScalarTower A F M := IsScalarTower.to₁₂₄ A F KC M
  let : IsScalarTower A L M := IsScalarTower.to₁₃₄ A F L M
  let : Algebra.EssFiniteType A V :=
    f.stalkPrimeLocalization_essFiniteType_of_etale u P.asIdeal
  let : Algebra.FormallyEtale A V :=
    f.stalkPrimeLocalization_formallyEtale_of_etale u P.asIdeal
  let p0 := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
  let pA : Ideal A := transportStalkIdeal hfu.symm p0
  have hbranchData :
      pA.IsPrime ∧ pA.height = 1 ∧ CharZero (A ⧸ pA) := by
    simpa only [A, p0, pA] using
      (transportedComponentBranchData D structural Z hZ z hz hD f u hfu)
  let : pA.IsPrime := hbranchData.1
  have hpAheight : pA.height = 1 := hbranchData.2.1
  let : CharZero (A ⧸ pA) := hbranchData.2.2
  have hqUcomap' : qU.comap (f.stalkMap u).hom = pA := by
    simpa only [pA, p0, transportStalkIdeal] using hqUcomap
  have hdisjoint : Disjoint
      ((P.asIdeal.primeCompl : Submonoid AU) : Set AU) (qU : Set AU) :=
    Set.disjoint_compl_left_iff_subset.mpr hqUP.le
  let : qU.LiesOver pA := ⟨hqUcomap'.symm⟩
  let : qV.LiesOver qU :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      P.asIdeal.primeCompl V hdisjoint
  let : qV.LiesOver pA := Ideal.LiesOver.trans qV qU pA
  have hqVheight : qV.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint
      P.asIdeal.primeCompl qU hdisjoint]
    exact hqUheight
  let : CharZero (V ⧸ qV) :=
    hqVeq.symm ▸ hlocalizedCharZero branch hbranch
  obtain ⟨Q, hQPrime, hQover⟩ :=
    exists_integralClosurePrime_liesOver
      (V := V) (KC := KC) (M := M) qV
  let : Q.IsPrime := hQPrime
  let : Q.LiesOver qV := hQover
  have hMapped := hQmapped Q hQPrime hQover
  extract_lets -descend -merge qY H at hMapped
  have hQcoprimeIntegralClosure : Nat.Coprime
      (Nat.card
        (letI := integralClosureAction
         Q.toAddSubgroup.inertia Gal(M/KC))) p := by
    exact pullbackComponent_integralClosureInertia_coprime
      c xiLocal W hW wLocal Y i y hiy hY hi V BLocal Q p hMapped
  have hgeneric : Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom F KC M)
        (IsScalarTower.toAlgHom F L M)) :=
    FiniteEtale.pullbackComponentFunctionFieldProductMap_surjective
      c hc W Y i
  obtain ⟨hqPrime, hqOver, hqCoprime⟩ :=
    exists_contractedNormalizationPrime_coprime
      (A := A) (C := V) (F := F) (KC := KC) (L := L) (M := M)
      p hgeneric pA hpAheight qV hqVheight Q hQcoprimeIntegralClosure
  let q := Q.comap
    (EtaleFundamentalGroups.integralClosureEtaleBaseChangeHom
      (A := A) (C := V) (L := L) (M := M))
  exact ⟨q, hqPrime, hqOver, hqCoprime⟩

/-- For a selected component through a locally horizontal normal-crossings
point, normalization inertia in every connected finite-etale Galois cover
of the complement has order prime to the residue characteristic.  The prime
on the original normalization is obtained by literal contraction from the
chosen pullback component. -/
theorem ComponentsThroughPointAreHorizontal.exists_componentNormalizationInertia_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    (hNC : D.1.IsNormalCrossingsAt (D.1.subschemeι z))
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    (hp : p.Prime) [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W) :
    let K := (D.1.supportComplement : Scheme).functionField
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let L := W.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    let : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
      (hfu : f u = D.1.subschemeι z), Etale f ∧
      let A := X.presheaf.stalk (f u)
      let : Algebra A K := D.1.supportComplementFunctionFieldAlgebra (f u)
      let : IsFractionRing A K :=
        D.1.supportComplementFunctionField_isFractionRing (f u)
      let : Algebra A L :=
        ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
      let B := integralClosure A L
      let : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
        hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
      ∃ q : Ideal B, q.IsPrime ∧ q.LiesOver branchPrime ∧
        Nat.Coprime (Nat.card (q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro K integralComplement integralW L algebraKL finiteKL galoisKL
  let : IsNormalIntegral D.1.supportComplement := inferInstance
  let : IsLocallyNoetherian D.1.supportComplement := inferInstance
  obtain ⟨U, f, u, hfu, hf, -, -, qU, hqUPrime, hqUheight, -,
      hqUcomap, hlocal⟩ :=
    hD.exists_etaleStrictChart_component_mappedQuotientIdealInertia_coprime
      D structural Z hZ z hz hNC p hp
  refine ⟨U, f, u, hfu, hf, ?_⟩
  intro A algebraAK fractionAK algebraAL towerAKL B fractionBL branchPrime
  exact exists_componentNormalizationInertia_coprime_of_mappedChart
    D structural Z hZ z hz hD p W hW U f u hfu hf qU hqUPrime
      hqUheight hqUcomap hlocal

namespace ComponentsThroughPointAreHorizontal

/-- A prescribed finite quotient of the complement's etale fundamental group
is realized by a connected Galois cover, and the inertia image attached to the
chosen normal-crossings component has order prime to the residue
characteristic.  The normalization prime lies over the literal transport of
the selected component branch to the stalk of the returned etale chart. -/
theorem exists_finiteQuotient_componentNormalizationInertiaImage_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    (hNC : D.1.IsNormalCrossingsAt (D.1.subschemeι z))
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    (hp : p.Prime)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ D.1.supportComplement)
    {G : Type v} [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) (hphi : Function.Surjective phi) :
    let : Nonempty D.1.supportComplement :=
      ⟨xi (genericPoint (Spec (.of Omega)))⟩
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsNormalIntegral D.1.supportComplement := inferInstance
    let : IsLocallyNoetherian D.1.supportComplement := inferInstance
    ∃ (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
      (w : (FiniteEtale.fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G),
      let : IsGalois W := hW
      e.toMonoidHom.comp
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w) = phi.toMonoidHom ∧
        ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
          (hfu : f u = D.1.subschemeι z), Etale f ∧
          let K := (D.1.supportComplement : Scheme).functionField
          let : IsIntegral W.left :=
            EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
          let L := W.left.functionField
          let : Algebra K L :=
            EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
          let : FiniteDimensional K L :=
            EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
          let : _root_.IsGalois K L :=
            EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
          let A := X.presheaf.stalk (f u)
          let : IsIntegrallyClosed A :=
            IsNormalIntegral.stalk_isIntegrallyClosed (f u)
          let : Algebra A K :=
            D.1.supportComplementFunctionFieldAlgebra (f u)
          let : IsFractionRing A K :=
            D.1.supportComplementFunctionField_isFractionRing (f u)
          let : Algebra A L :=
            ((algebraMap K L).comp (algebraMap A K)).toAlgebra
          let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
          let B := integralClosure A L
          let : IsFractionRing B L :=
            IsIntegralClosure.isFractionRing_of_finite_extension A K L B
          let : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
            EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
              W hW A B
          let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
            hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
          ∃ q : Ideal B, q.IsPrime ∧ q.LiesOver branchPrime ∧
            Nat.Coprime
              (Nat.card
                ((Subgroup.comap
                  (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
                    xi W hW w)
                  (q.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ)).map
                    phi.toMonoidHom)) p := by
  intro nonemptyComplement integralComplement normalComplement noetherianComplement
  obtain ⟨W, hW, w, e, hcomp⟩ :=
    exists_galoisCover_quotient_mulEquiv xi G phi hphi
  refine ⟨W, hW, w, e, ?_⟩
  intro galoisW
  refine ⟨hcomp, ?_⟩
  obtain ⟨U, f, u, hfu, hf, hPrime⟩ :=
    hD.exists_componentNormalizationInertia_coprime
      D structural Z hZ z hz hNC p hp W hW
  refine ⟨U, f, u, hfu, hf, ?_⟩
  intro K integralW L algebraKL finiteKL galoisKL A normalA algebraAK fractionAK
    algebraAL towerAKL B fractionBL normalizationAction branchPrime
  obtain ⟨q, hqPrime, hqOver, hqCoprime⟩ := hPrime
  let actionIC : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  have hqCoprimeIC : Nat.Coprime
      (Nat.card
        (letI := actionIC
         q.toAddSubgroup.inertia Gal(L/K))) p :=
    Eq.mpr (congrArg (fun n => Nat.Coprime n p)
      (integralClosure_galInertia_natCard_eq
        (V := A) (KC := K) (M := L) q)) hqCoprime
  have himage :=
    EtaleFundamentalGroups.Kummer.finiteQuotient_normalizationInertiaImage_coprime
      W A xi w e phi.toMonoidHom hcomp q p hqCoprimeIC
  exact ⟨q, hqPrime, hqOver, himage⟩

end ComponentsThroughPointAreHorizontal

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

namespace ComponentsThroughPointAreHorizontal

/-- Canonical integer-base form of finite-quotient component inertia
coprimality.  The unique structure morphism to `Spec (ULift Z)` and the
characteristic-zero generic residue field are constructed internally. -/
theorem exists_finiteQuotient_componentNormalizationInertiaImage_coprime_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal
      (specULiftZIsTerminal.from X) z)
    (hNC : D.1.IsNormalCrossingsAt (D.1.subschemeι z))
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    (hp : p.Prime)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ D.1.supportComplement)
    {G : Type v} [Finite G] [Group G] [TopologicalSpace G]
    [DiscreteTopology G]
    (phi : π₁ᵉᵗ(xi) →ₜ* G) (hphi : Function.Surjective phi) :
    letI : Nonempty D.1.supportComplement :=
      ⟨xi (genericPoint (Spec (.of Omega)))⟩
    letI : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    letI : IsNormalIntegral D.1.supportComplement := inferInstance
    letI : IsLocallyNoetherian D.1.supportComplement := inferInstance
    ∃ (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
      (w : (FiniteEtale.fiber xi).obj W) (e : (Aut W)ᵐᵒᵖ ≃* G),
      letI : IsGalois W := hW
      e.toMonoidHom.comp
          (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w) = phi.toMonoidHom ∧
        ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
          (hfu : f u = D.1.subschemeι z), Etale f ∧
          let K := (D.1.supportComplement : Scheme).functionField
          letI : IsIntegral W.left :=
            EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
          let L := W.left.functionField
          letI : Algebra K L :=
            EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
          letI : FiniteDimensional K L :=
            EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
          letI : _root_.IsGalois K L :=
            EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
          let A := X.presheaf.stalk (f u)
          letI : IsIntegrallyClosed A :=
            IsNormalIntegral.stalk_isIntegrallyClosed (f u)
          letI : Algebra A K :=
            D.1.supportComplementFunctionFieldAlgebra (f u)
          letI : IsFractionRing A K :=
            D.1.supportComplementFunctionField_isFractionRing (f u)
          letI : Algebra A L :=
            ((algebraMap K L).comp (algebraMap A K)).toAlgebra
          letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
          let B := integralClosure A L
          letI : IsFractionRing B L :=
            IsIntegralClosure.isFractionRing_of_finite_extension A K L B
          letI : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
            EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
              W hW A B
          let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
            hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
          ∃ q : Ideal B, q.IsPrime ∧ q.LiesOver branchPrime ∧
            Nat.Coprime
              (Nat.card
                ((Subgroup.comap
                  (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
                    xi W hW w)
                  (q.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ)).map
                    phi.toMonoidHom)) p := by
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  exact hD.exists_finiteQuotient_componentNormalizationInertiaImage_coprime
    D (specULiftZIsTerminal.from X) Z hZ z hz hNC p hp xi phi hphi

end ComponentsThroughPointAreHorizontal

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
