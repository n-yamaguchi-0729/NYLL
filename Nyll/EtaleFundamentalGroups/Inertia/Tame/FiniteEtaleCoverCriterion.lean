/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.FiniteGeometricFiberCriterion
public import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
public import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.TrivialImpliesUnramified
public import Nyll.EtaleFundamentalGroups.Purity.Local.DimensionOne
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaCardinality

/-!
# Classical tameness of an original finite Galois cover

The original geometric generic fiber of a connected finite étale cover is
identified with the embeddings of its actual function field. This comparison
intertwines the original field-source action and postcomposition of embeddings.
For a Galois cover, its function field embedded by a specified fiber point is
therefore tested by the same local normalization and wild inertia groups.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CategoryTheory
open CategoryTheory.PreGaloisCategory SchemeTheory

universe u v

attribute [local instance] Ideal.Quotient.field

/-- On the original fiber of any connected finite étale cover, a generic
Galois element acts trivially precisely when it fixes every embedding of
that cover's original function field. -/
theorem finiteEtaleGenericFiber_fieldSource_fixed_iff
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsConnected W] (σ : Gal(Ω/U.functionField)) :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    (∀ w : (fiber (U.genericExtensionMorphism Ω)).obj W,
      (fieldSourceAbsoluteGaloisHom U.functionField Ω
        (U.fromSpecStalk (genericPoint U)) σ).asIso.hom.app W w = w) ↔
      ∀ φ : W.left.functionField →ₐ[U.functionField] Ω, σ.toAlgHom.comp φ = φ := by
  intro hIntegral alg
  let e := (fiberObjEquivHom (U.genericExtensionMorphism Ω) W).trans
    (finiteEtaleGenericHomEquivFunctionFieldAlgHom (Ω := Ω) W)
  have hmap : fieldSourceAbsoluteGaloisHom U.functionField Ω
      (U.fromSpecStalk (genericPoint U)) σ =
      absoluteGenericGaloisToFundamentalGroup U Ω σ :=
    (congrArg (fun f => f σ)
      (absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom U Ω)).symm
  have he (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
      e ((fieldSourceAbsoluteGaloisHom U.functionField Ω
        (U.fromSpecStalk (genericPoint U)) σ).asIso.hom.app W w) = σ.toAlgHom.comp (e w) := by
    rw [hmap]
    change finiteEtaleGenericHomFunctionFieldAlgHom W
      (fiberObjEquivHom (U.genericExtensionMorphism Ω) W
        ((absoluteGenericGaloisToFundamentalGroup U Ω σ).asIso.hom.app W w)) = _
    rw [finiteEtaleGenericFiberLift_absoluteGalois]
    exact finiteEtaleGenericHomFunctionFieldAlgHom_precomp W _ σ
  constructor
  · intro h φ
    obtain ⟨w, rfl⟩ := e.surjective φ
    exact (he w).symm.trans (congrArg e (h w))
  · intro h w
    apply e.injective
    exact (he w).trans (h (e w))

/-- The actual function field of a Galois cover, embedded in the supplied
separable closure by an original generic fiber point. Its finite and Galois
properties follow from the given finite étale Galois cover. -/
def pointedFiniteGaloisCoverField
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsGalois W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    FiniteGaloisIntermediateField U.functionField Ω := by
  let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  have : FiniteDimensional U.functionField W.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  have : _root_.IsGalois U.functionField W.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale W inferInstance
  let i := finiteEtaleFiberPointFunctionFieldAlgHom W w
  exact
    { toIntermediateField := i.fieldRange
      finiteDimensional := i.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := _root_.IsGalois.of_algEquiv i.equivFieldRange }

/-- Local wild inertia acts trivially on the original geometric fiber of
an arbitrary finite Galois cover exactly when its embedded function-field
normalization has prime-to-`p` ramification index and separable residue field.
The prime is the contraction of the same absolute normalization prime `Q`;
the field embedding is selected by the actual fiber point `w`. -/
theorem finiteGaloisCover_wild_fixed_iff
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (A : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [Algebra A Ω] [IsScalarTower A U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsGalois W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    let E := pointedFiniteGaloisCoverField Ω W w
    let B := finiteAbsoluteNormalizationAlgebra A U.functionField Ω E
    let q : Ideal B.carrier := finiteAbsoluteNormalizationPrime A U.functionField Ω Q E
    let _ : q.IsMaximal := actualFiniteNormalizationPrime_isMaximal A U.functionField Ω Q E
    let _ : q.LiesOver (IsLocalRing.maximalIdeal A) :=
      subalgebraNormalizationPrime_liesOver_maximalIdeal
        (finiteLevelNormalizationSubalgebra A U.functionField Ω E) Q
    (∀ σ : (actualNormalizationWildGroup A U.functionField Ω Q).carrier,
      ∀ a : (fiber (U.genericExtensionMorphism Ω)).obj W,
        (fieldSourceAbsoluteGaloisHom U.functionField Ω
          (U.fromSpecStalk (genericPoint U)) σ.val.val).asIso.hom.app W a = a) ↔
      p.Coprime (q.ramificationIdx A) ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B.carrier ⧸ q) := by
  intro E B q hmax hlying
  let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let i := finiteEtaleFiberPointFunctionFieldAlgHom W w
  let e : W.left.functionField ≃ₐ[U.functionField] E := i.equivFieldRange
  have hfixed (σ : Gal(Ω/U.functionField)) :
      (∀ φ : W.left.functionField →ₐ[U.functionField] Ω, σ.toAlgHom.comp φ = φ) ↔
        ∀ φ : E →ₐ[U.functionField] Ω, σ.toAlgHom.comp φ = φ := by
    constructor
    · intro h φ
      ext x
      change σ (φ x) = φ x
      have hx := DFunLike.congr_fun (h (φ.comp e.toAlgHom)) (e.symm x)
      change σ (φ (e (e.symm x))) = φ (e (e.symm x)) at hx
      simpa only [AlgEquiv.apply_symm_apply] using hx
    · intro h φ
      ext x
      change σ (φ x) = φ x
      have hx := DFunLike.congr_fun (h (φ.comp e.symm.toAlgHom)) (e x)
      change σ (φ (e.symm (e x))) = φ (e.symm (e x)) at hx
      simpa only [AlgEquiv.symm_apply_apply] using hx
  have hgeometry :
      (∀ σ : (actualNormalizationWildGroup A U.functionField Ω Q).carrier,
        ∀ a : (fiber (U.genericExtensionMorphism Ω)).obj W,
          (fieldSourceAbsoluteGaloisHom U.functionField Ω
            (U.fromSpecStalk (genericPoint U)) σ.val.val).asIso.hom.app W a = a) ↔
      ∀ σ : (actualNormalizationWildGroup A U.functionField Ω Q).carrier,
        ∀ a : (fib U.functionField Ω).obj
          (fieldSourceFiniteSubfieldCover U.functionField Ω E.toIntermediateField),
          σ.val.val • a = a := by
    apply forall_congr'
    intro σ
    exact (finiteEtaleGenericFiber_fieldSource_fixed_iff Ω W σ.val.val).trans
      ((hfixed σ.val.val).trans
        (fieldSourceSubfieldFiber_fixed_iff
          U.functionField Ω E.toIntermediateField σ.val.val).symm)
  exact hgeometry.trans (finiteGaloisSubfieldCover_wild_fixed_iff A U.functionField Ω Q E p)

/-- A tame inertia group in a finite Galois `p`-group extension is trivial.
The assertion uses the actual inertia-cardinality formula, including the
inseparable residue degree, and yields the native unramifiedness property. -/
theorem finiteIdeal_pGroup_tame_unramified
    (A : Type u) (B : Type v) (G : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p G)
    (htame : p.Coprime (Q.ramificationIdx A) ∧
      Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)) :
    Q.inertia G = ⊥ ∧ Q.ramificationIdx A = 1 ∧ Algebra.IsUnramifiedAt A Q := by
  have hd : Field.finInsepDegree (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) = 1 :=
    (isSeparable_iff_finInsepDegree_eq_one
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)).mp htame.2
  have hcard : Nat.card (Q.inertia G) = Q.ramificationIdx A := by
    simpa only [hd, mul_one] using
      HilbertRamification.Dedekind.inertia_card_eq_ramificationIdx_mul_finInsepDegree
        (IsLocalRing.maximalIdeal A) (IsDiscreteValuationRing.not_a_field A) Q G
  have hone : Nat.card (Q.inertia G) = 1 :=
    (hP.to_subgroup (Q.inertia G)).card_eq_or_dvd.resolve_right fun hdiv =>
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp htame.1 (hcard ▸ hdiv)
  exact ⟨(Q.inertia G).eq_bot_of_card_eq hone, hcard.symm.trans hone,
    TameAbhyankar.SGA1.isUnramifiedAt_of_inertia_card_eq_one (G := G)
      (IsLocalRing.maximalIdeal A) (IsDiscreteValuationRing.not_a_field A) Q hone⟩

/-- The same assertion on the literal integral closure of a finite Galois
field extension. Its intrinsic automorphism group is identified with the
original field Galois group by integral restriction. -/
theorem originalNormalization_pGroup_tame_unramified
    (A : Type u) (K L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [hTower : IsScalarTower A K L]
    [FiniteDimensional K L] [_root_.IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p Gal(L/K)) :
    let _ : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
      normalizationCommAlgCat_liesOver_maximalIdeal Q
    p.Coprime (Q.ramificationIdx A) ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A)
          ((normalizationCommAlgCat A L).carrier ⧸ Q) →
      Q.inertia ((normalizationCommAlgCat A L).carrier ≃ₐ[A]
        (normalizationCommAlgCat A L).carrier) = ⊥ ∧
      Q.ramificationIdx A = 1 ∧ Algebra.IsUnramifiedAt A Q := by
  intro hlying htame
  let B := (normalizationCommAlgCat A L).carrier
  have hDedekind : IsDedekindDomain B := nativeFieldNormalization_isDedekindDomain A K L
  have hFinite : Module.Finite A B :=
    nativeNormalization_finite A K (CommAlgCat.of A L) (Field.toIsField L)
  have hTorsionFree : Module.IsTorsionFree A B := nativeFieldNormalization_isTorsionFree A K L
  have hGalois : IsGaloisGroup (B ≃ₐ[A] B) A B := nativeFieldNormalization_isGaloisGroup A K L
  have hPB : IsPGroup p (B ≃ₐ[A] B) :=
    hP.of_equiv (galRestrict A K L (integralClosure A L))
  exact finiteIdeal_pGroup_tame_unramified A B (B ≃ₐ[A] B) Q p hPB htame

/-- A finite Galois cover whose actual deck group is a `p`-group has a
`p`-group as its original function-field Galois group. -/
theorem finiteEtaleFunctionField_isPGroup
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (W : FiniteEtale U) [IsGalois W] (p : ℕ) (hP : IsPGroup p (Aut W)) :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    IsPGroup p Gal(W.left.functionField/U.functionField) := by
  intro hIntegral alg
  exact (hP.of_equiv (MulEquiv.inv' (Aut W))).of_equiv
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance)

/-- A tame finite Galois `p`-group cover is unramified at the same boundary
normalization prime. The hypothesis is the actual wild action on the
original generic fiber, not an independent bound on finite inertia. -/
theorem finiteGaloisCover_pGroup_wild_fixed_unramified
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (A : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [Algebra A Ω] [IsScalarTower A U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsGalois W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hP : IsPGroup p (Aut W))
    (hfixed : ∀ σ : (actualNormalizationWildGroup A U.functionField Ω Q).carrier,
      ∀ a : (fiber (U.genericExtensionMorphism Ω)).obj W,
        (fieldSourceAbsoluteGaloisHom U.functionField Ω
          (U.fromSpecStalk (genericPoint U)) σ.val.val).asIso.hom.app W a = a) :
    let E := pointedFiniteGaloisCoverField Ω W w
    let B := finiteAbsoluteNormalizationAlgebra A U.functionField Ω E
    let q : Ideal B.carrier := finiteAbsoluteNormalizationPrime A U.functionField Ω Q E
    let _ : q.IsMaximal := actualFiniteNormalizationPrime_isMaximal A U.functionField Ω Q E
    let _ : q.LiesOver (IsLocalRing.maximalIdeal A) :=
      subalgebraNormalizationPrime_liesOver_maximalIdeal
        (finiteLevelNormalizationSubalgebra A U.functionField Ω E) Q
    q.inertia (B.carrier ≃ₐ[A] B.carrier) = ⊥ ∧ q.ramificationIdx A = 1 ∧
      Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B.carrier ⧸ q) ∧
        Algebra.IsUnramifiedAt A q := by
  intro E B q hmax hlying
  let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let C := finiteLevelFieldAlgebra A U.functionField Ω E
  have hTower : IsScalarTower A U.functionField C.carrier :=
    finiteLevelFieldAlgebra_tower A U.functionField Ω E
  let i := finiteEtaleFiberPointFunctionFieldAlgHom W w
  let e : W.left.functionField ≃ₐ[U.functionField] C.carrier := i.equivFieldRange
  have hPE : IsPGroup p Gal(C.carrier/U.functionField) :=
    (finiteEtaleFunctionField_isPGroup W p hP).of_equiv (AlgEquiv.autCongr e)
  have htame := (finiteGaloisCover_wild_fixed_iff A Ω W w Q p).mp hfixed
  have hlocal := originalNormalization_pGroup_tame_unramified
    A U.functionField C.carrier (hTower := hTower) q (hQ := hmax) p hPE htame
  exact ⟨hlocal.1, hlocal.2.1, htame.2, hlocal.2.2⟩

/-- A finite Galois `p`-group cover with trivial actual wild action at every
normalization prime extends étale over the DVR. The conclusion uses the
original cover's function field and its original base-field algebra.
The embedded model is transported back by its proved integral-closure
algebra equivalence, so no replacement function field occurs in the result. -/
theorem finiteGaloisCover_normalization_etale_of_wild_fixed_of_isPGroup
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (A : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [Algebra A Ω] [IsScalarTower A U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsGalois W]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hP : IsPGroup p (Aut W))
    (hfixed : ∀ (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal],
      ∀ σ : (actualNormalizationWildGroup A U.functionField Ω Q).carrier,
        ∀ a : (fiber (U.genericExtensionMorphism Ω)).obj W,
          (fieldSourceAbsoluteGaloisHom U.functionField Ω
            (U.fromSpecStalk (genericPoint U)) σ.val.val).asIso.hom.app W a = a) :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let _ : Algebra A W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap A U.functionField)).toAlgebra
    let _ : IsScalarTower A U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    Algebra.Etale A (integralClosure A W.left.functionField) := by
  intro hIntegral alg algA hTower
  let w : (fiber (U.genericExtensionMorphism Ω)).obj W := Classical.choice inferInstance
  let E := pointedFiniteGaloisCoverField Ω W w
  let C := finiteLevelFieldAlgebra A U.functionField Ω E
  have : IsScalarTower A U.functionField C.carrier :=
    finiteLevelFieldAlgebra_tower A U.functionField Ω E
  let B := finiteAbsoluteNormalizationAlgebra A U.functionField Ω E
  let i := finiteEtaleFiberPointFunctionFieldAlgHom W w
  let e : W.left.functionField ≃ₐ[U.functionField] C.carrier := i.equivFieldRange
  have : Module.Finite A B.carrier :=
    nativeNormalization_finite A U.functionField C (Field.toIsField C.carrier)
  have : Module.IsTorsionFree A B.carrier :=
    nativeFieldNormalization_isTorsionFree A U.functionField C.carrier
  have hEtale : Algebra.Etale A B.carrier := by
    apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
    intro q hq
    let S := finiteLevelNormalizationSubalgebra A U.functionField Ω E
    let D := (normalizationCommAlgCat A Ω).carrier
    let f : B.carrier →ₐ[A] D := subalgebraNormalizationMap S
    let _ : Algebra B.carrier D := f.toRingHom.toAlgebra
    have : IsScalarTower A B.carrier D :=
      IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
    have : Algebra.IsIntegral A D :=
      inferInstanceAs (Algebra.IsIntegral A (integralClosure A Ω))
    have : Algebra.IsIntegral B.carrier D := Algebra.IsIntegral.tower_top A
    obtain ⟨Q, hQ, hcontract⟩ :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := D) q (by
        change RingHom.ker f.toRingHom ≤ q
        rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp
          (subalgebraNormalizationRingMap_injective S)]
        exact bot_le)
    have : Q.IsMaximal := hQ
    have hprime : finiteAbsoluteNormalizationPrime A U.functionField Ω Q E = q := hcontract
    have hlocal := finiteGaloisCover_pGroup_wild_fixed_unramified
      A Ω W w Q p hP (hfixed Q)
    have : (finiteAbsoluteNormalizationPrime A U.functionField Ω Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A U.functionField Ω Q E
    have hunramified : Algebra.IsUnramifiedAt A
        (finiteAbsoluteNormalizationPrime A U.functionField Ω Q E) := hlocal.2.2.2
    exact hprime ▸ hunramified
  have : Algebra.Etale A (integralClosure A C.carrier) := hEtale
  exact Algebra.Etale.of_equiv ((e.restrictScalars A).mapIntegralClosure).symm

end EtaleFundamentalGroups.Inertia
