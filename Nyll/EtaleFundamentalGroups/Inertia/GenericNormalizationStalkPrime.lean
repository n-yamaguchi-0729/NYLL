/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkPoint
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
public import Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
public import Nyll.SchemeTheory.Normalization.GenericFiber.IntegralClosure
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# The same generic-normalization point as a native local prime

The actual generic-stalk coefficient map identifies the field-source
pullback with the unchanged ambient field spectrum. Combining this source
isomorphism with normalization over the stalk gives a literal prime in the
local integral closure. It is maximal and has precisely the original
point's decomposition group, with the original field automorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction normalizationInertiaImageAction

private theorem normalizationPrime_fixed_iff_stabilizer
    (A K Ω : Type u) [CommRing A] [Field K] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [Algebra.IsAlgebraic K Ω]
    (Q : PrimeSpectrum (integralClosure A Ω)) (σ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom (σ.restrictScalars A).mapIntegralClosure.toRingHom) Q = Q ↔
      σ ∈ MulAction.stabilizer Gal(Ω/K) Q.asIdeal := by
  let r := (σ.restrictScalars A).mapIntegralClosure.toRingHom
  have hc (b : integralClosure A Ω) : r b = σ • b := by
    apply Subtype.ext
    exact congrArg (fun h : normalizationCommAlgCat A Ω →+* Ω => h b)
      (normalizationCommAlg_action_comp_inclusion A K Ω σ)
  have hcomap : Q.asIdeal.comap r = σ⁻¹ • Q.asIdeal := by
    ext b
    change r b ∈ Q.asIdeal ↔ b ∈ σ⁻¹ • Q.asIdeal
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc]
  constructor
  · intro h
    have hi : σ⁻¹ ∈ MulAction.stabilizer Gal(Ω/K) Q.asIdeal :=
      MulAction.mem_stabilizer_iff.mpr (hcomap.symm.trans (congrArg PrimeSpectrum.asIdeal h))
    exact (Subgroup.inv_mem_iff _).mp hi
  · intro h
    apply PrimeSpectrum.ext
    exact hcomap.trans (MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer Gal(Ω/K) Q.asIdeal).inv_mem h))

section Coefficients

variable {X : Scheme.{u}} [IsIntegral X]
  (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  (p : Spec (.of K) ⟶ X) [IsDominant p] [IsPreimmersion p] (x : X)

local notation "R" => X.presheaf.stalk x

variable [Algebra (X.presheaf.stalk x) K] [IsFractionRing (X.presheaf.stalk x) K]
  [Algebra (X.presheaf.stalk x) Ω] [IsScalarTower (X.presheaf.stalk x) K Ω]
  (hsource : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
    X.fromSpecStalk x = p)

local notation "f" => ξ K Ω ≫ p
local notation "b" => X.fromSpecStalk x
local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap R Ω))
local notation "fR" => pullback.snd f b

include hsource in
omit [IsIntegral X] [IsDominant p] [IsPreimmersion p]
  [IsFractionRing (X.presheaf.stalk x) K] in
private theorem genericStalkSource_comp : a ≫ b = f := by
  rw [IsScalarTower.algebraMap_eq R K Ω, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc, hsource]

include hsource in
omit [IsIntegral X] [IsDominant p] [IsPreimmersion p]
  [IsFractionRing (X.presheaf.stalk x) K] in
theorem genericStalkSource_isPullback : IsPullback (𝟙 (Spec (.of Ω))) a f b :=
  IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans
    (genericStalkSource_comp K Ω p x hsource).symm⟩

/-- The original generic source identifies the pullback along the stalk morphism. -/
def genericStalkSourceIso : Spec (.of Ω) ≅ pullback f b :=
  (genericStalkSource_isPullback K Ω p x hsource).isoPullback

omit [IsIntegral X] [IsDominant p] [IsPreimmersion p]
  [IsFractionRing (X.presheaf.stalk x) K] in
theorem genericStalkSourceIso_inv_snd :
    (genericStalkSourceIso K Ω p x hsource).inv ≫ a = fR :=
  (genericStalkSource_isPullback K Ω p x hsource).isoPullback_inv_snd

/-- The normalization over the actual stalk is its literal integral closure
in the unchanged original ambient field. -/
def genericNormalizationStalkIso :
    (fR).normalization ≅ Spec (.of (integralClosure R Ω)) :=
  normalizationSourceIso fR a (genericStalkSourceIso K Ω p x hsource).symm
    (genericStalkSourceIso_inv_snd K Ω p x hsource) ≪≫ specNormalizationIso R Ω

omit [IsIntegral X] [IsDominant p] [IsPreimmersion p]
  [IsFractionRing (X.presheaf.stalk x) K] in
/-- The comparison retains the original map to the actual local ring. -/
@[reassoc]
theorem genericNormalizationStalkIso_base :
    (genericNormalizationStalkIso K Ω p x hsource).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω))) =
      (fR).fromNormalization := by
  let E₁ : (fR).normalization ≅ (a).normalization :=
    normalizationSourceIso fR a (genericStalkSourceIso K Ω p x hsource).symm
      (genericStalkSourceIso_inv_snd K Ω p x hsource)
  let E₂ : (a).normalization ≅ Spec (.of (integralClosure R Ω)) :=
    specNormalizationIso R Ω
  have h₂ : E₂.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω))) =
        (a).fromNormalization := specNormalizationIso_hom_base R Ω
  have h₁ : E₁.hom ≫ (a).fromNormalization = (fR).fromNormalization :=
    normalizationSourceIso_hom_fromNormalization fR a
      (genericStalkSourceIso K Ω p x hsource).symm
      (genericStalkSourceIso_inv_snd K Ω p x hsource)
  change (E₁.hom ≫ E₂.hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => E₁.hom ≫ t) h₂).trans h₁)

omit [IsIntegral X] [IsDominant p] [IsPreimmersion p] in
theorem genericSource_specMap_fixed (σ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f = f := by
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact σ.toAlgHom.comp_algebraMap

omit [IsIntegral X] [IsFractionRing (X.presheaf.stalk x) K] in
private theorem genericStalk_specMap_fixed (σ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ a = a := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (σ.restrictScalars R).toAlgHom.comp_algebraMap

omit [IsIntegral X] [IsDominant p] [IsPreimmersion p]
  [IsFractionRing (X.presheaf.stalk x) K] in
/-- The comparison retains each original field automorphism, as its literal
restriction to the local integral closure. -/
@[reassoc]
theorem genericNormalizationStalkIso_action (σ : Gal(Ω/K)) :
    normalizationEndomorphism fR
        (pullbackEndomorphism f b (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericSource_specMap_fixed K Ω p σ))
        (pullbackEndomorphism_snd f b _ (genericSource_specMap_fixed K Ω p σ)) ≫
        (genericNormalizationStalkIso K Ω p x hsource).hom =
      (genericNormalizationStalkIso K Ω p x hsource).hom ≫
        Spec.map (CommRingCat.ofHom (σ.restrictScalars R).mapIntegralClosure.toRingHom) := by
  let s := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let h := genericSource_specMap_fixed K Ω p σ
  let t := pullbackEndomorphism f b s h
  let E : Spec (.of Ω) ≅ pullback f b := genericStalkSourceIso K Ω p x hsource
  have he₀ : E.inv ≫ 𝟙 (Spec (.of Ω)) = pullback.fst f b :=
    (genericStalkSource_isPullback K Ω p x hsource).isoPullback_inv_fst
  have he : (genericStalkSourceIso K Ω p x hsource).inv = pullback.fst f b :=
    (Category.comp_id E.inv).symm.trans he₀
  have ht : t ≫ (genericStalkSourceIso K Ω p x hsource).inv =
      (genericStalkSourceIso K Ω p x hsource).inv ≫ s := by
    rw [he]
    exact pullbackEndomorphism_fst f b s h
  have hnat := normalizationSourceIso_hom_endomorphism fR a
    (genericStalkSourceIso K Ω p x hsource).symm (genericStalkSourceIso_inv_snd K Ω p x hsource)
    t (pullbackEndomorphism_snd f b s h) s (genericStalk_specMap_fixed K Ω x σ) ht
  have hdeck : normalizationEndomorphism a s (genericStalk_specMap_fixed K Ω x σ) =
      affineNormalizationDeck R Ω (σ.restrictScalars R) := rfl
  let E₁ : (fR).normalization ≅ (a).normalization :=
    normalizationSourceIso fR a (genericStalkSourceIso K Ω p x hsource).symm
      (genericStalkSourceIso_inv_snd K Ω p x hsource)
  let E₂ : (a).normalization ≅ Spec (.of (integralClosure R Ω)) :=
    specNormalizationIso R Ω
  let n : (fR).normalization ⟶ (fR).normalization :=
    normalizationEndomorphism fR t (pullbackEndomorphism_snd f b s h)
  let d : (a).normalization ⟶ (a).normalization :=
    normalizationEndomorphism a s (genericStalk_specMap_fixed K Ω x σ)
  let r : Spec (.of (integralClosure R Ω)) ⟶ Spec (.of (integralClosure R Ω)) := Spec.map
    (CommRingCat.ofHom (σ.restrictScalars R).mapIntegralClosure.toRingHom)
  have hn : n ≫ E₁.hom = E₁.hom ≫ d := hnat
  have hd : d ≫ E₂.hom = E₂.hom ≫ r :=
    (congrArg (fun q => q ≫ E₂.hom) hdeck).trans
      (affineNormalizationDeck_specNormalizationIso_hom R Ω (σ.restrictScalars R))
  change n ≫ (E₁.hom ≫ E₂.hom) = (E₁.hom ≫ E₂.hom) ≫ r
  calc
    n ≫ (E₁.hom ≫ E₂.hom) = (n ≫ E₁.hom) ≫ E₂.hom := (Category.assoc _ _ _).symm
    _ = (E₁.hom ≫ d) ≫ E₂.hom := congrArg (fun q => q ≫ E₂.hom) hn
    _ = E₁.hom ≫ (d ≫ E₂.hom) := Category.assoc _ _ _
    _ = E₁.hom ≫ (E₂.hom ≫ r) := congrArg (fun q => E₁.hom ≫ q) hd
    _ = (E₁.hom ≫ E₂.hom) ≫ r := (Category.assoc _ _ _).symm

variable [Algebra.IsAlgebraic K Ω]

omit [IsIntegral X] [IsDominant p] [IsPreimmersion p] in
include hsource in
/-- The specified global point determines a maximal prime in the actual
local integral closure with exactly its original decomposition subgroup. -/
private theorem exists_genericNormalizationStalkPrime_of_coefficient
    (z : (f).normalization) (hz : (f).fromNormalization z = x) :
    ∃ Q : PrimeSpectrum (integralClosure R Ω), Q.asIdeal.IsMaximal ∧
      ∀ σ : Gal(Ω/K),
        σ ∈ MulAction.stabilizer Gal(Ω/K) Q.asIdeal ↔
          normalizationEndomorphism f (Spec.map (CommRingCat.ofHom σ.toRingHom))
            (genericSource_specMap_fixed K Ω p σ) z = z := by
  obtain ⟨q, _hqz, hqx, hfix⟩ := exists_normalizationStalkPoint f x z hz
  let Q : PrimeSpectrum (integralClosure R Ω) :=
    (genericNormalizationStalkIso K Ω p x hsource).hom q
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω))) Q =
      IsLocalRing.closedPoint R := by
    exact (congrArg (fun h : (fR).normalization ⟶ Spec R => h q)
      (genericNormalizationStalkIso_base K Ω p x hsource)).trans hqx
  have : Q.asIdeal.IsPrime := Q.isPrime
  have : Q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    exact (congrArg PrimeSpectrum.asIdeal hb).symm
  refine ⟨Q, Ideal.IsMaximal.of_liesOver_isMaximal Q.asIdeal (IsLocalRing.maximalIdeal R), ?_⟩
  intro σ
  let s := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let h := genericSource_specMap_fixed K Ω p σ
  let t := normalizationEndomorphism fR (pullbackEndomorphism f b s h)
    (pullbackEndomorphism_snd f b s h)
  have he := congrArg (fun h : (fR).normalization ⟶
      Spec (.of (integralClosure R Ω)) => h q)
    (genericNormalizationStalkIso_action K Ω p x hsource σ)
  have hlocal : t q = q ↔
      Spec.map (CommRingCat.ofHom (σ.restrictScalars R).mapIntegralClosure.toRingHom) Q = Q := by
    apply Iff.trans
      (genericNormalizationStalkIso K Ω p x hsource).hom.isOpenEmbedding.injective.eq_iff.symm
    exact Iff.of_eq (congrArg (fun w => w = Q) he)
  exact (normalizationPrime_fixed_iff_stabilizer R K Ω Q σ).symm.trans
    (hlocal.symm.trans (hfix s h))

end Coefficients

section Canonical

variable {X : Scheme.{u}} [IsIntegral X]
  (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  (p : Spec (.of K) ⟶ X) [IsDominant p] [IsPreimmersion p] (x : X)
  [Algebra.IsAlgebraic K Ω]

/-- The same global point supplies a maximal prime over its actual local ring,
using the original generic field map and the unchanged ambient field. -/
theorem exists_genericNormalizationStalkPrime
    (z : (ξ K Ω ≫ p).normalization) (hz : (ξ K Ω ≫ p).fromNormalization z = x) :
    let : Algebra (X.presheaf.stalk x) K := genericFieldSourceStalkAlgebra p x
    let : IsFractionRing (X.presheaf.stalk x) K :=
      genericFieldSourceStalk_isFractionRing p x
    let : Algebra (X.presheaf.stalk x) Ω :=
      ((algebraMap K Ω).comp (algebraMap (X.presheaf.stalk x) K)).toAlgebra
    let : IsScalarTower (X.presheaf.stalk x) K Ω :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∃ Q : PrimeSpectrum (integralClosure (X.presheaf.stalk x) Ω),
      Q.asIdeal.IsMaximal ∧ ∀ σ : Gal(Ω/K),
        σ ∈ MulAction.stabilizer Gal(Ω/K) Q.asIdeal ↔
          normalizationEndomorphism (ξ K Ω ≫ p)
            (Spec.map (CommRingCat.ofHom σ.toRingHom))
            (genericSource_specMap_fixed K Ω p σ) z = z := by
  intro aK hK aΩ hT
  exact exists_genericNormalizationStalkPrime_of_coefficient K Ω p x
    (genericFieldSourceStalkMap_fromSpecStalk p x) z hz

end Canonical

end EtaleFundamentalGroups.Inertia
