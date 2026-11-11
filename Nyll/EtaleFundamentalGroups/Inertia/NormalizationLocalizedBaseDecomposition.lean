/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
public import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaBaseLocalization
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Original decomposition groups after integral base enlargement and localization

The prime of the localized normalization is the literal extension of the
original prime after integral base enlargement. Its maximality and exact
contraction follow from the actual localization of integral closures.

The coefficient map is the identity inside the common ambient field. It
intertwines the original Galois actions, so the native decomposition group
at the constructed local prime maps to the original decomposition group
by restriction of scalars. No decomposition containment is an input.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe uA uB uR uK u

attribute [local instance] normalizationCommAlgGaloisAction

/-- Extending the given normalization prime to the actual prime localization
produces a maximal ideal with exactly the original contraction. -/
theorem normalizationBaseLocalization_prime_data
    (A : Type uA) (R : Type uR) (K : Type uK) (Ω : Type u)
    [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [Field Ω]
    [Algebra A R] [Algebra A K] [Algebra R K]
    [IsFractionRing A K] [IsFractionRing R K]
    [Algebra K Ω] [Algebra A Ω] [Algebra R Ω]
    [IsScalarTower A K Ω] [IsScalarTower R K Ω] [IsScalarTower A R Ω]
    [IsGalois K Ω]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (integralClosure A Ω)) [Q.IsPrime] [Q.LiesOver P] :
    let q := Q.map (normalizationBaseLocalizationRingMap A R Ω)
    q.IsMaximal ∧ q.comap (normalizationBaseLocalizationRingMap A R Ω) = Q := by
  intro q
  refine ⟨(originalNormalizationInertia_eq_of_primeLocalization A R K Ω P Q).1, ?_⟩
  let B := integralClosure A Ω
  let C := integralClosure R Ω
  let f : B →+* C := normalizationBaseLocalizationRingMap A R Ω
  let : Algebra B C := f.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R C :=
    IsScalarTower.of_algebraMap_eq fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply A R Ω a)
  let M := Algebra.algebraMapSubmonoid B P.primeCompl
  have : IsLocalization (Algebra.algebraMapSubmonoid Ω P.primeCompl) Ω :=
    IsLocalization.of_le_isUnit fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      change IsUnit (algebraMap A Ω a)
      rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply A K Ω,
        map_ne_zero_iff _ (algebraMap K Ω).injective,
        map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact fun h => ha (h ▸ P.zero_mem)
  have : IsLocalization M C :=
    IsLocalization.integralClosure (R := A) (S := Ω) (Rf := R) (Sf := Ω) P.primeCompl
  have hdisj : Disjoint (M : Set B) (Q : Set B) :=
    Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr
        (show Q.under A ≤ P by rw [Q.over_def P]))
  exact IsLocalization.under_map_of_isPrime_disjoint M C inferInstance hdisj

section Coefficients

variable (A : Type uA) (B : Type uB) (R : Type uR) (Ω : Type u)
  [CommRing A] [CommRing B] [CommRing R] [Field Ω]
  [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra A Ω] [Algebra B Ω] [IsScalarTower A B Ω]
  [Algebra B R] [Algebra R Ω] [IsScalarTower B R Ω]

/-- The literal map from the original normalization to the normalization
over the enlarged local base, through the canonical integral-base equivalence. -/
def normalizationIntegralLocalizedBaseRingMap :
    normalizationCommAlgCat A Ω →+* normalizationCommAlgCat R Ω :=
  (normalizationBaseLocalizationRingMap B R Ω).comp
    (normalizationIntegralBaseRingEquiv A B Ω).symm.toRingHom

/-- The coefficient comparison retains its exact value in the ambient field. -/
theorem normalizationIntegralLocalizedBaseRingMap_toAmbient
    (a : normalizationCommAlgCat A Ω) :
    normalizationCommAlgInclusion R Ω
        (normalizationIntegralLocalizedBaseRingMap A B R Ω a) =
      normalizationCommAlgInclusion A Ω a := by
  let e : normalizationCommAlgCat B Ω ≃+* normalizationCommAlgCat A Ω :=
    normalizationIntegralBaseRingEquiv A B Ω
  have h := normalizationIntegralBaseRingEquiv_toAmbient A B Ω (e.symm a)
  calc
    normalizationCommAlgInclusion R Ω
        (normalizationIntegralLocalizedBaseRingMap A B R Ω a) =
      normalizationCommAlgInclusion B Ω (e.symm a) := rfl
    _ = normalizationCommAlgInclusion A Ω (e (e.symm a)) := h.symm
    _ = normalizationCommAlgInclusion A Ω a :=
      congrArg (normalizationCommAlgInclusion A Ω) (e.apply_symm_apply a)

section Action

variable (F L : Type u) [Field F] [Field L]
  [Algebra A F] [IsFractionRing A F]
  [Algebra R L] [IsFractionRing R L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower R L Ω]
  [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]

/-- The canonical coefficient map intertwines the two original Galois actions. -/
theorem normalizationIntegralLocalizedBaseRingMap_smul
    (σ : Gal(Ω/L)) (a : normalizationCommAlgCat A Ω) :
    normalizationIntegralLocalizedBaseRingMap A B R Ω ((σ.restrictScalars F) • a) =
      σ • normalizationIntegralLocalizedBaseRingMap A B R Ω a := by
  apply (IsIntegralClosure.algebraMap_injective (integralClosure R Ω) R Ω)
  calc
    normalizationCommAlgInclusion R Ω
        (normalizationIntegralLocalizedBaseRingMap A B R Ω ((σ.restrictScalars F) • a)) =
      normalizationCommAlgInclusion A Ω ((σ.restrictScalars F) • a) :=
        normalizationIntegralLocalizedBaseRingMap_toAmbient A B R Ω _
    _ = (σ.restrictScalars F) (normalizationCommAlgInclusion A Ω a) := by
      have h := congrArg (fun f : normalizationCommAlgCat A Ω →+* Ω => f a)
        (normalizationCommAlg_action_comp_inclusion A F Ω (σ.restrictScalars F))
      exact h.symm
    _ = σ (normalizationCommAlgInclusion R Ω
        (normalizationIntegralLocalizedBaseRingMap A B R Ω a)) :=
      congrArg σ (normalizationIntegralLocalizedBaseRingMap_toAmbient A B R Ω a).symm
    _ = normalizationCommAlgInclusion R Ω
        (σ • normalizationIntegralLocalizedBaseRingMap A B R Ω a) := by
      exact congrArg (fun f : normalizationCommAlgCat R Ω →+* Ω =>
        f (normalizationIntegralLocalizedBaseRingMap A B R Ω a))
        (normalizationCommAlg_action_comp_inclusion R L Ω σ)

/-- Restriction of scalars takes the native local decomposition group into
the native decomposition group of its exact original contraction. -/
def normalizationLocalizedDecompositionToContracted
    (q : Ideal (normalizationCommAlgCat R Ω)) :
    normalizationDecompositionGroup R L Ω q →*
      normalizationDecompositionGroup A F Ω
        (q.comap (normalizationIntegralLocalizedBaseRingMap A B R Ω)) where
  toFun d := ⟨d.val.restrictScalars F, by
    apply MulAction.mem_stabilizer_iff.mpr
    ext a
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change normalizationIntegralLocalizedBaseRingMap A B R Ω
        ((d.val.restrictScalars F)⁻¹ • a) ∈ q ↔
      normalizationIntegralLocalizedBaseRingMap A B R Ω a ∈ q
    have haction := normalizationIntegralLocalizedBaseRingMap_smul A B R Ω F L d.val⁻¹ a
    change normalizationIntegralLocalizedBaseRingMap A B R Ω
        ((d.val.restrictScalars F)⁻¹ • a) =
      d.val⁻¹ • normalizationIntegralLocalizedBaseRingMap A B R Ω a at haction
    rw [haction, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, d.property]⟩
  map_one' := by
    apply Subtype.ext
    change (1 : Gal(Ω/L)).restrictScalars F = (1 : Gal(Ω/F))
    exact (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).map_one
  map_mul' d e := by
    apply Subtype.ext
    exact (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).map_mul d.val e.val

/-- The decomposition restriction uses the original field automorphism. -/
theorem normalizationLocalizedDecompositionToContracted_val
    (q : Ideal (normalizationCommAlgCat R Ω))
    (d : normalizationDecompositionGroup R L Ω q) :
    (normalizationLocalizedDecompositionToContracted A B R Ω F L q d).val =
      d.val.restrictScalars F := rfl

end Action

section LocalPrime

variable (L : Type u) [Field L] [IsLocalRing R]
  [Algebra B L] [IsFractionRing B L] [Algebra R L] [IsFractionRing R L]
  [Algebra L Ω] [IsScalarTower B L Ω] [IsScalarTower R L Ω] [IsGalois L Ω]

include L in
/-- The local prime is explicitly the extension of the contracted original
prime; it is maximal and contracts back to the same original prime. -/
theorem normalizationIntegralLocalizedBase_prime_data
    (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P) :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    q.IsMaximal ∧ q.comap (normalizationIntegralLocalizedBaseRingMap A B R Ω) = Q := by
  intro QB q
  have : QB.IsPrime := Ideal.IsPrime.comap _
  have : QB.LiesOver P := hQover
  have hlocal := normalizationBaseLocalization_prime_data B R L Ω P QB
  refine ⟨hlocal.1, ?_⟩
  let e : normalizationCommAlgCat B Ω ≃+* normalizationCommAlgCat A Ω :=
    normalizationIntegralBaseRingEquiv A B Ω
  ext a
  have hb := congrArg (fun J : Ideal (integralClosure B Ω) =>
    (e.symm a : integralClosure B Ω) ∈ J) hlocal.2
  have he := congrArg (fun b : normalizationCommAlgCat A Ω => b ∈ Q)
    (e.apply_symm_apply a)
  exact (Iff.of_eq hb).trans (Iff.of_eq he)

variable (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F L] [Algebra F Ω] [IsScalarTower F L Ω] [IsScalarTower A F Ω]
  [Algebra.IsAlgebraic F Ω]

/-- The constructed local prime supplies an actual homomorphism into the
decomposition group of the original specified prime. -/
def normalizationLocalizedDecompositionRestriction
    (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P) :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    normalizationDecompositionGroup R L Ω q →* normalizationDecompositionGroup A F Ω Q := by
  intro QB q
  have hQ := (normalizationIntegralLocalizedBase_prime_data A B R Ω L P Q hQover).2
  have hQ' : q.comap (normalizationIntegralLocalizedBaseRingMap A B R Ω) = Q := hQ
  let r := normalizationLocalizedDecompositionToContracted A B R Ω F L q
  exact
    { toFun := fun d => ⟨d.val.restrictScalars F, by
        exact hQ' ▸ (r d).property⟩
      map_one' := by
        apply Subtype.ext
        change (1 : Gal(Ω/L)).restrictScalars F = (1 : Gal(Ω/F))
        exact (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).map_one
      map_mul' := by
        intro d e
        apply Subtype.ext
        exact (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).map_mul d.val e.val }

/-- The original Galois-group inclusions commute with the constructed local
restriction, so no conjugation or change of field embedding is introduced. -/
theorem normalizationLocalizedDecompositionRestriction_inclusion
    (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P) :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    (normalizationDecompositionInclusion A F Ω Q).comp
        (normalizationLocalizedDecompositionRestriction A B R Ω L F P Q hQover) =
      (AlgEquiv.restrictScalarsHom F).comp (normalizationDecompositionInclusion R L Ω q) := by
  intro QB q
  rfl

end LocalPrime

end Coefficients

end EtaleFundamentalGroups.Inertia
