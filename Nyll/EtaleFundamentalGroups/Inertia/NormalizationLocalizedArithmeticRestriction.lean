/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalizedBaseDecomposition
public import Nyll.EtaleFundamentalGroups.Inertia.NormalLocalArithmeticDecomposition

/-!
# Arithmetic lifts in the original normalization decomposition group

The chosen field embedding gives the same coefficient map on integral
closures as the integral-base equivalence. Consequently its literal prime
contraction supplies the lying-over hypothesis for localization.

The rational residue map at that local ring lifts every constant-field
automorphism. Restriction gives an element of the original decomposition
group together with a witness in the intermediate-field restriction range.
-/

@[expose] public section

noncomputable section

open SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

section Coefficients

variable (A L Ω : Type u) [CommRing A] [CommRing L] [Field Ω]
  [Algebra A L] [Algebra A Ω] (φ : L →ₐ[A] Ω)

/-- Integral base enlargement retains the coefficient map of the specified
field embedding on the original integral closure. -/
theorem normalizationIntegralBaseRingEquiv_comp_mapIntegralClosure :
    let B := integralClosure A L
    let : Algebra B Ω := (φ.toRingHom.comp (algebraMap B L)).toAlgebra
    let : IsScalarTower A B Ω :=
      IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
    (normalizationIntegralBaseRingEquiv A B Ω).toRingHom.comp
        (algebraMap B (integralClosure B Ω)) = φ.mapIntegralClosure.toRingHom := by
  intro B instB tower
  apply RingHom.ext
  intro b
  apply Subtype.ext
  exact normalizationIntegralBaseRingEquiv_toAmbient A B Ω
    (algebraMap B (integralClosure B Ω) b)

/-- Contracting the same prime through integral base enlargement lies over
its exact contraction along the original field embedding. -/
theorem normalizationIntegralClosureBase_liesOver
    (Q : Ideal (integralClosure A Ω)) :
    let B := integralClosure A L
    let : Algebra B Ω := (φ.toRingHom.comp (algebraMap B L)).toAlgebra
    let : IsScalarTower A B Ω :=
      IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
    (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver
      (Q.comap φ.mapIntegralClosure.toRingHom) := by
  intro B instB tower
  constructor
  change Q.comap φ.mapIntegralClosure.toRingHom =
    (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).comap
      (algebraMap B (integralClosure B Ω))
  rw [Ideal.comap_comap,
    normalizationIntegralBaseRingEquiv_comp_mapIntegralClosure A L Ω φ]

end Coefficients

section Arithmetic

variable (k A B R F L κ Ω : Type u)
  [Field k] [CommRing A] [CommRing B] [CommRing R]
  [Field F] [Field L] [Field κ] [Field Ω]
  [IsLocalRing R] [IsIntegrallyClosed R]
  [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra A Ω] [Algebra B Ω] [IsScalarTower A B Ω]
  [Algebra B R] [Algebra R Ω] [IsScalarTower B R Ω]
  [Algebra B L] [IsFractionRing B L]
  [Algebra R L] [IsFractionRing R L]
  [Algebra L Ω] [IsScalarTower B L Ω] [IsScalarTower R L Ω] [IsGalois L Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F L] [Algebra F Ω] [IsScalarTower F L Ω] [IsScalarTower A F Ω]
  [Algebra.IsAlgebraic F Ω]
  [Algebra k R] [Algebra k F] [Algebra k L] [Algebra k κ] [Algebra k Ω]
  [Algebra κ Ω]
  [IsScalarTower k R Ω] [IsScalarTower k F Ω]
  [IsScalarTower k L Ω] [IsScalarTower k κ Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ]

/-- The actual local rational residue map supplies an element of the
original decomposition group with prescribed constants and an explicit
witness in the intermediate-field scalar-restriction range. -/
theorem exists_normalizationLocalizedDecomposition_lift_constants
    (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
    (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P)
    (r : R →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal R)
    (σ : Gal(κ/k)) :
    ∃ d : normalizationDecompositionGroup A F Ω Q,
      d.val ∈ (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).range ∧
        (d.val.restrictScalars k).restrictNormal κ = σ := by
  let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
  let q : Ideal (normalizationCommAlgCat R Ω) :=
    QB.map (normalizationBaseLocalizationRingMap B R Ω)
  have : q.IsMaximal :=
    (normalizationIntegralLocalizedBase_prime_data A B R Ω L P Q hQover).1
  obtain ⟨δ, hδ⟩ := exists_normalLocalDecomposition_lift_constants k R L κ Ω q r hr σ
  let d := normalizationLocalizedDecompositionRestriction A B R Ω L F P Q hQover δ
  refine ⟨d, ⟨δ.val, rfl⟩, ?_⟩
  change (δ.val.restrictScalars k).restrictNormal κ = σ
  exact hδ

end Arithmetic

end EtaleFundamentalGroups.Inertia
