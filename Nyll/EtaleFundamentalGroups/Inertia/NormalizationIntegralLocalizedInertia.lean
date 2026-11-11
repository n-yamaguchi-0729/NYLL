/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalizedBaseDecomposition

/-!
# Full inertia at the same prime after integral base change and localization

The local normalization prime is the extension of the original prime after
the canonical integral-base equivalence. Its full inertia is exactly the
restriction comap of the original inertia. In particular this calculation
retains wild inertia and the original ambient field automorphisms.
-/

noncomputable section

open SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe uA uB uR u

attribute [local instance] normalizationCommAlgGaloisAction normalizationInertiaImageAction

variable (A : Type uA) (B : Type uB) (R : Type uR)
  (F L Ω : Type u)
  [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R]
  [Field F] [Field L] [Field Ω]
  [Algebra A B] [Algebra.IsIntegral A B] [Algebra B R]
  [Algebra A F] [IsFractionRing A F]
  [Algebra B L] [IsFractionRing B L] [Algebra R L] [IsFractionRing R L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [Algebra A Ω] [Algebra B Ω] [Algebra R Ω]
  [IsScalarTower A B Ω] [IsScalarTower B R Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω]
  [IsScalarTower B L Ω] [IsScalarTower R L Ω]
  [Algebra.IsAlgebraic F Ω] [IsGalois L Ω]
  (P : Ideal B) [P.IsPrime] [IsLocalization.AtPrime R P]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsPrime]
  (hQover : (Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).LiesOver P)

include hQover in
/-- The explicitly constructed local prime is maximal, and its full native
inertia is the original inertia restricted to the enlarged function field. -/
theorem normalizationIntegralLocalized_inertia_comap :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    q.IsMaximal ∧
      (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) = q.inertia Gal(Ω/L) := by
  intro QB q
  have : QB.IsPrime := Ideal.IsPrime.comap _
  have : QB.LiesOver P := hQover
  have hlocal := originalNormalizationInertia_eq_of_primeLocalization B R L Ω P QB
  refine ⟨hlocal.1, ?_⟩
  exact (normalizationIntegralBase_inertia_comap (A := A) (B := B) F L Q).trans hlocal.2

include hQover in
/-- Under the original scalar restriction, local inertia has exactly the
original inertia image inside the actual function-field subgroup. -/
theorem normalizationIntegralLocalized_inertia_map :
    let QB := Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom
    let q := QB.map (normalizationBaseLocalizationRingMap B R Ω)
    (q.inertia Gal(Ω/L)).map (AlgEquiv.restrictScalarsHom F) =
      Q.inertia Gal(Ω/F) ⊓ (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).range := by
  intro QB q
  have h := (normalizationIntegralLocalized_inertia_comap A B R F L Ω P Q hQover).2
  rw [← h, Subgroup.map_comap_eq, inf_comm]

end EtaleFundamentalGroups.Inertia
