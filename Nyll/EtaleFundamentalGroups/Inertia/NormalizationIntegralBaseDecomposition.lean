/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Native decomposition groups under integral base enlargement

The integral-base equivalence retains the common ambient coefficient and
intertwines the two native normalization actions. Hence an automorphism of
the intermediate field extension stabilizes the contracted prime exactly
when its original scalar restriction stabilizes the original prime.

The resulting decomposition element has the specified automorphism itself
as its underlying field automorphism.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe uA uB u

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type uA) (B : Type uB) (Ω : Type u)
  [CommRing A] [CommRing B] [Field Ω]
  [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra A Ω] [Algebra B Ω] [IsScalarTower A B Ω]

/-- The literal integral-base equivalence with its native normalization
carriers, so both actions use the original normalization action. -/
@[reducible]
def normalizationIntegralBaseNativeRingEquiv :
    normalizationCommAlgCat B Ω ≃+* normalizationCommAlgCat A Ω :=
  normalizationIntegralBaseRingEquiv A B Ω

variable (F L : Type u) [Field F] [Field L]
  [Algebra A F] [IsFractionRing A F]
  [Algebra B L] [IsFractionRing B L]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower B L Ω]
  [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]

/-- The actual integral-base equivalence intertwines the native actions
through the original restriction of the same field automorphism. -/
theorem normalizationIntegralBaseNativeRingEquiv_smul
    (σ : Gal(Ω/L)) (b : normalizationCommAlgCat B Ω) :
    normalizationIntegralBaseNativeRingEquiv A B Ω (σ • b) =
      (σ.restrictScalars F) • normalizationIntegralBaseNativeRingEquiv A B Ω b := by
  apply Subtype.ext
  calc
    normalizationCommAlgInclusion A Ω
        (normalizationIntegralBaseNativeRingEquiv A B Ω (σ • b)) =
      normalizationCommAlgInclusion B Ω (σ • b) :=
        normalizationIntegralBaseRingEquiv_toAmbient A B Ω _
    _ = σ (normalizationCommAlgInclusion B Ω b) := by
      have h := congrArg (fun f : normalizationCommAlgCat B Ω →+* Ω => f b)
        (normalizationCommAlg_action_comp_inclusion B L Ω σ)
      exact h.symm
    _ = (σ.restrictScalars F) (normalizationCommAlgInclusion A Ω
        (normalizationIntegralBaseNativeRingEquiv A B Ω b)) :=
      congrArg σ (normalizationIntegralBaseRingEquiv_toAmbient A B Ω b).symm
    _ = normalizationCommAlgInclusion A Ω
        ((σ.restrictScalars F) • normalizationIntegralBaseNativeRingEquiv A B Ω b) :=
      congrArg (fun f : normalizationCommAlgCat A Ω →+* Ω =>
        f (normalizationIntegralBaseNativeRingEquiv A B Ω b))
        (normalizationCommAlg_action_comp_inclusion A F Ω (σ.restrictScalars F))

/-- The prime contraction commutes with the two native Galois actions. -/
theorem normalizationIntegralBaseNativeRingEquiv_comap_smul
    (Q : Ideal (normalizationCommAlgCat A Ω)) (σ : Gal(Ω/L)) :
    ((σ.restrictScalars F) • Q).comap
        (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom =
      σ • Q.comap (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom := by
  apply Ideal.ext
  intro b
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  have h := normalizationIntegralBaseNativeRingEquiv_smul A B Ω F L σ⁻¹ b
  change normalizationIntegralBaseNativeRingEquiv A B Ω (σ⁻¹ • b) =
    (σ.restrictScalars F)⁻¹ • normalizationIntegralBaseNativeRingEquiv A B Ω b at h
  exact (Iff.of_eq (congrArg (fun a : normalizationCommAlgCat A Ω => a ∈ Q) h)).symm

/-- Stabilizing the contracted prime is equivalent to stabilizing the
original prime after the prescribed restriction of scalars. -/
theorem normalizationIntegralBase_decomposition_iff
    (Q : Ideal (normalizationCommAlgCat A Ω)) (σ : Gal(Ω/L)) :
    σ ∈ MulAction.stabilizer Gal(Ω/L)
        (Q.comap (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom) ↔
      σ.restrictScalars F ∈ MulAction.stabilizer Gal(Ω/F) Q := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have h := normalizationIntegralBaseNativeRingEquiv_comap_smul A B Ω F L Q σ
  constructor
  · intro hσ
    apply Ideal.comap_injective_of_surjective
      (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom
      (normalizationIntegralBaseNativeRingEquiv A B Ω).surjective
    exact h.trans hσ
  · intro hσ
    exact h.symm.trans (congrArg (fun I : Ideal (normalizationCommAlgCat A Ω) =>
      I.comap (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom) hσ)

/-- An automorphism whose original restriction belongs to the original
decomposition group defines an element of the contracted-prime decomposition
group, retaining the specified automorphism literally. -/
def normalizationIntegralBaseDecompositionOfRestriction
    (Q : Ideal (normalizationCommAlgCat A Ω)) (σ : Gal(Ω/L))
    (hσ : σ.restrictScalars F ∈ MulAction.stabilizer Gal(Ω/F) Q) :
    normalizationDecompositionGroup B L Ω
      (Q.comap (normalizationIntegralBaseNativeRingEquiv A B Ω).toRingHom) :=
  ⟨σ, (normalizationIntegralBase_decomposition_iff A B Ω F L Q σ).mpr hσ⟩

/-- The constructed decomposition element is the specified automorphism. -/
theorem normalizationIntegralBaseDecompositionOfRestriction_val
    (Q : Ideal (normalizationCommAlgCat A Ω)) (σ : Gal(Ω/L))
    (hσ : σ.restrictScalars F ∈ MulAction.stabilizer Gal(Ω/F) Q) :
    (normalizationIntegralBaseDecompositionOfRestriction A B Ω F L Q σ hσ).val = σ := rfl

end EtaleFundamentalGroups.Inertia
