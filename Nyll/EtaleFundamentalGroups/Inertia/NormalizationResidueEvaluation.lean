/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueConstantField
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationConstantFrobenius

/-!
# Original normalization residues in the prescribed constant closure

The constant-residue isomorphism gives one evaluation map on the original
integral closure. Its kernel is the original prime. The map is compatible
with both decomposition elements and Galois transport to a different prime,
so geometric residue embeddings are retained before taking any quotient of
the original fundamental group.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

variable (k A κ Ω : Type u)
  [Field k] [CommRing A] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k κ] [Algebra k Ω]
  [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower k A Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ] [Algebra.FiniteType k A] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

/-- Evaluation through the constant-residue isomorphism of the same
original normalization prime. -/
def normalizationResidueValue : normalizationCommAlgCat A Ω →+* κ :=
  (RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)).symm.toRingHom.comp
      (Ideal.Quotient.mk Q)

/-- Coefficients retain their original residue embedding. -/
theorem normalizationResidueValue_coefficient (a : A) :
    normalizationResidueValue k A κ Ω Q (algebraMap A (normalizationCommAlgCat A Ω) a) =
      normalizationResidueConstantMap k A κ Ω Q a := rfl

/-- The prescribed constants evaluate to themselves. -/
theorem normalizationResidueValue_constant (x : κ) :
    normalizationResidueValue k A κ Ω Q (arithmeticConstantNormalizationMap k A κ Ω x) = x :=
  (RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)).symm_apply_apply x

/-- The same prime is exactly the kernel of the evaluation. -/
theorem normalizationResidueValue_eq_zero_iff (b : normalizationCommAlgCat A Ω) :
    normalizationResidueValue k A κ Ω Q b = 0 ↔ b ∈ Q := by
  let e : κ ≃+* (normalizationCommAlgCat A Ω ⧸ Q) :=
    RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
      (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)
  change e.symm (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
  rw [← e.symm.map_zero, e.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

variable (F : Type u) [Field F] [Algebra k F] [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [IsScalarTower A F Ω] [IsScalarTower k F Ω]
  [IsGalois F Ω] [IsAlgClosure k κ]

/-- Decomposition acts on residues by the original restriction to constants. -/
theorem normalizationResidueValue_equivariant
    (d : normalizationDecompositionGroup A F Ω Q) (b : normalizationCommAlgCat A Ω) :
    normalizationResidueValue k A κ Ω Q (d.val • b) =
      ((d.val.restrictScalars k).restrictNormal κ)
        (normalizationResidueValue k A κ Ω Q b) := by
  let e : κ ≃+* (normalizationCommAlgCat A Ω ⧸ Q) :=
    RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
      (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)
  have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
  rw [normalizationGaloisRingHom_eq_original] at hmap
  have hres := congrArg
    (fun t : normalizationCommAlgCat A Ω →+* (normalizationCommAlgCat A Ω ⧸ Q) => t b)
      hmap
  change actualNormalizationQuotientAction A F Ω Q d (Ideal.Quotient.mk Q b) =
    Ideal.Quotient.mk Q (d.val • b) at hres
  apply e.injective
  calc
    e (normalizationResidueValue k A κ Ω Q (d.val • b)) =
        Ideal.Quotient.mk Q (d.val • b) := e.apply_symm_apply _
    _ = actualNormalizationQuotientAction A F Ω Q d (Ideal.Quotient.mk Q b) := hres.symm
    _ = actualNormalizationQuotientAction A F Ω Q d
        (e (normalizationResidueValue k A κ Ω Q b)) :=
      congrArg (actualNormalizationQuotientAction A F Ω Q d) (e.apply_symm_apply _).symm
    _ = e (((d.val.restrictScalars k).restrictNormal κ)
        (normalizationResidueValue k A κ Ω Q b)) :=
      arithmeticConstantResidueMap_equivariant k A F κ Ω Q d _

/-- Galois transport to a second prime transports its residue embedding
through the same restriction to the prescribed constant closure. -/
theorem normalizationResidueValue_smul
    (Q' : Ideal (normalizationCommAlgCat A Ω)) [Q'.IsMaximal]
    (σ : Gal(Ω/F)) (hQ : σ • Q = Q') (b : normalizationCommAlgCat A Ω) :
    normalizationResidueValue k A κ Ω Q' (σ • b) =
      ((σ.restrictScalars k).restrictNormal κ) (normalizationResidueValue k A κ Ω Q b) := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (σ.restrictScalars k).restrictNormal κ
  let x := normalizationResidueValue k A κ Ω Q b
  have hbc : b - c x ∈ Q := by
    apply (normalizationResidueValue_eq_zero_iff k A κ Ω Q _).mp
    rw [map_sub, normalizationResidueValue_constant]
    exact sub_self x
  have hc : σ • c x = c (δ x) := by
    apply Subtype.ext
    have haction := congrArg (fun t : B →+* Ω => t (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω σ)
    change σ (algebraMap κ Ω x) =
      (show integralClosure A Ω from σ • c x).val at haction
    exact haction.symm.trans ((σ.restrictScalars k).restrictNormal_commutes κ x).symm
  have hσbc : σ • b - c (δ x) ∈ Q' := by
    have h := Ideal.smul_mem_pointwise_smul σ (b - c x) Q hbc
    rw [smul_sub, hc, hQ] at h
    exact h
  have hzero := (normalizationResidueValue_eq_zero_iff k A κ Ω Q' _).mpr hσbc
  rw [map_sub, normalizationResidueValue_constant, sub_eq_zero] at hzero
  exact hzero

/-- The original affine coefficient evaluations transform under the same
Galois restriction, including when the two closed points are nonrational. -/
theorem normalizationResidueConstantMap_smul
    (Q' : Ideal (normalizationCommAlgCat A Ω)) [Q'.IsMaximal]
    (σ : Gal(Ω/F)) (hQ : σ • Q = Q') (a : A) :
    normalizationResidueConstantMap k A κ Ω Q' a =
      ((σ.restrictScalars k).restrictNormal κ) (normalizationResidueConstantMap k A κ Ω Q a) := by
  have h := normalizationResidueValue_smul k A κ Ω Q F Q' σ hQ
    (algebraMap A (normalizationCommAlgCat A Ω) a)
  have hcoeff : σ • algebraMap A (normalizationCommAlgCat A Ω) a =
      algebraMap A (normalizationCommAlgCat A Ω) a :=
    congrArg (fun t : A →+* normalizationCommAlgCat A Ω => t a)
      (normalizationCommAlg_action_comp_coefficient A F Ω σ)
  rw [hcoeff, normalizationResidueValue_coefficient, normalizationResidueValue_coefficient] at h
  exact h

end EtaleFundamentalGroups.Inertia
