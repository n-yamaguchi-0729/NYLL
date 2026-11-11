/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueConstantField
public import Nyll.EtaleFundamentalGroups.Inertia.NormalLocalArithmeticDecomposition

/-!
# The arithmetic image of the same closed normalization point

The original decomposition group restricts onto precisely the automorphisms
fixing the finite constant field selected by its own residue map. Both the
containment and the lifting statement use the original normalization prime
and the original action on its integral closure. In particular the arithmetic
surjectivity needed after finite constant restriction is proved here rather
than supplied as an additional hypothesis.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra.FiniteType k A] [Algebra k F]
  [Algebra k κ] [Algebra k Ω] [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

/-- The original decomposition element fixes the constants selected by its
own residue embedding, including at a non-rational closed point. -/
theorem normalizationDecomposition_restrict_constants_mem_fixingSubgroup
    (d : normalizationDecompositionGroup A F Ω Q) :
    (d.val.restrictScalars k).restrictNormal κ ∈
      (normalizationResidueConstantField k A κ Ω Q).fixingSubgroup := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  apply (IntermediateField.mem_fixingSubgroup_iff _ δ).mpr
  intro x hx
  obtain ⟨a, ha⟩ := normalizationResidueConstantPoint_surjective k A κ Ω Q ⟨x, hx⟩
  have hax : normalizationResidueConstantMap k A κ Ω Q a = x :=
    congrArg (fun z : normalizationResidueConstantField k A κ Ω Q => (z : κ)) ha
  rw [← hax]
  apply (arithmeticConstantResidueMap k A κ Ω Q).injective
  let b : B := algebraMap A B a
  have hcoeff := normalizationResidueConstantMap_coefficient k A κ Ω Q a
  have hbc : c (normalizationResidueConstantMap k A κ Ω Q a) - b ∈ Q :=
    Ideal.Quotient.eq.mp hcoeff
  have hdb : d.val • (c (normalizationResidueConstantMap k A κ Ω Q a) - b) ∈ Q := by
    have h := Ideal.smul_mem_pointwise_smul d.val _ Q hbc
    have hQ : d.val • Q = Q := d.property
    rwa [hQ] at h
  have hb : d.val • b = b :=
    congrArg (fun z : A →+* B => z a)
      (normalizationCommAlg_action_comp_coefficient A F Ω d.val)
  rw [smul_sub, hb] at hdb
  change Ideal.Quotient.mk Q (c (δ (normalizationResidueConstantMap k A κ Ω Q a))) =
    Ideal.Quotient.mk Q (c (normalizationResidueConstantMap k A κ Ω Q a))
  rw [hc]
  exact (Ideal.Quotient.eq.mpr hdb).trans hcoeff.symm

/-- Every automorphism fixing precisely the selected finite constants lifts
to the original decomposition group at the same prime. -/
theorem exists_normalizationDecomposition_lift_selected_constants
    [IsIntegrallyClosed A] (σ : Gal(κ/k))
    (hσ : σ ∈ (normalizationResidueConstantField k A κ Ω Q).fixingSubgroup) :
    ∃ d : normalizationDecompositionGroup A F Ω Q,
      (d.val.restrictScalars k).restrictNormal κ = σ := by
  let B := normalizationCommAlgCat A Ω
  let R := B ⧸ Q
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let e : κ ≃+* R := RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)
  let τ : R ≃+* R := e.symm.trans (σ.toRingEquiv.trans e)
  let : Algebra (A ⧸ nativeAlgebraResidueBaseIdeal B Q) R :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := Q.under A) (P := Q) le_rfl
  let ρ : normalizationResidueAutomorphisms A Ω Q :=
    { τ with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change τ (Ideal.Quotient.mk Q (algebraMap A B a)) =
          Ideal.Quotient.mk Q (algebraMap A B a)
        rw [← normalizationResidueConstantPoint_coefficient k A κ Ω Q a]
        change e (σ (e.symm (e (normalizationResidueConstantPoint k A κ Ω Q a : κ)))) =
          e (normalizationResidueConstantPoint k A κ Ω Q a : κ)
        rw [e.symm_apply_apply]
        exact congrArg e ((IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
          (normalizationResidueConstantPoint k A κ Ω Q a).property) }
  obtain ⟨d, hd⟩ := normalizationResidueMorphism_surjective A F Ω Q ρ
  refine ⟨d, ?_⟩
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  have hres (b : B) : Ideal.Quotient.mk Q (d.val • b) =
      τ (Ideal.Quotient.mk Q b) := by
    have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
    rw [hd, normalizationGaloisRingHom_eq_original] at hmap
    have hb := congrArg (fun z : B →+* R => z b) hmap
    dsimp only [nativeAlgebraResidueCoefficientMap,
      nativeAlgebraResidueAutomorphismRingEquiv, nativeResidueAutomorphismRingEquiv,
      RingHom.comp_apply, ρ] at hb
    exact hb.symm
  apply AlgEquiv.ext
  intro x
  apply e.injective
  change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c (σ x))
  rw [hc, hres]
  change e (σ (e.symm (e x))) = e (σ x)
  rw [e.symm_apply_apply]

/-- The exact native arithmetic image is the fixing subgroup of the
finite field selected by the same normalization prime. -/
theorem normalizationDecomposition_constants_range
    [IsIntegrallyClosed A] :
    ((AlgEquiv.restrictNormalHom κ).comp
      ((AlgEquiv.restrictScalarsHom k).comp
        (normalizationDecompositionInclusion A F Ω Q))).range =
      (normalizationResidueConstantField k A κ Ω Q).fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨d, rfl⟩
    exact normalizationDecomposition_restrict_constants_mem_fixingSubgroup k A F κ Ω Q d
  · intro hσ
    obtain ⟨d, hd⟩ := exists_normalizationDecomposition_lift_selected_constants
      k A F κ Ω Q σ hσ
    exact ⟨d, hd⟩

end EtaleFundamentalGroups.Inertia
