/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ConstantResidueRationality
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Constant-field Frobenius in the original decomposition group

The prescribed constant embedding is equivariant for the original normalization
residue action. At a rational local point, or a closed point of a finite-type
algebra, this identifies the residue action of every decomposition element with
its restriction to constants. In particular, an element obtained by matching
decomposition images has the expected residue Frobenius as soon as its original
arithmetic label is Frobenius.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω))

/-- Reduction of the prescribed constants intertwines the original quotient
action and the original Galois restriction to those constants. -/
theorem arithmeticConstantResidueMap_equivariant
    (d : normalizationDecompositionGroup A F Ω Q) (x : κ) :
    actualNormalizationQuotientAction A F Ω Q d
        (arithmeticConstantResidueMap k A κ Ω Q x) =
      arithmeticConstantResidueMap k A κ Ω Q
        (((d.val.restrictScalars k).restrictNormal κ) x) := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun t : B →+* Ω => t (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
  rw [normalizationGaloisRingHom_eq_original] at hmap
  have hres := congrArg (fun t : B →+* (B ⧸ Q) => t (c x)) hmap
  change actualNormalizationQuotientAction A F Ω Q d
      (Ideal.Quotient.mk Q (c x)) = Ideal.Quotient.mk Q (d.val • c x) at hres
  exact hres.trans (congrArg (Ideal.Quotient.mk Q) hc.symm)

variable [Q.IsMaximal]

/-- The same equivariance on the canonical localization residue field. -/
theorem arithmeticConstantResidueMap_localization_equivariant
    (d : normalizationDecompositionGroup A F Ω Q) (x : κ) :
    actualNormalizationResidueFieldMap A F Ω Q d
        (maximalQuotientResidueEquiv Q (arithmeticConstantResidueMap k A κ Ω Q x)) =
      maximalQuotientResidueEquiv Q (arithmeticConstantResidueMap k A κ Ω Q
        (((d.val.restrictScalars k).restrictNormal κ) x)) := by
  let e := maximalQuotientResidueEquiv Q
  change e (actualNormalizationQuotientAction A F Ω Q d
    (e.symm (e (arithmeticConstantResidueMap k A κ Ω Q x)))) = _
  rw [e.symm_apply_apply]
  exact congrArg e (arithmeticConstantResidueMap_equivariant k A F κ Ω Q d x)

variable [Fintype k]

private theorem residue_frobenius_of_constants_surjective
    (hf : Function.Surjective (arithmeticConstantResidueMap k A κ Ω Q))
    (d : normalizationDecompositionGroup A F Ω Q)
    (hd : (d.val.restrictScalars k).restrictNormal κ =
      FiniteField.frobeniusAlgEquivOfAlgebraic k κ) :
    (∀ z : (normalizationCommAlgCat A Ω) ⧸ Q,
      actualNormalizationQuotientAction A F Ω Q d z = z ^ Nat.card k) ∧
    ∀ z : Q.ResidueField,
      actualNormalizationResidueFieldMap A F Ω Q d z = z ^ Nat.card k := by
  have hquot (z : (normalizationCommAlgCat A Ω) ⧸ Q) :
      actualNormalizationQuotientAction A F Ω Q d z = z ^ Nat.card k := by
    obtain ⟨x, rfl⟩ := hf z
    rw [arithmeticConstantResidueMap_equivariant k A F κ Ω Q d x, hd]
    rw [Nat.card_eq_fintype_card]
    exact (congrArg (arithmeticConstantResidueMap k A κ Ω Q)
      (congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k κ) x)).trans
        (map_pow (arithmeticConstantResidueMap k A κ Ω Q) x (Fintype.card k))
  refine ⟨hquot, ?_⟩
  intro z
  let e := maximalQuotientResidueEquiv Q
  change e (actualNormalizationQuotientAction A F Ω Q d (e.symm z)) = _
  exact (congrArg e (hquot (e.symm z))).trans
    ((map_pow e (e.symm z) (Nat.card k)).trans
      (congrArg (· ^ Nat.card k) (e.apply_symm_apply z)))

/-- At a rational local point, every original decomposition element with
constant-field Frobenius label induces Frobenius on both original residue
presentations. The residue comparison is constructed from the rational map. -/
theorem normalization_residue_frobenius_of_rationalPoint
    [IsLocalRing A] [IsAlgClosed κ]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    (d : normalizationDecompositionGroup A F Ω Q)
    (hd : (d.val.restrictScalars k).restrictNormal κ =
      FiniteField.frobeniusAlgEquivOfAlgebraic k κ) :
    (∀ z : (normalizationCommAlgCat A Ω) ⧸ Q,
      actualNormalizationQuotientAction A F Ω Q d z = z ^ Nat.card k) ∧
    ∀ z : Q.ResidueField,
      actualNormalizationResidueFieldMap A F Ω Q d z = z ^ Nat.card k :=
  residue_frobenius_of_constants_surjective k A F κ Ω Q
    (arithmeticConstantResidueMap_bijective k A κ Ω Q r hr).surjective d hd

/-- The same conclusion at any closed point of a finite-type algebra; no
rationality assumption or independently chosen residue identification is used. -/
theorem normalization_residue_frobenius_of_finiteType
    [Algebra.FiniteType k A] [IsAlgClosed κ]
    (d : normalizationDecompositionGroup A F Ω Q)
    (hd : (d.val.restrictScalars k).restrictNormal κ =
      FiniteField.frobeniusAlgEquivOfAlgebraic k κ) :
    (∀ z : (normalizationCommAlgCat A Ω) ⧸ Q,
      actualNormalizationQuotientAction A F Ω Q d z = z ^ Nat.card k) ∧
    ∀ z : Q.ResidueField,
      actualNormalizationResidueFieldMap A F Ω Q d z = z ^ Nat.card k :=
  residue_frobenius_of_constants_surjective k A F κ Ω Q
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q).surjective d hd

end EtaleFundamentalGroups.Inertia
