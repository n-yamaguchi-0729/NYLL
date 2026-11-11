/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ConstantResidueRationality
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# The finite constant field selected by the original normalization prime

The original constant-residue isomorphism embeds the residue field of the
contracted closed point into the fixed constant closure. Its literal field
range is the finite constant field of that same normalization point. The
coefficient formula retains the original prime and the original inclusion
of constants; no independently chosen residue embedding is introduced.
-/

@[expose] public section

noncomputable section

open SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field

variable (k A κ Ω : Type u)
  [Field k] [CommRing A] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k κ] [Algebra k Ω]
  [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower k A Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ] [Algebra.FiniteType k A] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

private local instance normalizationIntegral :
    Algebra.IsIntegral A (normalizationCommAlgCat A Ω) :=
  ⟨fun b => integralClosure.isIntegral (show integralClosure A Ω from b)⟩

/-- The contraction of the normalization maximal ideal is maximal. -/
local instance contractedMaximal : (Q.under A).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap A (normalizationCommAlgCat A Ω)) Algebra.IsIntegral.isIntegral Q

/-- The coefficient map into constants is determined by the original
normalization residue, through its proved constant-residue isomorphism. -/
def normalizationResidueConstantMap : A →ₐ[k] κ := by
  let e : κ ≃+* (normalizationCommAlgCat A Ω ⧸ Q) :=
    RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
      (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)
  refine
    { toRingHom := e.symm.toRingHom.comp
        ((Ideal.Quotient.mk Q).comp (algebraMap A (normalizationCommAlgCat A Ω)))
      commutes' := ?_ }
  intro a
  apply e.injective
  change e (e.symm (Ideal.Quotient.mk Q
    (algebraMap A (normalizationCommAlgCat A Ω) (algebraMap k A a)))) =
      e (algebraMap k κ a)
  rw [e.apply_symm_apply]
  exact (arithmeticConstantResidueMap_base k A κ Ω Q a).symm

/-- The original residue coefficient square holds for every coefficient. -/
theorem normalizationResidueConstantMap_coefficient (a : A) :
    arithmeticConstantResidueMap k A κ Ω Q (normalizationResidueConstantMap k A κ Ω Q a) =
      Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) :=
  (RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)).apply_symm_apply _

/-- Its kernel is exactly the prime contracted from the same original Q. -/
theorem normalizationResidueConstantMap_ker :
    RingHom.ker (normalizationResidueConstantMap k A κ Ω Q).toRingHom = Q.under A := by
  ext a
  change normalizationResidueConstantMap k A κ Ω Q a = 0 ↔
    algebraMap A (normalizationCommAlgCat A Ω) a ∈ Q
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← normalizationResidueConstantMap_coefficient k A κ Ω Q]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (arithmeticConstantResidueMap k A κ Ω Q).injective
    rw [map_zero]
    exact h

/-- The residue-field embedding is induced by that same original coefficient map. -/
def normalizationResidueFieldConstantEmbedding : A ⧸ Q.under A →ₐ[k] κ :=
  Ideal.Quotient.liftₐ (Q.under A) (normalizationResidueConstantMap k A κ Ω Q) (by
    intro a ha
    change a ∈ RingHom.ker (normalizationResidueConstantMap k A κ Ω Q).toRingHom
    rw [normalizationResidueConstantMap_ker]
    exact ha)

/-- The finite constant subfield selected by the original normalization prime. -/
def normalizationResidueConstantField : IntermediateField k κ := by
  let : Field (A ⧸ Q.under A) := Ideal.Quotient.field _
  exact (normalizationResidueFieldConstantEmbedding k A κ Ω Q).fieldRange

/-- Finiteness follows from the actual closed-point residue field. -/
theorem normalizationResidueConstantField_finiteDimensional :
    FiniteDimensional k (normalizationResidueConstantField k A κ Ω Q) := by
  have : Module.Finite k (A ⧸ Q.under A) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ Q.under A)
  let e := (normalizationResidueFieldConstantEmbedding k A κ Ω Q).equivFieldRange
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- The rational residue morphism over the selected finite constants. -/
def normalizationResidueConstantPoint : A →ₐ[k] normalizationResidueConstantField k A κ Ω Q := by
  let : Field (A ⧸ Q.under A) := Ideal.Quotient.field _
  exact (normalizationResidueFieldConstantEmbedding k A κ Ω Q).equivFieldRange.toAlgHom.comp
    (Ideal.Quotient.mkₐ k (Q.under A))

/-- The constant inclusion is the original coefficient map into κ. -/
theorem normalizationResidueConstantPoint_coe (a : A) :
    (normalizationResidueConstantPoint k A κ Ω Q a : κ) =
      normalizationResidueConstantMap k A κ Ω Q a := rfl

/-- All elements of the selected finite field occur as actual residues. -/
theorem normalizationResidueConstantPoint_surjective :
    Function.Surjective (normalizationResidueConstantPoint k A κ Ω Q) :=
  (normalizationResidueFieldConstantEmbedding k A κ Ω Q).equivFieldRange.surjective.comp
    (Ideal.Quotient.mk_surjective)

/-- The selected rational residue point lies over the original contracted prime. -/
theorem normalizationResidueConstantPoint_ker :
    RingHom.ker (normalizationResidueConstantPoint k A κ Ω Q).toRingHom = Q.under A := by
  ext a
  change normalizationResidueConstantPoint k A κ Ω Q a = 0 ↔ a ∈ Q.under A
  rw [← normalizationResidueConstantMap_ker k A κ Ω Q]
  change normalizationResidueConstantPoint k A κ Ω Q a = 0 ↔
    normalizationResidueConstantMap k A κ Ω Q a = 0
  exact Subtype.val_injective.eq_iff.symm

/-- The original normalization residue square is retained over the selected
finite constant field, not merely up to a field automorphism. -/
theorem normalizationResidueConstantPoint_coefficient (a : A) :
    arithmeticConstantResidueMap k A κ Ω Q
        (normalizationResidueConstantPoint k A κ Ω Q a : κ) =
      Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) :=
  normalizationResidueConstantMap_coefficient k A κ Ω Q a

end EtaleFundamentalGroups.Inertia
