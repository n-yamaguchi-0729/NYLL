/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum

/-!
# Field-theoretic composita for tame Abhyankar

The tame Abhyankar lemma is ultimately about the valued extension
`L K' / K'`.  Before adding valuation data to that extension, this file records
the field-theoretic facts about the compositum `L ⊔ K'` inside a common
ambient field.
-/

@[expose] public section

noncomputable section

universe u v

namespace TameAbhyankar
namespace FieldCompositum

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Tower formula for the degree of the compositum over the left factor. -/
theorem left_finrank_mul_compositum_finrank
    (L K' : IntermediateField K Ω) :
    Module.finrank K L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) =
      Module.finrank K (L ⊔ K' : IntermediateField K Ω) :=
  DiscreteValuationField.FieldCompositum.left_finrank_mul_compositum_finrank L K'

/-- The compositum is finite over the right factor when both factors are
finite over the base. -/
theorem finiteDimensional_compositum_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional K'
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) :=
  DiscreteValuationField.FieldCompositum.finiteDimensional_compositum_over_right L K'

/-- The common top field `L ⊔ K'` is finite over the right factor. -/
theorem finiteDimensional_sup_over_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
  DiscreteValuationField.FieldCompositum.finiteDimensional_sup_over_right L K'

/-- Common-top form of the degree bound for `L ⊔ K' / L`. -/
theorem sup_finrank_over_left_le_right
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K'] :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) ≤
      Module.finrank K K' :=
  DiscreteValuationField.FieldCompositum.sup_finrank_over_left_le_right L K'

/-- Relative-degree square for a compositum, measured from the intersection
`L ⊓ K'`.  This is the field-theoretic source shape behind the two branch
degree factors before any linear-disjointness or valuation input is used. -/
theorem relfinrank_intersection_square
    (L K' : IntermediateField K Ω) :
    (L ⊓ K').relfinrank K' * K'.relfinrank (L ⊔ K') =
      (L ⊓ K').relfinrank L * L.relfinrank (L ⊔ K') :=
  DiscreteValuationField.FieldCompositum.relfinrank_intersection_square L K'

/-- The same relative-degree square written with the actual base-changed
intermediate fields used by the right and left compositum records. -/
theorem relfinrank_intersection_extendScalars_square
    (L K' : IntermediateField K Ω) :
    (L ⊓ K').relfinrank K' *
        Module.finrank K'
          (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) =
      (L ⊓ K').relfinrank L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) :=
  DiscreteValuationField.FieldCompositum.relfinrank_intersection_extendScalars_square L K'

/-- The right compositum degree divides the product of the left intersection
degree and the left compositum degree. -/
theorem compositum_finrank_over_right_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank K'
        (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) ∣
      (L ⊓ K').relfinrank L *
        Module.finrank L
          (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) :=
  DiscreteValuationField.FieldCompositum.compositum_finrank_over_right_dvd_intersection_product L K'

/-- The left compositum degree divides the symmetric intersection-product
coming from the same relative-degree square. -/
theorem compositum_finrank_over_left_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank L
        (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) ∣
      (L ⊓ K').relfinrank K' *
        Module.finrank K'
          (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) :=
  DiscreteValuationField.FieldCompositum.compositum_finrank_over_left_dvd_intersection_product L K'

/-- Common-top form of the right branch degree divisibility coming from the
intersection-based relative-degree square. -/
theorem sup_finrank_over_right_dvd_intersection_product
    (L K' : IntermediateField K Ω) :
    Module.finrank K' (L ⊔ K' : IntermediateField K Ω) ∣
      (L ⊓ K').relfinrank L *
        Module.finrank L (L ⊔ K' : IntermediateField K Ω) :=
  DiscreteValuationField.FieldCompositum.sup_finrank_over_right_dvd_intersection_product L K'

/-- Common-top coprime-degree form of the degree equality for `L ⊔ K' / L`. -/
theorem sup_finrank_over_left_eq_right_of_finrank_coprime
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (hcop : Nat.Coprime (Module.finrank K L) (Module.finrank K K')) :
    Module.finrank L (L ⊔ K' : IntermediateField K Ω) =
      Module.finrank K K' :=
  DiscreteValuationField.FieldCompositum.sup_finrank_over_left_eq_right_of_linearDisjoint L K'
    (DiscreteValuationField.FieldCompositum.linearDisjoint_of_finrank_coprime L K' hcop)

/-- The compositum is separable over the right factor when both factors are
separable over the base. -/
theorem isSeparable_compositum_over_right
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable K'
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
  have : Algebra.IsSeparable K
      (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right)) := by
    change Algebra.IsSeparable K
      ((IntermediateField.extendScalars
        (show K' ≤ L ⊔ K' from le_sup_right)).restrictScalars K)
    rw [IntermediateField.extendScalars_restrictScalars]
    infer_instance
  exact Algebra.isSeparable_tower_top_of_isSeparable K K'
    (IntermediateField.extendScalars (show K' ≤ L ⊔ K' from le_sup_right))

/-- Symmetric separability statement for the compositum over the left factor. -/
theorem isSeparable_compositum_over_left
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable L
      (IntermediateField.extendScalars (show L ≤ L ⊔ K' from le_sup_left)) :=
  DiscreteValuationField.FieldCompositum.isSeparable_compositum_over_left L K'

/-- The common top field is separable over the right factor when both factors
are separable over the base. -/
theorem isSeparable_sup_over_right
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable K' (L ⊔ K' : IntermediateField K Ω) := by
  exact Algebra.isSeparable_tower_top_of_isSeparable K K'
    (L ⊔ K' : IntermediateField K Ω)

/-- The common top field is separable over the left factor when both factors
are separable over the base. -/
theorem isSeparable_sup_over_left
    (L K' : IntermediateField K Ω)
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] :
    Algebra.IsSeparable L (L ⊔ K' : IntermediateField K Ω) :=
  DiscreteValuationField.FieldCompositum.isSeparable_sup_over_left L K'

end FieldCompositum
end TameAbhyankar

end
