/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueEvaluation

/-!
# Algebra maps for the original normalization residue

The canonical constant algebra on the original integral closure is the
composite through the affine coefficient ring. The existing inclusion,
constant embedding, and residue evaluation then become algebra maps with
their literal ring maps retained. The dictionaries are named values, rather
than new global instances, so consumers can install the same ones explicitly.
-/

@[expose] public section

noncomputable section

open SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (k R Ω : Type u) [Field k] [CommRing R] [Field Ω]
  [Algebra k R] [Algebra k Ω] [Algebra R Ω] [IsScalarTower k R Ω]

/-- The canonical constant algebra on the same original integral closure. -/
@[instance_reducible]
def normalizationBaseAlgebra : Algebra k (normalizationCommAlgCat R Ω) :=
  ((algebraMap R (normalizationCommAlgCat R Ω)).comp (algebraMap k R)).toAlgebra

attribute [local instance] normalizationBaseAlgebra

/-- The original ambient algebra is the canonical integral-closure inclusion. -/
@[instance_reducible]
def normalizationAmbientAlgebra : Algebra (normalizationCommAlgCat R Ω) Ω :=
  inferInstanceAs (Algebra (integralClosure R Ω) Ω)

attribute [local instance] normalizationAmbientAlgebra

omit [Algebra k Ω] [IsScalarTower k R Ω] in
/-- The coefficient tower uses exactly the canonical composite algebra. -/
theorem normalizationBaseScalarTower : IsScalarTower k R (normalizationCommAlgCat R Ω) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] normalizationBaseScalarTower

/-- The original ambient inclusion is compatible with the same constants. -/
theorem normalizationAmbientScalarTower : IsScalarTower k (normalizationCommAlgCat R Ω) Ω :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact IsScalarTower.algebraMap_apply k R Ω x)

attribute [local instance] normalizationAmbientScalarTower

/-- The literal integral-closure inclusion, as a constant algebra map. -/
def normalizationInclusionAlgHom : normalizationCommAlgCat R Ω →ₐ[k] Ω :=
  IsScalarTower.toAlgHom k (normalizationCommAlgCat R Ω) Ω

/-- The inclusion algebra map has the original subtype inclusion as its ring map. -/
theorem normalizationInclusionAlgHom_toRingHom :
    (normalizationInclusionAlgHom k R Ω).toRingHom =
      (integralClosure R Ω).val.toRingHom := rfl

variable (κ : Type u) [Field κ] [Algebra k κ] [Algebra κ Ω]
  [IsScalarTower k κ Ω] [Algebra.IsAlgebraic k κ]

/-- The original prescribed constants, restricted to the integral closure,
preserve the canonical constant algebra structure. -/
def arithmeticConstantNormalizationAlgHom : κ →ₐ[k] normalizationCommAlgCat R Ω :=
  { toRingHom := arithmeticConstantNormalizationMap k R κ Ω
    commutes' := fun x => by
      apply Subtype.ext
      exact (IsScalarTower.algebraMap_apply k κ Ω x).symm.trans
        (IsScalarTower.algebraMap_apply k R Ω x) }

/-- Passing through the integral closure keeps the prescribed ambient constants. -/
theorem normalizationInclusionAlgHom_comp_constants :
    (normalizationInclusionAlgHom k R Ω).comp
        (arithmeticConstantNormalizationAlgHom k R Ω κ) =
      IsScalarTower.toAlgHom k κ Ω := by
  ext x
  rfl

variable [Algebra.FiniteType k R] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat R Ω)) [Q.IsMaximal]

/-- The same original normalization residue, as a constant algebra map. -/
def normalizationResidueAlgHom : normalizationCommAlgCat R Ω →ₐ[k] κ :=
  { toRingHom := normalizationResidueValue k R κ Ω Q
    commutes' := fun x =>
      (normalizationResidueValue_coefficient k R κ Ω Q (algebraMap k R x)).trans
        ((normalizationResidueConstantMap k R κ Ω Q).commutes x) }

/-- The algebra enhancement does not change the original residue ring map. -/
theorem normalizationResidueAlgHom_toRingHom :
    (normalizationResidueAlgHom k R Ω κ Q).toRingHom =
      normalizationResidueValue k R κ Ω Q := rfl

/-- Evaluation leaves every prescribed constant unchanged. -/
theorem normalizationResidueAlgHom_comp_constants :
    (normalizationResidueAlgHom k R Ω κ Q).comp
        (arithmeticConstantNormalizationAlgHom k R Ω κ) = AlgHom.id k κ := by
  ext x
  exact normalizationResidueValue_constant k R κ Ω Q x

/-- Restriction to the original affine ring is the selected geometric
coefficient embedding of the same normalization prime. -/
theorem normalizationResidueAlgHom_comp_coefficient :
    (normalizationResidueAlgHom k R Ω κ Q).comp
        (IsScalarTower.toAlgHom k R (normalizationCommAlgCat R Ω)) =
      normalizationResidueConstantMap k R κ Ω Q := by
  ext x
  exact normalizationResidueValue_coefficient k R κ Ω Q x

end EtaleFundamentalGroups.Inertia
