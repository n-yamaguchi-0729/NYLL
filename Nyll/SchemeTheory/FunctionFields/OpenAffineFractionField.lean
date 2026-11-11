/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Affine coefficients in the function field of an integral open subscheme

An affine chart of the ambient integral scheme has the function field of
its integral open subscheme as a fraction field. The coefficient map is
literally the ambient generic germ followed by the original open-immersion
function-field map. It also retains the scalar tower into each specified
generic extension, so normalization decomposition groups can continue to
use the original open subscheme's absolute Galois group.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The ambient affine coefficients embedded in the original open function field. -/
@[instance_reducible]
def functionFieldAlgebraOfIsOpenImmersionAffine (V : X.Opens) [Nonempty V] :
    Algebra Γ(X, V) U.functionField :=
  (j.functionFieldRingEquivOfIsOpenImmersion.toRingHom.comp
    (X.germToFunctionField V).hom).toAlgebra

/-- The original function-field equivalence respects these literal affine coefficients. -/
def functionFieldAlgEquivOfIsOpenImmersionAffine (V : X.Opens) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    X.functionField ≃ₐ[Γ(X, V)] U.functionField := by
  intro _
  exact { j.functionFieldRingEquivOfIsOpenImmersion with commutes' := fun _ => rfl }

/-- The open subscheme's original function field is a fraction field of every
nonempty affine ambient chart, for the specified coefficient map. -/
theorem functionField_isFractionRing_of_isOpenImmersionAffine
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    IsFractionRing Γ(X, V) U.functionField := by
  intro _
  have : IsFractionRing Γ(X, V) X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X V hV
  exact IsFractionRing.of_algEquiv (j.functionFieldAlgEquivOfIsOpenImmersionAffine V)

/-- The coefficient tower into a given generic extension is exactly the one
used by the actual ambient normalization chart. -/
theorem functionField_isScalarTower_of_isOpenImmersionAffine
    (V : X.Opens) [Nonempty V] (L : Type u) [Field L]
    [Algebra U.functionField L] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    let : Algebra X.functionField L :=
      ((algebraMap U.functionField L).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V L
    IsScalarTower Γ(X, V) U.functionField L := by
  intro _ _ _
  exact IsScalarTower.of_algebraMap_eq' rfl

end AlgebraicGeometry.Scheme.Hom
