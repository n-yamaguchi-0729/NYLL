/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import Mathlib.FieldTheory.Galois.Abelian

/-!
# The actual abelian function field of a Galois cover

Commutativity of the native deck group implies that the original extension
of function fields is abelian Galois. Every original embedding of that field
into the fixed separable closure then gives a finite abelian intermediate
field, with no separate field-level abelianity assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- The native contravariant deck/function-field comparison supplies the
abelian Galois property of the original field extension. -/
theorem isAbelianGalois_functionField_of_isGalois_finiteEtale
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsGalois Y] [IsMulCommutative (Aut Y)] :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    IsAbelianGalois X.functionField Y.left.functionField := by
  intro hIntegral alg
  have hGalois : _root_.IsGalois X.functionField Y.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale Y inferInstance
  let e := finiteEtaleAutOpFunctionFieldMulEquiv Y inferInstance
  have hcomm : IsMulCommutative
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) :=
    .of_comm fun σ τ => by
      obtain ⟨a, rfl⟩ := e.surjective σ
      obtain ⟨b, rfl⟩ := e.surjective τ
      rw [← e.map_mul, ← e.map_mul, mul_comm' a b]
  exact { }

/-- The literal image of an original embedding of an abelian Galois cover's
function field is an actual finite abelian extension in the separable closure. -/
def finiteEtaleAbelianFunctionFieldImage
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsGalois Y] [IsMulCommutative (Aut Y)] :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField) →
      ClassFieldTheory.FiniteAbelianLocalExtension X.functionField := by
  intro hIntegral alg i
  have hfinite : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have habelian : IsAbelianGalois X.functionField Y.left.functionField :=
    isAbelianGalois_functionField_of_isGalois_finiteEtale Y
  exact ⟨i.fieldRange, i.equivFieldRange.toLinearEquiv.finiteDimensional,
    IsAbelianGalois.of_algHom i.equivFieldRange.symm.toAlgHom⟩

end EtaleFundamentalGroups
