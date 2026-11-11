/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAffineRepresentative
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.FieldTheory.SeparableDegree

/-!
# Separable residue extensions at all actual henselization primes

Each actual affine étale representative has finite étale base change to
a field. A map from that algebra to another field factors through its
prime quotient, whose elements are separable by the existing étale
field theorem. This proves separability of the image of every stalk
element. Passing to fractions gives separability of every actual prime
residue extension, using its literal contraction and residue-field map.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem etale_fieldImage_isSeparable
    {K E L : Type u} [Field K] [CommRing E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra.Etale K E]
    (g : E →ₐ[K] L) (a : E) : IsSeparable K (g a) := by
  have : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g.toRingHom
  have : Algebra.IsSeparable K (E ⧸ RingHom.ker g) := inferInstance
  have hsep : IsSeparable K (Ideal.Quotient.mk (RingHom.ker g) a) :=
    Algebra.IsSeparable.isSeparable K (Ideal.Quotient.mk (RingHom.ker g) a)
  have himage : IsSeparable K
      ((Ideal.kerLiftAlg g) (Ideal.Quotient.mk (RingHom.ker g) a)) :=
    IsSeparable.map (Ideal.kerLiftAlg g) (Ideal.kerLiftAlg_injective g) hsep
  rw [Ideal.kerLiftAlg_mk] at himage
  exact himage

/-- Any field-valued image of the actual stalk is elementwise separable
over an intermediate coefficient field. -/
theorem geometricStalk_fieldImage_isSeparable
    {R Ω K L : Type u} [CommRing R] [Field Ω] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (g : H →ₐ[R] L) (a : H), IsSeparable K (g a) := by
  intro H actualStructureAlgebra g a
  let s := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨V, v, hVaffine, b, hb⟩ := geometricStalk_exists_affine_representative s a
  have : IsAffine V.left := hVaffine
  let E := Γ(V.left, ⊤)
  let β : R →+* E := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  let : Algebra R E := β.toAlgebra
  have : Algebra.Etale R E := geometricNeighborhood_structureMap_etale V
  let γ : E →ₐ[R] H :=
    { __ := (geometricStalkGerm s V v).hom
      commutes' r := RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r }
  let δ : (K ⊗[R] E) →ₐ[K] L := AlgHom.liftEquiv R K E L (g.comp γ)
  have hsep := etale_fieldImage_isSeparable δ (1 ⊗ₜ[R] b)
  have hδ : δ (1 ⊗ₜ[R] b) = g a := by
    rw [AlgHom.liftEquiv_tmul, one_smul]
    exact congrArg g hb
  exact hδ ▸ hsep

/-- The actual residue map at any prime of the geometric stalk is a
separable algebraic field extension of the residue field of its literal
contraction to the original ring. -/
theorem geometricStalk_primeResidue_isSeparable
    {R Ω : Type u} [CommRing R] [Field Ω] (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (q : Ideal H) [q.IsPrime],
      let p := q.comap (geometricStalkStructureMap φ)
      let : Algebra p.ResidueField q.ResidueField :=
        (Ideal.ResidueField.map p q (geometricStalkStructureMap φ) rfl).toAlgebra
      Algebra.IsSeparable p.ResidueField q.ResidueField := by
  intro H actualStructureAlgebra q hq p actualResidueAlgebra
  have : IsScalarTower R p.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R H q.ResidueField]
      exact
        (Ideal.ResidueField.map_algebraMap p q (geometricStalkStructureMap φ) rfl r).symm
  let g : H →ₐ[R] q.ResidueField := IsScalarTower.toAlgHom R H q.ResidueField
  have hsep (a : H) : IsSeparable p.ResidueField (algebraMap H q.ResidueField a) :=
    geometricStalk_fieldImage_isSeparable (K := p.ResidueField) φ g a
  constructor
  intro z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (nonZeroDivisors (H ⧸ q)) z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (s : H ⧸ q)
  rw [IsFractionRing.mk'_eq_div, ← ha, ← hb,
    Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk, div_eq_mul_inv]
  exact Field.isSeparable_mul (hsep a) (Field.isSeparable_inv (hsep b))

end EtaleFundamentalGroups.StrictHenselian
