/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormPolynomial
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The actual restriction morphism between finite-algebra unit norm opens -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis ι R A) (bB : Basis κ R B) (f : A →ₐ[R] B)

/-- The universal unit of the norm open, as an actual tensor-algebra unit. -/
def universalUnit : (CoordinateRing bA ⊗[R] A)ˣ :=
  homToUnit bA (AlgHom.id R (CoordinateRing bA))

/-- Restrict the actual universal unit through the given algebra homomorphism. -/
def restrictionRingHom : CoordinateRing bB →ₐ[R] CoordinateRing bA :=
  unitToHom bB (Units.map
    (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) f).toRingHom.toMonoidHom
    (universalUnit bA))

/-- The morphism of unit norm opens induced by restriction of the finite algebra. -/
def restrictionMap : unitOpen bA ⟶ unitOpen bB :=
  Spec.map (CommRingCat.ofHom (restrictionRingHom bA bB f).toRingHom)

/-- The same restriction on an arbitrary tensor-algebra point. -/
theorem restrictionRingHom_coordinates (j : κ) :
    restrictionRingHom bA bB f
        (algebraMap (MvPolynomial κ R) (CoordinateRing bB) (MvPolynomial.X j)) =
      coordinates bB
        (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) f
          (element bA (fun i =>
            algebraMap (MvPolynomial ι R) (CoordinateRing bA) (MvPolynomial.X i)))) j := by
  rw [restrictionRingHom, unitToHom_algebraMap, MvPolynomial.aeval_X]
  change coordinates bB
      (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) f
        (universalUnit bA : CoordinateRing bA ⊗[R] A)) j = _
  rw [universalUnit, homToUnit_val]
  rfl

/-- The map of norm opens is over the original coefficient scheme. -/
@[reassoc] theorem restrictionMap_toBase :
    restrictionMap bA bB f ≫ unitOpenToBase bB = unitOpenToBase bA := by
  rw [restrictionMap, unitOpenToBase, unitOpenToBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (restrictionRingHom bA bB f).comp_algebraMap

/-- Classification of the map agrees with restriction on every test algebra. -/
theorem restrictionRingHom_homEquiv {S : Type u} [CommRing S] [Algebra R S]
    (g : CoordinateRing bA →ₐ[R] S) :
    homEquivUnits bB (g.comp (restrictionRingHom bA bB f)) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom.toMonoidHom
        (homEquivUnits bA g) := by
  have hg : homEquivUnits bA g =
      Units.map (Algebra.TensorProduct.map g (AlgHom.id R A)).toRingHom.toMonoidHom
        (universalUnit bA) := by
    have hu : homEquivUnits bA (AlgHom.id R (CoordinateRing bA)) = universalUnit bA := rfl
    simpa only [AlgHom.comp_id, hu] using
      homEquivUnits_comp bA (AlgHom.id R (CoordinateRing bA)) g
  rw [homEquivUnits_comp, hg]
  change Units.map (Algebra.TensorProduct.map g (AlgHom.id R B)).toRingHom.toMonoidHom
      (homToUnit bB (unitToHom bB _)) = _
  rw [homToUnit_unitToHom]
  apply Units.ext
  change Algebra.TensorProduct.map g (AlgHom.id R B)
      (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) f
        (universalUnit bA : CoordinateRing bA ⊗[R] A)) =
    Algebra.TensorProduct.map (AlgHom.id R S) f
      (Algebra.TensorProduct.map g (AlgHom.id R A)
        (universalUnit bA : CoordinateRing bA ⊗[R] A))
  have hm : (Algebra.TensorProduct.map g (AlgHom.id R B)).comp
      (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) f) =
    (Algebra.TensorProduct.map (AlgHom.id R S) f).comp
      (Algebra.TensorProduct.map g (AlgHom.id R A)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.comp_id, AlgHom.id_comp, AlgHom.comp_id, AlgHom.id_comp]
  exact AlgHom.congr_fun hm _

/-- Identity restriction on a fixed norm open is the identity algebra homomorphism. -/
theorem restrictionRingHom_id :
    restrictionRingHom bA bA (AlgHom.id R A) = AlgHom.id R (CoordinateRing bA) := by
  apply (homEquivUnits bA).injective
  change homToUnit bA (unitToHom bA _) = universalUnit bA
  rw [homToUnit_unitToHom]
  apply Units.ext
  change Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) (AlgHom.id R A)
    (universalUnit bA : CoordinateRing bA ⊗[R] A) = _
  rw [Algebra.TensorProduct.map_id]
  rfl

/-- Successive restrictions compose on the actual representing coordinate rings. -/
theorem restrictionRingHom_comp {E : Type u} [CommRing E] [Algebra R E]
    {η : Type} [Fintype η] [DecidableEq η] (bE : Basis η R E) (g : B →ₐ[R] E) :
    (restrictionRingHom bA bB f).comp (restrictionRingHom bB bE g) =
      restrictionRingHom bA bE (g.comp f) := by
  apply (homEquivUnits bE).injective
  rw [restrictionRingHom_homEquiv]
  change Units.map
      (Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing bA)) g).toRingHom.toMonoidHom
      (homToUnit bB (unitToHom bB _)) = homToUnit bE (unitToHom bE _)
  rw [homToUnit_unitToHom, homToUnit_unitToHom]
  apply Units.ext
  exact AlgHom.congr_fun (Algebra.TensorProduct.map_id_comp g f).symm
    (universalUnit bA : CoordinateRing bA ⊗[R] A)

/-- The actual morphisms of norm opens satisfy the composition law. -/
theorem restrictionMap_comp {E : Type u} [CommRing E] [Algebra R E]
    {η : Type} [Fintype η] [DecidableEq η] (bE : Basis η R E) (g : B →ₐ[R] E) :
    restrictionMap bA bB f ≫ restrictionMap bB bE g =
      restrictionMap bA bE (g.comp f) := by
  rw [restrictionMap, restrictionMap, restrictionMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (restrictionRingHom_comp bA bB f bE g)

/-- Changing basis preserves the actual unit, and hence gives an algebra isomorphism. -/
def basisChangeRingIso {η : Type} [Fintype η] [DecidableEq η] (bA' : Basis η R A) :
    CoordinateRing bA ≃ₐ[R] CoordinateRing bA' :=
  AlgEquiv.ofAlgHom (restrictionRingHom bA' bA (AlgHom.id R A))
    (restrictionRingHom bA bA' (AlgHom.id R A))
    (by rw [restrictionRingHom_comp, AlgHom.comp_id, restrictionRingHom_id])
    (by rw [restrictionRingHom_comp, AlgHom.comp_id, restrictionRingHom_id])

/-- The identity algebra map gives an isomorphism between any two basis models. -/
theorem isIso_restrictionMap_id {η : Type} [Fintype η] [DecidableEq η]
    (bA' : Basis η R A) : IsIso (restrictionMap bA bA' (AlgHom.id R A)) := by
  let e : CommRingCat.of (CoordinateRing bA') ≅ CommRingCat.of (CoordinateRing bA) :=
    (basisChangeRingIso bA' bA).toRingEquiv.toCommRingCatIso
  change IsIso (Spec.map e.hom)
  infer_instance

end SchemeTheory.Affine.UnitNormPolynomial
