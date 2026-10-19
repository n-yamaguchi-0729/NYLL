/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SplitTorus
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Actual split-torus points and their unit coordinates

The canonical Hopf group law identifies points on affine test schemes with tuples
of units. The comparison uses the fully faithful monoidal algebra-spectrum functor,
so multiplication is the actual group-scheme multiplication.
-/

noncomputable section

universe u

open CategoryTheory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.GroupSchemes

/-- Characters of a finite integral lattice are determined by the images of its basis. -/
def latticeCharactersEquiv (M : Type u) [CommGroup M] (r : ℕ) :
    (Multiplicative (Fin r → ℤ) →* M) ≃* (Fin r → M) where
  toEquiv := MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans
      (((Pi.basisFun ℤ (Fin r)).constr ℤ).symm.toEquiv.trans
        (Equiv.piCongrRight fun _ => Additive.toMul)))
  map_mul' _ _ := by
    funext j
    rfl

/-- The unit coordinate of a character is its value on the corresponding basis vector. -/
theorem latticeCharactersEquiv_apply (M : Type u) [CommGroup M] (r : ℕ)
    (χ : Multiplicative (Fin r → ℤ) →* M) (j : Fin r) :
    latticeCharactersEquiv M r χ j = χ (Multiplicative.ofAdd (Pi.single j 1)) := by
  change χ (Multiplicative.ofAdd ((Pi.basisFun ℤ (Fin r)) j)) = _
  rw [Pi.basisFun_apply]

private def oppositeAlgHomEquiv (R : Type u) [CommRing R] (A B : CommAlgCat.{u} R) :
    (op A ⟶ op B) ≃ (B →ₐ[R] A) where
  toFun f := f.unop.hom
  invFun f := (CommAlgCat.ofHom f).op
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Hopf comultiplication on a character algebra gives pointwise multiplication
of characters. -/
def characterAlgebraPointsEquiv (R A : Type u) (M : Type)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] :
    (op (CommAlgCat.of R A) ⟶ op (CommAlgCat.of R (AddMonoidAlgebra R M))) ≃*
      (Multiplicative M →* Aˣ) where
  toEquiv := (oppositeAlgHomEquiv R (CommAlgCat.of R A)
    (CommAlgCat.of R (AddMonoidAlgebra R M))).trans
      ((AddMonoidAlgebra.lift R A M).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv)
  map_mul' f g := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    change (f * g).unop.hom (AddMonoidAlgebra.single m.toAdd 1) =
      f.unop.hom (AddMonoidAlgebra.single m.toAdd 1) *
        g.unop.hom (AddMonoidAlgebra.single m.toAdd 1)
    simp only [Hom.mul_def, unop_comp, CommAlgCat.hom_comp,
      CommAlgCat.lift_unop_hom, CommAlgCat.mul_op_of_unop_hom, AlgHom.comp_apply]
    have hΔ : Bialgebra.comulAlgHom R (AddMonoidAlgebra R M)
        (AddMonoidAlgebra.single m.toAdd 1) =
        AddMonoidAlgebra.single m.toAdd 1 ⊗ₜ[R] AddMonoidAlgebra.single m.toAdd 1 :=
      (AddMonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) m.toAdd).comul_eq_tmul_self
    rw [hΔ, Algebra.TensorProduct.lift_tmul]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

local instance : (algSpec (CommRingCat.of R)).Monoidal :=
  (braidedAlgSpec (R := CommRingCat.of R)).toMonoidal

/-- Actual affine-test points of the split torus are naturally tuples of units. -/
def splitTorusAffinePointEquiv (r : ℕ) :
    (((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) ⟶
      (splitTorus R r).X) ≃* (Fin r → Aˣ) :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).homMulEquiv
    (X := op (CommAlgCat.of R A))
    (M := op (CommAlgCat.of R (splitTorusAlgebra R r)))).symm.trans
      ((characterAlgebraPointsEquiv R A (Fin r → ℤ)).trans (latticeCharactersEquiv Aˣ r))

/-- The point determined by an algebra map has the expected coordinate units. -/
theorem splitTorusAffinePointEquiv_specMap (r : ℕ)
    (φ : splitTorusAlgebra R r →ₐ[R] A) (j : Fin r) :
    ↑(splitTorusAffinePointEquiv R A r
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op) j) =
      φ (AddMonoidAlgebra.single (Pi.single j 1) 1) := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of R)).homMulEquiv
    (X := op (CommAlgCat.of R A))
    (M := op (CommAlgCat.of R (splitTorusAlgebra R r)))
  change (↑(latticeCharactersEquiv Aˣ r
    (characterAlgebraPointsEquiv R A (Fin r → ℤ)
      (e.symm ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op))) j) : A) = _
  rw [show e.symm ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op) =
      (CommAlgCat.ofHom φ).op from e.symm_apply_apply (CommAlgCat.ofHom φ).op]
  exact congrArg Units.val
    (latticeCharactersEquiv_apply Aˣ r
      (characterAlgebraPointsEquiv R A (Fin r → ℤ) (CommAlgCat.ofHom φ).op) j)

/-- The actual affine-test point comparison commutes with every coefficient-algebra map. -/
theorem splitTorusAffinePointEquiv_naturality (r : ℕ)
    {B : Type u} [CommRing B] [Algebra R B] (g : A →ₐ[R] B)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)) ⟶
      (splitTorus R r).X) (j : Fin r) :
    splitTorusAffinePointEquiv R B r
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op ≫ x) j =
      Units.map g.toRingHom.toMonoidHom (splitTorusAffinePointEquiv R A r x j) := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of R)).homMulEquiv
    (X := op (CommAlgCat.of R A))
    (M := op (CommAlgCat.of R (splitTorusAlgebra R r)))
  let φ : splitTorusAlgebra R r →ₐ[R] A := (e.symm x).unop.hom
  have hx : (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op = x :=
    e.apply_symm_apply x
  have hc : (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op ≫
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom φ).op =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (g.comp φ)).op :=
    ((algSpec (CommRingCat.of R)).map_comp
      (CommAlgCat.ofHom g).op (CommAlgCat.ofHom φ).op).symm
  have hm : (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op ≫ x =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (g.comp φ)).op :=
    (congrArg
      (fun y : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)) ⟶
        (splitTorus R r).X => (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op ≫ y)
      hx.symm).trans hc
  apply Units.ext
  exact (congrArg (fun y => (↑(splitTorusAffinePointEquiv R B r y j) : B)) hm).trans
    ((splitTorusAffinePointEquiv_specMap R B r (g.comp φ) j).trans
      (congrArg g ((splitTorusAffinePointEquiv_specMap R A r φ j).symm.trans
        (congrArg (fun y => (↑(splitTorusAffinePointEquiv R A r y j) : A)) hx))))

end AlgebraicGeometry.GroupSchemes
