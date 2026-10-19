/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Actual split tori and their character morphisms

The torus is the spectrum of the group algebra of its integral character lattice,
with the Hopf-algebra group operation. Over a domain, every group-scheme homomorphism
between these split tori comes uniquely from a homomorphism of character lattices.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R]

/-- The actual character algebra of a split torus. -/
abbrev splitTorusAlgebra (r : ℕ) : Type u := AddMonoidAlgebra R (Fin r → ℤ)

/-- The split torus with its actual Hopf-algebra group operation. -/
def splitTorus (r : ℕ) : CommGrp (Over (Spec (CommRingCat.of R))) where
  X := ((hopfSpec (CommRingCat.of R)).obj
    (op (CommHopfAlgCat.of R (splitTorusAlgebra R r)))).X
  grp := ((hopfSpec (CommRingCat.of R)).obj
    (op (CommHopfAlgCat.of R (splitTorusAlgebra R r)))).grp
  comm := by
    change IsCommMonObj
      ((Spec (CommRingCat.of (splitTorusAlgebra R r))).asOver (Spec (CommRingCat.of R)))
    infer_instance

/-- The actual carrier is the spectrum of the integral-character group algebra. -/
theorem splitTorus_carrier (r : ℕ) :
    (splitTorus R r).X.left = Spec (CommRingCat.of (splitTorusAlgebra R r)) := rfl

/-- Split tori are affine group schemes. -/
instance splitTorus_isAffine (r : ℕ) : IsAffine (splitTorus R r).X.left := by
  change IsAffine (Spec (CommRingCat.of (splitTorusAlgebra R r)))
  infer_instance

/-- Character homomorphisms induce actual group-scheme homomorphisms contravariantly. -/
def splitTorusMap {r s : ℕ} (f : (Fin r → ℤ) →+ (Fin s → ℤ)) :
    splitTorus R s ⟶ splitTorus R r :=
  InducedCategory.homMk ((hopfSpec (CommRingCat.of R)).map
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom R f)).op)

/-- The identity character map gives the identity group-scheme morphism. -/
theorem splitTorusMap_id (r : ℕ) :
    splitTorusMap R (AddMonoidHom.id (Fin r → ℤ)) = 𝟙 (splitTorus R r) := by
  apply InducedCategory.hom_ext
  change (hopfSpec (CommRingCat.of R)).map
    (CommHopfAlgCat.ofHom
      (AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.id (Fin r → ℤ)))).op = _
  rw [AddMonoidAlgebra.mapDomainBialgHom_id]
  exact (hopfSpec (CommRingCat.of R)).map_id _

/-- Composition of character maps reverses the order of actual scheme morphisms. -/
theorem splitTorusMap_comp {r s t : ℕ}
    (f : (Fin r → ℤ) →+ (Fin s → ℤ)) (g : (Fin s → ℤ) →+ (Fin t → ℤ)) :
    splitTorusMap R (g.comp f) = splitTorusMap R g ≫ splitTorusMap R f := by
  apply InducedCategory.hom_ext
  change (hopfSpec (CommRingCat.of R)).map
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom R (g.comp f))).op = _
  rw [AddMonoidAlgebra.mapDomainBialgHom_comp]
  exact (hopfSpec (CommRingCat.of R)).map_comp
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom R g)).op
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom R f)).op

/-- Bundling an actual bialgebra homomorphism as a morphism of commutative Hopf algebras. -/
private def hopfHomEquiv (A B : CommHopfAlgCat.{u} R) :
    (A →ₐc[R] B) ≃ (A ⟶ B) where
  toFun := CommHopfAlgCat.ofHom
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl

variable [IsDomain R]

/-- Every actual homomorphism of split tori uniquely comes from its integral character map. -/
def splitTorusHomEquiv (r s : ℕ) :
    ((Fin r → ℤ) →+ (Fin s → ℤ)) ≃ (splitTorus R s ⟶ splitTorus R r) :=
  (AddMonoidAlgebra.mapDomainBialgHomEquiv (R := R)).trans
    ((hopfHomEquiv R (CommHopfAlgCat.of R (splitTorusAlgebra R r))
      (CommHopfAlgCat.of R (splitTorusAlgebra R s))).trans
      (Quiver.Hom.opEquiv.trans
        ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.trans
          ((CommGrp.fullyFaithfulForget₂Grp (Over (Spec (CommRingCat.of R)))).homEquiv
            (X := splitTorus R s) (Y := splitTorus R r)).symm)))

end AlgebraicGeometry.GroupSchemes
