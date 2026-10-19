/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.FreeTwistPolynomialMatrix
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Pullback of original free-to-twist morphisms along a ring homomorphism

Transport the actual pulled-back sheaf morphism through the existing
free-source comparison and the constructed free-twist comparison.
The polynomial matrix of this native morphism is obtained by applying
the original ring homomorphism to every coefficient. This description
also proves identity and composition for the actual transported maps.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original native morphism type, with its source and target
kept over the same projective-space sheaf of rings. -/
abbrev FreeTwistHom (R : Type u) [CommRing R] (n : ℕ) (I J : Type u) (d : ℕ) : Type u :=
  (show (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules from
    SheafOfModules.free I) ⟶
    (show (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules from
      SheafOfModules.free J) ⊗
      (twistingSheaf R n).tensorPow d

variable (R A : Type u) [CommRing R] [CommRing A] (g : R →+* A)
  (n : ℕ) (I J : Type u) [Finite J] (d : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- Pull the original native morphism back along a specified ring
map and use the constructed source and target comparisons. -/
def freeTwistHomPullback (φ : FreeTwistHom R n I J d) : FreeTwistHom A n I J d :=
  let _ : Algebra R A := g.toAlgebra
  (pullbackFreeIso (map R A n) I).inv ≫
    (Scheme.Modules.pullback (map R A n)).map φ ≫ (freeTwistBaseChangeIso R A n J d).hom

private theorem freeTwistHomPullback_polynomialMatrix (m : I → J → 𝒜R d) :
    let _h : Algebra R A := g.toAlgebra
    freeTwistHomPullback R A g n I J d (polynomialMatrixHom R n I J d m) =
      polynomialMatrixHom A n I J d
        (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)) := by
  intro h
  let p : (Scheme.Modules.pullback (map R A n)).obj
      (show (Proj 𝒜R).Modules from SheafOfModules.free I) ≅
    (show (Proj 𝒜A).Modules from SheafOfModules.free I) :=
    pullbackFreeIso (map R A n) I
  let v : FreeTwistHom A n I J d := polynomialMatrixHom A n I J d
    (fun i j => (mvMapGraded R A n).gradedAddHom d (m i j))
  have hs := polynomialMatrixHom_baseChange R A n I J d m
  have he := congrArg (fun w => p.inv ≫ w) hs
  have hcancel : p.inv ≫ (p.hom ≫ v) = v := p.inv_hom_id_assoc v
  exact he.trans hcancel

/-- The actual transported morphism has exactly the original
polynomial entries with coefficients mapped by the specified ring map. -/
theorem freeTwistHomPullback_entry (φ : FreeTwistHom R n I J d) (i : I) (j : J) :
    (freeTwistPolynomialMatrixEquiv A n I J d
        (freeTwistHomPullback R A g n I J d φ) i j).val =
      MvPolynomial.map g ((freeTwistPolynomialMatrixEquiv R n I J d φ i j).val) := by
  let _ : Algebra R A := g.toAlgebra
  let m : I → J → 𝒜R d := freeTwistPolynomialMatrixEquiv R n I J d φ
  let mA : I → J → 𝒜A d :=
    fun i j => (mvMapGraded R A n).gradedAddHom d (m i j)
  have hsource := congrArg (freeTwistHomPullback R A g n I J d)
    (polynomialMatrixHom_of_hom R n I J d φ)
  have hmap : freeTwistHomPullback R A g n I J d φ =
      polynomialMatrixHom A n I J d mA :=
    hsource.symm.trans (freeTwistHomPullback_polynomialMatrix R A g n I J d m)
  have hentry := congrArg
    (fun ψ : FreeTwistHom A n I J d =>
      (freeTwistPolynomialMatrixEquiv A n I J d ψ i j).val) hmap
  exact hentry.trans (congrArg Subtype.val
    (congrFun (congrFun (polynomialMatrixHom_matrix A n I J d mA) i) j))

omit A g in
/-- Transport along the identity ring map is the identity on the
original native morphism. -/
theorem freeTwistHomPullback_id (φ : FreeTwistHom R n I J d) :
    freeTwistHomPullback R R (RingHom.id R) n I J d φ = φ := by
  apply (freeTwistPolynomialMatrixEquiv R n I J d).injective
  funext i j
  apply Subtype.ext
  exact (freeTwistHomPullback_entry R R (RingHom.id R) n I J d φ i j).trans
    (MvPolynomial.map_id _)

/-- Successive actual transports agree with transport along the
composite ring map, as morphisms of the original free twists. -/
theorem freeTwistHomPullback_comp (B : Type u) [CommRing B] (h : A →+* B)
    (φ : FreeTwistHom R n I J d) :
    freeTwistHomPullback A B h n I J d (freeTwistHomPullback R A g n I J d φ) =
      freeTwistHomPullback R B (h.comp g) n I J d φ := by
  apply (freeTwistPolynomialMatrixEquiv B n I J d).injective
  funext i j
  apply Subtype.ext
  have h₁ := freeTwistHomPullback_entry A B h n I J d
    (freeTwistHomPullback R A g n I J d φ) i j
  have h₂ := freeTwistHomPullback_entry R A g n I J d φ i j
  have h₃ := freeTwistHomPullback_entry R B (h.comp g) n I J d φ i j
  exact h₁.trans ((congrArg (MvPolynomial.map h) h₂).trans
    ((MvPolynomial.map_map g h _).trans h₃.symm))

end AlgebraicGeometry.ProjSpace
