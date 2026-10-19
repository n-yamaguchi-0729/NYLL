/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCechComparison
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivFD
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistPositiveVanishing
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Vanishing for the actual nonnegative twisting sheaves

The computed equivalence of the two original Čech complexes transfers
the Laurent-monomial contraction to the actual native twisting sheaf.
Every positive cocycle is shown to be an actual boundary. No Noetherian
hypothesis is needed for this free-sheaf step of Serre vanishing.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

open ProjSpaceCech

attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
  GradedModule.H.addCommGroup GradedModule.H.module Twist.H.addCommGroup Twist.H.module
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem quotientKernel_subsingleton_of_equiv
    {R : Type u} [CommRing R]
    {A B C A' B' C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module R A] [Module R B] [Module R C]
    [Module R A'] [Module R B'] [Module R C']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hf : ∀ x : A, eB (f x) = f' (eA x))
    (hg : ∀ x : B, eC (g x) = g' (eB x))
    (h : Subsingleton ((LinearMap.ker g) ⧸
      (LinearMap.range f).comap (LinearMap.ker g).subtype)) :
    Subsingleton ((LinearMap.ker g') ⧸
      (LinearMap.range f').comap (LinearMap.ker g').subtype) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro x
  have hz : eB.symm x.val ∈ LinearMap.ker g := by
    apply LinearMap.mem_ker.mpr
    apply eC.injective
    calc
      eC (g (eB.symm x.val)) = g' (eB (eB.symm x.val)) := hg _
      _ = g' x.val := congrArg g' (eB.apply_symm_apply x.val)
      _ = 0 := LinearMap.mem_ker.mp x.property
      _ = eC 0 := (map_zero eC).symm
  let z : LinearMap.ker g := ⟨eB.symm x.val, hz⟩
  have hboundary : z.val ∈ LinearMap.range f :=
    (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range f).comap (LinearMap.ker g).subtype)).mp
      (h.elim (Submodule.Quotient.mk z) 0)
  obtain ⟨w, hw⟩ := hboundary
  change x.val ∈ LinearMap.range f'
  refine ⟨eA w, ?_⟩
  calc
    f' (eA w) = eB (f w) := (hf w).symm
    _ = eB z.val := congrArg eB hw
    _ = x.val := eB.apply_symm_apply x.val

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- All positive Čech cohomology groups of the actual native sheaf
`O(d)` vanish for every nonnegative twist over every coefficient ring. -/
theorem twistingSectionPresheaf_subsingleton_HSucc (d q : ℕ) :
    Subsingleton ((twistingSectionPresheaf R n d).HSucc
      (stdCoverPullback (𝟙 (Proj 𝒜))) q) := by
  obtain ⟨E⟩ := GradedModule.nonempty_HEquiv_FD R n d (q + 1)
  have htwist : Subsingleton (Twist.H R n d (q + 1)) :=
    Twist.subsingleton_cohomology_succ_of_nonneg R n d (Int.natCast_nonneg d) q
  have hgraded : Subsingleton (GradedModule.H (GradedModule.FD R n d) (q + 1)) :=
    ⟨fun x y => E.symm.injective (htwist.elim (E.symm x) (E.symm y))⟩
  exact quotientKernel_subsingleton_of_equiv
    (GradedModule.d (GradedModule.FD R n d) q)
    (GradedModule.d (GradedModule.FD R n d) (q + 1))
    ((twistingSectionPresheaf R n d).d (stdCoverPullback (𝟙 (Proj 𝒜))) q)
    ((twistingSectionPresheaf R n d).d (stdCoverPullback (𝟙 (Proj 𝒜))) (q + 1))
    (twistingCochainEquiv R n d q) (twistingCochainEquiv R n d (q + 1))
    (twistingCochainEquiv R n d (q + 2))
    (twistingCochainEquiv_d R n d q) (twistingCochainEquiv_d R n d (q + 1)) hgraded

end AlgebraicGeometry.ProjSpace
