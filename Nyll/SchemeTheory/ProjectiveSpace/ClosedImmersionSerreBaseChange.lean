/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionSerreVanishing
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Closed projective Serre vanishing after actual coefficient change

The original coefficient pullback has a constructed closed embedding
into projective space over the new coefficient ring. Apply the proved
closed-projective Serre theorem to that embedding. The constructed
structure-map triangle, coordinate cover equality, and twisting-line
isomorphism return its vanishing statement to the original pullback
scheme and the original first-projection pullback of the twisting line.

Only the new coefficient ring needs to be Noetherian. The coherent
module on the literal pullback is arbitrary, so the theorem applies to
the actual Rees image tensored with pulled back coefficients.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] closedImmersionBaseChangeProjection_isAffineHom

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
  {Y : Scheme.{u}} (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]

/-- One bound kills all positive cohomological degrees on the literal
coefficient pullback, using the original structural projection, the
original coordinate inverse-image cover, and the original twisting line. -/
theorem exists_closedImmersion_baseChange_twisting_bound_subsingleton_HSucc
    [IsNoetherianRing A]
    (F : (Limits.pullback (j ≫ π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    [SheafOfModules.IsQuasicoherent
      (R := (Limits.pullback (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType
      (R := (Limits.pullback (j ≫ π R n)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Subsingleton ((toOModulePresheaf (R := A)
        (Limits.pullback.snd (j ≫ π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A))))
        (F ⊗ ((Scheme.Modules.pullback
          (Limits.pullback.fst (j ≫ π R n)
            (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj
          ((Scheme.Modules.pullback j).obj (twistingSheaf R n))).tensorPow d)).HSucc
            (stdCoverPullback (A := R) (n := n)
              (Limits.pullback.fst (j ≫ π R n)
                (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ j)) k) := by
  let σ : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let P : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
  let X : Scheme.{u} := Limits.pullback (j ≫ π R n) σ
  let p : X ⟶ Y := Limits.pullback.fst (j ≫ π R n) σ
  let f : X ⟶ Spec (.of A) := Limits.pullback.snd (j ≫ π R n) σ
  let b : X ⟶ P := closedImmersionBaseChangeMap R A n j
  let L₀ : X.Modules := (Scheme.Modules.pullback b).obj (twistingSheaf A n)
  let L₁ : X.Modules :=
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback j).obj (twistingSheaf R n))
  let K : X.OrderedAffineCover := stdCoverPullback (A := R) (n := n) (p ≫ j)
  let e : L₀ ≅ L₁ := closedImmersionBaseChangeTwistingIso R A n j
  obtain ⟨c, hc⟩ := exists_closedImmersion_twisting_bound_subsingleton_HSucc A n b F
  refine ⟨c, ?_⟩
  intro d hd k
  have h₀ : Subsingleton ((toOModulePresheaf (R := A) (b ≫ π A n)
      (F ⊗ L₀.tensorPow d)).HSucc (stdCoverPullback (A := A) (n := n) b) k) := hc d hd k
  have hStruct : b ≫ π A n = f := closedImmersionBaseChangeMap_comp_π R A n j
  have hCover : stdCoverPullback (A := A) (n := n) b = K :=
    closedImmersionBaseChangeMap_cover R A n j
  have hNative : Subsingleton
      ((toOModulePresheaf (R := A) f (F ⊗ L₀.tensorPow d)).HSucc K k) := by
    rw [hStruct, hCover] at h₀
    exact h₀
  exact subsingleton_HSucc_of_iso f K (whiskerLeftIso F (tensorPowMapIso e d)) k

end AlgebraicGeometry.ProjSpace
