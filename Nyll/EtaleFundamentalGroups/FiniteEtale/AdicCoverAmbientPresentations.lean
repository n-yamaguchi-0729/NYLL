/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectivePresentations
public import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Nyll.SchemeTheory.Modules.Sections.AffineEpi
public import Nyll.SchemeTheory.Modules.Sections.NilpotentQuotientGeneration
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Actual compatible ambient presentations of a closed-projective cover tower

The previously constructed finite family on the closed projective family
has an actual adjoint from the same finite free module on projective space.
The closed-immersion unit is epimorphic, and affine pushforward preserves
the relevant quasicoherent epimorphisms. The adjoint is therefore an
epimorphism at every level. Naturality retains every original transition.

The target is the actual direct image of the twisted cover module. The
kernel on projective space includes the embedding ideal; it is not
identified with the kernel of the free presentation on the closed family.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

/-- An affine direct image preserves an epimorphism of quasicoherent
modules, by the original sections on inverse images of affine opens. -/
theorem pushforward_epi_of_isAffineHom
    {Y X : Scheme.{u}} (j : Y ⟶ X) [IsAffineHom j]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (α : M ⟶ N) [Epi α] :
    Epi ((pushforward j).map α) := by
  apply Hom.epi_of_surjective_affine_app
  intro U hU
  change Function.Surjective (α.app (j ⁻¹ᵁ U))
  exact Hom.app_surjective_of_epi_of_isAffineOpen α (j ⁻¹ᵁ U) (hU.preimage j)

/-- The actual adjoint of a free presentation on the closed subscheme,
using the canonical comparison of the two free modules. -/
def closedImmersionAmbientFreeMap
    {Y X : Scheme.{u}} (j : Y ⟶ X) (J : Type u)
    {N : Y.Modules} (α : (show Y.Modules from SheafOfModules.free J) ⟶ N) :
    (show X.Modules from SheafOfModules.free J) ⟶ (pushforward j).obj N :=
  (pullbackPushforwardAdjunction j).homEquiv _ _ ((pullbackFreeIso j J).hom ≫ α)

/-- The ambient map is the original quotient unit followed by the
direct image of the original free presentation. -/
theorem closedImmersionAmbientFreeMap_eq
    {Y X : Scheme.{u}} (j : Y ⟶ X) (J : Type u)
    {N : Y.Modules} (α : (show Y.Modules from SheafOfModules.free J) ⟶ N) :
    closedImmersionAmbientFreeMap j J α =
      (pullbackPushforwardAdjunction j).unit.app
          (show X.Modules from SheafOfModules.free J) ≫
        (pushforward j).map (pullbackFreeIso j J).hom ≫ (pushforward j).map α := by
  let P : X.Modules := SheafOfModules.free J
  let Q : Y.Modules := SheafOfModules.free J
  let e : (Scheme.Modules.pullback j).obj P ≅ Q := pullbackFreeIso j J
  let η : P ⟶ (pushforward j).obj ((Scheme.Modules.pullback j).obj P) :=
    (pullbackPushforwardAdjunction j).unit.app P
  exact ((pullbackPushforwardAdjunction j).homEquiv_unit
    (f := e.hom ≫ α)).trans
      (congrArg (fun a : (pushforward j).obj ((Scheme.Modules.pullback j).obj P) ⟶
          (pushforward j).obj N => η ≫ a)
        ((pushforward j).map_comp e.hom α))

/-- The actual ambient free map is epimorphic whenever the original
quasicoherent presentation is epimorphic. -/
theorem closedImmersionAmbientFreeMap_epi
    {Y X : Scheme.{u}} (j : Y ⟶ X) [IsClosedImmersion j] (J : Type u)
    {N : Y.Modules} [N.IsQuasicoherent]
    (α : (show Y.Modules from SheafOfModules.free J) ⟶ N) [Epi α] :
    Epi (closedImmersionAmbientFreeMap j J α) := by
  let P : X.Modules := SheafOfModules.free J
  let Q : Y.Modules := SheafOfModules.free J
  let e : (Scheme.Modules.pullback j).obj P ≅ Q := pullbackFreeIso j J
  let η : P ⟶ (pushforward j).obj ((Scheme.Modules.pullback j).obj P) :=
    (pullbackPushforwardAdjunction j).unit.app P
  have : Epi η := epi_pullbackUnit_of_isClosedImmersion j P
  have : IsIso ((pushforward j).map e.hom) := ((pushforward j).mapIso e).isIso_hom
  have : Epi ((pushforward j).map α) := pushforward_epi_of_isAffineHom j α
  have hcomp : Epi (η ≫ (pushforward j).map e.hom ≫ (pushforward j).map α) :=
    inferInstance
  exact Eq.mpr (congrArg Epi (closedImmersionAmbientFreeMap_eq j J α)) hcomp

/-- The adjoint preserves the actual transition equation of the
original free maps. -/
theorem closedImmersionAmbientFreeMap_comp
    {Y X : Scheme.{u}} (j : Y ⟶ X) (J : Type u)
    {M N : Y.Modules} (α : (show Y.Modules from SheafOfModules.free J) ⟶ M)
    (q : M ⟶ N) :
    closedImmersionAmbientFreeMap j J α ≫ (pushforward j).map q =
      closedImmersionAmbientFreeMap j J (α ≫ q) := by
  exact ((pullbackPushforwardAdjunction j).homEquiv_naturality_right
    ((pullbackFreeIso j J).hom ≫ α) q).symm.trans
      (congrArg ((pullbackPushforwardAdjunction j).homEquiv _ _)
        (Category.assoc _ _ _))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A single finite free module on the ambient projective space presents
all actual direct-image cover modules, with all original transitions.
The finite family and every map are constructed from the closed cover. -/
theorem exists_closedProjective_ambient_compatible_presentations
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (j ≫ π R n) I 0)) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    let f := j ≫ π R n
    let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∃ J : Type u, Finite J ∧
      ∃ β : ∀ k : ℕ, (show P.Modules from SheafOfModules.free J) ⟶
          (pushforward j).obj (moduleSheaf f I V k ⊗ L.tensorPow d),
        (∀ k : ℕ, Epi (β k)) ∧
        (∀ k : ℕ, β (k + 1) ≫
          (pushforward j).map (moduleTransition f I V k ▷ L.tensorPow d) = β k) := by
  intro P f L
  obtain ⟨c, hc⟩ :=
    exists_closedProjective_twisting_bound_compatible_presentations R I n j V
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨J, hJ, α, hαepi, hα⟩ := hc d hd
  let β : ∀ k : ℕ, (show P.Modules from SheafOfModules.free J) ⟶
      (pushforward j).obj (moduleSheaf f I V k ⊗ L.tensorPow d) :=
    fun k => closedImmersionAmbientFreeMap j J (α k)
  refine ⟨J, hJ, β, ?_, ?_⟩
  · intro k
    have : (moduleSheaf f I V k ⊗ L.tensorPow d).IsQuasicoherent :=
      IsInvertible.isQuasicoherent_tensorPow (moduleSheaf f I V k)
        (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d
    have : Epi (α k) := hαepi k
    exact closedImmersionAmbientFreeMap_epi j J (α k)
  · intro k
    exact (closedImmersionAmbientFreeMap_comp j J (α (k + 1))
      (moduleTransition f I V k ▷ L.tensorPow d)).trans
        (congrArg (closedImmersionAmbientFreeMap j J) (hα k))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
