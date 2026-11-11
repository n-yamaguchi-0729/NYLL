/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelTensorComparison
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicTwistingGlobalReduction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyVanishing
public import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
public import Nyll.SchemeTheory.Cohomology.Sheaves.ProperGlobalSections
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
public import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleCompatibleFibers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem

/-!
# Lifting actual compatible free-to-twist morphisms on a closed projective family

Uniform Rees vanishing supplies surjectivity of the original global
reductions of a fixed sufficiently positive free twist. Properness makes
its original global sections finite over the complete Noetherian local
base. The finite-module compatible-fiber theorem lifts each original
column of the compatible presenting morphisms simultaneously.

The result is a morphism on the original closed projective family, whose
composite with every actual closed-level quotient unit is the prescribed
level morphism. No global lift, matrix compatibility, kernel-filtration
comparison, or Hom-algebraization hypothesis is an input.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (I : Ideal R) (M : X.Modules)

/-- The original base-ring action on every original quotient module
is annihilated by the actual specified ideal power. -/
theorem levelPullbackModule_globalSections_annihilated (k : ℕ) :
    I ^ (k + 1) •
      (⊤ : Submodule R (sectionModuleOverBase f (levelPullbackModule f I M k) ⊤)) = ⊥ := by
  let i : level f I k ⟶ X := Limits.pullback.fst f (baseInclusion I k)
  let g : level f I k ⟶ Spec (.of (R ⧸ levelIdeal I k)) :=
    Limits.pullback.snd f (baseInclusion I k)
  let q : R →+* R ⧸ levelIdeal I k := Ideal.Quotient.mk (levelIdeal I k)
  have hcoeff : (i.app ⊤).hom.comp (f.constToPresheaf.app (op ⊤)).hom =
      (g.constToPresheaf.app (op (i ⁻¹ᵁ ⊤))).hom.comp q :=
    (Scheme.Hom.constToPresheaf_comp_app i f ⊤).trans
      ((congrArg (fun a : level f I k ⟶ Spec (.of R) =>
          (a.constToPresheaf.app (op (i ⁻¹ᵁ ⊤))).hom)
        (Limits.pullback.condition (f := f) (g := baseInclusion I k))).trans
          (Scheme.Hom.constToPresheaf_comp_Spec_map g (CommRingCat.ofHom q) (i ⁻¹ᵁ ⊤)))
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x _hx
  let y : Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ ⊤) := x
  change (i.app ⊤).hom ((f.constToPresheaf.app (op ⊤)).hom a) • y = 0
  have ha' : a ∈ levelIdeal I k := by
    rw [levelIdeal_eq_pow]
    exact ha
  have hz : (i.app ⊤).hom ((f.constToPresheaf.app (op ⊤)).hom a) = 0 := by
    have h := DFunLike.congr_fun hcoeff a
    exact h.trans ((congrArg (g.constToPresheaf.app (op (i ⁻¹ᵁ ⊤))).hom
      (Ideal.Quotient.eq_zero_iff_mem.mpr ha')).trans (map_zero _))
  rw [hz, zero_smul]

variable [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsProper f] [M.IsQuasicoherent] [M.IsFiniteType]

private theorem exists_section_lift_of_compatible_quotients
    (Q : ℕ → X.Modules) (τ : ∀ k : ℕ, Q (k + 1) ⟶ Q k)
    (η : ∀ k : ℕ, M ⟶ Q k)
    (hη : ∀ k : ℕ, η (k + 1) ≫ τ k = η k)
    (hsurj : ∀ k : ℕ, Function.Surjective ((η k).app ⊤))
    (hpow : ∀ k : ℕ, IsLocalRing.maximalIdeal R ^ (k + 1) •
      (⊤ : Submodule R (sectionModuleOverBase f (Q k) ⊤)) = ⊥)
    (z : ∀ k : ℕ, Γ(Q k, ⊤))
    (hz : ∀ k : ℕ, (τ k).app ⊤ (z (k + 1)) = z k) :
    ∃ x : Γ(M, ⊤), ∀ k : ℕ, (η k).app ⊤ x = z k := by
  let H : X.Modules ⥤ ModuleCat.{u} R :=
    moduleSectionsFunctor ⊤ ⋙ ModuleCat.restrictScalars (f.constToPresheaf.app (op ⊤)).hom
  let P : ModuleCat.{u} R := H.obj M
  let N (k : ℕ) : ModuleCat.{u} R := H.obj (Q k)
  let t (k : ℕ) : N (k + 1) →ₗ[R] N k :=
    (H.map (τ k)).hom
  let q (k : ℕ) : P →ₗ[R] N k := (H.map (η k)).hom
  have : Module.Finite R P := moduleFinite_globalSections_of_isProper f M
  have hq (k : ℕ) : (t k).comp (q (k + 1)) = q k := by
    have h : H.map (η (k + 1)) ≫ H.map (τ k) = H.map (η k) :=
      (H.map_comp (η (k + 1)) (τ k)).symm.trans (congrArg H.map (hη k))
    exact congrArg (fun b : P ⟶ N k => b.hom) h
  have hqsurj (k : ℕ) : Function.Surjective (q k) := hsurj k
  let w : AdicModuleSystem.sections (R := R) (fun k => N k) t := ⟨z, hz⟩
  obtain ⟨x, hx⟩ := AdicModuleSystem.exists_lift_of_finite_completeLocal
    (R := R) (M := P) (fun k => N k) t q hq hqsurj hpow w
  exact ⟨x, hx⟩

omit I in
/-- The actual finite global-section module lifts any compatible
family under its original surjective quotient-unit maps. -/
theorem exists_globalSection_of_compatible_levelSections
    (hsurj : ∀ k : ℕ, Function.Surjective
      ((levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k).app ⊤))
    (z : ∀ k : ℕ, Γ(levelPullbackModule f (IsLocalRing.maximalIdeal R) M k, ⊤))
    (hz : ∀ k : ℕ,
      (levelPullbackTransition f (IsLocalRing.maximalIdeal R) M k).app ⊤ (z (k + 1)) = z k) :
    ∃ x : Γ(M, ⊤), ∀ k : ℕ,
      (levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k).app ⊤ x = z k :=
  exists_section_lift_of_compatible_quotients f M
    (levelPullbackModule f (IsLocalRing.maximalIdeal R) M)
    (levelPullbackTransition f (IsLocalRing.maximalIdeal R) M)
    (levelPullbackUnit f (IsLocalRing.maximalIdeal R) M)
    (levelPullbackUnit_transition f (IsLocalRing.maximalIdeal R) M) hsurj
    (levelPullbackModule_globalSections_annihilated f (IsLocalRing.maximalIdeal R) M) z hz

private theorem freeHom_lift_from_section_lifts
    {Y : Scheme.{u}} (P : Y.Modules) (Q : ℕ → Y.Modules)
    (q : ∀ k : ℕ, P ⟶ Q k)
    (t : ∀ k : ℕ, Q (k + 1) ⟶ Q k)
    (hlift : ∀ (z : ∀ k : ℕ, Γ(Q k, ⊤)),
      (∀ k : ℕ, (t k).app ⊤ (z (k + 1)) = z k) →
      ∃ x : Γ(P, ⊤), ∀ k : ℕ, (q k).app ⊤ x = z k)
    (J : Type u)
    (β : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶ Q k)
    (hβ : ∀ k : ℕ, β (k + 1) ≫ t k = β k) :
    ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ P,
      ∀ k : ℕ, φ ≫ q k = β k := by
  let z (j : J) (k : ℕ) : Γ(Q k, ⊤) := freeHomTopSectionsEquiv (Q k) J (β k) j
  have hz (j : J) (k : ℕ) : (t k).app ⊤ (z j (k + 1)) = z j k := by
    exact (freeHomTopSectionsEquiv_comp (Q (k + 1)) J (β (k + 1)) (t k) j).symm.trans
      (congrArg (fun b => freeHomTopSectionsEquiv (Q k) J b j) (hβ k))
  let x : J → Γ(P, ⊤) := fun j => (hlift (z j) (hz j)).choose
  let φ : (show Y.Modules from SheafOfModules.free J) ⟶ P :=
    (freeHomTopSectionsEquiv P J).symm x
  refine ⟨φ, ?_⟩
  intro k
  apply (freeHomTopSectionsEquiv (Q k) J).injective
  funext j
  calc
    freeHomTopSectionsEquiv (Q k) J (φ ≫ q k) j =
        (q k).app ⊤ (freeHomTopSectionsEquiv P J φ j) :=
      freeHomTopSectionsEquiv_comp P J φ (q k) j
    _ = (q k).app ⊤ (x j) :=
      congrArg ((q k).app ⊤) (congrFun ((freeHomTopSectionsEquiv P J).apply_symm_apply x) j)
    _ = z j k := (hlift (z j) (hz j)).choose_spec k

omit I in
/-- Lift the actual original columns of compatible quotient maps from
a free sheaf, using the finite global-section module of the fixed target. -/
theorem exists_freeHom_of_compatible_levelMaps
    (hsurj : ∀ k : ℕ, Function.Surjective
      ((levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k).app ⊤))
    (J : Type u)
    (β : ∀ k : ℕ, (show X.Modules from SheafOfModules.free J) ⟶
      levelPullbackModule f (IsLocalRing.maximalIdeal R) M k)
    (hβ : ∀ k : ℕ, β (k + 1) ≫
      levelPullbackTransition f (IsLocalRing.maximalIdeal R) M k = β k) :
    ∃ φ : (show X.Modules from SheafOfModules.free J) ⟶ M,
      ∀ k : ℕ, φ ≫ levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k = β k := by
  exact freeHom_lift_from_section_lifts M
    (levelPullbackModule f (IsLocalRing.maximalIdeal R) M)
    (levelPullbackUnit f (IsLocalRing.maximalIdeal R) M)
    (levelPullbackTransition f (IsLocalRing.maximalIdeal R) M)
    (exists_globalSection_of_compatible_levelSections f M hsurj) J β hβ

end AlgebraicGeometry.FiniteEtale.AdicCoverTower

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem compatible_postcompose_iso
    {C : Type*} [Category C] {Q : C} {A B : ℕ → C}
    (dA : ∀ k : ℕ, A (k + 1) ⟶ A k)
    (dB : ∀ k : ℕ, B (k + 1) ⟶ B k)
    (E : ∀ k : ℕ, A k ≅ B k)
    (hE : ∀ k : ℕ, (E (k + 1)).hom ≫ dB k = dA k ≫ (E k).hom)
    (θ : ∀ k : ℕ, Q ⟶ A k) (hθ : ∀ k : ℕ, θ (k + 1) ≫ dA k = θ k)
    (k : ℕ) :
    (θ (k + 1) ≫ (E (k + 1)).hom) ≫ dB k = θ k ≫ (E k).hom := by
  calc
    (θ (k + 1) ≫ (E (k + 1)).hom) ≫ dB k =
        θ (k + 1) ≫ ((E (k + 1)).hom ≫ dB k) := Category.assoc _ _ _
    _ = θ (k + 1) ≫ (dA k ≫ (E k).hom) :=
      congrArg (fun b => θ (k + 1) ≫ b) (hE k)
    _ = (θ (k + 1) ≫ dA k) ≫ (E k).hom := (Category.assoc _ _ _).symm
    _ = θ k ≫ (E k).hom := congrArg (fun b => b ≫ (E k).hom) (hθ k)

private theorem exists_lift_compatible_postcompose_iso
    {C : Type*} [Category C] (S T : C) (A B : ℕ → C)
    (qA : ∀ k : ℕ, T ⟶ A k) (qB : ∀ k : ℕ, T ⟶ B k)
    (dA : ∀ k : ℕ, A (k + 1) ⟶ A k) (dB : ∀ k : ℕ, B (k + 1) ⟶ B k)
    (E : ∀ k : ℕ, A k ≅ B k)
    (hE : ∀ k : ℕ, (E (k + 1)).hom ≫ dB k = dA k ≫ (E k).hom)
    (hq : ∀ k : ℕ, qA k ≫ (E k).hom = qB k)
    (hlift : ∀ β : ∀ k : ℕ, S ⟶ B k,
      (∀ k : ℕ, β (k + 1) ≫ dB k = β k) →
      ∃ φ : S ⟶ T, ∀ k : ℕ, φ ≫ qB k = β k)
    (θ : ∀ k : ℕ, S ⟶ A k) (hθ : ∀ k : ℕ, θ (k + 1) ≫ dA k = θ k) :
    ∃ φ : S ⟶ T, ∀ k : ℕ, φ ≫ qA k = θ k := by
  let β (k : ℕ) : S ⟶ B k := θ k ≫ (E k).hom
  have hβ (k : ℕ) : β (k + 1) ≫ dB k = β k :=
    compatible_postcompose_iso (C := C) (Q := S) (A := A) (B := B)
      dA dB E hE θ hθ k
  obtain ⟨φ, hφ⟩ := hlift β hβ
  refine ⟨φ, ?_⟩
  intro k
  apply (cancel_mono (E k).hom).mp
  calc
    (φ ≫ qA k) ≫ (E k).hom = φ ≫ (qA k ≫ (E k).hom) := Category.assoc _ _ _
    _ = φ ≫ qB k := congrArg (fun b => φ ≫ b) (hq k)
    _ = θ k ≫ (E k).hom := hφ k

private theorem exists_levelTensorComparison_family
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) (a : Ideal R)
    (P N : Y.Modules) [P.IsQuasicoherent] [N.IsQuasicoherent] :
    ∃ E : ∀ k : ℕ,
        levelPullbackModule f a P k ⊗ N ≅ levelPullbackModule f a (P ⊗ N) k,
      (∀ k : ℕ, (E (k + 1)).hom ≫ levelPullbackTransition f a (P ⊗ N) k =
        (levelPullbackTransition f a P k ▷ N) ≫ (E k).hom) ∧
      (∀ k : ℕ, (levelPullbackUnit f a P k ▷ N) ≫ (E k).hom =
        levelPullbackUnit f a (P ⊗ N) k) :=
  ⟨levelPullbackTensorIso f a P N, levelPullbackTensorIso_transition f a P N,
    levelPullbackUnit_tensor_comparison f a P N⟩

private theorem exists_freeHom_of_compatible_levelComparison
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (A : ℕ → Y.Modules) (qA : ∀ k : ℕ, M ⟶ A k)
    (dA : ∀ k : ℕ, A (k + 1) ⟶ A k)
    (E : ∀ k : ℕ, A k ≅ levelPullbackModule f (IsLocalRing.maximalIdeal R) M k)
    (hE : ∀ k : ℕ, (E (k + 1)).hom ≫
      levelPullbackTransition f (IsLocalRing.maximalIdeal R) M k = dA k ≫ (E k).hom)
    (hq : ∀ k : ℕ, qA k ≫ (E k).hom =
      levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k)
    (hsurj : ∀ k : ℕ, Function.Surjective
      ((levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k).app ⊤))
    (J : Type u)
    (θ : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶ A k)
    (hθ : ∀ k : ℕ, θ (k + 1) ≫ dA k = θ k) :
    ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ M,
      ∀ k : ℕ, φ ≫ qA k = θ k := by
  have hlift : ∀ β : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
      levelPullbackModule f (IsLocalRing.maximalIdeal R) M k,
      (∀ k : ℕ, β (k + 1) ≫
        levelPullbackTransition f (IsLocalRing.maximalIdeal R) M k = β k) →
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ M,
        ∀ k : ℕ, φ ≫ levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k = β k := by
    intro β hβ
    exact exists_freeHom_of_compatible_levelMaps (R := R) (X := Y) f M hsurj J β hβ
  exact exists_lift_compatible_postcompose_iso (C := Y.Modules)
    (show Y.Modules from SheafOfModules.free J) M A
    (levelPullbackModule f (IsLocalRing.maximalIdeal R) M) qA
    (levelPullbackUnit f (IsLocalRing.maximalIdeal R) M) dA
    (levelPullbackTransition f (IsLocalRing.maximalIdeal R) M) E hE hq hlift θ hθ

private theorem exists_freeHom_of_compatible_tensored_levelMaps
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f]
    (P N : Y.Modules) [P.IsQuasicoherent] [N.IsQuasicoherent]
    [(P ⊗ N).IsQuasicoherent] [(P ⊗ N).IsFiniteType]
    (hsurj : ∀ k : ℕ, Function.Surjective
      ((levelPullbackUnit f (IsLocalRing.maximalIdeal R) (P ⊗ N) k).app ⊤))
    (J : Type u)
    (θ : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
      levelPullbackModule f (IsLocalRing.maximalIdeal R) P k ⊗ N)
    (hθ : ∀ k : ℕ, θ (k + 1) ≫
      (levelPullbackTransition f (IsLocalRing.maximalIdeal R) P k ▷ N) = θ k) :
    ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ P ⊗ N,
      ∀ k : ℕ, φ ≫
        (levelPullbackUnit f (IsLocalRing.maximalIdeal R) P k ▷ N) = θ k := by
  obtain ⟨E, hE, hq⟩ := exists_levelTensorComparison_family f (IsLocalRing.maximalIdeal R) P N
  exact exists_freeHom_of_compatible_levelComparison (R := R) (Y := Y)
    f (P ⊗ N) (fun k => levelPullbackModule f (IsLocalRing.maximalIdeal R) P k ⊗ N)
    (fun k => levelPullbackUnit f (IsLocalRing.maximalIdeal R) P k ▷ N)
    (fun k => levelPullbackTransition f (IsLocalRing.maximalIdeal R) P k ▷ N)
    E (fun k => hE k) hq hsurj J θ hθ

/-- On the original closed projective family, one bound algebraizes
every compatible relation family from a fixed free source to the
actual quotient of a sufficiently positive finite free twist. The
conclusion retains the original tensored quotient units. -/
theorem exists_closedProjective_freeTwist_bound_compatibleHom_lift
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (K : Type u) [Finite K] :
    let f := j ≫ π R n
    let a := IsLocalRing.maximalIdeal R
    let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
    let P : Y.Modules := SheafOfModules.free K
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ (J : Type u)
      (θ : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
        levelPullbackModule f a P k ⊗ L.tensorPow d),
      (∀ k : ℕ, θ (k + 1) ≫
        (levelPullbackTransition f a P k ▷ L.tensorPow d) = θ k) →
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ P ⊗ L.tensorPow d,
        ∀ k : ℕ, φ ≫ (levelPullbackUnit f a P k ▷ L.tensorPow d) = θ k := by
  intro f a L P
  have : IsProper f := inferInstance
  have : P.IsQuasicoherent := inferInstance
  have : P.IsFiniteType := finiteType_free K
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  obtain ⟨c, hc⟩ :=
    exists_closedProjective_freeTwist_bound_globalReduction_surjective R a n j K
  refine ⟨c, ?_⟩
  intro d hd J θ hθ
  let N : Y.Modules := L.tensorPow d
  let M : Y.Modules := P ⊗ N
  have : N.IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
  have : M.IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow P hL d
  have : M.IsFiniteType := IsInvertible.isFiniteType_tensorPow P hL d
  exact exists_freeHom_of_compatible_tensored_levelMaps (R := R)
    f P N (hc d hd) J θ hθ

end AlgebraicGeometry.ProjSpace
