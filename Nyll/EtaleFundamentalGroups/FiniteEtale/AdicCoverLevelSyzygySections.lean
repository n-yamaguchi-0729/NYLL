/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffinePresentation
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineSyzygies
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelFreeSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Sections.ClosedPullbackFreeSections
import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Sections.KernelSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations

/-!
# Original affine sections of the native closed-level syzygies

The actual closed pullback of the free source has the original quotient
coefficient module as its affine sections. Its presentation is the
quotient-linear combination of the original global generators. Restricting
this equivalence to the actual categorical kernel identifies the native
syzygy sections with the constructed affine presentation kernel.

The equivalences commute with the original transitions. Consequently the
actual native syzygy transitions are surjective on every affine chart
with a frame for the twist, and their kernels are exactly the original
adic ideal multiples. These conclusions concern the kernels on the
thickenings, not the kernels of the unreduced ambient free presentations.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

/-- The evaluation functor and the native section map have the same actual
underlying function. Establish this boundary while the modules are abstract,
so later applications do not normalize a concrete pullback transition. -/
private theorem module_app_eq_evaluation {Y : Scheme.{u}} {M N : Y.Modules}
    (a : M ⟶ N) (W : Y.Opens) (x : Γ(M, W)) :
    a.app W x = ((moduleSectionsFunctor W).map a).hom x := rfl

private theorem module_evaluation_triangle {Y : Scheme.{u}} {M N P : Y.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ P) (h : a ≫ b = c) (W : Y.Opens) :
    ((moduleSectionsFunctor W).map b).hom.comp ((moduleSectionsFunctor W).map a).hom =
      ((moduleSectionsFunctor W).map c).hom := by
  have he : (moduleSectionsFunctor W).map a ≫ (moduleSectionsFunctor W).map b =
      (moduleSectionsFunctor W).map c :=
    ((moduleSectionsFunctor W).map_comp a b).symm.trans
      (congrArg (moduleSectionsFunctor W).map h)
  exact congrArg ModuleCat.Hom.hom he

private theorem native_app_surjective_of_evaluation {Y : Scheme.{u}} {M N : Y.Modules}
    (a : M ⟶ N) (W : Y.Opens)
    (h : Function.Surjective ((moduleSectionsFunctor W).map a).hom) :
    Function.Surjective (a.app W) := by
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨x, (module_app_eq_evaluation a W x).trans hx⟩

private theorem module_evaluation_square {Y : Scheme.{u}} {M N P Q : Y.Modules}
    (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ P) (d : P ⟶ Q)
    (h : a ≫ b = c ≫ d) (W : Y.Opens) :
    ((moduleSectionsFunctor W).map b).hom.comp ((moduleSectionsFunctor W).map a).hom =
      ((moduleSectionsFunctor W).map d).hom.comp ((moduleSectionsFunctor W).map c).hom := by
  have he : (moduleSectionsFunctor W).map a ≫ (moduleSectionsFunctor W).map b =
      (moduleSectionsFunctor W).map c ≫ (moduleSectionsFunctor W).map d :=
    (((moduleSectionsFunctor W).map_comp a b).symm.trans
      (congrArg (moduleSectionsFunctor W).map h)).trans
        ((moduleSectionsFunctor W).map_comp c d)
  exact congrArg ModuleCat.Hom.hom he

private theorem linearMap_restricted_square
    {R C₀ C₁ M₀ M₁ : Type*} [CommRing R]
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    (e₀ : C₀ →ₗ[R] M₀) (e₁ : C₁ →ₗ[R] M₁)
    (S₀ : Submodule R C₀) (S₁ : Submodule R C₁)
    (q : C₁ →ₗ[R] C₀) (a : S₁ →ₗ[R] S₀) (T : M₁ →ₗ[R] M₀)
    (hs : S₀.subtype.comp a = q.comp S₁.subtype)
    (he : T.comp e₁ = e₀.comp q) :
    (e₀.domRestrict S₀).comp a = T.comp (e₁.domRestrict S₁) := by
  change (e₀.comp S₀.subtype).comp a = T.comp (e₁.comp S₁.subtype)
  calc
    (e₀.comp S₀.subtype).comp a = e₀.comp (S₀.subtype.comp a) :=
      LinearMap.comp_assoc a S₀.subtype e₀
    _ = e₀.comp (q.comp S₁.subtype) := congrArg (fun z => e₀.comp z) hs
    _ = (e₀.comp q).comp S₁.subtype := (LinearMap.comp_assoc S₁.subtype q e₀).symm
    _ = (T.comp e₁).comp S₁.subtype := congrArg (fun z => z.comp S₁.subtype) he.symm
    _ = T.comp (e₁.comp S₁.subtype) := LinearMap.comp_assoc S₁.subtype e₁ T

private theorem linearMap_square_of_inclusions
    {R K₀ K₁ S₀ S₁ M₀ M₁ : Type*} [CommRing R]
    [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup S₀] [Module R S₀] [AddCommGroup S₁] [Module R S₁]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    (e₀ : K₀ →ₗ[R] S₀) (e₁ : K₁ →ₗ[R] S₁)
    (j₀ : S₀ →ₗ[R] M₀) (j₁ : S₁ →ₗ[R] M₁)
    (κ₀ : K₀ →ₗ[R] M₀) (κ₁ : K₁ →ₗ[R] M₁)
    (τ : K₁ →ₗ[R] K₀) (a : S₁ →ₗ[R] S₀) (T : M₁ →ₗ[R] M₀)
    (hj₀ : Function.Injective j₀)
    (h₀ : j₀.comp e₀ = κ₀) (h₁ : j₁.comp e₁ = κ₁)
    (hκ : κ₀.comp τ = T.comp κ₁) (hj : j₀.comp a = T.comp j₁) :
    e₀.comp τ = a.comp e₁ := by
  apply (LinearMap.cancel_left hj₀).mp
  calc
    j₀.comp (e₀.comp τ) = (j₀.comp e₀).comp τ := (LinearMap.comp_assoc τ e₀ j₀).symm
    _ = κ₀.comp τ := congrArg (fun z => z.comp τ) h₀
    _ = T.comp κ₁ := hκ
    _ = T.comp (j₁.comp e₁) := congrArg (fun z => T.comp z) h₁.symm
    _ = (T.comp j₁).comp e₁ := (LinearMap.comp_assoc e₁ j₁ T).symm
    _ = (j₀.comp a).comp e₁ := congrArg (fun z => z.comp e₁) hj.symm
    _ = j₀.comp (a.comp e₁) := LinearMap.comp_assoc e₁ a j₀

private theorem linearMap_transition_of_coefficients
    {R C C₀ C₁ M₀ M₁ : Type*} [CommRing R]
    [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R C₀]
    [AddCommGroup C₁] [Module R C₁] [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁]
    (c₀ : C →ₗ[R] C₀) (c₁ : C →ₗ[R] C₁) (e₀ : C₀ →ₗ[R] M₀) (e₁ : C₁ →ₗ[R] M₁)
    (q : C₁ →ₗ[R] C₀) (τ : M₁ →ₗ[R] M₀) (b₀ : C →ₗ[R] M₀) (b₁ : C →ₗ[R] M₁)
    (hc : Function.Surjective c₁)
    (h₀ : e₀.comp c₀ = b₀) (h₁ : e₁.comp c₁ = b₁)
    (hq : q.comp c₁ = c₀) (hτ : τ.comp b₁ = b₀) :
    τ.comp e₁ = e₀.comp q := by
  apply (LinearMap.cancel_right hc).mp
  calc
    (τ.comp e₁).comp c₁ = τ.comp (e₁.comp c₁) := LinearMap.comp_assoc c₁ e₁ τ
    _ = τ.comp b₁ := congrArg (fun z => τ.comp z) h₁
    _ = b₀ := hτ
    _ = e₀.comp c₀ := h₀.symm
    _ = e₀.comp (q.comp c₁) := congrArg (fun z => e₀.comp z) hq.symm
    _ = (e₀.comp q).comp c₁ := (LinearMap.comp_assoc c₁ q e₀).symm

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (K : Type u) [Finite K]
  (U : X.affineOpens)

/-- The original free coefficients followed by the evaluated original unit. -/
private def levelFreeCoefficientMap (n : ℕ) :
    (K →₀ Γ(X, U)) →ₗ[Γ(X, U)]
      (moduleSectionsFunctor (U : X.Opens)).obj
        (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) n) :=
  (((moduleSectionsFunctor (U : X.Opens)).map
    (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) n)).hom).comp
      (finiteFreeSectionsEquiv (X := X) K (U : X.Opens)).toLinearMap

private theorem levelFreeSectionsEquiv_comp_coefficients (n : ℕ) :
    (levelFreeSectionsEquiv f I K U n).toLinearMap.comp
      (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K) =
        levelFreeCoefficientMap f I K U n := by
  apply LinearMap.ext
  intro c
  exact ((levelFreeSectionsEquiv_coefficients f I K U n c).trans
    (levelFreeSectionsCoefficients_apply f I K U n c)).trans
    (module_app_eq_evaluation
      (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) n)
      (U : X.Opens) (finiteFreeSectionsEquiv (X := X) K (U : X.Opens) c))

omit [Finite K] in
private theorem levelFreeUnit_transition_linear (n : ℕ) :
    (((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom).comp
        ((moduleSectionsFunctor (U : X.Opens)).map
          (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) (n + 1))).hom =
      ((moduleSectionsFunctor (U : X.Opens)).map
        (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) n)).hom :=
  module_evaluation_triangle
    (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) (n + 1))
    (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)
    (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) n)
    (levelPullbackUnit_transition f I (show X.Modules from SheafOfModules.free K) n) U

private theorem levelFreeCoefficientMap_transition (n : ℕ) :
    (((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom).comp
        (levelFreeCoefficientMap f I K U (n + 1)) = levelFreeCoefficientMap f I K U n :=
  (LinearMap.comp_assoc
    (finiteFreeSectionsEquiv (X := X) K (U : X.Opens)).toLinearMap
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackUnit f I (show X.Modules from SheafOfModules.free K) (n + 1))).hom
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom).symm.trans
        (congrArg (fun q : Γ((show X.Modules from SheafOfModules.free K), U) →ₗ[Γ(X, U)]
          Γ(levelPullbackModule f I (show X.Modules from SheafOfModules.free K) n, U) =>
            q.comp (finiteFreeSectionsEquiv (X := X) K (U : X.Opens)).toLinearMap)
          (levelFreeUnit_transition_linear f I K U n))

/-- The original evaluated transition commutes with the free-section
comparison as a linear map over the original affine coordinate ring. -/
theorem levelFreeSectionsEquiv_transition_linear (n : ℕ) :
    (((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom).comp
        (levelFreeSectionsEquiv f I K U (n + 1)).toLinearMap =
      (levelFreeSectionsEquiv f I K U n).toLinearMap.comp
        (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) :=
  linearMap_transition_of_coefficients
    (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K)
    (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1 + 1)) K)
    (levelFreeSectionsEquiv f I K U n).toLinearMap
    (levelFreeSectionsEquiv f I K U (n + 1)).toLinearMap
    (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom
    (levelFreeCoefficientMap f I K U n)
    (levelFreeCoefficientMap f I K U (n + 1))
    (quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1 + 1)) K)
    (levelFreeSectionsEquiv_comp_coefficients f I K U n)
    (levelFreeSectionsEquiv_comp_coefficients f I K U (n + 1))
    (quotientFreeFactor_coefficients K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (levelFreeCoefficientMap_transition f I K U n)

variable
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))

private abbrev generatorSections (n : ℕ) :
    K → Γ(tensor (moduleSheaf f I V n) (L.tensorPow d), ⊤) :=
  freeHomTopSectionsEquiv (tensor (moduleSheaf f I V n) (L.tensorPow d)) K (α n)

/-- The native closed-level presentation is the original affine
quotient presentation under the constructed free-section equivalence. -/
theorem levelFreeSectionsEquiv_presentation (n : ℕ)
    (x : K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) :
    (levelPresentation f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) n (α n)).app U
        (levelFreeSectionsEquiv f I K U n x) =
      affinePresentationMap f I V L d K
        (generatorSections f I K V L d α) U t ht n x := by
  obtain ⟨c, rfl⟩ :=
    quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1)) K x
  rw [levelFreeSectionsEquiv_coefficients, levelFreeSectionsCoefficients_apply,
    affinePresentationMap_coefficients_free, Equiv.symm_apply_apply]
  exact congrArg
    (fun k : (show X.Modules from SheafOfModules.free K) ⟶
      moduleSheaf f I V n ⊗ L.tensorPow d =>
        k.app U (finiteFreeSectionsEquiv (X := X) K (U : X.Opens) c))
    (levelUnit_levelPresentation f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) n (α n))

private theorem levelPresentationKernel_map (n : ℕ) :
    (affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n).map
        (levelFreeSectionsEquiv f I K U n).toLinearMap =
      (((moduleSectionsFunctor (U : X.Opens)).map
        (levelPresentation f I V (L.tensorPow d)
          (show X.Modules from SheafOfModules.free K) n (α n))).hom).ker := by
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (levelFreeSectionsEquiv_presentation f I K U V L d α t ht n x).trans hx
  · intro hy
    refine ⟨(levelFreeSectionsEquiv f I K U n).symm y, ?_,
      (levelFreeSectionsEquiv f I K U n).apply_symm_apply y⟩
    change affinePresentationMap f I V L d K
      (generatorSections f I K V L d α) U t ht n
        ((levelFreeSectionsEquiv f I K U n).symm y) = 0
    rw [← levelFreeSectionsEquiv_presentation,
      (levelFreeSectionsEquiv f I K U n).apply_symm_apply]
    exact hy

/-- Actual sections of the native syzygy identify with the kernel of
the original quotient-free affine presentation. -/
def levelPresentationKernelSectionsEquiv (n : ℕ) :
    Γ(levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) n (α n), U) ≃ₗ[Γ(X, U)]
        affineSyzygyKernel f I V L d K
          (generatorSections f I K V L d α) U t ht n := by
  let P : X.Modules := SheafOfModules.free K
  let Q : X.Modules := levelPullbackModule f I P n
  let T : X.Modules := moduleSheaf f I V n ⊗ L.tensorPow d
  let p : Q ⟶ T := levelPresentation f I V (L.tensorPow d) P n (α n)
  let q : Γ(Q, U) →ₗ[Γ(X, U)] Γ(T, U) :=
    ((moduleSectionsFunctor (U : X.Opens)).map p).hom
  let e : (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃ₗ[Γ(X, U)]
      Γ(Q, U) := levelFreeSectionsEquiv f I K U n
  let S : Submodule Γ(X, U) (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) :=
    affineSyzygyKernel f I V L d K (generatorSections f I K V L d α) U t ht n
  have hmap : S.map e.toLinearMap = q.ker :=
    levelPresentationKernel_map f I K U V L d α t ht n
  let eK : Γ(kernel p, U) ≃ₗ[Γ(X, U)] q.ker := kernelSectionsEquiv p (U : X.Opens)
  exact eK.trans (e.ofSubmodules S q.ker hmap).symm

/-- The syzygy-section comparison retains the original kernel inclusion. -/
theorem levelPresentationKernelSectionsEquiv_inclusion (n : ℕ)
    (x : Γ(levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) n (α n), U)) :
    levelFreeSectionsEquiv f I K U n
        (levelPresentationKernelSectionsEquiv f I K U V L d α t ht n x).val =
      (kernel.ι (levelPresentation f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) n (α n))).app U x := by
  change levelFreeSectionsEquiv f I K U n
    ((levelFreeSectionsEquiv f I K U n).symm
      (kernelSectionsEquiv
        (levelPresentation f I V (L.tensorPow d)
          (show X.Modules from SheafOfModules.free K) n (α n))
            (U : X.Opens) x).val) = _
  exact ((levelFreeSectionsEquiv f I K U n).apply_symm_apply _).trans
    (kernelSectionsEquiv_apply _ (U : X.Opens) x)

omit [(L.tensorPow d).IsQuasicoherent] in
/-- The actual coefficient inclusion of an affine syzygy into the
native free-section module, with its inherited submodule scalar action. -/
private def levelFreeSyzygySectionsInclusion (n : ℕ) :
    affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n →ₗ[Γ(X, U)]
        (moduleSectionsFunctor (U : X.Opens)).obj
          (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) n) :=
  (levelFreeSectionsEquiv f I K U n).toLinearMap.domRestrict
    (affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n)

omit [(L.tensorPow d).IsQuasicoherent] in
private theorem levelFreeSyzygySectionsInclusion_injective (n : ℕ) :
    Function.Injective (levelFreeSyzygySectionsInclusion f I K U V L d α t ht n) :=
  (levelFreeSectionsEquiv f I K U n).injective.comp Subtype.val_injective

private theorem levelPresentationKernelSectionsEquiv_inclusion_linear (n : ℕ) :
    (levelFreeSyzygySectionsInclusion f I K U V L d α t ht n).comp
      (levelPresentationKernelSectionsEquiv f I K U V L d α t ht n).toLinearMap =
      ((moduleSectionsFunctor (U : X.Opens)).map
        (kernel.ι (levelPresentation f I V (L.tensorPow d)
          (show X.Modules from SheafOfModules.free K) n (α n)))).hom := by
  apply LinearMap.ext
  intro x
  exact (levelPresentationKernelSectionsEquiv_inclusion f I K U V L d α t ht n x).trans
    (module_app_eq_evaluation
      (kernel.ι (levelPresentation f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) n (α n))) U x)

variable (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)

include hα in
omit [Finite K] [(L.tensorPow d).IsQuasicoherent] in
private theorem generatorSections_transition (n : ℕ) (k : K) :
    (moduleTransition f I V n ▷ L.tensorPow d).app ⊤
        (generatorSections f I K V L d α (n + 1) k) =
      generatorSections f I K V L d α n k := by
  rw [← freeHomTopSectionsEquiv_comp, hα n]

omit [Finite K] [(L.tensorPow d).IsQuasicoherent] in
private theorem affineSyzygyTransition_inclusion_linear (n : ℕ) :
    (affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n).subtype.comp
        (affineSyzygyTransition f I V L d K
          (generatorSections f I K V L d α) U t ht
          (generatorSections_transition f I K V L d α hα) n) =
      (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).comp
          (affineSyzygyKernel f I V L d K
            (generatorSections f I K V L d α) U t ht (n + 1)).subtype := by
  apply LinearMap.ext
  exact affineSyzygyTransition_val f I V L d K
    (generatorSections f I K V L d α) U t ht
    (generatorSections_transition f I K V L d α hα) n

private theorem levelPresentationKernelTransition_inclusion_linear
    (P N : X.Modules) [P.IsQuasicoherent] [N.IsQuasicoherent]
    (β : ∀ n : ℕ, P ⟶ moduleSheaf f I V n ⊗ N)
    (hβ : ∀ n : ℕ, β (n + 1) ≫ (moduleTransition f I V n ▷ N) = β n)
    (n : ℕ) (W : X.Opens) :
    ((moduleSectionsFunctor W).map
      (kernel.ι (levelPresentation f I V N P n (β n)))).hom.comp
        ((moduleSectionsFunctor W).map
          (levelPresentationKernelTransition f I V N P β hβ n)).hom =
      ((moduleSectionsFunctor W).map (levelPullbackTransition f I P n)).hom.comp
        ((moduleSectionsFunctor W).map
          (kernel.ι (levelPresentation f I V N P (n + 1) (β (n + 1))))).hom :=
  module_evaluation_square
    (levelPresentationKernelTransition f I V N P β hβ n)
    (kernel.ι (levelPresentation f I V N P n (β n)))
    (kernel.ι (levelPresentation f I V N P (n + 1) (β (n + 1))))
    (levelPullbackTransition f I P n)
    (levelPresentationKernelTransition_ι f I V N P β hβ n) W

omit [(L.tensorPow d).IsQuasicoherent] in
private theorem levelFreeSyzygyTransition_inclusion_linear (n : ℕ) :
    (levelFreeSyzygySectionsInclusion f I K U V L d α t ht n).comp
      (affineSyzygyTransition f I V L d K
        (generatorSections f I K V L d α) U t ht
        (generatorSections_transition f I K V L d α hα) n) =
      ((moduleSectionsFunctor (U : X.Opens)).map
        (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom.comp
          (levelFreeSyzygySectionsInclusion f I K U V L d α t ht (n + 1)) :=
  linearMap_restricted_square (R := Γ(X, U))
    (C₀ := K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
    (C₁ := K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1 + 1))
    (M₀ := (moduleSectionsFunctor (U : X.Opens)).obj
      (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) n))
    (M₁ := (moduleSectionsFunctor (U : X.Opens)).obj
      (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) (n + 1)))
    (levelFreeSectionsEquiv f I K U n).toLinearMap
    (levelFreeSectionsEquiv f I K U (n + 1)).toLinearMap
    (affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n)
    (affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht (n + 1))
    (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (affineSyzygyTransition f I V L d K
      (generatorSections f I K V L d α) U t ht
      (generatorSections_transition f I K V L d α hα) n)
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom
    (affineSyzygyTransition_inclusion_linear f I K U V L d α t ht hα n)
    (levelFreeSectionsEquiv_transition_linear f I K U n)

/-- The evaluated native kernel transition and the original affine
syzygy transition form the same square of linear maps. -/
theorem levelPresentationKernelSectionsEquiv_transition_linear (n : ℕ) :
    (levelPresentationKernelSectionsEquiv f I K U V L d α t ht n).toLinearMap.comp
      ((moduleSectionsFunctor (U : X.Opens)).map
        (levelPresentationKernelTransition f I V (L.tensorPow d)
          (show X.Modules from SheafOfModules.free K) α hα n)).hom =
      (affineSyzygyTransition f I V L d K
        (generatorSections f I K V L d α) U t ht
        (generatorSections_transition f I K V L d α hα) n).comp
          (levelPresentationKernelSectionsEquiv f I K U V L d α t ht (n + 1)).toLinearMap :=
  linearMap_square_of_inclusions (R := Γ(X, U))
    (K₀ := Γ(levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) n (α n), U))
    (K₁ := Γ(levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) (n + 1) (α (n + 1)), U))
    (S₀ := affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht n)
    (S₁ := affineSyzygyKernel f I V L d K
      (generatorSections f I K V L d α) U t ht (n + 1))
    (M₀ := (moduleSectionsFunctor (U : X.Opens)).obj
      (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) n))
    (M₁ := (moduleSectionsFunctor (U : X.Opens)).obj
      (levelPullbackModule f I (show X.Modules from SheafOfModules.free K) (n + 1)))
    (levelPresentationKernelSectionsEquiv f I K U V L d α t ht n).toLinearMap
    (levelPresentationKernelSectionsEquiv f I K U V L d α t ht (n + 1)).toLinearMap
    (levelFreeSyzygySectionsInclusion f I K U V L d α t ht n)
    (levelFreeSyzygySectionsInclusion f I K U V L d α t ht (n + 1))
    ((moduleSectionsFunctor (U : X.Opens)).map
      (kernel.ι (levelPresentation f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) n (α n)))).hom
    ((moduleSectionsFunctor (U : X.Opens)).map
      (kernel.ι (levelPresentation f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) (n + 1) (α (n + 1))))).hom
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα n)).hom
    (affineSyzygyTransition f I V L d K
      (generatorSections f I K V L d α) U t ht
      (generatorSections_transition f I K V L d α hα) n)
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free K) n)).hom
    (levelFreeSyzygySectionsInclusion_injective f I K U V L d α t ht n)
    (levelPresentationKernelSectionsEquiv_inclusion_linear f I K U V L d α t ht n)
    (levelPresentationKernelSectionsEquiv_inclusion_linear f I K U V L d α t ht (n + 1))
    (levelPresentationKernelTransition_inclusion_linear f I V
      (show X.Modules from SheafOfModules.free K) (L.tensorPow d) α hα n U)
    (levelFreeSyzygyTransition_inclusion_linear f I K U V L d α t ht hα n)

include t ht in
/-- The actual native syzygy transition is surjective on every affine
chart carrying a frame of the original twist. -/
theorem levelPresentationKernelTransition_sections_surjective (hL : IsInvertible L)
    (n : ℕ) (hgen : Epi (α (n + 1))) :
    Function.Surjective
      (((moduleSectionsFunctor (U : X.Opens)).map
        (levelPresentationKernelTransition f I V (L.tensorPow d)
          (show X.Modules from SheafOfModules.free K) α hα n)).hom) := by
  have ha : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V (n + 1)) (L.tensorPow d)) K).symm
        (generatorSections f I K V L d α (n + 1))) := by
    rw [generatorSections, Equiv.symm_apply_apply]
    exact hgen
  let e₀ := levelPresentationKernelSectionsEquiv f I K U V L d α t ht n
  let e₁ := levelPresentationKernelSectionsEquiv f I K U V L d α t ht (n + 1)
  intro y
  obtain ⟨z, hz⟩ := affineSyzygyTransition_surjective f I V L d K
    (generatorSections f I K V L d α) U t ht
    (generatorSections_transition f I K V L d α hα) hL n ha (e₀ y)
  refine ⟨e₁.symm z, e₀.injective ?_⟩
  exact (LinearMap.congr_fun
    (levelPresentationKernelSectionsEquiv_transition_linear f I K U V L d α t ht hα n)
      (e₁.symm z)).trans ((congrArg
      (affineSyzygyTransition f I V L d K
        (generatorSections f I K V L d α) U t ht
        (generatorSections_transition f I K V L d α hα) n)
      (e₁.apply_symm_apply z)).trans hz)

include t ht in
/-- The original native section map is surjective on an affine chart
with a frame of the original twist. -/
theorem levelPresentationKernelTransition_app_surjective (hL : IsInvertible L)
    (n : ℕ) (hgen : Epi (α (n + 1))) :
    Function.Surjective
      ((levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα n).app U) :=
  native_app_surjective_of_evaluation
    (levelPresentationKernelTransition f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) α hα n) U
    (levelPresentationKernelTransition_sections_surjective f I K U V L d α t ht hα hL n hgen)

include t ht in
/-- The kernel of the original native syzygy transition is precisely
the original ideal power times its actual affine section module. -/
theorem levelPresentationKernelTransition_sections_ker [IsLocallyNoetherian X]
    (hL : IsInvertible L) (n : ℕ) (hgen : Epi (α (n + 1))) :
    (((moduleSectionsFunctor (U : X.Opens)).map
      (levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα n)).hom).ker =
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U)
          Γ(levelPresentationKernel f I V (L.tensorPow d)
            (show X.Modules from SheafOfModules.free K) (n + 1) (α (n + 1)), U)) := by
  have ha : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V (n + 1)) (L.tensorPow d)) K).symm
        (generatorSections f I K V L d α (n + 1))) := by
    rw [generatorSections, Equiv.symm_apply_apply]
    exact hgen
  let e₀ := levelPresentationKernelSectionsEquiv f I K U V L d α t ht n
  let e₁ := levelPresentationKernelSectionsEquiv f I K U V L d α t ht (n + 1)
  let q : Γ(levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) (n + 1) (α (n + 1)), U) →ₗ[Γ(X, U)]
      Γ(levelPresentationKernel f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) n (α n), U) :=
    ((moduleSectionsFunctor (U : X.Opens)).map
      (levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα n)).hom
  let a := affineSyzygyTransition f I V L d K
    (generatorSections f I K V L d α) U t ht
    (generatorSections_transition f I K V L d α hα) n
  have hcomp : e₀.toLinearMap.comp q = a.comp e₁.toLinearMap :=
    levelPresentationKernelSectionsEquiv_transition_linear f I K U V L d α t ht hα n
  have hker : q.ker = a.ker.comap e₁.toLinearMap := by
    rw [← e₀.ker_comp q, hcomp, LinearMap.ker_comp]
  have hrange : (⊤ : Submodule Γ(X, U) _) ≤ e₁.toLinearMap.range := by
    rw [LinearMap.range_eq_top.mpr e₁.surjective]
  change q.ker = _
  rw [hker, affineSyzygyTransition_ker f I V L d K
    (generatorSections f I K V L d α) U t ht
    (generatorSections_transition f I K V L d α hα) hL n ha,
    Submodule.comap_smul'' e₁.injective hrange, Submodule.comap_top]

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
