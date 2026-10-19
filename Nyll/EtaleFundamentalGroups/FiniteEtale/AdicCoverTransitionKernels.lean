/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalLayers
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalModule
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
import Nyll.SchemeTheory.Modules.Sections.KernelSections
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The actual coherent transition kernels of the finite étale tower

Take the categorical kernel of each original cover transition on the
fixed scheme. Its inclusion and the original transition form a short
exact sequence. The kernel is quasicoherent, and finite type follows
over a locally Noetherian scheme from the actual injective maps on
affine sections.

The affine sections of this actual kernel are identified with the
tensor product of the original ideal-power coefficients and the first
cover's section module. The comparison is constructed through the
native formal sections, and its inclusion is the original scalar
multiplication of projected formal sections. No kernel comparison or
effective cover is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The actual native kernel of the original cover transition. -/
def transitionKernelSheaf (n : ℕ) : X.Modules :=
  kernel (moduleTransition f I V n)

instance transitionKernelSheaf_isQuasicoherent (n : ℕ) :
    (transitionKernelSheaf f I V n).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_kernel (moduleTransition f I V n)

/-- Affine lifting of the actual cover sections makes every original
transition an epimorphism of module sheaves. -/
theorem moduleTransition_epi (n : ℕ) : Epi (moduleTransition f I V n) := by
  apply (Scheme.Modules.Hom.epi_iff_locallySurjective (moduleTransition f I V n)).mpr
  intro U s x hx
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨W, hWU, hxW, ?_⟩
  obtain ⟨z, hz⟩ := moduleTransition_app_surjective f I V n W hW
    ((moduleSheaf f I V n).presheaf.map (homOfLE hWU).op s)
  exact ⟨z, hz⟩

/-- The original kernel inclusion and the original cover transition. -/
def transitionKernelSequence (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (moduleTransition f I V n)) (moduleTransition f I V n)
    (kernel.condition (moduleTransition f I V n))

private theorem mono_native_kernel {M N : X.Modules} (φ : M ⟶ N) :
    Mono (kernel.ι φ) := inferInstance

/-- The native kernel sequence is short exact, by actual affine
surjectivity of the cover transition. -/
theorem transitionKernelSequence_shortExact (n : ℕ) :
    (transitionKernelSequence f I V n).ShortExact :=
  { exact := ShortComplex.exact_kernel (moduleTransition f I V n)
    mono_f := mono_native_kernel (moduleTransition f I V n)
    epi_g := moduleTransition_epi f I V n }

variable [IsLocallyNoetherian X]

instance transitionKernelSheaf_isFiniteType (n : ℕ) :
    (transitionKernelSheaf f I V n).IsFiniteType := by
  apply Scheme.Modules.isFiniteType_of_finite_affine_sections (transitionKernelSheaf f I V n)
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U)
      ((Scheme.Modules.moduleSectionsFunctor U).obj (moduleSheaf f I V (n + 1))) :=
    moduleSheaf_finite_sections f I V (n + 1) U hU
  let e := Scheme.Modules.kernelSectionsEquiv (moduleTransition f I V n) U
  let j := (((Scheme.Modules.moduleSectionsFunctor U).map
    (moduleTransition f I V n)).hom.ker).subtype.comp e.toLinearMap
  exact Module.Finite.of_injective j (Subtype.val_injective.comp e.injective)

/-- The genuine section module of the original kernel sheaf is
computed from the original first-stage module and ideal-power coefficients. -/
def transitionKernelTensorSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] (affineSectionModule f I V U 0)
      ≃ₗ[Γ(X, U)]
        (Scheme.Modules.moduleSectionsFunctor (U : X.Opens)).obj
          (transitionKernelSheaf f I V n) :=
  (formalAffineTensorTransitionKernelEquiv f I V U n).trans
    (Scheme.Modules.kernelSectionsEquiv (moduleTransition f I V n) (U : X.Opens)).symm

/-- The comparison uses the literal original kernel inclusion and
the actual next-stage projection of a formal section. -/
theorem transitionKernelTensorSectionsEquiv_tmul_projection
    (U : X.affineOpens) (n : ℕ) (a : ↥((sectionsIdeal f I U) ^ (n + 1)))
    (x : formalAffineSectionModule f I V U) :
    (kernel.ι (moduleTransition f I V n)).app U
      (transitionKernelTensorSectionsEquiv f I V U n
        (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x)) =
      a.val • formalAffineProjection f I V U (n + 1) x := by
  have h := Scheme.Modules.kernelSectionsEquiv_symm_apply (moduleTransition f I V n)
    (U : X.Opens) (formalAffineTensorTransitionKernelEquiv f I V U n
      (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x))
  exact h.trans (formalAffineTensorTransitionKernelEquiv_tmul_projection f I V U n a x)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
