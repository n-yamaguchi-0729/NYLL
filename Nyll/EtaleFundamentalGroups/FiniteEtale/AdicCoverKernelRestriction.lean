/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTransitionKernels
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverFormalModule
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# Original affine restrictions of the actual transition-kernel tensors

Naturality of the original structural map identifies the extended
section ideals on smaller opens. The native cover and formal section
restrictions are semilinear for that same coefficient map. Lifting a
first-stage section to the actual formal module and restricting it proves
that the constructed tensor/kernel comparison commutes with the original
sheaf restrictions. This supplies the restriction compatibility required
for the Čech differential; it is not an additional comparison hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)

/-- The actual structural section ideal is extended by the actual
restriction homomorphism on every smaller open. -/
theorem sectionsIdeal_map_restriction {U W : X.Opens} (h : W ≤ U) :
    (sectionsIdeal f I U).map (X.presheaf.map (homOfLE h).op).hom =
      sectionsIdeal f I W := by
  have hcoef : (X.presheaf.map (homOfLE h).op).hom.comp
      (f.constToPresheaf.app (op U)).hom = (f.constToPresheaf.app (op W)).hom := by
    apply RingHom.ext
    intro a
    exact (congrArg (fun k : CommRingCat.of A ⟶ Γ(X, W) => k a)
      (f.constToPresheaf.naturality (homOfLE h).op)).symm
  rw [sectionsIdeal, Ideal.map_map, hcoef]
  rfl

/-- The original restriction homomorphism on the original ideal powers. -/
def idealPowerRestriction {U W : X.Opens} (h : W ≤ U) (n : ℕ) :
    ↥((sectionsIdeal f I U) ^ n) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      ↥((sectionsIdeal f I W) ^ n) where
  toFun a := ⟨X.presheaf.map (homOfLE h).op a.val, by
    rw [← sectionsIdeal_map_restriction f I h, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (X.presheaf.map (homOfLE h).op).hom a.property⟩
  map_add' a b := Subtype.ext ((X.presheaf.map (homOfLE h).op).hom.map_add a.val b.val)
  map_smul' a b := Subtype.ext ((X.presheaf.map (homOfLE h).op).hom.map_mul a b.val)

variable (V : MorphismProperty.Over
  ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The actual native restriction between original affine cover sections,
with the source and target coefficient actions retained. -/
def affineSectionRestriction (U W : X.affineOpens) (h : (W : X.Opens) ≤ U) (n : ℕ) :
    affineSectionModule f I V U n →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      affineSectionModule f I V W n :=
  (moduleSheaf f I V n).val.restrictₛₗ (homOfLE h).op

/-- The actual native restriction between affine sections of the
constructed formal module sheaf. -/
def formalAffineRestriction (U W : X.affineOpens) (h : (W : X.Opens) ≤ U) :
    formalAffineSectionModule f I V U →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
      formalAffineSectionModule f I V W :=
  (formalModuleSheaf f I V).val.restrictₛₗ (homOfLE h).op

/-- Every original stage projection commutes with these original
native affine restrictions. -/
theorem formalAffineProjection_restriction (U W : X.affineOpens)
    (h : (W : X.Opens) ≤ U) (n : ℕ) (x : formalAffineSectionModule f I V U) :
    affineSectionRestriction f I V U W h n (formalAffineProjection f I V U n x) =
      formalAffineProjection f I V W n (formalAffineRestriction f I V U W h x) := by
  let y : Γ(formalModuleSheaf f I V, U) := x
  have hn := congrArg
    (fun k : Γ(formalModuleSheaf f I V, U) ⟶ Γ(moduleSheaf f I V n, W) => k y)
    ((formalModuleProjection f I V n).mapPresheaf.naturality (homOfLE h).op)
  exact hn.symm

variable [IsLocallyNoetherian X]

/-- The actual tensor comparison for transition-kernel sections commutes
with restriction to any smaller affine open, using the original maps
on both the ideal coefficients and the first cover. -/
theorem transitionKernelTensorSectionsEquiv_restriction
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U) (n : ℕ)
    (z : ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)]
      (affineSectionModule f I V U 0)) :
    (transitionKernelSheaf f I V n).val.restrictₛₗ (homOfLE h).op
        (transitionKernelTensorSectionsEquiv f I V U n z) =
      transitionKernelTensorSectionsEquiv f I V W n
        (TensorProduct.map (idealPowerRestriction f I h (n + 1))
          (affineSectionRestriction f I V U W h 0) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
      obtain ⟨x, rfl⟩ := formalModuleProjection_app_surjective f I V U 0 y
      have hmono : Mono (kernel.ι (moduleTransition f I V n)) :=
        (transitionKernelSequence_shortExact f I V n).mono_f
      apply (Scheme.Modules.Hom.mono_iff_injective
        (kernel.ι (moduleTransition f I V n))).mp hmono W
      let k : Γ(transitionKernelSheaf f I V n, U) :=
        transitionKernelTensorSectionsEquiv f I V U n
          (a ⊗ₜ[Γ(X, U)] formalAffineProjection f I V U 0 x)
      have hnat := congrArg
        (fun q : Γ(transitionKernelSheaf f I V n, U) ⟶
          Γ(moduleSheaf f I V (n + 1), W) => q k)
        ((kernel.ι (moduleTransition f I V n)).mapPresheaf.naturality (homOfLE h).op)
      have hU := transitionKernelTensorSectionsEquiv_tmul_projection f I V U n a x
      have hW := transitionKernelTensorSectionsEquiv_tmul_projection f I V W n
        (idealPowerRestriction f I h (n + 1) a) (formalAffineRestriction f I V U W h x)
      have hr := formalAffineProjection_restriction f I V U W h (n + 1) x
      have h₀ := formalAffineProjection_restriction f I V U W h 0 x
      rw [TensorProduct.map_tmul, h₀]
      exact hnat.trans
        ((congrArg (fun b : Γ(moduleSheaf f I V (n + 1), U) =>
            (moduleSheaf f I V (n + 1)).presheaf.map (homOfLE h).op b) hU).trans
          (((moduleSheaf f I V (n + 1)).map_smul (homOfLE h) a.val
            (formalAffineProjection f I V U (n + 1) x)).trans
            ((congrArg (fun b : affineSectionModule f I V W (n + 1) =>
              (idealPowerRestriction f I h (n + 1) a).val • b) hr).trans hW.symm)))
  | add x y hx hy =>
      rw [map_add, map_add, map_add]
      have hr := ((transitionKernelSheaf f I V n).val.restrictₛₗ (homOfLE h).op).map_add
        (transitionKernelTensorSectionsEquiv f I V U n x)
        (transitionKernelTensorSectionsEquiv f I V U n y)
      exact hr.trans (congrArg₂
        (fun a b : Γ(transitionKernelSheaf f I V n, W) => a + b) hx hy)

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
