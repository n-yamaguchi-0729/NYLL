/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteIff
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFinitePushforwardIff
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Čech cohomology of the actual direct image sheaf

The native direct image has exactly the sections on preimage opens.
The coefficient action on these sections is compared using the actual
composite structural morphism. This gives the literal linear comparison
between the native direct image and the Čech presheaf pushforward.

For a closed immersion, compose this comparison with the existing
preimage-cover comparison. The resulting cochain and cohomology
equivalences use the original native restriction maps. Scheme
isomorphisms are included as a special case.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_pushforward_iff.AlgebraicGeometry.OModulePresheaf
  renaming pushforwardCochainEquiv → presheafPushforwardCochainEquiv,
    pushforwardCochainEquiv_d → presheafPushforwardCochainEquiv_d
open OModulePresheaf_cechFinite_iff_of_cochain_equiv.AlgebraicGeometry.OModulePresheaf
  (hSuccEquiv)

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (g : Y ⟶ X) (M : Y.Modules)

/-- The section comparison is the identity on the original native
sections, with the coefficient action checked along the actual composite. -/
def pushforwardSectionsOverBaseEquiv (U : X.Opens) :
    sectionModuleOverBase (g ≫ f) M (g ⁻¹ᵁ U) ≃ₗ[R]
      sectionModuleOverBase f ((pushforward g).obj M) U where
  toFun := fun x => (show Γ(M, g ⁻¹ᵁ U) from x)
  invFun := fun x => (show Γ(M, g ⁻¹ᵁ U) from x)
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro a x
    let y : Γ(M, g ⁻¹ᵁ U) := x
    change ((g ≫ f).constToPresheaf.app (op (g ⁻¹ᵁ U))).hom a • y =
      (g.app U).hom ((f.constToPresheaf.app (op U)).hom a) • y
    exact congrArg (fun b : Γ(Y, g ⁻¹ᵁ U) => b • y)
      (congrArg (fun k : R →+* Γ(Y, g ⁻¹ᵁ U) => k a)
        (Scheme.Hom.constToPresheaf_comp_app g f U)).symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The comparison keeps the original value of the section. -/
theorem pushforwardSectionsOverBaseEquiv_apply (U : X.Opens)
    (x : sectionModuleOverBase (g ≫ f) M (g ⁻¹ᵁ U)) :
    pushforwardSectionsOverBaseEquiv f g M U x = (show Γ(M, g ⁻¹ᵁ U) from x) := rfl

/-- The section comparison commutes with the original restrictions. -/
theorem pushforwardSectionsOverBaseEquiv_restriction {U V : X.Opens} (h : U ≤ V)
    (x : (OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)).obj V) :
    pushforwardSectionsOverBaseEquiv f g M U
        ((OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)).res h x) =
      (toOModulePresheaf f ((pushforward g).obj M)).res h
        (pushforwardSectionsOverBaseEquiv f g M V x) := rfl

private def nativePushforwardCochainComparison (K : X.OrderedAffineCover) (q : ℕ) :
    (OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)).cochain K q ≃ₗ[R]
      (toOModulePresheaf f ((pushforward g).obj M)).cochain K q :=
  LinearEquiv.piCongrRight (fun s : K.Idx q =>
    pushforwardSectionsOverBaseEquiv f g M (K.inter s))

private theorem nativePushforwardCochainComparison_d (K : X.OrderedAffineCover) (q : ℕ)
    (x : (OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)).cochain K q) :
    nativePushforwardCochainComparison f g M K (q + 1)
        ((OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)).d K q x) =
      (toOModulePresheaf f ((pushforward g).obj M)).d K q
        (nativePushforwardCochainComparison f g M K q x) := by
  funext s
  let F : OModulePresheaf f := OModulePresheaf.pushforward f g (toOModulePresheaf (g ≫ f) M)
  let G : OModulePresheaf f := toOModulePresheaf f ((pushforward g).obj M)
  let e : F.obj (K.inter s) →ₗ[R] G.obj (K.inter s) :=
    (pushforwardSectionsOverBaseEquiv f g M (K.inter s)).toLinearMap
  change e (F.d K q x s) = G.d K q (nativePushforwardCochainComparison f g M K q x) s
  rw [OModulePresheaf.d_apply, map_sum, OModulePresheaf.d_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  exact congrArg (fun z : G.obj (K.inter s) => ((-1 : ℤ) ^ (j : ℕ)) • z)
    (pushforwardSectionsOverBaseEquiv_restriction f g M
      (K.inter_le_inter_face s j) (x (K.face s j)))

variable [IsClosedImmersion g] (K : X.OrderedAffineCover)

/-- The original cochains of a native sheaf on the preimage cover
identify with the original cochains of its native direct image. -/
def pushforwardCochainEquiv (q : ℕ) :
    (toOModulePresheaf (g ≫ f) M).cochain (K.preimage g) q ≃ₗ[R]
      (toOModulePresheaf f ((pushforward g).obj M)).cochain K q :=
  (presheafPushforwardCochainEquiv g (toOModulePresheaf (g ≫ f) M) K q).trans
      (nativePushforwardCochainComparison f g M K q)

/-- The native direct-image comparison intertwines the actual Čech differentials. -/
theorem pushforwardCochainEquiv_d (q : ℕ)
    (x : (toOModulePresheaf (g ≫ f) M).cochain (K.preimage g) q) :
    pushforwardCochainEquiv f g M K (q + 1)
        ((toOModulePresheaf (g ≫ f) M).d (K.preimage g) q x) =
      (toOModulePresheaf f ((pushforward g).obj M)).d K q
        (pushforwardCochainEquiv f g M K q x) := by
  exact (congrArg (nativePushforwardCochainComparison f g M K (q + 1))
    (presheafPushforwardCochainEquiv_d g (toOModulePresheaf (g ≫ f) M) K q x)).trans
    (nativePushforwardCochainComparison_d f g M K q _)

/-- Positive cohomology of the native direct image, on the actual
cover, is the positive cohomology on its actual preimage cover. -/
def pushforwardHSuccEquiv (q : ℕ) :
    (toOModulePresheaf (g ≫ f) M).HSucc (K.preimage g) q ≃ₗ[R]
      (toOModulePresheaf f ((pushforward g).obj M)).HSucc K q :=
  hSuccEquiv (toOModulePresheaf (g ≫ f) M)
      (toOModulePresheaf f ((pushforward g).obj M)) (K.preimage g) K
      (pushforwardCochainEquiv f g M K) (pushforwardCochainEquiv_d f g M K) q

end AlgebraicGeometry.Scheme.Modules
