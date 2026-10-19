/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ReesImageModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.ReesAlgebra

/-!
# Affine coefficients of the native Rees image

On the pullback of an affine intersection, the native image sheaf has
sections equal to the Rees algebra of the extended ideal in the original
affine section ring. The original polynomial evaluation identifies the
inclusion. Coefficient membership and monomial lifting are supplied by
the existing Rees construction; the new comparison retains the native
module action and every face restriction.
-/

noncomputable section

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (.of A)) [IsSeparated q]
  (K : P.OrderedAffineCover)

/-- The actual image sections, with scalars from the original affine
intersection via its original pullback projection. -/
def imageAffineModuleOverOriginal {i : ℕ} (s : K.Idx i) : ModuleCat Γ(P, K.inter s) :=
  (ModuleCat.restrictScalars
    ((fst' I q).appLE (K.inter s) ((K' I q K).inter (indexEquiv I q K s))
      (e'_s I q K s)).hom).obj
    ((Scheme.Modules.moduleSectionsFunctor ((K' I q K).inter (indexEquiv I q K s))).obj
      (imageModule I q))

private theorem polynomial_projection_scalar {i : ℕ} (s : K.Idx i)
    (a : Γ(P, K.inter s)) :
    ΦC I q K s ((g I q).app ((K' I q K).inter (indexEquiv I q K s))
      ((fst' I q).appLE (K.inter s) ((K' I q K).inter (indexEquiv I q K s))
        (e'_s I q K s) a)) = C a := by
  have h := ΦC_θ I q K s (C a)
  rw [θ_C] at h
  have hcomp := congrArg
    (fun k : Γ(P, K.inter s) ⟶
      Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) => k a)
    (Scheme.Hom.appLE_comp_appLE (g I q) (fst' I q)
      (K.inter s) ((K' I q K).inter (indexEquiv I q K s))
      (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e'_s I q K s) le_rfl)
  rw [Scheme.Hom.appLE_eq_app] at hcomp
  exact (congrArg (ΦC I q K s) hcomp).trans h

/-- The original polynomial coordinate map on native image sections,
linear for the original affine coefficient ring. -/
def imageAffinePolynomial {i : ℕ} (s : K.Idx i) :
    imageAffineModuleOverOriginal I q K s →ₗ[Γ(P, K.inter s)] Γ(P, K.inter s)[X] where
  toFun x := ΦC I q K s
    ((Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)).app
      ((K' I q K).inter (indexEquiv I q K s)) x)
  map_add' x y := by
    let j := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
    let W := (K' I q K).inter (indexEquiv I q K s)
    have h := (j.app W).hom.map_add
      (show Γ(imageModule I q, W) from x) (show Γ(imageModule I q, W) from y)
    exact (congrArg (ΦC I q K s) h).trans ((ΦC I q K s).map_add _ _)
  map_smul' a x := by
    let W := (K' I q K).inter (indexEquiv I q K s)
    let j := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
    let a' : Γ(P' I q, W) := (fst' I q).appLE (K.inter s) W (e'_s I q K s) a
    let v : Γ(P₁ I q, g I q ⁻¹ᵁ W) := j.app W x
    have hs := j.app_smul a' (show Γ(imageModule I q, W) from x)
    have hs' : (j.app W (a • x) : Γ(P₁ I q, g I q ⁻¹ᵁ W)) =
        (g I q).app W a' * v := hs
    have hpoly := congrArg (ΦC I q K s) hs'
    have hmul := (ΦC I q K s).map_mul ((g I q).app W a') v
    exact hpoly.trans (hmul.trans
      ((congrArg (fun c : Γ(P, K.inter s)[X] => c * ΦC I q K s v)
        (polynomial_projection_scalar I q K s a)).trans
          (Polynomial.smul_eq_C_mul (p := ΦC I q K s v) a).symm))

private theorem imageAffinePolynomial_mem {i : ℕ} (s : K.Idx i)
    (x : imageAffineModuleOverOriginal I q K s) :
    imageAffinePolynomial I q K s x ∈ reesAlgebra (I.map (alg q (K.inter s))) := by
  classical
  let W := (K' I q K).inter (indexEquiv I q K s)
  have hW : IsAffineOpen W := by
    change IsAffineOpen ((K' I q K).inter (indexEquiv I q K s))
    rw [K'_inter]
    exact (haff q K s).preimage (fst' I q)
  let z : (F' I q).obj W := imageAffineSectionsEquiv I q W hW x
  let c : (F' I q).cochain (K' I q K) i := Pi.single (indexEquiv I q K s) z
  intro n
  have hm := coeffC_mem I q K i n c s
  have hcz : coeffC I q K i n c s = (ΦC I q K s (F'val I q z)).coeff n := by
    simp only [coeffC_apply, c, Pi.single_eq_same]
    rfl
  have hm' : (ΦC I q K s (F'val I q z)).coeff n ∈
      (I.map (alg q (K.inter s))) ^ n := by
    rw [← Ideal.map_pow]
    exact hcz ▸ hm
  have he := imageAffineSectionsEquiv_apply I q W hW
    (show Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) W from x)
  have hc : (ΦC I q K s (F'val I q z)).coeff n =
      (imageAffinePolynomial I q K s x).coeff n :=
    congrArg (fun y : Γ(P₁ I q, g I q ⁻¹ᵁ W) => (ΦC I q K s y).coeff n) he
  exact hc ▸ hm'

omit [IsSeparated q] in
private theorem rees_mem_Sθ {i : ℕ} (s : K.Idx i)
    (p : ↥(reesAlgebra (I.map (alg q (K.inter s))))) : p.val ∈ Sθ I q K s := by
  have hsum : p.val.sum (fun n a => monomial n a) ∈ Sθ I q K s := by
    apply (Sθ I q K s).sum_mem
    intro n _
    apply monomial_mem_Sθ I q K s
    change p.val.coeff n ∈ Ideal.map (alg q (K.inter s)) (I ^ n)
    rw [Ideal.map_pow]
    exact (mem_reesAlgebra_iff _ _).mp p.property n
  exact (Polynomial.sum_monomial_eq p.val) ▸ hsum

private def imageAffineReesMap {i : ℕ} (s : K.Idx i) :
    imageAffineModuleOverOriginal I q K s →ₗ[Γ(P, K.inter s)]
      ↥(reesAlgebra (I.map (alg q (K.inter s)))) where
  toFun x := ⟨imageAffinePolynomial I q K s x, imageAffinePolynomial_mem I q K s x⟩
  map_add' x y := Subtype.ext ((imageAffinePolynomial I q K s).map_add x y)
  map_smul' a x := Subtype.ext ((imageAffinePolynomial I q K s).map_smul a x)

private theorem imageAffineReesMap_bijective {i : ℕ} (s : K.Idx i) :
    Function.Bijective (imageAffineReesMap I q K s) := by
  let W := (K' I q K).inter (indexEquiv I q K s)
  have hW : IsAffineOpen W := by
    change IsAffineOpen ((K' I q K).inter (indexEquiv I q K s))
    rw [K'_inter]
    exact (haff q K s).preimage (fst' I q)
  constructor
  · intro x y h
    let j := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
    have hi := (Scheme.Modules.Hom.mono_iff_injective j).mp
      (inferInstanceAs (Mono (C := (P' I q).Modules)
        (Abelian.image.ι (C := (P' I q).Modules)
          (Scheme.DirectImageAlgebra.unitMap (g I q))))) W
    exact hi ((ΦC I q K s).injective (congrArg Subtype.val h))
  · intro p
    let z : (F' I q).obj W :=
      ⟨θ I q (K.inter s) (g I q ⁻¹ᵁ W) (e_s I q K s) p.val,
        mem_range_of_mem_Sθ I q K s (rees_mem_Sθ I q K s p)⟩
    let x : imageAffineModuleOverOriginal I q K s :=
      (imageAffineSectionsEquiv I q W hW).symm z
    refine ⟨x, Subtype.ext ?_⟩
    have he := imageAffineSectionsEquiv_apply I q W hW
      (show Scheme.Modules.sectionModuleOverBase (π' I q) (imageModule I q) W from x)
    have hz := (imageAffineSectionsEquiv I q W hW).apply_symm_apply z
    have hv : ((Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)).app W x :
        Γ(P₁ I q, g I q ⁻¹ᵁ W)) =
        θ I q (K.inter s) (g I q ⁻¹ᵁ W) (e_s I q K s) p.val :=
      he.symm.trans (congrArg (F'val I q) hz)
    exact (congrArg (ΦC I q K s) hv).trans (ΦC_θ I q K s p.val)

/-- Native image sections on an affine intersection are exactly the
Rees algebra of its extended ideal, with the original coefficient action. -/
def imageAffineReesEquiv {i : ℕ} (s : K.Idx i) :
    imageAffineModuleOverOriginal I q K s ≃ₗ[Γ(P, K.inter s)]
      ↥(reesAlgebra (I.map (alg q (K.inter s)))) :=
  LinearEquiv.ofBijective (imageAffineReesMap I q K s)
    (imageAffineReesMap_bijective I q K s)

/-- The affine comparison retains the actual polynomial-coordinate map
of the original image inclusion. -/
theorem imageAffineReesEquiv_apply {i : ℕ} (s : K.Idx i)
    (x : imageAffineModuleOverOriginal I q K s) :
    (imageAffineReesEquiv I q K s x).val =
      ΦC I q K s ((Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)).app
        ((K' I q K).inter (indexEquiv I q K s)) x) := rfl

/-- Each face restriction is the original restriction of every
coefficient in the original affine section ring. -/
theorem imageAffineReesEquiv_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (x : imageAffineModuleOverOriginal I q K (K.face s j)) :
    (imageAffineReesEquiv I q K s
      ((imageModule I q).presheaf.map
        (homOfLE (K'_inter_le_inter_face I q K s j)).op x)).val =
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
        (imageAffineReesEquiv I q K (K.face s j) x).val := by
  let W := (K' I q K).inter (indexEquiv I q K s)
  let V := (K' I q K).inter (indexEquiv I q K (K.face s j))
  let z : Γ(imageModule I q, V) := x
  let h : W ≤ V := K'_inter_le_inter_face I q K s j
  let ι := Scheme.DirectImageAlgebra.imageModuleInclusion (g I q)
  have hnat := congrArg
    (fun ψ : Γ(imageModule I q, V) ⟶
      Γ(Scheme.RelativeSpec.underlyingModule
        (Scheme.DirectImageAlgebra.structureMap (g I q)), W) => ψ z)
    (ι.mapPresheaf.naturality (homOfLE h).op)
  have hnat' :
      (ι.app W ((imageModule I q).presheaf.map (homOfLE h).op z) :
        Γ(P₁ I q, g I q ⁻¹ᵁ W)) =
      (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op
        (ι.app V z) := hnat
  exact (congrArg (ΦC I q K s) hnat').trans
    (ΦC_res I q K s j (show Γ(P₁ I q, g I q ⁻¹ᵁ V) from ι.app V z))

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
