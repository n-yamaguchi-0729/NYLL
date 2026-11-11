/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyLayers
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyTensorSections
public import Nyll.SchemeTheory.Cohomology.Cech.IntersectionCechVanishing
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Čech comparison for the original native syzygy layers

Choose the proved unique layer comparison on each actual cover
intersection. The original inclusion formulas identify the witnesses
on every face with the proved restriction-compatible pair. Tensoring
with the original coefficient sheaf therefore gives compatible additive
comparisons of the actual Čech cochains and transfers their vanishing.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) [IsSeparated f] (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (K : Type u) [Finite K]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)
  (hL : IsInvertible L) (hgen : ∀ n : ℕ, Epi (α n))
  (N : X.Modules) [N.IsQuasicoherent] (C : X.OrderedAffineCover)
  (t : ∀ (r : ℕ) (s : C.Idx r), Γ(L.tensorPow d, C.inter s))
  (ht : ∀ (r : ℕ) (s : C.Idx r), IsFrameOn (t r s) (C.inter s))

include hL hgen t ht in
/-- The actual ideal-tensor Čech vanishing implies vanishing for the
original native syzygy-transition kernel with the same coefficients. -/
theorem nativeSyzygyTensorHSucc_subsingleton_of_idealTensor (a k : ℕ) :
    let M : ℕ → X.Modules := fun b => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) b (α b)
    let q : ∀ b : ℕ, M (b + 1) ⟶ M b := fun b =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα b
    Subsingleton ((ReesTensor.idealTensorPresheaf f I (M 0 ⊗ N) (a + 1)).HSucc C k) →
      Subsingleton ((toOModulePresheaf f (kernel (q a) ⊗ N)).HSucc C k) := by
  intro M q hvan
  have : (kernel (q a)).IsQuasicoherent := isQuasicoherent_kernel (q a)
  let F := ReesTensor.idealTensorPresheaf f I (M 0 ⊗ N) (a + 1)
  let G := toOModulePresheaf f (kernel (q a) ⊗ N)
  have hex (r : ℕ) (s : C.Idx r) :
      ∃! e : (↥((sectionsIdeal f I (C.inter s)) ^ (a + 1))
          ⊗[Γ(X, C.inter s)] Γ(M 0, C.inter s)) ≃ₗ[Γ(X, C.inter s)]
          Γ(kernel (q a), C.inter s),
        ∀ (b : ↥((sectionsIdeal f I (C.inter s)) ^ (a + 1)))
          (x : sections (R := Γ(X, C.inter s)) (fun b => Γ(M b, C.inter s))
            (fun b => ((moduleSectionsFunctor (C.inter s)).map (q b)).hom)),
          (kernel.ι (q a)).app (C.inter s) (e (b ⊗ₜ[Γ(X, C.inter s)] x.val 0)) =
            b.val • x.val (a + 1) :=
    existsUnique_levelPresentationKernelTensorEquiv
      f I V L d K α hα hL hgen (C.affineInter f s) (t r s) (ht r s) a
  let e (r : ℕ) (s : C.Idx r) :
      (↥((sectionsIdeal f I (C.inter s)) ^ (a + 1))
        ⊗[Γ(X, C.inter s)] Γ(M 0, C.inter s)) ≃ₗ[Γ(X, C.inter s)]
        Γ(kernel (q a), C.inter s) := (hex r s).choose
  let E (r : ℕ) (s : C.Idx r) : F.obj (C.inter s) ≃+ G.obj (C.inter s) :=
    (tensorAffineEquiv (M 0) (kernel (q a)) N (C.affineInter f s)
      ((sectionsIdeal f I (C.inter s)) ^ (a + 1)) (e r s)).toAddEquiv
  have hE (r : ℕ) (s : C.Idx (r + 1)) (i : Fin (r + 2))
      (z : F.obj (C.inter (C.face s i))) :
      E (r + 1) s (F.res (C.inter_le_inter_face s i) z) =
        G.res (C.inter_le_inter_face s i) (E r (C.face s i) z) := by
    let U : X.affineOpens := C.affineInter f (C.face s i)
    let W : X.affineOpens := C.affineInter f s
    let h : (W : X.Opens) ≤ U := C.inter_le_inter_face s i
    obtain ⟨eU, eW, heU, heW, he⟩ :=
      exists_levelPresentationKernelTensorEquiv_restriction
        f I V L d K α hα hL hgen U W h
          (t r (C.face s i)) (ht r (C.face s i)) (t (r + 1) s) (ht (r + 1) s) a
    have hU : eU = e r (C.face s i) := (hex r (C.face s i)).choose_spec.2 eU heU
    have hW : eW = e (r + 1) s := (hex (r + 1) s).choose_spec.2 eW heW
    rw [hU, hW] at he
    exact (tensorAffineEquiv_restriction (M 0) (kernel (q a)) N U W h
      ((sectionsIdeal f I U) ^ (a + 1)) ((sectionsIdeal f I W) ^ (a + 1))
      (idealPowerRestriction f I h (a + 1)) (e r (C.face s i)) (e (r + 1) s) he z).symm
  have : Subsingleton (F.HSucc C k) := hvan
  exact OModulePresheaf.subsingleton_HSucc_of_intersectionEquiv C F G E hE k

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
