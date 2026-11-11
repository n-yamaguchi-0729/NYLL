/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Homogeneous sections in degree-zero Cech cohomology

A specified section map supplies the cocycle by restriction to the original
standard cover. The construction retains that map; it makes no further choice.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjSpace.HomogeneousSectionsH0

variable {n : ℕ} {k : Type u} [CommRing k] {Zk : Scheme.{u}}
  (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ιk] (d : ℕ)

/-- The actual homogeneous fraction viewed on the pulled-back coordinate chart. -/
noncomputable def chartVal (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d) (i : Fin (n
  + 1)) :
    Γ(Zk, ProjSpace.pullbackChart ιk i) :=
  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }))

/-- Membership in the degree piece supplies its homogeneity proof. -/
theorem isHomogeneous_of_mem (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    (F : MvPolynomial (Fin (n + 1)) k).IsHomogeneous d :=
  (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2

/-- The degree-zero index of the specified standard coordinate chart. -/
def vertex (i : Fin (n + 1)) : (ProjSpace.stdCoverPullback ιk).Idx 0 :=
  ⟨fun _ => ULift.up i, fun a b hab => absurd (Fin.lt_def.mp hab)
    (by have := a.isLt; have := b.isLt; omega)⟩

/-- A standard chart lies in the intersection indexed by its vertex. -/
theorem chart_le_inter_vertex (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ιk i ≤ (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
      ProjSpace.pullbackChart ιk i :=
  le_inf (le_iInf fun _ => le_rfl) le_rfl

/-- Restrict the given section map to an H0-valued map with the same chart values. -/
theorem exists_theta_of_section_map
    (θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
      ProjSpace.twistObj (ιk ≫ ProjSpace.π k n) ιk d ⊤)
    (hθ : ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d)
      (i : Fin (n + 1)),
      (θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩).val i =
        ProjSpace.restrictFun
          (inf_le_right : (⊤ : Zk.Opens) ⊓ ProjSpace.pullbackChart ιk i ≤
            ProjSpace.pullbackChart ιk i)
          (chartVal ιk d F hF i)) :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)),
      ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i) := by
  let T := ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d
  let K := ProjSpace.stdCoverPullback ιk
  let Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k] T.cochain K 0 :=
    LinearMap.pi fun s => (T.res (le_top : K.inter s ≤ ⊤)).comp θ
  have hΘ₀ : ∀ F s, Θ₀ F s = T.res (le_top : K.inter s ≤ ⊤) (θ F) := fun F s => rfl
  have hcoc : ∀ F, Θ₀ F ∈ T.H0 K := by
    intro F
    rw [LinearMap.mem_ker]
    funext s
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, hΘ₀]
    change T.res (K.inter_le_inter_face s 0) (T.res le_top (θ F)) +
      -T.res (K.inter_le_inter_face s 1) (T.res le_top (θ F)) = (0 : T.obj (K.inter s))
    exact (congrArg₂ (fun x y : T.obj (K.inter s) => x + -y)
      (T.res_res (K.inter_le_inter_face s 0) le_top (θ F))
      (T.res_res (K.inter_le_inter_face s 1) le_top (θ F))).trans
      (add_neg_cancel (T.res (le_top : K.inter s ≤ ⊤) (θ F)))
  refine ⟨LinearMap.codRestrict (T.H0 K) Θ₀ hcoc, fun F s i => ?_⟩
  rw [LinearMap.codRestrict_apply, hΘ₀]
  change (ProjSpace.twistRes (ιk ≫ ProjSpace.π k n) ιk d (le_top : K.inter s ≤ ⊤) (θ F)).val i = _
  rw [ProjSpace.twistRes_val]
  have hF : (θ F).val i =
      ProjSpace.restrictFun (inf_le_right : (⊤ : Zk.Opens) ⊓ ProjSpace.pullbackChart ιk i ≤
        ProjSpace.pullbackChart ιk i) (chartVal ιk d F (isHomogeneous_of_mem d F) i) :=
    hθ F.1 (isHomogeneous_of_mem d F) i
  exact (congrArg (ProjSpace.restrictFun
      (inf_le_inf_right (ProjSpace.pullbackChart ιk i) (le_top : K.inter s ≤ ⊤))) hF).trans
    (ProjSpace.restrictFun_restrictFun
      (inf_le_inf_right (ProjSpace.pullbackChart ιk i) (le_top : K.inter s ≤ ⊤))
      inf_le_right (chartVal ιk d F (isHomogeneous_of_mem d F) i))

variable {ιk d}

/-- A cocycle with the specified chart formula vanishes exactly on all chart values. -/
theorem theta_eq_zero_iff
    (Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) →ₗ[k]
        ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk)))
    (hΘ : ∀ (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d))
        (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
        ((Θ F : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback
          ιk) 0) s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i
              ≤ ProjSpace.pullbackChart ιk i)
            (chartVal ιk d F (isHomogeneous_of_mem d F) i))
    (F : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d)) :
    Θ F = 0 ↔ ∀ i : Fin (n + 1), chartVal ιk d F (isHomogeneous_of_mem d F) i = 0 := by
  constructor
  · intro h i
    have h1 := hΘ F (vertex ιk i) i
    rw [h] at h1
    have h2 : ProjSpace.restrictFun (chart_le_inter_vertex ιk i)
        (ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter (vertex ιk i) ⊓
            ProjSpace.pullbackChart ιk i ≤
            ProjSpace.pullbackChart ιk i)
          (chartVal ιk d F (isHomogeneous_of_mem d F) i)) = chartVal ιk d F (isHomogeneous_of_mem d
            F) i := by
      rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl _
    rw [← h2, ← h1]
    have hz : (((0 : ↥((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback
      ιk))) :
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).cochain (ProjSpace.stdCoverPullback ιk) 0)
          (vertex ιk i)).val i
        = 0 := rfl
    rw [hz, map_zero]
  · intro h
    apply Subtype.ext
    funext s
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ, h i, map_zero]
    rfl

end AlgebraicGeometry.ProjSpace.HomogeneousSectionsH0
